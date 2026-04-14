#!/usr/bin/env python3
import argparse
import csv
import re
import sys
import json
import os
import difflib
from collections import defaultdict

try:
    import pypdf
except ImportError:
    print("Error: pypdf is required. Please install it using 'pip install pypdf'")
    sys.exit(1)

# ANSI Color Codes
COLOR_RED = '\033[91m'
COLOR_GREEN = '\033[92m'
COLOR_YELLOW = '\033[93m'
COLOR_CYAN = '\033[96m'
COLOR_RESET = '\033[0m'

# Dictionary mapping known CUSIPs to Security Names requiring a Fed Source percentage
KNOWN_GOVT_FUNDS = {
    "9999100": "VANGUARD FEDL MONEY MKT"
}

class MultiLogger:
    """Writes to terminal, a color log, and a stripped non-color log simultaneously."""
    def __init__(self, prefix):
        self.terminal = sys.stdout
        self.log_color = open(f"{prefix}console_output_color.txt", "w", encoding="utf-8")
        self.log_nocolor = open(f"{prefix}console_output.txt", "w", encoding="utf-8")
        self.ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')

    def write(self, message):
        self.terminal.write(message)
        if not self.log_color.closed:
            self.log_color.write(message)
        if not self.log_nocolor.closed:
            self.log_nocolor.write(self.ansi_escape.sub('', message))

    def flush(self):
        self.terminal.flush()
        if not self.log_color.closed:
            self.log_color.flush()
        if not self.log_nocolor.closed:
            self.log_nocolor.flush()
        
    def close(self):
        if not self.log_color.closed:
            self.log_color.close()
        if not self.log_nocolor.closed:
            self.log_nocolor.close()

def clean_num(val):
    if not val or val == '...': return 0.0
    try: return float(str(val).replace(',', '').replace('%', ''))
    except ValueError: return 0.0

def clean_sec_name(name_parts):
    name = " ".join(name_parts)
    name = re.sub(r'\(cont.*?\)', '', name, flags=re.IGNORECASE)
    name = re.sub(r'\b\d{2}/\d{2}/\d{2}\b', '', name)
    # Strip Vanguard footnote markers (e.g., "Note: 99" or "Note 99")
    name = re.sub(r'\bNote:?\s*\d+\b', '', name, flags=re.IGNORECASE)
    return re.sub(r'\s{2,}', ' ', name).strip()

def get_clean_pdf_lines(pdf_path):
    """Extracts layout text, dynamically identifies the statement date, removes it along with CORRECTED, and normalizes whitespace."""
    lines = []
    statement_date = None
    try:
        with open(pdf_path, 'rb') as file:
            reader = pypdf.PdfReader(file)
            
            # First pass: dynamically find the specific statement date on page 1
            if len(reader.pages) > 0:
                first_page_text = reader.pages[0].extract_text(extraction_mode="layout") or ""
                date_match = re.search(r'Statement Date:\s*(\d{2}/\d{2}/\d{4})', first_page_text, re.IGNORECASE)
                if date_match:
                    statement_date = date_match.group(1)

            # Second pass: process all pages
            for page in reader.pages:
                text = page.extract_text(extraction_mode="layout")
                if not text: continue
                
                for line in text.split('\n'):
                    # 1. Remove the specifically found statement date from everywhere in this file
                    if statement_date:
                        line = line.replace(statement_date, '')
                        
                    # 2. Remove the optional CORRECTED string
                    line = re.sub(r'\bCORRECTED\b', '', line, flags=re.IGNORECASE)
                    
                    # 3. Remove Document ID dynamic values to prevent meaningless false diffs
                    line = re.sub(r'Document ID:\s*[A-Z0-9]+(?:\s+[A-Z0-9]+)*', 'Document ID:', line, flags=re.IGNORECASE)
                    
                    # 4. Collapse whitespace layout artifacts
                    line = re.sub(r'\s+', ' ', line)
                    stripped = line.strip()
                    
                    if stripped:
                        lines.append(stripped)
    except Exception: pass
    return lines

def parse_statement(pdf_path, target_boxes, fed_csv_path=None, debug=False, log_filepath=None, use_color=True, is_comparison=False):
    transactions = []
    summary_expected = {}
    supplemental_extracted = []
    statement_date = "Unknown Date"
    
    info_1099 = {
        '1a': 0.0, '1b': 0.0, '2a': 0.0, '2b': 0.0, '3': 0.0, '5': 0.0, '12': 0.0,
        'grand_totals': {
            'Total Dividends & distributions': 0.0,
            'Total Tax-exempt dividends': 0.0,
            'Total Foreign tax withheld': 0.0
        }
    }
    
    correction_flags = {
        'info_1099': defaultdict(bool),
        'grand_totals': defaultdict(bool),
        'securities': defaultdict(lambda: defaultdict(bool)),
        'transactions': []
    }
    
    working_div_data = defaultdict(lambda: {
        'name_parts': [],
        'cusip': '',
        'transactions': [],
        'totals': defaultdict(float),
        'supplemental': {}
    })
    
    debug_log = {
        "metadata": {"target_boxes": target_boxes, "method": "layout", "is_comparison_run": is_comparison},
        "summary_expected": {},
        "categories": {box: {"transactions": []} for box in target_boxes},
        "dividends_and_supplemental": {},
        "corrections_detected": {},
        "raw_pages": {}
    }

    def cprint(msg, color=None):
        if not msg or is_comparison: return
        if color and use_color: print(f"{color}{msg}{COLOR_RESET}")
        else: print(msg)

    cprint(f"=== STARTING BROKERAGE 1099 PARSE: {os.path.basename(pdf_path)} ===", COLOR_CYAN)

    fed_csv_data = {}
    if fed_csv_path and not is_comparison:
        try:
            with open(fed_csv_path, mode='r', encoding='utf-8') as f:
                reader = csv.DictReader(f)
                if reader.fieldnames and "CUSIP or Description" in reader.fieldnames:
                    for row in reader:
                        key = row.get("CUSIP or Description", "").strip().upper()
                        val_str = row.get("Fed source percentage", "").strip()
                        if key and val_str:
                            try: fed_csv_data[key] = float(val_str) / 100.0
                            except ValueError: pass
        except Exception: pass

    summary_row_pattern = re.compile(
        r'(B\s+or\s+E|C\s+or\s+F|A|B|C|D|E|F)\s*(?:\(basis.*?\)|\(Form.*?\))\s*'
        r'([\d,]+\.\d{2})\s*([\d,]+\.\d{2})\s*([\d,]+\.\d{2})\s*([\d,]+\.\d{2})\s*([-\d,]+\.\d{2})', re.IGNORECASE
    )
    
    core_pattern = re.compile(
        r'(?P<dsold>\d{2}/\d{2}/\d{2})\s+(?P<qty>[\d,]+\.\d+)\s+(?P<proceeds>[\d,]+\.\d{2})\s+'
        r'(?P<dacq>\d{2}/\d{2}/\d{2}|VARIOUS)\s+(?P<basis>[\d,]+\.\d{2})\s*'
        r'(?P<adj>[-\d,]+\.\d{2}|\.\.\.)?\s*(?P<gl>[-\d,]+\.\d{2})(?P<addl_info>[^\n]*)', re.IGNORECASE
    )

    div_row_pattern = re.compile(r'^(.*?)\s*(\d{2}/\d{2}/\d{2})\s+([-\d,]+\.\d{2})\s+(.*)$')
    div_total_pattern = re.compile(
        r'^(.*?)\s*([-\d,]+\.\d{2})\s+(Total Dividends & distributions|Total Tax-exempt dividends|Total Foreign tax withheld)', 
        re.IGNORECASE
    )
    
    supp_sec_pattern = re.compile(r'^([A-Z0-9\s\.\-\']+?)\s*/\s*([A-Z0-9]{9})(?:\s*/.*)?$')
    treasury_pattern = re.compile(r'U\.S\.\s*Treasury\s+([\d\.]+)')
    ny_pattern = re.compile(r'New York\s+([\d\.]+)')
    
    vanguard_note_pattern = re.compile(r'For the[^\(]{1,100}\(([A-Z0-9]+)\)[^%]{1,150}percentage is\s*([\d\.]+)%', re.IGNORECASE)

    current_global_box = None
    in_div_section = False
    in_supp_section = False
    in_grand_totals = False
    
    current_sec_id = None
    current_page_prefixes = []
    current_page_has_cont = False
    current_1099b_sec = "UNKNOWN"

    try:
        with open(pdf_path, 'rb') as file:
            reader = pypdf.PdfReader(file)
            
            for page_num in range(len(reader.pages)):
                if current_sec_id and current_page_prefixes and not current_page_has_cont:
                    working_div_data[current_sec_id]['name_parts'].extend(current_page_prefixes)
                
                current_page_prefixes = []
                current_page_has_cont = False

                page = reader.pages[page_num]
                try: page_text = page.extract_text(extraction_mode="layout")
                except TypeError:
                    if not is_comparison: cprint("\n[!] ERROR: pypdf is too old for layout extraction.", COLOR_RED)
                    sys.exit(1)
                
                if not page_text: continue
                if debug: debug_log["raw_pages"][f"page_{page_num + 1}"] = page_text
                
                if "Statement Date:" in page_text:
                    date_match = re.search(r'Statement Date:\s*(\d{2}/\d{2}/\d{4})', page_text, re.IGNORECASE)
                    if date_match and statement_date == "Unknown Date":
                        statement_date = date_match.group(1)
                
                # Active scan for Vanguard Endnotes anywhere on the page
                flat_text = re.sub(r'\s+', ' ', page_text)
                for endnote_match in vanguard_note_pattern.finditer(flat_text):
                    supplemental_extracted.append({
                        'name': 'UNKNOWN',
                        'cusip': endnote_match.group(1).upper(),
                        'fed_pct': clean_num(endnote_match.group(2)) / 100.0,
                        'ny_pct': None
                    })
                
                if "1099-DIV" in page_text.upper():
                    div_start_idx = page_text.upper().find("1099-DIV")
                    div_block = page_text[div_start_idx:]
                    for line_match in [
                        (r'1a-\s*Total ordinary dividends.{0,150}?([\d,]+\.\d{2})', '1a'),
                        (r'1b-\s*Qualified dividends.{0,150}?([\d,]+\.\d{2})', '1b'),
                        (r'2a-\s*Total capital gain distributions.{0,150}?([\d,]+\.\d{2})', '2a'),
                        (r'2b-\s*Unrecaptured Section 1250 gain.{0,150}?([\d,]+\.\d{2})', '2b'),
                        (r'3-\s*Nondividend distributions.{0,150}?([\d,]+\.\d{2})', '3'),
                        (r'5-\s*Section 199A dividends.{0,150}?([\d,]+\.\d{2})', '5'),
                        (r'12-\s*Exempt-interest dividends.{0,150}?([\d,]+\.\d{2})', '12'),
                    ]:
                        m = re.search(line_match[0], div_block, re.DOTALL | re.IGNORECASE)
                        if m:
                            val = clean_num(m.group(1))
                            end_idx = m.end(1)
                            is_corrected = bool(re.match(r'[ \t]*C\b', div_block[end_idx:end_idx+10]))
                            
                            info_1099[line_match[1]] = max(info_1099[line_match[1]], val)
                            if is_corrected:
                                correction_flags['info_1099'][line_match[1]] = True

                lines = page_text.split('\n')
                
                if "Detail for Dividends and Distributions" in page_text:
                    in_div_section = True
                    in_supp_section = False
                elif "Mutual Fund and UIT Supplemental Information" in page_text:
                    in_div_section = False
                    in_supp_section = True
                elif any(x in page_text for x in ["Fees and Expenses", "Proceeds from Broker", "Detail for Interest Income", "Detail for Original Issue"]):
                    in_div_section = False
                    in_supp_section = False

                for sum_match in summary_row_pattern.finditer(page_text):
                    box = re.sub(r'\s+', ' ', sum_match.group(1)).upper()
                    summary_expected[box] = {
                        'proceeds': clean_num(sum_match.group(2)), 'cost_basis': clean_num(sum_match.group(3)),
                        'adjustments': clean_num(sum_match.group(4)) + clean_num(sum_match.group(5)),
                        'gain_loss': clean_num(sum_match.group(6))
                    }

                box_headers = [{'box': m.group(1).upper(), 'start': m.start()} for m in re.finditer(r'Box\s+([A-F])\s+checked', page_text, re.IGNORECASE)]
                def get_box(idx):
                    b = current_global_box
                    for h in box_headers:
                        if h['start'] < idx: b = h['box']
                    return b

                matches = list(core_pattern.finditer(page_text))
                for i, match in enumerate(matches):
                    data = match.groupdict()
                    box = get_box(match.start())
                    if box and box in target_boxes:
                        start_desc = matches[i-1].end() if i > 0 else 0
                        between_text = page_text[start_desc:match.start()]
                        
                        anchors = [
                            r'Additional\s*information', r'also\s*not\s*reported\s*\(Z\)', 
                            r'alsonotreported\(Z\)', r'Original\s*basis:\s*\$[\d,]+\.\d{2}'
                        ]
                        for anchor in anchors:
                            between_text = re.split(anchor, between_text, flags=re.IGNORECASE)[-1]
                            
                        between_text = re.sub(r'Securitytotal:[\s\d\.\-,]+', '', between_text, flags=re.IGNORECASE)
                        between_text = re.sub(r'Totals:[\s\d\.\-,]+', '', between_text, flags=re.IGNORECASE)
                        between_text = re.sub(r'Page\s+\d+\s+of\s+\d+', '', between_text, flags=re.IGNORECASE)
                        
                        valid_lines = []
                        for line in between_text.split('\n'):
                            line = line.strip()
                            if not line: continue
                            p_lower = line.lower()
                            if '1a-description' in p_lower or '1c-date' in p_lower or 'gainorloss' in p_lower or 'proceeds' in p_lower: continue
                            if 'report on form' in p_lower or 'basis is' in p_lower or 'gain or loss' in p_lower: continue
                            if 'short term transactions' in p_lower or 'long term transactions' in p_lower: continue
                            if 'quantity' in p_lower or 'disposed' in p_lower or 'acquired' in p_lower: continue
                            if 'see the instructions for form' in p_lower: continue
                            if 'additional information' in p_lower: continue
                            valid_lines.append(line)
                            
                        if valid_lines:
                            new_sec = " ".join(valid_lines)
                            new_sec = re.sub(r'\s{2,}', ' ', new_sec).strip()
                            if new_sec:
                                current_1099b_sec = new_sec
                        
                        addl_info = data['addl_info'].strip()
                        is_corrected_tx = False
                        if re.search(r'\bC$', addl_info):
                            is_corrected_tx = True
                            
                        qty_str = data['qty'].replace(',', '')
                        base_desc = re.sub(r'\s*/\s*Symbol:?\s*$', '', current_1099b_sec, flags=re.IGNORECASE).strip()
                        base_desc = re.sub(r'\bNote:?\s*\d+\b', '', base_desc, flags=re.IGNORECASE).strip()
                        
                        formatted_desc = f"{qty_str} {base_desc}"
                        
                        tx = {
                            'box': box, 
                            'description': formatted_desc, 
                            'base_description': base_desc,
                            'date_sold': data['dsold'],
                            'quantity': qty_str, 
                            'proceeds': data['proceeds'].replace(',', ''),
                            'date_acquired': data['dacq'], 
                            'cost_basis': data['basis'].replace(',', ''),
                            'adjustments': data['adj'].replace(',', '') if data['adj'] else "0.00",
                            'gain_loss': data['gl'].replace(',', ''),
                            'corrected': is_corrected_tx
                        }
                        transactions.append(tx)
                if box_headers: current_global_box = box_headers[-1]['box']

                for raw_line in lines:
                    line = raw_line.strip()
                    if not line: continue
                    
                    if in_div_section:
                        p_lower = line.lower()
                        if any(x in p_lower for x in ["security description", "detail for dividends", "page", "1099-div"]):
                            continue
                            
                        ld = {}
                        tot_match = div_total_pattern.match(line)
                        row_match = div_row_pattern.match(line)
                        
                        if tot_match:
                            rest_of_line = line[tot_match.end():]
                            is_corrected = bool(re.search(r'\bC\b', rest_of_line))
                            
                            ld = {'type': 'total', 'prefix': tot_match.group(1).strip(), 'amount': clean_num(tot_match.group(2)), 'desc': tot_match.group(3).strip(), 'corrected': is_corrected}
                        elif row_match:
                            desc = row_match.group(4).strip()
                            is_corrected = False
                            
                            if re.search(r'\bC$', desc):
                                is_corrected = True
                                desc = re.sub(r'\s+C$', '', desc).strip()
                                
                            ld = {'type': 'transaction', 'prefix': row_match.group(1).strip(), 'date': row_match.group(2), 'amount': clean_num(row_match.group(3)), 'desc': desc, 'corrected': is_corrected}
                        else:
                            ld = {'type': 'text', 'prefix': line.strip()}
                            
                        prefix = ld['prefix']
                        
                        is_new_sec, cusip, name = False, "", ""
                        if prefix:
                            parts = re.split(r'\s{2,}', prefix)
                            if len(parts) > 1:
                                raw_cusip = parts[1].strip()
                                alpha_match = re.match(r'^([A-Z0-9]{9})\b', raw_cusip, re.IGNORECASE)
                                if alpha_match:
                                    is_new_sec, cusip, name = True, alpha_match.group(1).upper(), parts[0].strip()
                                elif raw_cusip.startswith("9999100"):
                                    alpha_match = re.match(r'^([A-Z0-9]+)', raw_cusip, re.IGNORECASE)
                                    is_new_sec, cusip, name = True, alpha_match.group(1).upper() if alpha_match else raw_cusip.upper(), parts[0].strip()
                        
                        if is_new_sec:
                            if current_sec_id and current_page_prefixes and not current_page_has_cont:
                                working_div_data[current_sec_id]['name_parts'].extend(current_page_prefixes)
                            
                            current_page_prefixes = []
                            current_page_has_cont = False
                            
                            current_sec_id = f"{cusip}_{name}"
                            working_div_data[current_sec_id]['cusip'] = cusip
                            if name: working_div_data[current_sec_id]['name_parts'].append(name)
                            
                            in_grand_totals = False
                            prefix = ""
                            
                        if prefix:
                            current_page_prefixes.append(prefix)
                            if "(cont" in prefix.lower(): current_page_has_cont = True
                                
                        if ld['type'] == 'total' and current_sec_id:
                            t_raw, amt = ld['desc'], ld['amount']
                            if 'tax-exempt' in t_raw.lower(): t_type = 'Total Tax-exempt dividends'
                            elif 'foreign' in t_raw.lower(): t_type = 'Total Foreign tax withheld'
                            else: t_type = 'Total Dividends & distributions'
                                
                            if not in_grand_totals:
                                has_divs = 'Total Dividends & distributions' in working_div_data[current_sec_id]['totals']
                                has_exempt = 'Total Tax-exempt dividends' in working_div_data[current_sec_id]['totals']
                                if (t_type == 'Total Dividends & distributions' and (has_divs or has_exempt)) or \
                                   (t_type == 'Total Tax-exempt dividends' and has_exempt) or \
                                   (t_type == 'Total Foreign tax withheld' and 'Total Foreign tax withheld' in working_div_data[current_sec_id]['totals']):
                                    in_grand_totals = True

                            if in_grand_totals: 
                                info_1099['grand_totals'][t_type] = max(info_1099['grand_totals'].get(t_type, 0.0), amt)
                                if ld['corrected']: correction_flags['grand_totals'][t_type] = True
                            else: 
                                working_div_data[current_sec_id]['totals'][t_type] = amt
                                if ld['corrected']: correction_flags['securities'][current_sec_id][t_type] = True
                                
                        elif ld['type'] == 'transaction' and current_sec_id:
                            working_div_data[current_sec_id]['transactions'].append({
                                'date': ld['date'], 'amount': ld['amount'], 'type': ld['desc'], 'corrected': ld['corrected']
                            })
                            
                    elif in_supp_section:
                        sec_match = supp_sec_pattern.search(line)
                        if sec_match:
                            supplemental_extracted.append({'name': sec_match.group(1).strip(), 'cusip': sec_match.group(2).strip().upper(), 'fed_pct': None, 'ny_pct': None})
                        elif supplemental_extracted:
                            t_m, ny_m = treasury_pattern.search(line), ny_pattern.search(line)
                            if t_m: supplemental_extracted[-1]['fed_pct'] = clean_num(t_m.group(1)) / 100.0
                            if ny_m: supplemental_extracted[-1]['ny_pct'] = clean_num(ny_m.group(1)) / 100.0

            if current_sec_id and current_page_prefixes and not current_page_has_cont:
                working_div_data[current_sec_id]['name_parts'].extend(current_page_prefixes)

    except FileNotFoundError:
        print(f"Error: Could not find file {pdf_path}")
        sys.exit(1)

    # --- Missing Totals Fallback (For single-transaction securities omitting a total line) ---
    for sec_id, data in working_div_data.items():
        if data['transactions'] and not data['totals']:
            if len(data['transactions']) == 1:
                tx = data['transactions'][0]
                t_type = tx['type'].lower()
                if 'exempt' in t_type:
                    data['totals']['Total Tax-exempt dividends'] = tx['amount']
                elif 'foreign' in t_type:
                    data['totals']['Total Foreign tax withheld'] = tx['amount']
                else:
                    data['totals']['Total Dividends & distributions'] = tx['amount']
            else:
                div_total, exempt_total, foreign_total = 0.0, 0.0, 0.0
                for tx in data['transactions']:
                    t_type = tx['type'].lower()
                    if 'exempt' in t_type:
                        exempt_total += tx['amount']
                    elif 'foreign' in t_type:
                        foreign_total += tx['amount']
                    elif '199a' not in t_type: # Skip subsets to avoid double counting
                        div_total += tx['amount']
                
                if exempt_total > 0: data['totals']['Total Tax-exempt dividends'] = exempt_total
                if foreign_total > 0: data['totals']['Total Foreign tax withheld'] = foreign_total
                if div_total > 0: data['totals']['Total Dividends & distributions'] = div_total
    # ------------------------------------------------------------------------------------------

    dividends_data = defaultdict(lambda: {'cusip': '', 'transactions': [], 'totals': defaultdict(float), 'supplemental': {}})
    for sec_id, data in working_div_data.items():
        if not data['name_parts']: continue
        clean_name = clean_sec_name(data['name_parts'])
        if dividends_data[clean_name]['cusip'] == '':
            dividends_data[clean_name]['cusip'] = data['cusip']
            dividends_data[clean_name]['supplemental'] = data['supplemental']
        dividends_data[clean_name]['transactions'].extend(data['transactions'])
        for k, v in data['totals'].items(): dividends_data[clean_name]['totals'][k] += v
        
        for k, is_c in correction_flags['securities'][sec_id].items():
            if is_c: correction_flags['securities'][clean_name][k] = True

    for supp in supplemental_extracted:
        matched_sec = next((k for k, v in dividends_data.items() if (v['cusip'] and v['cusip'] == supp['cusip']) or (supp['name'] != 'UNKNOWN' and k.upper() == supp['name'].upper())), None)
        if matched_sec:
            if supp['fed_pct'] is not None: dividends_data[matched_sec]['supplemental']['fed_pct'] = supp['fed_pct']
            if supp['ny_pct'] is not None: dividends_data[matched_sec]['supplemental']['ny_pct'] = supp['ny_pct']

    # Auto-save dynamically discovered Fed percentages from the PDF to the CSV
    if fed_csv_path and not is_comparison:
        new_pcts_saved = 0
        try:
            with open(fed_csv_path, 'a', newline='', encoding='utf-8') as f:
                writer = csv.writer(f)
                for supp in supplemental_extracted:
                    if supp.get('fed_pct') is not None and supp.get('cusip'):
                        if supp['cusip'] not in fed_csv_data:
                            writer.writerow([supp['cusip'], f"{supp['fed_pct'] * 100.0:.2f}"])
                            fed_csv_data[supp['cusip']] = supp['fed_pct']
                            new_pcts_saved += 1
            if new_pcts_saved > 0:
                cprint(f"    [+] Auto-saved {new_pcts_saved} newly discovered Fed percentage(s) to '{fed_csv_path}'", COLOR_GREEN)
        except IOError as e:
            cprint(f"    [!] Error auto-saving to {fed_csv_path}: {e}", COLOR_RED)

    if fed_csv_data:
        for k, v in dividends_data.items():
            override = fed_csv_data.get(v['cusip']) or fed_csv_data.get(k.upper()) or next((ov for mk, ov in fed_csv_data.items() if k.upper().startswith(mk)), None)
            if override is not None: v['supplemental']['fed_pct'] = override

    if debug:
        debug_log["dividends_and_supplemental"] = {k: dict(v) for k, v in dividends_data.items() if v['transactions']}
        debug_log["document_grand_totals"] = info_1099['grand_totals']
        debug_log["corrections_detected"] = {
            'info_1099': dict(correction_flags['info_1099']),
            'grand_totals': dict(correction_flags['grand_totals']),
            'securities': {k: dict(v) for k, v in correction_flags['securities'].items()}
        }
        if log_filepath:
            try:
                with open(log_filepath, 'w', encoding='utf-8') as f: json.dump(debug_log, f, indent=2)
            except IOError as e: cprint(f"[!] Error writing debug JSON log: {e}", COLOR_RED)

    return transactions, summary_expected, dividends_data, info_1099, correction_flags, statement_date

def print_single_summary_grid(info_1099, correction_flags, statement_date, use_color=True):
    c_c, c_res = (COLOR_CYAN, COLOR_RESET) if use_color else ("", "")
    print(f"\n{c_c}[1099-DIV Summary Boxes]{c_res}")
    
    fields = {
        '1a': '1a- Total ordinary dividends',
        '1b': '1b- Qualified dividends',
        '2a': '2a- Total capital gain',
        '2b': '2b- Unrecaptured Section 1250',
        '3':  ' 3- Nondividend distributions',
        '5':  ' 5- Section 199A',
        '12': '12- Exempt-interest dividends'
    }
    
    h_flag = f"{'C_Flagged':<9}"
    h_box = f"{'Box':<30}"
    h_val = f"{'Value':<12}"
    
    print(f"{h_flag}\t{h_box}\t{h_val}")
    
    total_val = 0.0
    for k, label in fields.items():
        if info_1099[k] != 0.0:
            is_flagged = "Yes" if correction_flags['info_1099'].get(k, False) else "No"
            print(f"{is_flagged:>9}\t{label:<30}\t{info_1099[k]:>12.2f}")
            if k in ['1a', '2a', '3', '12']:
                total_val += info_1099[k]
            
    print(f"{'':>9}\t{'Total dividend line':<30}\t{total_val:>12.2f}")

def print_corrected_items(correction_flags, transactions, dividends_data, use_color=True):
    c_y, c_res = (COLOR_YELLOW, COLOR_RESET) if use_color else ("", "")
    print(f"\n{c_y}--- Corrected Items Detected ('C' Marker) ---{c_res}")
    
    found_any = False
    
    if any(correction_flags['info_1099'].values()):
        found_any = True
        print("  [1099-DIV Summary Boxes]")
        for k, is_c in correction_flags['info_1099'].items():
            if is_c: print(f"    - Box {k}")
            
    if any(correction_flags['grand_totals'].values()):
        found_any = True
        print("  [Document Grand Totals]")
        for k, is_c in correction_flags['grand_totals'].items():
            if is_c: print(f"    - {k}")
            
    if correction_flags['securities']:
        sec_found = False
        for sec, flags in correction_flags['securities'].items():
            if any(flags.values()):
                if not sec_found:
                    print("  [Security Totals]")
                    sec_found = True
                    found_any = True
                for k, is_c in flags.items():
                    if is_c: print(f"    - {sec}: {k}")
                    
    div_tx_found = False
    for sec, data in dividends_data.items():
        for t in data['transactions']:
            if t.get('corrected'):
                if not div_tx_found:
                    print("  [Dividend Transactions]")
                    div_tx_found = True
                    found_any = True
                print(f"    - {sec} | Date: {t['date']} | Amount: {t['amount']} ({t['type']})")
                
    tx_found = False
    for tx in transactions:
        if tx.get('corrected'):
            if not tx_found:
                print("  [1099-B Sales Transactions]")
                tx_found = True
                found_any = True
            desc_short = tx['base_description'][:25] + "..." if len(tx['base_description']) > 25 else tx['base_description']
            print(f"    - Box {tx['box']} | {desc_short} | Sold: {tx['date_sold']} | Qty: {tx['quantity']}")
                    
    if not found_any:
        print("  No correction markers found.")

def compare_statements(p_info, p_divs, p_tx, c_info, c_divs, c_tx, p_path, c_path, prefix_str, correction_flags, p_date, c_date, log_filepath=None, use_color=True):
    c_c, c_y, c_g, c_r, c_res = (COLOR_CYAN, COLOR_YELLOW, COLOR_GREEN, COLOR_RED, COLOR_RESET) if use_color else ("", "", "", "", "")
    
    txt_log_path = f"{prefix_str}comparison.txt"
    csv_log_path = f"{prefix_str}comparison.csv"
    
    txt_file = open(txt_log_path, 'w', encoding='utf-8')
    ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
    
    def cmp_print(msg):
        print(msg)
        txt_file.write(ansi_escape.sub('', msg) + '\n')
    
    cmp_print(f"\n{c_c}--- STATEMENT COMPARISON (Previous vs Current) ---{c_res}")
    
    diff_log = []
    def log_diff(section, desc, old_val, new_val, c_flagged):
        msg = f"  {desc}:\n    From: {old_val}\n    To  : {new_val}\n    C_Flagged: {c_flagged}"
        cmp_print(msg)
        diff_log.append({"section": section, "description": desc, "previous": old_val, "current": new_val, "C_Flagged": c_flagged})

    # 1. Summary Compare (Spreadsheet Ready Grid)
    cmp_print("\n[1099-DIV Summary Boxes]")
    
    fields = {
        '1a': '1a- Total ordinary dividends',
        '1b': '1b- Qualified dividends',
        '2a': '2a- Total capital gain',
        '2b': '2b- Unrecaptured Section 1250',
        '3':  ' 3- Nondividend distributions',
        '5':  ' 5- Section 199A',
        '12': '12- Exempt-interest dividends'
    }
    
    h_flag = f"{'C_Flagged':<9}"
    h_box = f"{'Box':<30}"
    h_d1 = f"{p_date:<12}"
    h_d2 = f"{c_date:<12}"
    h_diff = f"{'Difference':<12}"
    
    cmp_print(f"{h_flag}\t{h_box}\t{h_d1}\t{h_d2}\t{h_diff}")
    
    total_p = 0.0
    total_c = 0.0
    
    for k, label in fields.items():
        if p_info[k] != 0.0 or c_info[k] != 0.0:
            is_flagged = "Yes" if correction_flags['info_1099'].get(k, False) else "No"
            
            diff_val = c_info[k] - p_info[k]
            if abs(diff_val) < 0.005: diff_val = 0.0
            
            diff_str_padded = f"{diff_val:>12.2f}"
            if diff_val > 0: diff_str = f"{c_g}{diff_str_padded}{c_res}"
            elif diff_val < 0: diff_str = f"{c_r}{diff_str_padded}{c_res}"
            else: diff_str = diff_str_padded
            
            cmp_print(f"{is_flagged:>9}\t{label:<30}\t{p_info[k]:>12.2f}\t{c_info[k]:>12.2f}\t{diff_str}")
            
            if k in ['1a', '2a', '3', '12']:
                total_p += p_info[k]
                total_c += c_info[k]
            
            if p_info[k] != c_info[k]:
                diff_log.append({"section": "1099-DIV Summary", "description": label, "previous": p_info[k], "current": c_info[k], "C_Flagged": is_flagged})

    total_diff = total_c - total_p
    if abs(total_diff) < 0.005: total_diff = 0.0
    tot_diff_padded = f"{total_diff:>12.2f}"
    if total_diff > 0: tot_diff_str = f"{c_g}{tot_diff_padded}{c_res}"
    elif total_diff < 0: tot_diff_str = f"{c_r}{tot_diff_padded}{c_res}"
    else: tot_diff_str = tot_diff_padded

    cmp_print(f"{'':>9}\t{'Total dividend line':<30}\t{total_p:>12.2f}\t{total_c:>12.2f}\t{tot_diff_str}")

    # 2. Grand Totals Compare
    cmp_print("\n[Document Grand Totals]")
    has_gt_diff = False
    for k in c_info['grand_totals']:
        p_val = p_info['grand_totals'].get(k, 0.0)
        c_val = c_info['grand_totals'].get(k, 0.0)
        if p_val != c_val:
            is_flagged = "Yes" if correction_flags['grand_totals'].get(k, False) else "No"
            log_diff("Grand Totals", k, p_val, c_val, is_flagged)
            has_gt_diff = True
    if not has_gt_diff: cmp_print("  No changes.")

    # 3. Dividend Transaction Detail Recharacterization Compare
    cmp_print("\n[Dividend Transaction Detail Changes]")
    has_div_tx_diff = False
    all_secs = set(p_divs.keys()).union(c_divs.keys())
    for sec in sorted(all_secs):
        p_txs = p_divs.get(sec, {}).get('transactions', [])
        c_txs = c_divs.get(sec, {}).get('transactions', [])
        
        if not p_txs and not c_txs: continue
        
        p_by_date = defaultdict(list)
        for t in p_txs: p_by_date[t['date']].append(t)
        
        c_by_date = defaultdict(list)
        for t in c_txs: c_by_date[t['date']].append(t)
        
        all_dates = sorted(set(p_by_date.keys()).union(c_by_date.keys()), key=lambda d: d[6:8]+d[0:2]+d[3:5])
        
        for date in all_dates:
            p_list = p_by_date[date]
            c_list = c_by_date[date]
            
            p_breakdown = ", ".join([f"${x['amount']:.2f} ({x['type']})" for x in p_list])
            c_breakdown = ", ".join([f"${x['amount']:.2f} ({x['type']})" for x in c_list])
            
            if p_breakdown == c_breakdown: continue
            
            p_sum = sum(x['amount'] for x in p_list)
            c_sum = sum(x['amount'] for x in c_list)
            
            is_flagged = "Yes" if any(x.get('corrected', False) for x in c_list) else "No"
            
            diff = abs(p_sum - c_sum)
            if diff < 0.02 and len(p_list) > 0 and len(c_list) > 0:
                log_diff("Dividend Detail", f"{sec} on {date}", f"Total ${p_sum:.2f} [ {p_breakdown} ]", f"Total ${c_sum:.2f} (Recharacterized) [ {c_breakdown} ]", is_flagged)
                has_div_tx_diff = True
            else:
                log_diff("Dividend Detail", f"{sec} on {date}", f"Total ${p_sum:.2f} [ {p_breakdown} ]" if p_list else "None", f"Total ${c_sum:.2f} [ {c_breakdown} ]" if c_list else "None", is_flagged)
                has_div_tx_diff = True
    if not has_div_tx_diff: cmp_print("  No changes.")

    # 4. 1099-B Proceeds Transaction Compare
    cmp_print("\n[1099-B Proceeds from Broker Transactions]")
    has_1099b_diff = False
    
    p_tx_map = defaultdict(list)
    for tx in p_tx:
        key = f"{tx['box']}|{tx['base_description']}|{tx['date_sold']}|{tx['quantity']}"
        p_tx_map[key].append(tx)
        
    c_tx_map = defaultdict(list)
    for tx in c_tx:
        key = f"{tx['box']}|{tx['base_description']}|{tx['date_sold']}|{tx['quantity']}"
        c_tx_map[key].append(tx)
        
    all_tx_keys = sorted(set(p_tx_map.keys()).union(c_tx_map.keys()))
    
    for key in all_tx_keys:
        p_list = p_tx_map[key]
        c_list = c_tx_map[key]
        
        max_len = max(len(p_list), len(c_list))
        for i in range(max_len):
            p_item = p_list[i] if i < len(p_list) else None
            c_item = c_list[i] if i < len(c_list) else None
            
            parts = key.split('|')
            desc_short = parts[1][:25] + "..." if len(parts[1]) > 25 else parts[1]
            row_label = f"Box {parts[0]} | {desc_short} | Sold: {parts[2]} | Qty: {parts[3]}"
            
            is_flagged = "Yes" if (c_item and c_item.get('corrected', False)) else "No"
            
            if p_item and c_item:
                changes = []
                for f in ['proceeds', 'cost_basis', 'gain_loss', 'adjustments']:
                    if abs(clean_num(p_item[f]) - clean_num(c_item[f])) > 0.01:
                        changes.append(f"{f}: {p_item[f]} -> {c_item[f]}")
                
                if changes:
                    change_str = ", ".join(changes)
                    log_diff("1099-B Detail", row_label, "Previous Values", f"Changed: {change_str}", is_flagged)
                    has_1099b_diff = True
            elif not p_item and c_item:
                log_diff("1099-B Detail", row_label, "Not Present", f"Added (Proceeds: {c_item['proceeds']}, Gain/Loss: {c_item['gain_loss']})", is_flagged)
                has_1099b_diff = True
            elif p_item and not c_item:
                log_diff("1099-B Detail", row_label, f"Present (Proceeds: {p_item['proceeds']}, Gain/Loss: {p_item['gain_loss']})", "Removed", is_flagged)
                has_1099b_diff = True
                
    if not has_1099b_diff: cmp_print("  No changes.")
    
    # Write Dedicated CSV Output
    if diff_log:
        try:
            with open(csv_log_path, 'w', newline='', encoding='utf-8') as f:
                writer = csv.DictWriter(f, fieldnames=["section", "description", "previous", "current", "C_Flagged"])
                writer.writeheader()
                writer.writerows(diff_log)
            cmp_print(f"\n    [+] Created: {csv_log_path} ({len(diff_log)} changes tracked)")
        except IOError as e:
            cmp_print(f"    [!] Error writing {csv_log_path}: {e}")
    
    # 5. Raw Text Diff Fallback
    cmp_print(f"\n{c_y}--- RAW TEXT DIFFERENCES (Exempting Statement Date & 'CORRECTED') ---{c_res}")
    p_lines = get_clean_pdf_lines(p_path)
    c_lines = get_clean_pdf_lines(c_path)
    
    diff = list(difflib.unified_diff(p_lines, c_lines, fromfile='Original', tofile='Corrected', lineterm=''))
    if not diff:
        cmp_print("  No raw text differences found.")
    else:
        for line in diff:
            if line.startswith('---') or line.startswith('+++') or line.startswith('@@'):
                continue
            if line.startswith('-'): cmp_print(f"{c_r}{line}{c_res}")
            elif line.startswith('+'): cmp_print(f"{c_g}{line}{c_res}")
            
    cmp_print("")
    txt_file.close()
    
    if log_filepath and diff_log:
        try:
            with open(log_filepath, 'r+', encoding='utf-8') as f:
                data = json.load(f)
                data['comparison_diff'] = diff_log
                f.seek(0)
                json.dump(data, f, indent=2)
                f.truncate()
        except (IOError, json.JSONDecodeError): pass

def prompt_for_missing_fed_pct(dividends_data, fed_csv_path, use_color=True):
    for sec_name, data in dividends_data.items():
        cusip = data.get('cusip', '')
        
        is_known = False
        for k_cusip, k_name in KNOWN_GOVT_FUNDS.items():
            if cusip.startswith(k_cusip) or sec_name.strip().upper().startswith(k_name):
                is_known = True
                break
                
        if is_known and 'fed_pct' not in data['supplemental']:
            c_y, c_res, c_g, c_r = (COLOR_YELLOW, COLOR_RESET, COLOR_GREEN, COLOR_RED) if use_color else ("", "", "", "")
            print(f"\n{c_y}[!] Supplemental information missing for:{c_res}\n    Security: {sec_name}\n    CUSIP   : {cusip}")
            while True:
                try:
                    val = input(f"Please enter the Fed Source percentage (e.g., 50 for 50%) or press Enter to skip: ").strip()
                    if not val: break
                    pct = float(val) / 100.0
                    data['supplemental']['fed_pct'] = pct
                    print(f"{c_g}Recorded Fed Source Percentage as {float(val):.2f}%{c_res}")
                    
                    if fed_csv_path:
                        try:
                            with open(fed_csv_path, 'a', newline='', encoding='utf-8') as f:
                                writer = csv.writer(f)
                                save_key = cusip if cusip else sec_name
                                writer.writerow([save_key, val])
                            print(f"{c_g}Saved '{save_key}' to '{fed_csv_path}' for future runs.{c_res}")
                        except IOError as e:
                            print(f"{c_r}Error saving to {fed_csv_path}: {e}{c_res}")
                    break
                except ValueError: print(f"{c_r}Invalid input.{c_res}")

def perform_dividend_cross_checks(dividends_data, info_1099, prefix_str, use_color=True):
    print("\n--- Cross-Check vs Dividend & Tax-Exempt Summaries ---")
    ov_divs = sum(d['totals'].get('Total Dividends & distributions', 0.0) for d in dividends_data.values())
    ov_exempt = sum(d['totals'].get('Total Tax-exempt dividends', 0.0) for d in dividends_data.values())
    
    sum_div_f = info_1099['1a'] + info_1099['2a'] + info_1099['3']
    
    grand_div = info_1099['grand_totals']['Total Dividends & distributions']
    grand_exempt = info_1099['grand_totals']['Total Tax-exempt dividends']
    
    c_green, c_red, c_reset = (COLOR_GREEN, COLOR_RED, COLOR_RESET) if use_color else ("", "", "")

    for label, src1_label, s1, s2, s3, tag, file_suffix in [
        ("Total Dividends & distributions", "DIV 1a+2a+3", sum_div_f, ov_divs, grand_div, 'Total Dividends & distributions', 'dividends.csv'),
        ("Total Tax-exempt dividends", "DIV 12", info_1099['12'], ov_exempt, grand_exempt, 'Total Tax-exempt dividends', 'tax_exempt.csv')
    ]:
        print(f"\n[{label}]")
        print(f"  Source 1: {src1_label:<25} : {s1:>12.2f}")
        print(f"  Source 2: {'Securities Sub Totals Sum':<25} : {s2:>12.2f}")
        print(f"  Source 3: {'Detail Grand Total':<25} : {s3:>12.2f}")
        
        vals = [s1, s2]
        if s3 > 0 or s3 < 0: vals.append(s3)
        diff = max(vals) - min(vals)
        
        if diff < 0.02: 
            status = f"{c_green}MATCH{c_reset}"
        else:
            status = f"{c_red}MISMATCH (diff: {diff:.2f}){c_reset}"
            
        print(f"  Status  : {'':<25}   {status}")
        write_category_totals_csv(f"{prefix_str}{file_suffix}", dividends_data, tag)
    print("\n------------------------------------------------------\n")

def write_category_totals_csv(filename, dividends_data, target_key):
    rows = [{'Security Name': k, 'CUSIP': v['cusip'], 'Amount': f"{v['totals'].get(target_key, 0.0):.2f}"} for k, v in dividends_data.items() if v['totals'].get(target_key, 0.0) != 0]
    overall_total = sum(v['totals'].get(target_key, 0.0) for v in dividends_data.values())
    rows.append({'Security Name': 'OVERALL TOTAL', 'CUSIP': '', 'Amount': f"{overall_total:.2f}"})
    try:
        with open(filename, mode='w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=['Security Name', 'CUSIP', 'Amount'])
            writer.writeheader()
            writer.writerows(rows)
        print(f"    [+] Created: {filename}")
    except IOError as e:
        print(f"    [!] Error writing {filename}: {e}")

def write_supplemental_csvs(dividends_data, prefix_str, threshold=0.0):
    fed_rows = []
    for k, v in dividends_data.items():
        tot_div = v['totals'].get("Total Dividends & distributions", 0.0)
        fed_pct = v['supplemental'].get("fed_pct")
        if tot_div > 0 and fed_pct is not None and (fed_pct * 100) >= threshold:
            calc_div = tot_div * fed_pct
            fed_rows.append({'Security Name': k, 'CUSIP': v['cusip'], 'Total Amount': f"{tot_div:.2f}", 'Percentage': f"{fed_pct*100:.2f}%", 'Calculated': f"{calc_div:.2f}"})
            
    if fed_rows:
        filename = f"{prefix_str}us_securities_state_exempt_box20.csv"
        try:
            with open(filename, mode='w', newline='', encoding='utf-8') as f:
                w = csv.DictWriter(f, fieldnames=['Security Name', 'CUSIP', 'Total Amount', 'Percentage', 'Calculated'])
                w.writeheader()
                w.writerows(fed_rows)
                w.writerow({'Security Name': 'OVERALL TOTAL', 'CUSIP': '', 'Total Amount': f"{sum(float(r['Total Amount']) for r in fed_rows):.2f}", 'Percentage': '', 'Calculated': f"{sum(float(r['Calculated']) for r in fed_rows):.2f}"})
            print(f"    [+] Created: {filename} ({len(fed_rows)} securities, >= {threshold}% threshold applied)")
        except IOError as e: print(f"Error writing {filename}: {e}")

    ny_rows = []
    for k, v in dividends_data.items():
        tot_exempt = v['totals'].get("Total Tax-exempt dividends", 0.0)
        ny_pct = v['supplemental'].get("ny_pct")
        if tot_exempt > 0 and ny_pct is not None:
            calc_exempt = tot_exempt * ny_pct
            ny_rows.append({'Security Name': k, 'CUSIP': v['cusip'], 'Total Amount': f"{tot_exempt:.2f}", 'Percentage': f"{ny_pct*100:.2f}%", 'Calculated': f"{calc_exempt:.2f}"})
            
    if ny_rows:
        filename = f"{prefix_str}fed_exempt_state_exempt_box21.csv"
        try:
            with open(filename, mode='w', newline='', encoding='utf-8') as f:
                w = csv.DictWriter(f, fieldnames=['Security Name', 'CUSIP', 'Total Amount', 'Percentage', 'Calculated'])
                w.writeheader()
                w.writerows(ny_rows)
                w.writerow({'Security Name': 'OVERALL TOTAL', 'CUSIP': '', 'Total Amount': f"{sum(float(r['Total Amount']) for r in ny_rows):.2f}", 'Percentage': '', 'Calculated': f"{sum(float(r['Calculated']) for r in ny_rows):.2f}"})
            print(f"    [+] Created: {filename} ({len(ny_rows)} securities)")
        except IOError as e: print(f"Error writing {filename}: {e}")

def cross_check(transactions, expected_summary, use_color=True):
    print("\n--- Cross-Check vs 1099-B Statement Summary ---")
    calculated = defaultdict(lambda: {'proceeds': 0.0, 'cost_basis': 0.0, 'adjustments': 0.0, 'gain_loss': 0.0})
    for tx in transactions:
        b = tx['box']
        calculated[b]['proceeds'] += clean_num(tx['proceeds'])
        calculated[b]['cost_basis'] += clean_num(tx['cost_basis'])
        calculated[b]['adjustments'] += clean_num(tx['adjustments'])
        calculated[b]['gain_loss'] += clean_num(tx['gain_loss'])
        
    all_match = True
    for box in [box for box in expected_summary.keys() if box in ['A', 'B', 'C', 'D', 'E', 'F']]:
        expected = expected_summary[box]
        calc = calculated[box]
        print(f"\nBox {box}:")
        for field in ['proceeds', 'cost_basis', 'adjustments', 'gain_loss']:
            diff = abs(expected[field] - calc[field])
            if diff < 0.02: status = f"{COLOR_GREEN}MATCH{COLOR_RESET}" if use_color else "MATCH"
            else:
                status = f"{COLOR_RED}MISMATCH (diff: {diff:.2f}){COLOR_RESET}" if use_color else f"MISMATCH (diff: {diff:.2f})"
                all_match = False
            print(f"  {field.capitalize():<12} | Expected: {expected[field]:>10.2f} | Parsed: {calc[field]:>10.2f} | {status}")
            
    print("\n-------------------------------------------------")
    if all_match: print(f"{COLOR_GREEN}SUCCESS: All parsed 1099-B totals match the statement summary.{COLOR_RESET}" if use_color else "SUCCESS: All parsed 1099-B totals match the statement summary.")
    else: print(f"{COLOR_RED}WARNING: 1099-B Cross-check failed! Parsed data does not match summary.{COLOR_RESET}" if use_color else "WARNING: 1099-B Cross-check failed! Parsed data does not match summary.")

def main():
    parser = argparse.ArgumentParser(description="Parse Brokerage 1099-B and Dividend statements.")
    parser.add_argument("pdf", help="Path to the current 1099 PDF file.")
    parser.add_argument("--original", type=str, help="Path to the original (previous) 1099 PDF file to compare changes against.")
    parser.add_argument("--boxes", type=str, default="A,B,C,D,E,F", help="Comma-separated list of boxes to extract.")
    parser.add_argument("--output", type=str, default="1099b_data.csv", help="Output CSV filename for 1099-B data.")
    parser.add_argument("--fed-csv", type=str, help="Path to a CSV file containing Fed source percentage overrides.")
    parser.add_argument("--box20-threshold", type=float, default=50.0, help="Minimum percentage (0-100) of Fed source income required to be included in the Box 20 CSV.")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug logging to a categorized JSON file.")
    parser.add_argument("--log-file", type=str, default="parser_debug.json", help="Path for the debug log file.")
    args = parser.parse_args()

    target_boxes = [b.strip().upper() for b in args.boxes.split(',')]
    use_color = not getattr(args, 'no_color', False)

    base_pdf_name = os.path.basename(args.pdf)
    clean_prefix = os.path.splitext(base_pdf_name)[0].replace('1099_', '').replace('1099', '').strip('_-')
    prefix_str = f"{clean_prefix}_" if clean_prefix else ""
    
    original_stdout = sys.stdout
    logger = MultiLogger(prefix_str)
    sys.stdout = logger
    
    actual_output_file, actual_log_file = f"{prefix_str}{args.output}", f"{prefix_str}{args.log_file}" if args.log_file else None
    
    default_fed_csv = "fed_percentages.csv"
    fed_csv_path = args.fed_csv
    
    if fed_csv_path:
        if not os.path.exists(fed_csv_path):
            print(f"{COLOR_RED}[!] ERROR: The specified Fed percentage file '{fed_csv_path}' does not exist.{COLOR_RESET}")
            sys.stdout = original_stdout
            logger.close()
            sys.exit(1)
        print(f"{COLOR_CYAN}Found manually specified Fed percentage file: {fed_csv_path}{COLOR_RESET}")
    else:
        if os.path.exists(default_fed_csv):
            fed_csv_path = default_fed_csv
            print(f"{COLOR_CYAN}Found default Fed percentage file: {default_fed_csv}{COLOR_RESET}")
        else:
            print(f"{COLOR_YELLOW}[!] Default Fed percentage file '{default_fed_csv}' not found. A template has been created at that path.{COLOR_RESET}")
            try:
                with open(default_fed_csv, 'w', newline='', encoding='utf-8') as f:
                    writer = csv.writer(f)
                    writer.writerow(["CUSIP or Description", "Fed source percentage"])
            except IOError as e:
                print(f"{COLOR_RED}Error creating template: {e}{COLOR_RESET}")
            fed_csv_path = default_fed_csv 
            
    # ---------------------------------------------------------
    # COMPARISON RUN BYPASS: This block strictly isolated.
    # ---------------------------------------------------------
    prev_info, prev_divs, prev_tx, prev_date = None, None, None, None
    if args.original:
        if not os.path.exists(args.original):
            print(f"{COLOR_RED}[!] ERROR: Original file '{args.original}' does not exist.{COLOR_RESET}")
            sys.stdout = original_stdout
            logger.close()
            sys.exit(1)
            
        print(f"\n{COLOR_YELLOW}=== PARSING ORIGINAL STATEMENT FOR COMPARISON ==={COLOR_RESET}" if use_color else "\n=== PARSING ORIGINAL STATEMENT FOR COMPARISON ===")
        prev_tx, _, prev_divs, prev_info, _, prev_date = parse_statement(
            args.original, target_boxes, fed_csv_path=fed_csv_path, debug=False, log_filepath=None, use_color=use_color, is_comparison=True
        )
    # ---------------------------------------------------------
    
    transactions, expected_summary, dividends_data, info_1099, c_flags, curr_date = parse_statement(
        args.pdf, target_boxes, fed_csv_path=fed_csv_path, debug=args.debug, log_filepath=actual_log_file if args.debug else None, use_color=use_color
    )

    print_corrected_items(c_flags, transactions, dividends_data, use_color=use_color)
    
    # Strictly isolated doc comparison block
    if args.original:
        compare_statements(prev_info, prev_divs, prev_tx, info_1099, dividends_data, transactions, p_path=args.original, c_path=args.pdf, prefix_str=prefix_str, correction_flags=c_flags, p_date=prev_date, c_date=curr_date, log_filepath=actual_log_file if args.debug else None, use_color=use_color)
    else:
        print_single_summary_grid(info_1099, c_flags, curr_date, use_color=use_color)

    prompt_for_missing_fed_pct(dividends_data, fed_csv_path, use_color=use_color)

    if transactions:
        with open(actual_output_file, mode='w', newline='', encoding='utf-8') as csv_file:
            writer = csv.DictWriter(csv_file, fieldnames=['box', 'description', 'date_sold', 'quantity', 'proceeds', 'date_acquired', 'cost_basis', 'adjustments', 'gain_loss'])
            writer.writeheader()
            for tx in transactions: writer.writerow({k: tx.get(k, '') for k in ['box', 'description', 'date_sold', 'quantity', 'proceeds', 'date_acquired', 'cost_basis', 'adjustments', 'gain_loss']})
        print(f"\nCreated: {actual_output_file} ({len(transactions)} 1099-B transactions)")
        cross_check(transactions, expected_summary, use_color=use_color)
        
        summary_1099b = defaultdict(lambda: {
            'date_sold_set': set(),
            'date_acquired_set': set(),
            'base_desc_set': set(),
            'quantity': 0.0,
            'proceeds': 0.0,
            'cost_basis': 0.0,
            'adjustments': 0.0,
            'gain_loss': 0.0
        })
        for tx in transactions:
            b = tx['box']
            summary_1099b[b]['date_sold_set'].add(tx['date_sold'])
            summary_1099b[b]['date_acquired_set'].add(tx['date_acquired'])
            summary_1099b[b]['base_desc_set'].add(tx['base_description'])
            summary_1099b[b]['quantity'] += clean_num(tx['quantity'])
            summary_1099b[b]['proceeds'] += clean_num(tx['proceeds'])
            summary_1099b[b]['cost_basis'] += clean_num(tx['cost_basis'])
            summary_1099b[b]['adjustments'] += clean_num(tx['adjustments'])
            summary_1099b[b]['gain_loss'] += clean_num(tx['gain_loss'])

        summary_file = f"{prefix_str}1099b_summary.csv"
        try:
            with open(summary_file, mode='w', newline='', encoding='utf-8') as f:
                writer = csv.DictWriter(f, fieldnames=['box', 'description', 'date_sold', 'quantity', 'proceeds', 'date_acquired', 'cost_basis', 'adjustments', 'gain_loss'])
                writer.writeheader()
                for b in sorted(summary_1099b.keys()):
                    data = summary_1099b[b]
                    ds = list(data['date_sold_set'])[0] if len(data['date_sold_set']) == 1 else "VARIOUS"
                    da = list(data['date_acquired_set'])[0] if len(data['date_acquired_set']) == 1 else "VARIOUS"
                    
                    if len(data['base_desc_set']) == 1:
                        base_desc = list(data['base_desc_set'])[0]
                        qty_sum_str = f"{data['quantity']:.4f}".rstrip('0').rstrip('.')
                        desc = f"{qty_sum_str} {base_desc}"
                    else:
                        desc = "VARIOUS"

                    writer.writerow({
                        'box': b,
                        'description': desc,
                        'date_sold': ds,
                        'quantity': f"{data['quantity']:.4f}",
                        'proceeds': f"{data['proceeds']:.2f}",
                        'date_acquired': da,
                        'cost_basis': f"{data['cost_basis']:.2f}",
                        'adjustments': f"{data['adjustments']:.2f}",
                        'gain_loss': f"{data['gain_loss']:.2f}"
                    })
            print(f"    [+] Created: {summary_file} ({len(summary_1099b)} box summaries)")
        except IOError as e:
            print(f"Error writing {summary_file}: {e}")
            
    else: print(f"{COLOR_YELLOW}No 1099-B transactions found.{COLOR_RESET}")

    if dividends_data:
        perform_dividend_cross_checks(dividends_data, info_1099, prefix_str, use_color=use_color)
        write_supplemental_csvs(dividends_data, prefix_str, threshold=args.box20_threshold)
        
    print(f"\n{COLOR_CYAN}Terminal output additionally logged to: {prefix_str}console_output.txt and {prefix_str}console_output_color.txt{COLOR_RESET}")
    
    sys.stdout = original_stdout
    logger.close()

if __name__ == "__main__":
    main()
