#!/usr/bin/env python3
import argparse
import csv
import re
import sys
import json
import os
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

def parse_val_and_c(val_str):
    """Parses a string into a float and detects if it has a 'C' (Corrected) flag."""
    if not val_str or val_str == '...': 
        return 0.0, False
    val_str_upper = val_str.upper()
    has_c = 'C' in val_str_upper
    try:
        # Strip everything except digits, decimals, and negative signs
        clean_str = re.sub(r'[^\d\.\-]', '', val_str)
        return float(clean_str), has_c
    except ValueError:
        return 0.0, False

def clean_num(val):
    return parse_val_and_c(val)[0]

def clean_sec_name(name_parts):
    """Joins buffered name parts and strips continuation markers and stray dates."""
    name = " ".join(name_parts)
    name = re.sub(r'\(cont.*?\)', '', name, flags=re.IGNORECASE)
    name = re.sub(r'\b\d{2}/\d{2}/\d{2}\b', '', name)
    return re.sub(r'\s{2,}', ' ', name).strip()

def parse_statement(pdf_path, target_boxes, fed_csv_path=None, debug=False, log_filepath=None, use_color=True):
    transactions = []
    summary_expected = {}
    supplemental_extracted = []
    
    info_1099 = {
        '1a': {'val': 0.0, 'c': False}, '1b': {'val': 0.0, 'c': False}, 
        '2a': {'val': 0.0, 'c': False}, '2b': {'val': 0.0, 'c': False}, 
        '3': {'val': 0.0, 'c': False}, '5': {'val': 0.0, 'c': False}, 
        '12': {'val': 0.0, 'c': False},
        'grand_totals': {
            'Total Dividends & distributions': {'val': 0.0, 'c': False},
            'Total Tax-exempt dividends': {'val': 0.0, 'c': False},
            'Total Foreign tax withheld': {'val': 0.0, 'c': False}
        }
    }
    
    working_div_data = defaultdict(lambda: {
        'name_parts': [],
        'cusip': '',
        'transactions': [],
        'totals': defaultdict(lambda: {'val': 0.0, 'c': False}),
        'supplemental': {}
    })
    
    debug_log = {
        "metadata": {"target_boxes": target_boxes, "method": "layout"},
        "summary_expected": {},
        "categories": {box: {"transactions": []} for box in target_boxes},
        "dividends_and_supplemental": {},
        "raw_pages": {}
    }

    def cprint(msg, color=None):
        if not msg: return
        if color and use_color: print(f"{color}{msg}{COLOR_RESET}")
        else: print(msg)

    if debug: cprint(f"=== PARSING: {pdf_path} ===", COLOR_CYAN)

    fed_csv_data = {}
    if fed_csv_path:
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
        except Exception:
            pass

    # Regexes updated to capture trailing C/c
    summary_row_pattern = re.compile(
        r'(B\s+or\s+E|C\s+or\s+F|A|B|C|D|E|F)\s*(?:\(basis.*?\)|\(Form.*?\))\s*'
        r'([\d,]+\.\d{2}\s*[cC]?)\s*([\d,]+\.\d{2}\s*[cC]?)\s*([\d,]+\.\d{2}\s*[cC]?)\s*([\d,]+\.\d{2}\s*[cC]?)\s*([-\d,]+\.\d{2}\s*[cC]?)', re.IGNORECASE
    )
    
    core_pattern = re.compile(
        r'(?P<dsold>\d{2}/\d{2}/\d{2})\s+(?P<qty>[\d,]+\.\d+\s*[cC]?)\s+(?P<proceeds>[\d,]+\.\d{2}\s*[cC]?)\s+'
        r'(?P<dacq>\d{2}/\d{2}/\d{2}|VARIOUS)\s+(?P<basis>[\d,]+\.\d{2}\s*[cC]?)\s*'
        r'(?P<adj>[-\d,]+\.\d{2}\s*[cC]?|\.\.\.)?\s*(?P<gl>[-\d,]+\.\d{2}\s*[cC]?)(?P<addl_info>[^\n]*)', re.IGNORECASE
    )

    div_row_pattern = re.compile(r'^(.*?)\s*(\d{2}/\d{2}/\d{2})\s+([-\d,]+\.\d{2}\s*[cC]?)\s+(.*)$')
    div_total_pattern = re.compile(
        r'^(.*?)\s*([-\d,]+\.\d{2}\s*[cC]?)\s+(Total Dividends & distributions|Total Tax-exempt dividends|Total Foreign tax withheld)', 
        re.IGNORECASE
    )
    
    supp_sec_pattern = re.compile(r'^([A-Z0-9\s\.\-\']+?)\s*/\s*([A-Z0-9]{9})(?:\s*/.*)?$')
    treasury_pattern = re.compile(r'U\.S\.\s*Treasury\s+([\d\.]+)')
    ny_pattern = re.compile(r'New York\s+([\d\.]+)')

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
                    cprint("\n[!] ERROR: pypdf is too old for layout extraction. Run: pip install --upgrade pypdf", COLOR_RED)
                    sys.exit(1)
                
                if not page_text: continue
                if debug: debug_log["raw_pages"][f"page_{page_num + 1}"] = page_text
                
                if "1099-DIV" in page_text.upper():
                    div_start_idx = page_text.upper().find("1099-DIV")
                    div_block = page_text[div_start_idx:]
                    for line_match in [
                        (r'1a-\s*Total ordinary dividends.{0,150}?([\d,]+\.\d{2}\s*[cC]?)', '1a'),
                        (r'1b-\s*Qualified dividends.{0,150}?([\d,]+\.\d{2}\s*[cC]?)', '1b'),
                        (r'2a-\s*Total capital gain distributions.{0,150}?([\d,]+\.\d{2}\s*[cC]?)', '2a'),
                        (r'2b-\s*Unrecaptured Section 1250 gain.{0,150}?([\d,]+\.\d{2}\s*[cC]?)', '2b'),
                        (r'3-\s*Nondividend distributions.{0,150}?([\d,]+\.\d{2}\s*[cC]?)', '3'),
                        (r'5-\s*Section 199A dividends.{0,150}?([\d,]+\.\d{2}\s*[cC]?)', '5'),
                        (r'12-\s*Exempt-interest dividends.{0,150}?([\d,]+\.\d{2}\s*[cC]?)', '12'),
                    ]:
                        m = re.search(line_match[0], div_block, re.DOTALL | re.IGNORECASE)
                        if m: 
                            val, has_c = parse_val_and_c(m.group(1))
                            if val > info_1099[line_match[1]]['val']:
                                info_1099[line_match[1]] = {'val': val, 'c': has_c}

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
                        'proceeds': parse_val_and_c(sum_match.group(2)), 
                        'cost_basis': parse_val_and_c(sum_match.group(3)),
                        'adjustments': parse_val_and_c(sum_match.group(4)),
                        'gain_loss': parse_val_and_c(sum_match.group(6))
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
                        
                        anchors = [r'Additional\s*information', r'also\s*not\s*reported\s*\(Z\)', r'alsonotreported\(Z\)', r'Original\s*basis:\s*\$[\d,]+\.\d{2}']
                        for anchor in anchors: between_text = re.split(anchor, between_text, flags=re.IGNORECASE)[-1]
                            
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
                            if new_sec: current_1099b_sec = new_sec
                        
                        qty_val, qty_c = parse_val_and_c(data['qty'])
                        qty_str = f"{qty_val}".rstrip('0').rstrip('.') if '.' in f"{qty_val}" else f"{qty_val}"
                        
                        base_desc = re.sub(r'\s*/\s*Symbol:?\s*$', '', current_1099b_sec, flags=re.IGNORECASE).strip()
                        formatted_desc = f"{qty_str} {base_desc}"
                        
                        tx = {
                            'box': box, 'description': formatted_desc, 'base_description': base_desc,
                            'date_sold': data['dsold'], 'date_acquired': data['dacq'],
                            'quantity': {'val': qty_val, 'c': qty_c},
                            'proceeds': {'val': parse_val_and_c(data['proceeds'])[0], 'c': parse_val_and_c(data['proceeds'])[1]},
                            'cost_basis': {'val': parse_val_and_c(data['basis'])[0], 'c': parse_val_and_c(data['basis'])[1]},
                            'gain_loss': {'val': parse_val_and_c(data['gl'])[0], 'c': parse_val_and_c(data['gl'])[1]}
                        }
                        transactions.append(tx)
                if box_headers: current_global_box = box_headers[-1]['box']

                for raw_line in lines:
                    line = raw_line.strip()
                    if not line: continue
                    
                    if in_div_section:
                        p_lower = line.lower()
                        if any(x in p_lower for x in ["security description", "detail for dividends", "page", "1099-div"]): continue
                            
                        ld = {}
                        tot_match = div_total_pattern.match(line)
                        row_match = div_row_pattern.match(line)
                        
                        if tot_match:
                            ld = {'type': 'total', 'prefix': tot_match.group(1).strip(), 'amount': tot_match.group(2), 'desc': tot_match.group(3).strip()}
                        elif row_match:
                            ld = {'type': 'transaction', 'prefix': row_match.group(1).strip(), 'date': row_match.group(2), 'amount': row_match.group(3), 'desc': row_match.group(4).strip()}
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
                            t_raw = ld['desc']
                            amt_val, amt_c = parse_val_and_c(ld['amount'])
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
                                if amt_val > info_1099['grand_totals'][t_type]['val']:
                                    info_1099['grand_totals'][t_type] = {'val': amt_val, 'c': amt_c}
                            else:
                                working_div_data[current_sec_id]['totals'][t_type] = {'val': amt_val, 'c': amt_c}
                                
                        elif ld['type'] == 'transaction' and current_sec_id:
                            amt_val, amt_c = parse_val_and_c(ld['amount'])
                            working_div_data[current_sec_id]['transactions'].append({
                                'date': ld['date'], 'amount': {'val': amt_val, 'c': amt_c}, 'type': ld['desc']
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

    dividends_data = defaultdict(lambda: {'cusip': '', 'transactions': [], 'totals': defaultdict(lambda: {'val':0.0, 'c':False}), 'supplemental': {}})
    for sec_id, data in working_div_data.items():
        if not data['name_parts']: continue
        clean_name = clean_sec_name(data['name_parts'])
        if dividends_data[clean_name]['cusip'] == '':
            dividends_data[clean_name]['cusip'] = data['cusip']
            dividends_data[clean_name]['supplemental'] = data['supplemental']
        dividends_data[clean_name]['transactions'].extend(data['transactions'])
        for k, v in data['totals'].items(): 
            dividends_data[clean_name]['totals'][k] = {'val': dividends_data[clean_name]['totals'][k]['val'] + v['val'], 'c': v['c']}

    for supp in supplemental_extracted:
        matched_sec = next((k for k, v in dividends_data.items() if v['cusip'] == supp['cusip'] or k.upper() == supp['name'].upper()), None)
        if matched_sec:
            if supp['fed_pct'] is not None: dividends_data[matched_sec]['supplemental']['fed_pct'] = supp['fed_pct']
            if supp['ny_pct'] is not None: dividends_data[matched_sec]['supplemental']['ny_pct'] = supp['ny_pct']

    if fed_csv_data:
        for k, v in dividends_data.items():
            override = fed_csv_data.get(v['cusip']) or fed_csv_data.get(k.upper()) or next((ov for mk, ov in fed_csv_data.items() if k.upper().startswith(mk)), None)
            if override is not None: v['supplemental']['fed_pct'] = override

    if debug and log_filepath:
        try:
            with open(log_filepath, 'w', encoding='utf-8') as f: json.dump(debug_log, f, indent=2)
        except IOError: pass

    return transactions, summary_expected, dividends_data, info_1099

def compare_statements(curr_tx, curr_info, curr_divs, orig_tx, orig_info, orig_divs, log_path, use_color=True):
    c_red = COLOR_RED if use_color else ""
    c_yellow = COLOR_YELLOW if use_color else ""
    c_res = COLOR_RESET if use_color else ""
    
    discrepancies = []
    
    def log_diff(context, old_val, new_val, is_c):
        if old_val == new_val: return
        flag_str = "[C-FLAGGED]" if is_c else "[UNMARKED CHANGE]"
        msg = f"{flag_str} {context}: Original: {old_val:.2f} -> Current: {new_val:.2f}"
        discrepancies.append(msg)
        if not is_c: print(f"{c_red}{msg}{c_res}")
        else: print(f"{c_yellow}{msg}{c_res}")

    print(f"\n{COLOR_CYAN}--- Running Original vs Current Comparison ---{COLOR_RESET}")
    
    # 1. Compare Info 1099
    for key in ['1a', '1b', '2a', '2b', '3', '5', '12']:
        log_diff(f"Summary Box {key}", orig_info[key]['val'], curr_info[key]['val'], curr_info[key]['c'])
        
    for key in ['Total Dividends & distributions', 'Total Tax-exempt dividends']:
        log_diff(f"Grand Total '{key}'", orig_info['grand_totals'][key]['val'], curr_info['grand_totals'][key]['val'], curr_info['grand_totals'][key]['c'])

    # 2. Compare Dividends
    for sec, c_data in curr_divs.items():
        o_data = orig_divs.get(sec)
        if not o_data:
            # Try matching by CUSIP if name changed slightly
            o_data = next((v for k, v in orig_divs.items() if v['cusip'] and v['cusip'] == c_data['cusip']), None)
        
        if not o_data:
            msg = f"[NEW] Security added in current statement: {sec}"
            discrepancies.append(msg)
            continue
            
        for t_type, c_tot in c_data['totals'].items():
            o_val = o_data['totals'].get(t_type, {'val': 0.0})['val']
            log_diff(f"Div Total [{sec}] '{t_type}'", o_val, c_tot['val'], c_tot['c'])
            
        # Match transactions by date/type
        for c_t in c_data['transactions']:
            o_t = next((t for t in o_data['transactions'] if t['date'] == c_t['date'] and t['type'] == c_t['type']), None)
            if o_t: log_diff(f"Div Tx [{sec}] ({c_t['date']} {c_t['type']})", o_t['amount']['val'], c_t['amount']['val'], c_t['amount']['c'])
            else: discrepancies.append(f"[NEW] Div Tx [{sec}] added: {c_t['date']} {c_t['type']} {c_t['amount']['val']:.2f}")

    # 3. Compare 1099-B Transactions
    for c_t in curr_tx:
        o_t = next((t for t in orig_tx if t['box'] == c_t['box'] and t['base_description'] == c_t['base_description'] and t['date_sold'] == c_t['date_sold'] and t['quantity']['val'] == c_t['quantity']['val']), None)
        if o_t:
            ctx = f"1099-B Tx [{c_t['box']}] {c_t['base_description']} ({c_t['date_sold']})"
            log_diff(f"{ctx} Proceeds", o_t['proceeds']['val'], c_t['proceeds']['val'], c_t['proceeds']['c'])
            log_diff(f"{ctx} Cost Basis", o_t['cost_basis']['val'], c_t['cost_basis']['val'], c_t['cost_basis']['c'])
            log_diff(f"{ctx} Gain/Loss", o_t['gain_loss']['val'], c_t['gain_loss']['val'], c_t['gain_loss']['c'])
            
    if discrepancies:
        try:
            with open(log_path, 'w', encoding='utf-8') as f:
                f.write("\n".join(discrepancies))
            print(f"{COLOR_CYAN}Comparison log saved to: {log_path}{COLOR_RESET}")
        except IOError: pass
    else:
        print(f"{COLOR_GREEN}No value discrepancies found between statements.{COLOR_RESET}")

def prompt_for_missing_fed_pct(dividends_data, fed_csv_path, use_color=True):
    for sec_name, data in dividends_data.items():
        cusip = data.get('cusip', '')
        if (sec_name.strip().upper().startswith("VANGUARD FEDL MONEY MKT") or cusip.startswith("9999100")) and 'fed_pct' not in data['supplemental']:
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
    ov_divs = sum(d['totals'].get('Total Dividends & distributions', {'val':0.0})['val'] for d in dividends_data.values())
    ov_exempt = sum(d['totals'].get('Total Tax-exempt dividends', {'val':0.0})['val'] for d in dividends_data.values())
    
    sum_div_f = info_1099['1a']['val'] + info_1099['2a']['val'] + info_1099['3']['val']
    
    grand_div = info_1099['grand_totals']['Total Dividends & distributions']['val']
    grand_exempt = info_1099['grand_totals']['Total Tax-exempt dividends']['val']
    
    c_green, c_red, c_reset = (COLOR_GREEN, COLOR_RED, COLOR_RESET) if use_color else ("", "", "")

    for label, src1_label, s1, s2, s3, tag, file_suffix in [
        ("Total Dividends & distributions", "DIV 1a+2a+3", sum_div_f, ov_divs, grand_div, 'Total Dividends & distributions', 'dividends.csv'),
        ("Total Tax-exempt dividends", "DIV 12", info_1099['12']['val'], ov_exempt, grand_exempt, 'Total Tax-exempt dividends', 'tax_exempt.csv')
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
    rows = [{'Security Name': k, 'CUSIP': v['cusip'], 'Amount': f"{v['totals'].get(target_key, {'val':0.0})['val']:.2f}"} for k, v in dividends_data.items() if v['totals'].get(target_key, {'val':0.0})['val'] != 0]
    overall_total = sum(v['totals'].get(target_key, {'val':0.0})['val'] for v in dividends_data.values())
    rows.append({'Security Name': 'OVERALL TOTAL', 'CUSIP': '', 'Amount': f"{overall_total:.2f}"})
    try:
        with open(filename, mode='w', newline='', encoding='utf-8') as f:
            writer = csv.DictWriter(f, fieldnames=['Security Name', 'CUSIP', 'Amount'])
            writer.writeheader()
            writer.writerows(rows)
        print(f"    [+] Created: {filename}")
    except IOError as e:
        print(f"    [!] Error writing {filename}: {e}")

def write_supplemental_csvs(dividends_data, prefix_str):
    for label, key, pct_key in [("us_securities_state_exempt_box20.csv", "Total Dividends & distributions", "fed_pct"), ("fed_exempt_state_exempt_box21.csv", "Total Tax-exempt dividends", "ny_pct")]:
        rows = []
        for k, v in dividends_data.items():
            tot_val = v['totals'].get(key, {'val':0.0})['val']
            if tot_val > 0 and v['supplemental'].get(pct_key) is not None:
                rows.append({'Security Name': k, 'CUSIP': v['cusip'], 'Total Amount': f"{tot_val:.2f}", 'Percentage': f"{v['supplemental'][pct_key]*100:.2f}%", 'Calculated': f"{tot_val*v['supplemental'][pct_key]:.2f}"})
        if rows:
            filename = f"{prefix_str}{label}"
            try:
                with open(filename, mode='w', newline='', encoding='utf-8') as f:
                    w = csv.DictWriter(f, fieldnames=['Security Name', 'CUSIP', 'Total Amount', 'Percentage', 'Calculated'])
                    w.writeheader()
                    w.writerows(rows)
                    w.writerow({'Security Name': 'OVERALL TOTAL', 'CUSIP': '', 'Total Amount': f"{sum(float(r['Total Amount']) for r in rows):.2f}", 'Percentage': '', 'Calculated': f"{sum(float(r['Calculated']) for r in rows):.2f}"})
                print(f"Created: {filename} ({len(rows)} securities)")
            except IOError as e: print(f"Error writing {filename}: {e}")

def main():
    parser = argparse.ArgumentParser(description="Parse Brokerage 1099-B and Dividend statements.")
    parser.add_argument("pdf", help="Path to the current 1099 PDF file.")
    parser.add_argument("--original", type=str, help="Path to the original 1099 PDF file to compare against.")
    parser.add_argument("--boxes", type=str, default="A,B,C,D,E,F", help="Comma-separated list of boxes to extract.")
    parser.add_argument("--output", type=str, default="1099b_data.csv", help="Output CSV filename for 1099-B data.")
    parser.add_argument("--fed-csv", type=str, help="Path to a CSV file containing Fed source percentage overrides.")
    parser.add_argument("-d", "--debug", action="store_true", help="Enable debug logging to a categorized JSON file.")
    parser.add_argument("--log-file", type=str, default="parser_debug.json", help="Path for the debug log file.")
    args = parser.parse_args()

    target_boxes = [b.strip().upper() for b in args.boxes.split(',')]
    use_color = not getattr(args, 'no_color', False)

    base_pdf_name = os.path.basename(args.pdf)
    clean_prefix = os.path.splitext(base_pdf_name)[0].replace('1099_', '').replace('1099', '').strip('_-')
    prefix_str = f"{clean_prefix}_" if clean_prefix else ""
    
    actual_output_file, actual_log_file = f"{prefix_str}{args.output}", f"{prefix_str}{args.log_file}" if args.log_file else None
    
    default_fed_csv = "fed_percentages.csv"
    fed_csv_path = args.fed_csv
    
    if fed_csv_path:
        if not os.path.exists(fed_csv_path):
            print(f"{COLOR_RED}[!] ERROR: The specified Fed percentage file '{fed_csv_path}' does not exist.{COLOR_RESET}")
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
    
    # 1. Parse Original Statement (if provided)
    orig_transactions, orig_summary, orig_dividends, orig_info = [], {}, {}, {}
    if args.original:
        if not os.path.exists(args.original):
            print(f"{COLOR_RED}[!] ERROR: Original PDF '{args.original}' not found.{COLOR_RESET}")
            sys.exit(1)
        orig_transactions, orig_summary, orig_dividends, orig_info = parse_statement(
            args.original, target_boxes, fed_csv_path=fed_csv_path, debug=False, use_color=use_color
        )
    
    # 2. Parse Current Statement
    transactions, expected_summary, dividends_data, info_1099 = parse_statement(
        args.pdf, target_boxes, fed_csv_path=fed_csv_path, debug=args.debug, log_filepath=actual_log_file if args.debug else None, use_color=use_color
    )

    # 3. Compare Statements
    if args.original:
        compare_statements(transactions, info_1099, dividends_data, orig_transactions, orig_info, orig_dividends, f"{prefix_str}comparison_log.txt", use_color)

    prompt_for_missing_fed_pct(dividends_data, fed_csv_path, use_color=use_color)

    if transactions:
        with open(actual_output_file, mode='w', newline='', encoding='utf-8') as csv_file:
            writer = csv.DictWriter(csv_file, fieldnames=['box', 'description', 'date_sold', 'quantity', 'proceeds', 'date_acquired', 'cost_basis', 'adjustments', 'gain_loss'])
            writer.writeheader()
            for tx in transactions: 
                writer.writerow({k: (tx[k]['val'] if isinstance(tx[k], dict) else tx[k]) for k in ['box', 'description', 'date_sold', 'quantity', 'proceeds', 'date_acquired', 'cost_basis', 'adjustments', 'gain_loss']})
        print(f"Created: {actual_output_file} ({len(transactions)} 1099-B transactions)")
        
        # 1099-B Summary CSV Generation
        summary_1099b = defaultdict(lambda: {
            'date_sold_set': set(), 'date_acquired_set': set(), 'base_desc_set': set(),
            'quantity': 0.0, 'proceeds': 0.0, 'cost_basis': 0.0, 'adjustments': 0.0, 'gain_loss': 0.0
        })
        for tx in transactions:
            b = tx['box']
            summary_1099b[b]['date_sold_set'].add(tx['date_sold'])
            summary_1099b[b]['date_acquired_set'].add(tx['date_acquired'])
            summary_1099b[b]['base_desc_set'].add(tx['base_description'])
            summary_1099b[b]['quantity'] += tx['quantity']['val']
            summary_1099b[b]['proceeds'] += tx['proceeds']['val']
            summary_1099b[b]['cost_basis'] += tx['cost_basis']['val']
            summary_1099b[b]['adjustments'] += tx['adjustments']['val']
            summary_1099b[b]['gain_loss'] += tx['gain_loss']['val']

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
                        'box': b, 'description': desc, 'date_sold': ds, 'quantity': f"{data['quantity']:.4f}",
                        'proceeds': f"{data['proceeds']:.2f}", 'date_acquired': da, 'cost_basis': f"{data['cost_basis']:.2f}",
                        'adjustments': f"{data['adjustments']:.2f}", 'gain_loss': f"{data['gain_loss']:.2f}"
                    })
            print(f"    [+] Created: {summary_file} ({len(summary_1099b)} box summaries)")
        except IOError as e:
            print(f"Error writing {summary_file}: {e}")
            
    else: print(f"{COLOR_YELLOW}No 1099-B transactions found.{COLOR_RESET}")

    if dividends_data:
        perform_dividend_cross_checks(dividends_data, info_1099, prefix_str, use_color=use_color)
        write_supplemental_csvs(dividends_data, prefix_str)

if __name__ == "__main__":
    main()
