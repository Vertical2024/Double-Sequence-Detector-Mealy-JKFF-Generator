from itertools import product
from sympy import symbols
from sympy.logic import SOPform

def get_longest_matching_prefix(string, valid_prefixes):
    """查找 string 的最长后缀，该后缀同时属于 valid_prefixes"""
    for length in range(len(string), -1, -1):
        suffix = string[-length:] if length > 0 else ""
        if suffix in valid_prefixes:
            return suffix
    return ""

def build_mealy_solver(seq1, seq2, ff_type='JK'):
    print(f"=== 正在求解 Mealy 序列检测器: 序列1={seq1}(01), 序列2={seq2}(10), 触发器={ff_type} ===")
    
    # 1. 提取所有有效前缀作为状态（Mealy机在第4位产生输出，前缀长度最多为3）
    prefixes = set()
    for i in range(len(seq1)):
        prefixes.add(seq1[:i])
    for i in range(len(seq2)):
        prefixes.add(seq2[:i])
    
    states = sorted(list(prefixes), key=lambda x: (len(x), x))
    num_states = len(states)
    state_to_id = {s: i for i, s in enumerate(states)}
    
    # 计算所需触发器数量
    num_ffs = (num_states - 1).bit_length()
    print(f"状态列表 ({num_states}个状态): {states}")
    print(f"所需触发器数量: {num_ffs} (编码位宽)")
    
    # 2. 构建状态转移表与输出表
    transition_table = []
    for s in states:
        curr_id = state_to_id[s]
        for x in [0, 1]:
            next_str = s + str(x)
            
            # 判断 Mealy 输出
            y1, y0 = 0, 0
            if next_str.endswith(seq1):
                y1, y0 = 0, 1  # 序列 1 检测到 -> 01
            elif next_str.endswith(seq2):
                y1, y0 = 1, 0  # 序列 2 检测到 -> 10
            
            # 下一状态是最长匹配前缀
            next_prefix = get_longest_matching_prefix(next_str, prefixes)
            next_id = state_to_id[next_prefix]
            
            transition_table.append({
                'state_str': s,
                'curr_id': curr_id,
                'X': x,
                'next_id': next_id,
                'Y1': y1,
                'Y0': y0
            })

    # 3. 生成真值表与 JK/T 激励表
    # 变量顺序: Q_{n-1}, ..., Q_0, X
    vars_symbols = [symbols(f'Q{i}') for i in range(num_ffs - 1, -1, -1)] + [symbols('X')]
    
    # 准备各输出函数的 minterms 与 dontcares
    # outputs: Y1, Y0, J2, K2, J1, K1... 或者 T2, T1...
    logic_data = {}
    
    # 记录所有在用和未用的逻辑项
    used_minterms = set()
    for row in transition_table:
        curr_bin = format(row['curr_id'], f'0{num_ffs}b')
        term_val = int(curr_bin + str(row['X']), 2)
        used_minterms.add(term_val)
        
    all_terms = set(range(2 ** (num_ffs + 1)))
    dont_cares = all_terms - used_minterms

    print(f"\n未用状态/组合 (Don't Cares 数量): {len(dont_cares)}")

    # 构造 JK / T 激励映射
    # 遍历所有存在的真值表项
    expr_inputs = {} # key -> {'minterms': [], 'dontcares': list(dont_cares)}
    
    def add_val(target_key, term_val, val):
        if target_key not in expr_inputs:
            expr_inputs[target_key] = {'minterms': set(), 'dontcares': set(dont_cares)}
        if val == 1:
            expr_inputs[target_key]['minterms'].add(term_val)
        elif val == 'X':
            expr_inputs[target_key]['dontcares'].add(term_val)

    for row in transition_table:
        curr_bin = format(row['curr_id'], f'0{num_ffs}b')
        next_bin = format(row['next_id'], f'0{num_ffs}b')
        term_val = int(curr_bin + str(row['X']), 2)
        
        # 输出 Y1, Y0
        add_val('Y1', term_val, row['Y1'])
        add_val('Y0', term_val, row['Y0'])
        
        # 触发器激励
        for i in range(num_ffs):
            q_curr = int(curr_bin[num_ffs - 1 - i])
            q_next = int(next_bin[num_ffs - 1 - i])
            
            if ff_type.upper() == 'JK':
                # JK 激励化简规则
                # 0->0: J=0, K=X ; 0->1: J=1, K=X ; 1->0: J=X, K=1 ; 1->1: J=X, K=0
                if q_curr == 0 and q_next == 0:
                    add_val(f'J{i}', term_val, 0)
                    add_val(f'K{i}', term_val, 'X')
                elif q_curr == 0 and q_next == 1:
                    add_val(f'J{i}', term_val, 1)
                    add_val(f'K{i}', term_val, 'X')
                elif q_curr == 1 and q_next == 0:
                    add_val(f'J{i}', term_val, 'X')
                    add_val(f'K{i}', term_val, 1)
                elif q_curr == 1 and q_next == 1:
                    add_val(f'J{i}', term_val, 'X')
                    add_val(f'K{i}', term_val, 0)
            elif ff_type.upper() == 'T':
                # T 激励规则: 变化为 1，不变为 0
                t_val = 1 if q_curr != q_next else 0
                add_val(f'T{i}', term_val, t_val)

    # 4. 化简并打印逻辑表达式
    print("\n=== 最简逻辑表达式 (SOP) ===")
    simplified_exprs = {}
    for func_name, data in sorted(expr_inputs.items()):
        minterms = list(data['minterms'])
        dcs = list(data['dontcares'])
        expr = SOPform(vars_symbols, minterms, dcs)
        simplified_exprs[func_name] = expr
        print(f"{func_name} = {expr}")

    # 5. 未用状态误检测验证 (Check Unused States)
    print("\n=== 未用状态安全性检查 ===")
    y1_expr = simplified_exprs['Y1']
    y0_expr = simplified_exprs['Y0']
    
    has_false_positive = False
    for dc_term in sorted(dont_cares):
        # 提取二进制位
        bin_str = format(dc_term, f'0{num_ffs + 1}b')
        q_vals = [int(b) for b in bin_str[:-1]]
        x_val = int(bin_str[-1])
        
        # 代入求值
        eval_dict = {vars_symbols[i]: q_vals[i] for i in range(num_ffs)}
        eval_dict[vars_symbols[-1]] = x_val
        
        res_y1 = bool(y1_expr.xreplace(eval_dict))
        res_y0 = bool(y0_expr.xreplace(eval_dict))
        
        if res_y1 or res_y0:
            has_false_positive = True
            print(f"⚠️ 警告: 未用项 {bin_str} (Q={q_vals}, X={x_val}) 输出了 {int(res_y1)}{int(res_y0)}！需要修正 Karnaugh map。")
            
    if not has_false_positive:
        print("✅ 验证通过：所有未用状态（Don't Cares）均不会误触发 01 或 10 输出。")

# 示例调用 (以甚至/奇数学号常见组合为例)
if __name__ == '__main__':
    # 例如：Even-Even 组合 seq1="0101", seq2="0110", JK触发器
    build_mealy_solver(seq1="0101", seq2="0110", ff_type="JK")