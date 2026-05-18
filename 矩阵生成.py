import itertools

def get_gift_ddt():
    """1. 计算 GIFT 算法的差分分布表 (DDT)"""
    sbox = [1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14]
    ddt = [[0] * 16 for _ in range(16)]
    for dx in range(16):
        for x in range(16):
            dy = sbox[x] ^ sbox[x ^ dx]
            ddt[dx][dy] += 1
    return ddt

def generate_valid_states(ddt):
    """2. 生成 11 bit 变量的所有合法状态 (x3..x0, y3..y0, p, q, m)"""
    valid_states = set()
    for dx in range(16):
        for dy in range(16):
            count = ddt[dx][dy]
            if count == 0:
                continue # 不可能的差分，直接跳过
            
            # 根据概率分配 p, q, m 权重变量
            if dx == 0 and dy == 0:
                p, q, m = 0, 0, 0  # 权重 0
            elif count == 4:
                p, q, m = 1, 1, 0  # 权重 2 (2^-2)
            elif count == 2:
                p, q, m = 1, 1, 1  # 权重 3 (2^-3)
            else:
                continue
                
            # 将 dx, dy 转化为 4位二进制元组
            dx_bits = tuple((dx >> i) & 1 for i in range(3, -1, -1))
            dy_bits = tuple((dy >> i) & 1 for i in range(3, -1, -1))
            state = dx_bits + dy_bits + (p, q, m)
            valid_states.add(state)
    return valid_states

def greedy_minimize(invalid_states):
    """3. 贪心逻辑化简算法 (将真值表压缩为 CNF 子句)"""
    # 这里使用简单的启发式合并：寻找只有 1 bit 不同的子句进行合并 (9 代表无关项/消去)
    clauses = set(invalid_states)
    changed = True
    while changed:
        changed = False
        new_clauses = set()
        marked = set()
        clauses_list = list(clauses)
        
        for i in range(len(clauses_list)):
            for j in range(i + 1, len(clauses_list)):
                c1 = clauses_list[i]
                c2 = clauses_list[j]
                
                # 检查两条子句是否只有 1 bit 不同
                diff_count = sum(1 for a, b in zip(c1, c2) if a != b)
                if diff_count == 1:
                    # 合并这两条子句，不同的那一位设为 9 (无关项)
                    merged = tuple(a if a == b else 9 for a, b in zip(c1, c2))
                    new_clauses.add(merged)
                    marked.add(c1)
                    marked.add(c2)
                    changed = True
                    
        # 保留没有被合并的子句
        for c in clauses_list:
            if c not in marked:
                new_clauses.add(c)
        clauses = new_clauses
        
    return clauses

def format_to_cnf_matrix(minimized_clauses):
    """4. 格式化为搜索代码中需要的 0, 1, 9 矩阵"""
    matrix = []
    for clause in minimized_clauses:
        # 注意：在 SAT 中，为了剔除非法状态，我们需要对其取反 (De Morgan 定理)
        # 所以原状态的 0 变成 0(正变量), 1 变成 1(负变量)
        formatted_clause = []
        for bit in clause:
            if bit == 0:
                formatted_clause.append(0)
            elif bit == 1:
                formatted_clause.append(1)
            else:
                formatted_clause.append(9)
        matrix.append(formatted_clause)
    return matrix

if __name__ == "__main__":
    print("开始分析 GIFT 算法 S 盒...")
    ddt = get_gift_ddt()
    valid_states = generate_valid_states(ddt)
    
    # 获取所有的非法状态 (11 bit 组合)
    all_possible_states = set(itertools.product([0, 1], repeat=11))
    invalid_states = all_possible_states - valid_states
    print(f"找到合法状态数: {len(valid_states)}")
    print(f"找到非法状态数: {len(invalid_states)} (需要转化为 CNF 剔除)")
    
    print("正在进行逻辑化简压缩，请稍候...")
    minimized_clauses = greedy_minimize(invalid_states)
    
    cnf_matrix = format_to_cnf_matrix(minimized_clauses)
    
    print("\n================= 替换代码生成完毕 =================")
    print(f"请将以下矩阵替换掉你原代码中的 SymbolicCNFConstraintForSbox")
    print(f"注意：你需要将代码里的硬编码常量改成 {len(cnf_matrix)} ")
    print("SymbolicCNFConstraintForSbox = [")
    for i, clause in enumerate(cnf_matrix):
        if i == len(cnf_matrix) - 1:
            print(f"    {clause}")
        else:
            print(f"    {clause},")
    print("]")