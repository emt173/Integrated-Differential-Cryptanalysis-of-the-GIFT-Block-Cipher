import os
import time
import random

FullRound = 32 # 算法的总轮数

SearchRoundStart = 8 # 搜索的起始轮数
SearchRoundEnd = 14 # 搜索的结束轮数
InitialLowerBound = 0 # 初始的概率下界

GroupConstraintChoice = 0 # 分组约束的选项

# 选项 1 的参数
GroupNumForChoice1 = 1 

DifferentialProbabilityBound = list([])
for i in range(FullRound):
    DifferentialProbabilityBound += [0]
    
def CountClausesInRoundFunction(Round, Probability, clause_num):
    # 计算轮函数中的 CNF 子句数量
    count = clause_num
    # 非零输入约束（保证差分分析的输入差分不全为0）
    count += 1
    # S 盒的约束子句
    for r in range(Round):
        for i in range(16):
            for j in range(325):
                count += 1
    return count
    
def CountClausesInSequentialEncoding(main_var_num, cardinalitycons, clause_num):
    # 计算原始顺序编码中的子句数量，用于处理概率加法
    count = clause_num
    n = main_var_num
    k = cardinalitycons
    if (k > 0):
        count += 1
        for j in range(1, k):
            count += 1
        for i in range(1, n-1):
            count += 3
        for j in range(1, k):
            for i in range(1, n-1):
                count += 2
        count += 1
    if (k == 0):
        for i in range(n):
            count += 1
    return count
    
def CountClausesForMatsuiStrategy(n, k, left, right, m, clausenum):
    # 计算松井策略引入的附加子句数量，用于剪枝加速搜索
    count = clausenum
    if (m > 0):
        if ((left == 0) and (right < n-1)):
            for i in range(1, right + 1):
                count += 1
        if ((left > 0) and (right == n-1)):
            for i in range(0, k-m):
                count += 1
            for i in range(0, k-m+1):
                count += 1
        if ((left > 0) and (right < n-1)):
            for i in range(0, k-m):
                count += 1
    if (m == 0):
        for i in range(left, right + 1):
            count += 1
    return count
    
def GenSequentialEncoding(x, u, main_var_num, cardinalitycons, fout):
    # 生成顺序编码的具体 CNF 语句并写入文件
    n = main_var_num
    k = cardinalitycons
    if (k > 0):
        clauseseq = "-" + str(x[0]+1) + " " + str(u[0][0]+1) + " 0" + "\n"
        fout.write(clauseseq)
        for j in range(1, k):
            clauseseq = "-" + str(u[0][j]+1) + " 0" + "\n"
            fout.write(clauseseq)
        for i in range(1, n-1):
            clauseseq = "-" + str(x[i]+1) + " " + str(u[i][0]+1) + " 0" + "\n"
            fout.write(clauseseq)
            clauseseq = "-" + str(u[i-1][0]+1) + " " + str(u[i][0]+1) + " 0" + "\n"
            fout.write(clauseseq)
            clauseseq = "-" + str(x[i]+1) + " " + "-" + str(u[i-1][k-1]+1) + " 0" + "\n"
            fout.write(clauseseq)
        for j in range(1, k):
            for i in range(1, n-1):
                clauseseq = "-" + str(x[i]+1) + " " + "-" + str(u[i-1][j-1]+1) + " " + str(u[i][j]+1) + " 0" + "\n"
                fout.write(clauseseq)
                clauseseq = "-" + str(u[i-1][j]+1) + " " + str(u[i][j]+1) + " 0" + "\n"
                fout.write(clauseseq)
        clauseseq = "-" + str(x[n-1]+1) + " " + "-" + str(u[n-2][k-1]+1) + " 0" + "\n"
        fout.write(clauseseq)
    if (k == 0):
        for i in range(n):
            clauseseq = "-" + str(x[i]+1) + " 0" + "\n"
            fout.write(clauseseq)
            
def GenMatsuiConstraint(x, u, n, k, left, right, m, fout):
    # 生成松井策略的具体 CNF 约束并写入文件
    if (m > 0):
        if ((left == 0) and (right < n-1)):
            for i in range(1, right + 1):
                clauseseq = "-" + str(x[i] + 1) + " " + "-" + str(u[i-1][m-1] + 1) + " 0" + "\n"
                fout.write(clauseseq)
        if ((left > 0) and (right == n-1)):
            for i in range(0, k-m):
                clauseseq = str(u[left-1][i] + 1) + " " + "-" + str(u[right - 1][i+m] + 1) + " 0" + "\n"
                fout.write(clauseseq)
            for i in range(0, k-m+1):
                clauseseq = str(u[left-1][i] + 1) + " " + "-" + str(x[right] + 1) + " " + "-" + str(u[right - 1][i+m-1] + 1) + " 0" + "\n"
                fout.write(clauseseq)
        if ((left > 0) and (right < n-1)):
            for i in range(0, k-m):
                clauseseq = str(u[left-1][i] + 1) + " " + "-" + str(u[right][i+m] + 1) + " 0" + "\n"
                fout.write(clauseseq)
    if (m == 0):
        for i in range(left, right + 1):
            clauseseq = "-" + str(x[i] + 1) + " 0" + "\n"
            fout.write(clauseseq)
            
def Decision(Round, Probability, MatsuiRoundIndex, MatsuiCount, flag):
    # 核心判决函数：生成当前轮数和概率下的完整 SAT 约束，并调用求解器判断是否有解
    
    # 1. 定义三层结构的轮数分配
    R_b = 1  # 头部扩展轮数 (Eb)
    R_f = 1  # 尾部扩展轮数 (Ef)
    R_m = Round - R_b - R_f # 中间的区分器轮数 (Em)
    
    # 如果搜索总轮数太短，不够切分三层，直接返回无解
    if R_m < 1:
        return False
        
    # 概率辅助变量的最高上限仅由中间层 R_m 决定
    TotalProbability = 16 * R_m * 3
    count_var_num = 0;
    time_start = time.time()
    
    # 声明变量 (xin: 输入差分, xout: 输出差分, p/q/m: 概率辅助变量)
    xin = []
    p = []
    q = []
    m = []
    xout = []
    for i in range(Round):
        xin.append([])
        p.append([])
        q.append([])
        m.append([])
        xout.append([])
        for j in range(64):
            xin[i].append(0)
        for j in range(16):
            p[i].append(0)
            q[i].append(0)
            m[i].append(0)
        for j in range(64):
            xout[i].append(0)
            
    # 给变量分配具体的编号（用于生成 CNF 格式）
    for i in range(Round):
        for j in range(64):
            xin[i][j] = count_var_num
            count_var_num += 1
        for j in range(16):
            p[i][j] = count_var_num
            count_var_num += 1
        for j in range(16):
            q[i][j] = count_var_num
            count_var_num += 1
        for j in range(16):
            m[i][j] = count_var_num
            count_var_num += 1
    for i in range(Round - 1):
        for j in range(64):
            xout[i][j] = xin[i + 1][j]
    for i in range(64):
        xout[Round - 1][i] = count_var_num
        count_var_num += 1
    auxiliary_var_u = []
    for i in range(TotalProbability - 1):
        auxiliary_var_u.append([])
        for j in range(Probability):
            auxiliary_var_u[i].append(count_var_num)
            count_var_num += 1

    MaxActiveV_b = 16 # 允许头部最多猜 16 bit 密钥
    MaxActiveV_f = 16 # 允许尾部最多猜 16 bit 密钥
    
 
    v_b = []
    v_f = []
    for i in range(64):
        v_b.append(count_var_num)
        count_var_num += 1
    for i in range(64):
        v_f.append(count_var_num)
        count_var_num += 1
        
    auxiliary_var_u_v_b = []
    if MaxActiveV_b > 0:
        for i in range(63): # 64个主变量，需要63组辅助变量
            auxiliary_var_u_v_b.append([])
            for j in range(MaxActiveV_b):
                auxiliary_var_u_v_b[i].append(count_var_num)
                count_var_num += 1
                
    auxiliary_var_u_v_f = []
    if MaxActiveV_f > 0:
        for i in range(63):
            auxiliary_var_u_v_f.append([])
            for j in range(MaxActiveV_f):
                auxiliary_var_u_v_f[i].append(count_var_num)
                count_var_num += 1
    # ---------------------------------------------------------------------
    
    # 计算所有约束所需的子句总数，并生成 CNF 文件头部
    count_clause_num = 0
    # 计算轮函数约束的子句数
    count_clause_num = CountClausesInRoundFunction(Round, Probability, count_clause_num)
    count_clause_num += 54 * 16 * 2  
    count_clause_num = CountClausesInSequentialEncoding(64, MaxActiveV_b, count_clause_num)
    count_clause_num = CountClausesInSequentialEncoding(64, MaxActiveV_f, count_clause_num)
    # ---------------------------------------------------------------------
  # 计算原始顺序编码约束的子句数
    Main_Var_Num = 16 * R_m * 3  
    CardinalityCons = Probability
    count_clause_num = CountClausesInSequentialEncoding(Main_Var_Num, CardinalityCons, count_clause_num)
    # 计算松井策略引入的子句数
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = 16 * StartingRound * 3
        RightNode = 16 * EndingRound * 3 - 1
        PartialCardinalityCons = Probability - DifferentialProbabilityBound[StartingRound] - DifferentialProbabilityBound[Round - EndingRound]
        count_clause_num = CountClausesForMatsuiStrategy(Main_Var_Num, CardinalityCons, LeftNode, RightNode, PartialCardinalityCons, count_clause_num)
        
    # 创建并打开具体的 .cnf 问题文件
    file = open("Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf", "w")
    file.write("p cnf " + str(count_var_num) + " " + str(count_clause_num) + "\n")
    
    # 添加声明非零输入差分的约束（至少有一个输入比特不是 0）
    clauseseq = ""
    for i in range(64):
        clauseseq += str(xin[0][i] + 1) + " "
    clauseseq += "0" + "\n"
    file.write(clauseseq)
    GenSequentialEncoding(v_b, auxiliary_var_u_v_b, 64, MaxActiveV_b, file)
    GenSequentialEncoding(v_f, auxiliary_var_u_v_f, 64, MaxActiveV_f, file)

    # 为每一轮的加密操作（S盒 + P盒）添加具体的逻辑约束
    for r in range(Round):
        y = list([])
        # gift算法的比特置换层映射规则
        P = [0, 17, 34, 51, 48, 1, 18, 35, 32, 49, 2, 19, 16, 33, 50, 3, 4, 21, 38, 55, 52, 5, 22, 39, 36, 53, 6, 23, 20, 37, 54, 7, 8, 25, 42, 59, 56, 9, 26, 43, 40, 57, 10, 27, 24, 41, 58, 11, 12, 29, 46, 63, 60, 13, 30, 47, 44, 61, 14, 31, 28, 45, 62, 15
]
        
        # gift 算法的 S 盒差分概率转化出的逻辑合取范式矩阵
        SymbolicCNFConstraintForSbox =  [
    [0, 9, 0, 9, 9, 9, 9, 0, 9, 1, 0],
    [9, 9, 0, 9, 9, 0, 0, 9, 1, 9, 0],
    [0, 9, 9, 9, 0, 1, 0, 0, 9, 9, 9],
    [0, 1, 1, 0, 1, 9, 9, 1, 9, 9, 9],
    [9, 0, 1, 9, 9, 0, 1, 9, 9, 9, 0],
    [9, 0, 0, 0, 9, 9, 0, 9, 1, 9, 9],
    [9, 1, 1, 9, 9, 1, 9, 1, 9, 9, 0],
    [1, 1, 1, 1, 1, 0, 9, 0, 9, 9, 9],
    [0, 9, 9, 1, 9, 9, 0, 9, 9, 9, 0],
    [9, 1, 0, 9, 9, 0, 9, 1, 9, 9, 0],
    [0, 9, 1, 1, 9, 1, 9, 9, 9, 9, 0],
    [9, 0, 9, 9, 9, 0, 9, 0, 9, 1, 0],
    [1, 9, 9, 1, 9, 9, 1, 9, 9, 9, 0],
    [0, 9, 9, 9, 0, 9, 1, 1, 9, 9, 0],
    [9, 0, 0, 9, 1, 1, 1, 0, 9, 9, 9],
    [0, 9, 9, 9, 0, 9, 0, 0, 1, 9, 9],
    [0, 0, 9, 9, 0, 0, 9, 1, 9, 9, 9],
    [1, 1, 1, 1, 9, 1, 0, 9, 9, 9, 1],
    [1, 0, 1, 9, 1, 9, 1, 1, 9, 9, 9],
    [1, 0, 0, 9, 1, 1, 1, 9, 9, 9, 1],
    [0, 9, 9, 9, 0, 9, 0, 0, 9, 1, 9],
    [0, 9, 9, 0, 9, 1, 0, 0, 9, 9, 9],
    [9, 0, 0, 0, 9, 9, 0, 9, 9, 1, 9],
    [0, 9, 9, 0, 1, 9, 0, 0, 9, 9, 9],
    [9, 9, 9, 0, 1, 9, 1, 1, 9, 9, 1],
    [1, 9, 1, 9, 9, 1, 9, 1, 9, 9, 0],
    [9, 0, 0, 9, 9, 1, 9, 0, 9, 9, 0],
    [9, 1, 9, 0, 9, 9, 1, 1, 9, 9, 0],
    [9, 9, 9, 1, 0, 0, 0, 0, 9, 9, 9],
    [0, 9, 0, 9, 9, 0, 1, 9, 9, 9, 0],
    [0, 9, 0, 0, 9, 9, 9, 0, 9, 9, 1],
    [1, 9, 0, 9, 9, 9, 0, 1, 9, 9, 0],
    [0, 0, 9, 9, 9, 0, 1, 9, 9, 9, 0],
    [9, 0, 0, 9, 9, 9, 9, 0, 1, 9, 0],
    [1, 9, 1, 9, 9, 0, 1, 9, 9, 9, 0],
    [0, 0, 9, 9, 9, 0, 9, 9, 9, 1, 0],
    [9, 9, 0, 0, 0, 1, 9, 9, 9, 9, 1],
    [9, 0, 0, 0, 9, 9, 1, 0, 9, 9, 9],
    [0, 1, 0, 9, 1, 0, 1, 9, 9, 9, 9],
    [9, 1, 0, 0, 9, 1, 1, 1, 9, 9, 9],
    [1, 1, 0, 1, 9, 1, 9, 0, 9, 9, 1],
    [1, 0, 9, 9, 0, 0, 9, 0, 9, 9, 9],
    [0, 9, 0, 0, 1, 9, 9, 0, 9, 9, 9],
    [9, 0, 0, 0, 9, 1, 9, 0, 9, 9, 9],
    [1, 9, 1, 1, 1, 0, 1, 0, 9, 9, 9],
    [1, 9, 9, 9, 9, 0, 0, 0, 9, 9, 0],
    [9, 9, 0, 0, 0, 0, 0, 1, 9, 9, 9],
    [1, 0, 0, 9, 9, 9, 9, 0, 9, 9, 0],
    [9, 0, 9, 1, 0, 0, 9, 0, 9, 9, 9],
    [1, 9, 9, 9, 9, 1, 0, 1, 9, 9, 0],
    [9, 0, 9, 0, 9, 9, 0, 0, 9, 1, 9],
    [9, 9, 9, 1, 9, 0, 9, 0, 9, 9, 0],
    [9, 9, 0, 1, 9, 0, 9, 9, 9, 9, 0],
    [0, 1, 0, 0, 9, 9, 9, 0, 9, 9, 9],
    [0, 9, 9, 9, 9, 0, 0, 1, 9, 9, 0],
    [9, 9, 1, 9, 9, 1, 1, 1, 9, 9, 0],
    [9, 1, 9, 0, 1, 9, 9, 9, 9, 9, 0],
    [1, 9, 9, 9, 9, 9, 9, 9, 9, 0, 9],
    [9, 1, 9, 9, 0, 0, 0, 0, 9, 9, 9],
    [1, 0, 0, 1, 1, 1, 1, 9, 9, 9, 9],
    [0, 9, 1, 9, 0, 9, 0, 0, 9, 9, 9],
    [9, 0, 9, 9, 9, 0, 1, 0, 9, 9, 0],
    [0, 0, 0, 0, 9, 9, 1, 9, 9, 9, 9],
    [9, 9, 9, 0, 0, 9, 0, 9, 9, 9, 1],
    [9, 0, 9, 9, 9, 9, 0, 0, 9, 1, 0],
    [0, 0, 9, 9, 0, 0, 9, 9, 9, 9, 1],
    [0, 9, 9, 9, 0, 0, 0, 9, 1, 9, 9],
    [0, 1, 9, 9, 1, 9, 1, 1, 9, 9, 1],
    [9, 9, 0, 0, 0, 1, 1, 0, 9, 9, 9],
    [9, 1, 9, 9, 0, 9, 1, 1, 9, 9, 0],
    [9, 9, 9, 9, 9, 1, 9, 9, 0, 9, 9],
    [9, 9, 1, 9, 9, 9, 9, 9, 9, 0, 9],
    [9, 1, 9, 9, 9, 9, 9, 9, 0, 9, 9],
    [1, 1, 1, 9, 1, 0, 1, 0, 9, 9, 9],
    [9, 9, 9, 9, 9, 9, 1, 9, 0, 9, 9],
    [1, 9, 1, 0, 0, 0, 9, 0, 9, 9, 9],
    [9, 1, 9, 9, 0, 1, 1, 9, 9, 9, 0],
    [9, 9, 9, 1, 9, 9, 9, 9, 9, 0, 9],
    [9, 0, 0, 0, 9, 1, 0, 9, 9, 9, 9],
    [9, 0, 0, 9, 9, 9, 9, 0, 9, 1, 0],
    [9, 1, 9, 1, 0, 1, 1, 9, 9, 9, 9],
    [0, 9, 0, 0, 9, 9, 1, 0, 9, 9, 9],
    [1, 1, 9, 1, 9, 0, 0, 0, 9, 9, 9],
    [9, 9, 9, 9, 9, 9, 9, 9, 9, 0, 1],
    [1, 0, 1, 1, 1, 1, 9, 1, 9, 9, 9],
    [9, 9, 0, 9, 9, 1, 1, 0, 9, 9, 0],
    [9, 9, 1, 9, 9, 9, 9, 9, 0, 9, 9],
    [0, 1, 1, 1, 9, 1, 1, 9, 9, 9, 9],
    [1, 1, 0, 1, 1, 0, 0, 9, 9, 9, 9],
    [0, 1, 1, 0, 9, 0, 9, 1, 9, 9, 9],
    [1, 9, 1, 0, 9, 9, 1, 1, 9, 9, 9],
    [0, 9, 9, 9, 0, 0, 0, 9, 9, 1, 9],
    [0, 0, 0, 0, 1, 9, 9, 9, 9, 9, 9],
    [9, 9, 9, 9, 1, 9, 0, 9, 9, 9, 0],
    [9, 9, 1, 9, 1, 1, 9, 9, 9, 9, 0],
    [1, 0, 9, 1, 1, 9, 1, 1, 9, 9, 9],
    [9, 0, 9, 0, 9, 9, 0, 0, 1, 9, 9],
    [9, 9, 0, 0, 0, 0, 0, 9, 9, 1, 9],
    [9, 9, 9, 9, 9, 0, 0, 0, 1, 9, 0],
    [9, 1, 0, 0, 0, 0, 0, 9, 9, 9, 9],
    [9, 0, 1, 0, 9, 9, 0, 0, 9, 9, 9],
    [9, 0, 0, 0, 1, 9, 0, 9, 9, 9, 9],
    [0, 9, 9, 9, 9, 1, 0, 0, 9, 9, 0],
    [9, 0, 9, 9, 9, 0, 9, 0, 1, 9, 0],
    [0, 0, 0, 9, 9, 1, 9, 9, 9, 9, 0],
    [0, 0, 1, 1, 9, 0, 0, 1, 9, 9, 9],
    [9, 0, 9, 9, 0, 0, 9, 0, 9, 1, 9],
    [9, 9, 9, 9, 9, 9, 9, 1, 9, 0, 9],
    [9, 0, 1, 9, 9, 0, 9, 0, 9, 9, 0],
    [0, 9, 1, 9, 9, 9, 0, 0, 9, 9, 0],
    [0, 0, 9, 9, 1, 9, 9, 9, 9, 9, 0],
    [0, 0, 0, 9, 9, 9, 9, 1, 9, 9, 0],
    [9, 9, 0, 0, 0, 0, 0, 9, 1, 9, 9],
    [1, 0, 1, 1, 1, 0, 1, 9, 9, 9, 9],
    [1, 1, 9, 9, 1, 9, 9, 9, 9, 9, 0],
    [0, 9, 9, 1, 0, 0, 9, 1, 9, 9, 9],
    [0, 1, 9, 9, 0, 9, 0, 0, 9, 9, 9],
    [0, 0, 9, 9, 9, 9, 1, 1, 9, 9, 0],
    [9, 9, 0, 0, 9, 1, 1, 1, 9, 9, 1],
    [0, 9, 0, 9, 9, 1, 9, 0, 9, 9, 0],
    [0, 1, 0, 1, 9, 0, 9, 1, 9, 9, 9],
    [0, 9, 0, 9, 9, 9, 9, 0, 1, 9, 0],
    [9, 0, 0, 9, 9, 9, 1, 0, 9, 9, 0],
    [1, 1, 9, 9, 0, 9, 1, 1, 9, 9, 9],
    [9, 0, 9, 0, 0, 9, 9, 9, 9, 9, 1],
    [1, 1, 9, 9, 0, 1, 9, 1, 9, 9, 9],
    [0, 9, 9, 9, 0, 0, 0, 1, 9, 9, 9],
    [1, 0, 0, 1, 1, 0, 9, 1, 9, 9, 9],
    [1, 9, 9, 1, 1, 9, 9, 9, 9, 9, 0],
    [0, 9, 9, 1, 9, 9, 9, 0, 9, 9, 0],
    [9, 9, 9, 1, 9, 9, 0, 1, 9, 9, 0],
    [1, 9, 9, 9, 9, 9, 9, 9, 0, 9, 9],
    [9, 9, 9, 9, 9, 0, 0, 0, 9, 1, 0],
    [0, 0, 0, 9, 9, 9, 9, 9, 1, 9, 0],
    [9, 0, 9, 9, 9, 9, 0, 0, 1, 9, 0],
    [1, 9, 0, 0, 9, 9, 9, 1, 9, 9, 1],
    [9, 1, 0, 1, 1, 0, 0, 1, 9, 9, 9],
    [0, 9, 9, 0, 9, 0, 9, 1, 9, 9, 0],
    [1, 0, 0, 9, 1, 0, 9, 1, 9, 9, 1],
    [0, 9, 9, 1, 0, 9, 9, 9, 9, 9, 0],
    [1, 1, 9, 0, 9, 9, 1, 1, 9, 9, 9],
    [9, 9, 9, 9, 1, 9, 9, 9, 9, 0, 9],
    [9, 0, 0, 9, 9, 1, 0, 9, 9, 9, 0],
    [1, 1, 9, 9, 9, 1, 9, 1, 9, 9, 0],
    [0, 9, 0, 0, 9, 9, 9, 0, 1, 9, 9],
    [9, 9, 1, 0, 0, 0, 9, 9, 9, 9, 1],
    [0, 9, 0, 9, 0, 1, 1, 1, 9, 9, 9],
    [0, 9, 0, 9, 9, 0, 9, 9, 9, 1, 0],
    [9, 9, 9, 1, 9, 9, 1, 0, 9, 9, 0],
    [0, 1, 1, 0, 9, 9, 0, 9, 9, 9, 9],
    [1, 9, 1, 0, 0, 0, 1, 9, 9, 9, 9],
    [9, 9, 9, 9, 9, 9, 9, 9, 0, 9, 1],
    [1, 0, 9, 9, 0, 9, 0, 0, 9, 9, 9],
    [9, 0, 9, 0, 1, 9, 0, 0, 9, 9, 9],
    [1, 9, 9, 1, 9, 0, 9, 9, 9, 9, 0],
    [9, 0, 9, 1, 0, 9, 0, 0, 9, 9, 9],
    [9, 9, 9, 9, 1, 9, 9, 9, 0, 9, 9],
    [9, 0, 9, 0, 9, 1, 0, 0, 9, 9, 9],
    [0, 9, 9, 9, 0, 0, 9, 1, 9, 9, 0],
    [1, 9, 0, 9, 9, 0, 0, 9, 9, 9, 0],
    [0, 0, 0, 0, 9, 9, 9, 9, 9, 1, 9],
    [9, 9, 9, 9, 1, 9, 9, 0, 9, 9, 0],
    [0, 9, 0, 0, 1, 9, 1, 9, 9, 9, 9],
    [9, 9, 1, 9, 0, 0, 0, 0, 9, 9, 9],
    [0, 0, 9, 9, 0, 0, 9, 9, 1, 9, 9],
    [9, 1, 9, 0, 1, 9, 1, 1, 9, 9, 9],
    [0, 1, 9, 0, 9, 9, 0, 0, 9, 9, 9],
    [9, 9, 1, 0, 1, 9, 1, 1, 9, 9, 9],
    [9, 0, 1, 9, 1, 9, 9, 9, 9, 9, 0],
    [1, 1, 9, 1, 1, 9, 0, 0, 9, 9, 9],
    [9, 9, 9, 1, 9, 0, 0, 9, 9, 9, 0],
    [9, 1, 0, 9, 1, 0, 9, 9, 9, 9, 0],
    [0, 9, 9, 0, 9, 9, 0, 0, 9, 9, 1],
    [9, 0, 9, 9, 9, 1, 0, 0, 9, 9, 0],
    [0, 9, 0, 9, 9, 0, 9, 9, 1, 9, 0],
    [0, 1, 1, 9, 9, 0, 1, 1, 9, 9, 1],
    [0, 1, 0, 9, 9, 9, 9, 0, 9, 9, 0],
    [9, 9, 9, 0, 0, 9, 9, 0, 9, 9, 1],
    [9, 0, 1, 0, 9, 9, 1, 1, 9, 9, 9],
    [1, 9, 0, 0, 9, 9, 0, 1, 9, 9, 9],
    [0, 1, 1, 9, 9, 9, 0, 9, 9, 9, 0],
    [1, 1, 9, 9, 9, 9, 1, 1, 9, 9, 0],
    [0, 1, 1, 0, 9, 9, 9, 1, 9, 9, 0],
    [0, 0, 9, 1, 0, 0, 9, 9, 9, 9, 9],
    [0, 0, 0, 9, 9, 9, 9, 9, 9, 1, 0],
    [0, 9, 0, 9, 0, 9, 1, 9, 9, 9, 0],
    [1, 0, 9, 0, 9, 9, 0, 0, 9, 9, 9],
    [9, 0, 9, 9, 0, 0, 9, 0, 1, 9, 9],
    [9, 9, 0, 9, 9, 0, 0, 1, 9, 9, 0],
    [1, 9, 0, 0, 0, 0, 0, 9, 9, 9, 9],
    [9, 0, 1, 0, 0, 0, 1, 9, 9, 9, 9],
    [9, 0, 1, 1, 9, 0, 1, 0, 9, 9, 9],
    [0, 9, 0, 0, 9, 1, 9, 0, 9, 9, 9],
    [9, 0, 9, 0, 9, 9, 1, 1, 9, 9, 1],
    [0, 9, 0, 0, 9, 9, 9, 0, 9, 1, 9],
    [9, 0, 0, 9, 9, 9, 0, 1, 9, 9, 0],
    [1, 1, 0, 1, 1, 1, 9, 0, 9, 9, 9],
    [1, 1, 0, 1, 9, 1, 1, 0, 9, 9, 9],
    [9, 0, 0, 0, 9, 9, 9, 9, 9, 9, 1],
    [9, 9, 9, 1, 0, 9, 9, 1, 9, 9, 0],
    [0, 9, 9, 1, 0, 9, 0, 0, 9, 9, 9],
    [1, 0, 9, 9, 1, 9, 1, 1, 9, 9, 1],
    [9, 1, 1, 1, 1, 1, 0, 1, 9, 9, 9],
    [9, 0, 0, 9, 9, 9, 0, 9, 1, 9, 0],
    [0, 0, 9, 9, 0, 0, 9, 9, 9, 1, 9],
    [9, 9, 9, 1, 9, 9, 9, 9, 0, 9, 9],
    [9, 0, 0, 0, 9, 9, 9, 0, 9, 1, 9],
    [1, 1, 9, 9, 0, 1, 1, 9, 9, 9, 9],
    [0, 9, 9, 0, 9, 9, 0, 0, 9, 1, 9],
    [9, 1, 9, 9, 9, 1, 1, 0, 9, 9, 0],
    [9, 1, 1, 0, 0, 1, 0, 1, 9, 9, 9],
    [9, 0, 0, 0, 1, 9, 9, 0, 9, 9, 9],
    [1, 9, 1, 1, 9, 1, 0, 1, 9, 9, 9],
    [1, 9, 0, 9, 1, 0, 0, 1, 9, 9, 9],
    [9, 1, 9, 1, 0, 9, 1, 1, 9, 9, 9],
    [1, 1, 9, 9, 9, 1, 1, 9, 9, 9, 0],
    [9, 9, 1, 9, 9, 0, 0, 0, 9, 9, 0],
    [0, 1, 9, 1, 9, 9, 1, 1, 9, 9, 1],
    [9, 0, 9, 9, 0, 9, 0, 0, 9, 1, 9],
    [0, 9, 9, 0, 1, 9, 9, 9, 9, 9, 0],
    [0, 9, 1, 9, 0, 0, 9, 1, 9, 9, 9],
    [0, 0, 1, 9, 0, 0, 9, 9, 9, 9, 9],
    [0, 0, 9, 9, 9, 0, 9, 9, 1, 9, 0],
    [9, 9, 1, 0, 9, 9, 1, 1, 9, 9, 0],
    [1, 0, 9, 9, 9, 9, 0, 0, 9, 9, 0],
    [0, 9, 9, 9, 9, 9, 0, 0, 9, 1, 0],
    [9, 9, 1, 0, 1, 9, 9, 9, 9, 9, 0],
    [0, 9, 0, 0, 9, 9, 1, 9, 9, 9, 0],
    [0, 9, 9, 9, 9, 0, 0, 9, 9, 1, 0],
    [1, 9, 1, 9, 9, 0, 9, 0, 9, 9, 0],
    [0, 9, 1, 0, 9, 9, 0, 0, 9, 9, 9],
    [0, 1, 0, 9, 9, 1, 1, 1, 9, 9, 1],
    [0, 0, 9, 9, 0, 0, 1, 9, 9, 9, 9],
    [9, 0, 9, 1, 9, 9, 9, 9, 9, 9, 0],
    [1, 9, 9, 9, 0, 1, 0, 1, 9, 9, 9],
    [0, 9, 0, 9, 9, 9, 1, 0, 9, 9, 0],
    [9, 1, 9, 9, 0, 1, 9, 0, 9, 9, 1],
    [1, 9, 9, 9, 0, 0, 0, 0, 9, 9, 9],
    [0, 9, 9, 9, 9, 9, 0, 0, 1, 9, 0],
    [9, 0, 1, 9, 0, 0, 9, 0, 9, 9, 9],
    [1, 1, 0, 9, 9, 9, 9, 1, 9, 9, 0],
    [1, 9, 9, 1, 9, 9, 9, 1, 9, 9, 0],
    [9, 0, 0, 9, 9, 9, 0, 9, 9, 1, 0],
    [0, 1, 1, 9, 1, 1, 9, 1, 9, 9, 9],
    [0, 0, 0, 0, 9, 9, 9, 1, 9, 9, 9],
    [0, 0, 0, 0, 9, 9, 9, 9, 1, 9, 9],
    [0, 1, 9, 9, 9, 0, 0, 9, 9, 9, 0],
    [1, 9, 0, 1, 1, 1, 1, 0, 9, 9, 9],
    [9, 0, 9, 9, 0, 0, 1, 0, 9, 9, 9],
    [9, 1, 1, 9, 0, 0, 1, 1, 9, 9, 9],
    [1, 9, 9, 9, 0, 1, 0, 9, 9, 9, 1],
    [0, 1, 9, 9, 9, 9, 0, 0, 9, 9, 0],
    [9, 9, 0, 9, 9, 0, 0, 9, 9, 1, 0],
    [9, 9, 9, 9, 0, 9, 0, 0, 9, 9, 1],
    [1, 9, 1, 9, 9, 9, 1, 1, 9, 9, 0],
    [0, 1, 0, 9, 9, 0, 9, 9, 9, 9, 0],
    [0, 9, 9, 9, 0, 0, 0, 9, 9, 9, 1],
    [0, 0, 1, 9, 9, 0, 9, 9, 9, 9, 0],
    [9, 9, 1, 9, 0, 9, 1, 1, 9, 9, 0],
    [0, 1, 1, 9, 9, 1, 9, 9, 9, 9, 0],
    [9, 9, 9, 9, 9, 9, 9, 1, 0, 9, 9],
    [9, 0, 0, 0, 9, 9, 9, 0, 1, 9, 9],
    [1, 9, 1, 0, 0, 1, 9, 1, 9, 9, 9],
    [9, 1, 0, 9, 0, 1, 1, 9, 9, 9, 9],
    [0, 1, 9, 9, 0, 0, 0, 9, 9, 9, 9],
    [9, 9, 9, 9, 9, 9, 1, 9, 9, 0, 9],
    [9, 0, 1, 9, 9, 9, 0, 0, 9, 9, 0],
    [0, 0, 9, 0, 9, 9, 1, 1, 9, 9, 9],
    [0, 9, 0, 9, 9, 0, 9, 1, 9, 9, 0],
    [0, 9, 9, 0, 1, 9, 1, 1, 9, 9, 9],
    [0, 9, 9, 0, 9, 9, 0, 0, 1, 9, 9],
    [9, 9, 9, 9, 9, 1, 9, 9, 9, 0, 9],
    [0, 1, 9, 9, 0, 1, 9, 0, 9, 9, 9],
    [9, 9, 1, 1, 9, 1, 1, 9, 9, 9, 0],
    [1, 0, 0, 0, 9, 9, 0, 9, 9, 9, 9],
    [1, 9, 9, 0, 9, 9, 1, 1, 9, 9, 1],
    [0, 0, 0, 0, 9, 1, 9, 9, 9, 9, 9],
    [9, 0, 0, 0, 9, 9, 0, 1, 9, 9, 9],
    [9, 9, 9, 1, 0, 0, 9, 9, 9, 9, 0],
    [0, 9, 9, 0, 9, 9, 1, 1, 9, 9, 0],
    [9, 1, 9, 9, 9, 0, 0, 0, 9, 9, 0],
    [9, 0, 9, 9, 0, 0, 9, 0, 9, 9, 1],
    [1, 9, 9, 0, 0, 9, 9, 9, 9, 9, 1],
    [0, 9, 9, 1, 0, 9, 1, 1, 9, 9, 9],
    [9, 0, 9, 9, 0, 9, 0, 0, 1, 9, 9],
    [1, 1, 1, 9, 9, 9, 1, 9, 9, 9, 0],
    [9, 0, 1, 9, 9, 9, 1, 1, 9, 9, 0],
    [0, 9, 0, 9, 1, 0, 9, 9, 9, 9, 0],
    [1, 0, 0, 9, 9, 9, 0, 9, 9, 9, 0],
    [1, 1, 1, 0, 9, 9, 1, 9, 9, 9, 9],
    [9, 1, 9, 0, 9, 1, 1, 9, 9, 9, 0],
    [9, 9, 1, 0, 9, 0, 1, 1, 9, 9, 9],
    [9, 1, 9, 9, 9, 9, 9, 9, 9, 0, 9],
    [9, 9, 9, 9, 0, 0, 0, 0, 1, 9, 9],
    [9, 0, 1, 9, 0, 9, 0, 0, 9, 9, 9],
    [9, 9, 9, 1, 0, 9, 1, 9, 9, 9, 0],
    [0, 0, 0, 9, 9, 9, 1, 9, 9, 9, 0],
    [1, 0, 9, 9, 0, 1, 0, 9, 9, 9, 9],
    [1, 0, 9, 9, 9, 0, 9, 0, 9, 9, 0],
    [9, 9, 9, 9, 0, 0, 0, 0, 9, 1, 9],
    [0, 1, 9, 9, 9, 1, 9, 0, 9, 9, 0],
    [0, 1, 1, 9, 0, 9, 9, 1, 9, 9, 0],
    [1, 1, 9, 1, 9, 9, 0, 0, 9, 9, 1],
    [0, 9, 0, 0, 9, 1, 1, 9, 9, 9, 9],
    [9, 1, 9, 9, 0, 1, 1, 0, 9, 9, 9],
    [0, 9, 9, 1, 0, 0, 0, 9, 9, 9, 9],
    [1, 1, 1, 1, 1, 1, 0, 9, 9, 9, 9],
    [9, 1, 1, 9, 9, 1, 1, 9, 9, 9, 0],
    [0, 0, 9, 9, 0, 9, 1, 1, 9, 9, 9],
    [9, 9, 9, 9, 9, 9, 9, 9, 1, 0, 9],
    [9, 1, 0, 9, 9, 0, 0, 9, 9, 9, 0],
    [1, 1, 0, 0, 9, 9, 9, 1, 9, 9, 9],
    [0, 0, 9, 9, 9, 0, 9, 1, 9, 9, 0],
    [9, 0, 9, 0, 9, 9, 0, 0, 9, 9, 1],
    [0, 9, 1, 9, 9, 0, 0, 9, 9, 9, 0],
    [1, 0, 0, 0, 9, 9, 9, 0, 9, 9, 9],
    [9, 9, 1, 1, 9, 1, 9, 1, 9, 9, 0],
    [0, 9, 9, 9, 9, 0, 0, 9, 1, 9, 0],
    [1, 1, 9, 9, 0, 1, 9, 9, 9, 9, 1],
    [9, 0, 9, 9, 0, 1, 0, 0, 9, 9, 9],
    [1, 9, 1, 9, 1, 9, 9, 9, 9, 9, 0],
    [9, 9, 9, 9, 9, 9, 9, 9, 0, 1, 9],
    [0, 0, 0, 9, 1, 1, 0, 1, 9, 9, 9],
    [0, 9, 1, 9, 0, 0, 0, 9, 9, 9, 9],
    [1, 0, 9, 9, 9, 1, 0, 9, 9, 9, 0]
]
        SymbolicCNFConstraintForExtension = [
            [9, 9, 9, 9, 0, 1, 0, 9, 1, 1, 0, 9], [9, 9, 9, 0, 0, 1, 9, 9, 9, 9, 9, 0], [9, 0, 9, 9, 9, 9, 9, 9, 1, 0, 9, 9],
            [0, 9, 0, 9, 1, 1, 9, 0, 9, 9, 9, 9], [9, 9, 9, 9, 9, 0, 9, 9, 0, 1, 1, 0], [9, 9, 9, 0, 1, 0, 1, 0, 9, 9, 9, 9],
            [9, 9, 9, 9, 1, 1, 9, 0, 9, 9, 0, 0], [9, 9, 0, 9, 9, 9, 9, 1, 9, 1, 0, 9], [9, 9, 1, 9, 9, 9, 9, 0, 0, 9, 9, 9],
            [9, 9, 9, 1, 9, 1, 1, 9, 0, 0, 9, 9], [9, 9, 9, 9, 0, 1, 0, 0, 9, 9, 0, 9], [9, 9, 9, 1, 1, 9, 0, 0, 9, 1, 9, 9],
            [9, 9, 9, 9, 0, 9, 0, 1, 1, 1, 1, 1], [9, 9, 1, 9, 1, 0, 0, 9, 1, 1, 9, 0], [9, 9, 9, 9, 9, 1, 1, 0, 9, 9, 1, 1],
            [9, 1, 9, 9, 0, 9, 0, 0, 0, 9, 9, 9], [1, 0, 9, 0, 9, 0, 9, 9, 9, 0, 9, 9], [9, 1, 9, 9, 1, 0, 9, 0, 0, 9, 9, 9],
            [0, 9, 9, 9, 9, 9, 9, 9, 0, 9, 1, 9], [1, 0, 9, 9, 9, 1, 9, 1, 9, 9, 1, 1], [1, 9, 9, 9, 9, 9, 9, 9, 1, 9, 9, 9],
            [9, 9, 9, 9, 0, 9, 9, 9, 0, 0, 0, 1], [9, 9, 9, 1, 9, 9, 9, 9, 0, 0, 0, 9], [9, 1, 9, 9, 9, 9, 1, 9, 0, 9, 0, 9],
            [9, 1, 9, 9, 9, 9, 9, 9, 9, 1, 9, 9], [9, 9, 9, 9, 9, 1, 1, 9, 1, 1, 1, 0], [9, 9, 9, 1, 1, 9, 0, 9, 1, 0, 1, 9],
            [1, 9, 9, 9, 1, 1, 9, 1, 9, 9, 9, 9], [9, 9, 9, 1, 9, 9, 9, 9, 9, 9, 9, 1], [9, 9, 9, 9, 0, 0, 0, 0, 1, 9, 9, 9],
            [9, 9, 9, 9, 0, 1, 1, 1, 1, 0, 9, 1], [9, 9, 9, 9, 1, 1, 9, 9, 0, 1, 9, 1], [9, 0, 0, 9, 1, 9, 1, 1, 9, 9, 9, 0],
            [9, 9, 9, 9, 1, 0, 1, 1, 9, 0, 0, 0], [9, 9, 9, 9, 1, 0, 0, 1, 9, 0, 9, 1], [9, 9, 9, 9, 0, 1, 1, 1, 9, 0, 0, 9],
            [9, 9, 9, 0, 9, 9, 1, 9, 9, 1, 9, 0], [9, 9, 9, 9, 0, 0, 9, 1, 1, 9, 1, 1], [9, 0, 9, 9, 1, 9, 0, 9, 9, 0, 9, 9],
            [9, 9, 9, 9, 0, 9, 0, 0, 0, 1, 9, 1], [1, 9, 9, 9, 0, 0, 9, 9, 9, 9, 0, 9], [0, 0, 9, 9, 1, 0, 1, 9, 9, 9, 9, 1],
            [9, 9, 9, 9, 0, 0, 1, 0, 9, 9, 0, 9], [9, 9, 0, 9, 9, 9, 9, 9, 1, 9, 0, 9], [9, 9, 1, 0, 1, 1, 9, 1, 9, 9, 9, 9],
            [9, 9, 9, 9, 0, 9, 1, 0, 9, 9, 1, 0], [9, 9, 1, 9, 9, 9, 9, 9, 9, 9, 1, 9], [9, 9, 9, 9, 0, 9, 9, 9, 0, 0, 1, 0],
            [0, 9, 9, 9, 9, 9, 9, 9, 0, 1, 9, 9], [9, 9, 9, 9, 1, 0, 0, 0, 9, 9, 9, 0], [9, 9, 0, 9, 9, 1, 0, 1, 9, 0, 9, 0],
            [9, 1, 9, 0, 1, 9, 9, 9, 0, 9, 1, 9], [9, 9, 9, 1, 1, 1, 9, 9, 1, 9, 1, 9], [9, 9, 9, 0, 9, 0, 9, 1, 9, 9, 9, 0]
        ]
        for k in range(64):
            y += [xout[r][P[k]]]
        for i in range(16):
            X = list([])
            for j in range(4):
                X += [xin[r][4 * i + j]]
            for j in range(4):
                X += [y[4 * i + j]]
            X += [p[r][i]]
            X += [q[r][i]]
            X += [m[r][i]]
            for j in range(len(SymbolicCNFConstraintForSbox)):
                clauseseq = ""
                for k in range(11):
                    # 1 代表该变量取反 (-x)，0 代表正向变量 (x)
                    if (SymbolicCNFConstraintForSbox[j][k] == 1):
                        clauseseq += "-" + str(X[k] + 1) + " "
                    if (SymbolicCNFConstraintForSbox[j][k] == 0):
                        clauseseq += str(X[k] + 1) + " "
                clauseseq += "0" + "\n"
                file.write(clauseseq)
            
            if r == 0: # 头部扩展层
                V_vars = [v_b[4 * i + j] for j in range(4)]
                X_ext = X[0:8] + V_vars # 拼接变量：dx (4位), dy (4位), v (4位)
                for j in range(len(SymbolicCNFConstraintForExtension)):
                    clauseseq = ""
                    for k in range(12):
                        if (SymbolicCNFConstraintForExtension[j][k] == 1):
                            clauseseq += "-" + str(X_ext[k] + 1) + " "
                        if (SymbolicCNFConstraintForExtension[j][k] == 0):
                            clauseseq += str(X_ext[k] + 1) + " "
                    clauseseq += "0\n"
                    file.write(clauseseq)
                    
            if r == Round - 1: # 尾部扩展层
                V_vars = [v_f[4 * i + j] for j in range(4)]
                X_ext = X[0:8] + V_vars
                for j in range(len(SymbolicCNFConstraintForExtension)):
                    clauseseq = ""
                    for k in range(12):
                        if (SymbolicCNFConstraintForExtension[j][k] == 1):
                            clauseseq += "-" + str(X_ext[k] + 1) + " "
                        if (SymbolicCNFConstraintForExtension[j][k] == 0):
                            clauseseq += str(X_ext[k] + 1) + " "
                    clauseseq += "0\n"
                    file.write(clauseseq)
        # --------------------------------------------------------  

        
    Main_Vars = list([])
    for r in range(R_b, R_b + R_m):
        for i in range(16):
            Main_Vars += [p[r][i]]
            Main_Vars += [q[r][i]]
            Main_Vars += [m[r][i]]
    GenSequentialEncoding(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, file)
    
    # 将松井策略约束条件写入文件
    for matsui_count in range(0, MatsuiCount):
        StartingRound = MatsuiRoundIndex[matsui_count][0]
        EndingRound = MatsuiRoundIndex[matsui_count][1]
        LeftNode = 16 * StartingRound * 3
        RightNode = 16 * EndingRound * 3 - 1
        PartialCardinalityCons = Probability - DifferentialProbabilityBound[StartingRound] - DifferentialProbabilityBound[Round - EndingRound]
        GenMatsuiConstraint(Main_Vars, auxiliary_var_u, Main_Var_Num, CardinalityCons, LeftNode, RightNode, PartialCardinalityCons, file)
    file.close()
    
    # 调用系统命令行执行 Cadical 求解器
    order = "~/Install/cadical/build/cadical " + "Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf > Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out"
    os.system(order)
    
    # 从求解器的输出文件中提取 "SATISFIABLE"（有解）和 "UNSATISFIABLE"（无解）信息
    order = "sed -n '/s SATISFIABLE/p' Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out > SatSolution.out"
    os.system(order)
    order = "sed -n '/s UNSATISFIABLE/p' Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out > UnsatSolution.out"
    os.system(order)
    satsol = open("SatSolution.out")
    unsatsol = open("UnsatSolution.out")
    satresult = satsol.readlines()
    unsatresult = unsatsol.readlines()
    satsol.close()
    unsatsol.close()
    if ((len(satresult) == 0) and (len(unsatresult) > 0)):
        flag = False
    if ((len(satresult) > 0) and (len(unsatresult) == 0)):
        flag = True
        
      
        try:
            solution_file_name = "Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out"
            with open(solution_file_name, "r") as sol_file:
                lines = sol_file.readlines()
                v_lines = [line for line in lines if line.startswith("v ")]
                
                true_vars = set()
                for line in v_lines:
                    vars_str = line.strip().split()[1:]
                    for v in vars_str:
                        if int(v) > 0:
                            true_vars.add(int(v))
                
                #  找出具体是哪几个 bit 被打上了 v 标签
                active_v_b_bits = [i for i in range(64) if (v_b[i] + 1) in true_vars]
                active_v_f_bits = [i for i in range(64) if (v_f[i] + 1) in true_vars]
                
                # 将 bit 编号映射回 S 盒编号 (每个S盒包含4个bit，所以除以4向下取整)
                active_sbox_b = sorted(list(set([bit // 4 for bit in active_v_b_bits])))
                active_sbox_f = sorted(list(set([bit // 4 for bit in active_v_f_bits])))
                
                #  计算具体的比特总数
                active_v_b = len(active_v_b_bits)
                active_v_f = len(active_v_f_bits)
                
               
                print("    -> 头部波及 S 盒: " + str(active_sbox_b) + " | 尾部波及 S 盒: " + str(active_sbox_f))
                print("    -> 头部实际猜测: " + str(active_v_b) + " bit | 尾部实际猜测: " + str(active_v_f) + " bit")
                
                total_key_guess = active_v_b + active_v_f
                print("    -> 总猜测密钥量: 2^" + str(total_key_guess) + " bit ")
                
        except FileNotFoundError:
            pass
        

    order = "rm SatSolution.out"
    os.system(order)
    order = "rm UnsatSolution.out"
    os.system(order)
    
    os.system("rm Round" + str(Round) + "-Probability" + str(Probability) + "-solution.out")
    # 清理删除临时生成的 cnf 问题文件
    order = "rm Problem-Round" + str(Round) + "-Probability" + str(Probability) + ".cnf"
    os.system(order)
    time_end = time.time()
    
    # 打印当前轮数和概率的搜索结果及耗时
    if (flag == True):
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Sat; TotalCost: " + str(time_end - time_start))
    else:
        print("Round:" + str(Round) + "; Probability: " + str(Probability) + "; Unsat; TotalCost: " + str(time_end - time_start))
    return flag
            
# ==================================
# 主函数
# ==================================
CountProbability = InitialLowerBound
TotalTimeStart = time.time()
for totalround in range(SearchRoundStart, SearchRoundEnd):
    flag = False
    time_start = time.time()
    MatsuiRoundIndex = []
    MatsuiCount = 0
    
    # 在选项1（GroupConstraintChoice == 1）的设定下，生成松井策略的分组条件
    if (GroupConstraintChoice == 1):
        for group in range(0, GroupNumForChoice1):
            for round in range(1, totalround - group + 1):
                MatsuiRoundIndex.append([])
                MatsuiRoundIndex[MatsuiCount].append(group)
                MatsuiRoundIndex[MatsuiCount].append(group + round)
                MatsuiCount += 1
                
    # 将松井条件写入日志文件
    file = open("MatsuiCondition.out", "a")
    resultseq = "Round: " + str(totalround) + "; Partial Constraint Num: " + str(MatsuiCount) + "\n"
    file.write(resultseq)
    file.write(str(MatsuiRoundIndex) + "\n")
    file.close()
    
   # 不断递增目标概率边界，直到找到能使模型满足的解
  
    R_m_temp = totalround - 2 # 假设头尾各1轮
    if R_m_temp < 1: 
        R_m_temp = totalround
    Max_Probability = 16 * R_m_temp * 3 
    
    while (flag == False):
        if CountProbability > Max_Probability:
            print("    -> 已超出理论最大概率，当前头尾激活限制太严，该结构下无解！")
            break # 强制跳出死循环
            
        flag = Decision(totalround, CountProbability, MatsuiRoundIndex, MatsuiCount, flag)
        CountProbability += 1
        
    if flag == False:
        print("    -> 第 " + str(totalround) + " 轮搜索失败，结束程序。")
        break # 如果无解，直接结束外层循环，不再继续搜下一轮
        
    DifferentialProbabilityBound[totalround] = CountProbability - 1
    time_end = time.time()
    
    # 记录该轮的最优概率界限及运算时间
    file = open("RunTimeSummarise.out", "a")
    resultseq = "Round: " + str(totalround) + "; Differential Probability: " + str(DifferentialProbabilityBound[totalround]) + "; Runtime: " + str(time_end - time_start) + "\n"
    file.write(resultseq)
    file.close()

# 打印最终统计的各轮差分概率最优边界及总耗时
print(str(DifferentialProbabilityBound))
TotalTimeEnd = time.time()
print("Total Runtime: " + str(TotalTimeEnd - TotalTimeStart))
file = open("RunTimeSummarise.out", "a")
resultseq = "Total Runtime: " + str(TotalTimeEnd - TotalTimeStart)
file.write(resultseq)