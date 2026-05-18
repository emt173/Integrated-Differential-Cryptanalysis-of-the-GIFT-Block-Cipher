#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>

// =========================================================================
// 此处填写gift.py中的输入输出差分
// =========================================================================
const char* DIN_STR = "1100000000000000000000000000000000000000000000000000000000000000";
const char* DOUT_STR = "0000000000100000000000010000000000000000000000000000010001000000";
// 将原本的 8 bit 扩充为涵盖这 4 个 S 盒的完整 16 bit
const int V_F_BITS[] = {8, 9, 10, 11, 20, 21, 22, 23, 52, 53, 54, 55, 56, 57, 58, 59};
const int V_F_NUM = 16;


const uint8_t SBOX[16] = {1, 10, 4, 12, 6, 15, 3, 9, 2, 13, 11, 7, 5, 0, 8, 14};
const uint8_t INV_SBOX[16] = {13, 0, 8, 6, 2, 12, 4, 11, 14, 7, 1, 10, 3, 9, 15, 5};
const int PBOX[64] = {0, 17, 34, 51, 48, 1, 18, 35, 32, 49, 2, 19, 16, 33, 50, 3,
                      4, 21, 38, 55, 52, 5, 22, 39, 36, 53, 6, 23, 20, 37, 54, 7,
                      8, 25, 42, 59, 56, 9, 26, 43, 40, 57, 10, 27, 24, 41, 58, 11,
                      12, 29, 46, 63, 60, 13, 30, 47, 44, 61, 14, 31, 28, 45, 62, 15};
int INV_PBOX[64];

uint64_t str2uint(const char* str) {
    uint64_t res = 0;
    for(int i=0; i<64; i++) {
        if(str[i] == '1') res |= (1ULL << i);
    }
    return res;
}


uint64_t apply_sbox(uint64_t state) {
    uint64_t out = 0;
    for(int i=0; i<16; i++) {
        // 强制分配权重：第0位是MSB(左移3)，第3位是LSB
        int b0 = (state >> (4*i + 0)) & 1; 
        int b1 = (state >> (4*i + 1)) & 1;
        int b2 = (state >> (4*i + 2)) & 1;
        int b3 = (state >> (4*i + 3)) & 1; 
        
        uint8_t nibble = (b0 << 3) | (b1 << 2) | (b2 << 1) | b3;
        uint8_t s_out = SBOX[nibble];
        
      
        out |= ((uint64_t)((s_out >> 3) & 1) << (4*i + 0));
        out |= ((uint64_t)((s_out >> 2) & 1) << (4*i + 1));
        out |= ((uint64_t)((s_out >> 1) & 1) << (4*i + 2));
        out |= ((uint64_t)((s_out >> 0) & 1) << (4*i + 3));
    }
    return out;
}

uint64_t apply_pbox(uint64_t state) {
    uint64_t out = 0;
    for(int i=0; i<64; i++) {
        if((state >> i) & 1) out |= (1ULL << PBOX[i]);
    }
    return out;
}

uint64_t gift_round(uint64_t state, uint64_t rk) {
    state = apply_sbox(state);
    state = apply_pbox(state);
    state ^= rk;
    return state;
}


uint64_t apply_inv_sbox(uint64_t state) {
    uint64_t out = 0;
    for(int i=0; i<16; i++) {
        int b0 = (state >> (4*i + 0)) & 1; 
        int b1 = (state >> (4*i + 1)) & 1;
        int b2 = (state >> (4*i + 2)) & 1;
        int b3 = (state >> (4*i + 3)) & 1; 
        
        uint8_t nibble = (b0 << 3) | (b1 << 2) | (b2 << 1) | b3;
        uint8_t s_out = INV_SBOX[nibble];
        
        out |= ((uint64_t)((s_out >> 3) & 1) << (4*i + 0));
        out |= ((uint64_t)((s_out >> 2) & 1) << (4*i + 1));
        out |= ((uint64_t)((s_out >> 1) & 1) << (4*i + 2));
        out |= ((uint64_t)((s_out >> 0) & 1) << (4*i + 3));
    }
    return out;
}

uint64_t apply_inv_pbox(uint64_t state) {
    uint64_t out = 0;
    for(int i=0; i<64; i++) {
        if((state >> i) & 1) out |= (1ULL << INV_PBOX[i]);
    }
    return out;
}

uint64_t partial_decrypt_with_erk(uint64_t c, uint64_t erk) {
    uint64_t state = apply_inv_pbox(c);
    state ^= erk;
    state = apply_inv_sbox(state);
    return state;
}

uint64_t rand64() {
    return ((uint64_t)rand() << 48) ^ ((uint64_t)rand() << 32) ^ ((uint64_t)rand() << 16) ^ rand();
}


int main() {
    for(int i=0; i<64; i++) INV_PBOX[PBOX[i]] = i;
    srand(time(NULL));

    uint64_t din = str2uint(DIN_STR);
    uint64_t dout = str2uint(DOUT_STR);
    int KEY_SPACE = 1 << V_F_NUM; 

    uint64_t mask = 0;
    for(int i=0; i<16; i++) {
        if(((dout >> (4*i)) & 0xF) != 0) {
            mask |= (0xFULL << (4*i));
        }
    }

    printf("========== 1. 搭建靶场与收集数据 ==========\n");
    int N = 2000000;
    uint64_t *C1 = malloc(N * sizeof(uint64_t));
    uint64_t *C2 = malloc(N * sizeof(uint64_t));
    int right_pairs[10000];
    int num_rp = 0;
    
    uint64_t target_key_bits = 0;
    int attempt = 1;

    printf("开始生成 %d 万对明密文...\n", N/10000);
    while(num_rp == 0) {
        uint64_t real_rk[4];
        for(int i=0; i<4; i++) real_rk[i] = rand64();

        uint64_t real_erk = apply_inv_pbox(real_rk[3]);
        target_key_bits = 0;
        for(int i=0; i<V_F_NUM; i++) {
            if((real_erk >> V_F_BITS[i]) & 1) target_key_bits |= (1 << i);
        }

        for(int i=0; i<N; i++) {
            uint64_t p1 = rand64();
            uint64_t p2 = p1 ^ din; 
            uint64_t c1 = p1, c2 = p2;
            
            for(int r=0; r<4; r++) {
                c1 = gift_round(c1, real_rk[r]);
                c2 = gift_round(c2, real_rk[r]);
            }
            C1[i] = c1;
            C2[i] = c2;
            
            uint64_t diff_S = apply_inv_pbox(c1 ^ c2);
            if((diff_S & ~mask) == 0) {
                if (num_rp < 10000) right_pairs[num_rp++] = i;
            }
        }
        if(num_rp == 0) {
            printf("  -> 第 %d 次尝试的随机密钥概率过低，正在更换密钥重试...\n", attempt++);
        }
    }

    printf("\n在第 %d 次尝试中，成功找到了 %d 对有效密文对！\n", attempt, num_rp);
    printf("本次演习中，真实的第4轮目标密钥片段为: 0x%02lX\n", target_key_bits);

    printf("\n========== 2. 等效局部解密 ==========\n");
    printf("开始对 2^%d = %d 种密钥可能进行尝试...\n", V_F_NUM, KEY_SPACE);
    
    int best_guess = 0;
    int max_score = 0;

    for(int guess = 0; guess < KEY_SPACE; guess++) {
        uint64_t guess_erk = 0;
        for(int i=0; i<V_F_NUM; i++) {
            if((guess >> i) & 1) guess_erk |= (1ULL << V_F_BITS[i]);
        }

        int score = 0;
        for(int j=0; j<num_rp; j++) {
            int pair_idx = right_pairs[j];
            uint64_t x1 = partial_decrypt_with_erk(C1[pair_idx], guess_erk);
            uint64_t x2 = partial_decrypt_with_erk(C2[pair_idx], guess_erk);
            
            if((x1 ^ x2) == dout) score++; 
            
  
            if (j == 30 && score == 0) {
                break;
            }
        }
        
        if(score > max_score) {
            max_score = score;
            best_guess = guess;
        }
    }

    printf("\n========== 3. 攻击结果 ==========\n");
    printf("最高得分: %d 分\n", max_score);
    printf("得分最高的猜测密钥: 0x%02X\n", best_guess);
    if(best_guess == target_key_bits) {
        printf("\n[破解完成]\n");
    } else {
        printf("\n[破解失败] 可能是受到概率碰撞干扰...\n");
    }

    free(C1); free(C2);
    return 0;
}