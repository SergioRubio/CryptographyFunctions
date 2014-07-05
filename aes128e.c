#include <stdint.h>
#include <stdio.h>
#include "aes128e.h"

/* Multiplication by two in GF(2^8). Multiplication by three is xtime(a) ^ a */
#define xtime(a) ( ((a) & 0x80) ? (((a) << 1) ^ 0x1b) : ((a) << 1) )

/* The S-box table */
static const unsigned char sbox[256] = {
    0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5,
    0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
    0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0,
    0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
    0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc,
    0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
    0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a,
    0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
    0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0,
    0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
    0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b,
    0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
    0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85,
    0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
    0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5,
    0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
    0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17,
    0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
    0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88,
    0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
    0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c,
    0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
    0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9,
    0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
    0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6,
    0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
    0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e,
    0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
    0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94,
    0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
    0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68,
    0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16 };

/* The round constant table (needed in KeyExpansion) */
static const unsigned char rcon[10] = {
    0x01, 0x02, 0x04, 0x08, 0x10, 
    0x20, 0x40, 0x80, 0x1b, 0x36 };

/* Cyclic shift of the bytes of a word */
void rotate(unsigned char *w) {

    /* Copy of the first char of the word in a temporal char */
    unsigned char c = w[0];

    /* Shifting of each char with the next one */
    int i;
    for (i = 0; i < 3; ++i) {
        w[i] = w[i + 1];
    }

    /* Copy of the temporal char in the last char of the word */
    w[3] = c;
}

/* The keyExpansion routine takes the cipher key k and generates a key schedule with Nb*(Nr + 1) words */
void keyExpansion(const unsigned char *k, unsigned char *expK) {
    
    /* Iterator for the round constant table */
    int rconIt = 0;

    unsigned char temp[4];

    /* The first 16 words of the expanded key are filled with the cipher key */
    int i;
    for (i = 0; i < 16; ++i) {
        expK[i] = k[i];
    }

    /* From word 16 until word Nb*(Nr + 1) = 176 */
    int cont = 16;
    while (cont < 176) {

        /* Copy in temp of the previous word */
        for (i = 0; i < 4; ++i) {
            temp[i] = expK[cont + i - 4];
        }

        /* For words in positions that are multiple of Nk */
        if (cont%16 == 0) {

            /* Cyclic shift of the bytes in the word temp */
            rotate(temp);
            
            /* Table lookup to the four bytes of the word temp */
            for (i = 0; i < 4; ++i) {
                temp[i] = sbox[temp[i]];
            }

            /* XOR with a round constant of the round constant word array rcon */
            temp[0] = temp[0] ^ rcon[rconIt];
            ++rconIt;
        }

        /* XOR of the previous word (temp) and the word Nk = 16 positions earlier */
        for(i = 0; i < 4; ++i) {
            expK[cont] = expK[cont - 16] ^ temp[i];
            ++cont;
        }
    }
}

/* A round key is added to the state by a bitwise XOR operation*/
void addRoundKey(unsigned char state[4][4], unsigned char *k, int round) {

    /* Loop of the matrix by columns and application of XOR in each word of state 
       with Nb = 16 words of the key schedule from the word in position round */
    int i, j;
    int c = 0;
    for (i = 0; i < 4; ++i) {
        for (j = 0; j < 4; ++j) {
            state[j][i] = state[j][i] ^ k[16*round + c];
            ++c;
        }
    }
}

/* Non-linear byte substitution that operates on each byte of the state using S-box table */
void subBytes(unsigned char state[4][4]) {

    /* Substitution of each byte of the state with the corresponding byte in S-box.
       The value of each byte (0 - 255) indicates the index of the corresponding byte in S-box */
    int i, j;
    for (i = 0; i < 4; ++i) {
        for (j = 0; j < 4; ++j) {
            state[i][j] = sbox[state[i][j]];        
        }    
    }
}

/* ShiftRows shift cyclically the bytes in the last 3 rows of the state */
void shiftRows(unsigned char state[4][4]) {

    unsigned char temp[4];

    /* The number of bytes for shifting is 1 for row 1, 2 for row 2 and 3 for row 3. Row 0 is not shifted */
    int i, j, k;    
    for (i = 1; i < 4; ++i) {
        
        /* Shifting of the row i */ 
        for (j = 0; j < 4; ++j) {
            temp[j] = state[i][(i + j)%4];      
        }
        
        /* Copy of the shifted row to the state */
        for (k = 0; k < 4; ++k) {
            state[i][k] = temp[k];        
        }
    }
}

/* MixColumns operates on the state considering each column as polynomial 
   over GF(2^8) and multiplied modulo x^4 + 1 with a fixed polynomial */
void mixColumns(unsigned char state[4][4]) {

    unsigned char temp[4];

    /* The four bytes of each column are calculated using the function xtime and stored in temp.
       Multiplication by two in GF(2^8) is xtime(x) and multiplication by three is xtime(x) ^ x */
    int i, j;    
    for (i = 0; i < 4; ++i) {
        temp[0] = ((xtime(state[0][i])) ^ (xtime(state[1][i]) ^ state[1][i]) ^ state[2][i] ^ state[3][i]);
        temp[1] = (state[0][i] ^ (xtime(state[1][i])) ^ (xtime(state[2][i]) ^ state[2][i]) ^ state[3][i]);
        temp[2] = (state[0][i] ^ state[1][i] ^ (xtime(state[2][i])) ^ (xtime(state[3][i]) ^ state[3][i]));
        temp[3] = ((xtime(state[0][i]) ^ state[0][i]) ^ state[1][i] ^ state[2][i] ^ (xtime(state[3][i])));

        /* Copy of the calculated column stored in temp to the state */
        for (j = 0; j < 4; ++j) {
            state[j][i] = temp[j];
        }   
    }  
}

/* Under the 16-byte key at k, encrypt the 16-byte plaintext at p and store it at c. */
void aes128e(unsigned char *c, const unsigned char *p, const unsigned char *k) {
    
    /* State matrix of 16 bytes */
    unsigned char state[4][4];

    /* Expansion key of size Nb*(Nr + 1) = 16*11 = 176 */
    unsigned char expK[176];

    /* Key expansion for generating the key schedule */
    keyExpansion(k, expK);

    /* Input plaintext copied to state matrix */
    int i, j;
    for (i = 0; i < 4; ++i) {   
        for (j = 0; j < 4; ++j) {
            state[i][j] = p[i + 4*j];
        }
    }

    /* First addRoundKey with round 0 */
    addRoundKey(state, expK, 0);

    /* First (Nr - 1) rounds */
    for (i = 1; i < 10; ++i) {
        subBytes(state);
        shiftRows(state);
        mixColumns(state);
        addRoundKey(state, expK, i);
    }

    /* Final round without mixColumns */
    subBytes(state);
    shiftRows(state);
    addRoundKey(state, expK, 10);

    /* State matrix copied to output ciphertext */
    for (i = 0; i < 4; ++i) {   
        for (j = 0; j < 4; ++j) {
            c[i + 4*j] = state[i][j];
        }
    }
}


