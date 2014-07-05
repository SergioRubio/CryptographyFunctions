#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "groestl256.h"

#define NUMBYTES 64

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

static void groestl_pad(unsigned char **m_pad, unsigned long long *len_pad, const unsigned char *m, const unsigned long long n);

/* Multiplication of a and b in GF(2^8) */
static char gmul(char a, char b) {
    char p = 0;
    char c;
    char hb;
    for (c = 0; c < 8; ++c) {
        if (b & 1) p ^= a;
        hb = (a & 0x80);
        a <<= 1;
        if (hb) a ^= 0x1b;
        b >>= 1;
    }
    return p;
}

/* Transformation that adds a round-dependent constant to the state (permutation P)*/
static void addRoundConstantP(unsigned char state[8][8], int round) {

    /* The round constant modifies only the first row of the state matrix.  
    The modification is an xor betwen each byte and (0x00 ^ round), (0x10 ^ round), etc */
    int i;
    for (i = 0; i < 8; ++i) {
        state[0][i] = (((0x00 ^ (i<<4)) ^ round) ^ state[0][i]);   
    }  
}

/* Transformation that adds a round-dependent constant to the state (permutation Q)*/
static void addRoundConstantQ(unsigned char state[8][8], int round) {

    unsigned char cons[8] = { 0xff, 0xef, 0xdf, 0xcf, 0xbf, 0xaf, 0x9f, 0x8f};

    /* The round constant modifies the first 7 rows with xor betwen each byte and 0xff */

    int i, j;
    for (i = 0; i < 7; ++i) {
        for (j = 0; j < 8; ++j) {
            state[i][j] = ((0xff) ^ state[i][j]);
        }
    }

    /* The modification of the last row is an xor betwen each byte and (cons[0] ^ round), (cons[1] ^ round), etc */
    for (i = 0; i < 8; ++i) {
        state[7][i] = (((cons[i]) ^ round) ^ state[7][i]);
    }
}

/* Non-linear byte substitution that operates on each byte of the state using S-box table */
static void subBytes(unsigned char state[8][8]) {

    /* Substitution of each byte of the state with the corresponding byte in S-box.
       The value of each byte indicates the index of the corresponding byte in S-box */
    int i, j;
    for (i = 0; i < 8; ++i) {
        for (j = 0; j < 8; ++j) {
            state[i][j] = sbox[state[i][j]];        
        }    
    }
}

/* Shift the bytes of the state within a row to the left by a number of positions (permutation P) */
static void shiftBytesP(unsigned char state[8][8]) {

    unsigned char temp[8];

    /* The number of bytes for shifting is 1 for row 1, 2 for row 2 and so on. Row 0 is not shifted */
    int i, j, k;    
    for (i = 1; i < 8; ++i) {
        
        /* Shifting of the row i */ 
        for (j = 0; j < 8; ++j) {
            temp[j] = state[i][(i + j)%8];      
        }
        
        /* Copy of the shifted row to the state */
        for (k = 0; k < 8; ++k) {
            state[i][k] = temp[k];        
        }
    }
}

/* Shift the bytes of the state within a row to the left by a number of positions (permutation Q) */
static void shiftBytesQ(unsigned char state[8][8]) {

    unsigned char temp[8];
    int sh[8] = { 1,3,5,7,0,2,4,6};

    /* The number of bytes for shifting is 1 for row 0, 3 for row 2, 5 for row 3, and so on using array sh. */
    int i, j, k;    
    for (i = 0; i < 8; ++i) {
        
        /* Shifting of the row i */ 
        for (j = 0; j < 8; ++j) {
            temp[j] = state[i][(sh[i] + j)%8];      
        }
        
        /* Copy of the shifted row to the state */
        for (k = 0; k < 8; ++k) {
            state[i][k] = temp[k];        
        }
    }
}

/* This transformation multiplies each column of state with circ(02, 02, 03, 04, 05, 03, 05, 07) in GF(2^8)*/
static void mixBytes(unsigned char state[8][8]) {

    unsigned char temp[8];
    int i, j;

    for (i = 0; i < 8; i++) {
        for (j = 0; j < 8; j++) {
          temp[j] = 
	        gmul(state[(j+0)%8][i], 2)^
	        gmul(state[(j+1)%8][i], 2)^
	        gmul(state[(j+2)%8][i], 3)^
	        gmul(state[(j+3)%8][i], 4)^
	        gmul(state[(j+4)%8][i], 5)^
	        gmul(state[(j+5)%8][i], 3)^
	        gmul(state[(j+6)%8][i], 5)^
	        gmul(state[(j+7)%8][i], 7);
        }

        /* Copy of the calculated column stored in temp to the state */
        for (j = 0; j < 8; j++) {
            state[j][i] = temp[j];
        }
    }
}

/* Permutation P */
static void permutP(unsigned char state[8][8]) {

    /* 10 rounds */
    int i;
    for (i = 0; i < 10; ++i) {
        addRoundConstantP(state, i);
        subBytes(state);
        shiftBytesP(state);
        mixBytes(state);
    }
}

/* Permutation Q */
static void permutQ(unsigned char state[8][8]) {

    /* 10 rounds */
    int i;
    for (i = 0; i < 10; ++i) {
        addRoundConstantQ(state, i);
        subBytes(state);
        shiftBytesQ(state);
        mixBytes(state);
    }
}

/* Hash the message at m and store the 32-byte hash at h. The length of m in bytes is given at n. */
void groestl256(unsigned char *h, const unsigned char *m, unsigned long long n) {

    /* An array for the padded message */
	unsigned char *m_pad;

    /* The length of the padded message (in 64-byte blocks) */					
	unsigned long long len_pad;			

    /* Perform the message padding */
	groestl_pad(&m_pad,&len_pad,m,n);	

    /* Initial value array */    
    unsigned char iv[8][8];

    int i, j;
    for (i = 0; i < 8; ++i) {
        for (j = 0; j < 8; ++j) {
            iv[j][i] = 0x00;
        }
    }

    iv[6][7] = 0x01;

    /* Iteration over the number of 64-bytes blocks of the padded message */

    int pad = 0;
    while (len_pad > 0) {

        /* 64-bytes of the current block of the message */
        unsigned char bc[8][8];

        for (i = 0; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                bc[j][i] = m_pad[i*8 + j + pad*64];
            }
        }

        /* Input state for the permutation P */
        unsigned char inputP[8][8];

        for (i = 0; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                inputP[i][j] = bc[i][j] ^ iv[i][j];
            }
        }

        /* Permutation P */
        permutP(inputP);    

        /* Input state for the permutation Q */
        unsigned char inputQ[8][8];

        for (i = 0; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                inputQ[i][j] = bc[i][j];
            }
        }

        /* Permutation Q */
        permutQ(inputQ);

        /* Compression function f */
        unsigned char f[8][8];

        for (i = 0; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                f[i][j] = inputP[i][j] ^ inputQ[i][j] ^ iv[i][j];
            }
        }

        unsigned char finalInput[8][8];

        for (i = 0; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                finalInput[i][j] = f[i][j];
            }
        }

        /* Permutation P for the output transformation */
        permutP(finalInput);

        unsigned char exit[8][8];

        for (i = 0; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                exit[i][j] = finalInput[i][j] ^ f[i][j];
            }
        }
        
        /* Truncation of the last 32 bytes */
        int c = 0;
        for (i = 4; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                h[c] = exit[j][i];
                ++c;
            }
        }

        /* In case that the length of the padded message is more than 64 bytes, the 
            initial value for the next block has to be the exit of the one before */
        for (i = 0; i < 8; ++i) {
            for (j = 0; j < 8; ++j) {
                iv[i][j] = f[i][j];
            }
        }

        --len_pad;
        ++pad;
    }

	free(m_pad); 								
}

/* Performs the message padding. The original message and its length (in bytes) are given at
	m and n, respectively. Reserves memory for the	padded message and stores it at m_pad. 
	The length (in 512-bit blocks) is stored at len_pad. */
static void groestl_pad(unsigned char **m_pad, unsigned long long *len_pad, const unsigned char *m, const unsigned long long n) {

	/* Compute the length of the padded message (in 64-byte blocks) */
	*len_pad = (n*8 + 65 + (-n*8 - 65) % 512) / 512;	

	/* Allocate memory for the padded message */
	*m_pad = (unsigned char*) calloc(*len_pad*NUMBYTES, sizeof(unsigned char));

	/* Copy m to m_pad */
	memcpy(*m_pad, m, n);

	/* Add a bit to the end of the original message */
	(*m_pad)[n] = 0x80;

	/* Add the 64-bit representation of ((N+w+65)/512) in the end of m_pad */
	(*m_pad)[*len_pad*NUMBYTES-8] = (unsigned char) (*len_pad >> 56);
	(*m_pad)[*len_pad*NUMBYTES-7] = (unsigned char) (*len_pad >> 48);
	(*m_pad)[*len_pad*NUMBYTES-6] = (unsigned char) (*len_pad >> 40);
	(*m_pad)[*len_pad*NUMBYTES-5] = (unsigned char) (*len_pad >> 32);
	(*m_pad)[*len_pad*NUMBYTES-4] = (unsigned char) (*len_pad >> 24);
	(*m_pad)[*len_pad*NUMBYTES-3] = (unsigned char) (*len_pad >> 16);
	(*m_pad)[*len_pad*NUMBYTES-2] = (unsigned char) (*len_pad >> 8);
	(*m_pad)[*len_pad*NUMBYTES-1] = (unsigned char) (*len_pad);
}

