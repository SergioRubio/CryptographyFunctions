#include <stdint.h>
#include <stdlib.h>
#include "aes128ocb.h"
#include "aes128e.h"

/* Returns the exponent of the msb of 'value' */
static unsigned int msb(unsigned int value);

/* Returns the number of trailing zeros in 'value' */
static unsigned int ntz(unsigned int value);

/* Shift an array by bit one position to the left */
static void shiftB(unsigned char *s, const unsigned int len) {
    /* Carry of the previous byte */
    int c1 = 0;
    
    /* Carry of the current byte */
    int c2 = 0;

    int i = len - 1;
    while (i >= 0) {
        /* If the first bit of the current byte is one, carry true */
        if ((s[i])&0x80) c2 = 1;

        s[i] = (s[i])<<1;
        /* If there is previous carry, last bit of current byte to one */
        if (c1 == 1) s[i] = s[i] | 0x01;
        c1 = c2;
        c2 = 0;
        --i;
    }
}

/* Double function of the specification of OCB */
static void doubleB(unsigned char *l, const unsigned int len) {
    
    /* If first bit of the byte is one, shifting and xor with 135 */
    if ((l[0])&0x80) {
        shiftB(l, len);
        l[len - 1] = l[len - 1] ^ 0x87;    
    }
    /* If it is zero, only shifting */
    else shiftB(l, len);
}

/* Under the 16-byte (128-bit) key at k and the 12-byte (96-bit) nonce at n, encrypt the plaintext at p and store it at c. 
   The length of the plaintext is a multiple of 16 bytes given at len (e.g., len = 2 for a 32-byte p). The length of the
   ciphertext c is (len+1)*16 bytes. */
void aes128ocb(unsigned char *c, const unsigned char *k, const unsigned char *n, const unsigned char *p, const unsigned int len) {

    /* Array of zeros for use with aes128e */
    unsigned char zeros[16];
    int i;
    for (i = 0; i < 16; ++i) {
        zeros[i] = 0x00;
    }

    unsigned char l[16];
    unsigned char l_dollar[16];

    aes128e(l, zeros, k);
    /* Now l is l_star */

    doubleB(l, 16);
    /* Now l is l_dollar */

    /* We keep l_dollar for using it for calculate the tag */
    for (i = 0; i < 16; ++i) {
        l_dollar[i] = l[i];
    }

    doubleB(l, 16);
    /* Now l is l_0 */

    /* m = bitlen(P)/128 */
    unsigned int m = ((16*len)*8)/128;

    /* numL is the maximum value of trailing zeros for the given size m */
    unsigned int numL = msb(m) + 1;

    /* ls is the array of all the l_i arrays */
    unsigned char ls[numL][16];

    int a;
    for (a = 0; a < numL; ++a) {
        for (i = 0; i < 16; ++i) {
            ls[a][i] = l[i];
        }
        doubleB(l, 16);
    }

    /* Addition of 0x00000001 to the nonce */
    unsigned char nonce[20];
    nonce[0] = nonce[1] = nonce[2] = 0x00;
    nonce[3] = 0x01;

    a = 0;
    for (i = 4; i < 20; ++i) {
        nonce[i] = n[a];
        ++a;
    }

    /* Bottom is the integer value of the last 6 bits of nonce */
    unsigned int bottom = nonce[15]&0x3F;

    /* Temporal array for aes128e with last 6 bits of nonce to zero */
    unsigned char top[16];
    
    for (i = 0; i < 16; ++i) {
        top[i] = nonce[i];
    }
    top[15] = nonce[15]&0xC0;

    /* Calculation of ktop using the block cipher */
    unsigned char ktop[16];

    aes128e(ktop, top, k);

    /* Stretch is ktop concatenated with the xor of the bits 1...64 and 9...72 of ktop */
    unsigned char stretch[24];
    
    for (i = 0; i < 16; ++i) {
        stretch[i] = ktop[i];
    }
    a = 0;
    for (i = 16; i < 24; ++i) {
        stretch[i] = (ktop[a] ^ ktop[a + 1]);
        ++a;
    }

    /* Array of the m offset arrays */
    unsigned char offset[m][16];

    /* Array of the m checksum arrays */
    unsigned char checksum[m][16];

    /* Temporal array for get stretch[1 + bottom...128 + bottom] */
    unsigned char tempS[24];
    
    for (i = 0; i < 24; ++i) {
        tempS[i] = stretch[i];
    }

    /* Shifting of stretch bottom times to the left */
    for (i = 0; i < bottom; ++i) {
        shiftB(tempS, 24);
    }

    /* Copy of temp array to offset and inicialization of checksum */
    for (i = 0; i < 16; ++i) {
        offset[0][i] = tempS[i];
        checksum[0][i] = 0x00;
    }

    /* Temporal arrays for use them with aes128 as plaintext and ciphertext */
    unsigned char temp1[16];
    unsigned char temp2[16];

    int ntzV;

    /* Counters */
    int countP1 = 0;
    int countP2 = 0;
    int countC = 0;
    
    /* Loop over the m blocks */
    for (i = 1; i <= m; ++i) {

        /* Number of trailing zeros in i */
        ntzV = ntz(i);

        /* Calculation of the offset_i with xor betwen offset_{i-1} and l_{ntz(i)} */
        for (a = 0; a < 16; ++a) {
            offset[i][a] = offset[i - 1][a] ^ ls[ntzV][a];
        }

        /* Calculation of xor betwen p_i and offset_i for use it in aes128 */
        for (a = 0; a < 16; ++a) {
            temp1[a] = (p[countP1] ^ offset[i][a]);
            ++countP1;
        }
        
        aes128e(temp2, temp1, k);

        /* Calculation of c_i with xor betwen offset_i and result of aes128 */
        for (a = 0; a < 16; ++a) {
           c[countC] = offset[i][a] ^ temp2[a];
           ++countC;
        }

        /* Calculation of checksum_i with the xor betwen checksum_{i-1} and p_i */
        for (a = 0; a < 16; ++a) {
            checksum[i][a] = checksum[i - 1][a] ^ p[countP2];
            ++countP2;
        }
    }

    unsigned char tag[16];
    unsigned char tempTag[16];
        
    /* Calculation of the xor betwen checksum_m, offset_m and l_dollar for use it in aes128 to calculate the tag */
    int w;
    for (w = 0; w < 16; ++w) {
        tempTag[w] = ((l_dollar[w] ^ offset[m][w]) ^ checksum[m][w]);
    }

    aes128e(tag, tempTag, k);

    /* Concatenation of the tag at the end of the ciphertext. 16*m is the 
    current lenght of the cipher lenght and 16*m +16 is the total lenght */
    int countTag = 0;
    for (a = 16*m; a < (16*m + 16); ++a) {
        c[a] = tag[countTag];
        ++countTag;
    }
}

/* Returns the exponent of the msb of 'value' */
static unsigned int msb(unsigned int value) {

	unsigned int index = 0;

    /* Loop while greater than one */
	while (value >>= 1) { 		 
		index++;
	}
	return index;
}

/* Returns the number of trailing zeros in 'value' */
static unsigned int ntz(unsigned int value) {

	unsigned int zeros = 0;

    /* Loop while the lsb is zero */
	while (!(value & 0x01)) {
 
        /* Shift to the right; that is, observe the next bit. */	
		value >>= 1;				
		zeros++;
	}
	return zeros;
}
