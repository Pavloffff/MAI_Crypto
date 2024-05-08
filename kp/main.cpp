#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <time.h>
#include <random>

#define BlueMidnightWish256_DIGEST_SIZE 32
#define BlueMidnightWish256_BLOCK_SIZE 64

// #define EXPAND_1_ROUNDS 2
// #define EXPAND_2_ROUNDS 14

typedef unsigned char BitSequence;
typedef u_int64_t DataLength; // a typical 64-bit value
typedef enum {
    SUCCESS = 0,
    FAIL = 1,
    BAD_HASHLEN = 2,
    BAD_CONSECUTIVE_CALL_TO_UPDATE = 3
} HashReturn;

typedef struct {
    u_int32_t DoublePipe[32];
    BitSequence LastPart[BlueMidnightWish256_BLOCK_SIZE * 2];
} Data256;

typedef struct {
    int hashbitlen;
    u_int64_t bits_processed;
    Data256 pipe[1];
    int unprocessed_bits;
} hashState;

void printBits(BitSequence *str, int size) {
    for (int i = 0; i < size; i++) {
        unsigned char ch = str[i];
        for (int j = 7; j >= 0; j--) {
            putchar((ch & (1 << j)) ? '1' : '0');
        }
    }
    putchar('\n');
}

void invertBit(BitSequence *str, int index) {
    int cindex = index / 8;
    int position = index % 8;
    str[cindex] ^= (1 << (7 - position));
}

int countDifferentBits(BitSequence *str1, BitSequence *str2, int size) {
    int count = 0;
    for (int i = 0; i < size; i++) {
        unsigned char diff = str1[i] ^ str2[i];
        for (int j = 0; j < 8; j++) {
            if (diff & (1 << j)) {
                count++;
            }
        }
    }
    return count;
}

#define rotl32(x, n) (((x) << (n)) | ((x) >> (32 - (n))))
#define rotr32(x, n) (((x) >> (n)) | ((x) << (32 - (n))))

#define shl(x, n) ((x) << n)
#define shr(x, n) ((x) >> n)

/* BlueMidnightWish256 initial double chaining pipe */
const u_int32_t i256p2[16] = {
    0x40414243ul,
    0x44454647ul,
    0x48494a4bul,
    0x4c4d4e4ful,
    0x50515253ul,
    0x54555657ul,
    0x58595a5bul,
    0x5c5d5e5ful,
    0x60616263ul,
    0x64656667ul,
    0x68696a6bul,
    0x6c6d6e6ful,
    0x70717273ul,
    0x74757677ul,
    0x78797a7bul,
    0x7c7d7e7ful,
};

#define hashState256(x) ((x)->pipe)

#define s32_0(x) (shr((x), 1) ^ shl((x), 3) ^ rotl32((x), 4) ^ rotl32((x), 19))
#define s32_1(x) (shr((x), 1) ^ shl((x), 2) ^ rotl32((x), 8) ^ rotl32((x), 23))
#define s32_2(x) (shr((x), 2) ^ shl((x), 1) ^ rotl32((x), 12) ^ rotl32((x), 25))
#define s32_3(x) (shr((x), 2) ^ shl((x), 2) ^ rotl32((x), 15) ^ rotl32((x), 29))
#define s32_4(x) (shr((x), 1) ^ (x))
#define s32_5(x) (shr((x), 2) ^ (x))
#define r32_01(x) rotl32((x), 3)
#define r32_02(x) rotl32((x), 7)
#define r32_03(x) rotl32((x), 13)
#define r32_04(x) rotl32((x), 16)
#define r32_05(x) rotl32((x), 19)
#define r32_06(x) rotl32((x), 23)
#define r32_07(x) rotl32((x), 27)

/* Message expansion function 2 */
u_int32_t expand32_1(int i, u_int32_t* M32, u_int32_t* H, u_int32_t* Q)
{
    return (s32_1(Q[i - 16]) + s32_2(Q[i - 15]) + s32_3(Q[i - 14])
        + s32_0(Q[i - 13]) + s32_1(Q[i - 12]) + s32_2(Q[i - 11])
        + s32_3(Q[i - 10]) + s32_0(Q[i - 9]) + s32_1(Q[i - 8]) + s32_2(Q[i - 7])
        + s32_3(Q[i - 6]) + s32_0(Q[i - 5]) + s32_1(Q[i - 4]) + s32_2(Q[i - 3])
        + s32_3(Q[i - 2]) + s32_0(Q[i - 1])
        + ((i * (0x05555555ul) + rotl32(M32[(i - 16) % 16], ((i - 16) % 16) + 1)
               + rotl32(M32[(i - 13) % 16], ((i - 13) % 16) + 1)
               - rotl32(M32[(i - 6) % 16], ((i - 6) % 16) + 1))
            ^ H[(i - 16 + 7) % 16]));
}

/* Message expansion function 2 */
u_int32_t expand32_2(int i, u_int32_t* M32, u_int32_t* H, u_int32_t* Q)
{
    return (Q[i - 16] + r32_01(Q[i - 15]) + Q[i - 14] + r32_02(Q[i - 13])
        + Q[i - 12] + r32_03(Q[i - 11]) + Q[i - 10] + r32_04(Q[i - 9])
        + Q[i - 8] + r32_05(Q[i - 7]) + Q[i - 6] + r32_06(Q[i - 5]) + Q[i - 4]
        + r32_07(Q[i - 3]) + s32_4(Q[i - 2]) + s32_5(Q[i - 1])
        + ((i * (0x05555555ul) + rotl32(M32[(i - 16) % 16], ((i - 16) % 16) + 1)
               + rotl32(M32[(i - 13) % 16], ((i - 13) % 16) + 1)
               - rotl32(M32[(i - 6) % 16], ((i - 6) % 16) + 1))
            ^ H[(i - 16 + 7) % 16]));
}

void Compression256(u_int32_t* M32, u_int32_t* H, int rounds1, int rounds2)
{
    int i;
    u_int32_t XL32, XH32, W[32], Q[32];

    // printf("\n==============================================================");
    // printf("\n");
    // printf("\nBlock Contents:");
    // for (i = 0; i < 16; i++)
    //     printf("\n  M[%2d] = %08lX", i, M32[i]);

    /*  This part is the function f0 - in the documentation */

    /*  First we mix the message block *M32 (M in the documatation)        */
    /*  with the previous double pipe *H.                                  */
    /*  For a fixed previous double pipe, or fixed message block, this     */
    /*  part is bijection.                                                 */
    /*  This transformation diffuses every one bit difference in 5 words.  */
    W[0] = (M32[5] ^ H[5]) - (M32[7] ^ H[7]) + (M32[10] ^ H[10])
        + (M32[13] ^ H[13]) + (M32[14] ^ H[14]);
    W[1] = (M32[6] ^ H[6]) - (M32[8] ^ H[8]) + (M32[11] ^ H[11])
        + (M32[14] ^ H[14]) - (M32[15] ^ H[15]);
    W[2] = (M32[0] ^ H[0]) + (M32[7] ^ H[7]) + (M32[9] ^ H[9])
        - (M32[12] ^ H[12]) + (M32[15] ^ H[15]);
    W[3] = (M32[0] ^ H[0]) - (M32[1] ^ H[1]) + (M32[8] ^ H[8])
        - (M32[10] ^ H[10]) + (M32[13] ^ H[13]);
    W[4] = (M32[1] ^ H[1]) + (M32[2] ^ H[2]) + (M32[9] ^ H[9])
        - (M32[11] ^ H[11]) - (M32[14] ^ H[14]);
    W[5] = (M32[3] ^ H[3]) - (M32[2] ^ H[2]) + (M32[10] ^ H[10])
        - (M32[12] ^ H[12]) + (M32[15] ^ H[15]);
    W[6] = (M32[4] ^ H[4]) - (M32[0] ^ H[0]) - (M32[3] ^ H[3])
        - (M32[11] ^ H[11]) + (M32[13] ^ H[13]);
    W[7] = (M32[1] ^ H[1]) - (M32[4] ^ H[4]) - (M32[5] ^ H[5])
        - (M32[12] ^ H[12]) - (M32[14] ^ H[14]);
    W[8] = (M32[2] ^ H[2]) - (M32[5] ^ H[5]) - (M32[6] ^ H[6])
        + (M32[13] ^ H[13]) - (M32[15] ^ H[15]);
    W[9] = (M32[0] ^ H[0]) - (M32[3] ^ H[3]) + (M32[6] ^ H[6]) - (M32[7] ^ H[7])
        + (M32[14] ^ H[14]);
    W[10] = (M32[8] ^ H[8]) - (M32[1] ^ H[1]) - (M32[4] ^ H[4])
        - (M32[7] ^ H[7]) + (M32[15] ^ H[15]);
    W[11] = (M32[8] ^ H[8]) - (M32[0] ^ H[0]) - (M32[2] ^ H[2])
        - (M32[5] ^ H[5]) + (M32[9] ^ H[9]);
    W[12] = (M32[1] ^ H[1]) + (M32[3] ^ H[3]) - (M32[6] ^ H[6])
        - (M32[9] ^ H[9]) + (M32[10] ^ H[10]);
    W[13] = (M32[2] ^ H[2]) + (M32[4] ^ H[4]) + (M32[7] ^ H[7])
        + (M32[10] ^ H[10]) + (M32[11] ^ H[11]);
    W[14] = (M32[3] ^ H[3]) - (M32[5] ^ H[5]) + (M32[8] ^ H[8])
        - (M32[11] ^ H[11]) - (M32[12] ^ H[12]);
    W[15] = (M32[12] ^ H[12]) - (M32[4] ^ H[4]) - (M32[6] ^ H[6])
        - (M32[9] ^ H[9]) + (M32[13] ^ H[13]);

    // printf("\n");
    // printf("\n==============================================================");
    // printf("\n");
    // printf("\nThe content of W after the bijective transformation of M xor H");
    // for (i = 0; i < 16; i++)
    //     printf("\n  W[%2d] = %08lX", i, W[i]);

    /*  Diffuse the differences in every word in a bijective manner with s32_i,
     * and then add the values of the previous double pipe.*/
    Q[0] = s32_0(W[0]) + H[1];
    Q[1] = s32_1(W[1]) + H[2];
    Q[2] = s32_2(W[2]) + H[3];
    Q[3] = s32_3(W[3]) + H[4];
    Q[4] = s32_4(W[4]) + H[5];
    Q[5] = s32_0(W[5]) + H[6];
    Q[6] = s32_1(W[6]) + H[7];
    Q[7] = s32_2(W[7]) + H[8];
    Q[8] = s32_3(W[8]) + H[9];
    Q[9] = s32_4(W[9]) + H[10];
    Q[10] = s32_0(W[10]) + H[11];
    Q[11] = s32_1(W[11]) + H[12];
    Q[12] = s32_2(W[12]) + H[13];
    Q[13] = s32_3(W[13]) + H[14];
    Q[14] = s32_4(W[14]) + H[15];
    Q[15] = s32_0(W[15]) + H[0];

    // printf("\n");
    // printf("\n==============================================================");
    // printf("\n");
    // printf("\nFirst part of the quadrupled pipe Qa:");
    // for (i = 0; i < 16; i++)
    //     printf("\n  Q[%2d] = %08lX", i, Q[i]);

    /* This is the Message expansion or f_1 in the documentation.       */
    /* It has 16 rounds.                                                */
    /* Blue Midnight Wish has two tunable security parameters.          */
    /* The parameters are named EXPAND_1_ROUNDS and EXPAND_2_ROUNDS.    */
    /* The following relation for these parameters should is satisfied: */
    /* EXPAND_1_ROUNDS + EXPAND_2_ROUNDS = 16                           */

    // printf("\n");
    // printf("\n==============================================================");
    // printf("\n");
    // printf("\nSecond part of the quadrupled pipe Qb:");
    for (i = 0; i < rounds1; i++) {
        Q[i + 16] = expand32_1(i + 16, M32, H, Q);
        // printf("\n  Q[%2d] = %08lX", i + 16, Q[i + 16]);
    }
    for (i = rounds1; i < rounds1 + rounds2; i++) {
        Q[i + 16] = expand32_2(i + 16, M32, H, Q);
        // printf("\n  Q[%2d] = %08lX", i + 16, Q[i + 16]);
    }

    /* Blue Midnight Wish has two temporary cummulative variables that
     * accumulate via XORing */
    /* 16 new variables that are prooduced in the Message Expansion part. */
    XL32 = Q[16] ^ Q[17] ^ Q[18] ^ Q[19] ^ Q[20] ^ Q[21] ^ Q[22] ^ Q[23];
    XH32 = XL32 ^ Q[24] ^ Q[25] ^ Q[26] ^ Q[27] ^ Q[28] ^ Q[29] ^ Q[30] ^ Q[31];
    // printf("\n");
    // printf("\n==============================================================");
    // printf("\n");
    // printf("\nCumulative variables:");
    // printf("\n  XL = %08lX", XL32);
    // printf("\n  XH = %08lX", XH32);

    /*  This part is the function f_2 - in the documentation            */

    /*  Compute the double chaining pipe for the next message block.    */
    // printf("\n");
    // printf("\n==============================================================");
    // printf("\n");
    // printf("\nNew value of the double pipe:");
    H[0] = (shl(XH32, 5) ^ shr(Q[16], 5) ^ M32[0]) + (XL32 ^ Q[24] ^ Q[0]);
    // i = 0;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[1] = (shr(XH32, 7) ^ shl(Q[17], 8) ^ M32[1]) + (XL32 ^ Q[25] ^ Q[1]);
    // i = 1;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[2] = (shr(XH32, 5) ^ shl(Q[18], 5) ^ M32[2]) + (XL32 ^ Q[26] ^ Q[2]);
    // i = 2;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[3] = (shr(XH32, 1) ^ shl(Q[19], 5) ^ M32[3]) + (XL32 ^ Q[27] ^ Q[3]);
    // i = 3;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[4] = (shr(XH32, 3) ^ Q[20] ^ M32[4]) + (XL32 ^ Q[28] ^ Q[4]);
    // i = 4;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[5] = (shl(XH32, 6) ^ shr(Q[21], 6) ^ M32[5]) + (XL32 ^ Q[29] ^ Q[5]);
    // i = 5;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[6] = (shr(XH32, 4) ^ shl(Q[22], 6) ^ M32[6]) + (XL32 ^ Q[30] ^ Q[6]);
    // i = 6;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[7] = (shr(XH32, 11) ^ shl(Q[23], 2) ^ M32[7]) + (XL32 ^ Q[31] ^ Q[7]);
    // i = 7;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[8] = rotl32(H[4], 9) + (XH32 ^ Q[24] ^ M32[8])
        + (shl(XL32, 8) ^ Q[23] ^ Q[8]);
    // i = 8;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[9] = rotl32(H[5], 10) + (XH32 ^ Q[25] ^ M32[9])
        + (shr(XL32, 6) ^ Q[16] ^ Q[9]);
    // i = 9;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[10] = rotl32(H[6], 11) + (XH32 ^ Q[26] ^ M32[10])
        + (shl(XL32, 6) ^ Q[17] ^ Q[10]);
    // i = 10;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[11] = rotl32(H[7], 12) + (XH32 ^ Q[27] ^ M32[11])
        + (shl(XL32, 4) ^ Q[18] ^ Q[11]);
    // i = 11;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[12] = rotl32(H[0], 13) + (XH32 ^ Q[28] ^ M32[12])
        + (shr(XL32, 3) ^ Q[19] ^ Q[12]);
    // i = 12;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[13] = rotl32(H[1], 14) + (XH32 ^ Q[29] ^ M32[13])
        + (shr(XL32, 4) ^ Q[20] ^ Q[13]);
    // i = 13;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[14] = rotl32(H[2], 15) + (XH32 ^ Q[30] ^ M32[14])
        + (shr(XL32, 7) ^ Q[21] ^ Q[14]);
    // i = 14;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
    H[15] = rotl32(H[3], 16) + (XH32 ^ Q[31] ^ M32[15])
        + (shr(XL32, 2) ^ Q[22] ^ Q[15]);
    // i = 15;
    // printf("\n  H[%2d] = %08lX", i, H[i]);
}

HashReturn Init(hashState* state, int hashbitlen)
{
    int i;
    u_int32_t* H256;
    u_int64_t* H512;
    state->hashbitlen = 256;
    // #1 Between comments #1 and #2 add algorithm specific initialization
    state->bits_processed = 0;
    state->unprocessed_bits = 0;
    memcpy(hashState256(state)->DoublePipe, i256p2, 16 * sizeof(u_int32_t));

    // Printing intermediate values
    H256 = hashState256(state)->DoublePipe;
    // printf("\n==============================================================");
    // printf("\n");
    // printf("\nInitial double pipe value:");
    // for (i = 0; i < 16; i++)
    //     printf("\n  H[%2d] = %08lX", i, H256[i]);
    // #2 Between comments #1 and #2 add algorithm specific initialization
    return (SUCCESS);
}

HashReturn Update(
    hashState* state, const BitSequence* data, DataLength databitlen,
    int rounds1, int rounds2)
{
    u_int32_t *M32, *H256;
    u_int64_t *M64, *H512;
    int LastBytes;
    if (state->unprocessed_bits > 0) {
        if (state->unprocessed_bits + databitlen
            > BlueMidnightWish256_BLOCK_SIZE * 8) {
            return BAD_CONSECUTIVE_CALL_TO_UPDATE;
        } else {
            LastBytes = (int)databitlen >> 3; // LastBytes = databitlen / 8
            memcpy(
                hashState256(state)->LastPart + (state->unprocessed_bits >> 3),
                data, LastBytes);
            state->unprocessed_bits += (int)databitlen;
            databitlen = state->unprocessed_bits;
            M32 = (u_int32_t*)hashState256(state)->LastPart;
        }
    } else
        M32 = (u_int32_t*)data;

    H256 = hashState256(state)->DoublePipe;
    while (databitlen >= BlueMidnightWish256_BLOCK_SIZE * 8) {
        databitlen -= BlueMidnightWish256_BLOCK_SIZE * 8;
        // #1 Between comments #1 and #2 add algorithm specifics

        state->bits_processed += BlueMidnightWish256_BLOCK_SIZE * 8;
        Compression256(M32, H256, rounds1, rounds2);
        M32 += 16;
    }
    state->unprocessed_bits = (int)databitlen;
    if (databitlen > 0) {
        LastBytes = ((~(((-(int)databitlen) >> 3) & 0x01ff)) + 1)
            & 0x01ff; // LastBytes = Ceil(databitlen / 8)
        memcpy(hashState256(state)->LastPart, M32, LastBytes);
    }
    // #2 Between comments #1 and #2 add algorithm specifics
    return (SUCCESS);
}

HashReturn Final(hashState* state, BitSequence* hashval, int rounds1, int rounds2)
{
    u_int32_t *M32, *H256;
    u_int64_t *M64, *H512;
    DataLength databitlen;
    int LastByte, PadOnePosition;
    u_int32_t CONST32final[16] = { 0xaaaaaaa0ul, 0xaaaaaaa1ul, 0xaaaaaaa2ul,
        0xaaaaaaa3ul, 0xaaaaaaa4ul, 0xaaaaaaa5ul, 0xaaaaaaa6ul, 0xaaaaaaa7ul,
        0xaaaaaaa8ul, 0xaaaaaaa9ul, 0xaaaaaaaaul, 0xaaaaaaabul, 0xaaaaaaacul,
        0xaaaaaaadul, 0xaaaaaaaeul, 0xaaaaaaaful };

    int i;

    H256 = NULL;
    LastByte = (int)state->unprocessed_bits >> 3;
    PadOnePosition = 7 - (state->unprocessed_bits & 0x07);
    hashState256(state)->LastPart[LastByte]
        = (hashState256(state)->LastPart[LastByte]
              & (0xff << (PadOnePosition + 1)))
        ^ (0x01 << PadOnePosition);
    M64 = (u_int64_t*)hashState256(state)->LastPart;

    if (state->unprocessed_bits < 448) {
        memset((hashState256(state)->LastPart) + LastByte + 1, 0x00,
            BlueMidnightWish256_BLOCK_SIZE - LastByte - 9);
        databitlen = BlueMidnightWish256_BLOCK_SIZE * 8;
        M64[7] = state->bits_processed + state->unprocessed_bits;
    } else {
        memset((hashState256(state)->LastPart) + LastByte + 1, 0x00,
            BlueMidnightWish256_BLOCK_SIZE * 2 - LastByte - 9);
        databitlen = BlueMidnightWish256_BLOCK_SIZE * 16;
        M64[15] = state->bits_processed + state->unprocessed_bits;
    }

    M32 = (u_int32_t*)hashState256(state)->LastPart;
    H256 = hashState256(state)->DoublePipe;
    while (databitlen >= BlueMidnightWish256_BLOCK_SIZE * 8) {
        databitlen -= BlueMidnightWish256_BLOCK_SIZE * 8;
        // #1 Between comments #1 and #2 add algorithm specifics
        Compression256(M32, H256, rounds1, rounds2);
        M32 += 16;
    }
    // #2 Between comments #1 and #2 add algorithm specifics

    // This is the tweak for Blue Midnight Wish, to be submitted on 15 September
    // 2009. Below is a code for final invocation of the compression function
    // after digesting the whole padded message. Here, the role of the message
    // has the obtained final double pipe, and the role of the initial double
    // pipe is a constant.
    // printf("\n");
    // printf("\n--------------------------------------------------------------");
    // printf("\n");
    // printf("\nFINALIZATION\n");
    Compression256(H256, CONST32final, rounds1, rounds2);

    // printf("\n");
    // printf("\n--------------------------------------------------------------");
    // printf("\n");
    // printf("\nMessage Digest is\n");

    memcpy(hashval, CONST32final + 8, BlueMidnightWish256_DIGEST_SIZE);
    return (SUCCESS);
}

BitSequence *Hash(int hashbitlen, const BitSequence* data, DataLength databitlen,
    BitSequence* hashval, int rounds1, int rounds2)
{
    HashReturn qq;
    hashState state;

    qq = Init(&state, hashbitlen);
    if (qq != SUCCESS)
        exit(-1);
    qq = Update(&state, data, databitlen, rounds1, rounds2);
    if (qq != SUCCESS)
        exit(-1);
    qq = Final(&state, hashval, rounds1, rounds2);
    return hashval;
}

int main(int argc, char const* argv[])
{
    int i, bitlen = 256;
    BitSequence Msg[100001], MD[64], MD1[64];

    // int rounds1 = 2, rounds2 = 14;
    // printf("Enter count of expand1 rounds:\n");
    // scanf("%d", &rounds1);
    // getchar();
    // printf("Enter count of expand2 rounds:\n");
    // scanf("%d", &rounds2);
    // getchar();
    printf("Enter message:\n");

    char c;
    int sz = 0, capacity = 1;
    BitSequence *input = new BitSequence[capacity];
    while ((c = getchar()) != '\n') {
        if (sz >= capacity) {
            capacity *= 2;
            BitSequence *tmp = new BitSequence[capacity];
            for (int i = 0; i < capacity; i++) {
                tmp[i] = input[i];
            }
            delete[] input;
            input = tmp;
        }
        input[sz++] = c;
    }

    // printf("Message in 2 SS:\n");
    // printBits(input, sz);

    memcpy(Msg, input, sz);

    for (int i = 1; i <= 17; i++) {
        BitSequence *hashval = Hash(bitlen, Msg, 24, MD, i, 0);

        // printf("Hash 1 in 16 SS:\n");
        // for (i = 0; i < BlueMidnightWish256_DIGEST_SIZE; i++)
        //     printf("%02X", hashval[i]);
        // printf("\n");
        // printf("Hash 1 in 2 SS:\n");
        // printBits(hashval, BlueMidnightWish256_DIGEST_SIZE);

        // int randomIndex = distrib(gen);
        int randomIndex = 10 % sz;

        invertBit(input, randomIndex);
        memcpy(Msg, input, sz);
        
        // printf("Message in 2 SS with inverted bit %d:\n", randomIndex);
        // printBits(input, sz);
        
        BitSequence *hashval2 = Hash(bitlen, Msg, 24, MD1, i, 0);
        // printf("Hash 2 in 16 SS:\n");
        // for (i = 0; i < BlueMidnightWish256_DIGEST_SIZE; i++)
        //     printf("%02X", hashval2[i]);
        // printf("\n");
        // printf("Hash 2 in 2 SS:\n");
        // printBits(hashval2, BlueMidnightWish256_DIGEST_SIZE);

        printf("%d\n", 
            countDifferentBits(hashval, hashval2, BlueMidnightWish256_DIGEST_SIZE));
    }
    printf("\n");
    for (int i = 1; i <= 17; i++) {
        BitSequence *hashval = Hash(bitlen, Msg, 24, MD, 0, i);

        // std::random_device rd;
        // std::mt19937 gen(rd());
        // std::uniform_int_distribution<> distrib(1, sz * 8 - 1);
        // int randomIndex = distrib(gen);
        int randomIndex = 10 % sz;

        invertBit(input, randomIndex);
        memcpy(Msg, input, sz);
        
        BitSequence *hashval2 = Hash(bitlen, Msg, 24, MD1, 0, i);

        printf("%d\n", 
            countDifferentBits(hashval, hashval2, BlueMidnightWish256_DIGEST_SIZE));
    }

    delete[] input;
    return 0;
}
