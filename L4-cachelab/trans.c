/*
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 */
#include <stdio.h>
#include "cachelab.h"
#include "contracts.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/*
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. The REQUIRES and ENSURES from 15-122 are included
 *     for your convenience. They can be removed if you like.
 */

#define BLOCKSIZE 32
char transpose_submit_desc[] = "Transpose submission";


void transpose_square(int N, int A[N][N], int B[N][N], int step)
{
    for (int x = 0; x < N; x += step) {
        int j_end = x + step;
        for (int y = 0; y < N; y += step) {
            int i_end = y + step;
            for (int i = y; i < i_end; ++i) {
                if( y == x ) {
                    int diag, tmp;
                    for (int j = x; j < j_end; ++j) {
                        if (i == j) {
                            diag = i;
                            tmp = A[diag][diag];
                        } else
                            B[j][i] = A[i][j];
                    }
                    B[diag][diag] = tmp;
                } else {
                    for (int j = x; j < j_end; ++j) {
                        if (i != j) 
                            B[j][i] = A[i][j];
                    }
                }
            }	
        }
    }
}

void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{
    REQUIRES(M > 0);
    REQUIRES(N > 0);

    if( N == M ) {
        transpose_square(N, A, B, ( N==32 ? 8: 4) );
    } else {
        const int step = 16;
		for (int x = 0; x < M; x += step) {
            int j_end = x + step;
			for (int y = 0; y < N; y += step) {		
                int i_end = y + step;
				for (int i = y; i < i_end && i < N; ++i) {
                    if( y == x ) {
                        int tmp, diag;
                        for (int j = x; j < j_end && j < M; ++j) {
                            if (i == j) {
                                diag = i;
                                tmp = A[diag][diag];
                            } else 
                                B[j][i] = A[i][j];
                        }
						B[diag][diag] = tmp;
                    } else {
                        for (int j = x; j < j_end && j < M; ++j) {
                            if (i != j)
                                B[j][i] = A[i][j];
                        }
                    }
				}
			
	 		}
		}
	}

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started.
 */

/*
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    REQUIRES(M > 0);
    REQUIRES(N > 0);

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }

    ENSURES(is_transpose(M, N, A, B));
}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the registered functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc);

    /* Register any additional transpose functions */
    registerTransFunction(trans, trans_desc);

}

/*
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}
