/**
******************************************************************************
* @file         main.c
* @author       Diego Martínez García (dmartinezgarcia@outlook.com)
*
* @verbatim
*   LTP = left-truncatable prime, LookUp tables not allowed
*
*   The first thing to do was to find a suitable primality test, at first I thought of AKS which is deterministic, but it was very slow.
*   I decided to look for probabilistic primality tests, and I finally decided to implement the Miller-Rabin algorithm, which under certain circumstances, has proven to be deterministic.
*
*   While implementing the algorithm, I had to optimize all the operations so it would execute as fast as possible, and specially to prevent overflows, in this regard I used modular arithmetic.
*
*   The next step was to implement the program logical behaviour, I decided to implement a circular buffer which stores LTPs that can generate other LTPs, brute force in this algorithm is minimum.
*   This algorithm needs some initial values, which are {2, 3, 5, 7}, which are the first LTPs, from there, it generates LTPs till the one specified by the user is calculated.
*   It can be modified so it calculates these initial values by itself, but the circular buffer logic should be slightly modified aswell, I thought it would be more readable leaving it this way.
*
*   The function FindLTP is where I implemented this and it should be easier to understand by checking the code there.
*   It can also be modified to print out all the LTPs found.
*
*   I think the memory consumption could be improved, but the program executes quite fast, I can get the 2166th LTP on my machine under 50ms (per Codeblocks).
*   Perhaps by restructuring the code more execution speed could be achieved at the expense of readability.
*
*   I must say that overall this was a very interesting exercise, I hope you like my implementation.
*
*   Tools used:
*       - CodeBlocks IDE
*       - GNU GCC Compiler (MinGw)
*
*   Portability:
*       - The program uses fixed size variables (stdint.h)
*       - All variables are unsigned, so there shouldn't be any problems with logical or arithmetic shifts, something which is machine dependent.
*
*   Useful documentation:
*       - Khan Academy webpage for a refresher on modular arithmetic
*       - List of 4260 LTP: http://www.worldofnumbers.com/truncat.htm
*       - Miller-Rabin primality test: http://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test
*       - AKS deterministic primality test and implementation: Salembier_Southerington_AKS.pdf
* @endverbatim
*
******************************************************************************
*/

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>

// Length of the buffer that will store the LTP tails.
// It is big enough so no LTP is overwritten.
#define BUF_LENGTH      (680)

/*
 * Modular exponentiation. (base ^ (exp)) % mod
 *
 * The logic behind this algorithm can be found on "Discrete Mathematics and its Applications" By Kenneth H Rosen.
 *
 * I slightly modified it and included modular multiplication and 64 bit variables to avoid overflows.
 */

uint64_t ModulusPow (uint64_t base, uint64_t exp, uint64_t mod)
{
    base = base % mod;
    uint64_t result = 1;

    while (exp > 0)
    {
        if (exp & 1)
            result = ((result % mod) * (base % mod)) % mod;
        base = ((base % mod) * (base % mod)) % mod;
        exp >>= 1;
    }
    return result;
}

/*
 *  Checks whether the given number is even or odd.
 *
 *  (val % 2) could be replaced by (val & 1) and the function will work the same way, but the former is more readable. In any case, that will be optimized during the build process.
 */

bool IsEven (uint32_t val)
{
    if (val % 2)
        return false;
    return true;
}

/*
 * Simple val^n algorithm.
 */

uint32_t Power (uint32_t val, uint8_t n)
{
    uint8_t i;
    uint32_t OldVal = val;

    if (n)
    {
        for (i = 1; i < n; i++)
            val = val * OldVal;
        return val;
    }
    return 1;
}

/*
 *  Miller-Rabin primality test. Slightly modified, takes a number (k) of guesses (g) that turns the algoritm deterministic.
 *
 *  It also implements modular multiplication.
 *
 *  It was implemented following the steps at http://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test
 */

bool MillerRabin (uint64_t n, uint32_t* g, uint8_t k)
{
    uint64_t x = 0;
    uint32_t d = n - 1;
    uint16_t s = 0, i;

    while (IsEven(d))
    {
        s++;
        d >>= 1;
    }

    while (k)
    {
        x = ModulusPow(g[--k], d, n);
        if ((x == 1) || (x == n - 1)) continue;
        for (i = 1; i < s; i++)
        {
            x = ((x % n) * (x % n)) % n;
            if (x == 1) return false;
            if (x == n - 1) break;
        }
        if (i == s) return false;
    }
    return true;
}

/*
 *  Mostly a wrapper function for the MillerRabin function.
 *
 *  The guesses hardcoded in this function make the algorithm deterministic for the specified ranges.
 *
 *  The value of the guesses was found at: http://en.wikipedia.org/wiki/Miller%E2%80%93Rabin_primality_test
 */

bool IsPrime (uint32_t n)
{
    if ((!(n % 2)) || (n <= 1))
        return false;

    if (n < 2047)
    {
        uint32_t g[1] = {2};
        return MillerRabin(n, g, 1);
    }
    if (n < 1373653)
    {
        uint32_t g[2] = {2, 3};
        return MillerRabin(n, g, 2);
    }
    if (n < 9080191)
    {
        uint32_t g[2] = {31, 73};
        return MillerRabin(n, g, 2);
    }
    if (n < 25326001)
    {
        uint32_t g[3] = {2, 3, 5};
        return MillerRabin(n, g, 3);
    }
    if (n < 4759123141)
    {
        uint32_t g[3] = {2, 7, 61};
        return MillerRabin(n, g, 3);
    }
}

/*
 *  Function that returns the specified LTP.
 */

uint32_t FindLTP (uint16_t LTP_n)
{
    uint32_t LTP_Buf[BUF_LENGTH] = {2, 3, 5, 7};
    uint32_t num, PwVal, PwValN;
    uint16_t LTP_IndexProc = 0, LTP_IndexFree = 4, LTP_IndexOldFree = 0, u, i, v;
    uint16_t order = 0, PrimesCount = 4;

    // Single cases
    if (LTP_n <= 4)
        return LTP_Buf[LTP_n - 1];

    // It will return before satisfying this condition, the condition is put here so it isn't an infinite loop.
    while (order < 9)
    {
        // Sets the initial variables.
        PwVal = Power(10, ++order);
        LTP_IndexOldFree = LTP_IndexFree;

        for (i = 1; i < 10; i++)
        {
            for (u = LTP_IndexProc; u != LTP_IndexOldFree; )
            {
                num = LTP_Buf[u++] + i * PwVal;

                if (u >= BUF_LENGTH)
                    u = 0;

                if (IsPrime(num))
                {
                    if (++PrimesCount == LTP_n)
                        return num;

                    // Check if this prime is tail to another LTP before storing it into memory.
                    // This part could be removed at the expense of increasing the size of LTP_Buf, but since the algorithm overall is quite fast I decided to put this here.
                    PwValN = Power(10, order + 1);
                    for (v = 1; v < 10; v++)
                    {
                        if (IsPrime(num + PwValN * v))
                            break;
                    }

                    if (v < 10)
                    {
                        // The last LTP calculated is tail to at least another LTP, so store it into memory.
                        LTP_Buf[LTP_IndexFree++] = num;

                        if (LTP_IndexFree >= BUF_LENGTH)
                            LTP_IndexFree = 0;
                    }
                }
            }
        }
        LTP_IndexProc = LTP_IndexOldFree;
    }

    // This will never be executed, but compiler will complain if removed.
    return 0;
}

/*
 *  Main function.
 *
 */

int main()
{
    uint32_t num;
    clock_t start, end;
    double ms;

    do
    {
        printf("Please input a number between 1 and 2166: ");
        scanf("%i", &num);
    } while ((num > 2166) || (num < 1));

    start = clock();
    num = FindLTP(num);
	end = clock();

	ms = (end - start) * 1000 / CLOCKS_PER_SEC;
	printf("Time spent %04.2lf ms\n", ms);
    printf("Left-truncatable prime at the specified position is: %i\r\n", num);

    return 0;
}
