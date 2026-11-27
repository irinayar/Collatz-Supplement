// Independent regeneration of the predecessor labels (budgets 0..9) for sources r = 103 + 8192*i, i < 2^28.
// Written from the definition, not from the producer's search order: eligibility is tested on the actual source at all
// 41 depths; the inverse search is breadth-first in the number e of doublings. Single thread, about 400 MB.
using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;

class P
{
    const int D = 41;
    static readonly UInt128[] p3 = new UInt128[80];
    static readonly bool[,,] slope = new bool[42, 100, 10];   // 2^(b+e) 3^(a-b) < 2^41
    static byte[] mine;
    static long coefLeaves, eligible, bigPath, improvedNoCap, newHitNoCap;
    static long[] count = new long[11];

    static void Main(string[] args)
    {
        var sw = Stopwatch.StartNew();
        p3[0] = 1; for (int i = 1; i < 80; i++) p3[i] = p3[i - 1] * 3;
        for (int a = 0; a <= 41; a++)
            for (int b = 0; b < 100; b++)
                for (int e = 0; e <= 9; e++)
                {
                    BigInteger lhs = BigInteger.Pow(2, b + e), rhs = BigInteger.Pow(2, D);
                    if (a >= b) lhs *= BigInteger.Pow(3, a - b); else rhs *= BigInteger.Pow(3, b - a);
                    slope[a, b, e] = lhs < rhs;
                }
        mine = new byte[1 << 28]; Array.Fill(mine, (byte)15);

        // common 13 steps of residue 103
        UInt128 x = 103; int aa = 0;
        for (int j = 1; j <= 13; j++)
        {
            if (((ulong)x & 1) == 1) { aa++; x = (3 * x + 1) / 2; } else x /= 2;
            if (p3[aa] < ((UInt128)1 << j)) throw new Exception("common prefix fails coefficient test");
        }
        Gen(103, x, 13, aa);
        Console.WriteLine($"coefficient survivors={coefLeaves} eligible={eligible} bigPath={bigPath} t={sw.Elapsed.TotalSeconds:F1}s");
        for (int e = 0; e <= 10; e++) Console.WriteLine($"label {e}: {count[e]}");

        if (!File.Exists(args[0]))
        {
            var packed = new byte[1 << 27];
            for (int i = 0; i < (1 << 28); i++) packed[i >> 1] |= (byte)(mine[i] << ((i & 1) * 4));
            File.WriteAllBytes(args[0], packed);
            Console.WriteLine($"label file written: {args[0]}");
        }
        var stored = File.ReadAllBytes(args[0]);
        if (stored.Length != 1 << 27) throw new Exception("unexpected label file length");
        long mism = 0, first = -1;
        for (int i = 0; i < (1 << 28); i++)
        {
            int s = (stored[i >> 1] >> ((i & 1) * 4)) & 15;
            if (s != mine[i]) { mism++; if (first < 0) first = i; }
        }
        Console.WriteLine($"entries compared={1 << 28} mismatches={mism} first={first}");
        Console.WriteLine($"without the cap b<=a: label lowered for {improvedNoCap} eligible sources, of which {newHitNoCap} had label 10");
        Console.WriteLine($"t={sw.Elapsed.TotalSeconds:F1}s peakMB={Process.GetCurrentProcess().PeakWorkingSet64 >> 20}");
    }

    static void Gen(ulong r, UInt128 x, int j, int a)
    {
        if (j == D) { Leaf(r); return; }
        for (int bit = 0; bit < 2; bit++)
        {
            UInt128 y = bit == 1 ? x + p3[a] : x;
            bool odd = ((ulong)y & 1) == 1;
            int na = odd ? a + 1 : a;
            if (p3[na] < ((UInt128)1 << (j + 1))) continue;
            Gen(r | ((ulong)bit << j), odd ? (3 * y + 1) >> 1 : y >> 1, j + 1, na);
        }
    }

    static void Leaf(ulong r)
    {
        coefLeaves++;
        UInt128 y = r; int a = 0; ulong small = r; bool big = false;
        for (int i = 1; i <= D; i++)
        {
            bool rev;
            if (!big)
            {
                if ((small & 1) == 1) { a++; small = (3 * small + 1) >> 1; } else small >>= 1;
                rev = small % 3 == 2 && 2 * small - 1 < 3 * r;
                if (small > (1UL << 61)) { big = true; y = small; }
            }
            else
            {
                if (((ulong)y & 1) == 1) { a++; y = (3 * y + 1) >> 1; } else y >>= 1;
                rev = y % 3 == 2 && 2 * y - 1 < (UInt128)3 * r;
            }
            if (p3[a] < ((UInt128)1 << i)) throw new Exception("coefficient test disagrees with tree");
            if (rev && 2 * p3[a] < 3 * ((UInt128)1 << i)) return;
        }
        UInt128 end = big ? y : small;
        eligible++;
        int lab, free;
        if (end < ((UInt128)1 << 52)) { lab = Label<ulong>((ulong)end, r, a, a, 10); free = Label<ulong>((ulong)end, r, a, 99, lab); }
        else { bigPath++; lab = Label<UInt128>(end, r, a, a, 10); free = Label<UInt128>(end, r, a, 99, lab); }
        count[lab]++;
        if (free < lab) { improvedNoCap++; if (lab == 10) newHitNoCap++; }
        mine[(r - 103) >> 13] = (byte)lab;
    }

    static class Buf<T> { public static T[] x0 = new T[1 << 16], x1 = new T[1 << 16]; public static int[] b0 = new int[1 << 16], b1 = new int[1 << 16]; }

    // least e < limit having an inverse word with e doublings and b <= cap odd-inverse steps, endpoint < r, slope < 1
    static int Label<T>(T end, ulong r, int a, int cap, int limit) where T : struct, IBinaryInteger<T>
    {
        T three = T.CreateChecked(3), two = T.CreateChecked(2), target = T.CreateChecked(r);
        var cur = Buf<T>.x0; var curB = Buf<T>.b0; var nxt = Buf<T>.x1; var nxtB = Buf<T>.b1;
        int n = 1; cur[0] = end; curB[0] = 0;       // seeds of level 0
        for (int e = 0; e < limit && e <= 9; e++)
        {
            int m = 0;
            for (int k = 0; k < n; k++)
            {
                T v = cur[k]; int b = curB[k];
                while (true)
                {
                    if (v < target && b < 100 && slope[a, b, e]) return e;
                    nxt[m] = v << 1; nxtB[m] = b; m++;      // this element, doubled, seeds level e+1
                    if (b >= cap || v % three != two) break;
                    v = (v / three) * two + T.One; b++;
                    if (b >= 99) throw new Exception("odd run too long");
                }
            }
            (cur, nxt) = (nxt, cur); (curB, nxtB) = (nxtB, curB); n = m;
        }
        return limit;
    }
}
