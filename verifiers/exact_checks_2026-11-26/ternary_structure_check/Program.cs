// For every eligible capped-label-10 source r (a >= 32): compare the witness set (e <= 9, any b) with the translate of
// S_k, k = a - 32 = numbers n having an expanding inverse word from n itself with at most k doublings; then count what
// remains after the finite mixed rules, and after them plus the expanding catalogue A14, split by n mod 3.
// args: direct9.bin finite_ledger_transcribed.csv
using System;
using System.IO;
using System.Collections.Generic;

class P
{
    const int D = 41, N9 = 19683, M14 = 4782969;
    static readonly UInt128[] p3 = new UInt128[64];
    static byte[] labels;
    static readonly byte[] mask = new byte[N9];
    static readonly bool[][] S = new bool[6][];
    static long sources, mismatch, notContain;
    static readonly long[] freeF = new long[N9], freeFA = new long[N9];
    static readonly long[,] remF = new long[6, 3], remFA = new long[6, 3];

    static void Main(string[] args)
    {
        p3[0] = 1; for (int i = 1; i < 64; i++) p3[i] = p3[i - 1] * 3;
        labels = File.ReadAllBytes(args[0]);
        // S_k by direct search from representatives
        for (int k = 0; k <= 5; k++)
        {
            S[k] = new bool[N9]; int size = 0;
            for (int v = 0; v < N9; v++) { S[k][v] = Has((UInt128)v + (UInt128)N9 * 1000003, 0, 0, k); if (S[k][v]) size++; }
            Console.WriteLine($"S_{k}: {size} residues of n mod 3^9, i.e. {size}/19683");
        }
        // finite mixed rules and A14 as bitmaps over n mod 3^14
        var ruled = new bool[M14];
        var lines = File.ReadAllLines(args[1]);
        for (int i = 1; i < lines.Length; i++)
        {
            var f = lines[i].Split(','); long res = long.Parse(f[1]), m = long.Parse(f[2]); int d = 0, e = 0;
            while (m % 2 == 0) { m /= 2; d++; }
            while (m % 3 == 0) { m /= 3; e++; }
            if (e == 0 || 103 % (1L << d) != res % (1L << d)) continue;
            for (long v = res % (long)p3[e]; v < M14; v += (long)p3[e]) ruled[v] = true;
        }
        var a14 = new bool[M14]; long words = 0;
        for (int a = 1; a <= 14; a++)
        {
            long mod = (long)p3[a]; int L = 0; while ((1L << (L + 1)) <= mod) L++;
            long inv2 = (mod + 1) / 2, invL = 1; for (int i = 0; i < L; i++) invL = invL * inv2 % mod;
            Words(0, 0, 0, a, L, mod, invL, a14, ref words);
        }
        long cr = 0, ca = 0; for (int v = 0; v < M14; v++) { if (ruled[v]) cr++; if (a14[v]) ca++; }
        for (int v = 0; v < M14; v++) { if (!ruled[v]) freeF[v % N9]++; if (!ruled[v] && !a14[v]) freeFA[v % N9]++; }
        Console.WriteLine($"finite rules uncovered {M14 - cr}/3^14; A14 words={words}, measure {ca}/3^14");

        UInt128 x = 103; int aa = 0;
        for (int j = 1; j <= 13; j++) { if (((ulong)x & 1) == 1) { aa++; x = (3 * x + 1) / 2; } else x /= 2; }
        Gen(103, x, 13, aa);

        Console.WriteLine($"sources={sources}; witness set differs from translate of S_(a-32): {mismatch}; S translate not contained: {notContain}");
        string[] name = { "after finite rules", "after finite rules + A14" };
        for (int w = 0; w < 2; w++)
        {
            var rem = w == 0 ? remF : remFA; long total = 0, by0 = 0, by1 = 0, by2 = 0;
            string d = "";
            for (int k = 0; k < 6; k++) { long s = rem[k, 0] + rem[k, 1] + rem[k, 2]; total += s; by0 += rem[k, 0]; by1 += rem[k, 1]; by2 += rem[k, 2]; d += $" a{32 + k}={s}"; }
            Console.WriteLine($"{name[w]}: total {total}/3^14; by n mod 3: {by0}, {by1}, {by2};{d}");
        }
    }

    // expanding inverse word from n with at most k doublings (stop at the first prefix with 2^(b+d) < 3^b)
    static bool Has(UInt128 y, int b, int d, int k)
    {
        if (b + d > 0 && Math.Pow(2, b + d) < Math.Pow(3, b)) return true;
        if (b > 30) return false;
        if (y % 3 == 2 && Has((2 * y - 1) / 3, b + 1, d, k)) return true;
        return d < k && Has(2 * y, b, d + 1, k);
    }

    static void Words(int j, int odd, long C, int a, int L, long mod, long invL, bool[] set, ref long words)
    {
        if (j == L) { if (odd != a) return; words++; long y = (long)((UInt128)C * (UInt128)invL % (UInt128)mod); for (long v = y; v < M14; v += mod) set[v] = true; return; }
        if (a - odd > L - j) return;
        Words(j + 1, odd, C, a, L, mod, invL, set, ref words);
        if (odd < a) Words(j + 1, odd + 1, 3 * C + (1L << j), a, L, mod, invL, set, ref words);
    }

    static void Gen(ulong r, UInt128 x, int j, int a)
    {
        if (a + (D - j) < 32) return;
        if (j == D) { Leaf(r, x, a); return; }
        for (int bit = 0; bit < 2; bit++)
        {
            UInt128 y = bit == 1 ? x + p3[a] : x;
            bool odd = ((ulong)y & 1) == 1;
            int na = odd ? a + 1 : a;
            if (p3[na] < ((UInt128)1 << (j + 1))) continue;
            Gen(r | ((ulong)bit << j), odd ? (3 * y + 1) >> 1 : y >> 1, j + 1, na);
        }
    }

    static void Leaf(ulong r, UInt128 x, int a)
    {
        long idx = (long)((r - 103) >> 13);
        if (((labels[idx >> 1] >> (int)((idx & 1) * 4)) & 15) != 10) return;
        sources++;
        Array.Clear(mask);
        Walk(x, p3[a], a, 0, 0, 0, 0, r);
        int k = a - 32; long step = (long)((1UL << 41) % N9), nm = (long)(r % N9);
        bool diff = false, miss = false;
        for (int t = 0; t < N9; t++)
        {
            bool inS = S[k][nm];
            if ((mask[t] == 1) != inS) diff = true;
            if (inS && mask[t] != 1) miss = true;
            if (mask[t] == 1) { remF[k, nm % 3] += freeF[nm]; remFA[k, nm % 3] += freeFA[nm]; }
            nm += step; if (nm >= N9) nm -= N9;
        }
        if (diff) mismatch++;
        if (miss) notContain++;
    }

    static void Walk(UInt128 v, UInt128 s, int a, int b, int e, long R, int k, ulong r)
    {
        UInt128 bound = ((UInt128)1 << 41) * p3[k];
        if (s < bound) { Record(R, k); return; }
        if (s == bound && v < (UInt128)r + ((UInt128)R << 41)) Record(R, k);
        if (e < 9) Walk(v + v, s + s, a, b, e + 1, R, k, r);
        if (s % 3 == 0) { if (v % 3 == 2) Walk((2 * v - 1) / 3, 2 * s / 3, a, b + 1, e, R, k, r); }
        else
        {
            int sm = (int)(s % 3), vm = (int)(v % 3), h0 = ((2 - vm + 3) * sm) % 3;
            Walk((2 * (v + s * (UInt128)h0) - 1) / 3, 2 * s, a, b + 1, e, R + (long)p3[k] * h0, k + 1, r);
        }
    }

    static void Record(long R, int k) { long m = (long)p3[k]; for (long t = R; t < N9; t += m) mask[t] = 1; }
}
