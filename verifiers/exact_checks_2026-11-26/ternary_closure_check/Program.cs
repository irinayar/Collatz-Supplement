// Independent check of the depth-41 ternary closure (e <= 9, arbitrary number of odd inverses).
// Part 1: the 120-row slope table. Part 2: direct search of smaller origins on full periods of lifts. Single thread.
using System;
using System.IO;
using System.Numerics;

class P
{
    static readonly UInt128[] p3 = new UInt128[60];
    static UInt128[] cur = new UInt128[1 << 14], nxt = new UInt128[1 << 14];
    static int[] curB = new int[1 << 14], nxtB = new int[1 << 14];

    // least number of doublings e <= 9 giving an origin < n; odd inverses capped at 'cap'; slopeA >= 0 also demands 2^(b+e)3^(a-b) < 2^41
    static int MinE(UInt128 end, UInt128 n, int cap, int slopeA)
    {
        int count = 1; cur[0] = end; curB[0] = 0;
        for (int e = 0; e <= 9; e++)
        {
            int m = 0;
            for (int k = 0; k < count; k++)
            {
                UInt128 v = cur[k]; int b = curB[k];
                while (true)
                {
                    if (v < n && (slopeA < 0 || ((BigInteger.One << (b + e)) * BigInteger.Pow(3, slopeA - b) < (BigInteger.One << 41)))) return e;
                    nxt[m] = v + v; nxtB[m] = b; m++;
                    if (b >= cap || v % 3 != 2) break;
                    v = (v / 3) * 2 + 1; b++;
                }
            }
            (cur, nxt) = (nxt, cur); (curB, nxtB) = (nxtB, curB); count = m;
        }
        return 10;
    }

    static void Table()
    {
        int maxB = 0, maxExcess = 0, bad = 0; BigInteger lnum = 0, lden = 1, hnum = 0, hden = 1;
        for (int a = 26; a <= 37; a++)
        {
            string line = "";
            for (int e = 0; e <= 9; e++)
            {
                int b = 0;
                while ((BigInteger.One << (b + e)) * BigInteger.Pow(3, a) >= (BigInteger.One << 41) * BigInteger.Pow(3, b)) b++;
                maxB = Math.Max(maxB, b); maxExcess = Math.Max(maxExcess, b - a);
                if (a <= 31 && b > a) bad++;
                // largest slope below 1 is at b: bound (a/2) rho/(1-rho)
                BigInteger N = (BigInteger.One << (b + e)) * BigInteger.Pow(3, a), D = (BigInteger.One << 41) * BigInteger.Pow(3, b);
                BigInteger num = a * N, den = 2 * (D - N);
                if (num * lden > lnum * den) { lnum = num; lden = den; }
                // smallest slope above 1: b-1 (or b-2 if b-1 gives exactly 1)
                for (int c = b - 1; c >= 0; c--)
                {
                    BigInteger N2 = (BigInteger.One << (c + e)) * BigInteger.Pow(3, Math.Max(a - c, 0)), D2 = (BigInteger.One << 41) * BigInteger.Pow(3, Math.Max(c - a, 0));
                    if (N2 == D2) continue;
                    BigInteger hn = (BigInteger.One << e) * D2, hd = N2 - D2;
                    if (hn * hden > hnum * hd) { hnum = hn; hden = hd; }
                    break;
                }
                if (e == 9) line = $"a={a} B(a,9)={b}";
            }
            Console.Write(line + "; ");
        }
        var g1 = BigInteger.GreatestCommonDivisor(lnum, lden); var g2 = BigInteger.GreatestCommonDivisor(hnum, hden);
        Console.WriteLine($"\nmaxB={maxB} max(B-a)={maxExcess} rows with a<=31 and B>a: {bad}");
        Console.WriteLine($"low bound {lnum / g1}/{lden / g1}   high bound {hnum / g2}/{hden / g2}");
    }

    static void Main(string[] args)
    {
        p3[0] = 1; for (int i = 1; i < 60; i++) p3[i] = p3[i - 1] * 3;
        Table();
        UInt128 M0 = (UInt128)2075 << 60; const int PER = 19683;
        long total = 0, periodFail = 0, mism = 0; bool rows = false;
        foreach (var line in File.ReadLines(args[0]))
        {
            if (line.StartsWith("base_r,")) { rows = true; continue; }
            if (!rows) continue;
            var f = line.Split(',');
            if (f.Length != 5 || !ulong.TryParse(f[0], out ulong r)) break;
            // forward 41 steps, eligibility as in the census
            UInt128 x = r; int a = 0; bool elig = true;
            for (int j = 1; j <= 41; j++)
            {
                if (((ulong)x & 1) == 1) { a++; x = (3 * x + 1) >> 1; } else x >>= 1;
                if (p3[a] < ((UInt128)1 << j)) elig = false;
                if (x % 3 == 2 && 2 * x - 1 < (UInt128)3 * r && 2 * p3[a] < 3 * ((UInt128)1 << j)) elig = false;
            }
            int capped = MinE(x, r, a, a), free = MinE(x, r, 1000, -1);
            var low = new int[PER]; int hits = 0; long t0 = (long)((M0 - r) >> 41) + 1;
            for (int t = 0; t < PER; t++)
            {
                UInt128 n = (UInt128)r + ((UInt128)t << 41);
                low[t] = MinE(x + p3[a] * (UInt128)t, n, 1000, -1); total++;
            }
            for (int k = 0; k < PER; k++)
            {
                long t = t0 + k; UInt128 n = (UInt128)r + ((UInt128)t << 41);
                int e = MinE(x + p3[a] * (UInt128)t, n, 1000, -1); total++;
                if (e <= 9) hits++;
                if (n >= 18764 && e != low[t % PER] && r + ((UInt128)(t % PER) << 41) >= 18764) periodFail++;
            }
            if (a != int.Parse(f[1]) || free != int.Parse(f[2]) || hits != int.Parse(f[3])) mism++;
            if (a >= 32)
            {
                // describe the hit set by residues mod 3 and mod 9
                string d = "";
                for (int q = 0; q < 9; q++)
                {
                    int min = 10, max = 0;
                    for (int t = q; t < PER; t += 9) { min = Math.Min(min, low[t]); max = Math.Max(max, low[t]); }
                    d += $" {q}:{(min == max ? min.ToString() : min + "-" + max)}";
                }
                Console.WriteLine($"r={r} a={a} eligible={elig} capped={capped} baseUncapped={free} hits={hits} e by t mod 9:{d}");
            }
            else if (!(elig && capped == 10 && hits == 0)) Console.WriteLine($"UNEXPECTED low-a row r={r} a={a} elig={elig} capped={capped} hits={hits}");
        }
        Console.WriteLine($"direct searches={total} mismatches with source rows={mism} periodicity failures={periodFail}");
    }
}
