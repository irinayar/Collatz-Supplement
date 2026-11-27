// Exact ternary witness masks (e <= 9, any number of odd inverses) for all eligible sources r = 103 + 8192 i,
// i < 2^28, with capped label 10 and a >= 32. Labels are read from the (independently regenerated) classification.
// Mask = set of t mod 3^9 such that n = r + 2^41 t has a smaller origin from T^41(n). Single thread.
// args: direct9.bin finite_ledger_transcribed.csv previous_cylinders.csv projected181.csv
using System;
using System.Collections.Generic;
using System.IO;
using System.Numerics;
using System.Diagnostics;

class P
{
    const int D = 41, N9 = 19683;
    static readonly UInt128[] p3 = new UInt128[64];
    static byte[] labels;
    static readonly long[] cand = new long[6], src = new long[6], nonempty = new long[6];
    static readonly long[] raw = new long[6];                 // sum of mask sizes (out of 3^9)
    static long equalSlope, states, minR = long.MaxValue, verified, verifyFail, in149, in181, newAfterRules, rawE;
    static BigInteger newNum = 0;                             // sum over sources of |mask \ rules|, modulus 3^M
    static int M = 9;
    static bool[] ruled;                                      // residues of n mod 3^M removed by the finite mixed rules
    static int[] freeAbove;
    static readonly bool[] mask = new bool[N9];
    static readonly List<(ulong r, int d)> proj = new(), prev = new();
    static long sampleCounter;
    static readonly Stopwatch clock = Stopwatch.StartNew();
    static readonly long[] byMinE = new long[11];

    static void Main(string[] args)
    {
        var sw = Stopwatch.StartNew();
        p3[0] = 1; for (int i = 1; i < 64; i++) p3[i] = p3[i - 1] * 3;
        labels = File.ReadAllBytes(args[0]);

        var mixed = new List<(long res, int e)>(); int maxE = 0, nMixed = 0, nPure = 0;
        var lines = File.ReadAllLines(args[1]);
        for (int i = 1; i < lines.Length; i++)
        {
            var f = lines[i].Split(','); long res = long.Parse(f[1]), m = long.Parse(f[2]); int d = 0, e = 0;
            while (m % 2 == 0) { m /= 2; d++; }
            while (m % 3 == 0) { m /= 3; e++; }
            if (m != 1) throw new Exception("modulus");
            if (e == 0) { nPure++; continue; }
            nMixed++;
            if (103 % (1L << d) == res % (1L << d)) { if (d > 13) throw new Exception("binary part deeper than parent"); mixed.Add((res % (long)p3[e], e)); maxE = Math.Max(maxE, e); }
        }
        // C121: 303 mod 5184 = 2^6 * 3^4
        bool c121 = 103 % 64 == 303 % 64; if (c121) mixed.Add((303 % 81, 4));
        M = Math.Max(9, maxE);
        ruled = new bool[(int)p3[M]];
        foreach (var (res, e) in mixed) for (long v = res; v < ruled.Length; v += (long)p3[e]) ruled[v] = true;
        long free = 0; foreach (var b in ruled) if (!b) free++;
        Console.WriteLine($"pure={nPure} mixed={nMixed} active on parent={mixed.Count} C121 active={c121} maxE={maxE} Q={free}/{ruled.Length}");

        var pc = File.ReadAllLines(args[2]); var head = pc[0].Split(',');
        int iL = Array.IndexOf(head, "L"), ir = Array.IndexOf(head, "r");
        for (int i = 1; i < pc.Length; i++) { var f = pc[i].Split(','); prev.Add((ulong.Parse(f[ir]), int.Parse(f[iL]))); }
        var pj = File.ReadAllLines(args[3]);
        for (int i = 1; i < pj.Length; i++) { var f = pj[i].Split(','); proj.Add((ulong.Parse(f[0]), int.Parse(f[1]))); }

        UInt128 x = 103; int a = 0;
        for (int j = 1; j <= 13; j++) { if (((ulong)x & 1) == 1) { a++; x = (3 * x + 1) / 2; } else x /= 2; }
        Gen(103, x, 13, a);

        long tc = 0, ts = 0, tn = 0, tr = 0;
        for (int k = 0; k < 6; k++) { tc += cand[k]; ts += src[k]; tn += nonempty[k]; tr += raw[k]; Console.WriteLine($"a={32 + k}: coefficient survivors={cand[k]} label10 sources={src[k]} with nonempty mask={nonempty[k]} mask sum={raw[k]}/19683"); }
        Console.WriteLine($"total candidates={tc} sources={ts} nonempty={tn} equal-slope witnesses present in {equalSlope} sources; smallest source r={minR}");
        Console.WriteLine($"raw sum of lift fractions={tr}/19683 = {(double)tr / N9:F6}");
        Console.WriteLine($"after finite mixed rules: {newNum}/3^{M} = {(double)newNum / (double)ruled.Length:F6}; sources with new part={newAfterRules}");
        Console.WriteLine($"residual factor of these sources before: Q*sources = {free}*{ts}/3^{M}");
        Console.WriteLine($"sources inside the 149 earlier cylinders={in149}, inside the 181 projected={in181}");
        Console.Write("t-residues by least e:"); for (int e = 0; e < 10; e++) Console.Write($" e{e}={byMinE[e]}"); Console.WriteLine();
        Console.WriteLine($"states={states} direct-verified sources={verified} failures={verifyFail} t={sw.Elapsed.TotalSeconds:F0}s peakMB={Process.GetCurrentProcess().PeakWorkingSet64 >> 20}");
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

    static readonly byte[] minE = new byte[N9];

    static void Leaf(ulong r, UInt128 x, int a)
    {
        int k = a - 32; cand[k]++;
        long idx = (long)((r - 103) >> 13);
        int lab = (labels[idx >> 1] >> (int)((idx & 1) * 4)) & 15;
        if (lab != 10) return;
        src[k]++; minR = Math.Min(minR, (long)r);
        foreach (var (pr, d) in prev) if ((r & ((1UL << d) - 1)) == pr) { in149++; break; }
        foreach (var (pr, d) in proj) if ((r & ((1UL << d) - 1)) == pr) { in181++; break; }
        Array.Fill(minE, (byte)10);
        bool eq = false;
        Walk(x, p3[a], a, 0, 0, 0, 0, r, ref eq);
        if (eq) equalSlope++;
        int size = 0; for (int t = 0; t < N9; t++) if (minE[t] <= 9) { size++; byMinE[minE[t]]++; }
        if (size > 0) nonempty[k]++;
        raw[k] += size;
        // subtract finite mixed rules: n = r + 2^41 t; freeAbove[q] counts the unruled n mod 3^M with n = q mod 3^9
        if (freeAbove == null)
        {
            freeAbove = new int[N9];
            for (int v = 0; v < ruled.Length; v++) if (!ruled[v]) freeAbove[v % N9]++;
        }
        long nw = 0, nm = (long)(r % N9), step = (long)((1UL << 41) % N9);
        for (int t = 0; t < N9; t++)
        {
            if (minE[t] <= 9) nw += freeAbove[(int)nm];
            nm += step; if (nm >= N9) nm -= N9;
        }
        newNum += nw; if (nw > 0) newAfterRules++;
        if (sampleCounter++ % 2111 == 0) Verify(r, x, a);
        long done = src[0] + src[1] + src[2] + src[3] + src[4] + src[5];
        if (done % 2000 == 0 || done == 10) Console.WriteLine($"progress sources={done} states={states} verified={verified} t={clock.Elapsed.TotalSeconds:F1}s");
    }

    // state: y = v + s h, t = R + 3^k h; b odd inverses and e doublings used
    static void Walk(UInt128 v, UInt128 s, int a, int b, int e, long R, int k, ulong r, ref bool eq)
    {
        states++;
        UInt128 bound = ((UInt128)1 << 41) * p3[k];
        if (s < bound) { Record(R, k, e); return; }
        if (s == bound && v < (UInt128)r + ((UInt128)R << 41)) { eq = true; Record(R, k, e); }
        if (e < 9) Walk(v + v, s + s, a, b, e + 1, R, k, r, ref eq);
        if (s % 3 == 0)
        {
            if (v % 3 == 2) Walk((2 * v - 1) / 3, 2 * s / 3, a, b + 1, e, R, k, r, ref eq);
        }
        else
        {
            if (k >= 9) throw new Exception("ternary precision exceeded");
            int sm = (int)(s % 3), vm = (int)(v % 3);
            int h0 = ((2 - vm + 3) * sm) % 3;
            Walk((2 * (v + s * (UInt128)h0) - 1) / 3, 2 * s, a, b + 1, e, R + (long)p3[k] * h0, k + 1, r, ref eq);
        }
    }

    static void Record(long R, int k, int e)
    {
        long m = (long)p3[k];
        for (long t = R; t < N9; t += m) if (e < minE[t]) minE[t] = (byte)e;
    }

    static UInt128[] cur = new UInt128[1 << 14], nxt = new UInt128[1 << 14];

    static int Direct(UInt128 end, UInt128 n)
    {
        int count = 1; cur[0] = end;
        for (int e = 0; e <= 9; e++)
        {
            int m = 0;
            for (int i = 0; i < count; i++)
            {
                UInt128 v = cur[i];
                while (true)
                {
                    if (v < n) return e;
                    nxt[m++] = v + v;
                    if (v % 3 != 2) break;
                    v = (v / 3) * 2 + 1;
                }
            }
            (cur, nxt) = (nxt, cur); count = m;
        }
        return 10;
    }

    static void Verify(ulong r, UInt128 x, int a)
    {
        verified++;
        for (int t = 0; t < N9; t++)
        {
            long lift = t + 19683L * 7;
            UInt128 n = (UInt128)r + ((UInt128)lift << 41);
            if (Direct(x + p3[a] * (UInt128)lift, n) != minE[t]) { verifyFail++; return; }
        }
    }
}
