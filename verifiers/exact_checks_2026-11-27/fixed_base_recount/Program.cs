// Exact recount of fixed-base affordable starts n = 159 + 384u in [M0, 2 M0), M0 = 2075 * 2^60, at endpoints from step seven,
// by recursion on arithmetic progressions of inverse words, with exact removal of overlaps.  No arguments.
using System;
using System.Collections.Generic;
using System.Linq;

class P
{
    static readonly Int128 M0 = (Int128)2075 << 60;
    // parameter v in [lo,hi]; the affordable ones are recorded as v = s + q*w, w in [a,b]
    static List<(long q, long s, long a, long b)> rec = new();
    static long nodes;

    static Int128 FloorDiv(Int128 x, Int128 y) { var q = x / y; if ((x % y != 0) && ((x < 0) != (y < 0))) q--; return q; }
    static Int128 CeilDiv(Int128 x, Int128 y) => -FloorDiv(-x, y);

    static Int128[] p2 = new Int128[100], p3 = new Int128[60];

    // x = a*w + c for v = s + q*w, w in [lo,hi]; e evens and j odd steps remain
    static void Walk(Int128 a, Int128 c, long q, long s, Int128 lo, Int128 hi, int e, int j)
    {
        if (lo > hi) return;
        nodes++;
        // record the part with x <= M0
        var cut = FloorDiv(M0 - c, a);
        if (cut >= lo) { var top = cut < hi ? cut : hi; rec.Add((q, s, (long)lo, (long)top)); lo = top + 1; if (lo > hi) return; }
        // height condition 2^j (x+1) <= 3^j (M0+1)
        var limit = FloorDiv(p3[j] * (M0 + 1), p2[j]) - 1;
        var hcut = FloorDiv(limit - c, a);
        if (hcut < hi) hi = hcut;
        if (lo > hi) return;
        if (e > 0) Walk(2 * a, 2 * c, q, s, lo, hi, e - 1, j);
        if (j > 0)
        {
            // odd inverse (2x-1)/3 requires 2(a w + c) - 1 = 0 mod 3
            if (a % 3 == 0) { if ((2 * c - 1) % 3 == 0) Walk(2 * a / 3, (2 * c - 1) / 3, q, s, lo, hi, e, j - 1); }
            else for (int w0 = 0; w0 < 3; w0++)
            {
                var v = 2 * (a * w0 + c) - 1;
                if (v % 3 != 0) continue;
                Walk(2 * a, v / 3, checked(q * 3), s + q * w0, CeilDiv(lo - w0, 3), FloorDiv(hi - w0, 3), e, j - 1);
                break;
            }
        }
    }

    // exact size of the union of the recorded sets
    static long Union(List<(long q, long s, long a, long b)> list)
    {
        var arr = list.ToArray();
        Array.Sort(arr, (x, y) => x.q != y.q ? x.q.CompareTo(y.q) : x.s != y.s ? x.s.CompareTo(y.s) : x.a.CompareTo(y.a));
        var groups = new Dictionary<(long, long), (int from, int count)>();
        var merged = new (long a, long b)[arr.Length]; int n = 0;
        var keys = new List<(long q, long s)>();
        int i = 0;
        while (i < arr.Length)
        {
            var (q, s) = (arr[i].q, arr[i].s); int start = n;
            while (i < arr.Length && arr[i].q == q && arr[i].s == s)
            {
                var (a, b) = (arr[i].a, arr[i].b);
                if (n > start && a <= merged[n - 1].b + 1) { if (b > merged[n - 1].b) merged[n - 1].b = b; }
                else merged[n++] = (a, b);
                i++;
            }
            groups[(q, s)] = (start, n - start); keys.Add((q, s));
        }
        long total = 0; var cover = new List<(long a, long b)>();
        foreach (var (q, s) in keys)
        {
            var g = groups[(q, s)]; cover.Clear();
            for (long p = q / 3; p >= 1; p /= 3)
            {
                long s1 = s % p;
                if (!groups.TryGetValue((p, s1), out var h)) continue;
                long d = (s - s1) / p, f = q / p;
                for (int k = h.from; k < h.from + h.count; k++)
                {
                    long a = (long)CeilDiv((Int128)merged[k].a - d, f), b = (long)FloorDiv((Int128)merged[k].b - d, f);
                    if (a <= b) cover.Add((a, b));
                }
            }
            cover.Sort();
            int c = 0; long curA = 0, curB = -1; bool have = false;
            var unionCover = new List<(long a, long b)>();
            foreach (var iv in cover)
            {
                if (!have) { curA = iv.a; curB = iv.b; have = true; }
                else if (iv.a <= curB + 1) { if (iv.b > curB) curB = iv.b; }
                else { unionCover.Add((curA, curB)); curA = iv.a; curB = iv.b; }
            }
            if (have) unionCover.Add((curA, curB));
            for (int k = g.from; k < g.from + g.count; k++)
            {
                long a = merged[k].a, b = merged[k].b; total += b - a + 1;
                while (c < unionCover.Count && unionCover[c].b < a) c++;
                for (int t = c; t < unionCover.Count && unionCover[t].a <= b; t++)
                    total -= Math.Min(b, unionCover[t].b) - Math.Max(a, unionCover[t].a) + 1;
            }
        }
        return total;
    }

    static int Cutoff(Int128 y, int E)
    {
        for (int B = 0; B < 45; B++)
        {
            var l = (System.Numerics.BigInteger)y << (B + E);
            if (l <= System.Numerics.BigInteger.Pow(3, B) * (System.Numerics.BigInteger)M0) return B;
        }
        throw new Exception("no cutoff");
    }

    static int bad = 0;
    static void Check(string name, long got, long want) { if (got != want) bad++; Console.WriteLine($"{(got == want ? "ok  " : "FAIL")} {name}: {got}{(got == want ? "" : " expected " + want)}"); }

    static void Main()
    {
        p2[0] = 1; for (int i = 1; i < 100; i++) p2[i] = p2[i - 1] * 2;
        p3[0] = 1; for (int i = 1; i < 60; i++) p3[i] = p3[i - 1] * 3;
        Int128 ulo = CeilDiv(M0 - 159, 384), uhi = FloorDiv(2 * M0 - 1 - 159, 384); long span = (long)(uhi - ulo); // parameter u - ulo
        Check("starts in the range", span + 1, 6229979484529186134);

        long[] w7 = { 235008307056740097, 270524926121638027, 295881190237829896, 312767911121204596 };
        int[] Bs = { 15, 17, 18, 20 };
        for (int E = 5; E <= 8; E++)
        {
            var Y = (Int128)911 + 2187 * uhi;
            int B = Cutoff(Y, E);
            if (B != Bs[E - 5]) { Console.WriteLine($"note: least cutoff for E={E} is {B}, listed cutoff is {Bs[E - 5]}"); if (B > Bs[E - 5]) bad++; B = Bs[E - 5]; }
            rec.Clear(); nodes = 0;
            Walk(2187, 911 + 2187 * ulo, 1, 0, 0, span, E, B);
            Check($"endpoint 7, E={E}, B={B} (records {rec.Count})", Union(rec), w7[E - 5]);
        }

        // cumulative unions through endpoint 13 for E = 5
        const int h = 6; long[] want = { 235008307056740097, 235008307056740097, 311930426130370828, 570599112058097741, 945284810650125626, 1487853318178329236, 1931220979488442717 };
        long[] wantDirect = { 0, 0, 0, 315130992444463290, 546939214005305778, 1147913601008857096, 1415196314233292415 };
        var sum = new long[h + 1]; var direct = new long[h + 1];
        for (long r = 0; r < (1L << h); r++)
        {
            long vlo = 0, vhi = (span - r) >> h;
            Int128 A = (Int128)2187 << h, C = 911 + 2187 * (ulo + r);
            var all = new List<(long q, long s, long a, long b)>();
            var dir = new List<(long q, long s, long a, long b)>();
            for (int j = 0; j <= h; j++)
            {
                var top = A * vhi + C;
                int B = Cutoff(top, 5);
                rec.Clear(); Walk(A, C, 1, 0, vlo, vhi, 5, B);
                all.AddRange(rec);
                var cut = FloorDiv(M0 - C, A);
                if (cut >= vlo) dir.Add((1, 0, vlo, (long)(cut < vhi ? cut : vhi)));
                all = Compress(all);
                sum[j] += Union(all);
                direct[j] += dir.Count == 0 ? 0 : Union(dir);
                if (j < h)
                {
                    // parity is constant on the leaf while A is even
                    if (A % 2 != 0) throw new Exception("parity not constant");
                    if (C % 2 == 0) { A /= 2; C /= 2; } else { A = 3 * A / 2; C = (3 * C + 1) / 2; }
                }
            }
        }
        for (int j = 0; j <= h; j++) { Check($"E=5 union through endpoint {7 + j}", sum[j], want[j]); Check($"direct to [1,M0] through endpoint {7 + j}", direct[j], wantDirect[j]); }
        // cumulative unions through endpoint 11 for E = 8
        {
            const int h8 = 4; long[] want8 = { 312767911121204596, 312767911121204596, 388157214987184800, 642518980770505248, 1012490585164402578 };
            var sum8 = new long[h8 + 1];
            for (long r = 0; r < (1L << h8); r++)
            {
                long vlo = 0, vhi = (span - r) >> h8;
                Int128 A = (Int128)2187 << h8, C = 911 + 2187 * (ulo + r);
                var all8 = new List<(long q, long s, long a, long b)>();
                for (int j = 0; j <= h8; j++)
                {
                    int B = Cutoff(A * vhi + C, 8);
                    rec.Clear(); Walk(A, C, 1, 0, vlo, vhi, 8, B);
                    all8.AddRange(rec); all8 = Compress(all8); sum8[j] += Union(all8);
                    if (j < h8) { if (C % 2 == 0) { A /= 2; C /= 2; } else { A = 3 * A / 2; C = (3 * C + 1) / 2; } }
                }
            }
            for (int j = 0; j <= h8; j++) Check($"E=8 union through endpoint {7 + j}", sum8[j], want8[j]);
        }
        Console.WriteLine($"TOTAL failures {bad}");
    }

    // merge overlapping intervals inside each residue group to keep lists small
    static List<(long q, long s, long a, long b)> Compress(List<(long q, long s, long a, long b)> list)
    {
        list.Sort((x, y) => x.q != y.q ? x.q.CompareTo(y.q) : x.s != y.s ? x.s.CompareTo(y.s) : x.a.CompareTo(y.a));
        var res = new List<(long q, long s, long a, long b)>(list.Count);
        foreach (var it in list)
        {
            if (res.Count > 0 && res[^1].q == it.q && res[^1].s == it.s && it.a <= res[^1].b + 1) { if (it.b > res[^1].b) res[^1] = (it.q, it.s, res[^1].a, it.b); }
            else res.Add(it);
        }
        return res;
    }
}
