// Regenerate C44 (inverse target words through length 24 behind the forward words 1101 and 11101) and compute what its
// part on multiples of 3 adds to the ledger through C121 (finite rules, C85, coefficient stopping; zero-tail and other
// direct-ancestor rules cannot meet multiples of 3). args: finite_ledger_transcribed.csv parents27.txt
using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;

class P
{
    const int M = 14; static readonly long P14 = 4782969;
    static readonly long[] p3 = new long[40];
    static bool[] set; static int maxK;
    static List<(long r, int d, int e)> rules = new();
    static List<ulong> parents = new();

    // inverse words from x = 20 + 3^a t; origin must satisfy m < n = r0 + 2^p t; length at most 24
    static void Walk(BigInteger v, BigInteger s, int len, long R, int k, long r0, int p)
    {
        BigInteger bound = (BigInteger.One << p) * p3[k];
        if (len > 0 && (s < bound || (s == bound && v < r0 + (BigInteger.One << p) * R)))
        {
            if (v + s * 0 < r0 + (BigInteger.One << p) * R) { for (long t = R; t < p3[12]; t += p3[k]) set[t] = true; maxK = Math.Max(maxK, k); }
            else if (s < bound) { for (long t = R; t < p3[12]; t += p3[k]) set[t] = true; maxK = Math.Max(maxK, k); }
            if (s < bound) return;
        }
        if (len == 24) return;
        Walk(2 * v, 2 * s, len + 1, R, k, r0, p);
        if (s % 3 == 0) { if (v % 3 == 2) Walk((2 * v - 1) / 3, 2 * s / 3, len + 1, R, k, r0, p); }
        else
        {
            int sm = (int)(s % 3), vm = (int)(v % 3), h0 = ((2 - vm + 3) * sm) % 3;
            if (k + 1 > 12) return;
            Walk((2 * (v + s * h0) - 1) / 3, 2 * s, len + 1, R + p3[k] * h0, k + 1, r0, p);
        }
    }

    static BigInteger T(BigInteger x) => x.IsEven ? x / 2 : (3 * x + 1) / 2;
    static BigInteger Ext(int l, int a, int depth, Dictionary<(int, int), BigInteger> memo)
    {
        if (l >= depth) return 1;
        if (memo.TryGetValue((l, a), out var v)) return v;
        BigInteger s = 0;
        for (int o = 0; o <= 1; o++) if (BigInteger.Pow(3, a + o) > (BigInteger.One << (l + 1))) s += Ext(l + 1, a + o, depth, memo);
        memo[(l, a)] = s; return s;
    }
    // number of residues mod 2^depth in the class b mod 2^l whose first depth steps do not cross
    static BigInteger Count(BigInteger b, int l, int depth, Dictionary<(int, int), BigInteger> memo)
    {
        BigInteger x = b % (BigInteger.One << l); int a = 0;
        for (int j = 1; j <= l; j++) { if (!x.IsEven) a++; x = T(x); if (BigInteger.Pow(3, a) < (BigInteger.One << j)) return 0; }
        return Ext(l, a, depth, memo);
    }

    static void Main(string[] args)
    {
        p3[0] = 1; for (int i = 1; i < 39; i++) p3[i] = 3 * p3[i - 1];
        var lines = File.ReadAllLines(args[0]);
        for (int i = 1; i < lines.Length; i++)
        {
            var f = lines[i].Split(','); long r = long.Parse(f[1]), m = long.Parse(f[2]); int d = 0, e = 0;
            while (m % 2 == 0) { m /= 2; d++; }
            while (m % 3 == 0) { m /= 3; e++; }
            rules.Add((r, d, e));
        }
        foreach (var tok in File.ReadAllText(args[1]).Split(new[] { ' ', '\n', '\r', ',', '\t' }, StringSplitOptions.RemoveEmptyEntries)) parents.Add(ulong.Parse(tok));

        double tot32 = 0, tot100 = 0;
        foreach (var (word, r0, p, a, expect, den) in new[] { ("11101", 7L, 5, 4, 268711, 531441), ("1101", 11L, 4, 3, 89570, 177147) })
        {
            set = new bool[p3[12]]; maxK = 0;
            Walk(20, p3[a], 0, 0, 0, r0, p);
            long size = 0; foreach (var z in set) if (z) size++;
            long scaled = size / (531441 / den);
            Console.WriteLine($"{word}: regenerated cover {size}/3^12 (reported {expect}/{den} = {expect * (531441L / den)}/3^12) exact match={size == expect * (531441L / den)}; deepest level {maxK}");

            if (word == "11101" && args.Length > 2)
            {
                // are the five-step families inside the catalogue? family: n = n0 mod 3^k (and 7 mod 32)
                var inN = new bool[p3[12]]; long st = 32 % p3[12];
                for (long t = 0; t < p3[12]; t++) if (set[t]) inN[(7 + st * t) % p3[12]] = true;
                int total = 0, outside = 0;
                var rows = File.ReadAllLines(args[2]);
                for (int i = 1; i < rows.Length; i++)
                {
                    var g = rows[i].Split(','); long n0 = long.Parse(g[0]), N = long.Parse(g[1]) / 32, md = 1; int k = 0; while (N % 3 == 0) { N /= 3; md *= 3; k++; }
                    total++; for (long v = n0 % md; v < p3[12]; v += md) if (!inN[v]) { outside++; break; }
                }
                Console.WriteLine($"  families checked: {total}; not inside the regenerated catalogue: {outside}");
            }
            // set in terms of n mod 3^12, restricted to multiples of 3
            var nset = new bool[p3[12]]; long step = (1L << p) % p3[12];
            for (long t = 0; t < p3[12]; t++) if (set[t]) { long nm = (r0 + step * t) % p3[12]; if (nm % 3 == 0) nset[nm] = true; }

            foreach (int depth in new[] { 32, 100 })
            {
                var memo = new Dictionary<(int, int), BigInteger>(); double gain = 0;
                var cache = new Dictionary<string, double>();
                for (long b = r0; b < 8192; b += 1L << p)
                {
                    // binary part: residues surviving stopping, minus C85 and minus pure rules
                    BigInteger cnt = 0;
                    if (b != 103) cnt = Count(b, 13, depth, memo);
                    else foreach (var q in parents) cnt += Count(q, 27, depth, memo);
                    var active = new List<(long r, int e)>(); var pure = new List<(long r, int d)>(); var key = new System.Text.StringBuilder();
                    for (int i = 0; i < rules.Count; i++)
                    {
                        var q = rules[i];
                        if (q.e == 0)
                        {
                            if (q.d <= 13) { if (b % (1L << q.d) == q.r % (1L << q.d)) { cnt = 0; } }
                            else if (b == q.r % 8192) pure.Add((q.r % (1L << q.d), q.d));
                        }
                        else if (q.d <= 13 && b % (1L << q.d) == q.r % (1L << q.d)) { active.Add((q.r % p3[Math.Min(q.e, M)], Math.Min(q.e, M))); key.Append(i).Append(','); }
                        else if (q.d > 13) throw new Exception("deep mixed rule");
                    }
                    // pure rules deeper than 13 (antichain): they never meet the uncertified parents
                    pure.Sort((u, v) => u.d.CompareTo(v.d)); var anti = new List<(long r, int d)>();
                    foreach (var c in pure) if (!anti.Exists(u => c.r % (1L << u.d) == u.r)) anti.Add(c);
                    if (b != 103) foreach (var c in anti) cnt -= Count(c.r, Math.Min(c.d, depth), depth, memo);
                    if (cnt <= 0) continue;
                    var ks = key.ToString();
                    if (!cache.TryGetValue(ks, out var mu))
                    {
                        var cov = new bool[P14];
                        foreach (var (res, e) in active) for (long z = res; z < P14; z += p3[e]) cov[z] = true;
                        long free = 0; for (long z = 0; z < P14; z++) if (!cov[z] && nset[z % p3[12]]) free++;
                        mu = (double)free / P14; cache[ks] = mu;
                    }
                    gain += mu * (double)cnt / Math.Pow(2, depth);
                }
                Console.WriteLine($"  {word} depth {depth}: gain on multiples of 3 = {gain:E8} (percent +{100 * gain:F8})");
                if (depth == 32) tot32 += gain; else tot100 += gain;
            }
        }
        Console.WriteLine($"ledger through C121 plus this part: {99.5965843025 + 100 * tot32:F8} (depth 32), {99.9898203958 + 100 * tot100:F8} (depth 100)");
    }
}
