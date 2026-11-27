// Rule: n = 2247 + 2592 h, m = 1775 + 2048 h, T^5(n) = T^11(m), m < n.  (1) brute-force check;
// (2) marginal density against the ledger through C121: 119 finite rules, C85 (depth-27 parents), coefficient stopping.
// C08, C121 and the zero-tail families are disjoint by hand (parity word; 7 vs 15 mod 32; n = 0 mod 3).
// args: finite_ledger_transcribed.csv parents27.txt
using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;

class P
{
    static BigInteger T(BigInteger x) => x.IsEven ? x / 2 : (3 * x + 1) / 2;
    static void Main(string[] args)
    {
        long bad = 0, visits = 0;
        for (long h = 0; h < 300000; h++)
        {
            BigInteger n = 2247 + 2592 * (BigInteger)h, m = 1775 + 2048 * (BigInteger)h, x = n, y = m;
            if (!(m < n && m > 0 && 81 * m == 64 * n - 33)) bad++;
            for (int i = 0; i < 5; i++) x = T(x);
            for (int i = 0; i < 11; i++) { if (y == n) visits++; y = T(y); }
            if (x != y) bad++;
        }
        Console.WriteLine($"brute force h<300000: failures={bad}, target passing through n={visits}");

        var parents = new List<ulong>();
        foreach (var tok in File.ReadAllText(args[1]).Split(new[] { ' ', '\n', '\r', ',', '\t' }, StringSplitOptions.RemoveEmptyEntries)) parents.Add(ulong.Parse(tok));
        var rules = new List<(long r, int d, int e)>();
        var lines = File.ReadAllLines(args[0]);
        for (int i = 1; i < lines.Length; i++)
        {
            var f = lines[i].Split(','); long res = long.Parse(f[1]), mm = long.Parse(f[2]); int d = 0, e = 0;
            while (mm % 2 == 0) { mm /= 2; d++; }
            while (mm % 3 == 0) { mm /= 3; e++; }
            rules.Add((res, d, e));
        }
        // rules that can meet n = 7 mod 32, n = 60 mod 81
        var pure = new List<(long r, int d)>();
        foreach (var q in rules)
        {
            long p2 = 1L << Math.Min(q.d, 5), m3 = 1; for (int k = 0; k < Math.Min(q.e, 4); k++) m3 *= 3;
            if (q.r % p2 != 7 % p2 || q.r % m3 != 60 % m3) continue;
            if (q.e != 0) throw new Exception("a mixed rule meets the class");
            pure.Add((q.r % (1L << q.d), q.d));
        }
        pure.Sort((u, v) => u.d.CompareTo(v.d));
        var anti = new List<(long r, int d)>();
        foreach (var c in pure) if (!anti.Exists(u => c.r % (1L << u.d) == u.r)) anti.Add(c);
        Console.WriteLine($"binary rules meeting the class: {pure.Count}, disjoint after nesting: {anti.Count}; parents={parents.Count}");
        foreach (var c in anti) foreach (var p in parents) if ((long)(p % (1UL << Math.Min(c.d, 27))) == c.r % (1L << Math.Min(c.d, 27))) throw new Exception("a binary rule meets a depth-27 parent");

        Exact(parents, anti, 32); Exact(parents, anti, 100);
    }

    public static void Exact(List<ulong> parents, List<(long r, int d)> anti, int depth)
    {
        var memo = new Dictionary<(int, int), BigInteger>();
        BigInteger Count(BigInteger b, int l)
        {
            BigInteger x = b % (BigInteger.One << l); int a = 0;
            for (int j = 1; j <= l; j++) { if (!x.IsEven) a++; x = T(x); if (BigInteger.Pow(3, a) < (BigInteger.One << j)) return 0; }
            return Ext(l, a, depth, memo);
        }
        BigInteger n = 0;
        for (long b = 7; b < 8192; b += 32)
        {
            if (b != 103) n += Count(b, 13);
            else foreach (var p in parents) n += Count(p, 27);
        }
        // rules never meet the uncertified depth-27 parents, so their part inside 103 mod 8192 is already excluded by C85
        foreach (var c in anti)
        {
            BigInteger inside = c.d <= 13 ? (103 % (1L << c.d) == c.r % (1L << c.d) ? Count(103, 13) : 0) : (c.r % 8192 == 103 ? Count(c.r, c.d) : 0);
            var whole = Count(c.r, c.d);
            Console.WriteLine($"  depth {depth} rule mod 2^{c.d}: survivors {whole}, of which inside 103 mod 8192 {inside}");
            n -= whole - inside;
        }
        Console.WriteLine($"  depth {depth} count over 81*2^{depth}: {n}");
        BigInteger den = (BigInteger.One << depth) * 81, g = BigInteger.GreatestCommonDivisor(n, den);
        Console.WriteLine($"depth {depth} exact marginal = {n / g}/{den / g}");
    }
    // continuations from step l with a odd steps up to step depth keeping 3^a_j > 2^j
    static BigInteger Ext(int l, int a, int depth, Dictionary<(int, int), BigInteger> memo)
    {
        if (l >= depth) return 1;
        if (memo.TryGetValue((l, a), out var v)) return v;
        BigInteger s = 0;
        for (int odd = 0; odd <= 1; odd++) if (BigInteger.Pow(3, a + odd) > (BigInteger.One << (l + 1))) s += Ext(l + 1, a + odd, depth, memo);
        memo[(l, a)] = s; return s;
    }
}
