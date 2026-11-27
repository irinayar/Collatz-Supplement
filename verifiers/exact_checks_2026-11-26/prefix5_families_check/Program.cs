// Independent check of the five-step meeting families n = n0 + N t, m = m0 + M t, T^5(n) = T^ell(m), and of their
// union's additional density over the ledger through C121. args: prefix5_families.csv finite_ledger_transcribed.csv
using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;

class P
{
    static BigInteger T(BigInteger x, out int bit) { bit = x.IsEven ? 0 : 1; return x.IsEven ? x / 2 : (3 * x + 1) / 2; }
    static long Gcd(long a, long b) { while (b != 0) (a, b) = (b, a % b); return a; }
    static void Main(string[] args)
    {
        var lines = File.ReadAllLines(args[0]); int bad = 0;
        var fam = new List<(long n0, long N, string w, int k)>();
        int maxEll = 0, maxK = 0;
        for (int i = 1; i < lines.Length; i++)
        {
            var f = lines[i].Split(','); long n0 = long.Parse(f[0]), N = long.Parse(f[1]), m0 = long.Parse(f[2]), M = long.Parse(f[3]); string w = f[4]; int tmin = int.Parse(f[5]);
            long q = N / 32; int k = 0; while (q % 3 == 0) { q /= 3; k++; }
            bool ok = N % 32 == 0 && q == 1 && M == 1L << w.Length && tmin == 0 && n0 % 3 == 0 && k >= 1 && m0 > 0 && m0 < n0 && M < N;
            for (long t = 0; t < 40 && ok; t++)
            {
                BigInteger x = n0 + (BigInteger)N * t, y = m0 + (BigInteger)M * t; var s = ""; var u = "";
                for (int j = 0; j < 5; j++) { x = T(x, out int b); s += b; }
                for (int j = 0; j < w.Length; j++) { y = T(y, out int b); u += b; }
                ok = s == "11101" && u == w && x == y;
            }
            if (!ok) bad++;
            fam.Add((n0, N, w, k)); maxEll = Math.Max(maxEll, w.Length); maxK = Math.Max(maxK, k);
        }
        int overlap = 0;
        for (int i = 0; i < fam.Count; i++)
            for (int j = i + 1; j < fam.Count; j++)
                if ((fam[i].n0 - fam[j].n0) % Gcd(fam[i].N, fam[j].N) == 0) overlap++;
        Console.WriteLine($"families={fam.Count} failures={bad} overlapping pairs={overlap} max target length={maxEll} max ternary exponent={maxK}");

        // finite ledger rules that share integers with some family
        var rules = File.ReadAllLines(args[1]); var mixedHit = new List<string>(); var pureHit = new HashSet<string>();
        for (int i = 1; i < rules.Length; i++)
        {
            var f = rules[i].Split(','); long r = long.Parse(f[1]), m = long.Parse(f[2]);
            foreach (var q in fam)
                if ((r - q.n0) % Gcd(m, q.N) == 0) { if (m % 3 == 0) mixedHit.Add($"{f[0]}(mod {m}) meets {q.n0} mod {q.N}"); else pureHit.Add(f[0]); }
        }
        Console.WriteLine($"binary rules met: {string.Join(" ", pureHit)}; mixed rules met: {mixedHit.Count}");
        foreach (var s in mixedHit.GetRange(0, Math.Min(6, mixedHit.Count))) Console.WriteLine("  " + s);

        BigInteger den = BigInteger.Pow(3, maxK), num = 0;
        foreach (var q in fam) num += BigInteger.Pow(3, maxK - q.k);
        Console.WriteLine($"ternary measure of the union = {num}/3^{maxK} = {(double)num / (double)den:F9} (C130 alone 1/81)");
        Console.WriteLine($"ratio to C130 = {(double)num * 81 / (double)den:F9}");
    }
}
