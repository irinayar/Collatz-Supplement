// Brute-force check of the depth-32 increment of the rule n = 2247 mod 2592: enumerate every n = 7 mod 32 below 2^32,
// iterate, and apply each exclusion directly. The ternary condition (n = 60 mod 81) is independent of the residue mod 2^32,
// so the density is count / (81 * 2^32). args: finite_ledger_transcribed.csv parents27.txt
using System;
using System.IO;
using System.Collections.Generic;

class P
{
    static long Gcd(long a, long b) { while (b != 0) (a, b) = (b, a % b); return a; }
    static void Main(string[] args)
    {
        var parents = new HashSet<ulong>();
        foreach (var tok in File.ReadAllText(args[1]).Split(new[] { ' ', '\n', '\r', ',', '\t' }, StringSplitOptions.RemoveEmptyEntries)) parents.Add(ulong.Parse(tok));
        var meet = new List<(ulong r, ulong m, string id)>();
        var lines = File.ReadAllLines(args[0]);
        for (int i = 1; i < lines.Length; i++)
        {
            var f = lines[i].Split(','); long r = long.Parse(f[1]), m = long.Parse(f[2]);
            long g = Gcd(m, 2592);
            if (((r - 2247) % g + g) % g != 0) continue;                       // no common integer
            if (m % 3 == 0) throw new Exception($"mixed rule {f[0]} meets the class");
            meet.Add(((ulong)r, (ulong)m, f[0]));
        }
        Console.Write("rules meeting the class:"); foreach (var q in meet) Console.Write($" {q.id}(mod {q.m})"); Console.WriteLine();
        ulong[] p3 = new ulong[34]; p3[0] = 1; for (int i = 1; i < 34; i++) p3[i] = 3 * p3[i - 1];
        long survivors = 0, byC85 = 0, byRules = 0, left = 0;
        for (ulong n = 7; n < (1UL << 32); n += 32)
        {
            ulong x = n; int a = 0; bool ok = true;
            for (int j = 1; j <= 32; j++)
            {
                if ((x & 1) != 0) { a++; x = (3 * x + 1) >> 1; } else x >>= 1;
                if (p3[a] < (1UL << j)) { ok = false; break; }
            }
            if (!ok) continue;
            survivors++;
            if (n % 8192 == 103 && !parents.Contains(n % (1UL << 27))) { byC85++; continue; }
            bool hit = false; foreach (var q in meet) if (n % q.m == q.r % q.m) { hit = true; break; }
            if (hit) { byRules++; continue; }
            left++;
        }
        Console.WriteLine($"survivors through depth 32: {survivors}; removed by C85: {byC85}; removed by binary rules: {byRules}; left: {left}");
        // marginal 432937/21743271936 = 6926992/(81 * 2^32)
        Console.WriteLine($"expected numerator over 81*2^32: 6926992; equal: {left == 6926992}; denominator check: {21743271936L * 16 == 81L << 32}");
    }
}
