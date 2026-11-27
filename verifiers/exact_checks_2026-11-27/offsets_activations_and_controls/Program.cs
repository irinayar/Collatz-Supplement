// Exact checks: count-layer offsets and the split of the minimum-six cells, first activations in the later census,
// exclusions of listed progressions, local stage cell counts and continuation count controls.  Argument: the data folder.
using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Numerics;

class P
{
    static int bad = 0;
    static void Check(string name, bool ok, string info = "") { if (!ok) bad++; Console.WriteLine($"{(ok ? "ok  " : "FAIL")} {name} {info}"); }
    static UInt128 T(UInt128 x) => (x & 1) == 1 ? (3 * x + 1) >> 1 : x >> 1;
    static bool Reach(UInt128 z, UInt128 n, int e) { if (z < n) return true; if (z % 3 == 2 && Reach((2 * z - 1) / 3, n, e)) return true; return e > 0 && Reach(2 * z, n, e - 1); }
    static UInt128 H(UInt128 z, int e, int b)
    {
        if (b == 0) return z << e;
        UInt128 best = UInt128.MaxValue;
        if (e > 0) best = H(2 * z, e - 1, b);
        if (z % 3 == 2) { var h = H((2 * z - 1) / 3, e, b - 1); if (h < best) best = h; }
        return best;
    }
    static BigInteger Crt(BigInteger a, BigInteger m, BigInteger b, BigInteger q) { BigInteger x = a % m; while (x % q != b % q) x += m; if (x == 0) x += m * q; return x; }
    static readonly int[] R81 = Enumerable.Range(0, 81).Where(a => a % 3 != 2 && a % 9 != 4 && a != 10 && a != 60).ToArray();

    // all words with 'zeros' even steps and 'ones' odd steps, with affine numerator
    static IEnumerable<(string v, BigInteger c)> Words(int zeros, int ones)
    {
        var buf = new char[zeros + ones];
        IEnumerable<(string, BigInteger)> Rec(int pos, int z, int o, BigInteger c)
        {
            if (pos == buf.Length) { yield return (new string(buf), c); yield break; }
            if (z < zeros) { buf[pos] = '0'; foreach (var x in Rec(pos + 1, z + 1, o, c)) yield return x; }
            if (o < ones) { buf[pos] = '1'; foreach (var x in Rec(pos + 1, z, o + 1, 3 * c + (BigInteger.One << pos))) yield return x; }
        }
        return Rec(0, 0, 0, 0);
    }

    static void Main(string[] args)
    {
        var data = args[0];
        var sixData = File.ReadAllLines(Path.Combine(data, "six_even_rows.csv")).Skip(1).Where(l => l.Length > 0).Select(l => l.Split(',')).ToList();
        var pc = File.ReadAllLines(Path.Combine(data, "previous_cylinders.csv")); var head = pc[0].Split(','); int iL = Array.IndexOf(head, "L"), ir = Array.IndexOf(head, "r");
        var c126 = pc.Skip(1).Select(l => l.Split(',')).Select(f => (L: int.Parse(f[iL]), r: ulong.Parse(f[ir]) & ((1UL << int.Parse(f[iL])) - 1))).ToList();
        Check("149 equal-count cylinders loaded", c126.Count == 149, c126.Count.ToString());
        bool Meets(BigInteger x, BigInteger M) => c126.Any(c => { var g = BigInteger.GreatestCommonDivisor(M, BigInteger.One << c.L); return (x - c.r) % g == 0; });

        // ---- offsets of the five- and six-even layers, and the split of the minimum-six cells
        var sixRows = new HashSet<BigInteger>();
        {
            foreach (var r in sixData) sixRows.Add(BigInteger.Parse(r[0]));
            // finite rules with the one further finite rule 303 mod 5184, the pullback progressions, and the equal-count cylinders
            var dom = File.ReadAllLines(Path.Combine(data, "finite_ledger_119.csv")).Skip(1).Where(l => l.Length > 0).Select(l => l.Split(',')).Select(f => (r: BigInteger.Parse(f[1]), m: BigInteger.Parse(f[2]))).ToList();
            dom.Add((303, 5184));
            dom.AddRange(File.ReadAllLines(Path.Combine(data, "pullbacks.txt")).Where(l => l.Length > 0).Select(l => l.Split(',')).Select(f => (r: BigInteger.Parse(f[1]), m: BigInteger.Parse(f[0]))));
            dom.AddRange(c126.Select(c => (r: (BigInteger)c.r, m: BigInteger.One << c.L)));
            Check("501 listed domains", dom.Count == 501, dom.Count.ToString());
            bool Hits(BigInteger x, BigInteger M) => dom.Any(d => (x - d.r) % BigInteger.GreatestCommonDivisor(M, d.m) == 0);
            var fam = sixData.Where(r => r[5] == "1").Select(r => (x: BigInteger.Parse(r[1]), M: 19683 * (BigInteger.One << int.Parse(r[3])))).ToList();
            var comp = File.ReadAllLines(Path.Combine(data, "complement_rows.csv")).Skip(1).Where(l => l.Length > 0).Select(l => l.Split(',')).ToList();
            var compSets = comp.Select(r => (x: BigInteger.Parse(r[2]), M: r[0] == "a" ? BigInteger.Parse(r[4]) * 4096 : r[0] == "b" ? 2187 * (BigInteger.One << int.Parse(r[4])) : new BigInteger(1327104))).ToList();
            int hit = fam.Count(f => Hits(f.x, f.M)), hit2 = compSets.Count(f => Hits(f.x, f.M));
            Check("43 starred six-even rows avoid the 501 domains", fam.Count == 43 && hit == 0, $"rows {fam.Count}, intersections {hit}");
            Check("complementary rows avoid the 501 domains", compSets.Count == 21 && hit2 == 0, $"rows {compSets.Count}, intersections {hit2}");
            Check("delayed progression avoids the 501 domains", !Hits(73161711, 80621568));

            var five = Words(5, 12).Select(w => (w.v, num: w.c - 2048 * 227)).Where(w => w.num % 243 == 0).Select(w => (w.v, D: w.num / 243)).ToList();
            Check("five-even offsets: 495 distinct in 317 classes", five.Count == 495 && five.Select(w => w.D).Distinct().Count() == 495 && five.Select(w => ((w.D % 2187) + 2187) % 2187).Distinct().Count() == 317, $"{five.Count} {five.Select(w => ((w.D % 2187) + 2187) % 2187).Distinct().Count()}");
            var six = Words(6, 14).Select(w => (w.v, num: w.c - 16384 * 227)).Where(w => w.num % 243 == 0).Select(w => (w.v, D: w.num / 243)).ToList();
            var byClass = six.GroupBy(w => (int)(((w.D % 19683) + 19683) % 19683)).ToDictionary(g => g.Key, g => g.OrderByDescending(w => w.D).First());
            Check("six-even offsets: 3004 distinct in 1874 classes", six.Count == 3004 && six.Select(w => w.D).Distinct().Count() == 3004 && byClass.Count == 1874, $"{six.Count} {byClass.Count}");

            var formulas = new Dictionary<BigInteger, string>(); int cells6 = 0;
            foreach (int root in R81) for (long u = 0; u < 243; u++)
            {
                var n = (UInt128)Crt(111, 128, root + 81 * u, 19683);
                var y = n; for (int s = 0; s < 6; s++) y = T(y);
                if (Reach(y, n, 5) || !Reach(y, n, 6)) continue;
                cells6++;
                var w = byClass[(int)((16384 * (BigInteger)n) % 19683)];
                formulas[w.D] = w.v;
            }
            int one = 0, anc = 0, full = 0, other = 0; var fullD = new HashSet<BigInteger>();
            foreach (var kv in formulas)
            {
                string src = "111101", tgt = kv.Value; int c = 0;
                while (c < src.Length && c < tgt.Length && src[src.Length - 1 - c] == tgt[tgt.Length - 1 - c]) c++;
                int left = src.Length - c;
                if (left == 1) one++; else if (left == 0) anc++; else if (left == 6) { full++; fullD.Add(kv.Key); } else other++;
            }
            Check("minimum-six formulas: 110 = 34 one-step + 28 ancestor + 48 full", cells6 == 110 && formulas.Count == 110 && one == 34 && anc == 28 && full == 48 && other == 0, $"cells {cells6} formulas {formulas.Count} split {one}/{anc}/{full}/{other}");
            Check("the 48 full-source offsets are the listed six-even rows", fullD.SetEquals(sixRows));
        }

        // ---- first activations in the later census
        {
            var accepted = new Dictionary<int, HashSet<long>>(); bool uniform = true;
            for (int j = 6; j <= 18; j++)
            {
                int l = Math.Max(7, j); var set = new HashSet<long>();
                for (long ext = 0; ext < (1L << (l - 7)); ext++)
                {
                    long bin = 111 + 128 * ext; int acc = 0;
                    foreach (int a in R81)
                    {
                        var n = (UInt128)Crt(bin, BigInteger.One << l, a, 81);
                        var y = n; int k = 0; for (int s = 0; s < j; s++) { if ((y & 1) == 0) k++; y = T(y); }
                        if (Reach(y, n, k + 2)) acc++;
                    }
                    if (acc != 0 && acc != 43) uniform = false;
                    if (acc == 43) set.Add(bin);
                }
                accepted[j] = set;
            }
            Check("acceptance independent of the ternary root", uniform);
            Check("endpoints 9 and 10 accept exactly 367 mod 512", accepted[9].SetEquals(new[] { 367L }) && accepted[10].All(b => b % 512 == 367) && accepted[10].Count == 2);
            var first = new List<(long r, int len, int j)>();
            var counts = new Dictionary<int, int>();
            for (int j = 6; j <= 18; j++)
            {
                int l = Math.Max(7, j);
                foreach (var r in accepted[j]) if (!first.Any(f => r % (1L << f.len) == f.r)) { first.Add((r, l, j)); counts[j] = counts.GetValueOrDefault(j) + 1; }
            }
            string got = string.Join(" ", counts.OrderBy(k => k.Key).Select(k => $"{k.Key}:{k.Value}"));
            Check("first activations", got == "9:1 11:1 12:1 13:6 14:6 15:10 16:38 17:35 18:62", got);
            var late = first.Where(f => f.j >= 15).ToList();
            var above = late.Where(f => { UInt128 x = (UInt128)f.r; int a = 0; for (int i = 1; i <= f.len; i++) { if ((x & 1) == 1) a++; x = T(x); if (!(BigInteger.Pow(3, a) > (BigInteger.One << i))) return false; } return true; }).ToList();
            int meet = above.Count(f => Meets(f.r, BigInteger.One << f.len));
            Check("145 later cylinders, 48 with coefficients above 1, 4 meeting the equal-count set", late.Count == 145 && above.Count == 48 && meet == 4, $"{late.Count}/{above.Count}/{meet}");
        }

        // ---- local stage cell counts, enumerated from the two independent conditions
        {
            var budget = new List<int>();   // least source-six budget on the 10449 ternary refinements (-1: more than six)
            foreach (int root in R81) for (long u = 0; u < 243; u++)
            {
                var n = (UInt128)Crt(111, 128, root + 81 * u, 19683); var y = n; for (int s = 0; s < 6; s++) y = T(y);
                int mb = -1; for (int e = 0; e <= 6 && mb < 0; e++) if (Reach(y, n, e)) mb = e; budget.Add(mb);
            }
            bool Acc(long bin, int j)   // endpoint j, binary class bin mod 2^max(7,j)
            {
                var n = (UInt128)Crt(bin, BigInteger.One << Math.Max(7, j), R81[0], 81); var y = n; int k = 0; for (int s = 0; s < j; s++) { if ((y & 1) == 0) k++; y = T(y); }
                return Reach(y, n, k + 2);
            }
            var bins = Enumerable.Range(0, 128).Select(i => 111L + 128 * i).ToList();   // refinements mod 2^14
            long e9 = bins.Count(b => b % 512 == 367), e14 = bins.Count(b => Acc(b % (1L << 14), 14));
            long le4 = budget.Count(b => b >= 0 && b <= 4), le5 = budget.Count(b => b >= 0 && b <= 5), six = budget.Count(b => b == 6), all = budget.Count;
            // period 2^10 3^6: 3096 cells
            long A = le4 * 3096 / all, B = 3096 * e9 / 128, AB = le4 * 3096 / all * e9 / 128;
            Check("period 746496: 56 and 774, overlap 14, union 816", A == 56 && B == 774 && AB == 14 && A + B - AB == 816, $"{A} {B} {AB}");
            // period 2^14 3^7: 148608 cells
            long cells = 148608, prior = cells - (cells * (all - le4) / all) * (128 - e9) / 128, late = cells - (cells * (all - le4) / all) * (128 - e14) / 128, five = cells - (cells * (all - le5) / all) * (128 - e14) / 128;
            Check("period 35831808: 39168, +34200, +1980, union 75348", prior == 39168 && late - prior == 34200 && five - late == 1980 && five == 75348, $"{prior} {late - prior} {five - late} {five}");
            long add = six * (1337472 / all) * (128 - e14) / 128;
            Check("six-even cells add 7260, union 685392", add == 7260 && five * 9 + add == 685392, $"{add} {five * 9 + add}");
        }
        // ---- continuation count controls on the 903 old rows
        {
            var words = new SortedSet<string>(StringComparer.Ordinal);
            foreach (int q in new[] { 2, 3 }) for (int j = 1; j <= 12; j++) { var w = "111"; for (int i = 0; i < j; i++) w += "10" + new string('1', 1 + (BitOperations.PopCount((uint)i) % q)); words.Add(w); }
            long total = 0, relEmpty = 0, feas = 0, empty = 0, badFeas = 0;
            foreach (var w in words)
            {
                int len = w.Length, r = w.Count(c => c == '1'), k = len - r; string full = w + "1"; BigInteger res = 0;
                for (int bit = 0; bit <= len; bit++) { BigInteger x = res; for (int s = 0; s < bit; s++) x = x.IsEven ? x / 2 : (3 * x + 1) / 2; if ((x.IsEven ? '0' : '1') != full[bit]) res += BigInteger.One << bit; }
                for (int d = 1; d <= 4; d++) for (long ext = 0; ext < (1L << (d - 1)); ext++)
                {
                    BigInteger mod = BigInteger.One << (len + d), br = res + ext * (BigInteger.One << (len + 1));
                    foreach (int a in R81)
                    {
                        var n = (UInt128)Crt(br, mod, a, 81);
                        var y = n; int k2 = 0; for (int s = 0; s < len + d; s++) { if ((y & 1) == 0) k2++; y = T(y); }
                        int r2 = len + d - k2; total++;
                        if (H(y, k2 + 2, r2 + 4) == UInt128.MaxValue) relEmpty++;
                        var m = H(y, k + 2, r + 4);
                        if (m == UInt128.MaxValue) empty++;
                        else
                        {
                            feas++;
                            UInt128 P = (UInt128)(mod * 81), n1 = n + P, y1 = n1; for (int s = 0; s < len + d; s++) y1 = T(y1);
                            var m1 = H(y1, k + 2, r + 4);
                            if (!(m > n && m1 != UInt128.MaxValue && m1 - m > P)) badFeas++;
                        }
                    }
                }
            }
            Check("13545 relative layers empty", total == 13545 && relEmpty == 13545, $"{relEmpty}/{total}");
            Check("original-count layers: 3297 feasible, 10248 empty, none affordable", feas == 3297 && empty == 10248 && badFeas == 0, $"{feas}/{empty}, affordable {badFeas}");
        }
        Console.WriteLine($"TOTAL failures {bad}");
    }
}
