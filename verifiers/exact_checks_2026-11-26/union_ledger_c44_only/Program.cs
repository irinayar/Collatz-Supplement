// Fixed-depth conditional-rule ledger: density of integers covered by coefficient crossing within T steps or by a listed
// certificate class. Classes are binary x ternary cylinders; the 103 mod 8192 part is treated by direct enumeration of
// its depth-41 tree and the stored classification. Single thread.
// args: finite_ledger.csv parents27.txt direct9.bin previous_cylinders.csv pullbacks.txt
using System;
using System.IO;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;

class Cyl { public int a; public ulong rb; public int b; public long rt; public int id; }

class P
{
    static readonly long[] p3 = new long[39];
    static readonly UInt128[] P3 = new UInt128[70];
    const int G = 14; static readonly long P14 = 4782969;
    static byte[] labels;
    static List<ulong> parents = new();

    static void Main(string[] args)
    {
        var clock = Stopwatch.StartNew();
        p3[0] = 1; for (int i = 1; i < 39; i++) p3[i] = 3 * p3[i - 1];
        P3[0] = 1; for (int i = 1; i < 70; i++) P3[i] = 3 * P3[i - 1];
        foreach (var tok in File.ReadAllText(args[1]).Split(new[] { ' ', '\n', '\r', ',', '\t' }, StringSplitOptions.RemoveEmptyEntries)) parents.Add(ulong.Parse(tok));
        labels = File.ReadAllBytes(args[2]);

        var finite = new List<Cyl>();
        var lines = File.ReadAllLines(args[0]);
        for (int i = 1; i < lines.Length; i++) { var f = lines[i].Split(','); finite.Add(FromMod(ulong.Parse(f[1]), ulong.Parse(f[2]))); }
        finite.Add(FromMod(303, 5184));                       // C121

        var zeroBase = ZeroTail(false); var zeroAll = ZeroTail(true);
        var baseline = new List<Cyl>(finite); baseline.AddRange(zeroBase);

        // additions
        var ancestors = Ancestors(14);
        var c44 = new List<Cyl>(); c44.AddRange(C44(5, 7, 4)); c44.AddRange(C44(4, 11, 3));
        var pulls = new List<Cyl>(); int tiny = 0; foreach (var l in File.ReadAllLines(args[4])) { var f = l.Split(','); if (BigInteger.Parse(f[0]) % (BigInteger.One << 50) == 0) { tiny++; continue; } pulls.Add(FromMod(BigInteger.Parse(f[1]), BigInteger.Parse(f[0]))); }
        var eq = new List<Cyl>(); var pc = File.ReadAllLines(args[3]); var head = pc[0].Split(','); int iL = Array.IndexOf(head, "L"), ir = Array.IndexOf(head, "r");
        for (int i = 1; i < pc.Length; i++) { var f = pc[i].Split(','); int L = int.Parse(f[iL]); eq.Add(new Cyl { a = L, rb = ulong.Parse(f[ir]) & ((1UL << L) - 1) }); }
        Console.WriteLine($"pullback exponents: 2^{(pulls.Count > 0 ? System.Linq.Enumerable.Max(pulls, c => c.a) : 0)} 3^{(pulls.Count > 0 ? System.Linq.Enumerable.Max(pulls, c => c.b) : 0)}");
        Console.WriteLine($"pullbacks with binary exponent at least 50 left out (negligible measure): {tiny}");
        Console.WriteLine($"cylinders: finite+C121={finite.Count} zero-tail(baseline)={zeroBase.Count} zero-tail(all)={zeroAll.Count} ancestors={ancestors.Count} C44={c44.Count} pullbacks={pulls.Count} C126={eq.Count}");

        var steps = new List<(string name, List<Cyl> cyl, bool labelsOn)>();
        var cur = baseline;
        steps.Add(("baseline: published ledger through C121", cur, false)); { var only = new List<Cyl>(cur); only.AddRange(c44); steps.Add(("baseline + C44 only", only, false)); }
        cur = new List<Cyl>(cur); cur.AddRange(zeroAll); cur.AddRange(ancestors); steps.Add(("+ expanding ancestors (14) and zero tails", cur, false));
        cur = new List<Cyl>(cur); cur.AddRange(c44); steps.Add(("+ C44 (both words)", cur, false));
        cur = new List<Cyl>(cur); cur.AddRange(pulls); steps.Add(("+ K209 pullbacks", cur, false));
        cur = new List<Cyl>(cur); cur.AddRange(eq); steps.Add(("+ C126 equal-count cylinders", cur, false));
        steps.Add(("+ under 103 mod 8192: C125, C127 and earlier budgets, C129", cur, true));

        steps.RemoveRange(2, steps.Count - 2); foreach (var (name, cyl, labelsOn) in steps)
        {
            for (int i = 0; i < cyl.Count; i++) cyl[i].id = i;
            var r32 = Ledger(cyl, 32, labelsOn); var r100 = Ledger(cyl, 100, labelsOn);
            Console.WriteLine($"{name}\n    depth 32: {100 * (1 - r32):F10}%   depth 100: {100 * (1 - r100):F10}%   t={clock.Elapsed.TotalSeconds:F0}s");
        }
        Console.WriteLine($"peakMB={Process.GetCurrentProcess().PeakWorkingSet64 >> 20}");
    }

    static Cyl FromMod(BigInteger r, BigInteger m)
    {
        int a = 0, b = 0; while (m % 2 == 0) { m /= 2; a++; } while (m % 3 == 0) { m /= 3; b++; }
        if (m != 1 || a > 63 || b > 38) throw new Exception($"modulus out of range 2^{a} 3^{b}");
        return new Cyl { a = a, rb = (ulong)(r % (BigInteger.One << a)), b = b, rt = (long)(r % p3[b]) };
    }
    static List<Cyl> ZeroTail(bool all)
    {
        var list = new List<Cyl>();
        for (int k = 0; k <= 40; k++)
            for (int s = 0; s <= 21; s++)
            {
                if (!all && !(k == 0 || k == 2 || k == 12 || ((k == 6 || k == 8) && s <= 5))) continue;
                int r = 2; while (BigInteger.Pow(3, r + s) <= BigInteger.One << (r + 2 * s + k + 1)) r++;
                int p = r + s; if (p > 21) continue;
                long mod = p3[p], inv2 = (mod + 1) / 2;
                BigInteger i2s = BigInteger.ModPow(inv2, 2 * s + 1, mod), ik = BigInteger.ModPow(inv2, k, mod);
                BigInteger v = ik * (1 - BigInteger.Pow(3, s + 1) * i2s) % mod; if (v < 0) v += mod;
                list.Add(new Cyl { a = 0, b = p, rt = (long)v });
            }
        return list;
    }

    // minimal cylinders of a subset of Z/3^top
    static List<(int b, long rt)> Compress(bool[] set, int top)
    {
        var res = new List<(int, long)>(); var done = new bool[set.Length];
        for (int j = 0; j <= top; j++)
            for (long v = 0; v < p3[j]; v++)
            {
                bool full = true; if (done[v]) continue;
                for (long w = v; w < set.Length; w += p3[j]) if (!set[w]) { full = false; break; }
                if (full) { res.Add((j, v)); for (long w = v; w < set.Length; w += p3[j]) done[w] = true; }
            }
        return res;
    }

    static List<Cyl> Ancestors(int top)
    {
        var set = new bool[p3[top]];
        for (int a = 1; a <= top; a++)
        {
            long mod = p3[a]; int L = 0; while ((1L << (L + 1)) <= mod) L++;
            long inv2 = (mod + 1) / 2, invL = 1; for (int i = 0; i < L; i++) invL = invL * inv2 % mod;
            void Words(int j, int odd, long C)
            {
                if (j == L) { if (odd != a) return; long y = (long)((UInt128)C * (UInt128)invL % (UInt128)mod); for (long v = y; v < set.Length; v += mod) set[v] = true; return; }
                if (a - odd > L - j) return;
                Words(j + 1, odd, C); if (odd < a) Words(j + 1, odd + 1, 3 * C + (1L << j));
            }
            Words(0, 0, 0);
        }
        long m = 0; foreach (var z in set) if (z) m++;
        Console.WriteLine($"ancestor catalogue measure {m}/3^{top}");
        var list = new List<Cyl>(); foreach (var (b, rt) in Compress(set, top)) list.Add(new Cyl { a = 0, b = b, rt = rt });
        return list;
    }

    static List<Cyl> C44(int p, ulong r0, int a)
    {
        var set = new bool[p3[12]];
        void Walk(BigInteger v, BigInteger s, int len, long R, int k)
        {
            BigInteger bound = (BigInteger.One << p) * p3[k];
            if (len > 0 && (s < bound || (s == bound && v < r0 + (BigInteger.One << p) * R)))
            {
                for (long t = R; t < set.Length; t += p3[k]) set[t] = true;
                if (s < bound) return;
            }
            if (len == 24) return;
            Walk(2 * v, 2 * s, len + 1, R, k);
            if (s % 3 == 0) { if (v % 3 == 2) Walk((2 * v - 1) / 3, 2 * s / 3, len + 1, R, k); }
            else if (k < 12)
            {
                int sm = (int)(s % 3), vm = (int)(v % 3), h0 = ((2 - vm + 3) * sm) % 3;
                Walk((2 * (v + s * h0) - 1) / 3, 2 * s, len + 1, R + p3[k] * h0, k + 1);
            }
        }
        Walk(20, p3[a], 0, 0, 0);
        long cnt = 0; foreach (var z in set) if (z) cnt++;
        Console.WriteLine($"C44 word of length {p}: cover {cnt}/3^12");
        var nset = new bool[set.Length]; long step = (1L << p) % set.Length;
        for (long t = 0; t < set.Length; t++) if (set[t]) nset[((long)r0 + step * t) % set.Length] = true;
        var list = new List<Cyl>(); foreach (var (b, rt) in Compress(nset, 12)) list.Add(new Cyl { a = p, rb = r0, b = b, rt = rt });
        return list;
    }

    // measure of the union of ternary cylinders (nested or disjoint)
    static double Union(List<Cyl> t)
    {
        t.Sort((x, y) => x.b != y.b ? x.b.CompareTo(y.b) : x.rt.CompareTo(y.rt));
        var kept = new HashSet<(int, long)>(); var levels = new List<int>(); double m = 0;
        foreach (var c in t)
        {
            bool inside = false;
            foreach (var j in levels) if (j <= c.b && kept.Contains((j, c.rt % p3[j]))) { inside = true; break; }
            if (inside) continue;
            kept.Add((c.b, c.rt)); if (levels.Count == 0 || levels[^1] != c.b) levels.Add(c.b);
            m += 1.0 / p3[c.b];
        }
        return m;
    }

    static Dictionary<(int, int, int), double> memo; static int depthT;
    // fraction of binary extensions from (l steps, a odd, state of the initial-run rule C08) surviving to depth T
    static double Ext(int l, int a, int st)
    {
        if (l >= depthT && st != 0 && st != 1) return 1;
        if (l >= depthT) return 1;
        if (memo.TryGetValue((l, a, st), out var v)) return v;
        double s = 0;
        for (int o = 0; o <= 1; o++)
        {
            int na = a + o; if (BigInteger.Pow(3, na) < (BigInteger.One << (l + 1))) continue;
            int ns = Step(st, o == 1); if (ns == 2) continue;
            s += 0.5 * Ext(l + 1, na, ns);
        }
        memo[(l, a, st)] = s; return s;
    }
    // 0 initial odd run, 1 one even after it, 2 two evens (covered by C08), 3 run ended by a single even
    static int Step(int st, bool odd) => st == 0 ? (odd ? 0 : 1) : st == 1 ? (odd ? 3 : 2) : st;

    static Dictionary<string, double> ucache = new();

    static double Ledger(List<Cyl> cyl, int T, bool labelsOn)
    {
        memo = new(); depthT = T; ucache = new();
        var pure = new List<Cyl>(); var tern = new List<Cyl>(); var global = new List<Cyl>();
        foreach (var c in cyl) { if (c.b == 0) pure.Add(c); else if (c.a == 0) global.Add(c); else tern.Add(c); }
        double unc = 0;
        void Rec(int d, ulong res, UInt128 x, int a, int st, List<Cyl> pl, List<Cyl> tl)
        {
            if (d == 13 && res == 103) return;                       // treated separately
            foreach (var c in pl) if (c.a <= d) return;               // a binary class covers the whole node
            bool split = d < 13;
            if (!split) { foreach (var c in pl) if (c.a > d) { split = true; break; } if (!split) foreach (var c in tl) if (c.a > d) { split = true; break; } }
            if (split)
            {
                for (int bit = 0; bit < 2; bit++)
                {
                    UInt128 y = bit == 1 ? x + P3[a] : x; bool odd = ((ulong)y & 1) == 1; int na = a + (odd ? 1 : 0), ns = Step(st, odd);
                    if (d + 1 <= T && P3[na] < ((UInt128)1 << (d + 1))) continue;
                    if (ns == 2) continue;
                    ulong nr = res | ((ulong)bit << d); ulong m = (1UL << (d + 1)) - 1;
                    var np = pl.FindAll(c => c.a <= d || (c.rb & m) == nr);
                    var nt = tl.FindAll(c => c.a <= d || (c.rb & m) == nr);
                    Rec(d + 1, nr, odd ? (3 * y + 1) >> 1 : y >> 1, na, ns, np, nt);
                }
                return;
            }
            var key = new System.Text.StringBuilder(); foreach (var c in tl) { key.Append(c.id).Append(','); }
            if (!ucache.TryGetValue(key.ToString(), out var u)) { var all = new List<Cyl>(global); all.AddRange(tl); u = Union(all); ucache[key.ToString()] = u; }
            double surv = (d < T ? Ext(d, a, st) : 1) / Math.Pow(2, d);
            unc += (1 - u) * surv;
        }
        Rec(0, 0, 0, 0, 0, pure, tern);
        return unc + Region103(cyl, T, labelsOn);
    }

    static double Region103(List<Cyl> cyl, int T, bool labelsOn)
    {
        var active = cyl.FindAll(c => c.b > 0 && c.a <= 13 && (103UL & ((1UL << c.a) - 1)) == c.rb);
        if (cyl.Exists(c => c.b > 0 && c.a > 13 && (c.rb & 8191) == 103)) Console.WriteLine("note: a deeper ternary class under 103 is not used (lower bound)");
        double free = 1 - Union(new List<Cyl>(active));
        if (!labelsOn)
        {
            double s = 0;
            foreach (var q in parents)
            {
                UInt128 y = q; int a = 0; for (int j = 1; j <= 27; j++) { if (((ulong)y & 1) == 1) { a++; y = (3 * y + 1) >> 1; } else y >>= 1; }
                s += (T > 27 ? Ext(27, a, 3) : 1) / Math.Pow(2, 27);
            }
            return s * free;
        }
        // grid of uncovered residues of n mod 3^14, summed over classes mod 3^9
        var cov = new bool[P14]; foreach (var c in active) if (c.b <= G) for (long v = c.rt; v < P14; v += p3[c.b]) cov[v] = true;
        var above = new int[19683]; for (long v = 0; v < P14; v++) if (!cov[v]) above[v % 19683]++;
        double open = 0, minus = 0; var mask = new bool[19683];
        void Gen(ulong r, UInt128 x, int j, int a)
        {
            if (j == 41)
            {
                long idx = (long)((r - 103) >> 13);
                int lab = (labels[idx >> 1] >> (int)((idx & 1) * 4)) & 15;
                if (lab == 15) throw new Exception("eligible source labelled 15");
                if (lab != 10) return;
                double w = (T > 41 ? Ext(41, a, 3) : 1) / Math.Pow(2, 41);
                open += w;
                if (a >= 32)
                {
                    Array.Clear(mask); Walk(x, (UInt128)p3[a], 0, 0, 0, r, mask);
                    long nm = (long)(r % 19683), step = (long)((1UL << 41) % 19683), cnt = 0;
                    for (int t = 0; t < 19683; t++) { if (mask[t]) cnt += above[nm]; nm += step; if (nm >= 19683) nm -= 19683; }
                    minus += w * cnt / P14;
                }
                return;
            }
            for (int bit = 0; bit < 2; bit++)
            {
                UInt128 y = bit == 1 ? x + P3[a] : x; bool odd = ((ulong)y & 1) == 1; int na = a + (odd ? 1 : 0);
                UInt128 nx = odd ? (3 * y + 1) >> 1 : y >> 1; ulong nr = r | ((ulong)bit << j); int nj = j + 1;
                // reverse meeting on the whole cylinder: a smaller predecessor of the current state
                if (nx % 3 == 2 && 2 * nx - 1 < (UInt128)3 * nr && 2 * P3[na] < 3 * ((UInt128)1 << nj)) continue;
                if (P3[na] < ((UInt128)1 << nj))
                {
                    if (nj > T) open += 1.0 / Math.Pow(2, nj);     // crossing after depth T is not counted
                    continue;
                }
                Gen(nr, nx, nj, na);
            }
        }
        UInt128 x0 = 103; int a0 = 0; for (int j = 1; j <= 13; j++) { if (((ulong)x0 & 1) == 1) { a0++; x0 = (3 * x0 + 1) >> 1; } else x0 >>= 1; }
        Gen(103, x0, 13, a0);
        return open * free - minus;
    }

    // witness set (e <= 9, any number of odd inverses) of a depth-41 source, as residues of t mod 3^9
    static void Walk(UInt128 v, UInt128 s, int e, long R, int k, ulong r, bool[] mask)
    {
        UInt128 bound = ((UInt128)1 << 41) * (UInt128)p3[k];
        bool hit = s < bound || (s == bound && v < (UInt128)r + ((UInt128)R << 41));
        if (hit) { for (long t = R; t < 19683; t += p3[k]) mask[t] = true; if (s < bound) return; }
        if (e < 9) Walk(v + v, s + s, e + 1, R, k, r, mask);
        if (s % 3 == 0) { if (v % 3 == 2) Walk((2 * v - 1) / 3, 2 * s / 3, e, R, k, r, mask); }
        else
        {
            int sm = (int)(s % 3), vm = (int)(v % 3), h0 = ((2 - vm + 3) * sm) % 3;
            Walk((2 * (v + s * (UInt128)h0) - 1) / 3, 2 * s, e, R + p3[k] * h0, k + 1, r, mask);
        }
    }
}
