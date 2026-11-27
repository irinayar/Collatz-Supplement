// Exact checks: odd-count cap table, closure on twenty-one source words, count-layer and later-endpoint censuses,
// delayed and fixed-base families, certified-base counts, local union fractions, logarithmic-strip constants,
// and the six-even and complementary family tables.  Argument: the data folder.
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
    static BigInteger TB(BigInteger x) => x.IsEven ? x / 2 : (3 * x + 1) / 2;

    // is there a legal inverse word from z to a state below n using at most e doublings (any number of odd inverses)?
    static bool Reach(UInt128 z, UInt128 n, int e)
    {
        if (z < n) return true;
        if (z % 3 == 2 && Reach((2 * z - 1) / 3, n, e)) return true;
        return e > 0 && Reach(2 * z, n, e - 1);
    }
    static int MinBudget(UInt128 y, UInt128 n, int max) { for (int e = 0; e <= max; e++) if (Reach(y, n, e)) return e; return -1; }
    // least origin with exactly e even and b odd steps
    static UInt128 H(UInt128 z, int e, int b)
    {
        if (b == 0) return z << e;
        UInt128 best = UInt128.MaxValue;
        if (e > 0) best = H(2 * z, e - 1, b);
        if (z % 3 == 2) { var h = H((2 * z - 1) / 3, e, b - 1); if (h < best) best = h; }
        return best;
    }
    static BigInteger Crt(BigInteger a, BigInteger m, BigInteger b, BigInteger q)
    {
        BigInteger x = a % m; while (x % q != b % q) x += m; if (x == 0) x += m * q; return x;
    }
    static readonly int[] R81 = Enumerable.Range(0, 81).Where(a => a % 3 != 2 && a % 9 != 4 && a != 10 && a != 60).ToArray();

    static void Main(string[] args)
    {
        Check("43 root residues", R81.Length == 43, R81.Length.ToString());

        // ---- depth-41 cap table
        {
            int[] K = { 0, 0, 0, 0, 0, 0, 1, 2, 4, 6, 7, 9 };
            string[] th = { "26/189", "9/31", "28/45", "29/21", "10/3", "31/3", "64/3", "88/1", "128/3", "2560/93", "24576/139", "606208/9897" };
            bool ok = true; double largest = 0;
            for (int a = 26; a <= 37; a++)
            {
                int k = 41 - a, d = 9 - k, h = 0;
                if (d >= 0) { h = 1; while (!(BigInteger.Pow(3, h) > BigInteger.Pow(2, h + d))) h++; }
                BigInteger num = BigInteger.Pow(2, h) * BigInteger.Pow(2, Math.Max(d, 0)), den = BigInteger.Pow(3, h) * BigInteger.Pow(2, Math.Max(-d, 0));
                BigInteger tn = a * num, td = 3 * (den - num); var f = th[a - 26].Split('/');
                if (h != K[a - 26] || tn * BigInteger.Parse(f[1]) != td * BigInteger.Parse(f[0])) { ok = false; Console.WriteLine($"   a={a} K={h} thr={tn}/{td}"); }
                largest = Math.Max(largest, (double)tn / (double)td);
            }
            Check("depth-41 odd-cap table", ok, $"largest threshold {largest:F3} < 177");
        }

        // ---- twenty-one source words
        {
            var words = new SortedSet<string>(StringComparer.Ordinal);
            foreach (int q in new[] { 2, 3 }) for (int j = 1; j <= 12; j++)
            {
                var w = "111";
                for (int i = 0; i < j; i++) w += "10" + new string('1', 1 + (BitOperations.PopCount((uint)i) % q));
                words.Add(w);
            }
            Check("distinct source words", words.Count == 21, words.Count.ToString());
            long oldAcc = 0, accepted = 0, rejected = 0, earlier = 0, layer12 = 0, layer13 = 0, layer25 = 0, pos36 = 0, empty36 = 0; bool per = true;
            foreach (var w in words)
            {
                int len = w.Length, r = w.Count(c => c == '1'), k = len - r;
                string full = w + "1";
                BigInteger res = 0;                                   // residue mod 2^(len+1) with parity word w1
                for (int bit = 0; bit <= len; bit++)
                {
                    BigInteger x = res; for (int s = 0; s < bit; s++) x = TB(x);
                    if ((x.IsEven ? '0' : '1') != full[bit]) res += BigInteger.One << bit;
                }
                BigInteger Mw = BigInteger.One << (len + 1);
                int acc = 0, rej = 0;
                foreach (int a in R81)
                {
                    var n = (UInt128)Crt(res, Mw, a, 81);
                    var y = n; for (int s = 0; s < len; s++) y = T(y);
                    if (Reach(y, n, k + 2)) oldAcc++;
                    if (H(y, k + 1, r + 2) < n) layer12++;
                    if (H(y, k + 1, r + 3) < n) layer13++;
                    for (int u = 0; u < 3; u++)
                    {
                        var n3 = (UInt128)Crt(res, Mw, a + 81 * u, 243);
                        var y3 = n3; for (int s = 0; s < len; s++) y3 = T(y3);
                        if (H(y3, k + 2, r + 5) < n3) layer25++;
                    }
                    for (int u = 0; u < 9; u++)
                    {
                        var m = (UInt128)Crt(res, Mw, a + 81 * u, 729);
                        var z = m; for (int s = 0; s < len; s++) z = T(z);
                        int mb = MinBudget(z, m, k + 3);
                        if (mb < 0) rej++; else if (mb == k + 3) acc++; else earlier++;
                        if (H(z, k + 3, r + 6) < m) pos36++; else empty36++;
                        var m2 = m + (UInt128)(Mw * 729); var z2 = m2; for (int s = 0; s < len; s++) z2 = T(z2);
                        if (MinBudget(z2, m2, k + 3) != mb) per = false;
                    }
                }
                accepted += acc; rejected += rej;
                if (acc != 7 || rej != 380) Console.WriteLine($"   word length {len}: accepted {acc} rejected {rej}");
            }
            Check("no smaller origin within k+2 on all 903 rows", oldAcc == 0, $"found {oldAcc}");
            Check("refinements: 147 at k+3, 7980 none, none earlier", accepted == 147 && rejected == 7980 && earlier == 0, $"{accepted}/{rejected}/{earlier}");
            Check("same decisions on the next lift", per);
            Check("profiles (1,2),(1,3),(2,5) have no smaller origin", layer12 == 0 && layer13 == 0 && layer25 == 0, $"{layer12}/{layer13}/{layer25}");
            Check("profile (3,6): 147 smaller, 7980 not", pos36 == 147 && empty36 == 7980, $"{pos36}/{empty36}");
        }

        // ---- five- and six-even layers at the first source word
        foreach (var (pow3, label) in new[] { (7, "five"), (9, "six") })
        {
            long M3 = (long)BigInteger.Pow(3, pow3), cells = 0, exact = 0, m2 = 0; var cnt = new long[8];
            int top = pow3 == 7 ? 5 : 6, odd = pow3 == 7 ? 12 : 14;
            foreach (int a in R81) for (long u = 0; u < M3 / 81; u++)
            {
                var n = (UInt128)Crt(111, 128, a + 81 * u, M3); cells++;
                var y = n; for (int s = 0; s < 6; s++) y = T(y);
                int mb = MinBudget(y, n, top);
                cnt[mb < 0 ? 7 : mb]++;
                if (H(y, top, odd) != UInt128.MaxValue) { exact++; if (H(y, top, odd) >= n) m2++; }
            }
            var s0 = string.Join(" ", Enumerable.Range(0, 7).Where(i => cnt[i] > 0).Select(i => $"e{i}:{cnt[i]}")) + $" none:{cnt[7]}";
            if (pow3 == 7) Check("five-even classification", cells == 1161 && cnt[4] == 21 && cnt[5] == 30 && cnt[7] == 1110 && exact == 44, $"cells {cells} {s0} exact-layer {exact}");
            else Check("six-even classification", cells == 10449 && cnt[4] == 189 && cnt[5] == 270 && cnt[6] == 110 && cnt[7] == 9880 && exact == 270 && m2 == 0, $"cells {cells} {s0} exact-layer {exact}, not smaller {m2}");
        }

        // ---- later endpoints 6..18
        {
            long[] expect = { 0, 0, 0, 43, 86, 215, 473, 1204, 2666, 5762, 13158, 27821, 58308 };
            long[] cellsExp = { 43, 43, 86, 172, 344, 688, 1376, 2752, 5504, 11008, 22016, 44032, 88064 };
            bool ok = true; var got = new List<string>();
            for (int j = 6; j <= 18; j++)
            {
                int l = Math.Max(7, j); long acc = 0, cells = 0;
                for (long ext = 0; ext < (1L << (l - 7)); ext++)
                {
                    long bin = 111 + 128 * ext;
                    foreach (int a in R81)
                    {
                        var n = (UInt128)Crt(bin, BigInteger.One << l, a, 81); cells++;
                        var y = n; int k = 0; for (int s = 0; s < j; s++) { if ((y & 1) == 0) k++; y = T(y); }
                        if (Reach(y, n, k + 2)) acc++;
                    }
                }
                got.Add($"{j}:{acc}");
                if (acc != expect[j - 6] || cells != cellsExp[j - 6]) ok = false;
            }
            Check("later-endpoint census, endpoints 6..18", ok, string.Join(" ", got));
        }

        // ---- delayed families
        {
            string Word(ref BigInteger x, int len) { var c = new char[len]; for (int i = 0; i < len; i++) { c[i] = x.IsEven ? '0' : '1'; x = TB(x); } return new string(c); }
            bool ok = true; const string u = "1111011100";
            foreach (var (tail, tgtTail, s0) in new[] { ("00", "01", 3), ("01000001", "00011100", 9) })
                for (int s = s0; s <= s0 + 5; s++)
                {
                    string w = u + new string('1', s) + tail;
                    BigInteger res = 0;
                    for (int bit = 0; bit < w.Length; bit++) { BigInteger x = res; for (int i = 0; i < bit; i++) x = TB(x); if ((x.IsEven ? '0' : '1') != w[bit]) res += BigInteger.One << bit; }
                    for (int h = 0; h < 4; h++)
                    {
                        BigInteger n = res + (BigInteger)h * (BigInteger.One << w.Length), num = 729 * n + 105;
                        BigInteger m = num / 1024;
                        BigInteger a = n, b = m;
                        var ws = Word(ref a, w.Length); var wt = Word(ref b, s + (tail == "00" ? 2 : 8));
                        if (num % 1024 != 0 || !(m > 0 && m < n) || ws != w || wt != new string('1', s) + tgtTail || a != b) ok = false;
                    }
                }
            Check("two delayed families, six run lengths each", ok);
        }

        // ---- certified-base counts
        {
            BigInteger M0 = 2075 * (BigInteger.One << 60), N = (1024 * M0 - 106) / 729;
            Check("N* value", N == BigInteger.Parse("3360394530848598703161"));
            BigInteger[] want = { BigInteger.Parse("59087061083336870"), BigInteger.Parse("3692941317708557"), BigInteger.Parse("3001933703362"), BigInteger.Parse("187620856459") };
            int idx = 0; var got = new List<string>(); bool ok = true;
            foreach (var d in new[] { BigInteger.One, new BigInteger(19683) }) foreach (int S in new[] { 3, 7 })
            {
                BigInteger total = 0;
                for (int s = S; s <= 71; s++)
                {
                    BigInteger Pm = BigInteger.One << (s + 12), bs = (BigInteger.One << s) * (s % 2 == 1 ? 1 : 3) - 1;
                    // inverse of 729 modulo Pm
                    BigInteger inv = 1; for (int i = 0; i < 8; i++) inv = ((inv * (2 - 729 * inv)) % Pm + Pm) % Pm;
                    BigInteger rs = (((1024 * bs - 105) * inv) % Pm + Pm) % Pm;
                    BigInteger R = rs; while (R % d != 0) R += Pm;
                    BigInteger per = d * Pm;
                    BigInteger Floor(BigInteger x, BigInteger y) { var q = BigInteger.DivRem(x, y, out var rr); return rr < 0 ? q - 1 : q; }
                    total += Floor(N - R, per) - Floor(M0 - 1 - R, per);
                }
                got.Add(total.ToString()); if (total != want[idx++]) ok = false;
            }
            Check("certified-base counts (four rows)", ok, string.Join(" ", got));
            BigInteger nx = M0 + 80219119, x2 = nx, mx = BigInteger.Parse("1703120641583223368319"), y2 = mx;
            for (int i = 0; i < 19; i++) x2 = TB(x2); for (int i = 0; i < 9; i++) y2 = TB(y2);
            Check("explicit member T^19(n)=T^9(m), m<M0", x2 == y2 && mx < M0);

            // fixed-base one-zero family
            bool fam = true; for (int t = 0; t < 50; t++) { BigInteger n = 50847 + 93312 * (BigInteger)t, m = 17855 + 32768 * (BigInteger)t, a = n, b = m; for (int i = 0; i < 7; i++) a = TB(a); for (int i = 0; i < 15; i++) b = TB(b); if (a != b || a != 289595 + 531441 * (BigInteger)t) fam = false; }
            Check("fixed-base family identity", fam);
            BigInteger lo = (M0 - 50847 + 93311) / 93312, hi = (2 * M0 - 1 - 50847) / 93312, all = (M0 - 17855) / 32768 - lo + 1;
            Check("fixed-base family counts", hi - lo + 1 == BigInteger.Parse("25637775656498709") && all == BigInteger.Parse("47369796427827692"), $"{hi - lo + 1} {all}");
            BigInteger P32 = BigInteger.Parse("3131031158784"), n32 = BigInteger.Parse("724400142495"), m32 = BigInteger.Parse("254384686527"), q32 = BigInteger.Parse("1099511627776");
            BigInteger lo32 = (M0 - n32 + P32 - 1) / P32, hi32 = (2 * M0 - 1 - n32) / P32, all32 = (M0 - m32) / q32 - lo32 + 1;
            Check("horizon-32 refinement and counts", hi32 - lo32 + 1 == 764065255 && all32 == 1411729944 && P32 == 729 * (BigInteger.One << 32) && (n32 - 50847) % 93312 == 0, $"{hi32 - lo32 + 1} {all32}");
            BigInteger ns = BigInteger.Parse("6920864801696577926132392128895766034591"), z = ns; string w100 = "1111101" + new string('1', 93), word = w100 + new string('0', 57);
            bool follows = true; for (int i = 0; i < 100; i++) { if ((z.IsEven ? '0' : '1') != word[i]) follows = false; z = TB(z); }
            bool cross = true; int a3 = 0; BigInteger V = 0;
            for (int j = 1; j <= 157; j++) { if (word[j - 1] == '1') { V = 3 * V + (BigInteger.One << (j - 1)); a3++; } bool above = BigInteger.Pow(3, a3) > (BigInteger.One << j); if (j <= 156 && !above) cross = false; if (j == 157 && above) cross = false; }
            BigInteger bound = V / ((BigInteger.One << 157) - BigInteger.Pow(3, 99));
            Check("horizon-100 member and 157-letter word", follows && cross && a3 == 99 && V == 825 * BigInteger.Pow(3, 93) - (BigInteger.One << 100) && bound == 17 && (ns - n32) % P32 == 0, $"floor {bound}");
        }

        // ---- one-zero synchronous lemma, small brute force
        {
            bool ok = true; long tests = 0;
            for (int n = 3; n < 3000; n += 2)
            {
                UInt128 x = (UInt128)n; int zeros = 0;
                for (int j = 1; j <= 24; j++)
                {
                    if ((x & 1) == 0) zeros++; x = T(x); if (zeros > 1) break;
                    for (int m = 1; m < n; m++) { UInt128 y = (UInt128)m; for (int s = 0; s < j; s++) y = T(y); tests++; if (y == x) ok = false; }
                }
            }
            Check("one-zero obstruction on odd n<3000", ok, $"{tests} comparisons");
        }

        // ---- local union fractions
        {
            (BigInteger, BigInteger) F(BigInteger a, BigInteger b) { var g = BigInteger.GreatestCommonDivisor(a, b); return (a / g, b / g); }
            BigInteger D = 10449 * (BigInteger)524288;
            var u1 = F(10449 * (BigInteger)512 - 9880 * (BigInteger)(512 - 339), 10449 * (BigInteger)512);
            var uAll = F(D - 9880 * (BigInteger)(524288 - 339 * 1024 - 256 - 1), D);
            var uF = F(D - 9880 * (BigInteger)(524288 - 339 * 1024 - 256), D);
            Check("local union fractions", u1 == (455081, 668736) && uAll == (51813371, 76087296) && uF == (1821559, 2674944), $"{u1} {uF} {uAll}");
            var inc = F(uAll.Item1 * uF.Item2 - uF.Item1 * uAll.Item2, uAll.Item2 * uF.Item2);
            var st = F(10449 * (BigInteger)128 - 9880 * (BigInteger)66, 10449 * (BigInteger)128);
            Check("increments", inc == (1235, 684785664) && st == (14279, 27864) && F(110 * 66, 10449 * (BigInteger)128) == (605, 111456), $"{inc} {st}");
            Check("horizon lower bound sum", 5 * 9 + 58 * 27 + 43 == 1654);
        }

        // ---- affordability constants and crossing-cover comparisons
        {
            BigInteger S = BigInteger.Pow(10, 80);
            BigInteger Log(int zden) { BigInteger sum = 0, pw = S / zden; for (int j = 0; j < 100; j++) { sum += pw / (2 * j + 1); pw /= zden * zden; } return 2 * sum; }
            BigInteger l2 = Log(3), l3 = Log(2);   // z=1/3 gives log 2, z=1/2 gives log 3
            BigInteger p = 357638239, q = 225644606, Pp = 630138897, Q = 397573379;
            BigInteger M0 = 2075 * (BigInteger.One << 60);
            BigInteger tn = 3607 * BigInteger.Pow(10, 12), td = 15000 * M0;
            var g = BigInteger.GreatestCommonDivisor(tn, td);
            Check("tau fraction", tn / g == 56359375 && td / g == BigInteger.Parse("560698153607626752"));
            Check("determinant and enclosure of log2(3)", Pp * q - p * Q == 1 && p * l2 < q * l3 && Q * l3 < Pp * l2);
            BigInteger eta = Pp * l2 - Q * l3, d0 = (q + 15 * Q) * l3 - (p + 15 * Pp) * l2, tau = tn * S / td;
            Check("0 < delta0 < tau < eta", d0 > 0 && d0 < tau && tau < eta, $"eta~{(double)eta / (double)S:E10} d0~{(double)d0 / (double)S:E10} tau~{(double)tau / (double)S:E10}");
            Check("B+1 = q+15Q", q + 15 * Q == 6189245291L);
            Check("crossing-cover integer comparisons", BigInteger.Pow(3, 17) < BigInteger.Pow(2, 27) && BigInteger.Pow(8, 27) * BigInteger.Pow(100, 17) < BigInteger.Pow(3, 27) * BigInteger.Pow(5, 17) * BigInteger.Pow(97, 17) && 10 * BigInteger.Pow(97, 76) < BigInteger.Pow(100, 76) && 6189245291L / 76 == 81437438L);
        }

        // ---- listed family rows
        {
            var data = args[0];
            string Walk(ref BigInteger x, int len) { var c = new char[len]; for (int i = 0; i < len; i++) { c[i] = x.IsEven ? '0' : '1'; x = TB(x); } return new string(c); }
            bool Above(string w) { int a = 0; for (int i = 0; i < w.Length; i++) { if (w[i] == '1') a++; if (!(BigInteger.Pow(3, a) > (BigInteger.One << (i + 1)))) return false; } return true; }

            var rows = File.ReadAllLines(Path.Combine(data, "six_even_rows.csv")).Skip(1).Where(l => l.Length > 0).Select(l => l.Split(',')).ToList();
            int fails = 0, stars = 0, above = 0; var res9 = new HashSet<long>();
            foreach (var r in rows)
            {
                BigInteger D = BigInteger.Parse(r[0]), n0 = BigInteger.Parse(r[1]), m0 = BigInteger.Parse(r[2]);
                int L = int.Parse(r[3]); string v = r[4]; bool star = r[5] == "1"; if (star) stars++;
                BigInteger step = 19683 * (BigInteger.One << L), mstep = BigInteger.One << (L + 14);
                bool ok = v.Length == 20 && v.Count(c => c == '0') == 6;
                for (int h = 0; h < 3 && ok; h++)
                {
                    BigInteger n = n0 + step * h, m = m0 + mstep * h, a = n, b = m;
                    var wn = Walk(ref a, 6); var wm = Walk(ref b, 20);
                    if (wn != "111101" || wm != v || a != b || !(m > 0 && m < n) || 19683 * m != 16384 * n - D) ok = false;
                }
                if (n0 % 128 != 111 || !R81.Contains((int)(n0 % 81))) ok = false;
                var y = (UInt128)n0; for (int i = 0; i < 6; i++) y = T(y);
                if (MinBudget(y, (UInt128)n0, 6) != 6) ok = false;
                if ((n0 % 3 == 0) != star) ok = false;
                BigInteger x = n0; var pre = Walk(ref x, L); if (star) { if (Above(pre)) above++; res9.Add((long)(n0 % 19683)); }
                if (!ok) { fails++; Console.WriteLine($"   six-even row D={D} fails"); }
            }
            Check("48 six-even rows", rows.Count == 48 && fails == 0 && stars == 43 && above == 43 && res9.Count == 43, $"rows {rows.Count}, failures {fails}, starred {stars}, coefficient>1 {above}, distinct ternary {res9.Count}");

            var comp = File.ReadAllLines(Path.Combine(data, "complement_rows.csv")).Skip(1).Where(l => l.Length > 0).Select(l => l.Split(',')).ToList();
            var ra = comp.Where(r => r[0] == "a").ToList(); var rb = comp.Where(r => r[0] == "b").ToList(); var rc = comp.Where(r => r[0] == "c").ToList();
            int ef = 0;
            foreach (var r in ra)
            {
                BigInteger D = BigInteger.Parse(r[1]), a0 = BigInteger.Parse(r[2]), b0 = BigInteger.Parse(r[3]), q = BigInteger.Parse(r[4]);
                var w = r[5]; BigInteger x = a0, y = a0, z = b0; var pre = Walk(ref x, 12); Walk(ref y, 6); Walk(ref z, 15);
                if (pre != w || !Above(w) || y != z || 729 * b0 != 512 * a0 - D || !(b0 < a0) || a0 % 3 != 0) ef++;
                BigInteger a1 = a0 + q * 4096, b1 = b0 + 512 * q * 4096 / 729, c = a1, d = b1; Walk(ref c, 6); Walk(ref d, 15); if (c != d) ef++;
            }
            int bq = 2187;
            foreach (var r in rb)
            {
                BigInteger D = BigInteger.Parse(r[1]), a0 = BigInteger.Parse(r[2]), b0 = BigInteger.Parse(r[3]); int L = int.Parse(r[4]);
                var w = r[5]; BigInteger x = a0, y = a0, z = b0; var pre = Walk(ref x, L); Walk(ref y, 6); Walk(ref z, 17);
                if (pre != w || w.Length != L || !Above(w) || y != z || bq * b0 != 2048 * a0 - D || !(b0 < a0) || a0 % 3 != 0) ef++;
                var yy = (UInt128)a0; for (int i = 0; i < 6; i++) yy = T(yy); if (MinBudget(yy, (UInt128)a0, 5) != 5) ef++;
            }
            foreach (var r in rc)
            {
                BigInteger a0 = BigInteger.Parse(r[2]), b0 = BigInteger.Parse(r[3]); var w = r[5];
                BigInteger x = a0, z = b0; var pre = Walk(ref x, 14); Walk(ref z, 1);
                if (pre != w || !Above(w) || x != z || !(b0 < a0) || a0 % 81 != 0) ef++;
                var yy = (UInt128)a0; for (int i = 0; i < 6; i++) yy = T(yy); if (Reach(yy, (UInt128)a0, 5)) ef++;
            }
            Check("complementary refinements: 3 + 12 + 6 rows", ra.Count == 3 && rb.Count == 12 && rc.Count == 6 && ef == 0, $"rows {ra.Count}/{rb.Count}/{rc.Count}, failures {ef}");
        }
        Console.WriteLine($"TOTAL failures {bad}");
    }
}
