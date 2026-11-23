using System;
using System.Collections.Generic;
// Same-depth same-anchor collisions among genuine first returns from [n,H]: cells (x_i, i); check remaining phase c=Q_g-Q_i equal, sources 3 mod 4, phase gaps multiples of 4.
public class Collision {
  public static void Run(string[] a) {
    foreach (string s in a) {
      long n = long.Parse(s) | 1; long H = (4 * n - 2) / 3;
      var d = new Dictionary<(long, int), List<(long u, double q, double c)>>();
      long ret = 0;
      for (long u = n; u <= H; u += 2) {
        long x = u; double Z = 1.0, Q = 0.0; var xs = new List<long>(); var qs = new List<double>(); bool r = false; int steps = 0;
        while (steps < 100000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev;
          xs.Add(x); qs.Add(Q); Q += Z / 3.0; Z = Z * Math.Pow(2, ev) / 3.0; x = t; steps++;
          if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
        if (!r) continue; ret++;
        for (int i = 1; i < xs.Count; i++) { var k = (xs[i], i); if (!d.TryGetValue(k, out var l)) { l = new List<(long, double, double)>(); d[k] = l; } l.Add((u, qs[i], Q - qs[i])); }
      }
      long cells = d.Count, coll = 0, maxm = 0, badc = 0, bad4 = 0, badgap = 0; double mingap = 1e18;
      foreach (var kv in d) { var l = kv.Value; if (l.Count < 2) continue; coll++; maxm = Math.Max(maxm, l.Count);
        l.Sort((p, q) => p.q.CompareTo(q.q));
        foreach (var e in l) { if (Math.Abs(e.c - l[0].c) > 1e-9) badc++; if (e.u % 4 != 3) bad4++; }
        for (int i = 1; i < l.Count; i++) { double gap = l[i].q - l[i - 1].q; mingap = Math.Min(mingap, gap); if (gap < 4 - 1e-9 || Math.Abs(gap / 4 - Math.Round(gap / 4)) > 1e-6) badgap++; } }
      Console.WriteLine($"n={n} returns={ret} cells={cells} collision cells={coll} max mult={maxm} min phase gap={(coll > 0 ? mingap.ToString("F3") : "-")} violations: remaining-phase={badc}, not3mod4={bad4}, gap={badgap}");
    }
  }
}
