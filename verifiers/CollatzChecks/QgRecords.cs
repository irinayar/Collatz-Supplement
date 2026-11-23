using System;
using System.Collections.Generic;
// Record Q_g by return length g (odd steps) for all genuine first returns, odd n in [3,NMAX]; print max Q_g per g bucket and the 10 largest overall.
public class QgRecords {
  public static void Run(string[] a) {
    long NMAX = long.Parse(a[0]); int GM = 400;
    double[] mq = new double[GM + 1]; long[] mn = new long[GM + 1], mu = new long[GM + 1], cnt = new long[GM + 1];
    var top = new List<(double q, long n, long u, int g)>();
    for (long n = 3; n <= NMAX; n += 2) {
      long H = (4 * n - 2) / 3;
      for (long u = n | 1; u <= H; u += 2) {
        long x = u; double Z = 1.0, Q = 0.0; bool ret = false; int steps = 0;
        while (steps < 200000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev;
          Q += Z / 3.0; Z = Z * Math.Pow(2, ev) / 3.0; x = t; steps++;
          if (x < n) break; if (x <= H) { ret = true; break; } if (x > (1L << 60)) break; }
        if (!ret) continue;
        int g = Math.Min(steps, GM); cnt[g]++;
        if (Q > mq[g]) { mq[g] = Q; mn[g] = n; mu[g] = u; }
        if (Q > 5.2) { top.Add((Q, n, u, steps)); }
      }
    }
    top.Sort((p, q) => q.q.CompareTo(p.q));
    Console.WriteLine("largest Q_g overall (Q>5.2): count=" + top.Count);
    for (int i = 0; i < Math.Min(10, top.Count); i++) Console.WriteLine($"  Q={top[i].q:F4} n={top[i].n} u={top[i].u} g={top[i].g}");
    Console.WriteLine("max Q_g by return length g (selected g):");
    foreach (int g in new int[] { 2, 5, 10, 15, 20, 25, 30, 40, 50, 60, 80, 100, 150, 200, 300, 400 }) Console.WriteLine($"  g={g}: returns={cnt[g]} maxQ={mq[g]:F4} (n={mn[g]}, u={mu[g]})");
    int gmaxSeen = 0; for (int g = 0; g <= GM; g++) if (cnt[g] > 0) gmaxSeen = g; Console.WriteLine("longest return seen (capped at 400): g=" + gmaxSeen);
  }
}
