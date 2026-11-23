using System;
// Exhaustive: for every odd n in [3,NMAX] and every odd source u in [n,H], H=floor((4n-2)/3), follow the odd map F until the output is <n (discard)
// or in [n,H] (genuine first return, all proper outputs > H). Compute total phase Q_g = sum_{i<g} 2^{E_i}/3^{i+1} (double), record maxima.
public class QgScan {
  public static void Run(string[] a) {
    long NMAX = long.Parse(a[0]);
    double gmax = 0; long gn = 0, gu = 0; long returns = 0, over4 = 0, over5 = 0, over6 = 0, overflow = 0;
    double[] binMax = new double[40]; // by floor(log2 n)
    long[] binRet = new long[40];
    for (long n = 3; n <= NMAX; n += 2) {
      long H = (4 * n - 2) / 3;
      int bin = 63 - System.Numerics.BitOperations.LeadingZeroCount((ulong)n);
      for (long u = n | 1; u <= H; u += 2) {
        long x = u; double Z = 1.0, Q = 0.0; bool ret = false; int steps = 0;
        while (steps < 200000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev;
          Q += Z / 3.0; Z = Z * Math.Pow(2, ev) / 3.0; x = t; steps++;
          if (x < n) break;
          if (x <= H) { ret = true; break; }
          if (x > (1L << 60)) { overflow++; break; }
        }
        if (!ret) continue;
        returns++; binRet[bin]++;
        if (Q > binMax[bin]) binMax[bin] = Q;
        if (Q > gmax) { gmax = Q; gn = n; gu = u; }
        if (Q > 4) over4++; if (Q > 5) over5++; if (Q > 6) over6++;
      }
    }
    Console.WriteLine($"NMAX={NMAX} returns={returns} overflow={overflow} global max Q_g={gmax:F4} at n={gn}, u={gu}; counts Q>4:{over4} Q>5:{over5} Q>6:{over6}");
    for (int b = 1; b < 40; b++) if (binRet[b] > 0) Console.WriteLine($"  n in [2^{b},2^{b+1}): returns={binRet[b]} max Q_g={binMax[b]:F4}");
  }
}
