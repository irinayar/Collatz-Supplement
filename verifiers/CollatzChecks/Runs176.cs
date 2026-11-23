using System;
// K176/K175 run-level facts on all runs of all genuine returns: (A) runs with s>=2,e=2: psi <= 6(1/a-1/b) and b/a >= 9/8; (B) single-input runs (s=1): psi=0 and b<a.
public class Runs176 {
  public static void Run(string[] args) {
    foreach (string sn in args) {
      long n = long.Parse(sn) | 1; long H = (4 * n - 2) / 3; double kappa = 1 - 4.0 / (3.0 * n + 1);
      long expRuns = 0, badPsi = 0, badGrow = 0, single = 0, badSingle = 0; double minGrow = 1e9, maxRatio = 0;
      for (long u = n; u <= H; u += 2) {
        long x = u; int s = 0; long a = u; bool r = false; int steps = 0; var rl = new System.Collections.Generic.List<(long a, int s, int e, long b)>();
        while (steps < 100000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev; s++; x = t; steps++;
          if (ev >= 2) { rl.Add((a, s, ev, x)); s = 0; a = x; }
          if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
        if (!r) continue;
        foreach (var q in rl) {
          double z = Math.Pow(2.0 / 3, q.s), f = 1 - z, delta = f / q.a; double psi = Math.Max(0.0, kappa * delta + 1.0 / q.a - 1.0 / q.b);
          if (q.s >= 2 && q.e == 2) { expRuns++; double fl = 1.0 / q.a - 1.0 / q.b; if (psi > 6 * fl * (1 + 1e-12) + 1e-18) badPsi++; double g = (double)q.b / q.a; if (g < minGrow) minGrow = g; if (g < 9.0 / 8 * (1 - 1e-9)) badGrow++; if (fl > 0) maxRatio = Math.Max(maxRatio, psi / fl); }
          if (q.s == 1) { single++; if (psi != 0 || !(q.b < q.a)) badSingle++; }
        }
      }
      Console.WriteLine($"n={n}: expanding runs (s>=2,e=2)={expRuns}: psi<=6f failures={badPsi}, b/a<9/8 failures={badGrow}, min b/a={minGrow:F4}, max psi/f={maxRatio:F3}; single-input runs={single}: failures(psi!=0 or b>=a)={badSingle}");
    }
  }
}
