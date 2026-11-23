using System;
// Check K174: for every maximal run (s odd inputs from a, last exponent e>=2, output b): b=[3^s(a+1)-2^s]/2^(s-1+e), b<=(a+f)/(2z), a*psi<=[2-3z]_+,
// psi=[kappa*delta+1/a-1/b]_+, delta=f/a, f=1-z, z=(2/3)^s, kappa=1-4/(3n+1). All runs of all genuine first returns from [n,H].
public class Runs174 {
  public static void Run(string[] args) {
    foreach (string sn in args) {
      long n = long.Parse(sn) | 1; long H = (4 * n - 2) / 3; long runs = 0, badB = 0, badBound = 0, badPsi = 0, pos = 0; double maxRatio = 0; double kappa = 1 - 4.0 / (3.0 * n + 1);
      for (long u = n; u <= H; u += 2) {
        long x = u; int s = 0; long a = u; bool ret = false; int steps = 0; var rl = new System.Collections.Generic.List<(long a, int s, int e, long b)>();
        while (steps < 100000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev; s++; x = t; steps++;
          if (ev >= 2) { rl.Add((a, s, ev, x)); s = 0; a = x; }
          if (x < n) break; if (x <= H) { ret = true; break; } if (x > (1L << 60)) break; }
        if (!ret) continue;
        foreach (var r in rl) {
          runs++; double z = Math.Pow(2.0 / 3, r.s), f = 1 - z, delta = f / r.a;
          double bform = (Math.Pow(3, r.s) * (r.a + 1.0) - Math.Pow(2, r.s)) / Math.Pow(2, r.s - 1 + r.e);
          if (Math.Abs(bform - r.b) > 1e-6 * r.b) badB++;
          if (r.b > (r.a + f) / (2 * z) * (1 + 1e-12)) badBound++;
          double psi = Math.Max(0.0, kappa * delta + 1.0 / r.a - 1.0 / r.b); double lhs = r.a * psi, rhs = Math.Max(0.0, 2 - 3 * z);
          if (lhs > rhs * (1 + 1e-12) + 1e-12) badPsi++; if (psi > 0) { pos++; if (rhs > 0) maxRatio = Math.Max(maxRatio, lhs / rhs); }
        }
      }
      Console.WriteLine($"n={n} runs={runs} psi>0 runs={pos} failures: b-formula={badB}, b<=(a+f)/(2z)={badBound}, a*psi<=[2-3z]+={badPsi}; max (a*psi)/(2-3z) over psi>0, s>=2 = {maxRatio:F4}");
    }
  }
}
