using System;
// Per-return signed budget J_p = sum over ALL runs of a*psi (psi=[kappa*delta+1/a-1/b]_+), number of runs r_p and of psi>0 runs, for genuine returns.
// Mode "range N": all odd n in [3,N]; mode "single n..." : listed thresholds.
public class Census { static double maxQ = 0; static long q10 = 0;
  static void Run(long n, ref double maxJ, ref long maxJn, ref long maxJu, ref int maxR, ref int maxPos, ref long ret, ref long over10, ref long over20) {
    long H = (4 * n - 2) / 3; double kappa = 1 - 4.0 / (3.0 * n + 1);
    for (long u = n | 1; u <= H; u += 2) {
      long x = u; int s = 0; long a = u; bool r = false; int steps = 0; double J = 0; int runs = 0, pos = 0; double Zq = 1.0, Qg = 0.0;
      while (steps < 100000) {
        long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev; Qg += Zq / 3.0; Zq = Zq * Math.Pow(2, ev) / 3.0; s++; x = t; steps++;
        if (ev >= 2) { double z = Math.Pow(2.0 / 3, s), f = 1 - z, delta = f / a; double psi = Math.Max(0.0, kappa * delta + 1.0 / a - 1.0 / x); runs++; if (psi > 0) { pos++; J += a * psi; } s = 0; a = x; }
        if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
      if (!r) continue; ret++; if (Qg > maxQ) { maxQ = Qg; } if (Qg > 10) q10++;
      if (J > maxJ) { maxJ = J; maxJn = n; maxJu = u; } if (runs > maxR) maxR = runs; if (pos > maxPos) maxPos = pos; if (J > 10) over10++; if (J > 20) over20++;
    }
  }
  public static void Run(string[] a) {
    double maxJ = 0; long maxJn = 0, maxJu = 0, ret = 0, o10 = 0, o20 = 0; int maxR = 0, maxPos = 0;
    if (a[0] == "range") { long N = long.Parse(a[1]); for (long n = 3; n <= N; n += 2) Run(n, ref maxJ, ref maxJn, ref maxJu, ref maxR, ref maxPos, ref ret, ref o10, ref o20);
      Console.WriteLine($"range n<={N}: returns={ret} max J_p={maxJ:F4} at n={maxJn},u={maxJu}; max runs per return={maxR}; max psi>0 runs per return={maxPos}; returns with J>10: {o10}, J>20: {o20}"); }
    else for (int i = 1; i < a.Length; i++) { maxJ = 0; maxR = 0; maxPos = 0; ret = 0; o10 = 0; o20 = 0; long n = long.Parse(a[i]); Run(n, ref maxJ, ref maxJn, ref maxJu, ref maxR, ref maxPos, ref ret, ref o10, ref o20);
      Console.WriteLine($"n={n}: max Q_g={maxQ:F4}, Q_g>10: {q10}; returns={ret} max J_p={maxJ:F4} (u={maxJu}); max runs={maxR}; max psi>0 runs={maxPos}; J>10: {o10}, J>20: {o20}"); }
  }
}
