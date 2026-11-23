using System;
// Telescoped bound of K176 on every genuine return: J_p = sum a*psi (all runs); Tbound_p = u*[6(1/u - 1/w) + sum tau], tau=[psi-6f]_+, f=1/a-1/b; report distributions and how much of the toll comes from single-input runs (s=1).
public class Toll {
  public static void Run(string[] args) {
    foreach (string sn in args) {
      long n = long.Parse(sn) | 1; long H = (4 * n - 2) / 3; double kappa = 1 - 4.0 / (3.0 * n + 1); long ret = 0, over56J = 0, over56T = 0, over28T = 0; double maxJ = 0, maxT = 0, sumJ = 0, sumT = 0, tauSingle = 0, tauOther = 0;
      for (long u = n; u <= H; u += 2) {
        long x = u; int s = 0; long a = u; bool r = false; int steps = 0; double J = 0, tau = 0, tauS = 0, tauO = 0;
        while (steps < 100000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev; s++; x = t; steps++;
          if (ev >= 2) { double z = Math.Pow(2.0 / 3, s), f = 1 - z, delta = f / a; double psi = Math.Max(0.0, kappa * delta + 1.0 / a - 1.0 / x); double fl = 1.0 / a - 1.0 / x; double tt = Math.Max(0.0, psi - 6 * fl); J += a * psi; double contrib = u * tt; if (s == 1) tauS += contrib; else tauO += contrib; s = 0; a = x; }
          if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
        if (!r) continue; ret++; double Tb = u * 6 * (1.0 / u - 1.0 / x) + tauS + tauO; // x = w (final output)
        sumJ += J; sumT += Tb; tauSingle += tauS; tauOther += tauO; if (J > maxJ) maxJ = J; if (Tb > maxT) maxT = Tb; if (J > 56) over56J++; if (Tb > 56) over56T++; if (Tb > 28) over28T++;
      }
      Console.WriteLine($"n={n}: returns={ret}; J_p mean={sumJ / ret:F4} max={maxJ:F2} (>56: {over56J}); telescoped bound mean={sumT / ret:F4} max={maxT:F2} (>28: {over28T}, >56: {over56T}); mean toll from single-input runs={tauSingle / ret:F4}, from other runs={tauOther / ret:F4}");
    }
  }
}
