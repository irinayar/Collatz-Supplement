using System;
// All-source charge: for every genuine first return from [n,H] (every odd source u, NOT only least sources of distinct words) compute
// rho = G*Phi(w)/Phi(u), G=prod(1+1/(3x_i)) over odd inputs, Phi(x)=1+5/x; report sum of (rho-1)_+ , sum of (rho-1) over rho>1, and max single charge.
public class AllSource {
  public static void Run(string[] a) {
    foreach (string s in a) {
      long n = long.Parse(s) | 1; long H = (4 * n - 2) / 3; long ret = 0, pos = 0; double sumPos = 0, maxb = 0, sumQ = 0;
      for (long u = n; u <= H; u += 2) {
        long x = u; double G = 1.0; bool r = false; int steps = 0; double Z = 1.0, Q = 0.0;
        while (steps < 100000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev;
          G *= 1.0 + 1.0 / (3.0 * x); Q += Z / 3.0; Z = Z * Math.Pow(2, ev) / 3.0; x = t; steps++;
          if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
        if (!r) continue; ret++;
        double rho = G * (1 + 5.0 / x) / (1 + 5.0 / u); double b = rho - 1; sumQ += Q / u;
        if (b > 0) { pos++; sumPos += b; if (b > maxb) maxb = b; }
      }
      Console.WriteLine($"n={n} returns={ret} positive-charge returns={pos} sum(rho-1)+ over ALL sources={sumPos:F5} max single={maxb:E3} sum Q_g/u={sumQ:F5}  (21/125=0.168)");
    }
  }
}
