using System;
// Tail counts of the total phase Q_g over all genuine first returns at one threshold: #(Q_g > T) for T = 1..12, and fitted exponential slope.
public class PhaseTail {
  public static void Run(string[] args) {
    foreach (string sn in args) {
      long n = long.Parse(sn) | 1; long H = (4 * n - 2) / 3; long ret = 0; long[] cnt = new long[14];
      for (long u = n; u <= H; u += 2) {
        long x = u; double Z = 1.0, Q = 0.0; bool r = false; int steps = 0;
        while (steps < 100000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev;
          Q += Z / 3.0; Z = Z * Math.Pow(2, ev) / 3.0; x = t; steps++;
          if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
        if (!r) continue; ret++; for (int T = 1; T <= 13; T++) if (Q > T) cnt[T]++;
      }
      string line = $"n={n} returns={ret}: #(Q>T) for T=1..12:";
      for (int T = 1; T <= 12; T++) line += $" {T}:{cnt[T]}";
      Console.WriteLine(line);
      string sl = "  local slope -ln ratio per unit T:"; for (int T = 3; T <= 10; T++) if (cnt[T + 1] > 0 && cnt[T] > 0) sl += $" {T}->{T + 1}:{Math.Log((double)cnt[T] / cnt[T + 1]):F2}";
      Console.WriteLine(sl);
    }
  }
}
