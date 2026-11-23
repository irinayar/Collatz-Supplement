using System;
// Full-band census (all odd sources u in [n,H]) of the last exponent and arrival residue mod 3 of genuine first returns, for each given odd n.
public class LastExp {
  public static void Run(string[] a) {
    foreach (string s in a) {
      long n = long.Parse(s); long H = (4 * n - 2) / 3; long ret = 0, w1 = 0; long[] le = new long[12];
      for (long u = n | 1; u <= H; u += 2) {
        long x = u; int last = 0; bool r = false; int steps = 0;
        while (steps < 200000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev; last = ev; x = t; steps++;
          if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
        if (!r) continue; ret++; if (x % 3 == 1) w1++; le[Math.Min(last, 11)]++;
      }
      string line = $"n={n} returns={ret} arrival mod3=1 share={(double)w1 / ret:F4}  last e:";
      for (int e = 2; e <= 6; e++) line += $" e={e}:{(double)le[e] / ret:F3}";
      Console.WriteLine(line);
    }
  }
}
