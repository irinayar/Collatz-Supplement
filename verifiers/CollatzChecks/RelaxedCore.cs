using System;
using System.Collections.Generic;
// For genuine returns with total phase Q_g > QMIN at threshold n: compute the RELAXED core (n < 2^71 so P_* is undefined): proper run starts a (runs after the first)
// with (i) canonical block of floor(log2 a) shortcut steps ending strictly before the final output, (ii) block endpoint > a/64, (iii) Q_i > B and Q_g-Q_i > B (B=5.04).
public class RelaxedCore {
  public static void Run(string[] args) {
    long n = long.Parse(args[0]) | 1; double QMIN = double.Parse(args[1]); double B = 5.04; long H = (4 * n - 2) / 3; long found = 0, withCore = 0;
    for (long u = n; u <= H; u += 2) {
      var st = new List<long>(); var qAt = new List<double>(); var runStartIdx = new List<int>(); // shortcut states and phase before each odd input
      long x = u; double Z = 1.0, Q = 0.0; bool ret = false; int steps = 0; int runStartPos = 0; bool newRun = true; var starts = new List<(int pos, double q)>();
      st.Add(u); int shortcut = 0;
      while (steps < 100000) {
        long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t);
        if (newRun) { starts.Add((shortcut, Q)); newRun = false; }
        Q += Z / 3.0; Z = Z * Math.Pow(2, ev) / 3.0;
        // shortcut states: x -> (3x+1)/2 then halvings
        long y = (3 * x + 1) / 2; st.Add(y); shortcut++; for (int k = 1; k < ev; k++) { y /= 2; st.Add(y); shortcut++; }
        x = y; steps++; if (ev >= 2) newRun = true;
        if (x < n) break; if (x <= H) { ret = true; break; } if (x > (1L << 60)) break; }
      if (!ret || Q <= QMIN) continue; found++;
      int S = shortcut; int core = 0; double Wc = 0;
      for (int i = 1; i < starts.Count; i++) { int pos = starts[i].pos; long a = st[pos]; if (a <= H) continue; int j = 63 - System.Numerics.BitOperations.LeadingZeroCount((ulong)a);
        if (pos + j >= S) continue; if (!(st[pos + j] * 64.0 > a)) continue; double qi = starts[i].q; if (!(qi > B && Q - qi > B)) continue; core++; Wc += 1.0 / a; }
      if (core > 0) withCore++;
      Console.WriteLine($"u={u} Q_g={Q:F4} shortcut steps={S} odd transitions={steps} runs={starts.Count} relaxed core runs={core} core mass R={Wc:E3}");
    }
    Console.WriteLine($"n={n}: returns with Q_g>{QMIN}: {found}; with nonempty relaxed core: {withCore}");
  }
}
