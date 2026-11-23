using System;
// K181 / aggregate-compensation packet checks on ALL runs of ALL genuine first returns at one threshold n (family = every source, core = empty):
// kappa=(n-1)/(n+1), delta=(1-(2/3)^s)/a, f=1/a-1/b, t=kappa*delta+f.
//  (i) f<=delta; telescoping sum f = sum_p (1/u-1/w); exact identity kappa*W_U = R_U + D_F + sum_{i not in U} f with U={t<0};
//  (ii) criterion (14): [-f-delta/15]_+ > 0 <=> lambda > (1+beta/a)(1+beta/15), lambda = 2^(e-1) z; and (15) for single-input runs.
public class K181Checks {
  public static void Run(string[] args) {
    foreach (string sn in args) {
      long n = long.Parse(sn) | 1; long H = (4 * n - 2) / 3; double kappa = (n - 1.0) / (n + 1.0), kk = 1 - 4.0 / (3.0 * n + 1);
      long runs = 0, badF = 0, ret = 0, mism = 0, pos = 0, s1 = 0, bad15 = 0; double W = 0, sumF = 0, D = 0, WU = 0, RU = 0, offF = 0, Nall = 0, credit = 0;
      for (long u = n; u <= H; u += 2) {
        long x = u; int s = 0; long a = u; bool r = false; int steps = 0; var rl = new System.Collections.Generic.List<(long a, int s, long b, int e)>();
        while (steps < 100000) {
          long t = 3 * x + 1; int ev = System.Numerics.BitOperations.TrailingZeroCount((ulong)t); t >>= ev; s++; x = t; steps++;
          if (ev >= 2) { rl.Add((a, s, x, ev)); s = 0; a = x; }
          if (x < n) break; if (x <= H) { r = true; break; } if (x > (1L << 60)) break; }
        if (!r) continue; ret++; D += 1.0 / x - 1.0 / u;
        foreach (var q in rl) {
          runs++; double z = Math.Pow(2.0 / 3, q.s), beta = 1 - z, delta = beta / q.a, f = 1.0 / q.a - 1.0 / q.b, t = kappa * delta + f;
          if (f > delta * (1 + 1e-12)) badF++; W += delta; sumF += f;
          if (t < 0) { WU += delta; RU += t; Nall += -t; } else offF += f;
          double cr = Math.Max(0.0, -f - delta / 15); credit += cr; if (cr > 0) pos++;
          double lambda = Math.Pow(2, q.e - 1) * z; if ((cr > 0) != (lambda > (1 + beta / q.a) * (1 + beta / 15))) mism++;
          if (q.s == 1) { s1++; if (cr < (kk - 1.0 / 15) * delta * (1 - 1e-12)) bad15++; }
        }
      }
      double lhs = kappa * WU, rhs = RU + D + offF; double rel = Math.Abs(lhs - rhs) / Math.Max(Math.Abs(lhs), 1e-300);
      Console.WriteLine($"n={n}: returns={ret} runs={runs}; f<=delta failures={badF}; sum f={sumF:E4} vs -D_F={-D:E4}; identity rel err {rel:E1}; W={W:E4} N_all={Nall:E4} credit={credit:E4} D_F={D:E4}; credit>0 runs {100.0 * pos / runs:F1}%, (14) mismatches={mism}, single-input (15) violations={bad15}/{s1}");
    }
  }
}
