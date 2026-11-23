using System;
// Stopping code C_t: weight S_t = sum 2^-E and word COUNT |C_t| (total, and by total exponent E) for minimal admissible prefixes with P_m > t (Q rounded up to bins).
// Then at a threshold n: N(Q>t) <= sum_w ((H-n)/2^(E+1) + 1) = (H-n)/2 * S_t + |C_t| (counting bound).
public class StopDp {
  public static void Run(string[] args) {
    double bin = 0.02; int EMAX = 14; double lg3 = Math.Log(3, 2);
    foreach (string ts in args) {
      double t = double.Parse(ts); int nb = (int)Math.Ceiling(t / bin) + 1; int MAXM = 160; int EM = 270;
      var w = new double[EM, nb]; var c = new double[EM, nb]; double[] Sw = new double[EM], Sc = new double[EM];
      double P1 = 1.0 / 3 + 2.0 / 9; int b1 = (int)Math.Ceiling(P1 / bin); w[1, b1] = 0.5; c[1, b1] = 1;
      for (int m = 1; m < MAXM; m++) {
        var w2 = new double[EM, nb]; var c2 = new double[EM, nb]; bool any = false;
        for (int E = 1; E < Math.Min(EM - 20, (int)(m * lg3) + 1); E++) for (int b = 0; b < nb; b++) {
          double ww = w[E, b]; if (ww == 0) continue; double cc = c[E, b]; double Pm = b * bin;
          for (int e = 1; e <= EMAX; e++) {
            int E2 = E + e; if (E2 >= EM) break; if (E2 >= (m + 1) * lg3) break; // 2^E2 < 3^(m+1)
            double Pn = Pm + Math.Pow(2, E2) / Math.Pow(3, m + 2); double wn = ww * Math.Pow(2, -e);
            if (Pn > t) { Sw[E2] += wn; Sc[E2] += cc; } else { int bn = (int)Math.Ceiling(Pn / bin); if (bn < nb) { w2[E2, bn] += wn; c2[E2, bn] += cc; any = true; } else { Sw[E2] += wn; Sc[E2] += cc; } }
          }
        }
        w = w2; c = c2; if (!any) break;
      }
      double S = 0, C = 0; for (int E = 0; E < EM; E++) { S += Sw[E]; C += Sc[E]; }
      double n71 = Math.Pow(2, 71) * 3 / 2 + 1; double span = (4 * n71 - 2) / 3 - n71; // band width H-n at n=3*2^70+3
      double bound = span / 2 * S + C;
      // weight and count by E ranges
      double wlow = 0, whigh = 0, clow = 0, chigh = 0; for (int E = 0; E < EM; E++) { if (E < 70) { wlow += Sw[E]; clow += Sc[E]; } else { whigh += Sw[E]; chigh += Sc[E]; } }
      Console.WriteLine($"t={t}: S_t={S:E3}, |C_t|={C:E3}; E<70: weight {wlow:E2}, words {clow:E2}; E>=70: weight {whigh:E2}, words {chigh:E2}; at n=3*2^70+3: bound N(Q>t) <= {bound:E3}  (= {span / 2 * S:E2} + {C:E2}), as a fraction of n: {bound / n71:E2}");
    }
  }
}
