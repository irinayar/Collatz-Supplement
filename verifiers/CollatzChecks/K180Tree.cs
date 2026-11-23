using System;
using System.Collections.Generic;
using System.Numerics;
// K180 residue tree: alphabet of six balanced four-block words (B values for 2233,2323,2332,3223,3232,3322), A=3^24, D=2^38.
// For every code c_0..c_(N-1): U_(j+1) = A U_j + D^j B_(c_j); residue a = (D^N - U_N)(A^N)^(-1) mod 2 D^N. Reports distinctness, the minimum and its code, and the stated inequality.
public class K180Tree {
  static BigInteger[] B = { BigInteger.Parse("1806869652709"), BigInteger.Parse("1754626876645"), BigInteger.Parse("1705704514789"), BigInteger.Parse("1705037054053"), BigInteger.Parse("1656114692197"), BigInteger.Parse("1609676669029") };
  static BigInteger A = BigInteger.Pow(3, 24), D = BigInteger.Pow(2, 38);
  static BigInteger[] Dp; static int N; static BigInteger mod, inv, DN; static BigInteger best = BigInteger.Zero; static int[] bestCode; static int[] cur; static HashSet<BigInteger> seen = new HashSet<BigInteger>(); static long leaves = 0;
  static void Rec(int j, BigInteger U) {
    if (j == N) { BigInteger r = (((DN - U) % mod) + mod) % mod; r = (r * inv) % mod; leaves++; seen.Add(r); if (best.IsZero || r < best) { best = r; bestCode = (int[])cur.Clone(); } return; }
    for (int c = 0; c < 6; c++) { cur[j] = c; Rec(j + 1, A * U + Dp[j] * B[c]); }
  }
  public static void Run(string[] args) {
    N = int.Parse(args[0]); mod = 2 * BigInteger.Pow(D, N); DN = BigInteger.Pow(D, N); Dp = new BigInteger[N + 1]; Dp[0] = 1; for (int j = 1; j <= N; j++) Dp[j] = Dp[j - 1] * D;
    BigInteger AN = BigInteger.Pow(A, N); inv = BigInteger.ModPow(AN % mod, mod / 2 - 1, mod); cur = new int[N];
    Rec(0, BigInteger.Zero);
    Console.WriteLine($"N={N}: leaves={leaves}, distinct residues={seen.Count}");
    Console.WriteLine($"minimum residue = {best} at code [{string.Join(", ", bestCode)}]");
    BigInteger lhs = 3 * 56 * best * 7551629537; BigInteger rhs = BigInteger.Parse("1814421282246") * (4 * (BigInteger.Pow(2, 272) - 1) + 1);
    Console.WriteLine($"3*56*m*7551629537 >= 1814421282246*(4(2^272-1)+1): {lhs >= rhs}");
  }
}
