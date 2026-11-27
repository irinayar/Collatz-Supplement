// Minimal positive origin H_k(x,r) of a path ending at x with k even-input and r odd-input steps, by exact inverse recursion
// (even inverse y -> 2y; odd inverse y -> (2y-1)/3 when y = 2 mod 3), and by independent enumeration of the positions.
using System;
using System.Collections.Generic;
using System.Numerics;

class P
{
    static readonly Dictionary<(BigInteger, int, int), BigInteger?> memo = new();
    static BigInteger? H(BigInteger x, int k, int r)
    {
        if (k == 0 && r == 0) return x;
        if (memo.TryGetValue((x, k, r), out var c)) return c;
        BigInteger? best = null;
        if (k > 0) best = H(2 * x, k - 1, r);
        if (r > 0 && x % 3 == 2) { var o = H((2 * x - 1) / 3, k, r - 1); if (o != null && (best == null || o < best)) best = o; }
        memo[(x, k, r)] = best; return best;
    }
    static void Main()
    {
        int bad = 0, checks = 0;
        for (int t = 0; t <= 5; t++)
            for (int k = 3; k <= 40; k++)
            {
                BigInteger p = BigInteger.Pow(2, k);
                // x = 4 + 81t
                if (k >= 4)
                {
                    checks += 2;
                    if (H(4 + 81 * t, k, 3) != 17 * p / 16 + 24 * p * t) bad++;
                    if (H(4 + 81 * t, k, 4) != 11 * p / 16 + 16 * p * t) bad++;
                }
                checks += 2;
                if (H(5 + 81 * t, k, 3) != 11 * p / 8 + 24 * p * t) bad++;
                if (H(5 + 81 * t, k, 4) != 7 * p / 8 + 16 * p * t) bad++;
            }
        Console.WriteLine($"recursion checks={checks} mismatches={bad}");
        // largest correction over feasible position vectors e1<=e2<=e3<=e4<=40, found by direct replay
        foreach (var (x, num, den) in new[] { (4, 133, 1296), (5, 73, 648) })
        {
            double max = 0; string at = ""; int exceed = 0;
            for (int a = 0; a <= 40; a++) for (int b = a; b <= 40; b++) for (int c = b; c <= 40; c++) for (int d = c; d <= 40; d++)
            {
                int[] e = { a, b, c, d }; BigInteger y = x; int done = 0; bool ok = true;
                foreach (int pos in e) { y <<= pos - done; done = pos; if (y % 3 != 2) { ok = false; break; } y = (2 * y - 1) / 3; }
                if (!ok) continue;
                // exact correction times 81*2^40
                BigInteger corr = 8 * BigInteger.Pow(2, 40 - a) + 12 * BigInteger.Pow(2, 40 - b) + 18 * BigInteger.Pow(2, 40 - c) + 27 * BigInteger.Pow(2, 40 - d);
                BigInteger lhs = corr * den, rhs = (BigInteger)num * 81 * BigInteger.Pow(2, 40);
                if (lhs > rhs) exceed++;
                double v = (double)corr / (81.0 * Math.Pow(2, 40));
                if (v > max) { max = v; at = $"({a},{b},{c},{d})"; }
            }
            Console.WriteLine($"x={x}: feasible vectors exceeding {num}/{den}: {exceed}; largest {max:F10} = {(double)num / den:F10} at {at}");
        }
    }
}
