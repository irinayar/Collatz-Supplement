// Check of the meeting families n = n0 + N h, m = m0 + M h with T^k(n) = T^l(m), 0 < m < n, T the shortcut map.
// For each row: positivity, m < n and M <= N, divisibility of the steps by 2^k and 2^l, both parity words,
// the common value for h = 0..7, and the identity 3^a N / 2^k = 3^b M / 2^l that gives every h >= 0.
using System;
using System.IO;
using System.Numerics;

class P
{
    static BigInteger T(BigInteger x) => x.IsEven ? x / 2 : (3 * x + 1) / 2;

    static int Main(string[] args)
    {
        var lines = File.ReadAllLines(args[0]);
        int rows = 0, bad = 0;
        for (int i = 1; i < lines.Length; i++)
        {
            if (lines[i].Trim().Length == 0) continue;
            var f = lines[i].Split(',');
            BigInteger n0 = BigInteger.Parse(f[0]), N = BigInteger.Parse(f[1]), m0 = BigInteger.Parse(f[2]), M = BigInteger.Parse(f[3]);
            int k = int.Parse(f[4]), l = int.Parse(f[5]);
            string w = f[6], v = f[7];
            rows++;
            bool ok = m0 > 0 && m0 < n0 && M <= N && N % BigInteger.Pow(2, k) == 0 && M % BigInteger.Pow(2, l) == 0 && v.Length == l && w.Length >= k;
            for (int h = 0; ok && h < 8; h++)
            {
                BigInteger x = n0 + N * h, y = m0 + M * h;
                int a = 0, b = 0;
                for (int j = 0; j < k; j++) { int bit = x.IsEven ? 0 : 1; if (w[j] - '0' != bit) ok = false; a += bit; x = T(x); }
                for (int j = 0; j < l; j++) { int bit = y.IsEven ? 0 : 1; if (v[j] - '0' != bit) ok = false; b += bit; y = T(y); }
                if (x != y) ok = false;
                if (BigInteger.Pow(3, a) * N * BigInteger.Pow(2, l) != BigInteger.Pow(3, b) * M * BigInteger.Pow(2, k)) ok = false;
            }
            if (!ok) { bad++; Console.WriteLine($"FAIL row {i}"); }
        }
        Console.WriteLine($"rows={rows} failures={bad}");
        return bad == 0 && rows > 0 ? 0 : 1;
    }
}
