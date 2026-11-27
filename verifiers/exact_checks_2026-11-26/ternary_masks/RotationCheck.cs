// every mask (least even cost by t, 10 = none) must be a cyclic rotation, within its least period, of the first mask with the same a
static class Rot
{
    static readonly byte[][] first = new byte[6][];
    static readonly int[] period = new int[6];
    public static long failures;
    static int Least(byte[] m)
    {
        for (int p = 1; p < m.Length; p *= 3)
        {
            bool ok = true;
            for (int t = p; t < m.Length && ok; t++) if (m[t] != m[t - p]) ok = false;
            if (ok) return p;
        }
        return m.Length;
    }
    public static void Check(int k, byte[] minE)
    {
        int p = Least(minE);
        if (first[k] == null) { first[k] = (byte[])minE.Clone(); period[k] = p; return; }
        if (p != period[k]) { failures++; return; }
        var f = first[k];
        for (int s = 0; s < p; s++)
        {
            int t = 0;
            while (t < p && minE[t] == f[(t + s) % p]) t++;
            if (t == p) return;
        }
        failures++;
    }
    public static string Report()
    {
        string r = "";
        for (int k = 0; k < 6; k++)
        {
            if (first[k] == null) continue;
            int n = 0; for (int t = 0; t < period[k]; t++) if (first[k][t] <= 9) n++;
            r += $"a={32 + k}: least period {period[k]}, residues with witness {n}; ";
        }
        return r + $"rotation failures={failures}";
    }
}
