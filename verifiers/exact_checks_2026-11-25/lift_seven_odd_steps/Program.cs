// Actual lift of the e=17 witness through the prefix 1^7.
using System;
using System.Numerics;
class P {
 static void Main(){
  string w="111011101101101101101101101101101101101100001101", v="001110000010100000011111111111111111111110111100";
  BigInteger n0=BigInteger.Parse("267493532554983"); int d=2187; var M=BigInteger.One<<w.Length;
  // y = n0 mod 2^48 with 2^7 y = C_P mod 3^7, C_P = 3^7 - 2^7
  BigInteger p3=2187, CP=p3-128, y=n0%M; while(((128*y-CP)%p3)!=0) y+=M;
  BigInteger n=(128*y-CP)/p3, m=n-128;
  string P7="1111111"; bool ok=m>0; BigInteger a=n,b=m; int oa=0,ob=0; BigInteger pw=1; string W=P7+w, V=P7+v;
  for(int t=0;t<W.Length;t++){ ok&=(a.IsEven?'0':'1')==W[t]&&(b.IsEven?'0':'1')==V[t]; if(!a.IsEven){a=(3*a+1)/2;oa++;pw*=3;} else a/=2; if(!b.IsEven){b=(3*b+1)/2;ob++;} else b/=2; ok&=pw>(BigInteger.One<<(t+1)); }
  ok&=a==b&&oa==ob;
  Console.WriteLine($"{(ok?"ok":"FAIL")} n={n} m={m} n-m={n-m} steps={W.Length} odd={oa} endpoint={a} d={d}");
 }
}
