// Actual lift of the e=19 witness through the prefix 1^8.
using System;
using System.Numerics;
class P {
 static void Main(){
  string w="11101111001101111010011101101101101101101101100001101", v="01100000110000000001111111111101111111111111110111100";
  BigInteger n0=BigInteger.Parse("3004682937636455"); int d=6561; var M=BigInteger.One<<w.Length;
  // y = n0 mod 2^53 with 2^8 y = C_P mod 3^8
  BigInteger p3=6561, CP=p3-256, y=n0%M; while(((256*y-CP)%p3)!=0) y+=M;
  BigInteger n=(256*y-CP)/p3, m=n-256;
  string P8="11111111"; bool ok=m>0; BigInteger a=n,b=m; int oa=0,ob=0; BigInteger pw=1; string W=P8+w, V=P8+v;
  for(int t=0;t<W.Length;t++){ ok&=(a.IsEven?'0':'1')==W[t]&&(b.IsEven?'0':'1')==V[t]; if(!a.IsEven){a=(3*a+1)/2;oa++;pw*=3;} else a/=2; if(!b.IsEven){b=(3*b+1)/2;ob++;} else b/=2; ok&=pw>(BigInteger.One<<(t+1)); }
  ok&=a==b&&oa==ob;
  Console.WriteLine($"{(ok?"ok":"FAIL")} n={n} m={m} n-m={n-m} steps={W.Length} odd={oa} endpoint={a} d={d}");
 }
}
