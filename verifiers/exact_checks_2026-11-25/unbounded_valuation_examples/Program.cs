// Explicit equal-count synchronous meetings whose displacement is divisible by high powers of 3 (birthday search).
using System;
using System.Numerics;
using System.Collections.Generic;

class P {
 static void Main(){
  var rng=new Random(12345); int fails=0;
  foreach(var (B,M,a) in new[]{(4,24,6),(7,36,9),(8,40,10),(10,48,12),(12,56,14)}){
   ulong mod=1; for(int i=0;i<a+B;i++) mod*=3;
   var seen=new Dictionary<ulong,ulong>(); ulong w1=0,w2=0; BigInteger c1=0,c2=0; int tries=0;
   while(true){
    // random word of length M with exactly a odd steps, as a bit mask
    ulong w=0; int k=0; while(k<a){ int p=rng.Next(M); if((w>>p&1)==0){ w|=1UL<<p; k++; } }
    UInt128 C=0; for(int i=0;i<M;i++) if((w>>i&1)==1) C=3*C+((UInt128)1<<i);
    ulong key=(ulong)(C%mod); tries++;
    if(seen.TryGetValue(key,out var u)){ if(u!=w){ w1=u; w2=w; break; } } else seen[key]=w;
    if(tries>20000000) break;
   }
   BigInteger Num(ulong w){ BigInteger C=0; for(int i=0;i<M;i++) if((w>>i&1)==1) C=3*C+(BigInteger.One<<i); return C; }
   c1=Num(w1); c2=Num(w2); if(c1>c2){ (w1,w2)=(w2,w1); (c1,c2)=(c2,c1); }
   // w1 has the smaller numerator: its start n is the larger one, d=(C2-C1)/3^a
   var pa=BigInteger.Pow(3,a); var d=(c2-c1)/pa; bool ok=(c2-c1)%pa==0 && d%BigInteger.Pow(3,B)==0 && d>0 && d<(BigInteger.One<<M);
   var two=BigInteger.One<<M; BigInteger inv=1; for(int it=0;it<8;it++) inv=((inv*(2-pa*inv))%two+two)%two;
   var n=((-c1*inv)%two+two)%two; while(n<=d) n+=two; var m=n-d;
   // replay both actual trajectories
   BigInteger x=n,y=m; int ax=0,ay=0; for(int i=0;i<M;i++){ ok&=(x.IsEven?0UL:1UL)==(w1>>i&1) && (y.IsEven?0UL:1UL)==(w2>>i&1); if(!x.IsEven){ x=(3*x+1)/2; ax++; } else x/=2; if(!y.IsEven){ y=(3*y+1)/2; ay++; } else y/=2; }
   ok&=x==y&&ax==a&&ay==a;
   int v=0; var t=d; while(t%3==0){ t/=3; v++; }
   string Word(ulong w){ var s=new char[M]; for(int i=0;i<M;i++) s[i]=(w>>i&1)==1?'1':'0'; return new string(s); }
   Console.WriteLine($"{(ok?"ok  ":"FAIL")} B={B} M={M} a={a}: v3(d)={v} d={d} n={n} m={m} end={x} tries={tries}");
   Console.WriteLine($"     w={Word(w1)} v={Word(w2)}");
   if(!ok) fails++;
  }
  Console.WriteLine($"failed: {fails}");
 }
}
