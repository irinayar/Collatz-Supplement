// Random test of the carry-cylinder identities: C_t, binary integrality, ternary endpoint, shifted target.
using System;
using System.Numerics;
class P {
 static BigInteger Mod(BigInteger a,BigInteger m){ var r=a%m; return r<0?r+m:r; }
 static void Main(){
  var rng=new Random(7); long tests=0, bad=0, integralSeen=0, endpointSeen=0;
  for(int it=0;it<200000;it++){
   int t=rng.Next(1,8); var D=new BigInteger[t+1]; int i=rng.Next(0,3), j=rng.Next(0,3);
   for(int s=0;s<=t;s++){ D[s]=(BigInteger.One<<j)-(BigInteger.One<<i); i+=rng.Next(0,3); j+=rng.Next(0,3); }
   var C=new BigInteger[t+1]; C[0]=0; for(int h=0;h<t;h++) C[h+1]=3*C[h]+3*(BigInteger.One<<h)*(D[h]-D[h+1]);
   // closed form
   BigInteger closed=BigInteger.Pow(3,t)*D[0]-3*(BigInteger.One<<(t-1))*D[t]; for(int h=1;h<t;h++) closed-=BigInteger.Pow(3,t-h)*(BigInteger.One<<(h-1))*D[h];
   tests++; if(closed!=C[t]) bad++;
   BigInteger R0=rng.Next(-20000,20000);
   // direct recurrence with integrality
   BigInteger R=R0; bool integral=true; for(int s=0;s<t;s++){ var x=3*(R+D[s]-D[s+1]); if(x%2!=0){integral=false;break;} R=x/2; }
   var m2=BigInteger.One<<t; bool cong=Mod(BigInteger.Pow(3,t)*R0+C[t],m2)==0; if(integral!=cong) bad++;
   if(integral){ integralSeen++; if((BigInteger.One<<t)*R!=BigInteger.Pow(3,t)*R0+C[t]) bad++;
    for(int K=1;K<=10;K++){ bool direct=R%BigInteger.Pow(3,K)==0; bool crit = K<=t ? C[t]%BigInteger.Pow(3,K)==0 : (C[t]%BigInteger.Pow(3,t)==0 && Mod(R0+C[t]/BigInteger.Pow(3,t),BigInteger.Pow(3,K-t))==0); if(direct!=crit) bad++; if(direct) endpointSeen++; } }
  }
  Console.WriteLine($"tests {tests}, integral paths {integralSeen}, endpoint hits {endpointSeen}, mismatches {bad}");
 }
}
