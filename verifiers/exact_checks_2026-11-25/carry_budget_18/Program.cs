// Budget 18 filtered displacement set with a compact bit layout (carry range depends on i,j); plus the budget-19 witness.
using System;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;

class P {
 static void Main(){
  Witness();
  Run(17); Run(18);
  var pr=Process.GetCurrentProcess(); Console.WriteLine($"peak working set {pr.PeakWorkingSet64>>20} MB");
 }
 static void Witness(){
  string W="11101111001101111010011101101101101101101101100001101", V="01100000110000000001111111111101111111111111110111100";
  BigInteger n=BigInteger.Parse("3004682937636455"), m=BigInteger.Parse("3004682937629894"), a=n, b=m; bool ok=W.Length==53&&V.Length==53; BigInteger pw=1; int oa=0,ob=0;
  for(int t=0;t<W.Length;t++){ ok&=(a.IsEven?'0':'1')==W[t]&&(b.IsEven?'0':'1')==V[t]; if(!a.IsEven){a=(3*a+1)/2;oa++;pw*=3;} else a/=2; if(!b.IsEven){b=(3*b+1)/2;ob++;} else b/=2; ok&=pw>(BigInteger.One<<(t+1)); }
  int z=W.IndexOf('0'); ok&=!(z>0&&W[z+1]=='0'); var d=n-m;
  Console.WriteLine($"budget-19 witness: d={d} = 3^8 {d==6561}; odd {oa},{ob}; even {W.Length-oa}; endpoint {a}; parities, common endpoint, source filter: {(ok&&a==b&&oa==ob&&a==BigInteger.Parse("5563287974835866")?"ok":"FAIL")}");
 }
 static void Run(int e){
  var sw=Stopwatch.StartNew();
  int B=0; while(!(BigInteger.Pow(3,B)>(BigInteger.One<<(B+e)))) B++;
  var lim=new bool[e+1,B+1];
  for(int I=0;I<=e;I++) for(int b=0;b<=B;b++) lim[I,b]=(b==0&&I==0)||BigInteger.Pow(3,b)>(BigInteger.One<<(b+I));
  int H=1<<e; var baseOf=new long[e+1,e+1]; var loOf=new int[e+1]; long per=0;
  for(int i=0;i<=e;i++) loOf[i]=-(H-(1<<i));
  for(int i=0;i<=e;i++) for(int j=0;j<=e;j++){ baseOf[i,j]=per; per+=(H-(1<<j))-loOf[i]+1; }
  long total=per*(B+1); var bits=new ulong[(total+63)/64];
  var chunks=new Queue<(int r,byte i,byte j,byte b)[]>(); const int CH=1<<20; var cur=new (int,byte,byte,byte)[CH]; var read=cur; int wp=0, rp=0; long pushed=0, popped=0;
  void Push(int i,int j,int r,int b){ long k=per*b+baseOf[i,j]+(r-loOf[i]); var mk=1UL<<(int)(k&63); if((bits[k>>6]&mk)!=0) return; bits[k>>6]|=mk;
   if(wp==CH){ cur=new (int,byte,byte,byte)[CH]; chunks.Enqueue(cur); wp=0; } cur[wp++]=(r,(byte)i,(byte)j,(byte)b); pushed++; }
  for(int b=1;b<=B;b++) Push(e,e,0,b);
  while(popped<pushed){
   if(rp==CH){ read=chunks.Dequeue(); rp=0; }
   var (R,I,J,bb)=read[rp++]; popped++;
   if(R%3!=0||bb==0) continue; int baseC=2*R/3;
   for(int b=bb-1;b<=(bb<B?bb-1:B);b++){
    for(int i=0;i<=I;i++){
     if(!lim[I,b]) break; if(i==0&&I>=2) continue;
     for(int j=0;j<=J;j++){ int r=baseC+((1<<J)-(1<<j))-((1<<I)-(1<<i)); if(r<loOf[i]||r>H-(1<<j)) continue; Push(i,j,r,b); }
    }
   }
  }
  var D=new List<int>(); for(int d=1;d<H;d++){ long k=baseOf[0,0]+(d-loOf[0]); if((bits[k>>6]>>(int)(k&63)&1)!=0) D.Add(d); }
  int V3(int x){ int v=0; while(x%3==0){x/=3;v++;} return v; }
  Console.WriteLine($"e={e}: states {pushed}, positive d {D.Count}, max {D.Max()}, max v3 {D.Max(V3)}, multiples of 729: {string.Join(",",D.Where(d=>d%729==0))} ({sw.Elapsed.TotalSeconds:F0}s, bits {total/8/(1<<20)} MB)");
 }
}
