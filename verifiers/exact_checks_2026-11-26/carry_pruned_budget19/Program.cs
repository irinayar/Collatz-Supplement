// Filtered displacement sets with dead states pruned: at layers b>=1 carries are divisible by 3, so store s=R/3.
using System;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;

class P {
 static void Main(string[] args){
  foreach(var e in args.Select(int.Parse)){ Run(e); GC.Collect(); }
  Console.WriteLine($"peak working set {Process.GetCurrentProcess().PeakWorkingSet64>>20} MB");
 }
 static void Run(int e){
  var sw=Stopwatch.StartNew(); int H=1<<e;
  int B=0; while(!(BigInteger.Pow(3,B)>(BigInteger.One<<(B+e)))) B++;
  var allow=new bool[e+1,B+1];
  for(int I=0;I<=e;I++) for(int b=0;b<=B;b++) allow[I,b]=(b==0&&I==0)||BigInteger.Pow(3,b)>(BigInteger.One<<(b+I));
  int CDiv(int a)=>a>=0?(a+2)/3:-((-a)/3); int FDiv(int a)=>a>=0?a/3:-((-a+2)/3);
  var lo=new int[e+1]; for(int i=0;i<=e;i++) lo[i]=CDiv(-(H-(1<<i)));
  var hi=new int[e+1]; for(int j=0;j<=e;j++) hi[j]=FDiv(H-(1<<j));
  var baseOf=new long[e+1,e+1]; long per=0; for(int i=0;i<=e;i++) for(int j=0;j<=e;j++){ baseOf[i,j]=per; per+=Math.Max(0,hi[j]-lo[i]+1); }
  long total=per*B; var bits=new ulong[(total+63)/64];
  var init=new bool[H];
  var chunks=new Queue<(int s,byte i,byte j,byte b)[]>(); const int CH=1<<20; var cur=new (int,byte,byte,byte)[CH]; var read=cur; int wp=0,rp=0; long pushed=0,popped=0;
  void Push(int i,int j,int s,int b){ long k=per*(b-1)+baseOf[i,j]+(s-lo[i]); var m=1UL<<(int)(k&63); if((bits[k>>6]&m)!=0) return; bits[k>>6]|=m;
   if(wp==CH){ cur=new (int,byte,byte,byte)[CH]; chunks.Enqueue(cur); wp=0; } cur[wp++]=(s,(byte)i,(byte)j,(byte)b); pushed++; }
  for(int b=1;b<=B;b++) Push(e,e,0,b);
  while(popped<pushed){
   if(rp==CH){ read=chunks.Dequeue(); rp=0; }
   var (S,I,J,bb)=read[rp++]; popped++;
   int baseC=2*S; // 2R/3 with R=3S
   for(int h=bb-1;h<=(bb<B?bb-1:B);h++){
    if(h==0){ // initial states: i=j=0, and the source block 0..I must be empty
      if(I==0){ int r=baseC+(1<<J)-1; if(r>0&&r<H) init[r]=true; }
      continue; }
    for(int i=0;i<=I;i++){
     if(!allow[I,h]) break; if(i==0&&I>=2) continue;
     for(int j=0;j<=J;j++){
      int r=baseC+((1<<J)-(1<<j))-((1<<I)-(1<<i));
      if(r%3!=0) continue; if(r< -(H-(1<<i))||r>H-(1<<j)) continue;
      Push(i,j,r/3,h);
     }
    }
   }
  }
  var D=new List<int>(); for(int d=1;d<H;d++) if(init[d]) D.Add(d);
  int V3(int x){ int v=0; while(x%3==0){x/=3;v++;} return v; }
  Console.WriteLine($"e={e}: pruned states {pushed}, positive d {D.Count}, max {D.Max()}, max v3 {D.Max(V3)} ({sw.Elapsed.TotalSeconds:F0}s, bits {total/8>>20} MB)");
  Console.WriteLine($"  multiples of 729: {string.Join(" ",D.Where(d=>d%729==0))}; of 6561: {string.Join(" ",D.Where(d=>d%6561==0))}");
 }
}
