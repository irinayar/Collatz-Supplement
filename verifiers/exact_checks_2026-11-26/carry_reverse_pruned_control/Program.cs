// Reverse filtered carry graph with the mod-3 pruning at positive layers; states and displacement counts for e=2..10.
using System;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;
class P {
 static void Main(){
  var want=new Dictionary<int,(int B,int states,int edges,int d,int v)>{{2,(4,15,17,0,0)},{3,(6,43,57,0,0)},{4,(7,81,121,0,0)},{5,(9,266,417,0,0)},{6,(11,871,1502,3,1)},{7,(12,2251,4318,5,1)},{8,(14,6233,13870,6,1)},{9,(16,17137,42445,13,2)},{10,(18,43069,119789,31,3)}};
  int bad=0;
  for(int e=2;e<=10;e++){
   int B=0; while(!(BigInteger.Pow(3,B)>(BigInteger.One<<(B+e)))) B++;
   int H=1<<e; var seen=new HashSet<(int,int,int,int)>(); var q=new Queue<(int I,int J,int R,int b)>(); long edges=0;
   for(int b=1;b<=B;b++){ seen.Add((e,e,0,b)); q.Enqueue((e,e,0,b)); }
   while(q.Count>0){ var (I,J,R,bb)=q.Dequeue(); if(R%3!=0||bb==0) continue;
    foreach(var h in bb<B?new[]{bb-1}:new[]{B-1,B}) for(int i=0;i<=I;i++){
     if(!(h==0&&I==0) && !(BigInteger.Pow(3,h)>(BigInteger.One<<(h+I)))) continue; if(i==0&&I>=2) continue;
     for(int j=0;j<=J;j++){ int r=2*R/3+((1<<J)-(1<<j))-((1<<I)-(1<<i)); if(r< -(H-(1<<i))||r>H-(1<<j)) continue;
      if(h>0&&r%3!=0) continue; if(h==0&&!(i==0&&j==0&&r>0&&r<H)) continue;
      edges++; if(seen.Add((i,j,r,h))) q.Enqueue((i,j,r,h)); } } }
   var D=seen.Where(s=>s.Item1==0&&s.Item2==0&&s.Item4==0&&s.Item3>0).Select(s=>s.Item3).ToList();
   int v=D.Count==0?0:D.Max(d=>{int k=0; while(d%3==0){d/=3;k++;} return k;});
   var w=want[e]; bool ok=B==w.B&&seen.Count==w.states&&D.Count==w.d&&v==w.v; if(!ok) bad++;
   Console.WriteLine($"e={e}: B={B} states {seen.Count} ({w.states}) edges {edges} ({w.edges}) d {D.Count} ({w.d}) v3 {v} ({w.v}) {(ok?"ok":"DIFF")}");
  }
  Console.WriteLine($"mismatches (B, states, d, v3): {bad}");
 }
}
