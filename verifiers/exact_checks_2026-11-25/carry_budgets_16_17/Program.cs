// Filtered equal-count displacement set for a given even budget e (bit-array reverse closure), with an explicit witness check.
using System;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;
using System.Diagnostics;

class P {
 static void Main(string[] args){
  foreach(var e in args.Select(int.Parse)) Run(e);
 }
 static void Run(int e){
  var sw=Stopwatch.StartNew();
  int B=0; while(!(BigInteger.Pow(3,B)>(BigInteger.One<<(B+e)))) B++;
  var allow=new bool[e+1,B+1];
  for(int I=0;I<=e;I++) for(int b=0;b<=B;b++) allow[I,b]=(b==0&&I==0)||BigInteger.Pow(3,b)>(BigInteger.One<<(b+I));
  long off=1L<<e, rn=2*off+1, per=(e+1)*(e+1);
  long total=rn*(B+1)*per;
  var bits=new ulong[(total+63)/64];
  long Idx(int i,int j,int r,int b)=>((r+off)*(B+1)+b)*per+i*(e+1)+j;
  bool Get(long k)=>(bits[k>>6]>>(int)(k&63)&1)!=0;
  bool Set(long k){ var m=1UL<<(int)(k&63); if((bits[k>>6]&m)!=0) return false; bits[k>>6]|=m; return true; }
  var chunks=new List<long[]>(); long head=0, tail=0; const int CH=1<<20;
  void Push(long k){ if(tail/CH==chunks.Count) chunks.Add(new long[CH]); chunks[(int)(tail/CH)][tail%CH]=k; tail++; }
  for(int b=1;b<=B;b++){ var k=Idx(e,e,0,b); Set(k); Push(k); }
  while(head<tail){
   long k=chunks[(int)(head/CH)][head%CH]; if(head%CH==CH-1) chunks[(int)(head/CH)]=null; head++;
   long p=k%per; long q=k/per; int bb=(int)(q%(B+1)); int R=(int)(q/(B+1)-off); int I=(int)(p/(e+1)), J=(int)(p%(e+1));
   if(R%3!=0) continue; int baseC=2*R/3;
   for(int b=(bb<B?bb-1:B-1); b<=(bb<B?bb-1:B); b++){
    if(b<0) continue;
    for(int i=0;i<=I;i++){
     if(!allow[I,b]) break; if(i==0&&I>=2) continue;
     int lo=-((1<<e)-(1<<i));
     for(int j=0;j<=J;j++){
      int r=baseC+((1<<J)-(1<<j))-((1<<I)-(1<<i));
      if(r<lo||r>(1<<e)-(1<<j)) continue;
      var nk=Idx(i,j,r,b); if(Set(nk)) Push(nk);
     }
    }
   }
  }
  var D=new List<int>(); for(int d=1;d<(1<<e);d++) if(Get(Idx(0,0,d,0))) D.Add(d);
  int V3(int x){ int v=0; while(x%3==0){x/=3;v++;} return v; }
  int mv=D.Max(V3);
  Console.WriteLine($"e={e}: states {tail}, positive d {D.Count}, max {D.Max()}, max v3 {mv}, multiples of 729: {string.Join(",",D.Where(d=>d%729==0))}; multiples of 2187: {string.Join(",",D.Where(d=>d%2187==0))} ({sw.Elapsed.TotalSeconds:F0}s)");
  // explicit witness for the smallest d of maximal valuation: forward depth-first walk through marked states
  int target=D.First(d=>V3(d)==mv);
  var seen=new HashSet<long>(); var path=new List<(int i,int j,int I,int J)>();
  bool Dfs(int i,int j,int r,int b){
   if(i==e&&j==e&&r==0&&b>=1) return true;
   if(!seen.Add(Idx(i,j,r,b))) return false;
   for(int I=i;I<=e;I++){ if(!allow[I,b]) break; if(i==0&&I>=2) break;
    for(int J=j;J<=e;J++){
     long c=((1L<<J)-(1L<<j))-((1L<<I)-(1L<<i)); long x=3*((long)r-c); if(x%2!=0) continue; x/=2;
     int nb=Math.Min(b+1,B); if(x< -((1L<<e)-(1L<<I)) || x>(1L<<e)-(1L<<J)) continue;
     if(!Get(Idx(I,J,(int)x,nb))) continue;
     path.Add((i,j,I,J)); if(Dfs(I,J,(int)x,nb)) return true; path.RemoveAt(path.Count-1); } }
   return false;
  }
  bool found=Dfs(0,0,target,0);
  if(!found){ Console.WriteLine($"no witness path for d={target}"); return; }
  var w=new System.Text.StringBuilder(); var v=new System.Text.StringBuilder();
  for(int t=0;t<path.Count;t++){ var (i,j,I,J)=path[t]; w.Append('0',I-i); v.Append('0',J-j); if(t<path.Count-1){ w.Append('1'); v.Append('1'); } }
  string W=w.ToString(), Vw=v.ToString();
  BigInteger Num(string s){ BigInteger C=0; for(int t=0;t<s.Length;t++) if(s[t]=='1') C=3*C+(BigInteger.One<<t); return C; }
  int a=W.Count(c=>c=='1'); var mod=BigInteger.One<<W.Length; var pa=BigInteger.Pow(3,a); BigInteger inv=1; for(int it=0;it<9;it++) inv=((inv*(2-pa*inv))%mod+mod)%mod;
  var n=((-Num(W)*inv)%mod+mod)%mod; while(n<=target) n+=mod; var m=n-target;
  BigInteger x1=n,y1=m; bool ok=W.Length==Vw.Length&&a==Vw.Count(c=>c=='1'); BigInteger pw=1; int odd=0;
  for(int t=0;t<W.Length;t++){ ok&=(x1.IsEven?'0':'1')==W[t]&&(y1.IsEven?'0':'1')==Vw[t]; if(!x1.IsEven){x1=(3*x1+1)/2; odd++; pw*=3;} else x1/=2; y1=y1.IsEven?y1/2:(3*y1+1)/2; ok&=pw>(BigInteger.One<<(t+1)); }
  ok&=x1==y1 && !(W.IndexOf('0')>0 && W.IndexOf('0')+1<W.Length && W[W.IndexOf('0')+1]=='0');
  Console.WriteLine($"witness d={target} (v3={mv}), length {W.Length}, odd {a}, even {W.Length-a}: replay and filter {(ok?"ok":"FAIL")}\n w={W}\n v={Vw}\n n={n} m={m}");
 }
}
