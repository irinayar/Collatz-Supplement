// Interval certification of the residual-factor bounds. Input: depth-53 table "a,N,H,P" (exact integers, pending counted once in N).
// V: backward recursion in doubles with outward rounding after every operation; all final sums are exact rationals.
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;

readonly struct R { // exact rational
 public readonly BigInteger n,d;
 public R(BigInteger a,BigInteger b){ if(b<0){a=-a;b=-b;} var g=BigInteger.GreatestCommonDivisor(a,b); if(g>1){a/=g;b/=g;} n=a;d=b; }
 public static R operator+(R x,R y)=>new R(x.n*y.d+y.n*x.d,x.d*y.d);
 public static R operator-(R x,R y)=>new R(x.n*y.d-y.n*x.d,x.d*y.d);
 public static R operator*(R x,R y)=>new R(x.n*y.n,x.d*y.d);
 public static R operator/(R x,R y)=>new R(x.n*y.d,x.d*y.n);
 public static bool operator>(R x,R y)=>x.n*y.d>y.n*x.d;
 public static bool operator<(R x,R y)=>x.n*y.d<y.n*x.d;
 public static R Dbl(double v){ long b=BitConverter.DoubleToInt64Bits(v); int e=(int)((b>>52)&0x7ff); long m=b&0xfffffffffffffL; if(e!=0) m|=1L<<52; else e=1; e-=1075; BigInteger M=v<0?-m:m; return e>=0?new R(M<<e,1):new R(M,BigInteger.One<<(-e)); }
 public static R Dec(string s){ int k=s.IndexOf('.'); int f=k<0?0:s.Length-k-1; return new R(BigInteger.Parse(s.Replace(".","")),BigInteger.Pow(10,f)); }
}
class P {
 static double Dn(double v)=>Math.BitDecrement(v);
 static double Up(double v)=>Math.BitIncrement(v);
 static int fails=0;
 static void Check(string what,bool ok){ Console.WriteLine((ok?"CERTIFIED  ":"NOT PROVED ")+what); if(!ok) fails++; }
 // ln as exact-rational enclosure by 2 atanh(1/k) series, scale 2^200, padded by 2^-150
 static BigInteger Atanh2(int k){ var one=BigInteger.One<<200; BigInteger term=one/k, sum=0; int j=1; while(term>0){ sum+=term/j; term/=k*k; j+=2; } return 2*sum; }
 static void Main(string[] args){
  var S=BigInteger.One<<200; var pad=BigInteger.One<<50;
  var l2=Atanh2(3); var l32=Atanh2(5); var l3=l2+l32;
  double ToD(BigInteger v)=> (double)v/Math.Pow(2,200);
  double b2lo=Dn(Dn(ToD(l2))), b2hi=Up(Up(ToD(l2))), l3lo=Dn(Dn(ToD(l3))), l3hi=Up(Up(ToD(l3)));
  double thlo=Dn(Dn(b2lo/l3hi)), thhi=Up(Up(b2hi/l3lo));
  Check("double enclosures contain ln2, ln3, theta", R.Dbl(b2lo)<new R(l2-pad,S) && R.Dbl(b2hi)>new R(l2+pad,S) && R.Dbl(l3lo)<new R(l3-pad,S) && R.Dbl(l3hi)>new R(l3+pad,S)
    && R.Dbl(thlo)<new R(l2-pad,l3+pad) && R.Dbl(thhi)>new R(l2+pad,l3-pad));
  double colo=Dn(1-thhi), cohi=Up(1-thlo);
  int Bar(int d){ int x=(int)Math.Floor(d*thlo-1e-8), y=(int)Math.Floor(d*thhi+1e-8); if(x!=y) throw new Exception("ambiguous barrier at "+d); return x+1; }
  const int D=53, n=400000, W=2200;
  double Zlo(int a,int d)=>Dn(Dn(a*l3lo)-Up(d*b2hi));
  double Zhi(int a,int d)=>Up(Up(a*l3hi)-Dn(d*b2lo));
  int E=D+n, bE=Bar(E); var lo=new double[W+2]; var hi=new double[W+2];
  for(int i=0;i<=W+1;i++){ lo[i]=Math.Max(0,Zlo(bE+i,E)); hi[i]=Up(Zhi(bE+i,E)+b2hi); }
  var nlo=new double[W+2]; var nhi=new double[W+2];
  for(int d=E-1;d>=D;d--){
   int b=Bar(d), nb=Bar(d+1);
   for(int i=0;i<=W+1;i++){
    int a=b+i, i1=a+1-nb, i0=a-nb; double l=0,h=0;
    if(i1>W+1){ l=Dn(thlo*Zlo(a+1,d+1)); h=Up(thhi*Up(Zhi(a+1,d+1)+b2hi)); } else if(i1>=0){ l=Dn(thlo*lo[i1]); h=Up(thhi*hi[i1]); }
    if(i0>W+1){ l=Dn(l+Dn(colo*Zlo(a,d+1))); h=Up(h+Up(cohi*Up(Zhi(a,d+1)+b2hi))); } else if(i0>=0){ l=Dn(l+Dn(colo*lo[i0])); h=Up(h+Up(cohi*hi[i0])); }
    nlo[i]=l; nhi[i]=h;
   }
   (lo,nlo)=(nlo,lo); (hi,nhi)=(nhi,hi);
  }
  int bD=Bar(D);
  var rows=File.ReadAllLines(args[0]).Skip(1).Select(x=>x.Split(',')).Select(f=>(a:int.Parse(f[0]),N:BigInteger.Parse(f[1]),H:BigInteger.Parse(f[2]),P:BigInteger.Parse(f[3]))).ToList();
  R tl=R.Dbl(thlo), th=R.Dbl(thhi), cl=new R(1,1)-th, ch=new R(1,1)-tl;
  R Pw(R x,int k){ var r=new R(1,1); for(int i=0;i<k;i++) r=r*x; return r; }
  var hlo=new Dictionary<int,R>(); var hhi=new Dictionary<int,R>();
  foreach(var x in rows){ int a=x.a; hlo[a]=Pw(tl,a)*Pw(cl,D-a)*R.Dbl(lo[a-bD]); hhi[a]=Pw(th,a)*Pw(ch,D-a)*R.Dbl(hi[a-bD]); }
  Console.WriteLine($"states {rows.Count}, a={rows[0].a}..{rows[^1].a}; V width at a=44: {hi[44-bD]-lo[44-bD]:E3}");
  // sign of sum h_a c_a : lower and upper bounds with the endpoint chosen by the sign of c_a
  R Low(Func<(int a,BigInteger N,BigInteger H,BigInteger P),R> c){ var s=new R(0,1); foreach(var x in rows){ var v=c(x); s=s+v*(v.n>=0?hlo[x.a]:hhi[x.a]); } return s; }
  var zero=new R(0,1); var Q=new R(2519180,4782969); var L0=new R(BigInteger.Pow(3,21),1);
  R I(BigInteger v)=>new R(v,1);
  bool UqBelow(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>I(x.H)-k*I(x.N))>zero; }
  bool UoffBelow(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>I(x.H)-k*I(x.N-x.P))>zero; }
  bool PAbove(string t){ var k=R.Dec(t); return Low(x=>I(x.P)-k*I(x.N))>zero; }
  Check("U < 0.524471204",UqBelow("0.524471204"));
  Check("Uoff < 0.524469667",UoffBelow("0.524469667"));
  Check("Pi > 0.000689035",PAbove("0.000689035"));
  Check("U < 0.5244697060",UqBelow("0.5244697060"));
  Check("Uoff < 0.5244681700",UoffBelow("0.5244681700"));
  Check("Pi > 0.0006892269",PAbove("0.0006892269"));
  // exact limits: M = sum h N - Rm, Rm = sum_{m>=52} h(m+2,m) + sum_{j>=46} h(j+8,j+2) >= 0
  R RmHi=zero, RmLo=zero;
  R LnR(double v)=>R.Dbl(v);
  void Term(int d,int a){ RmLo=RmLo+Pw(tl,a)*Pw(cl,d-a)*LnR(Math.Max(0,Zlo(a,d))); RmHi=RmHi+Pw(th,a)*Pw(ch,d-a)*LnR(Up(Zhi(a,d)+b2hi)); }
  for(int m=52;m<=110;m++) Term(m+2,m);
  for(int j=46;j<=110;j++) Term(j+8,j+2);
  // tails beyond 110: terms are below th^a (a ln(3/2)+ln2) times a bounded factor; ratio of successive terms < 0.65
  R tail=(Pw(th,111)*Pw(ch,2)+Pw(th,113)*Pw(ch,6))*R.Dec("47.0")*R.Dec("3.0");
  RmHi=RmHi+tail;
  // q > x  iff  sum h((Q-x)L0 N - H) - (Q-x)L0 Rm > 0
  bool QAbove(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>k*I(x.N)-I(x.H))-k*RmHi>zero; }
  bool QoffAbove(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>k*I(x.N-x.P)-I(x.H))-k*RmHi>zero; }
  bool PBelow(string t){ var k=R.Dec(t); return Low(x=>k*I(x.N)-I(x.P))-k*RmHi>zero; }
  Check("q_inf > 0.5244690270",QAbove("0.5244690270"));
  Check("qoff_inf > 0.5244674880",QoffAbove("0.5244674880"));
  Check("p_inf < 0.0006899801",PBelow("0.0006899801"));
  // ---- joint model: the two e=13,15 pumped families and the offset-18 family also removed ----
  {
   R ELo=zero, EHi=zero;
   void T(int d,int a){ ELo=ELo+Pw(tl,a)*Pw(cl,d-a)*LnR(Math.Max(0,Zlo(a,d))); EHi=EHi+Pw(th,a)*Pw(ch,d-a)*LnR(Up(Zhi(a,d)+b2hi)); }
   for(int t=0;t<=130;t++){ T(41+t,28+t); T(47+t,32+t); }
   for(int t=43;t<=130;t++) T(113+t,56+t);
   // tail after t=130: each series has ratio < 0.65 and V < 80 there
   EHi=EHi+(Pw(th,159)*Pw(ch,13)+Pw(th,163)*Pw(ch,15)+Pw(th,187)*Pw(ch,57))*R.Dec("80.0")*R.Dec("3.0");
   Console.WriteLine($"E in [{(double)(ELo.n*BigInteger.Pow(10,24)/ELo.d)/1e24:E6}, {(double)(EHi.n*BigInteger.Pow(10,24)/EHi.d)/1e24:E6}]");
   bool JQAbove(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>k*I(x.N)-I(x.H))-k*(RmHi+EHi)>zero; }
   bool JQBelow(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>I(x.H)-k*I(x.N))+k*(RmLo+ELo)>zero; }
   bool JOffAbove(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>k*I(x.N-x.P)-I(x.H))-k*(RmHi+EHi)>zero; }
   bool JOffBelow(string t){ var k=(Q-R.Dec(t))*L0; return Low(x=>I(x.H)-k*I(x.N-x.P))+k*(RmLo+ELo)>zero; }
   bool JPAbove(string t){ var k=R.Dec(t); return Low(x=>I(x.P)-k*I(x.N))+k*(RmLo+ELo)>zero; }
   bool JPBelow(string t){ var k=R.Dec(t); return Low(x=>k*I(x.N)-I(x.P))-k*(RmHi+EHi)>zero; }
   Check("joint q in (0.5244690270, 0.5244697060)",JQAbove("0.5244690270")&&JQBelow("0.5244697060"));
   Check("joint qoff in (0.5244674880, 0.5244681700)",JOffAbove("0.5244674880")&&JOffBelow("0.5244681700"));
   Check("joint p in (0.0006892269, 0.0006899801)",JPAbove("0.0006892269")&&JPBelow("0.0006899801"));
  }
  // gain, with 2 S[5,46] <= 2 S* <= 2 (S[5,46] + 3/(2*3^e47))
  var S42=new R(BigInteger.Parse("3442126137756879465367893417111436"),BigInteger.Parse("443426488243037769948249630619149892803"));
  int r47=2; while(!(BigInteger.Pow(3,r47+47)>(BigInteger.One<<(r47+95)))) r47++;
  var Shi=S42+new R(3,2*BigInteger.Pow(3,r47+47)); var two=new R(2,1);
  Check("gain > 0.0000296014848 (from q<0.524471204)", two*S42/R.Dec("0.524471204")>R.Dec("0.0000296014848"));
  Check("sharp gain > 0.0000296015693", two*S42/R.Dec("0.5244697060")>R.Dec("0.0000296015693")); Check("sharp gain < 0.0000296016078", two*Shi/R.Dec("0.5244690270")<R.Dec("0.0000296016078"));
  Check("gain < 0.0000296016420 (from q>0.524468423)", two*Shi/R.Dec("0.524468423")<R.Dec("0.0000296016420"));
  Console.WriteLine($"failed: {fails}");
 }
}
