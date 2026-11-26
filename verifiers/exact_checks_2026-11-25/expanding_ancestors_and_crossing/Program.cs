// Independent replay: expanding ancestor catalogue, all-length residual floor, first-crossing bounds, zero-tail height table.
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;

class P {
 static int fails=0; static void Check(string s,bool ok){ Console.WriteLine((ok?"ok   ":"FAIL ")+s); if(!ok) fails++; }
 static BigInteger[] p3=Enumerable.Range(0,900).Select(i=>BigInteger.Pow(3,i)).ToArray();
 static BigInteger P2(int k)=>BigInteger.One<<k;
 static BigInteger Mod(BigInteger a,BigInteger m){ var r=a%m; return r<0?r+m:r; }
 static BigInteger Inv(BigInteger a,BigInteger m){ BigInteger g=m,x=0,x1=1,aa=Mod(a,m); while(aa!=0){ var q=g/aa; (g,aa)=(aa,g-q*aa); (x,x1)=(x1,x-q*x1); } return Mod(x,m); }
 static int R0(int j){ int r=2; while(!(p3[r+j]>P2(r+2*j+1))) r++; return r; }
 static BigInteger Binom(int n,int k){ BigInteger v=1; for(int i=0;i<k;i++) v=v*(n-i)/(i+1); return v; }
 static int La(int a){ int L=0; while(P2(L+1)<p3[a]) L++; return L; }
 // antichain of ternary cylinders
 class Set3 { public SortedDictionary<int,HashSet<BigInteger>> d=new();
  public bool Covered(BigInteger res,int e){ foreach(var kv in d){ if(kv.Key>e) break; if(kv.Value.Contains(res%p3[kv.Key])) return true; } return false; }
  public void Add(BigInteger res,int e){ if(!d.TryGetValue(e,out var h)) d[e]=h=new(); h.Add(res); } }
 static Set3 Anti(IEnumerable<(BigInteger res,int e)> c){ var s=new Set3(); foreach(var x in c.OrderBy(x=>x.e)) if(!s.Covered(x.res,x.e)) s.Add(x.res,x.e); return s; }
 static BigInteger Mass(Set3 s,int top){ BigInteger m=0; foreach(var kv in s.d) m+=kv.Value.Count*p3[top-kv.Key]; return m; }
 static void Main(string[] args){
  var rows=File.ReadAllLines(args[0]).Skip(1).Select(l=>l.Split(',')).Select(f=>(res:BigInteger.Parse(f[1]),mod:BigInteger.Parse(f[2]))).ToList();
  var mixed=new List<(int i,BigInteger b,BigInteger t,int e)>();
  foreach(var (res,mod) in rows){ int i=0,j=0; var m=mod; while(m%2==0){m/=2;i++;} while(m%3==0){m/=3;j++;} if(j>0) mixed.Add((i,res%P2(i),res%p3[j],j)); }
  mixed.Add((6,303%64,303%81,4));
  // expanding words, a<=14
  var anc=new List<(BigInteger,int)>(); long words=0; bool parity=true;
  for(int a=1;a<=14;a++){ int L=La(a); var mod=p3[a]; var inv=Inv(P2(L),mod);
   void Rec(int pos,int odd,BigInteger C){ if(pos==L){ if(odd==a){ words++; var res=Mod(C*inv,mod); anc.Add((res,a)); if(words%997==0){ var y=res+mod*7; var m=(P2(L)*y-C)/mod; var x=m; for(int i=0;i<L;i++){ x=x.IsEven?x/2:(3*x+1)/2; } parity&=(P2(L)*y-C)%mod==0&&m>0&&m<y&&x==y; } } return; }
     if(L-pos>a-odd) Rec(pos+1,odd,C); if(odd<a) Rec(pos+1,odd+1,3*C+P2(pos)); }
   Rec(0,0,0); }
  Check($"words through a=14: {words}; sampled smaller origins reach y", words==466012&&parity);
  var A=Anti(anc); int cnt=A.d.Sum(kv=>kv.Value.Count);
  Check($"antichain cylinders {cnt}, mass {Mass(A,14)}/3^14", cnt==3265&&Mass(A,14)==2233499);
  const int J=40; int e41=41+R0(41);
  var U=new List<(BigInteger,int)>(); for(int k=0;k<=J;k++) for(int s=0;k+s<=J;s++){ int r=k+R0(k+s); var q=p3[r+s]; U.Add((Mod(Inv(P2(k),q)*(1-p3[s+1]*Inv(P2(2*s+1),q)),q),r+s)); }
  Check($"zero-tail rows {U.Count}, e_41={e41}", U.Count==861&&e41==72);
  var excl=mixed.Select(x=>(res:x.t,e:x.e)).Concat(U.Select(c=>(res:c.Item1,e:c.Item2))).ToList();
  var safe=new List<(BigInteger,int)>(); var chosen=new Set3(); foreach(var (res,e) in anc.OrderBy(x=>x.Item2).ThenBy(x=>x.Item1)){ if(chosen.Covered(res,e)) continue; if(excl.Any(c=> c.e<=e ? res%p3[c.e]==c.res : c.res%p3[e]==res)) continue; chosen.Add(res,e); safe.Add((res,e)); } Console.WriteLine($"info selected by a: {string.Join(" ",safe.GroupBy(c=>c.Item2).Select(g=>g.Key+":"+g.Count()))}");
  Check($"cylinders disjoint from mixed projections and zero-tail head: {safe.Count}, mass {Mass(Anti(safe),14)}/3^14", safe.Count==3185&&Mass(Anti(safe),14)==11059);
  // profiles
  int top=Math.Max(72,Math.Max(e41,U.Max(c=>c.Item2))); var prof=new Dictionary<string,(BigInteger q,BigInteger g,int n)>();
  var ancList=A.d.SelectMany(kv=>kv.Value.Select(r=>(r,kv.Key))).ToList();
  for(int b=0;b<2048;b++){
   var P=mixed.Where(x=>(b%(1<<x.i))==x.b).Select(x=>(x.t,x.e)).ToList(); var key=string.Join(";",P.Distinct().OrderBy(c=>c.e).ThenBy(c=>c.t).Select(c=>$"{c.t}/{c.e}"));
   if(prof.TryGetValue(key,out var v)){ prof[key]=(v.q,v.g,v.n+1); continue; }
   var m1=Mass(Anti(P.Concat(U)),top); var m2=Mass(Anti(P.Concat(U).Concat(ancList)),top); prof[key]=(p3[top]-m1,m2-m1,1); }
  var T=p3[top];
  BigInteger epsNum=255, epsDen=4*p3[72];
  bool Lt(BigInteger an,BigInteger ad,BigInteger bn,BigInteger bd)=>an*bd<bn*ad;
  bool gOk=true, rOk=true; BigInteger minRes=-1;
  foreach(var v in prof.Values){
   var gLo=v.g*epsDen-epsNum*T; var gHi=v.g*epsDen+epsNum*T; var den=T*epsDen;
   var qLo=v.q*epsDen-epsNum*T; var qHi=v.q*epsDen;
   gOk&=Lt(2314,1000000,gLo,den)&&Lt(gHi,den,2340,1000000);
   rOk&=Lt(4369,1000000,gLo,qHi)&&Lt(gHi,qLo,4501,1000000);
   var res=v.q-v.g; if(minRes<0||res<minRes) minRes=res; }
  Check($"distinct profile sets {prof.Count}; 2314e-6 < g' < 2340e-6 for all", prof.Count==8&&gOk);
  Check("4369e-6 < g'/q' < 4501e-6 for all", rOk);
  // all-length bound
  BigInteger Sn=0, Sd=p3[400]; int eligible=0;
  for(int a=15;a<=400;a++){ int L=La(a); if(!(p3[a-1]<=P2(L-1))) continue; eligible++; Sn+=(Binom(L,a)/L)*p3[400-a]; }
  var tailN=BigInteger.Pow(97,401)*100; var tailD=BigInteger.Pow(100,401)*401*3;
  var Stot=Sn*tailD+tailN*Sd; var Sden=Sd*tailD;
  Check($"eligible layers {eligible}; remaining mass < 10859e-6", eligible==225&&Lt(Stot,Sden,10859,1000000));
  // 1 - mu(...) >= min(q-g)/T - eps - S > 5011/10000
  var lhsN=(minRes*epsDen-epsNum*T)*Sden-Stot*T*epsDen; var lhsD=T*epsDen*Sden;
  Check("all-length residual floor > 5011/10000", Lt(5011,10000,lhsN,lhsD));
  // ---- first coefficient crossing: smallest denominator with alpha < L/r < alpha + c/(3 N ln2) ----
  int PREC=700; BigInteger S=P2(PREC);
  BigInteger Atanh(int k){ var term=S/k; BigInteger sum=0; int j=1; while(term>0){ sum+=term/j; term/=k*k; j+=2; } return 2*sum; }
  var ln2=Atanh(3); var ln3=ln2+Atanh(5);
  BigInteger pad=P2(20);
  // alpha in (loN/loD, hiN/hiD)
  var aLoN=ln3-pad; var aLoD=ln2+pad; var aHiN=ln3+pad; var aHiD=ln2-pad;
  (BigInteger p,BigInteger q) Simplest(BigInteger an,BigInteger ad,BigInteger bn,BigInteger bd){ // simplest fraction in (an/ad, bn/bd)
    var fl=an/ad; if((fl+1)*bd<bn) return (fl+1,1);
    var r1=an-fl*ad; var r2=bn-fl*bd;
    if(r1==0){ var k=bd/r2+1; return (fl*k+1,k); }
    var (p,q)=Simplest(bd,r2,ad,r1); return (fl*p+q,p); }
  var M=2075*P2(60);
  foreach(var (name,N,rExp,Lexp,cN,cD) in new (string,BigInteger,string,string,int,int)[]{
     ("M",M,"72057431991","114208327604",3607,5000),("4M/3",4*M/3,"137528045312","217976794617",3607,5000),("2M",2*M,"137528045312","217976794617",3607,5000),
     ("2^80",P2(80),"3149971404836","4992586555009",3607,5000),("2^100",P2(100),"3816473305410548","6048967074079039",3607,5000),
     ("2^150",P2(150),"31150961018190238869556","49373105075258054570781",3607,5000),("2^272",P2(272),"144580536300674537151081081515762353325831","229154728370723013560448485454219755525522",3607,5000)}){
   // upper end: alpha_hi + cN/(cD*3*N*ln2_lo); lower end alpha_lo (outer interval, so the denominator found is a valid lower bound)
   var un=aHiN*cD*3*N*(ln2-pad)+cN*S*aHiD; var ud=aHiD*cD*3*N*(ln2-pad);
   var (p,q)=Simplest(aLoN,aLoD,un,ud);
   Check($"lower bound {name}: smallest odd count r={q}, L={p}", q.ToString()==rExp&&p.ToString()==Lexp);
  }
  Check("phase mean 1/(2 ln2)+1/31867+31867/72057431991 < 3607/5000", Lt(S*31867*72057431991L + (BigInteger)2*(ln2-pad)*72057431991L + (BigInteger)2*(ln2-pad)*31867*31867, (BigInteger)2*(ln2-pad)*31867*72057431991L,3607,5000));
  // ---- zero-tail catalogue below height H ----
  foreach(var (H,pairsExp,feasExp,two,three) in new[]{(72,2108,363,19,12),(272,30386,5098,84,53)}){
   long pairs=0,feas=0; BigInteger bn=0,bd=1; var lo=M; var hi=P2(H+1);
   for(int j=0;;j++){ int r0=R0(j); if(r0>H) break;
    for(int k=0;k<=Math.Min(j,H-r0);k++){ int s=j-k; int r=r0+k; var Q=p3[r+s]; var Pw=P2(r+2*s+k+1); pairs++;
      var res=Mod(Inv(P2(k),Q)*(1-p3[s+1]*Inv(P2(2*s+1),Q)),Q); if(res==0) res=Q;
      var y0=res+Q*(lo>res?(lo-res+Q-1)/Q:0); if(y0<hi){ feas++; if(Pw*bd>bn*Q){ bn=Pw; bd=Q; } } } }
   Check($"H={H}: pairs {pairs}, feasible in [M,2^{H+1}) {feas}, maximal slope 2^{two}/3^{three}", pairs==pairsExp&&feas==feasExp&&bn*p3[three]==bd*P2(two));
  }
  Check("(81/80) 2^19/3^12 < 1 and (501/500) 2^84/3^53 < 1", 81*P2(19)<80*p3[12]&&501*P2(84)<500*p3[53]);
  { BigInteger bn=0,bd=1; for(int j=0;;j++){ int r0=R0(j); if(r0>272) break; var Pw=P2(r0+2*j+1); var Q=p3[r0+j]; if(Pw*bd>bn*Q){bn=Pw;bd=Q;} }
    Check("whole catalogue below 2^273: maximal slope 2^569/3^359 and (1001/1000) slope < 1", bn*p3[359]==bd*P2(569)&&1001*bn<1000*bd); }
  Console.WriteLine($"failed: {fails}");
 }
}
