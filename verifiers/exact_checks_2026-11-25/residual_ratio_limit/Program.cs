// Harmonic (conserved-weight) bounds for the limiting residual factor: depth-53 bound, exact recurrence to 10000, double recurrence to 10^6.
// args: ledger.csv projected181.csv certificates_e0to6.csv direct7.sorted residual821.csv (needs replay_fraction_type.cs.txt)
using System;
using System.IO;
using System.Linq;
using System.Collections.Generic;
using System.Numerics;

// Independent check of the residual stabilization claim: depth-53 joint rows, order, six polynomial certificates,
// recurrence versus closed formulas, ratios through 512, the first non-monotone step and the limit enclosures.
// args: ledger.csv projected181.csv certificates_e0to6.csv direct7.sorted residual821.csv
class P {
 static BigInteger P2(int k)=>BigInteger.One<<k;
 static readonly BigInteger[] p3=Enumerable.Range(0,1100).Select(i=>BigInteger.Pow(3,i)).ToArray();
 static F Q(BigInteger a,BigInteger b)=>new F(a,b);
 static List<(BigInteger res,int j)> act;
 static F Unc(BigInteger pre,int d){
  bool deeper=false;
  foreach(var (res,j) in act){ if(j<=d){ if(pre%p3[j]==res) return new F(0,1); } else if(res%p3[d]==pre) deeper=true; }
  if(!deeper) return new F(1,1);
  F s=0; for(int c=0;c<3;c++) s+=Unc(pre+c*p3[d],d+1); return s/(F)3;
 }
 static readonly BigInteger L0=10460353203;
 struct V3 { public BigInteger N,V,P; }
 static void Add(Dictionary<(int a,int s),V3> T,(int,int) k,V3 v,int sign=1){ T.TryGetValue(k,out var o); o.N+=sign*v.N; o.V+=sign*v.V; o.P+=sign*v.P; T[k]=o; }
 static int Next(int s,int bit)=> s==3?3 : s==2?(bit==0?-1:3) : (bit==1?1:2);
 static Dictionary<(int,int),V3> Step(Dictionary<(int a,int s),V3> S,int d){
  var T=new Dictionary<(int,int),V3>();
  foreach(var kv in S) for(int bit=0;bit<2;bit++){ int a=kv.Key.a+bit; if(p3[a]<P2(d)) continue; int s=Next(kv.Key.s,bit); if(s<0) continue; Add(T,(a,s),kv.Value); }
  return T;
 }
 static List<int> Bits(BigInteger r,int e){ var w=new List<int>(); var x=r; for(int i=0;i<e;i++){ int b=x.IsEven?0:1; w.Add(b); x=b==1?(3*x+1)/2:x/2; } return w; }
 static (bool,int,int) Walk(List<int> w){ int a=0,s=1; for(int i=0;i<w.Count;i++){ a+=w[i]; if(p3[a]<=P2(i+1)) return (false,a,s); s= i==0?(w[0]==1?1:3):Next(s,w[i]); if(s<0) return (false,a,s); } return (true,a,s); }

 static void Main(string[] args){
  var rows=File.ReadAllLines(args[0]).Skip(1).Select(l=>l.Split(',')).Select(f=>(res:BigInteger.Parse(f[1]),mod:BigInteger.Parse(f[2]))).ToList();
  var mixed=new List<(int i,BigInteger bres,int j,BigInteger tres)>();
  foreach(var (res,mod) in rows){ int i=0,j=0; var m=mod; while(m%2==0){m/=2;i++;} while(m%3==0){m/=3;j++;} if(j>0) mixed.Add((i,res%P2(i),j,res%p3[j])); }
  var cache=new Dictionary<long,BigInteger>();
  BigInteger QL(long r11){ if(cache.TryGetValue(r11,out var v)) return v; act=mixed.Where(r=>(r11-r.bres)%P2(r.i)==0).Select(r=>(r.tres,r.j)).ToList(); var s=Unc(0,0)*(F)L0; cache[r11]=s.n; return s.n; }
  var cyl=File.ReadAllLines(args[1]).Skip(1).Select(l=>l.Split(',')).Select(f=>(res:BigInteger.Parse(f[0]),e:int.Parse(f[1]))).ToList();
  var words=cyl.Select(c=>Bits(c.res,c.e)).ToList();
  const int B0=13;
  var shortCyl=words.Where(w=>w.Count<=B0).ToList();
  var tag=new Dictionary<int,(bool parent,BigInteger ql)>();
  var S=new Dictionary<(int,int),V3>();
  for(int r=0;r<(1<<B0);r++){
   var w=Bits(r==0?(1<<B0):r,B0); var (alive,a,s)=Walk(w); if(!alive) continue;
   if(shortCyl.Any(c=>c.SequenceEqual(w.Take(c.Count)))) continue;
   var ql=QL(r%2048); tag[r]=(r==103,ql); Add(S,(a,s),new V3{N=1,V=ql,P=r==103?1:0});
  }
  for(int d=B0+1;d<=53;d++) S=Step(S,d);
  void Remove(Dictionary<(int,int),V3> T,List<int> w,int r13){
   var (alive,a,s)=Walk(w); if(!alive||!tag.ContainsKey(r13)) return; var t=tag[r13];
   var one=new Dictionary<(int,int),V3>{{(a,s),new V3{N=1,V=t.ql,P=t.parent?1:0}}};
   for(int d=w.Count+1;d<=53;d++) one=Step(one,d);
   foreach(var kv in one) Add(T,kv.Key,kv.Value,-1);
  }
  foreach(var c in cyl.Where(c=>c.e>B0)){ var w=Bits(c.res,c.e); if(w.Count>53) w=w.Take(53).ToList(); Remove(S,w,(int)(c.res%(1<<B0))); }
  // cumulative local masks, budgets 0..9
  var mask=new Dictionary<int,long>();
  foreach(var f in File.ReadLines(args[2]).Skip(1).Select(l=>l.Split(','))) mask[int.Parse(f[2])]=mask.GetValueOrDefault(int.Parse(f[2]))+1;
  foreach(var f in File.ReadLines(args[3]).Skip(1).Select(l=>l.Split(','))) mask[int.Parse(f[2])]=mask.GetValueOrDefault(int.Parse(f[2]))+1;
  foreach(var (a,n) in new[]{(26,16874L),(27,205211L),(28,417656L),(26,54314L),(27,443381L)}) mask[a]=mask.GetValueOrDefault(a)+n;
  var QLpar=(Q(2519180,4782969)*(F)L0).n;
  var M=new Dictionary<(int,int),V3>(); foreach(var kv in mask) Add(M,(kv.Key,3),new V3{N=kv.Value,V=kv.Value*QLpar,P=kv.Value});
  for(int d=42;d<=53;d++) M=Step(M,d);
  foreach(var kv in M) Add(S,kv.Key,kv.Value,-1);
  // the 149 equal-count cylinders
  var hits=Hits149(); Chk.A(hits.Count==149,"149");
  foreach(var (L,r) in hits) Remove(S,Bits(r,L),(int)(r%(1<<B0)));
  var S149=new Dictionary<(int,int),V3>(S);
  // 821 survivors
  var s821=File.ReadAllLines(args[4]).Skip(1).Where(l=>l.Length>0).Select(l=>long.Parse(l.Split(',')[0])).ToList(); Chk.A(s821.Count==821,"821");
  var R=new Dictionary<(int,int),V3>(); foreach(var kv in S149) R[kv.Key]=kv.Value;
  foreach(var r in s821) Remove(S,Bits(r,41),(int)(r%(1<<B0)));
  var ratio=Q(0,1); foreach(var kv in R){ if(kv.Value.P>0){ var rem=kv.Value.P-(S.ContainsKey(kv.Key)?S[kv.Key].P:0); var fr=Q(rem,kv.Value.P); if(fr>ratio) ratio=fr; } }
  Console.WriteLine($"max parent fraction removed by the 821: {ratio}"); Chk.A(ratio==Q(131587,4098305534),"821 parent fraction");
  bool Order(Dictionary<(int,int),V3> T){ var es=T.Where(k=>k.Key.Item2==3).ToDictionary(k=>k.Key.Item1,k=>(N:k.Value.N,H:QLpar*k.Value.N-k.Value.V,P:k.Value.P)); var ks=es.Keys.OrderBy(a=>a).ToList(); bool ok=ks.Count==19&&ks[0]==34&&ks[^1]==52; for(int i=0;i+1<ks.Count;i++){ var x=es[ks[i]]; var y=es[ks[i+1]]; ok&=x.H>0&&y.H>0&&y.H*x.N<x.H*y.N&&y.H*(x.N-x.P)<x.H*(y.N-y.P)&&y.P*x.N<=x.P*y.N; } return ok&&es[34].P>0&&es[52].P==0; }
  var S9=new Dictionary<(int,int),V3>(); foreach(var kv in S149) S9[kv.Key]=kv.Value; foreach(var (L,r) in hits) { } Console.WriteLine($"order after +149: {Order(S149)}; after +821: {Order(S)}"); Chk.A(Order(S149)&&Order(S),"nested orders");
  // family j=15..45
  for(int j=15;j<=45;j++){ var w=Enumerable.Repeat(1,j).Concat(new[]{0,1,0,0,0,0,0,1}).ToList(); int a=j+2;
   BigInteger C=0; for(int i=0;i<w.Count;i++) if(w[i]==1) C=3*C+P2(i);
   BigInteger mod=P2(B0), inv=1; for(int it=0;it<8;it++) inv=((inv*(2-p3[a]*inv))%mod+mod)%mod; int r13=(int)(((-C*inv)%mod+mod)%mod);
   Remove(S,w,r13); }
  // base rows and order
  var base7=new (BigInteger N,BigInteger H,BigInteger P)[8];
  var esc=S.Where(k=>k.Key.Item2==3).ToDictionary(k=>k.Key.Item1,k=>(N:k.Value.N,H:QLpar*k.Value.N-k.Value.V,P:k.Value.P));
  for(int e=1;e<=7;e++){ var x=esc[53-e]; base7[e]=(x.N,x.H,x.P); }
  var claimed=new (long N,long H,long P)[]{(0,0,0),(50,129140163,0),(1224,6199790716,0),(19542,145072233188,0),(228715,2205344110942,1),(2091187,24490943127370,40),(15544260,211801631162230,752),(96514513,1484661329575208,9119)};
  bool tableOk=Enumerable.Range(1,7).All(e=>base7[e].N==claimed[e].N&&base7[e].H==claimed[e].H&&base7[e].P==claimed[e].P);
  Console.WriteLine($"top-seven depth-53 rows equal the stated table: {tableOk}; escaped counts a={esc.Keys.Min()}..{esc.Keys.Max()}"); Chk.A(tableOk,"table");
  var keys=esc.Keys.OrderBy(a=>a).ToList(); bool order=keys.Count==19&&keys[0]==34&&keys[^1]==52;
  foreach(var a in keys){ var x=esc[a]; order&=x.N>x.P&&x.P>=0&&x.H>0; }
  for(int i=0;i+1<keys.Count;i++){ var x=esc[keys[i]]; var y=esc[keys[i+1]];
   order&= y.H*x.N < x.H*y.N;                      // global factor strictly increases
   order&= y.H*(x.N-x.P) < x.H*(y.N-y.P);          // off-parent factor strictly increases
   order&= y.P*x.N <= x.P*y.N; }                   // parent share nonincreasing
  order&=esc[34].P>0&&esc[52].P==0;
  Console.WriteLine($"statewise order at depth 53: {order}"); Chk.A(order,"order");
  // ---- harmonic upper bound for the limiting factor ----
  double th=Math.Log(2)/Math.Log(3), beta=Math.Log(2), ln3=Math.Log(3);
  // V(x)=lim E_x[Z_n;tau>n] for the theta-walk Z=a ln3 - d ln2 killed at Z<=0; enclosure f<=V<=f+beta*m.
  (Dictionary<int,double> lo, Dictionary<int,double> hi) VBounds(int D,int amin,int amax,int n){
   const int W=3500; // heights kept above the barrier
   int Bar(int d){ return (int)Math.Floor(d*th)+1; } // least a with 3^a>2^d, d>=1
   int dEnd=D+n; int b0=Bar(dEnd); var f=new double[W+2]; var m=new double[W+2];
   for(int i=0;i<=W+1;i++){ f[i]=(b0+i)*ln3-dEnd*beta; m[i]=1; }
   for(int d=dEnd-1;d>=D;d--){
    int b=Bar(d), nb=Bar(d+1), sh=nb-b; var nf=new double[W+2]; var nm=new double[W+2];
    for(int i=0;i<=W+1;i++){
     int a=b+i; int i1=a+1-nb, i0=a-nb; double ff=0, mm=0;
     if(i1>W+1){ ff+=th*((a+1)*ln3-(d+1)*beta); mm+=th; } else if(i1>=0){ ff+=th*f[i1]; mm+=th*m[i1]; }
     if(i0>W+1){ ff+=(1-th)*(a*ln3-(d+1)*beta); mm+=1-th; } else if(i0>=0){ ff+=(1-th)*f[i0]; mm+=(1-th)*m[i0]; }
     nf[i]=ff; nm[i]=mm; }
    f=nf; m=nm; }
   var lo=new Dictionary<int,double>(); var hi=new Dictionary<int,double>(); int bD=Bar(D);
   for(int a=amin;a<=amax;a++){ lo[a]=f[a-bD]*(1-1e-9); hi[a]=(f[a-bD]+beta*m[a-bD])*(1+1e-9); }
   return (lo,hi);
  }
  double Qd=2519180.0/4782969.0;
  var Tm=new Dictionary<(int,int),V3>(S);
  for(int d=53;d<=512;d++){
   if(d>53){ Tm=Step(Tm,d); Add(Tm,(d-6,3),new V3{N=1,V=QLpar,P=0},-1); }
   if(d!=53) continue;
   var st=new SortedDictionary<int,(BigInteger N,BigInteger H,BigInteger P)>();
   foreach(var kv in Tm){ st.TryGetValue(kv.Key.Item1,out var o); o.N+=kv.Value.N; o.H+=QLpar*kv.Value.N-kv.Value.V; if(kv.Key.Item2==3) o.P+=kv.Value.P; else Chk.A(kv.Value.P==0&&QLpar*kv.Value.N==kv.Value.V,"pending H=P=0"); st[kv.Key.Item1]=o; }
   var ks=st.Keys.ToList(); bool mono=true;
   for(int i=0;i+1<ks.Count;i++){ var x=st[ks[i]]; var y=st[ks[i+1]];
    mono&= y.H*x.N<=x.H*y.N && y.H*(x.N-x.P)<=x.H*(y.N-y.P) && y.P*x.N<=x.P*y.N; }
   Chk.A(mono,"monotone H/N, H/(N-P), P/N with pending included");
   var (lo,hi)=VBounds(d,ks[0],ks[^1],d==53?1600000:200000);
   double scale=Math.Pow(2,-(d-40));
   double HL=0,NH=0,NpH=0,PL=0;
   foreach(var a in ks){ var x=st[a];
    double w=Math.Exp(a*Math.Log(th)+(d-a)*Math.Log(1-th));
    HL+=w*lo[a]*(double)x.H; NH+=w*hi[a]*(double)x.N; NpH+=w*hi[a]*(double)(x.N-x.P); PL+=w*lo[a]*(double)x.P; }
   // matching non-rigorous midpoint (central value of V)
   double Hm=0,Nm=0,Pm=0; foreach(var a in ks){ var x=st[a]; double w=Math.Exp(a*Math.Log(th)+(d-a)*Math.Log(1-th))*(lo[a]+hi[a])/2; Hm+=w*(double)x.H; Nm+=w*(double)x.N; Pm+=w*(double)x.P; }
   double U=Qd-HL/NH/(double)L0, Uoff=Qd-HL/NpH/(double)L0, Pl=PL/NH;
   Console.WriteLine($"D={d} states a={ks[0]}..{ks[^1]} monotone={mono}: q_inf<= {U:F10}  qoff_inf<= {Uoff:F10}  p_inf>= {Pl:F12} | midpoint q {Qd-Hm/Nm/(double)L0:F10} p {Pm/Nm:F12}; V width at a={ks[ks.Count/2]}: {hi[ks[ks.Count/2]]-lo[ks[ks.Count/2]]:E2}");
   // ---- numerical test of the ratio limit theorem and of the exact-limit formula ----
   {
    var Vm=new Dictionary<int,double>(); foreach(var a in ks) Vm[a]=(lo[a]+hi[a])/2;
    double rr=th/(1-th); int Bar2(int t)=>(int)Math.Floor(t*th)+1;
    foreach(int n in new[]{1000,10000,100000,400000}){
     const int W=3000; int E=53+n; var g=new double[W+1]; for(int i=0;i<=W;i++) g[i]=Math.Pow(rr,-i);
     var ng=new double[W+1];
     for(int t=E-1;t>=53;t--){
      int b=Bar2(t), nb=Bar2(t+1), sh=nb-b;
      for(int i=0;i<=W;i++){ int e=i-sh, o=e+1; double v=0; if(e>=0&&e<=W) v+=(1-th)*g[e]; if(o>=0&&o<=W) v+=th*g[o]; ng[i]=v; }
      double s=ng[10]; for(int i=0;i<=W;i++) ng[i]/=s; (g,ng)=(ng,g);
     }
     // S_n(53,a) is proportional to g[a-34]*rr^(a-34); the theorem says g[a-34]/g[10] -> V(a)/V(44)
     double maxdev=0; bool below=true;
     foreach(var a in ks){ double gr=g[a-34]/g[10], target=Vm[a]/Vm[44]; maxdev=Math.Max(maxdev,Math.Abs(gr/target-1));
       if(a>44) below&=gr<=hi[a]/lo[44]; }
     Console.WriteLine($"ratio test n={n}: max relative deviation from midpoint V ratio {maxdev:E3}; upper inequality for a>44 holds {below}; a=34 {g[0]/g[10]:F6} vs {Vm[34]/Vm[44]:F6}; a=53 {g[19]/g[10]:F6} vs {Vm[53]/Vm[44]:F6}");
    }
    // exact-limit denominator M against the bound's denominator sum h N (pending counted once)
    double H53(int dd,int a,double V)=>Math.Exp(a*Math.Log(th)+(dd-a)*Math.Log(1-th))*V;
    double VZ(int dd,int a)=>a*ln3-dd*beta+beta/2;
    double sumN=0,sumH=0; foreach(var a in ks){ sumN+=H53(53,a,Vm[a])*(double)st[a].N; sumH+=H53(53,a,Vm[a])*(double)st[a].H; }
    double pend=H53(53,52,Vm[52])+H53(53,53,Vm[53]);
    double exits=0; for(int m=52;m<=900;m++) exits+=H53(m+2,m+1,VZ(m+2,m+1));
    double fam=0; for(int j=46;j<=900;j++) fam+=H53(j+8,j+2,VZ(j+8,j+2));
    double Mlim=sumN-pend+exits-fam;
    Console.WriteLine($"M relative defect (sumN-M)/sumN = {(sumN-Mlim)/sumN:E3}; pend {pend/sumN:E3} exits {exits/sumN:E3} family {fam/sumN:E3}");
    Console.WriteLine($"midpoint bound U={Qd-sumH/sumN/(double)L0:F13}  midpoint exact-limit formula={Qd-sumH/Mlim/(double)L0:F13}  difference {sumH/(double)L0*(1/Mlim-1/sumN):E3}");
   }
  }
  // exact integer recurrence from depth 512 to 10000, including the family removals and the two pending words
  {
   const int D=10000;
   var N=new BigInteger[D+2]; var H=new BigInteger[D+2]; var Pp=new BigInteger[D+2]; // escaped states indexed by a
   int pendA=0, pendB=0;
   foreach(var kv in Tm){ int a=kv.Key.Item1; if(kv.Key.Item2==3){ N[a]+=kv.Value.N; H[a]+=QLpar*kv.Value.N-kv.Value.V; Pp[a]+=kv.Value.P; }
     else { Chk.A(kv.Value.N==1&&(a==512||a==511),"pending words"); if(a==512) pendA++; else pendB++; } }
   Chk.A(pendA==1&&pendB==1,"two pending words");
   int bar=324; while(p3[0]!=1){}
   BigInteger pow3=BigInteger.Pow(3,bar); BigInteger pow2=BigInteger.One<<512; Chk.A(pow3>pow2&&pow3/3<pow2,"barrier at 512");
   int top=512;
   for(int d=513;d<=D;d++){
    pow2<<=1;
    var nbar=bar; if(pow3<pow2){ nbar=bar+1; pow3*=3; }
    // new state a comes from a (even step) and a-1 (odd step); states below the barrier are dropped
    for(int a=top+1;a>=nbar;a--){ N[a]+=N[a-1]; H[a]+=H[a-1]; Pp[a]+=Pp[a-1]; }
    for(int a=bar;a<nbar;a++){ N[a]=0; H[a]=0; Pp[a]=0; }
    bar=nbar; top++;
    N[d-1]+=1;      // the pending word 1^(d-2)0 followed by 1 escapes
    N[d-6]-=1;      // the one new family word (factor Q: H and P unchanged)
    if(d==1000||d==10000){
     BigInteger sn=0,sh2=0,sp=0; for(int a=bar;a<=top;a++){ sn+=N[a]; sh2+=H[a]; sp+=Pp[a]; }
     BigInteger W=2*sn+2, Hs=2*sh2, Ps=2*sp;            // escaped weight 2, the two pending words weight 1
     var qv=Q(2519180,4782969)-Q(Hs,W*L0); var pv=Q(Ps,W);
     var qoffv=Q(2519180,4782969)-Q(Hs,(W-Ps)*L0);
     Console.WriteLine($"exact d={d}: q={qv.ToDouble():F12} qoff={qoffv.ToDouble():F12} p={pv.ToDouble():F14}");
     if(d==10000){ Chk.A(qv>Q(524468423,1000000000),"q lower"); Chk.A(qoffv>Q(524466,1000000),"qoff lower coarse"); Chk.A(pv<Q(690600,1000000000),"p upper");
       Console.WriteLine($"exact: q>0.524468423 {qv>Q(524468423,1000000000)}; qoff>0.524466882 {qoffv>Q(524466882,1000000000)}; p<0.000690600 {pv<Q(690600,1000000000)}"); }
    }
   }
  }
  // forward recurrence from depth 512 in the theta-weighted variables M_a = N_a theta^(a-b) (1-theta)^-(a-b), stable at all depths
  {
   const int W=4000; double rho=th/(1-th);
   int Bar(int d)=>(int)Math.Floor(d*th)+1;
   var N=new double[W+1]; var H=new double[W+1]; var Pp=new double[W+1];
   int d0=512, b=Bar(d0); double scale0=Math.Pow(2,-500);
   foreach(var kv in Tm){ int i=kv.Key.Item1-b; double w=(kv.Key.Item2==3?2:1)*Math.Pow(rho,i)*scale0; Chk.A(i>=0&&i<=W,"in range");
    N[i]+=w*(double)kv.Value.N; H[i]+=w*(double)(QLpar*kv.Value.N-kv.Value.V); Pp[i]+=w*(double)kv.Value.P; }
   var nN=new double[W+1]; var nH=new double[W+1]; var nP=new double[W+1];
   double prevQ=0, prevP=1; bool incr=true;
   for(int d=d0+1;d<=1000000;d++){
    int nb=Bar(d), sh=nb-b; double tot=0;
    for(int i=0;i<=W;i++){ int e=i+sh, o=e-1; // a=nb+i from a (even, weight 1-theta) and a-1 (odd, weight theta)
     double n=0,h=0,p=0;
     if(e<=W){ n=(1-th)*N[e]; h=(1-th)*H[e]; p=(1-th)*Pp[e]; }
     if(o>=0&&o<=W){ n+=th*N[o]; h+=th*H[o]; p+=th*Pp[o]; }
     nN[i]=n; nH[i]=h; nP[i]=p; tot+=n; }
    // the state index is a-b, so a barrier advance rescales the weights by a constant factor only
    double inv=1/tot; for(int i=0;i<=W;i++){ nN[i]*=inv; nH[i]*=inv; nP[i]*=inv; }
    (N,nN)=(nN,N); (H,nH)=(nH,H); (Pp,nP)=(nP,Pp); b=nb;
    if(d==513||d==1000||d==10000||d==100000||d==300000||d==1000000){
     double sn=0,sh2=0,sp=0,w=1; for(int i=0;i<=W;i++){ sn+=N[i]*w; sh2+=H[i]*w; sp+=Pp[i]*w; w/=rho; }
     double qv=Qd-sh2/sn/(double)L0, pv=sp/sn; incr&=qv>=prevQ&&pv<=prevP; prevQ=qv; prevP=pv;
     Console.WriteLine($"forward d={d}: q={qv:F12} p={pv:F14} top weighted mass {N[W]:E1}"); }
   }
   Chk.A(incr,"sampled q increasing, p decreasing");
  }
  {
   F S42=F.Of("3442126137756879465367893417111436/443426488243037769948249630619149892803");
   int r47=2; while(!(p3[r47+47]>P2(r47+95))) r47++; var Shi=S42+Q(3,2*p3[r47+47]);
   double qlo=0.524469271, qhi=0.524471204;
   Console.WriteLine($"gain bounds: {2*S42.ToDouble()/qhi:E12} .. {2*Shi.ToDouble()/qlo:E12}");
  }
  Console.WriteLine($"checks passed {Chk.pass}, failed {Chk.fail}");
 }
 static List<(int L,long r)> Hits149(){
  var hits=new List<(int,long)>(); var q3=new long[24]; q3[0]=1; for(int i=1;i<24;i++)q3[i]=q3[i-1]*3;
  var Cp=new long[1]{0}; var ap=new byte[1]{0}; var okp=new bool[1]{true}; var dp=new bool[1]{false};
  for(int L=1;L<=22;L++){ int n=1<<L; var C=new long[n]; var a=new byte[n]; var ok=new bool[n]; var dead=new bool[n]; long half=1L<<(L-1);
   for(int w=0;w<n;w++){ int pre=w&(int)(half-1), bit=w>>(L-1); a[w]=(byte)(ap[pre]+bit); C[w]=bit==1?3*Cp[pre]+half:Cp[pre];
    bool al=okp[pre]&&q3[a[w]]>(1L<<L); if(al){ int t=0; while(t<L&&((w>>t)&1)==1)t++; if(t>=1&&t+1<L&&((w>>t)&3)==0) al=false; } ok[w]=al; dead[w]=dp[pre]; }
   var max=new Dictionary<(int,long),long>();
   for(int w=0;w<n;w++){ var k=((int)a[w],C[w]%q3[a[w]]); if(!max.TryGetValue(k,out var m)||C[w]>m) max[k]=C[w]; }
   for(int w=0;w<n;w++){ if(!ok[w]||dead[w]) continue; if(max[((int)a[w],C[w]%q3[a[w]])]>C[w]){ long mod=1L<<L; BigInteger inv=1; for(int it=0;it<6;it++) inv=(inv*(2-(BigInteger)q3[a[w]]*inv))%mod; inv=(inv+mod)%mod;
       hits.Add((L,(long)(((-(BigInteger)C[w]*inv)%mod+mod)%mod))); dead[w]=true; } }
   Cp=C; ap=a; okp=ok; dp=dead; }
  return hits;
 }
}
