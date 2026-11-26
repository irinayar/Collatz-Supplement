// Independent replay of the pullback of the 120 affine certificates through prefixes p<=12.
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;

class P {
 static int fails=0; static void Check(string s,bool ok){ Console.WriteLine((ok?"ok   ":"FAIL ")+s); if(!ok) fails++; }
 static BigInteger P2(int k)=>BigInteger.One<<k;
 static BigInteger Mod(BigInteger a,BigInteger m){ var r=a%m; return r<0?r+m:r; }
 static BigInteger Inv(BigInteger a,BigInteger m){ if(m==1) return 0; BigInteger g=m,x=0,x1=1,aa=Mod(a,m); while(aa!=0){ var q=g/aa; (g,aa)=(aa,g-q*aa); (x,x1)=(x1,x-q*x1); } return Mod(x,m); }
 static (int a,int b) Split(BigInteger m){ int a=0,b=0; while(m%2==0){m/=2;a++;} while(m%3==0){m/=3;b++;} if(m!=1) throw new Exception("modulus"); return (a,b); }
 static BigInteger T(BigInteger x)=>x.IsEven?x/2:(3*x+1)/2;
 static void Main(string[] args){
  var M=2075*P2(60);
  var rules=File.ReadAllLines(args[0]).Skip(1).Where(l=>l.Length>0).Select(l=>l.Split(',')).Select(f=>(n0:BigInteger.Parse(f[1]),P:BigInteger.Parse(f[2]),m0:BigInteger.Parse(f[3]),Q:BigInteger.Parse(f[4]),w:f[5]=="-"?"":f[5],v:f[6]=="-"?"":f[6])).ToList();
  var cand=new Dictionary<(BigInteger D,BigInteger R),int>(); bool certs=true;
  for(int p=1;p<=12;p++) for(int b=1;b<(1<<p);b+=2){
    BigInteger x=b; int r=0; bool keep=true; BigInteger pw=1; for(int i=1;i<=p;i++){ if(!x.IsEven){r++;pw*=3;} x=T(x); if(pw<P2(i)){keep=false;break;} }
    if(!keep) continue; var y0=x; var A=pw;
    foreach(var c in rules){
      var g=BigInteger.GreatestCommonDivisor(A,c.P); var rhs=c.n0-y0; if(Mod(rhs,g)!=0) continue; var h=c.P/g;
      var t0=h==1?BigInteger.Zero:Mod(rhs/g*Inv(A/g,h),h); BigInteger R=b+P2(p)*t0, D=P2(p)*h;
      if(!(A*c.Q<c.P*P2(p))) continue;
      var N=R%D; if(N<=0) N+=D; if(N<M) N+=D*((M-N+D-1)/D);
      var Y=N; for(int i=0;i<p;i++) Y=T(Y); if(Y<c.n0||(Y-c.n0)%c.P!=0) continue; var mN=c.m0+c.Q*((Y-c.n0)/c.P); if(!(mN>0&&mN<N)) continue;
      var key=(D,R%D); if(!cand.ContainsKey(key)){ cand[key]=p;
        // replay the whole certificate at the first lift
        var yy=Y; foreach(var ch in c.w){ certs&=(yy.IsEven?'0':'1')==ch; yy=T(yy); } var mm=mN; foreach(var ch in c.v){ certs&=(mm.IsEven?'0':'1')==ch; mm=T(mm); } certs&=yy==mm; }
    }
  }
  bool In(BigInteger D,BigInteger R,BigInteger D2,BigInteger R2)=>D%D2==0&&R%D2==R2;
  var kept=new List<(BigInteger D,BigInteger R,int p)>();
  foreach(var kv in cand.OrderBy(k=>k.Key.D).ThenBy(k=>k.Key.R)){ var (D,R)=kv.Key; if(rules.Any(c=>In(D,R,c.P,c.n0%c.P))||kept.Any(k=>In(D,R,k.D,k.R))) continue; kept.Add((D,R,kv.Value)); }
  Check("certificate replay at the first lift of every candidate", certs);
  var byP=string.Join(",",Enumerable.Range(1,12).Select(p=>kept.Count(k=>k.p==p)));
  Check($"retained {kept.Count}; by p: {byP}", kept.Count==232&&byP=="0,0,9,1,0,9,2,0,16,1,108,86");
  // exact masses: binary trie, ternary unions in the leaves, refined to depth 12
  var baseC=rules.Select(c=>{ var (a,b)=Split(c.P); return (a:a,rb:c.n0%P2(a),b:b,rt:c.n0%BigInteger.Pow(3,b)); }).ToList();
  var addC=kept.Select(k=>{ var (a,b)=Split(k.D); return (a:a,rb:k.R%P2(a),b:b,rt:k.R%BigInteger.Pow(3,b)); }).ToList();
  int amax=Math.Max(12,Math.Max(baseC.Max(c=>c.a),addC.Max(c=>c.a))); int bmax=Math.Max(baseC.Max(c=>c.b),addC.Max(c=>c.b));
  var p3=Enumerable.Range(0,bmax+1).Select(i=>BigInteger.Pow(3,i)).ToArray();
  BigInteger TU(IEnumerable<(int b,BigInteger rt)> cyl){ var set=new SortedDictionary<int,HashSet<BigInteger>>(); BigInteger tot=0; foreach(var (b,rt) in cyl.OrderBy(c=>c.b)){ bool cov=false; foreach(var kv in set){ if(kv.Key>b) break; if(kv.Value.Contains(rt%p3[kv.Key])){cov=true;break;} } if(cov) continue; if(!set.TryGetValue(b,out var h)) set[b]=h=new(); h.Add(rt); tot+=p3[bmax-b]; } return tot; }
  BigInteger baseM=0, addM=0, survOut=0, addSurv=0; long leaves=0;
  void Rec(int d,BigInteger res,List<(int a,BigInteger rb,int b,BigInteger rt)> bc,List<(int a,BigInteger rb,int b,BigInteger rt)> ac){
   bool split=d<12||bc.Any(c=>c.a>d)||ac.Any(c=>c.a>d);
   if(split){ foreach(var bit in new[]{0,1}){ var nr=res+(bit==1?P2(d):0); var mod=P2(d+1);
       Rec(d+1,nr,bc.Where(c=>c.a<=d||c.rb%mod==nr).ToList(),ac.Where(c=>c.a<=d||c.rb%mod==nr).ToList()); } return; }
   leaves++; var weight=P2(amax-d);
   var u0=TU(bc.Select(c=>(c.b,c.rt))); var u1=TU(bc.Concat(ac).Select(c=>(c.b,c.rt)));
   baseM+=weight*u0; addM+=weight*(u1-u0);
   BigInteger x=res%4096; if(x==0) x=4096; bool surv=true; BigInteger pw=1; for(int i=1;i<=12;i++){ if(!x.IsEven) pw*=3; x=T(x); if(pw<P2(i)){surv=false;break;} }
   if(surv){ survOut+=weight*(p3[bmax]-u0); addSurv+=weight*(u1-u0); } }
  Rec(0,0,baseC,addC);
  var den=P2(amax)*p3[bmax];
  bool Eq(BigInteger num,string a,string b)=>num*BigInteger.Parse(b)==BigInteger.Parse(a)*den;
  Console.WriteLine($"info leaves {leaves}; max exponents 2^{amax} 3^{bmax}");
  Check("baseline mass", Eq(baseM,"22077787551487997615578945","23554621393597287150649344"));
  Check("additional union mass", Eq(addM,"8405263598267714121179320873","192959458456348976338119426048"));
  Check("depth-12 survivors outside baseline", Eq(survOut,"645233726230513471938751","23554621393597287150649344"));
  Check("additional union in that stratum", Eq(addSurv,"1592795448988780612004860457","192959458456348976338119426048"));
  Check("relative reduction 0.3013373...", addSurv*10000000>survOut*3013373&&addSurv*10000000<survOut*3013374);
  Check("example: 59 mod 128 retained; partner", kept.Any(k=>k.D==128&&k.R==59));
  Console.WriteLine($"failed: {fails}");
 }
}
