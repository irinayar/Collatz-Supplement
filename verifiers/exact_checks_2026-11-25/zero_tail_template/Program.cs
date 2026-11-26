// Independent replay of the zero-tail template bounds against the 119-rule ledger and C121.
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;

class P {
 static int fails=0; static void Check(string s,bool ok){ Console.WriteLine((ok?"ok   ":"FAIL ")+s); if(!ok) fails++; }
 static BigInteger[] p3=Enumerable.Range(0,200).Select(i=>BigInteger.Pow(3,i)).ToArray();
 static BigInteger Mod(BigInteger a,BigInteger m){ var r=a%m; return r<0?r+m:r; }
 static BigInteger Inv(BigInteger a,BigInteger m){ BigInteger g=m,x=0,x1=1,aa=Mod(a,m); while(aa!=0){ var q=g/aa; (g,aa)=(aa,g-q*aa); (x,x1)=(x1,x-q*x1); } return Mod(x,m); }
 static int R0(int j){ int r=2; while(!(BigInteger.Pow(3,r+j)>(BigInteger.One<<(r+2*j+1)))) r++; return r; }
 static (BigInteger res,int e) F(int k,int s){ int r=k+R0(k+s); var q=p3[r+s]; var res=Mod(Inv(BigInteger.One<<k,q)*(1-p3[s+1]*Inv(BigInteger.One<<(2*s+1),q)),q); return (res,r+s); }
 // union measure of ternary cylinders, as numerator over 3^top
 static BigInteger Union(IEnumerable<(BigInteger res,int e)> cyl,int top){
  var kept=new SortedDictionary<int,HashSet<BigInteger>>(); BigInteger total=0;
  foreach(var c in cyl.OrderBy(c=>c.e)){
   bool covered=false; foreach(var kv in kept){ if(kv.Key>c.e) break; if(kv.Value.Contains(c.res%p3[kv.Key])){ covered=true; break; } }
   if(covered) continue; if(!kept.TryGetValue(c.e,out var h)) kept[c.e]=h=new(); h.Add(c.res); total+=p3[top-c.e];
  }
  return total;
 }
 static void Main(string[] args){
  var rows=File.ReadAllLines(args[0]).Skip(1).Select(l=>l.Split(',')).Select(f=>(res:BigInteger.Parse(f[1]),mod:BigInteger.Parse(f[2]))).ToList();
  var mixed=new List<(int i,BigInteger b,BigInteger t,int e)>();
  foreach(var (res,mod) in rows){ int i=0,j=0; var m=mod; while(m%2==0){m/=2;i++;} while(m%3==0){m/=3;j++;} if(j>0) mixed.Add((i,res%(BigInteger.One<<i),res%p3[j],j)); }
  Check($"ledger rows {rows.Count}, mixed {mixed.Count}, maximal binary exponent {mixed.Max(x=>x.i)}", rows.Count==119&&mixed.Count==103&&mixed.Max(x=>x.i)<=11);
  mixed.Add((6,303%64,303%81,4)); // C121: 303 mod 5184
  const int J=40; int e41=41+R0(41); Check($"e_41={e41}", e41==72);
  var U=new List<(BigInteger,int)>(); var O=new List<(BigInteger,int)>();
  for(int k=0;k<=J;k+=2) for(int s=(k==0?0:1);k+s<=J;s++){ if(k!=0&&k%6==4) continue; var c=F(k,s); U.Add(c); if(k==0||k==2||k==6||k==8||k==12) O.Add(c); }
  Check($"retained rows: old {O.Count}, new {U.Count-O.Count}", O.Count==173&&U.Count-O.Count==122);
  // proof identities on a sample of the family, including the actual orbit
  bool orbit=true;
  foreach(var (k,s) in new[]{(0,0),(0,3),(2,1),(6,2),(8,5),(12,1),(14,1),(18,4)}){
   var (res,e)=F(k,s); int r=e-s; var n=res+p3[e]*5; var X=(BigInteger.One<<(2*s))*((BigInteger.One<<(k+1))*n-2)+p3[s+1]; var m=(BigInteger.One<<r)*X/p3[e]-1;
   orbit&=((BigInteger.One<<r)*X)%p3[e]==0&&m>0&&m<n;
   var word=new string('1',r)+string.Concat(Enumerable.Repeat("01",s))+new string('0',k+1); var x=m;
   foreach(var ch in word){ orbit&= (x.IsEven?'0':'1')==ch; x=x.IsEven?x/2:(3*x+1)/2; }
   orbit&=x==n;
  }
  Check("sample classes: smaller origin follows 1^r (01)^s 0^(k+1) and reaches n", orbit);
  // gains over all binary residues
  int top=Math.Max(e41,U.Max(c=>c.Item2)); var G=new HashSet<BigInteger>(); BigInteger minq=-1,maxq=0; int profiles; var prof=new HashSet<string>();
  for(int b=0;b<2048;b++){
   var L=mixed.Where(x=>(b%(1<<x.i))==x.b).Select(x=>(x.t,x.e)).ToList();
   var key=string.Join(";",L.OrderBy(c=>c.e).ThenBy(c=>c.t).Select(c=>$"{c.t}/{c.e}"));
   if(!prof.Add(key)) continue;
   var a=Union(L.Concat(O),top); var bb=Union(L.Concat(U),top); G.Add(bb-a); var q=p3[top]-a; if(minq<0||q<minq) minq=q; if(q>maxq) maxq=q;
  }
  Console.WriteLine($"distinct mixed profiles {prof.Count}; top exponent {top}; distinct truncated gains {G.Count}");
  var g=G.First();
  var gn=BigInteger.Parse("378657549860866656317"); var gd=BigInteger.Parse("7509466514979724803946715958257547");
  Check("truncated gain is the same for every residue and equals the stated fraction", G.Count==1 && g*gd==gn*p3[top]);
  // tails: eps_U=255/(4*3^e41), eps_O=15/(2*3^e41); work over den = 4*3^top
  BigInteger den=4*p3[top], epsU=255*p3[top-e41], epsO=30*p3[top-e41];
  BigInteger gLo=4*g-epsO, gHi=4*g+epsU;
  bool Lt(BigInteger an,BigInteger ad,BigInteger bn,BigInteger bd)=>an*bd<bn*ad;
  var T=BigInteger.Pow(10,28);
  Check("5.04240280059214e-14 < g_b < 5.04240280059215e-14", Lt(BigInteger.Parse("504240280059214"),T,gLo,den)&&Lt(gHi,den,BigInteger.Parse("504240280059215"),T));
  BigInteger qLo=4*minq-epsO, qHi=4*maxq;
  Check("9.4e-14 < g_b/q_b < 9.9e-14", Lt(94,BigInteger.Pow(10,15),gLo,qHi)&&Lt(gHi,qLo,99,BigInteger.Pow(10,15)));
  Console.WriteLine($"q_b range about {(double)(minq*1000000000/p3[top])/1e9:F9} .. {(double)(maxq*1000000000/p3[top])/1e9:F9}");
  // explicit F(14,1)
  var f=F(14,1); var n0=BigInteger.Parse("5442907506622"); var m0=BigInteger.Parse("4185579847679");
  Check($"F(14,1): residue {f.res} mod 3^{f.e}", f.res==n0&&f.e==28);
  var y=m0; var w=new string('1',27)+"01"+new string('0',15); bool ok=true; foreach(var ch in w){ ok&=(y.IsEven?'0':'1')==ch; y=y.IsEven?y/2:(3*y+1)/2; }
  Check("F(14,1) example orbit reaches n", ok&&y==n0&&m0<n0);
  bool disjoint=!mixed.Any(x=>x.e<=28 ? n0%p3[x.e]==x.t : x.t%p3[28]==n0%p3[28]) && !O.Any(c=>c.Item2<=28 ? n0%p3[c.Item2]==c.Item1 : c.Item1%p3[28]==n0);
  Check("F(14,1) cylinder disjoint from the mixed projections, C121 and the old rows through J", disjoint);
  Console.WriteLine($"failed: {fails}");
 }
}
