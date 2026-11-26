// Independent implementation of the phase-localized weighted window capacity (window 44, charges 0,2,3, budget 28).
using System;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;

class P {
 static void Main(){
  int PREC=400; BigInteger S=BigInteger.One<<PREC;
  BigInteger Atanh(int k){ var term=S/k; BigInteger sum=0; int j=1; while(term>0){ sum+=term/j; term/=k*k; j+=2; } return 2*sum; }
  var l2=Atanh(3); var l3=l2+Atanh(5); BigInteger pad=BigInteger.One<<20;
  var l2lo=l2-pad; var l2hi=l2+pad; var l3lo=l3-pad; var l3hi=l3+pad;
  var M=2075*(BigInteger.One<<60); long r0=72057431991L; long q=31867, p=50508;
  // rational slope: 0 < alpha - p/q < 1/q^2
  bool slope = l3lo*q > p*l2hi && (l3hi*q - p*l2lo)*q < l2lo;
  Console.WriteLine($"slope check 0<alpha-50508/31867<1/q^2: {slope}");
  // Farey cone and the 73 retained pairs
  BigInteger ql=BigInteger.Parse("65470613321"), pl=BigInteger.Parse("103768467013"), qh=BigInteger.Parse("6586818670"), ph=BigInteger.Parse("10439860591"), Rmax=BigInteger.Pow(10,12);
  var pairs=new List<(long r,BigInteger L,BigInteger dl,BigInteger dh)>(); int total=0;
  for(BigInteger u=1;u*ql+qh<=Rmax;u++) for(BigInteger v=1;u*ql+v*qh<=Rmax;v++){ total++; var r=u*ql+v*qh; var L=u*pl+v*ph;
    var dl=L*l2lo-r*l3hi; var dh=L*l2hi-r*l3lo; if(dl>0 && dh*15000*M<3607*r*S) pairs.Add(((long)r,L,dl,dh)); }
  Console.WriteLine($"cone pairs {total}, retained {pairs.Count}");
  const int m=44, Hmax=28;
  // factors and offset counts for s = m-1-14 .. m-1
  var fac=new Dictionary<int,List<(int[] g,long A,long B)>>();
  var cnt=new Dictionary<(int s,int idx,bool rev),(BigInteger[] F,int ell)>();
  for(int s=m-1-Hmax/2;s<=m-1;s++){
   var cuts=Enumerable.Range(0,s+1).Select(j=>(((-j*p)%q)+q)%q).Append(q).Distinct().OrderBy(x=>x).ToList();
   var list=new List<(int[],long,long)>();
   for(int c=0;c+1<cuts.Count;c++){ long A=cuts[c], B=cuts[c+1]; var g=new int[s]; for(int j=0;j<s;j++) g[j]=(int)((A+B+2*(j+1)*p)/(2*q)-(A+B+2*j*p)/(2*q)); list.Add((g,A,B)); }
   fac[s]=list;
   for(int i=0;i<list.Count;i++) foreach(var rev in new[]{false,true}){
    var g=rev?list[i].Item1.Reverse().ToArray():list[i].Item1;
    int vmax=g.Sum(x=>x-1);
    var cur=new BigInteger[Hmax+1,vmax+2]; cur[0,0]=1;
    for(int j=0;j<s;j++){ var nxt=new BigInteger[Hmax+1,vmax+2];
      for(int k=0;k<=Hmax;k++) for(int v=0;v<=vmax;v++){ if(cur[k,v].IsZero) continue; int top=Math.Min(vmax,v+g[j]-1);
        for(int u=0;u<=top;u++){ if(j==s-1&&u!=0) continue; int w=u==0?0:u==1?2:3; if(k+w>Hmax) continue; nxt[k+w,u]+=cur[k,v]; } }
      cur=nxt; }
    var F=new BigInteger[Hmax+1]; BigInteger acc=0; for(int k=0;k<=Hmax;k++){ acc+=cur[k,0]; F[k]=acc; }
    cnt[(s,i,rev)]=(F,g.Sum());
   }
  }
  Console.WriteLine($"factors per length: {string.Join(" ",fac.Select(kv=>kv.Value.Count))}");
  // exclusion test per pair and mode
  var excl=new List<long>[]{new(),new(),new()}; string[] names={"general forward","distinct forward","shortest inverse"};
  foreach(var (r,L,dl,dh) in pairs){
   for(int mode=0;mode<3;mode++){
    bool inv=mode==2;
    // delta bounds as rationals dl/S, dh/S ; H = c r/(3 delta_lo) or c r/(3 z)
    BigInteger zNum=2*S*dl-dh*dh, zDen=2*S*S;                      // z = dl - dh^2/2
    BigInteger Hn= inv ? 3607*(BigInteger)r*zDen : 3607*(BigInteger)r*S;
    BigInteger Hd= inv ? 15000*zNum : 15000*dl;
    var X=new Dictionary<(int,int),BigInteger>();
    foreach(var kv in fac) for(int i=0;i<kv.Value.Count;i++){ var (g,A,B)=kv.Value[i]; int s=kv.Key;
      // width <= (B-A)/q + s/q^2 ;  X = floor(7/5 H w + 2r/3)
      BigInteger wn=(B-A)*q+s, wd=q*q;
      BigInteger num=7*Hn*wn*3+10*(BigInteger)r*Hd*wd, den=15*Hd*wd; X[(s,i)]=num/den; }
    long b= mode==0 ? 1+(r-1)/r0 : 1;
    long N= inv ? r-m : r-m+1;
    BigInteger sum=0;
    for(int h=0;h<=Hmax;h++){
     BigInteger V=0;
     for(int s=m-1-h/2;s<=m-1;s++){ BigInteger inner=0; for(int i=0;i<fac[s].Count;i++){ var (F,ell)=cnt[(s,i,inv)]; int H2=h-2*(m-1-s); if(H2<0) continue; inner+=F[H2]*(X[(s,i)]/(BigInteger.One<<(ell+1))+1); } V+=(m-s)*inner; }
     var rest=N-b*V; if(rest>0) sum+=rest;
    }
    // Cmin = ceil(sum/m)/2 ; lower = Cmin + ln2 max(0,Cmin-3e/2)^2/(3 r)
    BigInteger twoC=(sum+m-1)/m; BigInteger e=2*(r/q)+q;
    BigInteger excess2=twoC-3*e; if(excess2<0) excess2=0;                 // 2(Cmin - 3e/2)
    // lower*S*12 r = 6 twoC r S + ln2lo * excess2^2   (lower = twoC/2 + ln2 (excess2/2)^2/(3r))
    BigInteger lowerNum=6*twoC*r*S + l2lo*excess2*excess2, lowerDen=12*(BigInteger)r*S;
    // upper forward 4 c r - 12 M dl ; inverse 4 c r - 12 M z - 12(1-dh)
    BigInteger upNum, upDen;
    if(!inv){ upNum=14428*(BigInteger)r*S-60000*M*dl; upDen=5000*S; }
    else { upNum=14428*(BigInteger)r*zDen - 60000*M*zNum - 60000*zDen + 60000*dh*2*S; upDen=5000*zDen; }
    if(lowerNum*upDen>upNum*lowerDen) excl[mode].Add(r);
   }
  }
  for(int mode=0;mode<3;mode++) Console.WriteLine($"{names[mode]}: excluded {excl[mode].Count}, survivors {pairs.Count-excl[mode].Count}: r = {string.Join(" ",excl[mode].OrderBy(x=>x))}");
 }
}
