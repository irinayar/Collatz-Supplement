// Replay: 120 affine certificates and band, 73 count pairs, suffix envelope, finite origin check, tail constants.
using System;
using System.IO;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;

class P {
 static int fails=0; static void Check(string s,bool ok){ Console.WriteLine((ok?"ok   ":"FAIL ")+s); if(!ok) fails++; }
 static BigInteger P2(int k)=>BigInteger.One<<k; static BigInteger P3(int k)=>BigInteger.Pow(3,k);
 static void Main(string[] args){
  var M=2075*P2(60);
  // 120 certificates
  var rows=File.ReadAllLines(args[0]).Skip(1).Where(l=>l.Length>0).Select(l=>l.Split(',')).ToList();
  var ledger=File.ReadAllLines(args[1]).Skip(1).Select(l=>l.Split(',')).Select(f=>(res:BigInteger.Parse(f[1]),mod:BigInteger.Parse(f[2]))).ToHashSet();
  bool ok=true; int matched=0; BigInteger sn=0,sd=1,bn=0,bd=1; bool first=true; string maxS="";
  foreach(var f in rows){
   var n0=BigInteger.Parse(f[1]); var Pm=BigInteger.Parse(f[2]); var m0=BigInteger.Parse(f[3]); var Q=BigInteger.Parse(f[4]);
   var w=f[5]=="-"?"":f[5]; var v=f[6]=="-"?"":f[6];
   for(int t=0;t<=3;t++){ BigInteger x=n0+Pm*t, y=m0+Qt(Q,t);
     foreach(var ch in w){ ok&=(x.IsEven?'0':'1')==ch; x=x.IsEven?x/2:(3*x+1)/2; }
     foreach(var ch in v){ ok&=(y.IsEven?'0':'1')==ch; y=y.IsEven?y/2:(3*y+1)/2; } ok&=x==y; }
   // affine identity for all t: P divisible by 2^|w|, Q by 2^|v|, equal output slopes
   int aw=w.Count(c=>c=='1'), av=v.Count(c=>c=='1');
   ok&=Pm%P2(w.Length)==0&&Q%P2(v.Length)==0&&Pm*P3(aw)*P2(v.Length)==Q*P3(av)*P2(w.Length)&&m0>0&&Q<Pm;
   if(ledger.Contains((n0%Pm,Pm))) matched++;
   if(Q*sd>sn*Pm){ sn=Q; sd=Pm; maxS=f[0]; }
   var num=m0*Pm-Q*n0; if(first||num*bd>bn*Pm){ bn=num; bd=Pm; first=false; }
  }
  Check($"certificates {rows.Count}: words, meetings (t=0..3) and affine identities; rows equal to a ledger class {matched}", ok&&rows.Count==120&&matched==119);
  Check($"max slope 68630377364883/70368744177664 ({maxS}), max offset 103120058842515/70368744177664", sn*70368744177664==68630377364883*sd && bn*70368744177664==103120058842515*bd);
  Check("S*41/40 + B/M < 1", sn*41*bd*M + bn*40*sd < 40*sd*bd*M);
  // logarithms
  int PREC=400; var S=P2(PREC);
  BigInteger Atanh(int k){ var term=S/k; BigInteger sum=0; int j=1; while(term>0){ sum+=term/j; term/=k*k; j+=2; } return 2*sum; }
  var l2=Atanh(3); var l3=l2+Atanh(5); var pad=P2(20);
  var ql=BigInteger.Parse("65470613321"); var pl=BigInteger.Parse("103768467013"); var qh=BigInteger.Parse("6586818670"); var ph=BigInteger.Parse("10439860591");
  Check("neighbours unimodular", BigInteger.Abs(ph*ql-pl*qh)==1);
  BigInteger R=BigInteger.Pow(10,12); int total=0, kept=0; BigInteger firstCap=0; BigInteger minR=0; BigInteger capEx=0; bool strict=true; int wide=0;
  for(BigInteger u=1;u*ql+qh<=R;u++) for(BigInteger v=1;u*ql+v*qh<=R;v++){
    total++; var r=u*ql+v*qh; var L=u*pl+v*ph;
    // delta = L ln2 - r ln3 (scaled by S), enclosure
    var dlo=L*(l2-pad)-r*(l3+pad); var dhi=L*(l2+pad)-r*(l3-pad);
    // keep iff 0 < delta < c r/(3M), c=3607/5000
    bool inside=dlo>0 && dhi*15000*M < 3607*r*S;
    if(dlo>0 && dhi*(15000*M-3607*R) < 3607*r*S) wide++; else if(!(dhi<=0 || dlo*(15000*M-3607*R) >= 3607*r*S)) strict=false;
    bool outside=dhi<=0 || dlo*15000*M >= 3607*r*S;
    strict&=inside||outside;
    if(inside){ kept++; var cap=3607*r*S/(15000*dlo); if(minR==0||r<minR){ minR=r; firstCap=cap; }
      if(r==BigInteger.Parse("805805389241")){ // D < 4cr - 12M(delta_lo - delta_hi^2/2) - 12(1-delta_hi)
        var num=4*3607*r*2*S*S - 5000*(12*M*(2*S*dlo - dhi*dhi) + 24*S*(S-dhi)); capEx=num/(10000*S*S); Check($"pair r=805805389241 has L=1277171324826",L==BigInteger.Parse("1277171324826")); } }
  }
  Check($"pairs in the cone below 10^12: {total}; retained {kept}; with the wider cutoff {wide}; every pair strictly decided {strict}", total==1077&&kept==73&&wide==73&&strict);
  Console.WriteLine($"info smallest retained r={minR}, its endpoint bound {firstCap}; defect cap for r=805805389241: {capEx}");
  Check("endpoint bound 3144212673146423889669", firstCap==BigInteger.Parse("3144212673146423889669"));
  Check("defect cap 3750289562", capEx==3750289562);
  // suffix envelope S_r and caps
  foreach(var (Rmax,crudeExp,refExp,rr,LL) in new[]{(14,33,15,10,16),(100,3357,2313,94,149),(4096,1506053,1084811,3631,5755)}){
   BigInteger num=0; int den=0; BigInteger pw=1; BigInteger crude=0, refined=0; int br=0,bL=0;
   // S_r = num/(3*2^den)
   for(int r=1;r<=Rmax;r++){ pw*=3; int ell=(int)(pw.GetBitLength()); if(ell>den){ num<<=ell-den; den=ell; } num+=pw<<(den-ell);
     var gapN=P2(ell)-pw; // 1-a_r = gapN/2^ell
     var c=(BigInteger)r*P2(ell)/(3*gapN); if((BigInteger)r*P2(ell)%(3*gapN)==0) c-=1; if(c>crude) crude=c;
     // (S_r - a_r)/(1-a_r) with S_r=num/(3*2^den)
     var topN=num - 3*(pw<<(den-ell)); if(topN>0){ var q=topN*P2(ell)/(3*P2(den)*gapN); if(q>refined){ refined=q; br=r; bL=ell; } } }
   Check($"R={Rmax}: crude cap {crude}, refined cap {refined} at r={br}, L={bL}", crude==crudeExp&&refined==refExp&&br==rr&&bL==LL);
  }
  // finite check: no direct ancestor with all suffix multipliers <=1 and <=100 odds for origins below 2313
  long steps=0, hits=0;
  for(int m=1;m<=2312;m++){ var seen=new HashSet<BigInteger>(); BigInteger x=m; BigInteger three=1; int len=0, odd=0; BigInteger minNum=1; int minLen=0;
    while(seen.Add(x)){ if(!x.IsEven){ x=(3*x+1)/2; odd++; three*=3; } else x/=2; len++; steps++;
      // running minimum of 3^odd/2^len
      bool isMin= three*P2(minLen) <= minNum*P2(len); if(isMin){ minNum=three; minLen=len; }
      if(odd>100) break;
      if(isMin && x>m) hits++; } }
  Check($"origins 1..2312: hits {hits} (steps {steps})", hits==0);
  Check("3^27*25^17 < 144^17, 3^17 < 2^27, 10*24^60 < 25^60", P3(27)*BigInteger.Pow(25,17)<BigInteger.Pow(144,17)&&P3(17)<P2(27)&&10*BigInteger.Pow(24,60)<BigInteger.Pow(25,60));
  Check("floor(72057431991/60) = 1200957199", 72057431991L/60==1200957199L);
  Console.WriteLine($"failed: {fails}");
 }
 static BigInteger Qt(BigInteger Q,int t)=>Q*t;
}
