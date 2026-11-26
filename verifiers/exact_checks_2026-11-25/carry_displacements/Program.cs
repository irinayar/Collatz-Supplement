// Independent replay: equal-count carry classification (own implementation) and the stated word identities.
using System;
using System.Linq;
using System.Numerics;
using System.Collections.Generic;

class P {
 static int fails=0; static void Check(string s,bool ok){ Console.WriteLine((ok?"ok   ":"FAIL ")+s); if(!ok) fails++; }
 // ---- carry graph: state (i,j,r,b); reverse closure from (e,e,0,b), b>=1 ----
 static (long states,List<int> D,int maxlen) Closure(int e){
  int B=0; while(!(BigInteger.Pow(3,B)>(BigInteger.One<<(B+e)))) B++;
  var minAllowed=new bool[e+1,B+1]; // source test at end of a zero block: 3^b>2^(b+I)
  for(int I=0;I<=e;I++) for(int b=0;b<=B;b++) minAllowed[I,b]= BigInteger.Pow(3,b)>(BigInteger.One<<(b+I));
  long Key(int i,int j,int r,int b)=>((long)(r+(1<<e))<<20)|((long)b<<10)|(long)(i<<5)|(long)j;
  var seen=new HashSet<long>(1<<23); var q=new Queue<(int i,int j,int r,int b,int len)>();
  for(int b=1;b<=B;b++){ seen.Add(Key(e,e,0,b)); q.Enqueue((e,e,0,b,0)); }
  var D=new SortedSet<int>(); int maxlen=0;
  while(q.Count>0){
   var (I,J,R,bb,len)=q.Dequeue();
   if(R%3!=0) continue;
   int baseC=2*R/3;
   var preds= bb<B ? new[]{bb-1} : new[]{B-1,B};
   foreach(var b in preds){
    if(b<0) continue;
    for(int i=0;i<=I;i++){
     // the source block i..I ends at layer b: filters
     if(!(b==0&&I==0) && !minAllowed[I,b]) continue;
     if(I>i){
       if(b==0){ if(!(i==0 && I==0)) continue; }
       if(!minAllowed[I,b]) continue; }
     if(i==0 && I>=2) continue; // initial 1^j00 forbidden
     for(int j=0;j<=J;j++){
      int c=((1<<J)-(1<<j))-((1<<I)-(1<<i));
      int r=baseC+c;
      if(r< -((1<<e)-(1<<i)) || r>(1<<e)-(1<<j)) continue;
      var k=Key(i,j,r,b);
      if(seen.Add(k)){ q.Enqueue((i,j,r,b,len+1)); if(i==0&&j==0&&b==0&&r>0){ D.Add(r); int edges=len+1; maxlen=Math.Max(maxlen,e+edges-1); } }
     }
    }
   }
  }
  return (seen.Count,D.ToList(),maxlen);
 }
 // ---- words ----
 static BigInteger P3(int k)=>BigInteger.Pow(3,k);
 // R(w) as a fraction scaled by 3^M
 static (BigInteger s,int a,int z) Rw(string w,int M){ BigInteger s=0; int a=0,z=0; foreach(var ch in w){ if(ch=='1') a++; else { s+=(BigInteger.One<<(z+a))*P3(M-a); z++; } } return (s,a,z); }
 static bool Barrier(string w){ int a=0; for(int i=0;i<w.Length;i++){ if(w[i]=='1') a++; if(!(P3(a)>(BigInteger.One<<(i+1)))) return false; } return true; }
 static bool C08Free(string w){ int j=w.IndexOf('0'); return j<=0 || j+1>=w.Length || w[j+1]=='1'; }
 static BigInteger Residue(string w){ BigInteger C=0; int a=0; for(int i=0;i<w.Length;i++) if(w[i]=='1'){ C=3*C+(BigInteger.One<<i); a++; } var mod=BigInteger.One<<w.Length; BigInteger inv=1,x=P3(a); for(int it=0;it<12;it++) inv=((inv*(2-x*inv))%mod+mod)%mod; return ((-C*inv)%mod+mod)%mod; }
 static void Main(){
  var table=new Dictionary<int,(long st,int cnt,int max,int v3,int len)>{{8,(19046,6,6,1,0)},{9,(52118,13,15,2,0)},{10,(130177,31,47,3,29)},{11,(291534,55,71,3,31)},{12,(713465,130,287,3,34)},{13,(1725755,245,383,5,37)},{14,(3780015,458,679,5,39)},{15,(8751251,896,1647,6,42)}};
  int V3(int x){ int v=0; while(x%3==0){x/=3;v++;} return v; }
  for(int e=8;e<=15;e++){
   var (st,D,len)=Closure(e); var t=table[e];
   Check($"e={e}: states {st} (reported {t.st}), positive d {D.Count} ({t.cnt}), max {D.Max()} ({t.max}), max v3 {D.Max(V3)} ({t.v3}), longest shortest witness {len}"+(t.len>0?$" ({t.len})":""), st==t.st&&D.Count==t.cnt&&D.Max()==t.max&&D.Max(V3)==t.v3&&(t.len==0||len==t.len));
   if(e==9) Check("e=9 set", D.SequenceEqual(new[]{1,2,3,4,5,6,8,9,10,11,12,13,15}));
   if(e>=11) Console.WriteLine($"     multiples of 81: {string.Join(",",D.Where(d=>d%81==0))}");
  }
  // no filtered positive displacement through depth 17
  {
   long found=0, atlast=0;
   for(int L=1;L<=17;L++){
    var max=new Dictionary<(int,long),long>(); var C=new long[1<<L]; var A=new int[1<<L];
    for(int w=0;w<(1<<L);w++){ long c=0; int a=0; for(int i=0;i<L;i++) if(((w>>i)&1)==1){ c=3*c+(1L<<i); a++; } C[w]=c; A[w]=a; long m=1; for(int k=0;k<a;k++) m*=3; var key=(a,c%m); if(!max.TryGetValue(key,out var v)||c>v) max[key]=c; }
    for(int w=0;w<(1<<L);w++){ var s=new string(Enumerable.Range(0,L).Select(i=>((w>>i)&1)==1?'1':'0').ToArray()); if(!Barrier(s)||!C08Free(s)) continue; if(L==17) atlast++; long m=1; for(int k=0;k<A[w];k++) m*=3; if(max[(A[w],C[w]%m)]>C[w]) found++; }
   }
   Check($"depths 1..17: filtered words with a positive partner = {found}; filtered words at depth 17 = {atlast}", found==0&&atlast==3439);
  }
  // two pumped families
  foreach(var (e,k,A,Bw,res,len) in new[]{(13,5,"11111110111110101101110110000001","001100000100110111111111101101111",49340936191L,37),(15,6,"1111101111110011110101101110110000001","01100000001000111110111111111101101111",8004661569535L,43)}){
   var ra=Rw(A,40); var rb=Rw(Bw,40);
   Check($"e={e}: R(B)-R(A)=3^{k}, equal odd count {ra.a}, even counts {ra.z},{rb.z}", rb.s-ra.s==P3(k)*P3(40) && ra.a==rb.a && rb.z==ra.z+1);
   var pre=new string('1',k)+A; string W=pre+"1100", V=new string('1',k)+Bw+"101";
   var w=Rw(W,60); var v=Rw(V,60);
   Check($"e={e}: base words equal length {W.Length}, odd {w.a}, even {w.z}; R(V)-R(W)=2^{k}; barrier and C08 hold on source", W.Length==V.Length&&w.a==v.a&&w.z==e&&v.z==e&&v.s-w.s==(BigInteger.One<<k)*P3(60)&&Barrier(W)&&C08Free(W));
   Check($"e={e}: prefix residue {Residue(pre)} (stated {res}), length {pre.Length}, exceeds 2^{k}, residue mod 8192 = {Residue(pre)%8192}, mod 2048 = {Residue(pre)%2048}", Residue(pre)==res&&pre.Length==len&&res>(1L<<k));
  }
  // offset closure controls
  foreach(var (h,U,Vw) in new[]{(1,"100","01"),(2,"1101000001","01011100"),(3,"11100000001","01011100"),(4,"111101110000000001","01111110100100"),(5,"1111100110000000001","01111110100100"),(6,"111111010010000000001001","010111011111010000")}){
   var u=Rw(U,40); var v=Rw(Vw,40); Check($"offset h={h}: same odd count, h more evens, R(U)=2^h R(V)", u.a==v.a&&u.z==v.z+h&&u.s==(BigInteger.One<<h)*v.s);
  }
  // offset 18 family base
  {
   string U="11111111111111111111010001110010100111010001110010000100110000111000001011010110000101000110001000101010100000001";
   string V="11010110111111111110100111111011100101010110100101101100001101010011010100010111111101000100100";
   var u=Rw(U,200); var v=Rw(V,200); Check($"h=18: lengths {U.Length},{V.Length}; odd {u.a},{v.a}; R(U)=2^18 R(V)", U.Length==113&&V.Length==95&&u.a==56&&v.a==56&&u.s==(BigInteger.One<<18)*v.s);
   var w=new string('1',43)+U; var vv=new string('0',18)+new string('1',43)+V; var a=Rw(w,200); var b=Rw(vv,200);
   var n=Residue(w);
   Check($"family t=43: length {w.Length}, barrier {Barrier(w)}, C08 free {C08Free(w)}, R difference 2^18-1, least source {n}", w.Length==156&&vv.Length==156&&a.a==99&&a.z==57&&b.s-a.s==((BigInteger.One<<18)-1)*P3(200)&&Barrier(w)&&C08Free(w)&&n.ToString()=="45250704543207330089948317295792488210233294847");
  }
  // full examples: minimal prefix lifts
  foreach(var (n,m,end,L) in new[]{(132366335L,132366331L,382076432L,27),(1465465855L,1465465847L,7138257131L,31),(873354166271L,873354166255L,6057095864732L,40),(186779889663L,186779889631L,1943101219970L,41),(113557777836031L,113557777835967L,1495158520948220L,47)}){
   BigInteger x=n,y=m; int ax=0,ay=0; for(int i=0;i<L;i++){ if(!x.IsEven){x=(3*x+1)/2;ax++;} else x/=2; if(!y.IsEven){y=(3*y+1)/2;ay++;} else y/=2; }
   Check($"example n={n}: meet at {end} after {L} steps, equal odd counts {ax}={ay}", x==y&&x==end&&ax==ay);
  }
  Console.WriteLine($"failed: {fails}");
 }
}
