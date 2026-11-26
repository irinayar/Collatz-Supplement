using System;
using System.Numerics;

public struct F : IComparable<F> {
 public BigInteger n,d;
 public F(BigInteger a,BigInteger b){ if(b.Sign<0){a=-a;b=-b;} var g=BigInteger.GreatestCommonDivisor(a,b); if(!g.IsOne&&!g.IsZero){a/=g;b/=g;} n=a;d=b; }
 public F(BigInteger a){n=a;d=1;}
 public static implicit operator F(int a)=>new F((BigInteger)a);
 public static implicit operator F(long a)=>new F((BigInteger)a);
 public static implicit operator F(BigInteger a)=>new F(a);
 public BigInteger D=>d.IsZero?BigInteger.One:d;
 public static F operator+(F x,F y)=>new F(x.n*y.D+y.n*x.D,x.D*y.D);
 public static F operator-(F x,F y)=>new F(x.n*y.D-y.n*x.D,x.D*y.D);
 public static F operator-(F x)=>new F(-x.n,x.D);
 public static F operator*(F x,F y)=>new F(x.n*y.n,x.D*y.D);
 public static F operator/(F x,F y)=>new F(x.n*y.D,x.D*y.n);
 public static bool operator<(F x,F y)=>x.n*y.D<y.n*x.D;
 public static bool operator>(F x,F y)=>x.n*y.D>y.n*x.D;
 public static bool operator<=(F x,F y)=>x.n*y.D<=y.n*x.D;
 public static bool operator>=(F x,F y)=>x.n*y.D>=y.n*x.D;
 public static bool operator==(F x,F y)=>x.n*y.D==y.n*x.D;
 public static bool operator!=(F x,F y)=>!(x==y);
 public override bool Equals(object o)=>o is F f&&this==f;
 public override int GetHashCode()=>(n,D).GetHashCode();
 public int CompareTo(F o)=>(n*o.D).CompareTo(o.n*D);
 public static F Max(F a,F b)=>a>=b?a:b;
 public static F Min(F a,F b)=>a<=b?a:b;
 public static F Pow(F a,int k)=>new F(BigInteger.Pow(a.n,k),BigInteger.Pow(a.D,k));
 public static F Of(string s){ var p=s.Split('/'); return p.Length==1?new F(BigInteger.Parse(p[0])):new F(BigInteger.Parse(p[0]),BigInteger.Parse(p[1])); }
 public override string ToString()=>D.IsOne?n.ToString():n+"/"+D;
 public double ToDouble(){ if(n.IsZero) return 0; int s=Math.Max(0,(int)(D.GetBitLength()-900)); return (double)(n>>s)/(double)(D>>s); }
}

public static class Chk {
 public static int fail=0,pass=0;
 public static void A(bool c,string what){ if(c) pass++; else { fail++; if(fail<20) Console.WriteLine("FAILED: "+what); } }
}
