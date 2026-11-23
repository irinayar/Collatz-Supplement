# K180: the six balanced four-block words (2 x A2 + 2 x A3 in every order): offsets B, multiplier sums C0 and K_word = C0*A/(A-D).
# A2 = (1,2,1,2,2): affine (243,256,319), runs R,R,S ; A3 = (1,2,1,2,1,2,2): affine (2187,2048,3767), runs R,R,R,S (R = two-input run, multiplier 9/8; S = single-input run, multiplier 3/4).
function Frac($n,$d){ $g=[bigint]::GreatestCommonDivisor($n,$d); ,@(($n/$g),($d/$g)) }
function Add2($f,$g){ Frac ($f[0]*$g[1]+$g[0]*$f[1]) ($f[1]*$g[1]) }
$blocks=@{ '2'=@(243,256,319,'RRS'); '3'=@(2187,2048,3767,'RRRS') }
foreach($code in '2233','2323','2332','3223','3232','3322'){
  $At=[bigint]1; $Dt=[bigint]1; $Bt=[bigint]0; $lamN=[bigint]1; $lamD=[bigint]1; $sum=@([bigint]0,[bigint]1)
  foreach($ch in $code.ToCharArray()){
    $bk=$blocks[[string]$ch]; $Ab=[bigint]$bk[0]; $Db=[bigint]$bk[1]; $Bb=[bigint]$bk[2]
    $Bt=$Ab*$Bt+$Dt*$Bb; $At=$At*$Ab; $Dt=$Dt*$Db
    foreach($rc in $bk[3].ToCharArray()){
      if($rc -eq 'R'){ $sum=Add2 $sum (Frac $lamD $lamN); $lamN=$lamN*9; $lamD=$lamD*8 } else { $lamN=$lamN*3; $lamD=$lamD*4 }
    }
  }
  $C0=Frac ($sum[0]*2) ($sum[1]*3); $Kw=Frac ($C0[0]*$At) ($C0[1]*($At-$Dt))
  "$code : A=3^24 $($At -eq [bigint]::Pow(3,24)) D=2^38 $($Dt -eq [bigint]::Pow(2,38)) B=$Bt C0=$($C0[0])/$($C0[1]) K_word=$($Kw[0])/$($Kw[1])"
}
