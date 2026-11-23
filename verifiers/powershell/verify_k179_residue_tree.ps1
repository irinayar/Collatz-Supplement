# K179 residue certificate: all 2^15 pair codes (bit j: 0 = W_du, 1 = W_ud); r = (D^N - U_N)(A^N)^-1 mod 2D^N.
# Checks distinctness, the minimum (stated: mask 25847, m15 = 7631510170755948127862786147500572769390316906790491185139757695856112765430029307)
# and 3*56*m15*7153 >= 1669158*(4(2^256-1)+1).
$Ac=[bigint]531441; $Dc=[bigint]524288; $Bdu=[bigint]1662005; $Bud=[bigint]1568693; $Np=15
$mod=2*[bigint]::Pow($Dc,$Np); $inv=[bigint]::ModPow([bigint]::Pow($Ac,$Np) % $mod, ($mod/2)-1, $mod); $DN=[bigint]::Pow($Dc,$Np)
$Dp=@([bigint]1); for($jj=1;$jj -le $Np;$jj++){ $Dp+=($Dp[$jj-1]*$Dc) }
$best=$null; $bestmask=-1; $seen=@{}
for($mask=0;$mask -lt 32768;$mask++){
  $Uv=[bigint]0
  for($jj=0;$jj -lt $Np;$jj++){ if((($mask -shr $jj) -band 1) -eq 0){$Bj=$Bdu}else{$Bj=$Bud}; $Uv=$Ac*$Uv+$Dp[$jj]*$Bj }
  $rv=((($DN-$Uv) % $mod)+$mod) % $mod; $rv=($rv*$inv) % $mod; $seen[$rv.ToString()]=1
  if($best -eq $null -or $rv -lt $best){$best=$rv; $bestmask=$mask}
}
"distinct residues: $($seen.Count) of 32768 ; minimum at mask $bestmask"
"minimum equals stated m15: " + ($best -eq [bigint]::Parse('7631510170755948127862786147500572769390316906790491185139757695856112765430029307'))
"3*56*m15*7153 >= 1669158*(4(2^256-1)+1): " + (([bigint]3*56*$best*7153) -ge ([bigint]1669158*(4*([bigint]::Pow(2,256)-1)+1)))
