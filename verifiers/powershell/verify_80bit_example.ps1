# Rebuild ChatGPT's 80-bit nonempty-core example: prefix E_i=floor(i log2 3) (i<=46) by bit length, residue, lift, then iterate the odd map.
function BitLen([bigint]$x){ $cnt=0; while($x -gt 0){$x=$x/2;$cnt++}; $cnt }
$Ei=@(); for($ii=0;$ii -le 46;$ii++){ $Ei+=(BitLen ([bigint]::Pow(3,$ii)))-1 }
$U46=[bigint]0; for($ii=0;$ii -lt 46;$ii++){ $U46=3*$U46+[bigint]::Pow(2,$Ei[$ii]) }
$mod=[bigint]::Pow(2,73); $inv=[bigint]::ModPow([bigint]::Pow(3,46),[bigint]::Pow(2,72)-1,$mod)
$a=((([bigint]::Pow(2,72)-$U46) % $mod)+$mod) % $mod; $a=($a*$inv) % $mod; $u=$a+126*$mod
"u = $u  (stated 1194734292994222926486523: $($u -eq [bigint]::Parse('1194734292994222926486523')))"
$x=$u; $xs=New-Object System.Collections.ArrayList; $exps=New-Object System.Collections.ArrayList
while($true){ [void]$xs.Add($x); $t=3*$x+1; $ev=0; while($t % 2 -eq 0){$t=$t/2;$ev++}; [void]$exps.Add($ev); $x=$t; if($x -le $u){break} }
$w=$x; $oddn=$xs.Count; $Etot=0; $resets=0; foreach($ex in $exps){ $Etot+=$ex; if($ex -ge 2){$resets++} }
"odd transitions=$oddn (121), shortcut steps=$Etot (192), resets=$resets (54), w=$w"
$Dn=[bigint]0; $Ep=0; for($ii=0;$ii -lt $oddn;$ii++){ $Dn=3*$Dn+[bigint]::Pow(2,$Ep); $Ep+=$exps[$ii] }
"affine identity 2^E w = 3^g u + D: " + (([bigint]::Pow(2,$Etot)*$w) -eq ([bigint]::Pow(3,$oddn)*$u+$Dn))
"phase Q = D/3^g = $([double]$Dn/[double][bigint]::Pow(3,$oddn))"
$mod2=[bigint]::Pow(2,193); $inv2=[bigint]::ModPow([bigint]::Pow(3,121),[bigint]::Pow(2,192)-1,$mod2)
$full=((([bigint]::Pow(2,192)-$Dn) % $mod2)+$mod2) % $mod2; $full=($full*$inv2) % $mod2
"u is the least positive source of its odd-exponent cylinder: " + ($full -eq $u)
$n0=3*($u+1)/4; $n1=3*[bigint]::Pow(2,78)-1
"thresholds n0=$n0 n1=$n1 ; H(n0)=u: $(((4*$n0-2)/3) -eq $u) ; H(n1)=2^80-2: $(((4*$n1-2)/3) -eq ([bigint]::Pow(2,80)-2)) ; count=$(($n1-$n0)/2+1)"
