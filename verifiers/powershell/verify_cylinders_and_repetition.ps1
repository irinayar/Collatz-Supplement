# K177 cylinders (43 mod 64: valuations (1,2,2); 379 mod 512: (1,2,1,2,2)), polynomial shifts,
# and the repetition criterion k_max = floor((v2(Z)-1)/E) for W=(1,1,1,1,4) (A=243, D=256, B=211, Z=13u-211).
function OddStep([long]$x){ $t=3*$x+1; $v=0; while($t % 2 -eq 0){$t=$t/2;$v++}; ,@($t,$v) }
function Vals([long]$x,$cnt){ $r=@(); for($ii=0;$ii -lt $cnt;$ii++){ $s=OddStep $x; $r+=$s[1]; $x=$s[0] }; ,@($x,($r -join ',')) }
$bad1=0; $bad2=0
for($k=0;$k -lt 2000;$k++){
  $r=Vals (43+64*$k) 3; if($r[1] -ne '1,2,2' -or $r[0]*32 -ne 27*(43+64*$k)+23){$bad1++}
  $r2=Vals (379+512*$k) 5; if($r2[1] -ne '1,2,1,2,2' -or $r2[0]*256 -ne 243*(379+512*$k)+319){$bad2++}
}
"cylinder 43 mod 64 failures: $bad1 ; cylinder 379 mod 512 failures: $bad2 (of 2000 each)"
"poly A1 shift: const $(18*107*107-1676*107-1150) (25600) t-coef $(18*2*107-1676) (2176) ; at 43: $(18*43*43-1676*43-1150) (negative)"
"poly A2 shift: const $(486*1915*1915-750084*1915-813450) (345047040) t-coef $(486*2*1915-750084) (1111296) ; at 1403: $(486*1403*1403-750084*1403-813450) (negative)"
function V2([bigint]$z){ if($z -lt 0){$z=-$z}; $c=0; while($z % 2 -eq 0){$z=$z/2;$c++}; $c }
$rng=New-Object System.Random 777; $mm=0; $tt=0
foreach($q in 1..20000){
  if($q % 2 -eq 0){ $u=[long]($rng.Next(1,1000000))*2+1 } else { $u=60511L+131072L*[long]$rng.Next(0,1000000) }
  $x=$u; $kcount=0
  while($kcount -lt 30){
    $y=$x; $okk=$true
    foreach($want in 1,1,1,1,4){ if($y % 2 -eq 0){$okk=$false;break}; $s=OddStep $y; if($s[1] -ne $want){$okk=$false;break}; $y=$s[0] }
    if(-not $okk){break}; $kcount++; $x=$y
  }
  $Zv=[bigint](13*$u-211); if($Zv -eq 0){continue}
  $kf=[math]::Max(0,[math]::Floor(((V2 $Zv)-1)/8)); $tt++; if($kcount -ne $kf){$mm++}
}
"repetition criterion mismatches: $mm of $tt"
