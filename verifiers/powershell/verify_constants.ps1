# Exact verification (big-integer rationals) of the numerical constants of the first-source reduction (mirrors CollatzConstants.lean).
# Usage: powershell -NoProfile -File verify_constants.ps1     Prints PASS/FAIL per item.
# NOTE: PowerShell variable names are case-insensitive: keep variable names distinct.
function Frac($n,$d){ $g=[bigint]::GreatestCommonDivisor($n,$d); if($d -lt 0){$g=-$g}; ,@(($n/$g),($d/$g)) }
function Same($f,$n,$d){ ($f[0] -eq [bigint]$n) -and ($f[1] -eq [bigint]$d) }
$script:fails=0
function Check($name,$ok){ if($ok){"PASS  $name"}else{"FAIL  $name"; $script:fails++} }
function Pw($b,$e){ [bigint]::Pow([bigint]$b,[int]$e) }
Check "3^99 < 2^160" ((Pw 3 99) -lt (Pw 2 160))
Check "(193/200)^99 < 1/32" (((Pw 193 99)*32) -lt (Pw 200 99))
Check "3^39 < 2^62" ((Pw 3 39) -lt (Pw 2 62))
Check "4*193^39 < 200^39" ((4*(Pw 193 39)) -lt (Pw 200 39))
Check "3000^22 < 2^256" ((Pw 3000 22) -lt (Pw 2 256))
Check "47*51/(30*4700) = 17/1000" (Same (Frac (47*51) (30*4700)) 17 1000)
Check "151/1000+17/1000 = 21/125" (Same (Frac (151+17) 1000) 21 125)
Check "(488/375)(327/3904) = 109/1000" (Same (Frac (488*327) (375*3904)) 109 1000)
Check "59/1000+109/1000 = 21/125" (Same (Frac (59+109) 1000) 21 125)
Check "(61/50)/(1-4/64) = 488/375" (Same (Frac (61*64) (50*60)) 488 375)
$cn=[bigint]::Parse('620751769493359576'); $cd=(Pw 2 70)+1; $tn=[bigint]327; $td=[bigint]3904
Check "c denominator = 2^70+1" ($cd -eq [bigint]::Parse('1180591620717411303425'))
Check "c < 1/1500" ($cn*1500 -lt $cd)
$g159=$tn*$cd-159*$cn*$td; $g160=$tn*$cd-160*$cn*$td; $den=$td*$cd
Check "159c < T < 160c" (($g159 -gt 0) -and ($g160 -lt 0))
Check "T-159c = 730489586363446452039/4609029687280773728571200" (Same (Frac $g159 $den) 730489586363446452039 4609029687280773728571200)
Check "T-16c  = 347278821444960283664711/4609029687280773728571200" (Same (Frac ($tn*$cd-16*$cn*$td) $den) 347278821444960283664711 4609029687280773728571200)
$lhs56=[bigint]56*3000*170617*$cn + [bigint]8850*2797*$cd; $rhs159=[bigint]159*$cn*2797*170617; $lhs57=[bigint]57*3000*170617*$cn + [bigint]8850*2797*$cd
Check "56 b0 c + a0 < 159 c" ($lhs56 -lt $rhs159)
Check "159 c < 57 b0 c + a0" ($rhs159 -lt $lhs57)
$s1=Frac ([bigint]1669158*3000*2*170617 + [bigint]8850*7153*2797*16125) ([bigint]7153*2797*16125*170617)
Check "Kmax b0 c_tail + a0 = 4351172358/52478206243" (Same $s1 4351172358 52478206243)
$gp=Frac ($tn*$s1[1]-$s1[0]*$td) ($td*$s1[1])
Check "T - that = 2842566489/3358605199552" (Same $gp 2842566489 3358605199552)
function KC($Lp,$rn,$rd){ $t0n=Pw 9 $Lp; $t0d=Pw 8 $Lp; Frac (6*($t0n-$t0d)*$rn) ($t0n*$rn-$t0d*$rd) }
Check "K3 = 3906/139" (Same (KC 3 3 4) 3906 139)
Check "K4 = 44370/3299" (Same (KC 4 3 4) 44370 3299)
Check "K(e=3,L=9) = 4557649698/88519643" (Same (KC 9 3 8) 4557649698 88519643)
Check "K(two shorts,L=5,rho=9/16) = 1419174/7153" (Same (KC 5 9 16) 1419174 7153)
Check "B_du = 1662005" ((2187*319+256*3767) -eq 1662005)
Check "B_ud = 1568693" ((243*3767+2048*319) -eq 1568693)
Check "3^12 > 2^19" ((Pw 3 12) -gt (Pw 2 19))
Check "2(t+t^3/3) = 189480/493039 (t=15/79)" (((2*(15*6241+1125)) -eq 189480) -and ((Pw 79 3) -eq 493039))
Check "(61/50)(189480/493039)-15/32 = 8571/78886240" (Same (Frac ([bigint]61*189480*32-[bigint]15*50*493039) ([bigint]50*493039*32)) 8571 78886240)
Check "ln(47/32) > 189480/493039 (floating check)" ([math]::Log(47.0/32) -gt 189480.0/493039)
if($script:fails -eq 0){"ALL PASS"}else{"$($script:fails) FAILURES"}
