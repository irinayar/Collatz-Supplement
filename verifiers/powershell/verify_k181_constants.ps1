# K181 / aggregate-compensation packet: exact constants of the numerical consequence (16)-(19).
function Frac($n,$d){ $g=[bigint]::GreatestCommonDivisor($n,$d); ,@(($n/$g),($d/$g)) }
function Same($f,$n,$d){ ($f[0] -eq [bigint]$n) -and ($f[1] -eq [bigint]$d) }
"alpha0 = 15*999/1000-1 = 2797/200: " + (Same (Frac 13985 1000) 2797 200)
"16*375/488 = 750/61: " + (Same (Frac (16*375) 488) 750 61)
"16*375*235/(488*128) = 88125/3904 and minus 15/4 = 73485/3904: " + ((Same (Frac (16*375*235) (488*128)) 88125 3904) -and (Same (Frac (88125*4-15*3904) (3904*4)) 73485 3904))
"15/alpha0 = 3000/2797: " + (Same (Frac (15*200) 2797) 3000 2797)
"(750/61)(59/1000)/alpha0 = 8850/170617: " + (Same (Frac (750*59*200) (61*1000*2797)) 8850 170617)
"(73485/3904)/alpha0 = 1837125/1364936: " + (Same (Frac (73485*200) (3904*2797)) 1837125 1364936)
$Y=Frac (([bigint]327*170617 - [bigint]8850*3904)*2797) ([bigint]3904*170617*3000)
"Y* = (327/3904 - 8850/170617)(2797/3000) = 116073/3904000: " + (Same $Y 116073 3904000)
"relaxed coefficient 73485/(15*3904) = 4899/3904: " + (Same (Frac 73485 (15*3904)) 4899 3904)
