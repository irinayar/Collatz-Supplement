# Runs the quick exact verifiers (the C# census checks are run separately: see README.md).
foreach($s in 'verify_constants.ps1','verify_cylinders_and_repetition.ps1','verify_80bit_example.ps1','verify_k179_residue_tree.ps1','verify_k180_words.ps1'){
  "===== $s"
  & "$PSScriptRoot\$s"
}
