-- FALSE CONTROL (D28 item 10(a), k = 128): Eq. (1.5) reduced with the index off by two,
-- coeff_128 phi0 = coeff_256 psi (true identity is coeff_128 phi0 = coeff_258 psi).
import D28.Eq15
open DiracTimeD25.BHL D28
set_option maxRecDepth 100000 in
theorem false_eq15_shift_128 : (rep 129 phi0).getD 128 0 = (rep 259 psi).getD 256 0 := by
  rw [rep_phi0_fast, rep259_psi_tab]
  decide +kernel
