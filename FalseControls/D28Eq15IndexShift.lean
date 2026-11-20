-- FALSE CONTROL (D28 item 10(a)): Eq. (1.5) with the index off by two, coeff_k phi0 = coeff_{2k} psi;
-- at k = 1: coeff_1 phi0 = 2 but coeff_2 psi = 1.
import DiracTimeD25.BhlBoundaryTest
open DiracTimeD25.BHL
theorem false_eq15_shift : (rep 17 phi0).getD 1 0 = (rep 17 psi).getD 2 0 := by
  rw [rep17_phi0, rep17_psi]; decide
