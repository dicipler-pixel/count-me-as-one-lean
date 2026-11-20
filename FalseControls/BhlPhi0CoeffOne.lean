-- FALSE CONTROL: claims coeff_{q^1} phi_0 = 1, i.e. that phi_0 agrees with M(q) at q^1 (BHL Eq. 1.3).
-- The exact truncation [1, 2, 2, 3, ...] gives 2, not 1: the signed boundary does not vanish.
import DiracTimeD25.BhlBoundaryTest
open PowerSeries DiracTimeD25.BHL
theorem false_coeff_one_phi0 : coeff 1 phi0 = 1 := by
  rw [← getD_rep_of_lt phi0 (show 1 < 17 by norm_num), rep17_phi0]; decide
