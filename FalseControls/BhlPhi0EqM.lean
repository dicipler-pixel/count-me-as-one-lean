-- FALSE CONTROL: claims phi_0 and M(q) have the same coefficients through q^16 (they differ from q^1 on).
import DiracTimeD25.BhlBoundaryTest
open PowerSeries DiracTimeD25.BHL
theorem false_phi0_eq_bhlM_trunc : rep 17 phi0 = rep 17 bhlM := by
  rw [rep17_phi0, rep17_bhlM]; decide
