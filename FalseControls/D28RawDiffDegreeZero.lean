-- FALSE CONTROL (D28 item 9): positivity of phi0 - M fails in degree 0 (coefficient 0).
import DiracTimeD25.BhlBoundaryTest
open DiracTimeD25.BHL
theorem false_rawdiff_deg0 : 0 < (rep 17 (phi0 - bhlM)).getD 0 0 := by
  rw [rep17_phi0_sub_bhlM]; decide
