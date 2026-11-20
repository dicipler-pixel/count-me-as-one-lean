import D28.FastModel

/-!
# D28 item 9(b) [N30]: `φ₀ − M` has positive coefficients in degrees `1..128`
(kernel `decide`, linear-time model)
-/

namespace D28

open PowerSeries DiracTimeD25.BHL

set_option maxRecDepth 100000 in
theorem rep129_phi0_sub_bhlM_pos : ∀ k < 129, 1 ≤ k → 0 < (rep 129 (phi0 - bhlM)).getD k 0 := by
  rw [rep_sub, rep_phi0_fast, rep_bhlM_fast 129 65 (by norm_num)]
  decide +kernel

/-- Item 9(b) [N30]: `0 < coeff k (φ₀ − M)` for `1 ≤ k ≤ 128`. -/
theorem phi0_sub_bhlM_pos : ∀ k, 1 ≤ k → k ≤ 128 → 0 < coeff k (phi0 - bhlM) := by
  intro k h1 h2
  have h := rep129_phi0_sub_bhlM_pos k (by omega) h1
  rwa [getD_rep_of_lt _ (by omega)] at h

end D28
