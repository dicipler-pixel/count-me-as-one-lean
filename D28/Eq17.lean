import D28.Eq15  -- chained import: serialises the memory-heavy kernel checks under `lake build`

/-!
# D28 item 10(b) [N28]: BHL Eq. (1.7) exact through `q¹²⁸` (kernel `decide`, linear-time model)
-/

namespace D28

open PowerSeries DiracTimeD25.BHL

set_option maxRecDepth 100000 in
theorem rep129_eq17 :
    rep 129 ((2 : PowerSeries ℤ) + 2 * X ^ 2 * bhlM) = rep 129 (negInf + falseTheta) := by
  rw [show (2 : PowerSeries ℤ) * X ^ 2 * bhlM = X ^ 2 * (bhlM + bhlM) by ring, rep_add, rep_two,
    rep_X_pow_mul, rep_add, rep_bhlM_fast 129 65 (by norm_num), rep_add, rep_negInf_fast,
    rep_falseTheta_fast 129 10 (by norm_num)]
  decide +kernel

/-- Item 10(b) [N28]: `2 + 2q²M(q) = (−q)_∞ + ∑ q^{n(3n+1)/2}(1 − q^{2n+1})` in every degree
`d ≤ 128`. -/
theorem eq17_le128 : ∀ d ≤ 128,
    coeff d ((2 : PowerSeries ℤ) + 2 * X ^ 2 * bhlM) = coeff d (negInf + falseTheta) :=
  fun d hd => coeff_eq_of_rep_eq rep129_eq17 d (by omega)

end D28
