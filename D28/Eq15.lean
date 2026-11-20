import D28.Qq2Table

/-!
# D28 item 10(a) [N27]: BHL Eq. (1.5) reduced, `coeffₖ φ₀ = coeff_{2k+2} ψ` for `k ≤ 128`
(previously `k ≤ 23`). `ψ` mod `q²⁵⁹` is assembled from the kernel-checked table `qq2Tab`.
-/

namespace D28

open PowerSeries DiracTimeD25.BHL

theorem fQq2Inv_259_tab : ∀ m < 16, fQq2Inv 259 (m + 1) = qq2Tab (m + 1)
  | 0, _ => fQq2Inv_259_1
  | 1, _ => fQq2Inv_259_2
  | 2, _ => fQq2Inv_259_3
  | 3, _ => fQq2Inv_259_4
  | 4, _ => fQq2Inv_259_5
  | 5, _ => fQq2Inv_259_6
  | 6, _ => fQq2Inv_259_7
  | 7, _ => fQq2Inv_259_8
  | 8, _ => fQq2Inv_259_9
  | 9, _ => fQq2Inv_259_10
  | 10, _ => fQq2Inv_259_11
  | 11, _ => fQq2Inv_259_12
  | 12, _ => fQq2Inv_259_13
  | 13, _ => fQq2Inv_259_14
  | 14, _ => fQq2Inv_259_15
  | 15, _ => fQq2Inv_259_16
  | _ + 16, h => absurd h (by omega)

theorem rep259_psi_tab :
    rep 259 psi = fSum 259 (fun m => fShift ((m + 1) ^ 2) (qq2Tab (m + 1))) 16 := by
  rw [rep_psi_fast 259 16 (by norm_num)]
  refine fSum_congr _ _ _ _ fun m hm => ?_
  show fShift ((m + 1) ^ 2) (fQq2Inv 259 (m + 1)) = fShift ((m + 1) ^ 2) (qq2Tab (m + 1))
  rw [fQq2Inv_259_tab m hm]

set_option maxRecDepth 100000 in
theorem rep_eq15_reduced_le128 :
    ∀ k < 129, (rep 129 phi0).getD k 0 = (rep 259 psi).getD (2 * k + 2) 0 := by
  rw [rep_phi0_fast, rep259_psi_tab]
  decide +kernel

/-- Item 10(a) [N27]: `coeffₖ φ₀ = coeff_{2k+2} ψ` for `k ≤ 128`. -/
theorem eq15_reduced_le128 : ∀ k ≤ 128, coeff k phi0 = coeff (2 * k + 2) psi := by
  intro k hk
  have h := rep_eq15_reduced_le128 k (by omega)
  rwa [getD_rep_of_lt _ (by omega), getD_rep_of_lt _ (by omega)] at h

/-- The previous list-level `k ≤ 64` statement, now a corollary. -/
theorem rep_eq15_reduced_le64 :
    ∀ k < 65, (rep 65 phi0).getD k 0 = (rep 131 psi).getD (2 * k + 2) 0 := by
  intro k hk
  rw [getD_rep_of_lt _ hk, getD_rep_of_lt _ (by omega)]
  exact eq15_reduced_le128 k (by omega)

/-- The previous `k ≤ 64` statement, now a corollary. -/
theorem eq15_reduced_le64 : ∀ k ≤ 64, coeff k phi0 = coeff (2 * k + 2) psi :=
  fun k hk => eq15_reduced_le128 k (by omega)

/-- **Eq. (1.5) modulo `q²⁵⁹`**: `2q²φ₀(q²) ≡ ψ(q) + ψ(−q)`, every coefficient of degree
`≤ 258` agrees (from the reduced form by the all-degree parity lemmas). -/
theorem eq15_mod_q259 : ∀ d < 259,
    coeff d ((2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero phi0)
      = coeff d (psi + rescale (-1) psi) := by
  intro d hd
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' d
  · rcases j with _ | k
    · rw [coeff_lhs15_zero, show 2 * 0 = 0 by rfl, coeff_add_rescale_neg, coeff_zero_psi, mul_zero]
    · rw [show 2 * (k + 1) = 2 * k + 2 by ring, coeff_lhs15_even, eq15_reduced_le128 k (by omega),
        show 2 * k + 2 = 2 * (k + 1) by ring, coeff_even_add_rescale_neg]
  · rw [coeff_lhs15_odd, coeff_odd_add_rescale_neg]

end D28
