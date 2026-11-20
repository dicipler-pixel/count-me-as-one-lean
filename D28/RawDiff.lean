import DiracTimeD25.BhlBoundaryTest

/-!
# D28 item 9 [N30]: raw-difference ruler, term identity
-/

namespace D28

open PowerSeries DiracTimeD25.BHL

theorem negPoch_eq_prod_Icc (m : ℕ) :
    negPoch m = ∏ j ∈ Finset.Icc 1 m, (1 + X ^ j : PowerSeries ℤ) := by
  induction m with
  | zero => simp [negPoch]
  | succ k ih => rw [negPoch_succ, ih, Finset.prod_Icc_succ_top (by omega), mul_comm]

/-- Item 9(a): `qⁿ(1 − qⁿ)(−q)_{2n+1} = qⁿ(1 − q⁴ⁿ) ∏_{j ∈ [1, 2n+1] \ {n, 2n}} (1 + qʲ)`. -/
theorem rawDiff_term (n : ℕ) (hn : 1 ≤ n) :
    X ^ n * (1 - X ^ n) * negPoch (2 * n + 1)
      = X ^ n * (1 - X ^ (4 * n)) *
          ∏ j ∈ Finset.Icc 1 (2 * n + 1) \ {n, 2 * n}, (1 + X ^ j : PowerSeries ℤ) := by
  have h1 : n ∈ Finset.Icc 1 (2 * n + 1) := Finset.mem_Icc.2 ⟨hn, by omega⟩
  have h2 : 2 * n ∈ (Finset.Icc 1 (2 * n + 1)).erase n :=
    Finset.mem_erase.2 ⟨by omega, Finset.mem_Icc.2 ⟨by omega, by omega⟩⟩
  have hs : Finset.Icc 1 (2 * n + 1) \ {n, 2 * n} = ((Finset.Icc 1 (2 * n + 1)).erase n).erase (2 * n) := by
    ext j; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase]
    tauto
  rw [negPoch_eq_prod_Icc, ← Finset.mul_prod_erase _ _ h1, ← Finset.mul_prod_erase _ _ h2, hs]
  ring
