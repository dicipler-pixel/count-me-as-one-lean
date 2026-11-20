import DiracTimeD25.CircleOdometer

/-!
# D28 easy exact items (new_lean_statements_v1, items 2, 5, 7, 8)

* Item 2 [N37]: `L * M^6 = -1 ↔ L = -(M^6)⁻¹` in any field, `M ≠ 0`.
* Item 5 [N22]: circle odometer at `a = 1/4 → 3/4` (no crossing, Δη = −1) and `1/4 → 5/4`
  (one crossing, Δη = 0 ≠ 2·SF).
* Item 7 [N31, N33]: ±2 surgery arithmetic (Moser fibre orders, orbifold Euler characteristics,
  lens control `L(2,1)`).
* Item 8 [N41]: S² shell sum `Σ_{l<n} 2(2l+1) = 2n²`.
-/

namespace D28

open DiracTimeD25

/-! ### Item 2 -/

/-- Item 2 [N37]: Dirac Time `L = −M⁻⁶` is CMaO's `L·M⁶ = −1`. -/
theorem dirac_cmao_LM6 {K : Type*} [Field K] (L M : K) (hM : M ≠ 0) :
    L * M ^ 6 = -1 ↔ L = -(M ^ 6)⁻¹ := by
  have h6 : M ^ 6 ≠ 0 := pow_ne_zero 6 hM
  constructor
  · intro h
    calc L = L * M ^ 6 * (M ^ 6)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ h6, mul_one]
      _ = -(M ^ 6)⁻¹ := by rw [h, neg_one_mul]
  · intro h
    rw [h, neg_mul, inv_mul_cancel₀ h6]

/-! ### Item 5 -/

theorem etaCircle_three_quarter : etaCircle (3 / 4) = -1 / 2 := by
  have h : ¬ ∃ n : ℤ, (3 / 4 : ℝ) = n := by
    rintro ⟨n, hn⟩
    have h1 : (0 : ℝ) < n := by rw [← hn]; norm_num
    have h2 : (n : ℝ) < 1 := by rw [← hn]; norm_num
    have h1' : 0 < n := by exact_mod_cast h1
    have h2' : n < 1 := by exact_mod_cast h2
    omega
  rw [etaCircle_of_not_int h, Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]
  norm_num

theorem etaCircle_five_quarter : etaCircle (5 / 4) = 1 / 2 := by
  have : (5 / 4 : ℝ) = 1 / 4 + 1 := by norm_num
  rw [this, etaCircle_add_one, etaCircle_quarter]

/-- Item 5(b) [N22]: `1/4 → 3/4` crosses no integer, yet `η` drifts by `−1`. -/
theorem odometer_no_crossing :
    Finset.Ioc ⌊(1 / 4 : ℝ)⌋ ⌊(3 / 4 : ℝ)⌋ = ∅ ∧ etaCircle (3 / 4) - etaCircle (1 / 4) = -1 := by
  have h1 : ⌊(1 / 4 : ℝ)⌋ = 0 := Int.floor_eq_iff.2 ⟨by norm_num, by norm_num⟩
  have h3 : ⌊(3 / 4 : ℝ)⌋ = 0 := Int.floor_eq_iff.2 ⟨by norm_num, by norm_num⟩
  refine ⟨by rw [h1, h3]; rfl, ?_⟩
  rw [etaCircle_three_quarter, etaCircle_quarter]; norm_num

/-- Item 5(c) [N22]: `1/4 → 5/4` has one crossing but `Δη = 0`, so `Δη ≠ 2·SF`. -/
theorem odometer_one_crossing :
    ⌊(5 / 4 : ℝ)⌋ - ⌊(1 / 4 : ℝ)⌋ = 1 ∧ etaCircle (5 / 4) - etaCircle (1 / 4) = 0 ∧
      etaCircle (5 / 4) - etaCircle (1 / 4) ≠ 2 * ((⌊(5 / 4 : ℝ)⌋ - ⌊(1 / 4 : ℝ)⌋ : ℤ) : ℝ) := by
  have h1 : ⌊(1 / 4 : ℝ)⌋ = 0 := Int.floor_eq_iff.2 ⟨by norm_num, by norm_num⟩
  have h5 : ⌊(5 / 4 : ℝ)⌋ = 1 := Int.floor_eq_iff.2 ⟨by norm_num, by norm_num⟩
  refine ⟨by rw [h1, h5]; rfl, ?_, ?_⟩
  · rw [etaCircle_five_quarter, etaCircle_quarter]; norm_num
  · rw [etaCircle_five_quarter, etaCircle_quarter, h1, h5]; norm_num

/-! ### Item 7 -/

/-- Item 7(a) [N31]: Moser fibre order `|2·3·1 − p|` for `p = ±2`: `4` and `8`. -/
theorem moser_fibre_orders :
    |(2 * 3 * 1 - 2 : ℤ)| = 4 ∧ |(2 * 3 * 1 - (-2) : ℤ)| = 8 := by
  decide

/-- Item 7(b) [N33]: orbifold Euler characteristics of `S²(2,3,4)` (`1/12`) and `S²(2,3,8)`
(`−1/24`). -/
theorem orbifold_euler :
    (2 - ((1 - 1 / 2) + (1 - 1 / 3) + (1 - 1 / 4)) : ℚ) = 1 / 12 ∧
      (2 - ((1 - 1 / 2) + (1 - 1 / 3) + (1 - 1 / 8)) : ℚ) = -1 / 24 := by
  norm_num

/-- Item 7(c) [N33]: lens control `L(2,1)`: `q² ≡ −1 (mod p)` with `p = 2, q = 1`. -/
theorem lens_L21 : (1 ^ 2 + 1) % 2 = 0 := by decide

/-! ### Item 8 -/

/-- Item 8 [N41]: S² shell sum `Σ_{l<n} 2(2l+1) = 2n²`. -/
theorem shell_sum (n : ℕ) : ∑ l ∈ Finset.range n, 2 * (2 * l + 1) = 2 * n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

end D28
