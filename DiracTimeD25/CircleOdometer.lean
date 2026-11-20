module

public import Mathlib

/-!
# D25.3 — Exact 1D circle-odometer identity (Dirac Time `DT-E15`, §8.2)

`D_a = −i d/dx + a` on periodic functions has eigenvalues `λ_k(a) = k + a`, `k ∈ ℤ`.
For non-integer `a`, `η(D_a) = 1 − 2{a}`; for integer `a` the nonzero spectrum is symmetric,
so `η = 0` (zero mode excluded). For non-integer endpoints the spectral flow is
`SF(a₀ → a₁) = ⌊a₁⌋ − ⌊a₀⌋ = (a₁ − a₀) + ½(η₁ − η₀)`.

* `floor_sub_floor_eq` : the identity with `1 − 2{a}` written out, for **all** real `a₀, a₁`.
* `odometer_identity` : the same with `etaCircle`, for non-integer `a₀, a₁` (DT-E15).
* `mem_crossings_iff`, `floor_sub_floor_eq_card_crossings` : for `a₀ ≤ a₁` non-integer,
  `⌊a₁⌋ − ⌊a₀⌋` is the number of integers `m` with `a₀ < m < a₁`, i.e. the number of times an
  eigenvalue `k + a` crosses `0` (at `a = −k`) along the path.
* `etaCircle_add_one`, `floor_add_one_sub_floor` : `a` and `a + 1` have the same eta, yet the
  path between them has spectral flow 1 (no endpoint-only formula for path history).
-/

@[expose] public section

namespace DiracTimeD25

/-- Eta invariant of the circle operator `D_a` (zero mode excluded). -/
noncomputable def etaCircle (a : ℝ) : ℝ :=
  by classical exact if ∃ n : ℤ, a = n then 0 else 1 - 2 * Int.fract a

theorem etaCircle_of_not_int {a : ℝ} (ha : ¬ ∃ n : ℤ, a = n) :
    etaCircle a = 1 - 2 * Int.fract a := by
  rw [etaCircle, ite_eq_right_of_eq_false _ _ (eq_false ha)]

theorem etaCircle_intCast (n : ℤ) : etaCircle n = 0 := by
  rw [etaCircle, ite_eq_left_of_eq_true _ _ (eq_true ⟨n, rfl⟩)]

/-- The odometer identity with `1 − 2{a}` written out; holds for all real `a₀, a₁`. -/
theorem floor_sub_floor_eq (a₀ a₁ : ℝ) :
    (⌊a₁⌋ : ℝ) - (⌊a₀⌋ : ℝ)
      = (a₁ - a₀) + (1 / 2 : ℝ) * ((1 - 2 * Int.fract a₁) - (1 - 2 * Int.fract a₀)) := by
  rw [Int.fract, Int.fract]; ring

/-- **DT-E15, circle odometer**: for non-integer `a₀, a₁`,
`⌊a₁⌋ − ⌊a₀⌋ = (a₁ − a₀) + ½(η(D_{a₁}) − η(D_{a₀}))`. -/
theorem odometer_identity {a₀ a₁ : ℝ} (h₀ : ¬ ∃ n : ℤ, a₀ = n) (h₁ : ¬ ∃ n : ℤ, a₁ = n) :
    (⌊a₁⌋ : ℝ) - (⌊a₀⌋ : ℝ) = (a₁ - a₀) + (1 / 2 : ℝ) * (etaCircle a₁ - etaCircle a₀) := by
  rw [etaCircle_of_not_int h₀, etaCircle_of_not_int h₁, floor_sub_floor_eq]

/-- For non-integer `a₀, a₁`, the integers in `(⌊a₀⌋, ⌊a₁⌋]` are exactly those strictly
between `a₀` and `a₁`. -/
theorem mem_crossings_iff {a₀ a₁ : ℝ} (h₁ : ¬ ∃ n : ℤ, a₁ = n) (m : ℤ) :
    m ∈ Finset.Ioc ⌊a₀⌋ ⌊a₁⌋ ↔ a₀ < m ∧ (m : ℝ) < a₁ := by
  rw [Finset.mem_Ioc, Int.floor_lt, Int.le_floor]
  refine and_congr Iff.rfl ⟨fun h => lt_of_le_of_ne h fun he => h₁ ⟨m, he.symm⟩, le_of_lt⟩

/-- **Spectral flow = crossing count**: for `a₀ ≤ a₁` non-integer, `⌊a₁⌋ − ⌊a₀⌋` is the number
of integers strictly between `a₀` and `a₁`. -/
theorem floor_sub_floor_eq_card_crossings {a₀ a₁ : ℝ} (h : a₀ ≤ a₁)
    (h₁ : ¬ ∃ n : ℤ, a₁ = n) :
    ⌊a₁⌋ - ⌊a₀⌋ = ((Finset.Ioc ⌊a₀⌋ ⌊a₁⌋).card : ℤ) ∧
      ∀ m : ℤ, m ∈ Finset.Ioc ⌊a₀⌋ ⌊a₁⌋ ↔ a₀ < m ∧ (m : ℝ) < a₁ := by
  refine ⟨?_, mem_crossings_iff h₁⟩
  rw [Int.card_Ioc, Int.toNat_of_nonneg (sub_nonneg.2 (Int.floor_mono h))]

/-- Combined DT-E15 statement: crossing count = `(a₁ − a₀) + ½(η₁ − η₀)`. -/
theorem card_crossings_eq_odometer {a₀ a₁ : ℝ} (h : a₀ ≤ a₁)
    (h₀ : ¬ ∃ n : ℤ, a₀ = n) (h₁ : ¬ ∃ n : ℤ, a₁ = n) :
    (((Finset.Ioc ⌊a₀⌋ ⌊a₁⌋).card : ℤ) : ℝ)
      = (a₁ - a₀) + (1 / 2 : ℝ) * (etaCircle a₁ - etaCircle a₀) := by
  rw [← (floor_sub_floor_eq_card_crossings h h₁).1, Int.cast_sub, odometer_identity h₀ h₁]

theorem etaCircle_add_one (a : ℝ) : etaCircle (a + 1) = etaCircle a := by
  by_cases ha : ∃ n : ℤ, a = n
  · obtain ⟨n, rfl⟩ := ha
    have : (n : ℝ) + 1 = ((n + 1 : ℤ) : ℝ) := by push_cast; ring
    rw [this, etaCircle_intCast, etaCircle_intCast]
  · have ha1 : ¬ ∃ n : ℤ, a + 1 = n :=
      fun ⟨n, hn⟩ => ha ⟨n - 1, by push_cast; linarith⟩
    rw [etaCircle_of_not_int ha, etaCircle_of_not_int ha1, Int.fract_add_one]

/-- `a` and `a + 1`: same eta, but spectral flow `1` along the connecting path. -/
theorem floor_add_one_sub_floor (a : ℝ) : ⌊a + 1⌋ - ⌊a⌋ = 1 := by
  rw [Int.floor_add_one]; ring

/-- Non-vacuity: `η(D_{1/4}) = 1/2`. -/
theorem etaCircle_quarter : etaCircle (1 / 4) = 1 / 2 := by
  have h : ¬ ∃ n : ℤ, (1 / 4 : ℝ) = n := by
    rintro ⟨n, hn⟩
    have h1 : (0 : ℝ) < n := by linarith
    have h2 : (n : ℝ) < 1 := by linarith
    have h3 : (0 : ℤ) < n := by exact_mod_cast h1
    have h4 : n < (1 : ℤ) := by exact_mod_cast h2
    omega
  rw [etaCircle_of_not_int h, Int.fract_eq_self.2 ⟨by norm_num, by norm_num⟩]
  norm_num

end DiracTimeD25

end
