module

public import Mathlib

/-!
# D25.2 — Exact Alexander-polynomial wall criterion on `S¹`

Symmetrized Alexander polynomials
`Δ_{3₁}(t) = t − 1 + t⁻¹` (trefoil) and `Δ_{4₁}(t) = −t + 3 − t⁻¹` (figure-eight),
evaluated on the unit circle `t = e^{2πiα}`.

* `alex31_circle` : `Δ_{3₁}(e^{2πiα}) = 2 cos(2πα) − 1`.
* `alex31_circle_eq_zero_iff` : `Δ_{3₁}(e^{2πiα}) = 0 ↔ ∃ k : ℤ, α = k + 1/6 ∨ α = k − 1/6`.
* `alex41_circle` : `Δ_{4₁}(e^{2πiα}) = 3 − 2 cos(2πα)`, with `1 ≤` and `0 <` bounds,
  so `Δ_{4₁}` has no wall on `S¹`.
-/

@[expose] public section

namespace DiracTimeD25

open Complex

/-- Symmetrized trefoil Alexander polynomial `Δ_{3₁}(t) = t − 1 + t⁻¹`. -/
noncomputable def alex31 (t : ℂ) : ℂ := t - 1 + t⁻¹

/-- Symmetrized figure-eight Alexander polynomial `Δ_{4₁}(t) = −t + 3 − t⁻¹`. -/
noncomputable def alex41 (t : ℂ) : ℂ := -t + 3 - t⁻¹

/-- The point `e^{2πiα}` of the unit circle. -/
noncomputable def circ (α : ℝ) : ℂ := Complex.exp (2 * Real.pi * α * Complex.I)

theorem circ_ne_zero (α : ℝ) : circ α ≠ 0 := Complex.exp_ne_zero _

/-- Polynomial form: `t² − t + 1 = t · Δ_{3₁}(t)` for `t ≠ 0`. -/
theorem alex31_poly (t : ℂ) (ht : t ≠ 0) : t ^ 2 - t + 1 = t * alex31 t := by
  rw [alex31]; field_simp

/-- Polynomial form: `−t² + 3t − 1 = t · Δ_{4₁}(t)` for `t ≠ 0`. -/
theorem alex41_poly (t : ℂ) (ht : t ≠ 0) : -t ^ 2 + 3 * t - 1 = t * alex41 t := by
  rw [alex41]; field_simp

theorem circ_add_inv (α : ℝ) :
    circ α + (circ α)⁻¹ = ((2 * Real.cos (2 * Real.pi * α) : ℝ) : ℂ) := by
  rw [circ, ← Complex.exp_neg, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf

/-- `Δ_{3₁}(e^{2πiα}) = 2 cos(2πα) − 1`. -/
theorem alex31_circle (α : ℝ) :
    alex31 (circ α) = ((2 * Real.cos (2 * Real.pi * α) - 1 : ℝ) : ℂ) := by
  have h := circ_add_inv α
  rw [alex31]; push_cast at h ⊢; linear_combination h

/-- `Δ_{4₁}(e^{2πiα}) = 3 − 2 cos(2πα)`. -/
theorem alex41_circle (α : ℝ) :
    alex41 (circ α) = ((3 - 2 * Real.cos (2 * Real.pi * α) : ℝ) : ℂ) := by
  have h := circ_add_inv α
  rw [alex41]; push_cast at h ⊢; linear_combination -h

/-- `cos(2πα) = 1/2 ↔ α ≡ ±1/6 (mod 1)`. -/
theorem cos_two_pi_eq_half_iff (α : ℝ) :
    Real.cos (2 * Real.pi * α) = 1 / 2 ↔
      ∃ k : ℤ, α = (k : ℝ) + 1 / 6 ∨ α = (k : ℝ) - 1 / 6 := by
  rw [← Real.cos_pi_div_three, eq_comm, Real.cos_eq_cos_iff]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  constructor
  · rintro ⟨k, hk | hk⟩
    · refine ⟨k, Or.inl ?_⟩
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hπ)
      linear_combination hk
    · refine ⟨k, Or.inr ?_⟩
      apply mul_left_cancel₀ (mul_ne_zero two_ne_zero hπ)
      linear_combination hk
  · rintro ⟨k, hk | hk⟩
    · exact ⟨k, Or.inl (by rw [hk]; ring)⟩
    · exact ⟨k, Or.inr (by rw [hk]; ring)⟩

/-- **Trefoil wall criterion**: `Δ_{3₁}(e^{2πiα}) = 0 ↔ α ≡ ±1/6 (mod 1)`. -/
theorem alex31_circle_eq_zero_iff (α : ℝ) :
    alex31 (circ α) = 0 ↔ ∃ k : ℤ, α = (k : ℝ) + 1 / 6 ∨ α = (k : ℝ) - 1 / 6 := by
  rw [alex31_circle, Complex.ofReal_eq_zero, ← cos_two_pi_eq_half_iff]
  constructor <;> intro h <;> linarith

/-- Same criterion phrased as `α − 1/6 ∈ ℤ ∨ α + 1/6 ∈ ℤ`. -/
theorem alex31_circle_eq_zero_iff' (α : ℝ) :
    alex31 (circ α) = 0 ↔ ∃ k : ℤ, α - 1 / 6 = k ∨ α + 1 / 6 = k := by
  rw [alex31_circle_eq_zero_iff]
  constructor
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by rw [h]; ring)⟩
    · exact ⟨k, Or.inr (by rw [h]; ring)⟩
  · rintro ⟨k, h | h⟩
    · exact ⟨k, Or.inl (by linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩

/-- Polynomial form of the trefoil wall criterion: `z² − z + 1 = 0` at `z = e^{2πiα}`. -/
theorem alex31_poly_circle_eq_zero_iff (α : ℝ) :
    circ α ^ 2 - circ α + 1 = 0 ↔ ∃ k : ℤ, α = (k : ℝ) + 1 / 6 ∨ α = (k : ℝ) - 1 / 6 := by
  rw [alex31_poly _ (circ_ne_zero α), mul_eq_zero, or_iff_right (circ_ne_zero α),
    alex31_circle_eq_zero_iff]

/-- `1 ≤ 3 − 2 cos(2πα)`. -/
theorem one_le_alex41_real (α : ℝ) : 1 ≤ 3 - 2 * Real.cos (2 * Real.pi * α) := by
  have := Real.cos_le_one (2 * Real.pi * α); linarith

/-- `0 < 3 − 2 cos(2πα)`. -/
theorem alex41_real_pos (α : ℝ) : 0 < 3 - 2 * Real.cos (2 * Real.pi * α) := by
  have := one_le_alex41_real α; linarith

/-- **Figure-eight: no walls on `S¹`**: `Δ_{4₁}(e^{2πiα}) ≠ 0` for every real `α`. -/
theorem alex41_circle_ne_zero (α : ℝ) : alex41 (circ α) ≠ 0 := by
  rw [alex41_circle, Ne, Complex.ofReal_eq_zero]
  exact (alex41_real_pos α).ne'

/-- Polynomial form: `−z² + 3z − 1 ≠ 0` on `S¹`. -/
theorem alex41_poly_circle_ne_zero (α : ℝ) : -circ α ^ 2 + 3 * circ α - 1 ≠ 0 := by
  rw [alex41_poly _ (circ_ne_zero α)]
  exact mul_ne_zero (circ_ne_zero α) (alex41_circle_ne_zero α)

/-- Non-vacuity: the trefoil does have a wall, at `α = 1/6`. -/
theorem alex31_wall_at_sixth : alex31 (circ (1 / 6)) = 0 :=
  (alex31_circle_eq_zero_iff _).2 ⟨0, Or.inl (by simp)⟩

end DiracTimeD25

end
