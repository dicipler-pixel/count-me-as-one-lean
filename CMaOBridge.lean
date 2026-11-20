import DiracTimeD25.AlexanderWall
import FigureEightAnchors.Gluing
import FigureEightAnchors.Chirality

/-!
# Bridge: D25 trefoil walls on `S¹` are CMaO's regular-tetrahedron shapes

`DiracTimeD25.AlexanderWall` locates the walls of the trefoil Alexander polynomial on the
unit circle; `FigureEightAnchors.Gluing` (Count Me as One, core Lean, any `Lean.Grind.CommRing`)
proves that a root of `z² − z + 1` solves Thurston's edge equation, contributes `−1` per
tetrahedron, and is a sixth root of unity (`z³ = −1`).  Here the CMaO ring-generic theorems are
instantiated at `ℂ` on the D25 walls, so the two pictures are joined by proofs, not analogy.
The Laurent polynomials of D25 are also tied to CMaO's Seifert-matrix coefficients
`Chirality.alex V` (`det(V − tVᵀ) = p₀ + p₁t + p₂t²`).
-/

namespace DiracTimeD25.Bridge

open DiracTimeD25 FigureEightAnchors.Gluing

/-- A trefoil wall point `z = e^{2πiα}` (where `Δ_{3₁}(z) = 0`) is a root of `z·z − z + 1`. -/
theorem wall_regular_poly {α : ℝ} (h : alex31 (circ α) = 0) :
    circ α * circ α - circ α + 1 = 0 := by
  have hp := alex31_poly (circ α) (circ_ne_zero α)
  rw [h, mul_zero] at hp
  rw [← hp]; ring

/-- Every trefoil wall on `S¹` solves Thurston's figure-eight edge equation on the slice `z = w`
(CMaO `Gluing.regular_solves_edge`, instantiated at `ℂ`). -/
theorem wall_solves_edge {α : ℝ} (h : alex31 (circ α) = 0) : edge (circ α) (circ α) = 0 :=
  regular_solves_edge (circ α) (wall_regular_poly h)

/-- At a trefoil wall each tetrahedron contributes exactly `−1` (CMaO `Gluing.regular_half`). -/
theorem wall_half {α : ℝ} (h : alex31 (circ α) = 0) : circ α * (circ α - 1) = -1 :=
  regular_half (circ α) (wall_regular_poly h)

/-- A trefoil wall is a sixth root of unity, `z³ = −1` (CMaO `Gluing.regular_cubed`). -/
theorem wall_cubed {α : ℝ} (h : alex31 (circ α) = 0) : circ α * circ α * circ α = -1 :=
  regular_cubed (circ α) (wall_regular_poly h)

/-- Non-vacuity: the wall at `α = 1/6` solves the edge equation. -/
theorem sixth_solves_edge : edge (circ (1 / 6)) (circ (1 / 6)) = 0 :=
  wall_solves_edge ((alex31_circle_eq_zero_iff _).2 ⟨0, Or.inl (by simp)⟩)

/-- D25's symmetrized trefoil polynomial is CMaO's Seifert-matrix Alexander polynomial:
`t · Δ_{3₁}(t) = p₀ + p₁ t + p₂ t²` with `(p₀, p₁, p₂) = Chirality.alex V31`. -/
theorem alex31_eq_seifert (t : ℂ) (ht : t ≠ 0) :
    t * alex31 t = ((FigureEightAnchors.Chirality.alex FigureEightAnchors.Chirality.V31).1 : ℂ)
      + ((FigureEightAnchors.Chirality.alex FigureEightAnchors.Chirality.V31).2.1 : ℂ) * t
      + ((FigureEightAnchors.Chirality.alex FigureEightAnchors.Chirality.V31).2.2 : ℂ) * t ^ 2 := by
  rw [FigureEightAnchors.Chirality.alex_31, ← alex31_poly t ht]; push_cast; ring

/-- Same for the figure-eight: `t · Δ_{4₁}(t) = p₀ + p₁ t + p₂ t²` with
`(p₀, p₁, p₂) = Chirality.alex V41`. -/
theorem alex41_eq_seifert (t : ℂ) (ht : t ≠ 0) :
    t * alex41 t = ((FigureEightAnchors.Chirality.alex FigureEightAnchors.Chirality.V41).1 : ℂ)
      + ((FigureEightAnchors.Chirality.alex FigureEightAnchors.Chirality.V41).2.1 : ℂ) * t
      + ((FigureEightAnchors.Chirality.alex FigureEightAnchors.Chirality.V41).2.2 : ℂ) * t ^ 2 := by
  rw [FigureEightAnchors.Chirality.alex_41, ← alex41_poly t ht]; push_cast; ring

end DiracTimeD25.Bridge
