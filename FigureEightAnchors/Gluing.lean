/-
Thurston's gluing (edge) equation for the figure-eight knot complement,
built from two ideal tetrahedra with shapes z and w:

    z (z - 1) w (w - 1) = 1.

Source: W. P. Thurston, The Geometry and Topology of Three-Manifolds, ch. 4.
The complete hyperbolic structure is z = w = exp(i*pi/3): two REGULAR ideal
tetrahedra.  Here: the algebra of that equation, in any commutative ring and
in Z[w].  Core Lean 4 only.
-/
import FigureEightAnchors.Eisenstein

namespace FigureEightAnchors
namespace Gluing

open Lean.Grind

/-- Left side minus right side of Thurston's edge equation. -/
def edge {R : Type} [CommRing R] (z w : R) : R := z * (z - 1) * (w * (w - 1)) - 1

/-- On the symmetric slice z = w the edge equation FACTORS:
    z^2 (z-1)^2 - 1 = (z^2 - z + 1)(z^2 - z - 1).
    First factor: the regular tetrahedron (complex root exp(i*pi/3)).
    Second factor: the golden-ratio branch (real roots, flat tetrahedra). -/
theorem edge_symmetric_factor {R : Type} [CommRing R] (z : R) :
    edge z z = (z * z - z + 1) * (z * z - z - 1) := by
  simp only [edge]; grind

/-- Any root of z^2 - z + 1 solves the edge equation with w = z. -/
theorem regular_solves_edge {R : Type} [CommRing R] (z : R)
    (h : z * z - z + 1 = 0) : edge z z = 0 := by
  rw [edge_symmetric_factor, h]; grind

/-- Any root of z^2 - z - 1 (golden ratio branch) ALSO solves the bare edge
    equation with w = z.  The edge equation alone does not pick the geometry. -/
theorem golden_solves_edge {R : Type} [CommRing R] (z : R)
    (h : z * z - z - 1 = 0) : edge z z = 0 := by
  rw [edge_symmetric_factor, h]; grind

/-- A root of z^2 - z + 1 has z (z - 1) = -1: each tetrahedron contributes -1. -/
theorem regular_half {R : Type} [CommRing R] (z : R)
    (h : z * z - z + 1 = 0) : z * (z - 1) = -1 := by grind

/-- A root of z^2 - z + 1 is a sixth root of unity (z^3 = -1). -/
theorem regular_cubed {R : Type} [CommRing R] (z : R)
    (h : z * z - z + 1 = 0) : z * z * z = -1 := by grind

/-- A root of z^2 - z + 1 is fixed by the shape cycle z -> 1/(1-z):
    z (1 - z) = 1, so all three dihedral shapes of the tetrahedron are equal.
    That is what "regular" means for an ideal tetrahedron. -/
theorem regular_cycle_fixed {R : Type} [CommRing R] (z : R)
    (h : z * z - z + 1 = 0) : z * (1 - z) = 1 := by grind

/-- Conversely: a shape fixed by the cycle is a root of z^2 - z + 1. -/
theorem cycle_fixed_regular {R : Type} [CommRing R] (z : R)
    (h : z * (1 - z) = 1) : z * z - z + 1 = 0 := by grind

/-- The golden branch is NOT fixed by the shape cycle: there z (1 - z) = -1. -/
theorem golden_cycle {R : Type} [CommRing R] (z : R)
    (h : z * z - z - 1 = 0) : z * (1 - z) = -1 := by grind

/-- In Z[w]: Thurston's edge equation holds at z = w = exp(i*pi/3). -/
theorem eis_edge : Eis.w * (Eis.w - 1) * (Eis.w * (Eis.w - 1)) = 1 := by decide

/-- In Z[w]: each regular tetrahedron contributes exactly -1. -/
theorem eis_half : Eis.w * (Eis.w - 1) = -1 := by decide

/-- In Z[w]: the regular shape is fixed by the cycle, w (1 - w) = 1. -/
theorem eis_cycle_fixed : Eis.w * (1 - Eis.w) = 1 := by decide

/-- The conjugate shape 1 - w = exp(-i*pi/3) solves the same equation:
    the mirror-image structure. -/
theorem eis_edge_conj :
    Eis.conj Eis.w * (Eis.conj Eis.w - 1) * (Eis.conj Eis.w * (Eis.conj Eis.w - 1)) = 1 := by
  decide

/-- No INTEGER shape solves the symmetric edge equation: over the integers
    neither factor has a root (discriminants -3 and 5). -/
theorem no_integer_regular (n : Int) : n * n - n + 1 ≠ 0 := by
  intro h
  have h1 : 0 ≤ n * (n - 1) := by
    rcases (by omega : 1 ≤ n ∨ n ≤ 0) with hn | hn
    · exact Int.mul_nonneg (by omega) (by omega)
    · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have h2 : n * (n - 1) = n * n - n := by grind
  generalize n * n = m at h h2
  omega

/-- No integer shape solves the golden factor either: n^2 - n - 1 is always odd. -/
theorem no_integer_golden (n : Int) : n * n - n - 1 ≠ 0 := by
  intro h
  have hr : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hr with hr | hr
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k := ⟨n / 2, by omega⟩
    have e : 2 * k * (2 * k) - 2 * k - 1 = 2 * (2 * (k * k) - k) - 1 := by grind
    rw [e] at h; omega
  · obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have e : (2 * k + 1) * (2 * k + 1) - (2 * k + 1) - 1 = 2 * (2 * (k * k) + k) - 1 := by grind
    rw [e] at h; omega

end Gluing
end FigureEightAnchors
