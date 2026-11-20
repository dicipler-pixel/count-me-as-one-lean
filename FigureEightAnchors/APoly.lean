/-
The A-polynomial of the figure-eight knot,
  A(L, M) = M^4 L^2 + b(M) L + M^4,   b = -1 + M^2 + 2M^4 + M^6 - M^8,
is palindromic in L (the amphichiral involution L -> 1/L).  Its L-discriminant splits as
  b^2 - 4a^2 = (b + 2a)(b - 2a),
  b + 2a = -(x + 1)^2 (x^2 - 3x + 1),   b - 2a = -(x - 1)^2 (x^2 + x + 1),   x = M^2.
RELATIONS: the simple (ramification) factors are exactly the golden and regular branches of
Thurston's edge equation, SQUARED.  Used as a meridian eigenvalue, a golden shape lands on a
ramification point at L = +1 and a regular shape on one at L = -1.  Core Lean 4 only.
-/
namespace FigureEightAnchors
namespace APoly

open Lean.Grind

variable {R : Type} [CommRing R]

/-- Leading (and constant) coefficient a = M^4. -/
def a (M : R) : R := M * M * (M * M)
/-- Middle coefficient b = -1 + M^2 + 2M^4 + M^6 - M^8. -/
def b (M : R) : R :=
  -1 + M * M + 2 * (M * M * (M * M)) + M * M * (M * M) * (M * M) - M * M * (M * M) * (M * M * (M * M))
/-- The A-polynomial of 4_1. -/
def A (L M : R) : R := a M * L * L + b M * L + a M
/-- Its derivative in L. -/
def AL (L M : R) : R := 2 * a M * L + b M

/-- [rel: anchor/rule1] Expanded form: the standard A-polynomial of the figure-eight knot. -/
theorem A_expanded (L M : R) :
    A L M = -L + L * (M * M) + M * M * (M * M) + 2 * L * (M * M * (M * M)) +
      L * L * (M * M * (M * M)) + L * (M * M * (M * M) * (M * M)) -
      L * (M * M * (M * M) * (M * M * (M * M))) := by
  simp only [A, a, b]; grind

/-- [rel: mirror/rule3] Palindromic in L: with L * Linv = 1, L^2 A(Linv, M) = A(L, M).
    This is the amphichiral involution L -> 1/L. -/
theorem palindromic (L Linv M : R) (h : L * Linv = 1) :
    L * L * A Linv M = A L M := by
  simp only [A]; grind

/-- [rel: same-value] The discriminant splits into the two slices L = +1 and L = -1. -/
theorem disc_split (M : R) :
    b M * b M - 4 * (a M * a M) = (b M + 2 * a M) * (b M - 2 * a M) := by grind

/-- [rel: same-polynomial with Monodromy.h41_charpoly, Ladder.golden_squared]
    The L = +1 factor: b + 2a = -(x+1)^2 (x^2 - 3x + 1), x = M^2. -/
theorem plus_factor (M : R) :
    b M + 2 * a M = -((M * M + 1) * (M * M + 1)) * (M * M * (M * M) - 3 * (M * M) + 1) := by
  simp only [a, b]; grind

/-- [rel: same-polynomial with Ladder.regular_squared] The L = -1 factor:
    b - 2a = -(x-1)^2 (x^2 + x + 1), x = M^2. -/
theorem minus_factor (M : R) :
    b M - 2 * a M = -((M * M - 1) * (M * M - 1)) * (M * M * (M * M) + M * M + 1) := by
  simp only [a, b]; grind

/-- [rel: proof-step] On the slice L = 1 both A and its L-derivative equal b + 2a. -/
theorem slice_plus (M : R) : A 1 M = b M + 2 * a M ∧ AL 1 M = b M + 2 * a M := by
  simp only [A, AL]; constructor <;> grind

/-- [rel: proof-step] On the slice L = -1: A = 2a - b and the L-derivative is -(2a - b). -/
theorem slice_minus (M : R) : A (-1) M = -(b M - 2 * a M) ∧ AL (-1) M = b M - 2 * a M := by
  simp only [A, AL]; constructor <;> grind

/-- [rel: square-of, ruler/rule2] THE GOLDEN SHAPE IS A RAMIFICATION POINT AT L = +1:
    if z^2 - z - 1 = 0 then A(1, z) = 0 and dA/dL(1, z) = 0 (a double root in L). -/
theorem golden_ramifies (z : R) (h : z * z - z - 1 = 0) : A 1 z = 0 ∧ AL 1 z = 0 := by
  have hx : z * z * (z * z) - 3 * (z * z) + 1 = 0 := by grind
  obtain ⟨h1, h2⟩ := slice_plus z
  rw [h1, h2, plus_factor, hx]; constructor <;> grind

/-- [rel: square-of, anchor/rule1] THE REGULAR SHAPE IS A RAMIFICATION POINT AT L = -1:
    if z^2 - z + 1 = 0 then A(-1, z) = 0 and dA/dL(-1, z) = 0. -/
theorem regular_ramifies (z : R) (h : z * z - z + 1 = 0) : A (-1) z = 0 ∧ AL (-1) z = 0 := by
  have hx : z * z * (z * z) + z * z + 1 = 0 := by grind
  obtain ⟨h1, h2⟩ := slice_minus z
  rw [h1, h2, minus_factor, hx]; constructor <;> grind

/-- [rel: contrast] A NODE, not a ramification point: x = M^2 = 1 is a DOUBLE factor of b - 2a,
    so at M = 1 the L = -1 slice has A = 0 and dA/dL = 0 (and the curve is singular there). -/
theorem node_at_one : A (-1 : Int) 1 = 0 ∧ AL (-1 : Int) 1 = 0 := by decide

end APoly
end FigureEightAnchors
