/-
The chirality anchor: the figure-eight knot 4_1 is its own mirror image
(amphichiral); the trefoil 3_1 is chiral.  Checked on Seifert matrices.

Seifert matrices (standard genus-one surfaces):
  4_1 : V = [[1, -1], [0, -1]]      3_1 : V = [[-1, 1], [0, -1]]
Alexander polynomial det(V - t V^T):  4_1 -> -t^2 + 3t - 1,   3_1 -> t^2 - t + 1.
Signature of V + V^T:  4_1 -> 0 (indefinite),  3_1 -> -2 (negative definite).
A nonzero signature is a mirror obstruction (signature flips sign under mirroring),
so the trefoil's handedness is a real, invariant asymmetry.  Core Lean 4 only.
-/
namespace FigureEightAnchors
namespace Chirality

/-- Integer 2x2 matrices [[a, b], [c, d]]. -/
structure Z2 where
  a : Int
  b : Int
  c : Int
  d : Int
deriving DecidableEq, Repr

def mul (x y : Z2) : Z2 :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩
def tr (x : Z2) : Z2 := ⟨x.a, x.c, x.b, x.d⟩   -- transpose
def neg (x : Z2) : Z2 := ⟨-x.a, -x.b, -x.c, -x.d⟩
def add (x y : Z2) : Z2 := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d⟩
def det (x : Z2) : Int := x.a * x.d - x.b * x.c

/-- Seifert matrix of the figure-eight knot. -/
def V41 : Z2 := ⟨1, -1, 0, -1⟩
/-- Seifert matrix of the (left-handed) trefoil. -/
def V31 : Z2 := ⟨-1, 1, 0, -1⟩

/-- Alexander polynomial coefficients of det(V - t V^T) = p0 + p1 t + p2 t^2. -/
def alex (V : Z2) : Int × Int × Int :=
  (det V,
   -(V.a * V.d + V.d * V.a - V.b * V.b - V.c * V.c),
   det V)

/-- 4_1 : Alexander polynomial -1 + 3t - t^2. -/
theorem alex_41 : alex V41 = (-1, 3, -1) := by decide
/-- 3_1 : Alexander polynomial 1 - t + t^2. -/
theorem alex_31 : alex V31 = (1, -1, 1) := by decide

/-- Knot determinants |Delta(-1)|: 5 for the figure-eight, 3 for the trefoil. -/
theorem det_41 : det (add V41 (tr V41)) = -5 := by decide
theorem det_31 : det (add V31 (tr V31)) = 3 := by decide

/-- Symmetrised forms. -/
def S41 : Z2 := add V41 (tr V41)
def S31 : Z2 := add V31 (tr V31)

/-- 4_1: V + V^T is INDEFINITE (det < 0), so its signature is 0. -/
theorem S41_indefinite : det S41 < 0 := by decide

/-- 3_1: V + V^T is NEGATIVE DEFINITE: top-left entry < 0 and det > 0,
    so its signature is -2.  Under mirroring the signature becomes +2. -/
theorem S31_neg_definite : S31.a < 0 ∧ det S31 > 0 := by decide

/-- Explicit negative definiteness: x^T S31 x < 0 for every nonzero integer x,
    since x^T S31 x = -2(x1^2 - x1 x2 + x2^2) and x1^2 - x1 x2 + x2^2 > 0. -/
theorem S31_form (x y : Int) (h : x ≠ 0 ∨ y ≠ 0) :
    S31.a * x * x + (S31.b + S31.c) * x * y + S31.d * y * y < 0 := by
  have hq : 4 * (x * x - x * y + y * y) = (2 * x - y) * (2 * x - y) + 3 * (y * y) := by grind
  have h1 : 0 ≤ (2 * x - y) * (2 * x - y) := by
    rcases Int.le_total 0 (2 * x - y) with k | k
    · exact Int.mul_nonneg k k
    · exact Int.mul_nonneg_of_nonpos_of_nonpos k k
  have h2 : 0 ≤ y * y := by
    rcases Int.le_total 0 y with k | k
    · exact Int.mul_nonneg k k
    · exact Int.mul_nonneg_of_nonpos_of_nonpos k k
  have hpos : 0 < x * x - x * y + y * y := by
    rcases h with hx | hy
    · by_cases hy0 : y = 0
      · subst hy0
        have : 0 < x * x := by
          rcases Int.lt_or_gt_of_ne hx with k | k
          · exact Int.mul_pos_of_neg_of_neg k k
          · exact Int.mul_pos k k
        grind
      · have : 0 < y * y := by
          rcases Int.lt_or_gt_of_ne hy0 with k | k
          · exact Int.mul_pos_of_neg_of_neg k k
          · exact Int.mul_pos k k
        omega
    · have : 0 < y * y := by
        rcases Int.lt_or_gt_of_ne hy with k | k
        · exact Int.mul_pos_of_neg_of_neg k k
        · exact Int.mul_pos k k
      omega
  simp only [S31, add, tr, V31]
  grind

/-- AMPHICHIRALITY CERTIFICATE for 4_1: an integer change of basis P with
    det P = -1 carrying V to -V^T (the Seifert matrix of the mirror image).
    P = [[-1, -1], [2, 1]]. -/
def P41 : Z2 := ⟨-1, -1, 2, 1⟩
theorem P41_unimodular : det P41 = 1 ∨ det P41 = -1 := by decide
theorem amphichiral_41 : mul (mul (tr P41) V41) P41 = neg (tr V41) := by decide

/-- Congruence preserves the determinant of the symmetric form: det(P^T S P) = det(P)^2 det(S). -/
theorem det_congr (P S : Z2) :
    det (mul (mul (tr P) S) P) = det P * det P * det S := by
  simp only [det, mul, tr]; grind

/-- CHIRALITY OF 3_1: no integer change of basis carries V31 to -V31^T.
    Proof: congruence keeps the symmetric part's top-left entry sign class.
    Here we prove the sharp form: P^T S31 P has a NEGATIVE top-left entry for every
    unimodular P, while -(S31) has top-left +2, so they cannot be equal. -/
theorem chiral_31 (P : Z2) (hP : det P = 1 ∨ det P = -1) :
    add (mul (mul (tr P) V31) P) (tr (mul (mul (tr P) V31) P)) ≠ neg S31 := by
  intro h
  have ha := congrArg Z2.a h
  simp only [add, mul, tr, neg, S31, V31] at ha
  have hne : P.a ≠ 0 ∨ P.c ≠ 0 := by
    by_cases h1 : P.a = 0
    · by_cases h2 : P.c = 0
      · simp only [det, h1, h2] at hP; omega
      · exact Or.inr h2
    · exact Or.inl h1
  have := S31_form P.a P.c hne
  simp only [S31, add, tr, V31] at this
  grind

/-- The trefoil's mirror really is a different Seifert class:
    3_1 cannot be its own mirror image (signature -2 vs +2). -/
theorem chiral_31_basic : ∀ P : Z2, (det P = 1 ∨ det P = -1) →
    mul (mul (tr P) V31) P ≠ neg (tr V31) := by
  intro P hP h
  apply chiral_31 P hP
  rw [h]; decide

end Chirality
end FigureEightAnchors
