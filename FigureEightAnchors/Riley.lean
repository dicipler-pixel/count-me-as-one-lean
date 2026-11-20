/-
Riley's parabolic representation of the figure-eight knot group.

Knot group (two meridian generators):   G = < a, b | w a = b w >,  w = a^-1 b a b^-1.
Riley (1975): a -> [[1,1],[0,1]],  b -> [[1,0],[c,1]]  is a representation
exactly when c^2 - c + 1 = 0  -- the SAME polynomial as Thurston's regular
tetrahedron shape.  Core Lean 4 only.
-/
import FigureEightAnchors.Eisenstein

namespace FigureEightAnchors
namespace Riley

open Lean.Grind

/-- 2x2 matrices [[a, b], [c, d]]. -/
structure M2 (R : Type) where
  a : R
  b : R
  c : R
  d : R
deriving DecidableEq

variable {R : Type}

def mul [CommRing R] (x y : M2 R) : M2 R :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

def det [CommRing R] (x : M2 R) : R := x.a * x.d - x.b * x.c
def tr [CommRing R] (x : M2 R) : R := x.a + x.d

/-- Meridian a -> [[1,1],[0,1]]. -/
def A [CommRing R] : M2 R := ⟨1, 1, 0, 1⟩
/-- Its inverse. -/
def Ainv [CommRing R] : M2 R := ⟨1, -1, 0, 1⟩
/-- Meridian b -> [[1,0],[c,1]]. -/
def B [CommRing R] (c : R) : M2 R := ⟨1, 0, c, 1⟩
/-- Its inverse. -/
def Binv [CommRing R] (c : R) : M2 R := ⟨1, 0, -c, 1⟩

/-- The word w = a^-1 b a b^-1. -/
def W [CommRing R] (c : R) : M2 R := mul (mul (mul Ainv (B c)) A) (Binv c)

theorem A_inv [CommRing R] : mul (A : M2 R) Ainv = ⟨1, 0, 0, 1⟩ := by
  simp only [mul, A, Ainv, M2.mk.injEq]; grind

theorem B_inv [CommRing R] (c : R) : mul (B c) (Binv c) = ⟨1, 0, 0, 1⟩ := by
  simp only [mul, B, Binv, M2.mk.injEq]; grind

/-- Both meridians are parabolic and unimodular: trace 2, determinant 1. -/
theorem A_parabolic [CommRing R] : tr (A : M2 R) = 2 ∧ det (A : M2 R) = 1 := by
  simp only [tr, det, A]; grind

theorem B_parabolic [CommRing R] (c : R) : tr (B c) = 2 ∧ det (B c) = 1 := by
  simp only [tr, det, B]; grind

/-- THE RELATION DEFECT, entry by entry:
      w a - b w = [[0, p], [-c p, 0]]   with   p = c^2 - c + 1.
    So the knot-group relation is controlled by one polynomial. -/
theorem relation_defect [CommRing R] (c : R) :
    (mul (W c) A).a - (mul (B c) (W c)).a = 0 ∧
    (mul (W c) A).b - (mul (B c) (W c)).b = c * c - c + 1 ∧
    (mul (W c) A).c - (mul (B c) (W c)).c = -(c * (c * c - c + 1)) ∧
    (mul (W c) A).d - (mul (B c) (W c)).d = 0 := by
  simp only [W, mul, A, Ainv, B, Binv]; grind

/-- If c^2 - c + 1 = 0 the relation w a = b w holds: a representation. -/
theorem relation_of_shape [CommRing R] (c : R) (h : c * c - c + 1 = 0) :
    mul (W c) A = mul (B c) (W c) := by
  simp only [W, mul, A, Ainv, B, Binv, M2.mk.injEq]; grind

/-- Conversely, the relation forces c^2 - c + 1 = 0 (read off the top-right entry). -/
theorem shape_of_relation [CommRing R] (c : R)
    (h : mul (W c) A = mul (B c) (W c)) : c * c - c + 1 = 0 := by
  have hb := congrArg M2.b h
  simp only [W, mul, A, Ainv, B, Binv] at hb
  grind

/-- The Riley parameter and the Thurston shape obey one and the same equation. -/
theorem riley_iff_shape [CommRing R] (c : R) :
    mul (W c) A = mul (B c) (W c) ↔ c * c - c + 1 = 0 :=
  ⟨shape_of_relation c, relation_of_shape c⟩

/-- The peripheral trace: tr(a b) = 2 + c.  At the shape root this is not 2,
    so a and b do not generate a parabolic pencil together. -/
theorem trace_ab [CommRing R] (c : R) : tr (mul A (B c)) = 2 + c := by
  simp only [tr, mul, A, B]; grind

/-- The commutator trace tr[a, b] = 2 + c^2: at the shape root it equals 1 + c. -/
theorem trace_commutator [CommRing R] (c : R) :
    tr (mul (mul (mul A (B c)) Ainv) (Binv c)) = 2 + c * c := by
  simp only [tr, mul, A, Ainv, B, Binv]; grind

end Riley
end FigureEightAnchors
