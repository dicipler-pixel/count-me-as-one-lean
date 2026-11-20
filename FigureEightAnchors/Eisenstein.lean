/-
Eisenstein integers Z[w], written a + b*w with w = exp(i*pi/3), so w^2 = w - 1.
Core Lean 4 only (no Mathlib).  Author of the programme: Jeromie Beasley.
-/
namespace FigureEightAnchors

/-- `a + b*w` with `w^2 = w - 1` (w is the primitive sixth root of unity). -/
structure Eis where
  re : Int
  im : Int
deriving DecidableEq, Repr

namespace Eis

instance : Zero Eis := ⟨⟨0, 0⟩⟩
instance : One Eis := ⟨⟨1, 0⟩⟩
instance : Add Eis := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg Eis := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub Eis := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
/-- (a + b w)(c + d w) = (ac - bd) + (ad + bc + bd) w, using w^2 = w - 1. -/
instance : Mul Eis := ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩⟩

/-- The generator w = exp(i*pi/3). -/
def w : Eis := ⟨0, 1⟩

/-- The norm a^2 + ab + b^2 = |a + b w|^2. -/
def norm (x : Eis) : Int := x.re * x.re + x.re * x.im + x.im * x.im

/-- Complex conjugate: conj(w) = 1 - w. -/
def conj (x : Eis) : Eis := ⟨x.re + x.im, -x.im⟩

@[simp] theorem add_def (x y : Eis) : x + y = ⟨x.re + y.re, x.im + y.im⟩ := rfl
@[simp] theorem sub_def (x y : Eis) : x - y = ⟨x.re - y.re, x.im - y.im⟩ := rfl
@[simp] theorem neg_def (x : Eis) : -x = ⟨-x.re, -x.im⟩ := rfl
@[simp] theorem mul_def (x y : Eis) :
    x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re + x.im * y.im⟩ := rfl
@[simp] theorem one_def : (1 : Eis) = ⟨1, 0⟩ := rfl
@[simp] theorem zero_def : (0 : Eis) = ⟨0, 0⟩ := rfl

/-- The defining equation: w^2 - w + 1 = 0. -/
theorem w_shape : w * w - w + 1 = 0 := by decide

/-- w^3 = -1. -/
theorem w_cubed : w * w * w = -1 := by decide

/-- w^6 = 1: w is a sixth root of unity. -/
theorem w_sixth : w * w * w * w * w * w = 1 := by decide

/-- w is not real: its w-coordinate is 1, not 0. -/
theorem w_not_real : w.im ≠ 0 := by decide

/-- Multiplication is commutative. -/
theorem mul_comm' (x y : Eis) : x * y = y * x := by
  simp only [mul_def, Eis.mk.injEq]; constructor <;> grind

/-- Multiplication is associative. -/
theorem mul_assoc' (x y z : Eis) : x * y * z = x * (y * z) := by
  simp only [mul_def, Eis.mk.injEq]; constructor <;> grind

/-- The norm is multiplicative. -/
theorem norm_mul (x y : Eis) : norm (x * y) = norm x * norm y := by
  simp only [norm, mul_def]; grind

/-- The norm is x times its conjugate. -/
theorem mul_conj (x : Eis) : x * conj x = ⟨norm x, 0⟩ := by
  simp only [norm, conj, mul_def, Eis.mk.injEq]; constructor <;> grind

/-- The norm is never negative: 4N = (2a + b)^2 + 3 b^2. -/
theorem four_norm (x : Eis) :
    4 * norm x = (2 * x.re + x.im) * (2 * x.re + x.im) + 3 * (x.im * x.im) := by
  simp only [norm]; grind

end Eis
end FigureEightAnchors
