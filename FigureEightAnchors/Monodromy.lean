/-
Monodromy of the two genus-one fibred knots, read from their Seifert matrices:
h = V^{-1} V^T.  Figure-eight: the cat map [[2,1],[1,1]] (trace 3, hyperbolic).
Trefoil: [[0,1],[-1,1]] (trace 1, elliptic, order 6).
RELATIONS: the trefoil's monodromy polynomial is the regular-tetrahedron / Riley
polynomial z^2 - z + 1; the figure-eight's monodromy polynomial is its Alexander
polynomial t^2 - 3t + 1, which is the golden branch squared.  Core Lean 4 only.
-/
import FigureEightAnchors.Chirality

namespace FigureEightAnchors
namespace Monodromy

open Chirality

def I2 : Z2 := ⟨1, 0, 0, 1⟩
def trace (x : Z2) : Int := x.a + x.d

/-- [rel: anchor/rule1] V41 is its own inverse. -/
theorem V41_inv : mul V41 V41 = I2 := by decide
/-- Inverse of the trefoil Seifert matrix. -/
def V31inv : Z2 := ⟨-1, -1, 0, -1⟩
/-- [rel: anchor/rule1] -/
theorem V31_inv : mul V31 V31inv = I2 := by decide

/-- Figure-eight monodromy h41 = V41^{-1} V41^T. -/
def h41 : Z2 := mul V41 (tr V41)
/-- Trefoil monodromy h31 = V31^{-1} V31^T. -/
def h31 : Z2 := mul V31inv (tr V31)

/-- [rel: anchor/rule1] The figure-eight monodromy is the cat map [[2,1],[1,1]]. -/
theorem h41_cat : h41 = ⟨2, 1, 1, 1⟩ := by decide
/-- [rel: anchor/rule1] The trefoil monodromy is [[0,1],[-1,1]]. -/
theorem h31_form : h31 = ⟨0, 1, -1, 1⟩ := by decide

/-- [rel: ladder T=3] Trace 3, determinant 1: hyperbolic (|T| > 2), the gap side. -/
theorem h41_hyperbolic : trace h41 = 3 ∧ det h41 = 1 := by decide
/-- [rel: ladder T=1] Trace 1, determinant 1: elliptic (|T| < 2), the band side. -/
theorem h31_elliptic : trace h31 = 1 ∧ det h31 = 1 := by decide

/-- [rel: same-polynomial with Chirality.alex_41] Cayley-Hamilton for h41:
    h^2 = 3h - I, i.e. its characteristic polynomial is t^2 - 3t + 1, the Alexander
    polynomial of 4_1 (up to the overall sign in alex_41). -/
theorem h41_charpoly : mul h41 h41 = add (mul ⟨3, 0, 0, 3⟩ h41) (neg I2) := by decide

/-- [rel: same-polynomial with Gluing.regular_cycle_fixed, Riley.riley_iff_shape,
    Chirality.alex_31] Cayley-Hamilton for h31: h^2 = h - I, characteristic polynomial
    t^2 - t + 1 -- the regular-tetrahedron / Riley polynomial. -/
theorem h31_charpoly : mul h31 h31 = add h31 (neg I2) := by decide

/-- [rel: chiral-source/rule3, same-root with Eisenstein.w_cubed] h31^3 = -I. -/
theorem h31_cubed : mul (mul h31 h31) h31 = neg I2 := by decide
/-- [rel: chiral-source/rule3, same-root with Eisenstein.w_sixth] h31^6 = I:
    the chiral knot's monodromy has order 6, exactly like w = exp(i*pi/3). -/
theorem h31_order6 :
    mul (mul (mul (mul (mul h31 h31) h31) h31) h31) h31 = I2 := by decide

/-- Powers of h41. -/
def pow41 : Nat → Z2
  | 0 => I2
  | n + 1 => mul (pow41 n) h41

/-- [rel: ruler/rule2, ladder T=3 step 5, external Q1] trace(h41^5) = 123 = phi^10 + phi^-10:
    five turns of the figure-eight monodromy stretch exactly by Q1's convergence ratio. -/
theorem h41_trace5 : trace (pow41 5) = 123 := by decide
/-- [rel: ruler/rule2] h41 is never periodic in the first 12 powers (no return to I). -/
theorem h41_not_periodic : ∀ k, k ∈ [1,2,3,4,5,6,7,8,9,10,11,12] → pow41 k ≠ I2 := by decide

end Monodromy
end FigureEightAnchors
