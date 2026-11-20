/-
The trace ladder of a self-reciprocal pair {x, 1/x}: t_0 = 2, t_1 = T,
t_{k+1} = T t_k - t_{k-1}.  If x + y = T and x y = 1 then x^k + y^k = t_k.
RELATIONS: one ladder carries the trefoil (T=1, periodic), the figure-eight
(T=3, Q(sqrt5), reaching 123 = Q1's phi^10 at k=5) and Apery/Catalan
(T=6 -> 34, Q(sqrt2), eps^4 = 17 + 12 sqrt2).  Core Lean 4 only.
-/
namespace FigureEightAnchors
namespace Ladder

open Lean.Grind

/-- Plain powers by repeated multiplication (no reliance on a Pow instance). -/
def pw {R : Type} [CommRing R] (x : R) : Nat → R
  | 0 => 1
  | n + 1 => pw x n * x

/-- The ladder over the integers. -/
def lad (T : Int) : Nat → Int
  | 0 => 2
  | 1 => T
  | n + 2 => T * lad T (n + 1) - lad T n

/-- The ladder in any commutative ring. -/
def ladR {R : Type} [CommRing R] (T : R) : Nat → R
  | 0 => 2
  | 1 => T
  | n + 2 => T * ladR T (n + 1) - ladR T n

/-- [rel: ladder-law] THE LADDER LAW: x + y = T and x y = 1 give x^k + y^k = t_k. -/
theorem ladder_law {R : Type} [CommRing R] (x y T : R) (hs : x + y = T) (hp : x * y = 1) :
    ∀ k, pw x k + pw y k = ladR T k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    match k with
    | 0 => simp only [pw, ladR]; grind
    | 1 => simp only [pw, ladR]; grind
    | n + 2 =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      simp only [pw, ladR] at *
      rw [← h1, ← h0, ← hs]
      have : pw x n * x * x * y + pw y n * y * y * x = pw x n * x + pw y n * y := by
        grind
      grind

/-- [rel: chiral-source/rule3, ladder T=1] Trefoil rung sequence is periodic of period 6. -/
theorem trefoil_ladder : (List.range 7).map (lad 1) = [2, 1, -1, -2, -1, 1, 2] := by decide

/-- [rel: ladder T=3, same-polynomial with Monodromy.h41_charpoly] figure-eight rungs. -/
theorem fig8_ladder : (List.range 7).map (lad 3) = [2, 3, 7, 18, 47, 123, 322] := by decide

/-- [rel: ladder T=6, external Apery/Catalan] Q(sqrt2) rungs: eps^2 has trace 6, eps^4 trace 34. -/
theorem sqrt2_ladder : (List.range 4).map (lad 6) = [2, 6, 34, 198] := by decide

/-- [rel: ruler/rule2, square-of] THE GOLDEN BRANCH SQUARED IS THE FIGURE-EIGHT MONODROMY:
    if z^2 - z - 1 = 0 then w = z^2 satisfies w^2 - 3w + 1 = 0. -/
theorem golden_squared {R : Type} [CommRing R] (z : R) (h : z * z - z - 1 = 0) :
    (z * z) * (z * z) - 3 * (z * z) + 1 = 0 := by grind

/-- [rel: square-of] The regular branch squared stays on the regular-type ladder:
    if z^2 - z + 1 = 0 then w = z^2 satisfies w^2 + w + 1 = 0 (cube roots of unity). -/
theorem regular_squared {R : Type} [CommRing R] (z : R) (h : z * z - z + 1 = 0) :
    (z * z) * (z * z) + (z * z) + 1 = 0 := by grind

/-- [rel: ladder T=3 step 5, external Q1] For a root x of x^2 - 3x + 1 (figure-eight
    monodromy eigenvalue phi^2), x^5 + (3-x)^5 = 123: the Q1 ratio phi^10 + phi^-10. -/
theorem fig8_fifth {R : Type} [CommRing R] (x : R) (h : x * x - 3 * x + 1 = 0) :
    pw x 5 + pw (3 - x) 5 = 123 := by
  simp only [pw]; grind

/-- [rel: external Apery/Catalan saddle] The saddle quadratic t^2 + 2t - 1 = 0
    (root sqrt2 - 1, shared by Beukers' Apery integrand and Problem 2.5's Lemma 17):
    its root and reciprocal t + 2 satisfy t^4 * (t+2)^4 = 1 and t^4 + (t+2)^4 = 34. -/
theorem saddle_unit {R : Type} [CommRing R] (t : R) (h : t * t + 2 * t - 1 = 0) :
    pw t 4 * pw (t + 2) 4 = 1 ∧ pw t 4 + pw (t + 2) 4 = 34 := by
  simp only [pw]; constructor <;> grind

/-- [rel: external Catalan, rest-mode] Problem 2.5's limiting polynomial contains Apery's:
    l^3 - 35 l^2 + 35 l - 1 = (l - 1)(l^2 - 34 l + 1). -/
theorem catalan_contains_apery {R : Type} [CommRing R] (l : R) :
    l * l * l - 35 * (l * l) + 35 * l - 1 = (l - 1) * (l * l - 34 * l + 1) := by grind

/-- [rel: rest-mode] Every odd anti-palindromic cubic l^3 - a l^2 + a l - 1 has the rest mode
    l = 1 FORCED, and the cofactor is self-reciprocal: (l-1)(l^2 - (a-1) l + 1). -/
theorem antipalindromic_rest {R : Type} [CommRing R] (a l : R) :
    l * l * l - a * (l * l) + a * l - 1 = (l - 1) * (l * l - (a - 1) * l + 1) := by grind

/-- [rel: external Apery] Apery's middle coefficient factors through sec psi = 17:
    34n^3 + 51n^2 + 27n + 5 = (2n + 1)(17n^2 + 17n + 5). -/
theorem apery_middle {R : Type} [CommRing R] (n : R) :
    34 * (n * n * n) + 51 * (n * n) + 27 * n + 5 = (2 * n + 1) * (17 * (n * n) + 17 * n + 5) := by
  grind

/-- [rel: ladder T=34, Pell] eps^4 = 17 + 12 sqrt2 is a unit: 17^2 - 2 * 12^2 = 1,
    and 2 * 17 = 34 = lad 6 2. -/
theorem pell_34 : (17 : Int) * 17 - 2 * (12 * 12) = 1 ∧ 2 * 17 = lad 6 2 := by decide

/-- [rel: band-edge] The band edge |T| = 2 is the exceptional point: x + y = 2, xy = 1
    forces x = y (the two rails merge) -- over the integers, x = y = 1. -/
theorem band_edge_merge (x y : Int) (hs : x + y = 2) (hp : x * y = 1) : x = 1 ∧ y = 1 := by
  have hy : y = 2 - x := by omega
  subst hy
  have : (x - 1) * (x - 1) = 0 := by grind
  have hx : x - 1 = 0 := by
    rcases Int.mul_eq_zero.mp this with h | h <;> exact h
  omega

end Ladder
end FigureEightAnchors
