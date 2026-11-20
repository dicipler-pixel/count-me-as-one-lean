import D28.RawDiffPos  -- chained import (imports FastModel): serialises the memory-heavy kernel checks under `lake build`

/-!
# D28: quadratic-time model of `1 / (q; q²)_n` (proved equal to `rep L (qq2Inv n)`)

Multiplication by `1 / (1 − qᵃ)` is the recurrence `gₖ = fₖ + g_{k−a}`; `geomPre` builds the
first `n` entries of `g` by structural recursion. Used for item 10(a) through `k ≤ 128`.
-/

namespace D28

open PowerSeries DiracTimeD25.BHL

def geomPush (l : List ℤ) (a n : ℕ) (p : List ℤ) : List ℤ :=
  p ++ [l.getD n 0 + if a ≤ n then p.getD (n - a) 0 else 0]

def geomPre (a : ℕ) (l : List ℤ) : ℕ → List ℤ
  | 0 => []
  | n + 1 => geomPush l a n (geomPre a l n)

theorem length_geomPre (a : ℕ) (l : List ℤ) (n : ℕ) : (geomPre a l n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [geomPre, geomPush, ih]

theorem getD_geomPre_stable (a : ℕ) (l : List ℤ) {k n : ℕ} (h : k < n) :
    (geomPre a l n).getD k 0 = (geomPre a l (k + 1)).getD k 0 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · rw [geomPre, geomPush, List.getD_eq_getElem?_getD, List.getElem?_append_left
        (by rw [length_geomPre]; exact h'), ← List.getD_eq_getElem?_getD, ih h']
    · rfl

theorem getD_geomPre (a : ℕ) (ha : 0 < a) (l : List ℤ) {k n : ℕ} (h : k < n) :
    (geomPre a l n).getD k 0
      = l.getD k 0 + if a ≤ k then (geomPre a l n).getD (k - a) 0 else 0 := by
  rw [getD_geomPre_stable a l h, geomPre, geomPush, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [length_geomPre])]
  simp only [length_geomPre, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  split_ifs with hk
  · rw [getD_geomPre_stable a l (show k - a < k by omega),
      getD_geomPre_stable a l (show k - a < n by omega)]
  · rfl

theorem rep_geomInv_mul (L a : ℕ) (ha : 0 < a) (f : PowerSeries ℤ) :
    rep L (geomInv a * f) = geomPre a (rep L f) L := by
  have hG : geomInv a * f = f + X ^ a * (geomInv a * f) := by
    have h := one_sub_X_pow_mul_geomInv (a := a) ha
    linear_combination f * h
  symm
  refine (rep_ext (length_geomPre _ _ _) ?_).symm
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rw [getD_geomPre a ha _ hk, getD_rep_of_lt _ hk]
    conv_rhs => rw [hG]
    rw [map_add, coeff_X_pow_mul']
    split_ifs with h
    · rw [ih (k - a) (by omega) (by omega)]
    · rfl

def fQq2Inv (L : ℕ) : ℕ → List ℤ
  | 0 => mMono L 0 1
  | n + 1 => geomPre (2 * n + 1) (fQq2Inv L n) L

theorem rep_qq2Inv_fast (L n : ℕ) : rep L (qq2Inv n) = fQq2Inv L n := by
  induction n with
  | zero => simp [qq2Inv, fQq2Inv, rep_one]
  | succ n ih => rw [qq2Inv_succ, rep_geomInv_mul L _ (by omega), ih, fQq2Inv]

def fPsiTerm (L m : ℕ) : List ℤ := fShift ((m + 1) ^ 2) (fQq2Inv L (m + 1))

theorem rep_psi_fast (L K : ℕ) (hK : L ≤ (K + 1) ^ 2) : rep L psi = fSum L (fPsiTerm L) K := by
  rw [rep_psi L K hK, fSum_eq]; congr 1; funext m
  rw [fPsiTerm, mPsiTerm, fShift_eq, ← rep_qq2Inv_fast, rep_qq2Inv]

theorem fSum_congr (L : ℕ) (t t' : ℕ → List ℤ) (K : ℕ) (h : ∀ m < K, t m = t' m) :
    fSum L t K = fSum L t' K := by
  induction K with
  | zero => rfl
  | succ K ih => rw [fSum, fSum, ih (fun m hm => h m (by omega)), h K (by omega)]

end D28
