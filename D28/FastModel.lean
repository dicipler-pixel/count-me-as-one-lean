import DiracTimeD25.BhlBoundaryTest

/-!
# D28: linear-time list models (proved equal to the `DiracTimeD25.BHL` models)

The `getD`-based models of `DiracTimeD25.BhlBoundaryTest` cost `O(L²)` kernel steps per shift
or addition. The models here (`take`/`zipWith`) cost `O(L)` and are proved equal to them, so the
higher-order checks of items 9(b), 10(b) can be run by the kernel within memory.
-/

namespace D28

open PowerSeries DiracTimeD25.BHL

def fShift (e : ℕ) (l : List ℤ) : List ℤ := (List.replicate e 0 ++ l).take l.length

def fAdd (l₁ l₂ : List ℤ) : List ℤ := List.zipWith (· + ·) l₁ (l₂ ++ List.replicate l₁.length 0)

theorem fShift_eq (e : ℕ) (l : List ℤ) : fShift e l = mShift e l := by
  apply List.ext_getElem
  · simp [fShift, mShift]
  intro k h1 h2
  simp only [fShift, mShift, List.getElem_take, List.getElem_map, List.getElem_range]
  rw [List.getElem_append]
  simp only [List.length_replicate]
  split_ifs with ha hb hb
  · omega
  · simp
  · rw [List.getD_eq_getElem _ _ (by simp [mShift] at h2; omega)]
  · omega

theorem fAdd_eq (l₁ l₂ : List ℤ) : fAdd l₁ l₂ = mAdd l₁ l₂ := by
  apply List.ext_getElem
  · simp [fAdd, mAdd]
  intro k h1 h2
  simp only [fAdd, mAdd, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  have hk : k < l₁.length := by simp [mAdd] at h2; exact h2
  rw [List.getD_eq_getElem _ _ hk, List.getElem_append]
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ h]
  · rw [List.getD_eq_default _ _ (by omega)]; simp

theorem mShift_getD (i : ℕ) (l : List ℤ) {k : ℕ} (hk : k < l.length) :
    (mShift i l).getD k 0 = if i ≤ k then l.getD (k - i) 0 else 0 := by
  simp [mShift, List.getD_eq_getElem?_getD, hk]

theorem mOnePlus_eq (i : ℕ) (l : List ℤ) : mOnePlus i l = mAdd l (mShift i l) := by
  apply List.ext_getElem
  · simp [mOnePlus, mAdd]
  intro k h1 h2
  have hk : k < l.length := by simp [mOnePlus] at h1; exact h1
  simp only [mOnePlus, mAdd, List.getElem_map, List.getElem_range]
  rw [mShift_getD _ _ hk]

def fOnePlus (i : ℕ) (l : List ℤ) : List ℤ := fAdd l (fShift i l)

theorem fOnePlus_eq (i : ℕ) (l : List ℤ) : fOnePlus i l = mOnePlus i l := by
  rw [fOnePlus, fShift_eq, fAdd_eq, mOnePlus_eq]

def fNegPoch (L : ℕ) : ℕ → List ℤ
  | 0 => mMono L 0 1
  | m + 1 => fOnePlus (m + 1) (fNegPoch L m)

theorem fNegPoch_eq (L m : ℕ) : fNegPoch L m = mNegPoch L m := by
  induction m with
  | zero => rfl
  | succ m ih => rw [fNegPoch, mNegPoch, ih, fOnePlus_eq]

def fSum (L : ℕ) (t : ℕ → List ℤ) : ℕ → List ℤ
  | 0 => mMono L 0 0
  | K + 1 => fAdd (fSum L t K) (t K)

theorem fSum_eq (L : ℕ) (t : ℕ → List ℤ) (K : ℕ) : fSum L t K = mSum L t K := by
  induction K with
  | zero => rfl
  | succ K ih => rw [fSum, mSum, ih, fAdd_eq]

def fPhiTerm (L n : ℕ) : List ℤ := fShift n (fNegPoch L (2 * n + 1))
def fMTerm (L n : ℕ) : List ℤ := fShift (2 * n) (fNegPoch L (2 * n + 1))
def fFtTerm (L n : ℕ) : List ℤ :=
  fShift (n * (3 * n + 1) / 2) (fAdd (mMono L 0 1) (mMono L (2 * n + 1) (-1)))

theorem rep_phi0_fast (L : ℕ) : rep L phi0 = fSum L (fPhiTerm L) L := by
  rw [rep_phi0, fSum_eq]; congr 1; funext n
  rw [fPhiTerm, mPhiTerm, fShift_eq, fNegPoch_eq]

theorem rep_bhlM_fast (L K : ℕ) (hK : L ≤ 2 * K) : rep L bhlM = fSum L (fMTerm L) K := by
  rw [rep_bhlM L K hK, fSum_eq]; congr 1; funext n
  rw [fMTerm, mMTerm, fShift_eq, fNegPoch_eq]

theorem rep_falseTheta_fast (L K : ℕ) (hK : L ≤ K * (3 * K + 1) / 2) :
    rep L falseTheta = fSum L (fFtTerm L) K := by
  rw [rep_falseTheta L K hK, fSum_eq]; congr 1; funext n
  rw [fFtTerm, mFtTerm, fShift_eq, fAdd_eq]

theorem rep_negInf_fast (L : ℕ) : rep L negInf = fNegPoch L L := by
  rw [rep_negInf, fNegPoch_eq]

end D28
