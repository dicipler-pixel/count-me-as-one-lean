module

public import Mathlib

/-!
# D27 — Bringmann–Hikami–Lovejoy (2010) signed-boundary q-series benchmark
-/

@[expose] public section

namespace DiracTimeD25.BHL

open PowerSeries

/-! ## Truncated list model -/

/-- The first `L` coefficients of `f`. -/
noncomputable def rep (L : ℕ) (f : PowerSeries ℤ) : List ℤ :=
  (List.range L).map fun k => coeff k f

theorem length_rep (L : ℕ) (f : PowerSeries ℤ) : (rep L f).length = L := by simp [rep]

theorem getD_rep (L : ℕ) (f : PowerSeries ℤ) (k : ℕ) :
    (rep L f).getD k 0 = if k < L then coeff k f else 0 := by
  split_ifs with h
  · simp [rep, List.getD_eq_getElem?_getD, h]
  · simp [rep, List.getD_eq_getElem?_getD, not_lt.1 h]

theorem getD_rep_of_lt {L k : ℕ} (f : PowerSeries ℤ) (h : k < L) :
    (rep L f).getD k 0 = coeff k f := by
  rw [getD_rep]; simp [h]

@[simp] theorem getElem_rep {L k : ℕ} (f : PowerSeries ℤ) (h : k < (rep L f).length) :
    (rep L f)[k] = coeff k f := by
  simp [rep]

theorem listSum_map_range {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → M) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih,
      Finset.sum_range_succ]; simp

theorem rep_ext {L : ℕ} {f : PowerSeries ℤ} {l : List ℤ} (hl : l.length = L)
    (h : ∀ k < L, l.getD k 0 = coeff k f) : rep L f = l := by
  apply List.ext_getElem (by rw [length_rep, hl])
  intro k h1 h2
  rw [length_rep] at h1
  have := h k h1
  rw [List.getD_eq_getElem _ _ h2] at this
  simp [rep, this]

/-- Model of multiplication by `1 + X^i`. -/
def mOnePlus (i : ℕ) (l : List ℤ) : List ℤ :=
  (List.range l.length).map fun k => l.getD k 0 + if i ≤ k then l.getD (k - i) 0 else 0

/-- Model of multiplication by `X^e`. -/
def mShift (e : ℕ) (l : List ℤ) : List ℤ :=
  (List.range l.length).map fun k => if e ≤ k then l.getD (k - e) 0 else 0

/-- Model of the Cauchy product, truncated to the length of the first list. -/
def mMul (l₁ l₂ : List ℤ) : List ℤ :=
  (List.range l₁.length).map fun k =>
    ((List.range (k + 1)).map fun i => l₁.getD i 0 * l₂.getD (k - i) 0).sum

/-- Model of addition. -/
def mAdd (l₁ l₂ : List ℤ) : List ℤ :=
  (List.range l₁.length).map fun k => l₁.getD k 0 + l₂.getD k 0

/-- Model of the monomial `c X^e`. -/
def mMono (L e : ℕ) (c : ℤ) : List ℤ := (List.range L).map fun k => if k = e then c else 0

theorem rep_add (L : ℕ) (f g : PowerSeries ℤ) : rep L (f + g) = mAdd (rep L f) (rep L g) := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mAdd, length_rep]
  simp [mAdd, length_rep, hk, List.getD_eq_getElem?_getD]

theorem rep_X_pow_mul (L e : ℕ) (f : PowerSeries ℤ) :
    rep L (X ^ e * f) = mShift e (rep L f) := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mShift, length_rep]
  simp only [mShift, length_rep, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some, coeff_X_pow_mul']
  split_ifs with h
  · rw [← List.getD_eq_getElem?_getD, getD_rep_of_lt _ (by omega)]
  · rfl

theorem rep_one_add_X_pow_mul (L i : ℕ) (f : PowerSeries ℤ) :
    rep L ((1 + X ^ i) * f) = mOnePlus i (rep L f) := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mOnePlus, length_rep]
  simp only [mOnePlus, length_rep, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some, add_mul, one_mul, map_add,
    coeff_X_pow_mul']
  rw [← List.getD_eq_getElem?_getD, getD_rep_of_lt _ hk]
  split_ifs with h
  · rw [← List.getD_eq_getElem?_getD, getD_rep_of_lt _ (by omega)]
  · rfl

theorem rep_mul (L : ℕ) (f g : PowerSeries ℤ) : rep L (f * g) = mMul (rep L f) (rep L g) := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mMul, length_rep]
  simp only [mMul, length_rep, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hk, Option.map_some, Option.getD_some, coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, listSum_map_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, getD_rep_of_lt _ (by omega),
    getD_rep_of_lt _ (by omega)]

theorem rep_monomial (L e : ℕ) (c : ℤ) : rep L (C c * X ^ e) = mMono L e c := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mMono]
  simp [mMono, List.getD_eq_getElem?_getD, hk, coeff_X_pow]

theorem rep_congr {L : ℕ} {f g : PowerSeries ℤ} (h : ∀ k < L, coeff k f = coeff k g) :
    rep L f = rep L g := by
  unfold rep
  exact List.map_congr_left fun k hk => h k (List.mem_range.1 hk)

theorem coeff_eq_of_rep_eq {L : ℕ} {f g : PowerSeries ℤ} (h : rep L f = rep L g) :
    ∀ k < L, coeff k f = coeff k g := by
  intro k hk
  rw [← getD_rep_of_lt f hk, ← getD_rep_of_lt g hk, h]

theorem rep_one (L : ℕ) : rep L 1 = mMono L 0 1 := by
  rw [← rep_monomial]; simp

theorem rep_zero (L : ℕ) : rep L 0 = mMono L 0 0 := by
  rw [← rep_monomial]; simp

theorem rep_two (L : ℕ) : rep L 2 = mMono L 0 2 := by
  rw [← rep_monomial]; simp [map_ofNat]

/-- Model of subtraction. -/
def mSub (l₁ l₂ : List ℤ) : List ℤ :=
  (List.range l₁.length).map fun k => l₁.getD k 0 - l₂.getD k 0

theorem rep_sub (L : ℕ) (f g : PowerSeries ℤ) : rep L (f - g) = mSub (rep L f) (rep L g) := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mSub, length_rep]
  simp [mSub, length_rep, hk, List.getD_eq_getElem?_getD]

/-- Model of `f(q) ↦ f(−q)`. -/
def mNeg (l : List ℤ) : List ℤ := (List.range l.length).map fun k => (-1) ^ k * l.getD k 0

theorem rep_rescale_neg_one (L : ℕ) (f : PowerSeries ℤ) :
    rep L (rescale (-1) f) = mNeg (rep L f) := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mNeg, length_rep]
  simp [mNeg, length_rep, hk, List.getD_eq_getElem?_getD]

/-- Model of `f(q) ↦ f(q²)`, truncated to length `L`. -/
def mExpand2 (L : ℕ) (l : List ℤ) : List ℤ :=
  (List.range L).map fun k => if k % 2 = 0 then l.getD (k / 2) 0 else 0

theorem rep_expand_two (L L' : ℕ) (hL : L ≤ 2 * L') (f : PowerSeries ℤ) :
    rep L (expand 2 two_ne_zero f) = mExpand2 L (rep L' f) := by
  refine rep_ext ?_ (fun k hk => ?_)
  · simp [mExpand2]
  simp only [mExpand2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk,
    Option.map_some, Option.getD_some, coeff_expand, Nat.dvd_iff_mod_eq_zero]
  split_ifs
  · rw [← List.getD_eq_getElem?_getD, getD_rep_of_lt _ (by omega)]
  · rfl

/-- Model of a finite sum of modelled terms. -/
def mSum (L : ℕ) (t : ℕ → List ℤ) : ℕ → List ℤ
  | 0 => mMono L 0 0
  | K + 1 => mAdd (mSum L t K) (t K)

theorem rep_sum (L : ℕ) (f : ℕ → PowerSeries ℤ) (t : ℕ → List ℤ) (h : ∀ n, rep L (f n) = t n)
    (K : ℕ) : rep L (∑ n ∈ Finset.range K, f n) = mSum L t K := by
  induction K with
  | zero => simp [mSum, rep_zero]
  | succ K ih => rw [Finset.sum_range_succ, rep_add, ih, h, mSum]

/-! ## Series given by a sum of terms of increasing order -/

/-- `∑ₙ t n`, defined coefficientwise; `hasSum_seriesOf` shows it is the `X`-adic sum. -/
noncomputable def seriesOf (t : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  mk fun d => ∑ n ∈ Finset.range (d + 1), coeff d (t n)

/-- Term `n` has no coefficient below degree `n`. -/
def LowerOrd (t : ℕ → PowerSeries ℤ) : Prop := ∀ n d, d < n → coeff d (t n) = 0

open scoped PowerSeries.WithPiTopology in
/-- The coefficientwise definition is the genuine infinite sum (product topology on `ℤ⟦X⟧`). -/
theorem hasSum_seriesOf {t : ℕ → PowerSeries ℤ} (ht : LowerOrd t) : HasSum t (seriesOf t) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro d
  rw [seriesOf, coeff_mk]
  exact hasSum_sum_of_ne_finset_zero fun n hn => ht n d (by simpa using hn)

/-- Coefficients of `seriesOf t` below degree `L` are those of the partial sum over `n < K`,
provided all terms `n ≥ K` vanish below degree `L`. -/
theorem coeff_seriesOf_eq_partial {t : ℕ → PowerSeries ℤ} (ht : LowerOrd t) {L K : ℕ}
    (hK : ∀ n, K ≤ n → ∀ d < L, coeff d (t n) = 0) :
    ∀ d < L, coeff d (seriesOf t) = coeff d (∑ n ∈ Finset.range K, t n) := by
  intro d hd
  rw [seriesOf, coeff_mk, map_sum]
  have h1 : ∑ n ∈ Finset.range (d + 1), coeff d (t n)
      = ∑ n ∈ Finset.range (max (d + 1) K), coeff d (t n) :=
    Finset.sum_subset (Finset.range_subset_range.2 (le_max_left _ _)) fun n _ hn =>
      ht n d (by simp at hn; omega)
  have h2 : ∑ n ∈ Finset.range K, coeff d (t n)
      = ∑ n ∈ Finset.range (max (d + 1) K), coeff d (t n) :=
    Finset.sum_subset (Finset.range_subset_range.2 (le_max_right _ _)) fun n _ hn =>
      hK n (by simp at hn; omega) d hd
  rw [h1, h2]

theorem rep_seriesOf {t : ℕ → PowerSeries ℤ} (ht : LowerOrd t) {L K : ℕ}
    (hK : ∀ n, K ≤ n → ∀ d < L, coeff d (t n) = 0) :
    rep L (seriesOf t) = rep L (∑ n ∈ Finset.range K, t n) :=
  rep_congr (coeff_seriesOf_eq_partial ht hK)

theorem coeff_X_pow_mul_of_lt {e d : ℕ} (g : PowerSeries ℤ) (h : d < e) :
    coeff d (X ^ e * g) = 0 := by
  rw [coeff_X_pow_mul', ite_eq_right (by omega)]

/-! ## The q-series of BHL (2010), Eqs. (1.3), (1.4), (1.6), (1.7) -/

/-- `(−q)_m = (1 + q)(1 + q²)⋯(1 + qᵐ)`. -/
noncomputable def negPoch (m : ℕ) : PowerSeries ℤ := ∏ i ∈ Finset.range m, (1 + X ^ (i + 1))

theorem negPoch_succ (m : ℕ) : negPoch (m + 1) = (1 + X ^ (m + 1)) * negPoch m := by
  rw [negPoch, Finset.prod_range_succ, mul_comm]; rfl

/-- Term `qⁿ (−q)_{2n+1}` of `φ₀` (Eq. 1.3). -/
noncomputable def phiTerm (n : ℕ) : PowerSeries ℤ := X ^ n * negPoch (2 * n + 1)

/-- Term `q²ⁿ (−q)_{2n+1}` of `M` (Eq. 1.6). -/
noncomputable def MTerm (n : ℕ) : PowerSeries ℤ := X ^ (2 * n) * negPoch (2 * n + 1)

/-- `1 / (1 − qᵃ) = ∑ₘ q^{am}`. -/
noncomputable def geomInv (a : ℕ) : PowerSeries ℤ := mk fun m => if a ∣ m then 1 else 0

theorem one_sub_X_pow_mul_geomInv {a : ℕ} (ha : 0 < a) : (1 - X ^ a) * geomInv a = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', geomInv, coeff_mk, coeff_mk, coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [show ¬ a ≤ 0 by omega]
  · rw [ite_eq_right hm.ne']
    by_cases h : a ≤ m
    · rw [ite_eq_left h]
      have : a ∣ m - a ↔ a ∣ m := by
        conv_rhs => rw [show m = (m - a) + a by omega]
        exact (Nat.dvd_add_self_right).symm
      by_cases hd : a ∣ m <;> simp [hd, this]
    · rw [ite_eq_right h, ite_eq_right (fun hd => h (Nat.le_of_dvd hm hd))]; simp

/-- `(q; q²)_n = (1 − q)(1 − q³)⋯(1 − q^{2n−1})`. -/
noncomputable def qq2 (n : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.range n, (1 - X ^ (2 * j + 1))

/-- `1 / (q; q²)_n`. -/
noncomputable def qq2Inv (n : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.range n, geomInv (2 * j + 1)

theorem qq2_mul_qq2Inv (n : ℕ) : qq2 n * qq2Inv n = 1 := by
  rw [qq2, qq2Inv, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun j _ => one_sub_X_pow_mul_geomInv (by omega)

theorem qq2Inv_succ (n : ℕ) : qq2Inv (n + 1) = geomInv (2 * n + 1) * qq2Inv n := by
  rw [qq2Inv, Finset.prod_range_succ, mul_comm]; rfl

/-- Term `q^{n²} / (q; q²)_n` of `ψ` for `n = m + 1 ≥ 1` (Eq. 1.4). -/
noncomputable def psiTerm (m : ℕ) : PowerSeries ℤ := X ^ ((m + 1) ^ 2) * qq2Inv (m + 1)

/-- Term `q^{n(3n+1)/2} (1 − q^{2n+1})` of the false theta sum in Eq. (1.7). -/
noncomputable def ftTerm (n : ℕ) : PowerSeries ℤ :=
  X ^ (n * (3 * n + 1) / 2) * (1 - X ^ (2 * n + 1))

/-- Eq. (1.3): `φ₀(q) = ∑_{n ≥ 0} qⁿ (−q)_{2n+1}`. -/
noncomputable def phi0 : PowerSeries ℤ := seriesOf phiTerm

/-- Eq. (1.6): `M(q) = ∑_{n ≥ 0} q²ⁿ (−q)_{2n+1}`. -/
noncomputable def bhlM : PowerSeries ℤ := seriesOf MTerm

/-- Eq. (1.4): `ψ(q) = ∑_{n ≥ 1} q^{n²} / (q; q²)_n` (Ramanujan's third-order mock theta). -/
noncomputable def psi : PowerSeries ℤ := seriesOf psiTerm

/-- The false theta sum `∑_{n ≥ 0} q^{n(3n+1)/2} (1 − q^{2n+1})` of Eq. (1.7). -/
noncomputable def falseTheta : PowerSeries ℤ := seriesOf ftTerm

theorem phiTerm_lowerOrd : LowerOrd phiTerm := fun _ _ h => coeff_X_pow_mul_of_lt _ h
theorem MTerm_lowerOrd : LowerOrd MTerm := fun n d h => coeff_X_pow_mul_of_lt _ (by omega)
theorem psiTerm_lowerOrd : LowerOrd psiTerm := fun n d h =>
  coeff_X_pow_mul_of_lt _ (by nlinarith)
theorem ftTerm_lowerOrd : LowerOrd ftTerm := fun n d h =>
  coeff_X_pow_mul_of_lt _ (by
    have : 2 * n ≤ n * (3 * n + 1) := by nlinarith
    omega)

open scoped PowerSeries.WithPiTopology in
/-- `φ₀` is the `X`-adic sum of its defining terms. -/
theorem hasSum_phi0 : HasSum phiTerm phi0 := hasSum_seriesOf phiTerm_lowerOrd
open scoped PowerSeries.WithPiTopology in
theorem hasSum_bhlM : HasSum MTerm bhlM := hasSum_seriesOf MTerm_lowerOrd
open scoped PowerSeries.WithPiTopology in
theorem hasSum_psi : HasSum psiTerm psi := hasSum_seriesOf psiTerm_lowerOrd
open scoped PowerSeries.WithPiTopology in
theorem hasSum_falseTheta : HasSum ftTerm falseTheta := hasSum_seriesOf ftTerm_lowerOrd

/-! ### `(−q)_∞` -/

theorem coeff_mul_of_coeff_eq_one {d : ℕ} (f g : PowerSeries ℤ)
    (hg : ∀ j ≤ d, coeff j g = coeff j (1 : PowerSeries ℤ)) :
    ∀ k ≤ d, coeff k (f * g) = coeff k f := by
  intro k hk
  rw [coeff_mul, Finset.sum_eq_single (k, 0)]
  · rw [hg 0 (by omega)]; simp
  · rintro ⟨i, j⟩ hij hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    have hj : j ≠ 0 := by rintro rfl; apply hne; simp at hij ⊢; omega
    rw [hg j (by omega), coeff_one, ite_eq_right hj, mul_zero]
  · intro h; exact absurd (by simp) h

theorem coeff_prod_tail {d : ℕ} (s : Finset ℕ) (hs : ∀ i ∈ s, d ≤ i) :
    ∀ k ≤ d, coeff k (∏ i ∈ s, (1 + X ^ (i + 1) : PowerSeries ℤ)) = coeff k 1 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    intro k hk
    rw [Finset.prod_insert ha, mul_comm,
      coeff_mul_of_coeff_eq_one _ _ (fun j hj => ?_) k hk, ih (fun i hi => hs i (by simp [hi])) k hk]
    have := hs a (by simp)
    rw [map_add, coeff_X_pow, ite_eq_right (by omega), add_zero]

/-- `(−q)_∞ = ∏_{i ≥ 1} (1 + qⁱ)`, defined coefficientwise; `hasProd_negInf` shows it is the
`X`-adic infinite product. -/
noncomputable def negInf : PowerSeries ℤ := mk fun d => coeff d (negPoch d)

theorem coeff_negPoch_stable {d N : ℕ} (h : d ≤ N) : coeff d (negPoch N) = coeff d (negPoch d) := by
  rw [negPoch, ← Finset.prod_range_mul_prod_Ico _ h,
    coeff_mul_of_coeff_eq_one _ _ (coeff_prod_tail _ fun i hi => (Finset.mem_Ico.1 hi).1) d le_rfl]
  rfl

theorem coeff_negInf {d N : ℕ} (h : d ≤ N) : coeff d negInf = coeff d (negPoch N) := by
  rw [negInf, coeff_mk, coeff_negPoch_stable h]

open scoped PowerSeries.WithPiTopology in
/-- `(−q)_∞` is the `X`-adic infinite product `∏_{i ≥ 0} (1 + q^{i+1})`. -/
theorem hasProd_negInf : HasProd (fun i => (1 + X ^ (i + 1) : PowerSeries ℤ)) negInf := by
  unfold HasProd
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro d
  refine tendsto_const_nhds.congr' ?_
  rw [Filter.EventuallyEq, SummationFilter.unconditional_filter, Filter.eventually_atTop]
  refine ⟨Finset.range d, fun s hs => ?_⟩
  rw [negInf, coeff_mk, ← Finset.prod_sdiff hs, mul_comm,
    coeff_mul_of_coeff_eq_one _ _ (coeff_prod_tail _ fun i hi => ?_) d le_rfl]
  · rfl
  · simpa using (Finset.mem_sdiff.1 hi).2

/-! ## Computable models of the terms -/

/-- Model of `(−q)_m`. -/
def mNegPoch (L : ℕ) : ℕ → List ℤ
  | 0 => mMono L 0 1
  | m + 1 => mOnePlus (m + 1) (mNegPoch L m)

theorem rep_negPoch (L m : ℕ) : rep L (negPoch m) = mNegPoch L m := by
  induction m with
  | zero => simp [negPoch, mNegPoch, rep_one]
  | succ m ih => rw [negPoch_succ, rep_one_add_X_pow_mul, ih, mNegPoch]

/-- Model of `1 / (1 − qᵃ)`. -/
def mGeom (L a : ℕ) : List ℤ := (List.range L).map fun k => if k % a = 0 then 1 else 0

theorem rep_geomInv (L a : ℕ) : rep L (geomInv a) = mGeom L a := by
  unfold rep mGeom geomInv
  refine List.map_congr_left fun k _ => ?_
  rw [coeff_mk]
  by_cases h : a ∣ k
  · rw [ite_eq_left h, ite_eq_left (Nat.dvd_iff_mod_eq_zero.1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (Nat.dvd_iff_mod_eq_zero.2 h'))]

/-- Model of `1 / (q; q²)_n`. -/
def mQq2Inv (L : ℕ) : ℕ → List ℤ
  | 0 => mMono L 0 1
  | n + 1 => mMul (mGeom L (2 * n + 1)) (mQq2Inv L n)

theorem rep_qq2Inv (L n : ℕ) : rep L (qq2Inv n) = mQq2Inv L n := by
  induction n with
  | zero => simp [qq2Inv, mQq2Inv, rep_one]
  | succ n ih => rw [qq2Inv_succ, rep_mul, rep_geomInv, ih, mQq2Inv]

def mPhiTerm (L n : ℕ) : List ℤ := mShift n (mNegPoch L (2 * n + 1))
def mMTerm (L n : ℕ) : List ℤ := mShift (2 * n) (mNegPoch L (2 * n + 1))
def mPsiTerm (L m : ℕ) : List ℤ := mShift ((m + 1) ^ 2) (mQq2Inv L (m + 1))
def mFtTerm (L n : ℕ) : List ℤ :=
  mShift (n * (3 * n + 1) / 2) (mAdd (mMono L 0 1) (mMono L (2 * n + 1) (-1)))

theorem rep_phiTerm (L n : ℕ) : rep L (phiTerm n) = mPhiTerm L n := by
  rw [phiTerm, rep_X_pow_mul, rep_negPoch]; rfl
theorem rep_MTerm (L n : ℕ) : rep L (MTerm n) = mMTerm L n := by
  rw [MTerm, rep_X_pow_mul, rep_negPoch]; rfl
theorem rep_psiTerm (L m : ℕ) : rep L (psiTerm m) = mPsiTerm L m := by
  rw [psiTerm, rep_X_pow_mul, rep_qq2Inv]; rfl
theorem rep_ftTerm (L n : ℕ) : rep L (ftTerm n) = mFtTerm L n := by
  have : (1 - X ^ (2 * n + 1) : PowerSeries ℤ) = C 1 * X ^ 0 + C (-1) * X ^ (2 * n + 1) := by
    simp [sub_eq_add_neg]
  rw [ftTerm, rep_X_pow_mul, this, rep_add, rep_monomial, rep_monomial]; rfl

/-- Truncation is airtight: below degree `L`, a `seriesOf` with terms of order `≥ e n`
equals the finite model sum over `n < K` once `e n ≥ L` for all `n ≥ K`. -/
theorem rep_seriesOf_model {t : ℕ → PowerSeries ℤ} (ht : LowerOrd t) (e : ℕ → ℕ)
    (he : ∀ n d, d < e n → coeff d (t n) = 0) {L K : ℕ} (hK : ∀ n, K ≤ n → L ≤ e n)
    (mt : ℕ → List ℤ) (hm : ∀ n, rep L (t n) = mt n) :
    rep L (seriesOf t) = mSum L mt K := by
  rw [rep_seriesOf ht (K := K) (fun n hn d hd => he n d (by have := hK n hn; omega)),
    rep_sum L t mt hm]

theorem rep_phi0 (L : ℕ) : rep L phi0 = mSum L (mPhiTerm L) L :=
  rep_seriesOf_model phiTerm_lowerOrd id (fun _ _ h => coeff_X_pow_mul_of_lt _ h)
    (fun _ h => h) _ (rep_phiTerm L)

theorem rep_bhlM (L K : ℕ) (hK : L ≤ 2 * K) : rep L bhlM = mSum L (mMTerm L) K :=
  rep_seriesOf_model MTerm_lowerOrd (fun n => 2 * n) (fun _ _ h => coeff_X_pow_mul_of_lt _ h)
    (fun n h => by omega) _ (rep_MTerm L)

theorem rep_psi (L K : ℕ) (hK : L ≤ (K + 1) ^ 2) : rep L psi = mSum L (mPsiTerm L) K :=
  rep_seriesOf_model psiTerm_lowerOrd (fun m => (m + 1) ^ 2)
    (fun _ _ h => coeff_X_pow_mul_of_lt _ h)
    (fun n h => le_trans hK (Nat.pow_le_pow_left (by omega) 2)) _ (rep_psiTerm L)

theorem rep_falseTheta (L K : ℕ) (hK : L ≤ K * (3 * K + 1) / 2) :
    rep L falseTheta = mSum L (mFtTerm L) K :=
  rep_seriesOf_model ftTerm_lowerOrd (fun n => n * (3 * n + 1) / 2)
    (fun _ _ h => coeff_X_pow_mul_of_lt _ h)
    (fun n h => le_trans hK (Nat.div_le_div_right (Nat.mul_le_mul h (by omega)))) _
    (rep_ftTerm L)

theorem rep_negInf (L : ℕ) : rep L negInf = mNegPoch L L := by
  rw [← rep_negPoch]
  exact rep_congr fun k hk => coeff_negInf hk.le

/-! ## All-degree structural facts -/

theorem coeff_two_mul (g : PowerSeries ℤ) (n : ℕ) : coeff n ((2 : PowerSeries ℤ) * g) = 2 * coeff n g := by
  rw [show (2 : PowerSeries ℤ) = C 2 from (map_ofNat C 2).symm, coeff_C_mul]

/-- `coeffₖ(f(q) + f(−q)) = (1 + (−1)ᵏ) coeffₖ f`, all `k`. -/
theorem coeff_add_rescale_neg (f : PowerSeries ℤ) (k : ℕ) :
    coeff k (f + rescale (-1) f) = (1 + (-1) ^ k) * coeff k f := by
  rw [map_add, coeff_rescale]; ring

/-- Odd coefficients of `f(q) + f(−q)` vanish, all degrees. -/
theorem coeff_odd_add_rescale_neg (f : PowerSeries ℤ) (k : ℕ) :
    coeff (2 * k + 1) (f + rescale (-1) f) = 0 := by
  rw [coeff_add_rescale_neg, pow_succ, pow_mul]; norm_num

/-- Even coefficients of `f(q) + f(−q)` double, all degrees. -/
theorem coeff_even_add_rescale_neg (f : PowerSeries ℤ) (k : ℕ) :
    coeff (2 * k) (f + rescale (-1) f) = 2 * coeff (2 * k) f := by
  rw [coeff_add_rescale_neg, pow_mul]; norm_num

/-- `coeff_{2k+2}(2q² f(q²)) = 2 coeffₖ f`, all `k`. -/
theorem coeff_lhs15_even (f : PowerSeries ℤ) (k : ℕ) :
    coeff (2 * k + 2) ((2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero f) = 2 * coeff k f := by
  rw [mul_assoc, coeff_two_mul, coeff_X_pow_mul', ite_eq_left (by omega), coeff_expand,
    ite_eq_left (by omega), show (2 * k + 2 - 2) / 2 = k by omega]

/-- `coeff_{2k+1}(2q² f(q²)) = 0`, all `k`. -/
theorem coeff_lhs15_odd (f : PowerSeries ℤ) (k : ℕ) :
    coeff (2 * k + 1) ((2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero f) = 0 := by
  rw [mul_assoc, coeff_two_mul, coeff_X_pow_mul']
  split_ifs with h
  · rw [coeff_expand, ite_eq_right (by omega), mul_zero]
  · rfl

theorem coeff_lhs15_zero (f : PowerSeries ℤ) :
    coeff 0 ((2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero f) = 0 := by
  rw [mul_assoc, coeff_two_mul, coeff_X_pow_mul', ite_eq_right (by omega), mul_zero]

/-- Parity reduction, all degrees: for any `f, g` with `g₀ = 0`,
`2q² f(q²) = g(q) + g(−q) ↔ ∀ k, fₖ = g_{2k+2}`. -/
theorem lhs15_eq_iff (f g : PowerSeries ℤ) (hg : coeff 0 g = 0) :
    (2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero f = g + rescale (-1) g ↔
      ∀ k, coeff k f = coeff (2 * k + 2) g := by
  constructor
  · intro h k
    have := congrArg (coeff (2 * k + 2)) h
    rw [coeff_lhs15_even, show 2 * k + 2 = 2 * (k + 1) by ring, coeff_even_add_rescale_neg] at this
    rw [show 2 * k + 2 = 2 * (k + 1) by ring]
    omega
  · intro h
    ext n
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
    · rcases j with _ | k
      · rw [coeff_lhs15_zero, show 2 * 0 = 0 by rfl, coeff_add_rescale_neg, hg, mul_zero]
      · rw [show 2 * (k + 1) = 2 * k + 2 by ring, coeff_lhs15_even, h k,
          show 2 * k + 2 = 2 * (k + 1) by ring, coeff_even_add_rescale_neg]
    · rw [coeff_lhs15_odd, coeff_odd_add_rescale_neg]

theorem coeff_zero_psi : coeff 0 psi = 0 := by
  rw [psi, seriesOf, coeff_mk, Finset.sum_range_one, psiTerm, coeff_X_pow_mul_of_lt _ (by norm_num)]

/-- **Eq. (1.5) ⇔ parity reduction** (all degrees): `2q²φ₀(q²) = ψ(q) + ψ(−q)` holds iff
`coeffₖ φ₀ = coeff_{2k+2} ψ` for every `k`. -/
theorem eq15_iff_coeff :
    (2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero phi0 = psi + rescale (-1) psi ↔
      ∀ k, coeff k phi0 = coeff (2 * k + 2) psi :=
  lhs15_eq_iff phi0 psi coeff_zero_psi

/-! ## Eq. (1.5) and Eq. (1.7), exact through `q⁴⁸` -/

theorem rep_lhs15 (L L' : ℕ) (hL : L ≤ 2 * L') :
    rep L ((2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero phi0)
      = mMul (mMono L 0 2) (mShift 2 (mExpand2 L (mSum L' (mPhiTerm L') L'))) := by
  rw [mul_assoc, rep_mul, rep_two, rep_X_pow_mul, rep_expand_two L L' hL, rep_phi0]

/-- **Eq. (1.5) modulo `q⁴⁹`**: `2q²φ₀(q²) ≡ ψ(q) + ψ(−q)`, i.e. every coefficient of degree
`≤ 48` agrees. -/
theorem eq15_mod_q49 : ∀ d < 49,
    coeff d ((2 : PowerSeries ℤ) * X ^ 2 * expand 2 two_ne_zero phi0)
      = coeff d (psi + rescale (-1) psi) := by
  apply coeff_eq_of_rep_eq
  rw [rep_lhs15 49 25 (by norm_num), rep_add, rep_rescale_neg_one, rep_psi 49 6 (by norm_num)]
  decide +kernel

/-- Eq. (1.5) in reduced form: `coeffₖ φ₀ = coeff_{2k+2} ψ` for `k ≤ 23`. -/
theorem eq15_reduced_le23 : ∀ k ≤ 23, coeff k phi0 = coeff (2 * k + 2) psi := by
  intro k hk
  have h := eq15_mod_q49 (2 * k + 2) (by omega)
  rw [coeff_lhs15_even, show 2 * k + 2 = 2 * (k + 1) by ring, coeff_even_add_rescale_neg] at h
  rw [show 2 * k + 2 = 2 * (k + 1) by ring]
  omega

/-- **Eq. (1.7) modulo `q⁴⁹`**: `2 + 2q²M(q) ≡ (−q)_∞ + ∑_{n≥0} q^{n(3n+1)/2}(1 − q^{2n+1})`. -/
theorem eq17_mod_q49 : ∀ d < 49,
    coeff d ((2 : PowerSeries ℤ) + 2 * X ^ 2 * bhlM) = coeff d (negInf + falseTheta) := by
  apply coeff_eq_of_rep_eq
  rw [rep_add, mul_assoc, rep_mul, rep_two, rep_X_pow_mul, rep_bhlM 49 25 (by norm_num), rep_add,
    rep_negInf, rep_falseTheta 49 6 (by norm_num)]
  decide +kernel

/-! ## Exact coefficient tables (degrees 0..16) and separation at `q¹` -/

theorem rep17_phi0 : rep 17 phi0 =
    [1, 2, 2, 3, 5, 6, 8, 11, 13, 17, 22, 27, 34, 42, 51, 62, 76] := by
  rw [rep_phi0]; decide +kernel

theorem rep17_bhlM : rep 17 bhlM =
    [1, 1, 1, 1, 2, 3, 3, 4, 5, 6, 7, 9, 11, 14, 16, 19, 23] := by
  rw [rep_bhlM 17 9 (by norm_num)]; decide +kernel

/-- The raw difference `φ₀(q) − M(q)` through `q¹⁶`. -/
theorem rep17_phi0_sub_bhlM : rep 17 (phi0 - bhlM) =
    [0, 1, 1, 2, 3, 3, 5, 7, 8, 11, 15, 18, 23, 28, 35, 43, 53] := by
  rw [rep_sub, rep17_phi0, rep17_bhlM]; decide +kernel

theorem rep17_psi : rep 17 psi =
    [0, 1, 1, 1, 2, 2, 2, 3, 3, 4, 5, 5, 6, 7, 8, 9, 11] := by
  rw [rep_psi 17 4 (by norm_num)]; decide +kernel

theorem rep17_negInf : rep 17 negInf =
    [1, 1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 15, 18, 22, 27, 32] := by
  rw [rep_negInf]; decide +kernel

theorem rep17_falseTheta : rep 17 falseTheta =
    [1, -1, 1, 0, 0, -1, 0, 1, 0, 0, 0, 0, -1, 0, 0, 1, 0] := by
  rw [rep_falseTheta 17 4 (by norm_num)]; decide +kernel

theorem coeff_one_phi0 : coeff 1 phi0 = 2 := by
  rw [← getD_rep_of_lt phi0 (show 1 < 17 by norm_num), rep17_phi0]; rfl

theorem coeff_one_bhlM : coeff 1 bhlM = 1 := by
  rw [← getD_rep_of_lt bhlM (show 1 < 17 by norm_num), rep17_bhlM]; rfl

/-- **Strict separation at `q¹`**: `coeff₁ φ₀ = 2 ≠ 1 = coeff₁ M`, so `φ₀ ≠ M`. -/
theorem phi0_ne_bhlM : coeff 1 phi0 ≠ coeff 1 bhlM ∧ phi0 ≠ bhlM := by
  refine ⟨by rw [coeff_one_phi0, coeff_one_bhlM]; decide, fun h => ?_⟩
  have := congrArg (coeff 1) h
  rw [coeff_one_phi0, coeff_one_bhlM] at this
  exact absurd this (by decide)

end DiracTimeD25.BHL

end
