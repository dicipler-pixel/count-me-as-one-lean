import DiracTimeD25.AlexanderWall
import DiracTimeD25.ChiralEta

/-!
# D28 algebraic items (new_lean_statements_v1, items 1, 3, 4, 6)
-/

namespace D28

open DiracTimeD25

/-! ### Item 1 [K16]: Q1 companion-root ratio is φ¹⁰ -/

theorem sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- Item 1(a). -/
theorem q1_ratio :
    (297 + 135 * Real.sqrt 5) / (135 * Real.sqrt 5 - 297) = (123 + 55 * Real.sqrt 5) / 2 := by
  have hs := sqrt5_sq
  have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hne : 135 * Real.sqrt 5 - 297 ≠ 0 := by nlinarith
  rw [div_eq_div_iff hne two_ne_zero]
  linear_combination (-(55 * 135 : ℝ)) * hs

theorem golden_sq : ((1 + Real.sqrt 5) / 2) ^ 2 = (1 + Real.sqrt 5) / 2 + 1 := by
  linear_combination (1 / 4 : ℝ) * sqrt5_sq

/-- Item 1(b): `φ¹⁰ = (123 + 55√5)/2`. -/
theorem golden_pow_ten : ((1 + Real.sqrt 5) / 2) ^ 10 = (123 + 55 * Real.sqrt 5) / 2 := by
  set φ := (1 + Real.sqrt 5) / 2 with hφ
  have h2 := golden_sq
  have h4 : φ ^ 4 = 3 * φ + 2 := by
    have : φ ^ 4 = (φ ^ 2) ^ 2 := by ring
    rw [this, h2]; linear_combination h2
  have h8 : φ ^ 8 = 21 * φ + 13 := by
    have : φ ^ 8 = (φ ^ 4) ^ 2 := by ring
    rw [this, h4]; linear_combination 9 * h2
  have h10 : φ ^ 10 = 55 * φ + 34 := by
    have : φ ^ 10 = φ ^ 8 * φ ^ 2 := by ring
    rw [this, h8, h2]; linear_combination 21 * h2
  rw [h10, hφ]; ring

/-- Item 1(c): `φ¹⁰ + φ⁻¹⁰ = 123`. -/
theorem golden_pow_ten_add_inv :
    ((1 + Real.sqrt 5) / 2) ^ (10 : ℤ) + ((1 + Real.sqrt 5) / 2) ^ (-10 : ℤ) = 123 := by
  have hs := sqrt5_sq
  have hpos : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  rw [zpow_neg, show (10 : ℤ) = ((10 : ℕ) : ℤ) by rfl, zpow_natCast, golden_pow_ten]
  have hne : (123 + 55 * Real.sqrt 5) / 2 ≠ 0 := by positivity
  field_simp
  linear_combination (3025 : ℝ) * hs

/-- Item 1(d): the roots of `λ² + (297/2)λ − 729/4` are `(−297 ± 135√5)/4`. -/
theorem q1_char_roots (l : ℝ) :
    l ^ 2 + 297 / 2 * l - 729 / 4 = 0 ↔
      l = (-297 + 135 * Real.sqrt 5) / 4 ∨ l = (-297 - 135 * Real.sqrt 5) / 4 := by
  have hs := sqrt5_sq
  have hf : l ^ 2 + 297 / 2 * l - 729 / 4
      = (l - (-297 + 135 * Real.sqrt 5) / 4) * (l - (-297 - 135 * Real.sqrt 5) / 4) := by
    linear_combination (135 * 135 / 16 : ℝ) * hs
  rw [hf, mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-! ### Item 3 [N15]: `8₁₉ = T(3,4)` Alexander polynomial -/

open Polynomial in
/-- Item 3(a): `Δ_{T(3,4)} · (t³ − 1)(t⁴ − 1) = (t¹² − 1)(t − 1)` in `ℤ[t]`. -/
theorem alexT34_torus_formula :
    ((X ^ 6 - X ^ 5 + X ^ 3 - X + 1) * (X ^ 3 - 1) * (X ^ 4 - 1) : ℤ[X])
      = (X ^ 12 - 1) * (X - 1) := by
  ring

/-- Item 3(b): `2cos 3x − 2cos 2x + 1 = (2cos x − 1)(4cos² x − 3)`. -/
theorem alexT34_cos (x : ℝ) :
    2 * Real.cos (3 * x) - 2 * Real.cos (2 * x) + 1
      = (2 * Real.cos x - 1) * (4 * Real.cos x ^ 2 - 3) := by
  rw [Real.cos_three_mul, Real.cos_two_mul]; ring

open Polynomial in
/-- Item 3(d): trefoil factor, `Δ_{T(3,4)} = (t² − t + 1)(t⁴ − t² + 1)` in `ℤ[t]`. -/
theorem alexT34_factor :
    (X ^ 6 - X ^ 5 + X ^ 3 - X + 1 : ℤ[X]) = (X ^ 2 - X + 1) * (X ^ 4 - X ^ 2 + 1) := by
  ring

/-- The same factorisation in any commutative ring. -/
theorem alexT34_factor_ring {R : Type*} [CommRing R] (t : R) :
    t ^ 6 - t ^ 5 + t ^ 3 - t + 1 = (t ^ 2 - t + 1) * (t ^ 4 - t ^ 2 + 1) := by
  ring

theorem circ_sq (α : ℝ) : circ α ^ 2 = circ (2 * α) := by
  rw [circ, circ, sq, ← Complex.exp_add]; congr 1; push_cast; ring

/-- Item 3(c), `∃ k` form: `Δ_{T(3,4)}(e^{2πiα}) = 0` iff `α ≡ ±1/6 (mod 1)` (trefoil factor) or
`2α ≡ ±1/6 (mod 1)` (second factor). -/
theorem alexT34_circle_eq_zero_iff (α : ℝ) :
    circ α ^ 6 - circ α ^ 5 + circ α ^ 3 - circ α + 1 = 0 ↔
      (∃ k : ℤ, α = (k : ℝ) + 1 / 6 ∨ α = (k : ℝ) - 1 / 6) ∨
        (∃ k : ℤ, 2 * α = (k : ℝ) + 1 / 6 ∨ 2 * α = (k : ℝ) - 1 / 6) := by
  have h2 : circ α ^ 4 - circ α ^ 2 + 1 = circ (2 * α) ^ 2 - circ (2 * α) + 1 := by
    rw [← circ_sq]; ring
  rw [alexT34_factor_ring, mul_eq_zero, h2, alex31_poly_circle_eq_zero_iff,
    alex31_poly_circle_eq_zero_iff]

/-- Item 3(c), exact form: `Δ_{T(3,4)}(e^{2πiα}) = 0` iff
`α mod 1 ∈ {1/12, 1/6, 5/12, 7/12, 5/6, 11/12}`. -/
theorem alexT34_circle_eq_zero_iff_fract (α : ℝ) :
    circ α ^ 6 - circ α ^ 5 + circ α ^ 3 - circ α + 1 = 0 ↔
      Int.fract α ∈ ({1 / 12, 1 / 6, 5 / 12, 7 / 12, 5 / 6, 11 / 12} : Set ℝ) := by
  rw [alexT34_circle_eq_zero_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨k, h | h⟩ | ⟨k, h | h⟩)
    · right; left; exact Int.fract_eq_iff.2 ⟨by norm_num, by norm_num, k, by rw [h]; ring⟩
    · right; right; right; right; left
      exact Int.fract_eq_iff.2 ⟨by norm_num, by norm_num, k - 1, by rw [h]; push_cast; ring⟩
    · obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
      · left; exact Int.fract_eq_iff.2 ⟨by norm_num, by norm_num, j, by push_cast at h; linarith⟩
      · right; right; right; left
        exact Int.fract_eq_iff.2 ⟨by norm_num, by norm_num, j, by push_cast at h; linarith⟩
    · obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
      · right; right; right; right; right
        exact Int.fract_eq_iff.2 ⟨by norm_num, by norm_num, j - 1, by push_cast at h ⊢; linarith⟩
      · right; right; left
        exact Int.fract_eq_iff.2 ⟨by norm_num, by norm_num, j, by push_cast at h; linarith⟩
  · intro h
    have hα := Int.floor_add_fract α
    rcases h with h | h | h | h | h | h <;> rw [h] at hα
    · right; exact ⟨2 * ⌊α⌋, Or.inl (by push_cast; linarith)⟩
    · left; exact ⟨⌊α⌋, Or.inl (by linarith)⟩
    · right; exact ⟨2 * ⌊α⌋ + 1, Or.inr (by push_cast; linarith)⟩
    · right; exact ⟨2 * ⌊α⌋ + 1, Or.inl (by push_cast; linarith)⟩
    · left; exact ⟨⌊α⌋ + 1, Or.inr (by push_cast; linarith)⟩
    · right; exact ⟨2 * ⌊α⌋ + 2, Or.inr (by push_cast; linarith)⟩

/-! ### Item 4 [N16, N17]: Litherland count -/

/-- Litherland's count for the torus knot `T(p, q)` at `α` (the signature formula itself is
Litherland 1979, cited, not formalised). -/
def lt (p q : ℕ) (α : ℚ) : ℤ :=
  ∑ i ∈ Finset.Ioo 0 p, ∑ j ∈ Finset.Ioo 0 q,
    (if α < (i : ℚ) / p + (j : ℚ) / q ∧ (i : ℚ) / p + (j : ℚ) / q < α + 1 then -1
     else if (i : ℚ) / p + (j : ℚ) / q < α ∨ (i : ℚ) / p + (j : ℚ) / q > α + 1 then 1 else 0)

/-- Item 4(a), trefoil `T(2,3)`. -/
theorem lt23_values :
    lt 2 3 (1 / 12) = 0 ∧ lt 2 3 (1 / 4) = -2 ∧ lt 2 3 (1 / 2) = -2 ∧ lt 2 3 (3 / 4) = -2 ∧
      lt 2 3 (11 / 12) = 0 := by
  decide +kernel

/-- Item 4(a), `T(3,4) = 8₁₉`. -/
theorem lt34_values :
    lt 3 4 (1 / 24) = 0 ∧ lt 3 4 (1 / 8) = -2 ∧ lt 3 4 (1 / 4) = -4 ∧ lt 3 4 (11 / 24) = -6 ∧
      lt 3 4 (1 / 2) = -6 := by
  decide +kernel

/-- Item 4(b): the trefoil window `−2` on `(1/6, 5/6)`, `0` elsewhere in `(0, 1)`. -/
theorem lt23_window (α : ℚ) (h0 : 0 < α) (h1 : α < 1) (ha : α ≠ 1 / 6) (hb : α ≠ 5 / 6) :
    lt 2 3 α = if 1 / 6 < α ∧ α < 5 / 6 then -2 else 0 := by
  have hI : Finset.Ioo 0 2 = ({1} : Finset ℕ) := by decide
  have hJ : Finset.Ioo 0 3 = ({1, 2} : Finset ℕ) := by decide
  simp only [lt, hI, hJ, Finset.sum_singleton, Finset.sum_insert (by decide : (1 : ℕ) ∉ ({2} : Finset ℕ))]
  norm_num
  rcases lt_or_gt_of_ne ha with hA | hA
  · rw [ite_eq_left ⟨by linarith, by linarith⟩, ite_eq_right (fun h => by linarith [h.2]),
      ite_eq_left (Or.inr (by linarith)), ite_eq_right (fun h => by linarith [h.1])]
    norm_num
  · rcases lt_or_gt_of_ne hb with hB | hB
    · rw [ite_eq_left ⟨by linarith, by linarith⟩, ite_eq_left ⟨by linarith, by linarith⟩,
        ite_eq_left ⟨hA, hB⟩]
      norm_num
    · rw [ite_eq_right (fun h => by linarith [h.1]), ite_eq_left (Or.inl hB),
        ite_eq_left ⟨by linarith, by linarith⟩, ite_eq_right (fun h => by linarith [h.2])]
      norm_num

/-! ### Item 6 [N10, N11]: flat-torus zero modes, block-diagonal η = 0 -/

theorem pauliSymbol_det (a b : ℝ) : (pauliSymbol a b).det = -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
  rw [Matrix.det_fin_two]
  simp [pauliSymbol, σ₁, σ₂]
  ring_nf; rw [Complex.I_sq]; ring

/-- Item 6(a): the flat-torus symbol is singular iff `a = b = 0` (zero modes are codimension two). -/
theorem pauliSymbol_det_eq_zero_iff (a b : ℝ) : (pauliSymbol a b).det = 0 ↔ a = 0 ∧ b = 0 := by
  rw [pauliSymbol_det, neg_eq_zero]
  constructor
  · intro h
    have h' : ((a ^ 2 + b ^ 2 : ℝ) : ℂ) = 0 := by push_cast; exact h
    rw [Complex.ofReal_eq_zero] at h'
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
  · rintro ⟨rfl, rfl⟩; simp

/-- Block-diagonal flat-torus symbol `⊕ₖ (aₖ σ₁ + bₖ σ₂)`, reindexed to `Fin (2 * m)`. -/
noncomputable def blockPauli {m : ℕ} (a b : Fin m → ℝ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.blockDiagonal fun k => pauliSymbol (a k) (b k))

/-- Block-diagonal chiral grading `⊕ₖ σ₃`. -/
noncomputable def blockσ₃ (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.blockDiagonal fun _ : Fin m => σ₃)

/-- Item 6(b): the block-diagonal symbol is Hermitian. -/
theorem blockPauli_isHermitian {m : ℕ} (a b : Fin m → ℝ) : (blockPauli a b).IsHermitian := by
  unfold blockPauli
  rw [Matrix.reindex_apply]
  refine Matrix.IsHermitian.submatrix ?_ _
  unfold Matrix.IsHermitian
  rw [Matrix.blockDiagonal_conjTranspose]
  congr 1; funext k; exact pauliSymbol_isHermitian _ _

theorem blockσ₃_mul_self (m : ℕ) : blockσ₃ m * blockσ₃ m = 1 := by
  unfold blockσ₃
  rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul]
  simp only [σ₃_mul_self]
  rw [show (fun _ : Fin m => (1 : Matrix (Fin 2) (Fin 2) ℂ)) = 1 from rfl, Matrix.blockDiagonal_one]
  exact Matrix.submatrix_one_equiv _

theorem blockσ₃_blockPauli {m : ℕ} (a b : Fin m → ℝ) :
    blockσ₃ m * blockPauli a b * blockσ₃ m = -blockPauli a b := by
  unfold blockσ₃ blockPauli
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_mul]
  have h : (fun k => σ₃ * pauliSymbol (a k) (b k) * σ₃) = fun k => -pauliSymbol (a k) (b k) :=
    funext fun k => σ₃_pauliSymbol_σ₃ _ _
  rw [h, show (fun k => -pauliSymbol (a k) (b k)) = -(fun k => pauliSymbol (a k) (b k)) from rfl,
    Matrix.blockDiagonal_neg]; rfl

/-- Item 6(b): `η(⊕ₖ (aₖ σ₁ + bₖ σ₂)) = 0`, via `eta_eq_zero_of_chiral` with `Γ = ⊕ₖ σ₃`. -/
theorem blockPauli_eta_eq_zero {m : ℕ} (a b : Fin m → ℝ) :
    eta (blockPauli a b) (blockPauli_isHermitian a b) = 0 :=
  eta_eq_zero_of_chiral _ _ _ (blockσ₃_mul_self m) (blockσ₃_blockPauli a b)

end D28
