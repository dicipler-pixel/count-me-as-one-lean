module

public import Mathlib

/-!
# D25.1 — Finite-dimensional chiral-symmetry killing law and orientation sign flip

Dirac Time `DT-T14` (§5.3, item (2) for `η`), finite-dimensional case.

For a Hermitian `D : Matrix (Fin n) (Fin n) ℂ` the spectral eta invariant is
`η(D) = ∑ᵢ sign λᵢ = #{λ > 0} − #{λ < 0}` (with multiplicity), where `λᵢ` are the real
eigenvalues `Matrix.IsHermitian.eigenvalues`.

* `eta_one` : `η(1) = n` (the invariant is not trivially zero).
* `eta_neg` : `η(−D) = −η(D)` (orientation sign flip).
* `eta_eq_zero_of_anticommute` : if an invertible `Γ` satisfies `Γ D = −D Γ` then `η(D) = 0`.
* `eta_eq_zero_of_chiral` : `Γ Γ = 1`, `Γ D Γ = −D` ⇒ `η(D) = 0` (the DT-T14 hypothesis).
* `eta_eq_zero_of_unitary_chiral` : unitary involutive `Γ` version.
* `pauli_eta_eq_zero` : flat-torus 2×2 symbol `a σ₁ + b σ₂` with `Γ = σ₃`.
-/

@[expose] public section

namespace DiracTimeD25

open Matrix Polynomial

variable {n : ℕ}

/-- Finite-dimensional spectral eta invariant: sum of the signs of the real eigenvalues. -/
noncomputable def eta (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) : ℤ :=
  ∑ i, ((SignType.sign (hD.eigenvalues i) : SignType) : ℤ)

/-- `η(D)` is the signed count of roots of the characteristic polynomial (with multiplicity). -/
theorem eta_eq_roots (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    eta D hD = (D.charpoly.roots.map fun z : ℂ => ((SignType.sign z.re : SignType) : ℤ)).sum := by
  rw [hD.roots_charpoly_eq_eigenvalues, Multiset.map_map, eta, Finset.sum_eq_multiset_sum]
  congr 1

/-- `η` equals `#{λ > 0} − #{λ < 0}`. -/
theorem eta_eq_card_sub_card (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    eta D hD = ((Finset.univ.filter fun i => 0 < hD.eigenvalues i).card : ℤ)
      - ((Finset.univ.filter fun i => hD.eigenvalues i < 0).card : ℤ) := by
  rw [eta]
  have h : ∀ i, ((SignType.sign (hD.eigenvalues i) : SignType) : ℤ)
      = (if 0 < hD.eigenvalues i then 1 else 0) - (if hD.eigenvalues i < 0 then 1 else 0) := by
    intro i
    rcases lt_trichotomy (hD.eigenvalues i) 0 with h | h | h
    · simp [h, not_lt.2 h.le]
    · simp [h]
    · simp [h, not_lt.2 h.le]
  simp only [h, Finset.sum_sub_distrib, Finset.sum_boole]

/-- Charpoly of `−D` from the spectral theorem. -/
theorem charpoly_neg_eq (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    (-D).charpoly = ∏ i, (X - C (-(hD.eigenvalues i : ℂ))) := by
  have hs := hD.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hs
  set U := hD.eigenvectorUnitary
  have h1 : -D = ((U : Matrix (Fin n) (Fin n) ℂ) * diagonal fun i => -(hD.eigenvalues i : ℂ))
      * star (U : Matrix (Fin n) (Fin n) ℂ) := by
    conv_lhs => rw [hs]
    rw [← diagonal_neg]
    simp only [mul_neg, neg_mul]
    rfl
  rw [h1, charpoly_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul, charpoly_diagonal]

/-- **Orientation sign flip**: `η(−D) = −η(D)`. -/
theorem eta_neg (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian) :
    eta (-D) hD.neg = -eta D hD := by
  have hc : (-D).charpoly
      = ((Finset.univ.val.map fun i => -(hD.eigenvalues i : ℂ)).map fun a => X - C a).prod := by
    rw [charpoly_neg_eq D hD, Multiset.map_map]; rfl
  rw [eta_eq_roots, hc, Polynomial.roots_multiset_prod_X_sub_C, Multiset.map_map, eta,
    Finset.sum_eq_multiset_sum, ← Multiset.sum_map_neg]
  congr 1
  apply Multiset.map_congr rfl
  intro i _
  simp [Function.comp, Left.sign_neg]

/-- Non-vacuity: `η(1) = n`. -/
theorem eta_one : eta (1 : Matrix (Fin n) (Fin n) ℂ) isHermitian_one = n := by
  rw [eta_eq_roots, charpoly_one, Fintype.card_fin, Polynomial.roots_pow]
  have : (X - 1 : ℂ[X]) = X - C 1 := by simp
  rw [this, roots_X_sub_C]
  simp [Multiset.map_nsmul, Multiset.sum_nsmul]

/-- General killing law: an invertible `Γ` anticommuting with `D` forces `η(D) = 0`. -/
theorem eta_eq_zero_of_anticommute (D Γ : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (hΓ : Γ.det ≠ 0) (h : Γ * D = -D * Γ) : eta D hD = 0 := by
  have hc : (-D).charpoly = D.charpoly := charpoly_eq_of_mul_eq_mul hΓ h.symm
  have he : hD.neg.eigenvalues = hD.eigenvalues :=
    (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff hD.neg hD).2 hc
  have h1 : eta (-D) hD.neg = eta D hD := by simp only [eta, he]
  have h2 := eta_neg D hD
  omega

/-- **Chiral-symmetry killing law** (DT-T14 (2) for `η`, finite-dimensional):
`Γ Γ = 1` and `Γ D Γ = −D` imply `η(D) = 0`. -/
theorem eta_eq_zero_of_chiral (D Γ : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (hΓ2 : Γ * Γ = 1) (h : Γ * D * Γ = -D) : eta D hD = 0 := by
  have hdet : Γ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hΓ2
    rw [det_mul, det_one, h0, zero_mul] at this
    exact zero_ne_one this
  refine eta_eq_zero_of_anticommute D Γ hD hdet ?_
  calc Γ * D = Γ * D * (Γ * Γ) := by rw [hΓ2, mul_one]
    _ = (Γ * D * Γ) * Γ := by simp only [mul_assoc]
    _ = -D * Γ := by rw [h]

/-- Unitary version: `Γ` unitary and `Γ D Γ⋆ = −D` imply `η(D) = 0`. -/
theorem eta_eq_zero_of_unitary_conj (D Γ : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (hU : Γ ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (h : Γ * D * star Γ = -D) :
    eta D hD = 0 := by
  have hΓ1 : star Γ * Γ = 1 := Unitary.star_mul_self_of_mem hU
  have hdet : Γ.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hΓ1
    rw [det_mul, det_one, h0, mul_zero] at this
    exact zero_ne_one this
  refine eta_eq_zero_of_anticommute D Γ hD hdet ?_
  calc Γ * D = Γ * D * (star Γ * Γ) := by rw [hΓ1, mul_one]
    _ = (Γ * D * star Γ) * Γ := by simp only [mul_assoc]
    _ = -D * Γ := by rw [h]

/-- DT-T14 hypotheses verbatim: fixed unitary `Γ`, `Γ² = I`, `Γ D Γ = −D` ⇒ `η(D) = 0`. -/
theorem eta_eq_zero_of_unitary_chiral (D Γ : Matrix (Fin n) (Fin n) ℂ) (hD : D.IsHermitian)
    (_hU : Γ ∈ unitary (Matrix (Fin n) (Fin n) ℂ)) (hΓ2 : Γ * Γ = 1) (h : Γ * D * Γ = -D) :
    eta D hD = 0 :=
  eta_eq_zero_of_chiral D Γ hD hΓ2 h

/-! ### The 2×2 flat-torus Dirac symbol with `Γ = σ₃` -/

/-- Pauli `σ₁`. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli `σ₂`. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
/-- Pauli `σ₃`. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- The flat-torus Dirac symbol `a σ₁ + b σ₂`. -/
def pauliSymbol (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := (a : ℂ) • σ₁ + (b : ℂ) • σ₂

theorem pauliSymbol_isHermitian (a b : ℝ) : (pauliSymbol a b).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliSymbol, σ₁, σ₂, Matrix.conjTranspose_apply]

theorem σ₃_mul_self : σ₃ * σ₃ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₃_pauliSymbol_σ₃ (a b : ℝ) : σ₃ * pauliSymbol a b * σ₃ = -pauliSymbol a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ₃, pauliSymbol, σ₁, σ₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- Flat-torus corollary: `σ₃ (a σ₁ + b σ₂) σ₃ = −(a σ₁ + b σ₂)`, hence `η = 0`. -/
theorem pauli_eta_eq_zero (a b : ℝ) :
    eta (pauliSymbol a b) (pauliSymbol_isHermitian a b) = 0 :=
  eta_eq_zero_of_chiral _ σ₃ _ σ₃_mul_self (σ₃_pauliSymbol_σ₃ a b)

end DiracTimeD25

end
