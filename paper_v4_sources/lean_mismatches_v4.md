# Lean mismatches and partial matches, combined paper v4 (D32)

Lean source: `/workspace/lean_green/cmao_combined_lean` at commit `3a4902ccf187943d220900009da96dd6578aa982` (20 Nov 2026, 08:02 CT; HEAD, working tree clean when read). Every statement below was read with `git show 3a4902cc:<path>`. v2 used commit `24e08e12`.

**What changed from v2:** only N27, below in section A2. The name check (`name_check_v3.txt`) covers all 122 distinct [T] names of v2. Each one is in report.json at 3a4902cc, is declared as a `theorem` in the source there, and has the same statement text at 24e08e12 and 3a4902cc. None was flagged. Between the two commits the only .lean source files that changed are `D28/Eq15.lean` (new theorems; `eq15_reduced_le64` and `rep_eq15_reduced_le64` now have new proofs with unchanged statements) and `D28.lean`, plus two new files, `D28/FastPsi.lean` and `D28/Qq2Table.lean`.

**Rule applied:** a claim gets [T] only when the Lean statement has the same hypotheses, conclusion and range as the claim. When the claim is broader, it is split:
- **Suffix `a`:** the part Lean states exactly. It carries the tag.
- **Suffix `b`/`c`, or the plain id:** the remainder. It keeps its v1 grade and has no tag.

Bounded results are written as bounded in the claim and in the paper text.


## v4 changes (D32; same pin, 3a4902cc)

**K14, re-audited after D31 review G1.**
- Lean statement at 3a4902cc (`git show`): `theorem regular_squared {R : Type} [CommRing R] (z : R) (h : z * z - z + 1 = 0) : (z * z) * (z * z) + (z * z) + 1 = 0`.
- The v3 claim was "Regular root squared is a primitive cube root of unity". That is broader: the theorem does not state w ≠ 1, and over a ring of characteristic 3 (for example ℤ/3, with z = 2) w = 1 satisfies w² + w + 1 = 0.
- Split into **K14a** (EXACT, [T] `Ladder.regular_squared`): "if z² − z + 1 = 0 in a commutative ring then w = z² satisfies w² + w + 1 = 0".
- **K14b** (EXACT, by hand, no tag): over ℂ, z = e^{±iπ/3} and w = e^{±2πi/3} is primitive, because w = 1 would give 3 = 0.
- Part I line 140 (CMaO text, kept verbatim) gets a v4 note.

**Weaker-tag policy (D31 G4).** A theorem in a tag moves to the support column when it is a special case or a shorter range of another theorem in the same tag:

| Claim | Removed from tag (now named in the support column) | Stronger theorem kept in tag | Relation |
|---|---|---|---|
| N28 | `DiracTimeD25.BHL.eq17_mod_q49` (`∀ d < 49, …`) | `D28.eq17_le128` (`∀ d ≤ 128, …`) | shorter range |
| N7 | `DiracTimeD25.eta_eq_zero_of_unitary_chiral` (hyps: Γ unitary, Γ² = 1, ΓDΓ = −D) | `DiracTimeD25.eta_eq_zero_of_chiral` (hyps: Γ² = 1, ΓDΓ = −D) | special case (extra hypothesis) |
| N12 | `DiracTimeD25.alex31_wall_at_sixth` (`alex31 (circ (1/6)) = 0`) | `DiracTimeD25.alex31_circle_eq_zero_iff` | instance (k = 0, +1/6) |
| N27 (v3) | `eq15_mod_q49`, `eq15_reduced_le23`, `D28.eq15_reduced_le64` | `D28.eq15_mod_q259`, `D28.eq15_reduced_le128` | shorter ranges |

Kept, after checking: `eta_eq_zero_of_unitary_conj` (hypothesis ΓDΓ* = −D, a different form); N13 `sixth_solves_edge` (the claim states the α = 1/6 clause); N29 `phi0_ne_bhlM` (follows only from two theorems jointly); K10 `h31_order6`; N20 `mem_crossings_iff` (weaker hypotheses than the conjunct of `floor_sub_floor_eq_card_crossings`). The CMaO, D25 and Bridge tags carried over from v1 were otherwise checked only for existence and an unchanged statement (now stated in the paper's Scope).

**New claims N46–N49 (Rule 3 citations, D31 G5).** None is tagged; there are no Lean theorems for them.
- N46 EXACT: cited, KnotInfo.
- N47 EXACT: cited, Stipsicz–Szabó 2021 §1, plus the reflection argument.
- N48 MODEL: KnotInfo and SnapPy numerics. Amphichirality alone does not force CS = 0.
- N49 EXACT: by hand from amphichirality; KnotInfo agrees.

## A. Full matches (tagged as is)

| Claim | Lean | Lean statement | Note |
|---|---|---|---|
| N37 | `D28.dirac_cmao_LM6` | `{K} [Field K] (L M : K) (hM : M ≠ 0) : L * M ^ 6 = -1 ↔ L = -(M ^ 6)⁻¹` | Exact. The claim text now says "any field". |
| N28 | `D28.eq17_le128` (+ v1 `hasProd_negInf`, `hasSum_falseTheta`; `eq17_mod_q49` moved to the support column in v4) | `∀ d ≤ 128, coeff d (2 + 2 * X^2 * bhlM) = coeff d (negInf + falseTheta)` | **Bounded, d ≤ 128.** This is the same range as the Python check. Claim restated as "every degree d ≤ 128 (bounded)". In v1 the tag covered only q^48 while the claim said q^128; that gap is now closed. |
| K15 | v1 `Monodromy.h41_trace5`, `Ladder.fig8_fifth` + new `D28.golden_pow_ten_add_inv` | `((1+√5)/2)^(10:ℤ) + ((1+√5)/2)^(-10:ℤ) = 123` (over ℝ) | Partial in v1: `fig8_fifth` states x⁵ + (3−x)⁵ = 123 for any root of x² − 3x + 1 in a commutative ring, and does not mention φ. With the new theorem the "= φ¹⁰ + φ⁻¹⁰" part is stated directly. |
| N22 | `D28.etaCircle_three_quarter`, `D28.odometer_no_crossing`, `D28.odometer_one_crossing` | `etaCircle (3/4) = -1/2`; `Finset.Ioc ⌊1/4⌋ ⌊3/4⌋ = ∅ ∧ etaCircle (3/4) - etaCircle (1/4) = -1`; `⌊5/4⌋ - ⌊1/4⌋ = 1 ∧ etaCircle (5/4) - etaCircle (1/4) = 0 ∧ … ≠ 2 * (⌊5/4⌋ - ⌊1/4⌋)` | **Partial wording fixed.** Lean writes SF as the floor difference. Claim restated with "SF = ⌊5/4⌋ − ⌊1/4⌋". That this equals the crossing count is D25 `floor_sub_floor_eq_card_crossings` (N20, already [T]). `etaCircle` is the D25 definition `if a ∈ ℤ then 0 else 1 − 2·fract a`; that it is the spectral η stays N19 (DERIVED, untagged). |

## A2. N27 in v3 (Eq. 1.5): now fully matched, over a bounded range

| Claim (v3) | Lean | Lean statement | Note |
|---|---|---|---|
| N27a | D25 `DiracTimeD25.BHL.eq15_iff_coeff`, `lhs15_eq_iff` | `2 * X^2 * expand 2 phi0 = psi + rescale (-1) psi ↔ ∀ k, coeff k phi0 = coeff (2*k+2) psi` (the general form for f, g with `coeff 0 g = 0`) | Exact. All-degree **equivalence** only, not the identity in all degrees. |
| N27b | `D28.eq15_mod_q259`, `D28.eq15_reduced_le128` | `∀ d < 259, coeff d (2 * X^2 * expand 2 phi0) = coeff d (psi + rescale (-1) psi)`; `∀ k ≤ 128, coeff k phi0 = coeff (2*k+2) psi` | Exact. **Bounded: degrees d ≤ 258 (through q^258) and k ≤ 128.** This is the same range as the Python integer check, so the v2 remainder "through q^258, Python only" is now [T]. |

How v2 differs:
- v2 N27a listed `eq15_mod_q49`, `eq15_reduced_le23` and `D28.eq15_reduced_le64` and was bounded at k ≤ 64.
- v2 N27b (through q^258) had no tag.
- In v3 those three theorems still exist with unchanged statements, but they are weaker corollaries of the new theorems. They are no longer listed as tags, because a tag should state the claim itself. They are named in the support column of N27b.
- Eq. 1.5 in all degrees is **not** proved. Neither is Eq. 1.7 in all degrees (Franklin's involution not attempted), nor the WRT link (BHL Eqs. 2.1–2.6). None of these is tagged.

[v4: superseded. N28 no longer tags the weaker `eq17_mod_q49`; see "v4 changes".]

## B. Splits (claim broader than Lean)

| v1 claim | Tagged part (v2) and Lean | Lean statement (abridged only by notation) | Remainder (v2, v1 grade, no tag) | Why split |
|---|---|---|---|---|
| K16 (EXACT, untagged in v1) | **K16a**: `D28.q1_char_roots`, `D28.q1_ratio`, `D28.golden_pow_ten` | `l^2 + 297/2*l - 729/4 = 0 ↔ l = (-297+135√5)/4 ∨ l = (-297-135√5)/4`; `(297+135√5)/(135√5-297) = (123+55√5)/2`; `((1+√5)/2)^10 = (123+55√5)/2` | **K16b** EXACT: these are the companion roots of Ramanujan Challenge Q1, and \|λ_d/λ_s\| is that quotient | Lean knows nothing about Q1. The quadratic is cited from the RM proofs (Eq. 27), and the sign step that turns \|λ_d/λ_s\| into the quotient is done by hand. |
| N10 (DERIVED) | **N10a** EXACT: `D28.blockPauli_isHermitian`, `D28.blockσ₃_blockPauli`, `D28.blockPauli_eta_eq_zero` | `{m : ℕ} (a b : Fin m → ℝ) : eta (blockPauli a b) _ = 0`, where `blockPauli` is `blockDiagonal (k ↦ pauliSymbol (a k) (b k))` reindexed to `Fin (2m)` | **N10** DERIVED: the infinite flat-torus operator, η ≡ 0 for all twists | Lean covers finite truncations only. Analytic continuation of the infinite operator is by hand. The new_lean statement 6(b) asked for any finite index type ι; Lean uses `Fin m`. That is equivalent up to reindexing, but narrower as written. |
| N11 (EXACT) | **N11a**: `D28.pauliSymbol_det`, `D28.pauliSymbol_det_eq_zero_iff` | `(pauliSymbol a b).det = -((a:ℂ)^2 + (b:ℂ)^2)`; `(pauliSymbol a b).det = 0 ↔ a = 0 ∧ b = 0` | **N11b** EXACT: zero modes need (α, β) ∈ ℤ², codimension two | The step from the symbol to the twisted operator (a = m + α, b = n + β) is by hand. |
| N15 (EXACT) | **N15a**: `D28.alexT34_torus_formula`, `D28.alexT34_factor`, `D28.alexT34_cos`, `D28.alexT34_circle_eq_zero_iff_fract` | `(X^6-X^5+X^3-X+1)(X^3-1)(X^4-1) = (X^12-1)(X-1)` in ℤ[X]; `… = (X^2-X+1)(X^4-X^2+1)`; `2cos3x - 2cos2x + 1 = (2cos x - 1)(4cos²x - 3)`; `circ α^6 - … + 1 = 0 ↔ Int.fract α ∈ {1/12, 1/6, 5/12, 7/12, 5/6, 11/12}` | **N15b** EXACT: P = Δ_{T(3,4)} (torus-knot formula, cited), and e^{−3ix}P(e^{ix}) = 2cos3x − 2cos2x + 1 | Lean proves the identities about the polynomial P. That P is the Alexander polynomial of 8_19, and the symmetrisation step, are not in Lean. |
| N16 (EXACT) | **N16a**: `D28.lt23_values`, `D28.lt34_values` | `lt 2 3` at 1/12, 1/4, 1/2, 3/4, 11/12 = 0, −2, −2, −2, 0; `lt 3 4` at 1/24, 1/8, 1/4, 11/24, 1/2 = 0, −2, −4, −6, −6 (`lt` = Litherland's count, defined in D28/Algebra.lean) | **N16b** EXACT, cited: the count equals the Levine–Tristram signature (Litherland 1979) | Lean proves the count, not the signature. |
| N17 (EXACT) | **N17a**: `D28.lt23_window` | `(α : ℚ) (0 < α) (α < 1) (α ≠ 1/6) (α ≠ 5/6) : lt 2 3 α = if 1/6 < α ∧ α < 5/6 then -2 else 0` | **N17b** EXACT: the signature statement for real α | Lean covers rational α and the count only. The claim is about real α and the signature. |
| N30 (EXACT; [T] in v1 for 17 coefficients only) | **N30a**: D25 `rep17_phi0_sub_bhlM` + `D28.phi0_sub_bhlM_pos`. **N30b**: `D28.negPoch_eq_prod_Icc`, `D28.rawDiff_term` | `∀ k, 1 ≤ k → k ≤ 128 → 0 < coeff k (phi0 - bhlM)`; `(n ≥ 1) : X^n (1 - X^n) negPoch (2n+1) = X^n (1 - X^(4n)) ∏_{j ∈ Icc 1 (2n+1) \ {n, 2n}} (1 + X^j)` | **N30c** EXACT: the summands are not coefficientwise positive (exact arithmetic, d28_checks G) | **Positivity bounded at k ≤ 128.** All-degree positivity is open and stays in the bag. |
| N31 (DERIVED) | **N31a** EXACT: `D28.moser_fibre_orders`, `D28.orbifold_euler` | `\|2*3*1 - 2\| = 4 ∧ \|2*3*1 - (-2)\| = 8` (ℤ); `2 - ((1-1/2)+(1-1/3)+(1-1/4)) = 1/12 ∧ 2 - ((1-1/2)+(1-1/3)+(1-1/8)) = -1/24` (ℚ) | **N31** DERIVED: the surgery and geometry statement (Moser 1971, SnapPy H₁) | Lean checks the numbers only. That they are the fibre orders and orbifold Euler characteristics is cited. |
| N33 (EXACT) | **N33a**: `D28.lens_L21` | `(1^2 + 1) % 2 = 0` | **N33** EXACT: S³_{±2}(U) = L(2,1) = ℝP³ and L(2,1) ≅ −L(2,1) (classical) | Lean proves the congruence only. |
| N41 (EXACT) | **N41a**: `D28.shell_sum` | `(n : ℕ) : ∑ l ∈ range n, 2 * (2 * l + 1) = 2 * n ^ 2` | **N41b** EXACT: the T² counts are (2k+1)² and 4k | The claim had two parts; Lean proves the sum. The claim's "2Σ(2l+1)" was restated as Lean's "Σ 2(2l+1)", which is the same number. |

## C. D28 theorems not used as tags

`etaCircle_five_quarter` (implied by N22), `alexT34_circle_eq_zero_iff` (the ∃k form; the fract form is used), `alexT34_factor_ring`, `circ_sq`, `sqrt5_sq`, `golden_sq`, `blockσ₃_mul_self`, and the fast-model helper lemmas: `fShift_eq`, `fAdd_eq`, `mShift_getD`, `mOnePlus_eq`, `fOnePlus_eq`, `fNegPoch_eq`, `fSum_eq`, `rep_phi0_fast`, `rep_bhlM_fast`, `rep_falseTheta_fast`, `rep_negInf_fast`, `rep129_phi0_sub_bhlM_pos`, `rep_eq15_reduced_le64`, `rep129_eq17`. New at 3a4902cc and also not used as tags: `eq15_reduced_le64` (a corollary now), `rep_eq15_reduced_le128`, `rep259_psi_tab`, `fQq2Inv_259_tab`, the 17 `fQq2Inv_259_*` table lemmas, and the FastPsi lemmas (`length_geomPre`, `getD_geomPre_stable`, `getD_geomPre`, `rep_geomInv_mul`, `rep_qq2Inv_fast`, `rep_psi_fast`, `fSum_congr`). These are lemmas or alternative forms, and none is a claim of the paper.

## D. Not-for-Lean list: stays untagged

N2 and N3 (SnapPy, MODEL), N18 (ρ = LT signature, DERIVED), N19 (η(D_a) = 1 − 2{a} as a spectral statement, DERIVED), N23 and N24 (APS, Dai–Freed, Kirk–Lesch, cited), N26 (WRT ↔ φ₀, M by Laplace transform, DERIVED), N42 (mock theta, cited), N45 (eta_neg ↔ chiral_31, ANALOGY). All are untagged in claims_v2.py.

## E. Tags carried over from v1 without change

All other v1 tags (CMaO K-claims; D25 N7–N9, N12, N14, N20, N21, N29; Bridge N13, N44) are carried over unchanged. `git diff f4e37264 3a4902cc` shows no change to any non-D28 .lean file, so the statements read for v1 still apply. They were not re-audited against the stricter v2 rule, except N27, N28, N30 and K15. In v3, `name_check_v3.txt` confirms that every one of them exists unchanged at 3a4902cc.
