# D28 — new Lean statements (v1)

Ink Between the Stars, 2026-11-20 (America/Chicago). For Dispatch → Lean Green.

Each item is an EXACT claim of `combined_paper_v1.tex` that is **not** proved in the combined
project `/workspace/lean_green/cmao_combined_lean` @ `f4e372646ff458e3418eead24f0c304d9194bea9`
(Lean v4.36.0-rc2, Mathlib e8ba86fa). Checked by reading `CMaOBridge.lean`, `FigureEightAnchors/*.lean`,
`DiracTimeD25/*.lean` and the 201 names in `verification/report.json`, and by grepping for the key
objects (Litherland count, T(3,4), the Q1 roots, cos 3x, etaCircle(3/4), shells, block diagonals,
lens/Seifert arithmetic, q-series beyond q^48). None were found.
Paper claim ids are in brackets. Priority order: 1–5 first (small, decidable, directly used by the paper).

## 1. Q1 companion-root ratio is φ¹⁰   [K16]
Work in ℝ (or in ℚ(√5) as pairs of rationals). Let s = √5.
- (a) `(297 + 135*s) / (135*s - 297) = (123 + 55*s) / 2`.
- (b) `((1 + s)/2)^10 = (123 + 55*s) / 2`.
- (c) `((1 + s)/2)^10 + ((1 + s)/2)^(-10) = 123`.
- (d) the roots of `λ^2 + (297/2) λ - 729/4` are `(-297 ± 135*s)/4`.
Finite / decidable in ℚ(√5).

## 2. Dirac Time L = −M⁻⁶ ⇔ CMaO L·M⁶ = −1   [N37]
In any field `K`, for `M ≠ 0`: `L * M^6 = -1 ↔ L = -(M^6)⁻¹`.

## 3. 8₁₉ = T(3,4) Alexander polynomial and its unit-circle walls   [N15]
- (a) In ℤ[t]: `(t^6 - t^5 + t^3 - t + 1) * (t^3 - 1) * (t^4 - 1) = (t^12 - 1) * (t - 1)`.
- (b) For all real x: `2*cos(3x) - 2*cos(2x) + 1 = (2*cos x - 1) * (4*cos x ^ 2 - 3)`.
- (c) For all real α, with z = e^{2πiα}: `z^6 - z^5 + z^3 - z + 1 = 0 ↔ α mod 1 ∈ {1/12, 1/6, 5/12, 7/12, 5/6, 11/12}`.
- (d) Bridge form: `t^6 - t^5 + t^3 - t + 1 = (t^2 - t + 1) * (t^4 - t^2 + 1)` (the trefoil factor; the second factor's circle roots are cos = ±√3/2).

## 4. Litherland count for torus-knot Levine–Tristram signatures   [N16, N17]
Define for p q : ℕ and α : ℚ
`lt p q α = Σ_{1≤i<p} Σ_{1≤j<q} (if α < i/p + j/q < α+1 then -1 else if i/p + j/q < α ∨ i/p + j/q > α+1 then 1 else 0)`.
- (a) values: `lt 2 3` at 1/12, 1/4, 1/2, 3/4, 11/12 = 0, -2, -2, -2, 0; `lt 3 4` at 1/24, 1/8, 1/4, 11/24, 1/2 = 0, -2, -4, -6, -6 (decide).
- (b) window: for all α : ℚ with 0 < α < 1, α ≠ 1/6, α ≠ 5/6: `lt 2 3 α = if 1/6 < α ∧ α < 5/6 then -2 else 0`.
(This states the counting formula only; that it equals the Levine–Tristram signature is Litherland 1979, cited, not to be formalised here.)

## 5. Circle odometer: smooth drift with no crossing   [N22]
With `DiracTimeD25.etaCircle` as defined in the project:
- (a) `etaCircle (3/4) = -1/2`.
- (b) `Finset.Ioc ⌊(1/4:ℝ)⌋ ⌊(3/4:ℝ)⌋ = ∅` (no crossing) and `etaCircle (3/4) - etaCircle (1/4) = -1`.
- (c) `⌊(5/4:ℝ)⌋ - ⌊(1/4:ℝ)⌋ = 1` and `etaCircle (5/4) - etaCircle (1/4) = 0`, so `Δη ≠ 2·SF`.

## 6. Flat-torus zero modes are codimension two; block-diagonal η = 0   [N10, N11]
- (a) For real a b: `pauliSymbol a b` is singular (det = 0) ↔ `a = 0 ∧ b = 0`. (det = −(a² + b²).)
- (b) For a finite index type ι and families a b : ι → ℝ, the block-diagonal matrix
  `Matrix.blockDiagonal (fun k => pauliSymbol (a k) (b k))` is Hermitian and its `eta` is 0
  (Γ = blockDiagonal of σ₃; reuse `eta_eq_zero_of_chiral`).

## 7. ±2 surgery arithmetic (Moser fibres, orbifold Euler characteristic, lens control)   [N31, N33]
- (a) For p ∈ {2, −2}: `|2*3*1 - p| ∈ {4, 8}` with p=2 ↦ 4, p=−2 ↦ 8.
- (b) In ℚ: `2 - ((1-1/2) + (1-1/3) + (1-1/4)) = 1/12` and `2 - ((1-1/2) + (1-1/3) + (1-1/8)) = -1/24`.
- (c) `(1^2 + 1) % 2 = 0` (q² ≡ −1 mod p for L(2,1)).
Trivial; include only if cheap.

## 8. S² shell sum   [N41]
For all n : ℕ, `Σ_{l<n} 2*(2*l+1) = 2*n^2`.

## 9. Raw-difference ruler: term identity and finite positivity   [N30]
In `PowerSeries ℤ` (use the project's `negPoch`):
- (a) for n ≥ 1: `X^n * (1 - X^n) * negPoch (2n+1) = X^n * (1 - X^(4n)) * ∏_{j ∈ [1, 2n+1] \ {n, 2n}} (1 + X^j)`.
- (b) for 1 ≤ k ≤ 128: `0 < coeff k (phi0 - bhlM)` (currently proved only for k ≤ 16 via `rep17_phi0_sub_bhlM`). Kernel cost may be high; k ≤ 64 is an acceptable first step.

## 10. BHL identities to higher order   [N27, N28]
- (a) Eq. (1.5) reduced: `∀ k ≤ 128, coeff k phi0 = coeff (2*k+2) psi` (Python exact check covers this; Lean currently k ≤ 23 / degree ≤ 48).
- (b) Eq. (1.7): `∀ d ≤ 128, coeff d (2 + 2*X^2*bhlM) = coeff d (negInf + falseTheta)` (Lean currently d ≤ 48).
- (c) Stretch: Eq. (1.7) in all degrees via Franklin's involution (BHL §3). This is a real theorem, not a finite check.

## Not for Lean (cited or floating point; listed so nobody formalises them by mistake)
- WRT ↔ φ₀, M via BHL Laplace transforms (N26), Habiro expansion, Dai–Freed/Kirk–Lesch gluing, APS index and ρ = LT signature (N18), η(D_a) = 1 − 2{a} as a spectral statement (N19): cited, DERIVED.
- 4₁ volume, cusp shape 2√3 i, SnapPy outputs (N2, N3): MODEL.
- The link "η sign flip (`eta_neg`) ↔ trefoil chirality (`chiral_31`)" is NOT a theorem; it is graded ANALOGY (N45).
