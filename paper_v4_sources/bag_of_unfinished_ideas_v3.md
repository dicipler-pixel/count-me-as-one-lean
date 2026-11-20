# Bag of unfinished ideas v3 (D28 → D32)

> **v3 (D32, 20 Nov 2026).** This version keeps every item of `bag_of_unfinished_ideas_v1.md` (there was no v2 bag). Only the Lean status in items 1, 3 and 7 changes. The Lean references are to `/workspace/lean_green/cmao_combined_lean` at commit `3a4902ccf187943d220900009da96dd6578aa982`, read with `git show`. The companion paper is `combined_paper_v4`, and the current README is `README_v4.md`; README_v3 and README_v1 are superseded.

These are claims and ideas that are still broken or open after one strawman+breaker pass in `combined_paper_v1.tex`. Each comes with Jeromie's question, quoted verbatim with its file and message/turn. Questions are copied as written, typos included. Where a math expression in the sweep file was split across lines by the export (as in M067), the line breaks are shown as `/`.

Main quote file: `/workspace/ink/old_chats/aps_recovery/sweep/dirac_review_ALL_user_questions.md` (cited as "sweep", with its M-number).

---

## 1. An actual η for an actual operator on the 8_19 complement (B1, B3, B4)

> "Compute or estimate the η-invariant of the Spinᶜ Dirac operator on the 8₁₉ knot complement with minimal flux."
> (sweep, M043)

> "extract the finite η value via extrapolation, or / compute the Chern–Simons invariant for / 8 / 19 / … , or / explicitly state the theorem-level claim this calculation supports (and nothing more)."
> (sweep, M067)

- **Strawman:** η(8_19) ≈ 0.013 = CS/π, using hyperbolic volume 6.0259 or 10.149 and CS = 1/24.
- **Breaker:** 8_19 = T(3,4) is a torus knot. Its complement is Seifert fibred and has no hyperbolic metric. SnapPy 3.3.2 returns volume 0 with flat tetrahedra (d28_checks_v1_output.txt §F). The hyperbolic CS input does not exist, and no operator, metric, boundary condition or flux was ever fixed.
- **What survives:** the Levine–Tristram signature function of T(3,4), [0, −2, −4, −6, −6] on the five windows. This is a ρ-type invariant for the U(1) flat connections, from Litherland's count (verify_sweep_and_bhl_v1_output.txt). **[v3]** The count values are now a Lean theorem, `D28.lt34_values`. That the count equals the signature is cited (Litherland 1979), not proved in Lean. It is not the η of a Dirac operator on the complement.
- **Still open:** fix a metric (for example a Seifert-fibred metric on the complement with a cylindrical end), a spin^c structure, a flat or minimal-flux connection and APS boundary conditions, then compute η. Nicolaescu-type formulas for η on Seifert manifolds would be the route. None of this has been done.
- Grade now: BROKEN (old value); the replacement is DERIVED (LT signature as ρ).

## 2. The DT-O5 gluing formula: a signed boundary that the bulk can see

> "bring back our dirac anchor and writw the theorem level statement"
> (sweep, M047)

- **Strawman:** the boundary η/spectral-flow record alone determines the sign of the filling (+2 against −2 surgery on the trefoil).
- **Breaker:** the two fillings share the knot, the crossing number and H_1 = Z/2 (SnapPy, §F). The BHL boundary records φ0 and M differ (they split at q^1, which is in Lean), but no theorem says that a D-type boundary operator's η distinguishes them. The BHL identities are q-series identities, and their link to the WRT invariants is cited (BHL 2011; Lawrence–Zagier) and graded DERIVED, not proved here.
- **Still open:** a gluing formula of Kirk–Lesch / Dai–Freed type for the actual 3D operator on S^3 \ K with the two Dehn fillings, which produces a sign difference matching φ0 − M. That is DT-O5, and DT-O6 depends on it.

## 3. Positivity of φ0 − M in every degree

> "explicitly state the theorem-level claim this calculation supports (and nothing more)."
> (sweep, M067, third line)

- **Strawman:** φ0 − M > 0 coefficientwise because each term q^n(1 − q^{4n})∏(1+q^j) is positive.
- **Breaker:** the terms are not coefficientwise positive (d28_checks_v1_output.txt §G lists negative coefficients). Positivity of the sum holds through q^128 by exact arithmetic (the verify script). **[v3]** In Lean, `D28.phi0_sub_bhlM_pos` proves `∀ k, 1 ≤ k → k ≤ 128 → 0 < coeff k (phi0 - bhlM)`, so positivity is proved for 1 ≤ k ≤ 128 (bounded). `D28.rawDiff_term` proves the term identity `X^n (1 - X^n) negPoch(2n+1) = X^n (1 - X^(4n)) ∏_{j ∈ [1, 2n+1] \ {n, 2n}} (1 + X^j)` for every n ≥ 1. (v1 said "term identity only for k ≤ 16". That was stale and also misstated: what v1's Lean covered was the first 17 coefficients of φ0 − M, through `rep17_phi0_sub_bhlM`.)
- **Still open:** a combinatorial proof (an injection or a Franklin-type involution) for every degree. Eq. 1.7 holds in all degrees by Franklin's involution for the false theta, but that does not give positivity of φ0 − M.

## 4. The eta sign flip as the spectral face of trefoil chirality (N45, ANALOGY)

> "at this point i am unclear if we are doing ,seeing , or wanting  the same thing,, i wanted everthing to go back to the dirac anchor and the electron how off do you think we are now we seemed to lose our way there"
> (sweep, M045)

- **Strawman:** η(−D) = −η(D) (D25 `eta_neg`) and the trefoil has no mirror certificate (CMaO `chiral_31`), so they are the same fact.
- **Breaker:** both are Lean theorems, but no theorem links them. `eta_neg` is about a finite spectrum; `chiral_31` is about integer congruence of Seifert forms. The bridge file proves that the Alexander polynomials agree (`alex31_eq_seifert`), which is weaker.
- **Still open:** show that the LT signature (Seifert form) of the mirror is the negative, and identify it with η of an operator (APS ρ). The first part is classical. The identification on the knot complement for a specified operator is not done.

## 5. Time as "the only curve"

> "okay several things here i feel like we have done you 1 and 2  suggestions several times. also i did not think your response to my last workshare even discussed the biggest questions and ideas in the work worth pursuing like time being the only curve"
> (sweep, M085)

- **Strawman:** the odometer coordinate a (spectral flow + drift) is a time coordinate.
- **Breaker:** the circle odometer SF = (a1 − a0) + ½(η1 − η0) is a theorem about a one-parameter family of operators on the circle. Calling the parameter "time" is a MODEL choice. Nothing in the mathematics picks out time, and nothing makes it "the only curve".
- **Still open:** a precise mathematical statement of the idea. Grade: MODEL / ANALOGY.

## 6. Mock theta functions and the "backwards Fresnel lens"

> "or maybe the conjecture is about that mapping knots ,,,mock thetas might help,, its in the memory im sure,,, also why not look at it like a fresnal lens but baswards"
> (`/workspace/ink/old_chats/dirac_builds/chat4_T043_45_57.txt`, line 3, Chat #4 T043)

- **What is exact:** the BHL objects are false/partial theta series. The quantum-modular structure is cited (Lawrence–Zagier; Zwegers for mock theta functions).
- **Breaker:** no shadow computation was done for φ0 or M, and "Fresnel lens backwards" has no mathematical statement.
- **Still open:** compute the (quantum-)modular completion of φ0 − M and say what its shadow is. Grade: ANALOGY.

## 7. Atomic shells 2k² from torus lattice counts (B11)

> "i am not sure which one is right or wrong is the math truly diffrent look at these two response choices which would you chose or is there a third ----Response 1"
> (`/workspace/ink/old_chats/aps_recovery/chat1_96041d3b_T015_User.md`, line 3, Chat #1 T015)

- **Strawman:** the T² lattice ring counts give shell capacities 2k².
- **Breaker:** the ring counts on the torus and on the L¹ ball are 2k + 1 and 4k. Only the sums Σ_{j<k} 2(2j+1) = 2k² give 2k², and that is arithmetic (verify script: "shell sums 2n²"). **[v3]** The sum identity is now a Lean theorem, `D28.shell_sum`: `∑ l ∈ range n, 2(2l+1) = 2n²`. Nothing in the torus geometry derives the electron shell structure.
- **Still open:** nothing to rescue mathematically beyond the sum identity. Physical claim: BROKEN.

## 8. The electron as its own "bubble" that phase-locks

> "okay not do a big steer but to fyt a drone way above our current position and see we wanted to keep the dirac center and explore his idea of the electron,,,,now from this height what i see maybe a little crazy but if even the electron is its own bubble / onion or layer it is cut off from everyother electron and they all think they are the center as well but because they are on the same swing they must phase lock and be the same"
> (sweep, M029)

- **Breaker:** there is no operator, state space or coupling in which "phase lock" is a theorem. The chiral pairing result (η = 0 for every flat-torus build, N9–N10) says the old builds see no asymmetry at all, so there is nothing to lock.
- **Still open:** an idea, not a claim. Grade: ANALOGY.

## 9. Count Me as One's own open remark (Part I, Remark rem:open)

Jeromie has no verbatim question tied to this item in the recovered chats. The governing instruction is:

> "we need to be thorough here we need integrity so no cargo cult sciences ,,,do all three we need to be sure and question ourselves always"
> (sweep, M015)

- **Open, from CMaO:** why the real-shaped branch of the symmetric gluing slice lands on the Alexander roots. The conjecture is that it comes from reducible non-abelian representations at M² a root of Δ_{4_1}. Untested.
- **D28 adds:** the 4_1 has no LT wall on the unit circle because its Alexander roots are the golden branch squared (real, φ^{±2}). This is consistent with the conjecture but does not test it.

## 10. B6: source line not located

> "we need to be thorough here we need integrity so no cargo cult sciences ,,,do all three we need to be sure and question ourselves always"
> (sweep, M015)

- The claim "trefoil η = 0 for all k" was listed as a broken claim from the old chats. The closest located text is "η ≈ 0 (trivial holonomy)". The exact sentence was not found in the recovered files, so B6 is graded BROKEN against its closest located text only.
- **Breaker (for the mathematical content):** the twisted signature of T(2,3) is −2 on (1/6, 5/6) and 0 outside (verify script), so a U(1)-twisted ρ is not identically zero.
