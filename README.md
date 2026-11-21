# count-me-as-one-lean

**Jeromie Beasley**

The Lean home of **Count Me as One**: the figure-eight knot, the trefoil's turn and one trace ladder, joined to the Dirac anchor (APS rulers, the chiral seed and a signed boundary test).

Organised by three working rules:

1. **Anchor broken examples to established math.** Thurston's figure-eight knot complement (two regular ideal tetrahedra), Riley's representation, the genus-one Seifert surfaces.
2. **Keep raw differences as a ruler or weight**, not renormalised away: the golden branch of the gluing equation, the Riley relation defect, the APS difference, the odometer drift term, the boundary difference φ₀ − M.
3. **Preserve the chiral source of asymmetry.** The trefoil's handedness is a proved invariant; the figure-eight is its own mirror image.

One Lake project, one harness (`python3 scripts/verify.py`). Lean `v4.36.0-rc2`, Mathlib `e8ba86fa`.
**280 theorems, 0 sorry / admit / native_decide / custom axioms, 25 false controls, 280-node / 238-edge relations graph.** The GitHub Actions run on every push is the verdict.

| Library | Content | Theorems |
|---|---|---|
| `FigureEightAnchors` | Count Me as One v1: gluing, Riley, monodromy, trace ladder, A-polynomial, chirality. Core Lean only, no Mathlib import, source unchanged from v1 | 80 |
| `DiracTimeD25` | Chiral η, Alexander walls on the circle, the circle odometer; the Bringmann–Hikami–Lovejoy ±2 trefoil-surgery boundary test | 114 |
| `CMaOBridge` | Proofs joining the two: every trefoil wall on the unit circle solves Thurston's edge equation; the Alexander polynomials equal the Seifert-matrix ones | 7 |
| `D28` | Bounded q-series identities (Eq. 1.5 through q²⁵⁸, Eq. 1.7 and positivity of φ₀ − M through q¹²⁸), T(3,4) walls, Litherland counts, odometer drift, shells, the Q1 ratio φ¹⁰ | 79 |

Bounded results are stated as bounded; nothing here is claimed in all degrees unless the theorem says so. Edges of kind `external` or `analogy-only` in `RELATIONS.json` are recorded, not proved.

**Read `RELATIONS.html` first**: the map of how every result connects, rendered from the same `RELATIONS.json` the harness checks.

Release `v1` of this repository is the original 80-theorem core-Lean package (Lean v4.34.1, no Mathlib).

## The paper and the article

| File | What it is |
|---|---|
| [`paper/Count_Me_as_One_Dirac_Anchor_Recovered_v5_1.pdf`](paper/Count_Me_as_One_Dirac_Anchor_Recovered_v5_1.pdf) | **v5.1, current.** Adds the answers of issue #1: exact Lean authorship, the wider search for the old Dirac builds, the DT-O6 pair named and its signature window checked, Dirac Time's trefoil shown to be the right-handed one (the mirror of BHL's), and the -2/+2 sign flip traced to a Seifert-matrix convention. Same paper as a web page: [HTML](paper/Count_Me_as_One_Dirac_Anchor_Recovered_v5_1.html); mixer: [Mixer v5.1](paper/Count_Me_as_One_Dirac_Anchor_Recovered_Mixer_v5_1.html); source: [`paper/v5_1/`](paper/v5_1/); new check: [`checks/sig_flip_check_v1.py`](checks/sig_flip_check_v1.py) |
| [`paper/Count_Me_as_One_Dirac_Anchor_Recovered_v5.pdf`](paper/Count_Me_as_One_Dirac_Anchor_Recovered_v5.pdf) | **Count Me as One, with the Dirac Anchor Recovered** (v5): Part I is Count Me as One; Part II joins it to the APS rulers, the chiral seed and the signed boundary test. Every claim graded; every [T] tag names a theorem in this repository |
| [`paper/Count_Me_as_One_Dirac_Anchor_Recovered_v5.html`](paper/Count_Me_as_One_Dirac_Anchor_Recovered_v5.html) | The same paper as a web page: every formula typeset, the plates, and the full Lean source, harness, CI record and checks script to open in place |
| [`paper/Count_Me_as_One_Dirac_Anchor_Recovered_Mixer_v5.html`](paper/Count_Me_as_One_Dirac_Anchor_Recovered_Mixer_v5.html) | The v5 mixer: 17 live 3D eyes, one per result of Parts I and II, every readout computed live (walls, chiral η, odometer, signatures, the boundary ruler with Eqs. 1.5 and 1.7 checked in exact integers, surgery controls, repairs, grades, the 280-node relation graph) |
| [`paper/v5/`](paper/v5/) | Its source: the .tex, the plates, the record of the GitHub Actions run it cites, and the HTML and mixer source |
| [`checks/cmao_checks_v1.py`](checks/cmao_checks_v1.py) | Re-run of every number in the paper that is not a Lean theorem (exact arithmetic, sympy, mpmath, SnapPy), with its [output](checks/cmao_checks_v1_output.txt) |
| [`film/source/`](film/source/) | The deterministic 3D renderer for the film and every plate (`render_knots.py`, `plates_part2.py`) |
| [`paper/Count_Me_as_One_v1_20261120.pdf`](paper/Count_Me_as_One_v1_20261120.pdf) | Count Me as One v1, the paper of Part I on its own |
| [`paper/Count_Me_as_One_v1_20261120.html`](paper/Count_Me_as_One_v1_20261120.html) | The same as a web page, with the 3D models |
| [`paper/Count_Me_as_One_Mixer_v1_20261120.html`](paper/Count_Me_as_One_Mixer_v1_20261120.html) | The 3D mixer: move the knots and the gluing yourself |
| [`paper/Count_Me_as_One_The_Moving_Knot_v1_20261120.mp4`](paper/Count_Me_as_One_The_Moving_Knot_v1_20261120.mp4) | The film of the moving knot |
| [`article/Tying_the_Knot_v1_20261120.md`](article/Tying_the_Knot_v1_20261120.md) | **Tying the Knot: What Every Culture Binds, and Why**, the public article |

To open the HTML files as pages rather than source, download them and open them in a browser.

## Count Me as One v1: what the core library proves

### Thurston's gluing equation — `FigureEightAnchors/Gluing.lean`
The figure-eight complement is glued from two ideal tetrahedra with shapes z, w satisfying
z(z−1)·w(w−1) = 1.

| Theorem | Statement |
|---|---|
| `edge_symmetric_factor` | On the slice z = w: z²(z−1)² − 1 = (z² − z + 1)(z² − z − 1), in every commutative ring |
| `regular_solves_edge` | Any root of z² − z + 1 solves the edge equation |
| `golden_solves_edge` | Any root of z² − z − 1 **also** solves it — the edge equation alone does not choose the geometry |
| `regular_half` | At the regular root each tetrahedron contributes exactly −1 |
| `regular_cubed` | The regular root has z³ = −1 (sixth root of unity) |
| `regular_cycle_fixed`, `cycle_fixed_regular` | z is fixed by the shape cycle z ↦ 1/(1−z) **if and only if** z² − z + 1 = 0: "regular tetrahedron" exactly |
| `golden_cycle` | On the golden branch the cycle gives −1, not 1 — the kept difference that separates the branches |
| `eis_edge`, `eis_half`, `eis_cycle_fixed` | All of the above evaluated in the Eisenstein integers at z = w = e^{iπ/3} |
| `eis_edge_conj` | The conjugate shape e^{−iπ/3} also solves it: the mirror structure |
| `no_integer_regular`, `no_integer_golden` | No integer shape solves either factor |

### Riley's representation — `FigureEightAnchors/Riley.lean`
Knot group ⟨a, b | w a = b w⟩, w = a⁻¹ b a b⁻¹; a ↦ [[1,1],[0,1]], b ↦ [[1,0],[c,1]].

| Theorem | Statement |
|---|---|
| `relation_defect` | w a − b w = [[0, p], [−c p, 0]] with **p = c² − c + 1**, entry by entry, in every commutative ring |
| `riley_iff_shape` | The relation holds **if and only if** c² − c + 1 = 0 |
| `A_parabolic`, `B_parabolic` | Both meridians have trace 2, determinant 1 |
| `trace_ab`, `trace_commutator` | tr(ab) = 2 + c, tr[a,b] = 2 + c² |

So the Riley parameter and Thurston's tetrahedron shape satisfy **one and the same polynomial**:
the algebraic group picture and the geometric gluing picture meet at e^{iπ/3}. The defect p is
kept as a measured quantity (rule 2), not discarded.

### Chirality — `FigureEightAnchors/Chirality.lean`
Seifert matrices: 4₁ : V = [[1,−1],[0,−1]], 3₁ : V = [[−1,1],[0,−1]].

| Theorem | Statement |
|---|---|
| `alex_41`, `alex_31` | Alexander polynomials −1 + 3t − t² and 1 − t + t² |
| `det_41`, `det_31` | Determinants 5 and 3 |
| `amphichiral_41` | Explicit unimodular P = [[−1,−1],[2,1]] with Pᵀ V P = −Vᵀ: **4₁ is its own mirror** |
| `S31_form` | xᵀ(V+Vᵀ)x < 0 for every nonzero integer vector: the trefoil form is negative definite |
| `chiral_31`, `chiral_31_basic` | **No** unimodular P carries the trefoil's Seifert matrix to its mirror's: the trefoil is chiral |
| `det_congr` | det(Pᵀ S P) = det(P)² det(S) |

### Eisenstein integers — `FigureEightAnchors/Eisenstein.lean`
Z[ω] with ω² = ω − 1: ω³ = −1, ω⁶ = 1, multiplicative norm, norm via conjugate, 4N = (2a+b)² + 3b².

### Monodromy — `FigureEightAnchors/Monodromy.lean`
Fibred-knot monodromy h = V⁻¹Vᵀ from the Seifert matrices.

| Theorem | Statement |
|---|---|
| `h41_cat` | Figure-eight monodromy is the cat map [[2,1],[1,1]] |
| `h31_form` | Trefoil monodromy is [[0,1],[−1,1]] |
| `h41_hyperbolic`, `h31_elliptic` | Traces 3 (gap) and 1 (band), both determinant 1 |
| `h41_charpoly` | h² = 3h − I: characteristic polynomial t² − 3t + 1 = the figure-eight's Alexander polynomial |
| `h31_charpoly` | h² = h − I: **the trefoil's monodromy satisfies the regular-tetrahedron / Riley polynomial z² − z + 1** |
| `h31_cubed`, `h31_order6` | h³ = −I, h⁶ = I: order 6, exactly like ω = e^{iπ/3} |
| `h41_trace5` | trace(h⁵) = 123 = φ¹⁰ + φ⁻¹⁰ |
| `h41_not_periodic` | no return to I in 12 powers |

### Ladder — `FigureEightAnchors/Ladder.lean`
| Theorem | Statement |
|---|---|
| `ladder_law` | In any commutative ring: x + y = T, xy = 1 ⇒ xᵏ + yᵏ = t_k with t_{k+1} = T t_k − t_{k−1} |
| `trefoil_ladder`, `fig8_ladder`, `sqrt2_ladder` | T = 1: 2,1,−1,−2,−1,1,2 (period 6); T = 3: 2,3,7,18,47,123,322; T = 6: 2,6,34,198 |
| `golden_squared` | z² − z − 1 = 0 ⇒ w = z² satisfies w² − 3w + 1 = 0: **the golden branch squared is the figure-eight monodromy** |
| `regular_squared` | z² − z + 1 = 0 ⇒ z² is a primitive cube root of unity |
| `fig8_fifth` | x² − 3x + 1 = 0 ⇒ x⁵ + (3−x)⁵ = 123 (Q1's φ¹⁰) |
| `saddle_unit` | t² + 2t − 1 = 0 ⇒ t⁴(t+2)⁴ = 1 and t⁴ + (t+2)⁴ = 34 (Apéry/Catalan saddle) |
| `catalan_contains_apery` | λ³ − 35λ² + 35λ − 1 = (λ − 1)(λ² − 34λ + 1) |
| `antipalindromic_rest` | λ³ − aλ² + aλ − 1 = (λ − 1)(λ² − (a−1)λ + 1): the rest mode is forced |
| `apery_middle` | 34n³ + 51n² + 27n + 5 = (2n+1)(17n² + 17n + 5) |
| `pell_34` | 17² − 2·12² = 1 and 2·17 = 34 = rung 2 of the T = 6 ladder |
| `band_edge_merge` | x + y = 2, xy = 1 over ℤ forces x = y = 1: the rails merge at the band edge |

### A-polynomial — `FigureEightAnchors/APoly.lean`
A(L, M) = M⁴L² + b(M)L + M⁴, b = −1 + M² + 2M⁴ + M⁶ − M⁸.

| Theorem | Statement |
|---|---|
| `A_expanded` | the standard A-polynomial of 4₁ |
| `palindromic` | L·L′ = 1 ⇒ L²A(L′, M) = A(L, M): the amphichiral involution |
| `disc_split`, `plus_factor`, `minus_factor` | b² − 4a² = (b+2a)(b−2a), b+2a = −(x+1)²(x²−3x+1), b−2a = −(x−1)²(x²+x+1), x = M² |
| `slice_plus`, `slice_minus` | on L = ±1, A and ∂A/∂L reduce to ±(b ± 2a) |
| `golden_ramifies` | z² − z − 1 = 0 ⇒ A(1, z) = 0 and ∂A/∂L(1, z) = 0 |
| `regular_ramifies` | z² − z + 1 = 0 ⇒ A(−1, z) = 0 and ∂A/∂L(−1, z) = 0 |
| `node_at_one` | the node at M = 1, L = −1 |

## Relations — `RELATIONS.json`, `RELATIONS.html`
Every theorem is a node tagged with the rule(s) it serves (rule 1 anchor, rule 2 ruler, rule 3 chiral source).
Every connection is a typed edge (same-polynomial, square-of, kept-difference, contrast, ladder-step, boundary,
external, analogy-only, …) and names the **kernel-checked theorem that witnesses it**. External edges point to his
Ramanujan / Apéry / Catalan work and the literature; those links are recorded, not proved here. One edge is
analogy-only and is labelled so it is never cited as proved.

The harness rejects the build if any theorem is missing from the graph, has no rule tag, or has no edge; if any
edge points at something that is neither an audited theorem nor a declared source; or if any edge's witness is not
an audited theorem. A forged edge is run through the same checker on every build and must be rejected.

## False controls (must be rejected — they are)
| File | False claim | Rejected by |
|---|---|---|
| `TrefoilAmphichiral` | the figure-eight's certificate makes the trefoil its own mirror | `decide` proves it false |
| `GoldenRegular` | a golden root (z = 4 mod 11) is fixed by the shape cycle | `decide` proves it false |
| `RileyAnyParameter` | the Riley relation holds at c = 1 | `decide` proves it false |
| `SameAlexander` | 4₁ and 3₁ share an Alexander polynomial | `decide` proves it false |
| `EdgeAtTwo` | z = w = 2 solves the edge equation | `decide` proves it false |
| `WSquaredReal` | ω² = −1 in Z[ω] | `decide` proves it false |
| `TrefoilHyperbolic` | trefoil monodromy has trace 3 | `decide` proves it false |
| `LadderOffByOne` | trace(h41⁵) = 122 | `decide` proves it false |
| `GoldenSquaredRegular` | golden root squared satisfies w² − w + 1 = 0 (mod 11) | `decide` proves it false |
| `TrefoilAperiodic` | trefoil monodromy cubed is I | `decide` proves it false |
| `GoldenWrongSlice` | a golden shape ramifies on L = −1 (mod 11) | `decide` proves it false |

## The harness — `python3 scripts/verify.py`
1. `lake build` 2. `leanchecker` kernel replay of every module 3. `#print axioms` on every theorem,
allowed set {propext, Classical.choice, Quot.sound} (32 theorems use no axioms at all)
4. source scan for sorry/admit/native_decide/axiom 5. theorem inventory = 80
6. every false control rejected for a mathematical reason 7. SHA-256 of every source file and of RELATIONS.json
8. relations graph complete and every edge witnessed, plus the forged-edge control.
Report: `verification/report.json`.

## Sources
- W. P. Thurston, *The Geometry and Topology of Three-Manifolds*, ch. 4 (gluing equations, figure-eight).
- R. Riley, "A quadratic parabolic group", Math. Proc. Camb. Phil. Soc. 77 (1975).
- Standard Seifert-matrix data for 3₁ and 4₁ (Rolfsen, *Knots and Links*).
- Apéry (1979); Ramanujan Challenge official proofs (Technion, Aug 2026), Lemmas 5 and 17, for the external Q1 / Catalan links.

Licence: code MIT, prose CC BY 4.0.
