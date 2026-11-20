#!/usr/bin/env python3
# SCRIPT: FIG8-RELATIONS-BUILD-01
# Writes RELATIONS.json: every theorem is a node with its rule tags; every connection is a typed
# edge naming the theorem that WITNESSES it (proved here) or the external source it rests on.
import json, pathlib
ROOT = pathlib.Path(__file__).resolve().parents[1]
P = "FigureEightAnchors."
AP = P+"APoly."
E, G, R, C, M, L = P+"Eis.", P+"Gluing.", P+"Riley.", P+"Chirality.", P+"Monodromy.", P+"Ladder."
rules = {
 "rule1": "anchor broken examples to established math (Thurston, Riley, Seifert, minimal genus-one torus)",
 "rule2": "keep raw differences as a ruler or weight instead of renormalising them away",
 "rule3": "preserve the chiral source of asymmetry",
}
nodes = {}
def n(name, *tags): nodes[name] = {"rules": list(tags)}
for x in ["w_shape","w_cubed","w_sixth","w_not_real","mul_comm'","mul_assoc'","norm_mul","mul_conj","four_norm"]: n(E+x,"rule1")
for x in ["edge_symmetric_factor","regular_solves_edge","regular_half","regular_cubed","regular_cycle_fixed","cycle_fixed_regular","eis_edge","eis_half","eis_cycle_fixed","no_integer_regular"]: n(G+x,"rule1")
for x in ["golden_solves_edge","golden_cycle","no_integer_golden"]: n(G+x,"rule1","rule2")
n(G+"eis_edge_conj","rule1","rule3")
for x in ["A_inv","B_inv","A_parabolic","B_parabolic","relation_of_shape","shape_of_relation","riley_iff_shape","trace_ab","trace_commutator"]: n(R+x,"rule1")
n(R+"relation_defect","rule1","rule2")
for x in ["alex_41","alex_31","det_41","det_31","det_congr","P41_unimodular","S41_indefinite"]: n(C+x,"rule1")
for x in ["amphichiral_41"]: n(C+x,"rule1","rule3")
for x in ["S31_neg_definite","S31_form","chiral_31","chiral_31_basic"]: n(C+x,"rule1","rule3")
for x in ["V41_inv","V31_inv","h41_cat","h31_form","h41_hyperbolic","h41_charpoly"]: n(M+x,"rule1")
for x in ["h31_elliptic","h31_charpoly","h31_cubed","h31_order6"]: n(M+x,"rule1","rule3")
for x in ["h41_trace5","h41_not_periodic"]: n(M+x,"rule1","rule2")
for x in ["ladder_law","fig8_ladder","sqrt2_ladder","catalan_contains_apery","antipalindromic_rest","apery_middle","pell_34","band_edge_merge","regular_squared"]: n(L+x,"rule1")
for x in ["golden_squared","fig8_fifth","saddle_unit"]: n(L+x,"rule1","rule2")
n(L+"trefoil_ladder","rule1","rule3")
for x in ["A_expanded","disc_split","plus_factor","minus_factor","slice_plus","slice_minus","node_at_one"]: n(AP+x,"rule1")
n(AP+"palindromic","rule1","rule3")
n(AP+"golden_ramifies","rule1","rule2")
n(AP+"regular_ramifies","rule1")
external = {
 "X:Thurston": "W. P. Thurston, Geometry and Topology of Three-Manifolds, ch. 4: figure-eight complement from two regular ideal tetrahedra.",
 "X:Riley": "R. Riley 1975, parabolic representation of the figure-eight knot group over Z[w].",
 "X:Q1": "Ramanujan Challenge Q1 (pi PCF): convergence ratio (123+55 sqrt5)/2 = phi^10, saddle in Q(sqrt5) (official Lemma 5; checked in his ladder-paper notes).",
 "X:Apery": "Apery zeta(3) recurrence, limiting polynomial l^2 - 34 l + 1, roots (sqrt2 -+ 1)^4.",
 "X:Catalan2.5": "Problem 2.5 (Catalan G), limiting polynomial (l-1)(l^2-34l+1) (official Lemma 17).",
 "X:Saddle": "Shared saddle quadratic t^2+2t-1=0 of Beukers' Apery integrand and Problem 2.5 (his ladder paper, T = 34 closed 2026-08-31).",
 "X:ramanujan-challenge-lean": "dicipler-pixel/ramanujan-challenge-lean (153 theorems, Problem 2.1 closed).",
 "X:Hessian-July":"His July 13 2026 paper on the figure-eight A-polynomial (rebuilt 8 Aug as 'Axis-Aligned Tangent Cones at the Singular Points of the Figure-Eight A-Polynomial, and the Amphichiral Involution'): corrected discriminant, ramification vs nodes, palindromic involution = amphichirality.",
 "X:Borot-Eynard": "Borot and Eynard, arXiv:1205.2261: for 4_1 the involution (m,l) -> (m,1/l) coincides with the amphichiral symmetry; ramification points at m^2 = (3 +- sqrt5)/2, l = 1 and m^2 = (-1 +- i sqrt3)/2, l = -1.",
 "X:votkp-chiral-vortex": "votkp-lean old-Grok-chats salvage: 'chiral vortex knot of memory' = the VOTKP electron chain (section F).",
}
edges = []
def e(a, b, kind, witness, note):
    edges.append({"from": a, "to": b, "kind": kind, "witness": witness, "note": note})
# Thurston <-> Riley: one polynomial
e(G+"cycle_fixed_regular", R+"riley_iff_shape", "same-polynomial", R+"riley_iff_shape",
  "Regular-tetrahedron shape (fixed by z -> 1/(1-z)) and Riley parameter obey the same z^2 - z + 1 = 0: geometry and group meet at exp(i pi/3).")
e(G+"regular_cycle_fixed", G+"cycle_fixed_regular", "converse", G+"cycle_fixed_regular", "Regular <=> cycle-fixed, both directions.")
e(R+"relation_of_shape", R+"shape_of_relation", "converse", R+"riley_iff_shape", "Riley relation <=> shape polynomial.")
e(G+"edge_symmetric_factor", G+"eis_edge", "evaluates-in", G+"eis_edge", "General-ring factorisation evaluated at w in Z[w].")
e(G+"regular_cubed", E+"w_cubed", "same-root", E+"w_cubed", "Abstract regular root has z^3 = -1; w in Z[w] realises it.")
e(G+"eis_edge", G+"eis_edge_conj", "mirror", G+"eis_edge_conj", "exp(+i pi/3) and exp(-i pi/3): the two orientations of the same hyperbolic structure.")
e(X:="X:Thurston", G+"edge_symmetric_factor", "anchor", G+"edge_symmetric_factor", "Thurston's edge equation, symmetric slice.")
e("X:Riley", R+"riley_iff_shape", "anchor", R+"riley_iff_shape", "Riley's representation, relation <=> c^2-c+1=0.")
# Rule 2: kept differences
e(G+"golden_solves_edge", G+"golden_cycle", "kept-difference", G+"golden_cycle",
  "Golden branch solves the bare edge equation but the cycle gives -1 not +1: that sign is the ruler separating the branches.")
e(R+"relation_defect", R+"riley_iff_shape", "kept-difference", R+"relation_defect",
  "The relation's failure is exactly [[0,p],[-cp,0]], p = c^2-c+1: the defect is measured, not discarded.")
e(G+"golden_solves_edge", L+"golden_squared", "square-of", L+"golden_squared",
  "The discarded (flat) branch squared is the figure-eight monodromy polynomial: the broken example is a ruler for the hyperbolic stretch.")
e(L+"golden_squared", M+"h41_charpoly", "same-polynomial", M+"h41_charpoly", "w^2 - 3w + 1 = 0 is h41's Cayley-Hamilton polynomial.")
# Chirality / monodromy
e(C+"alex_31", M+"h31_charpoly", "same-polynomial", M+"h31_charpoly", "Trefoil Alexander polynomial = monodromy polynomial t^2 - t + 1.")
e(M+"h31_charpoly", G+"cycle_fixed_regular", "same-polynomial", M+"h31_charpoly",
  "THE CROSS-LINK: the chiral trefoil's monodromy satisfies the regular-tetrahedron polynomial that builds the amphichiral figure-eight's geometry.")
e(M+"h31_order6", E+"w_sixth", "same-root", M+"h31_order6", "Trefoil monodromy has order 6, like w = exp(i pi/3).")
e(C+"alex_41", M+"h41_charpoly", "same-polynomial", M+"h41_charpoly", "Figure-eight Alexander polynomial = monodromy (cat map) polynomial t^2 - 3t + 1.")
e(C+"amphichiral_41", C+"chiral_31", "contrast", C+"chiral_31", "4_1 is its own mirror; 3_1 provably is not: the asymmetry source survives.")
e(C+"chiral_31", M+"h31_elliptic", "contrast", M+"h41_hyperbolic", "Chiral trefoil: elliptic monodromy (band, T=1). Amphichiral figure-eight: hyperbolic (gap, T=3).")
e(C+"S31_form", C+"chiral_31", "proof-step", C+"chiral_31", "Negative definiteness is what blocks the mirror.")
e(M+"V41_inv", M+"h41_cat", "proof-step", M+"h41_cat", "h = V^-1 V^T needs the inverse.")
e(M+"V31_inv", M+"h31_form", "proof-step", M+"h31_form", "h = V^-1 V^T needs the inverse.")
# Ladder
e(L+"ladder_law", L+"trefoil_ladder", "ladder-step", L+"trefoil_ladder", "T = 1: periodic, period 6.")
e(L+"ladder_law", L+"fig8_ladder", "ladder-step", L+"fig8_ladder", "T = 3: Q(sqrt5).")
e(L+"ladder_law", L+"sqrt2_ladder", "ladder-step", L+"sqrt2_ladder", "T = 6 -> 34: Q(sqrt2).")
e(M+"h41_trace5", L+"fig8_ladder", "same-value", L+"fig8_ladder", "trace(h41^5) = 123 = rung 5 of the T=3 ladder.")
e(L+"fig8_fifth", "X:Q1", "external", L+"fig8_fifth", "123 = phi^10 + phi^-10 = Q1's ratio trace (ratio recorded in his ladder-paper notes, not re-derived here).")
e(L+"saddle_unit", "X:Saddle", "external", L+"saddle_unit", "Saddle root sqrt2-1: fourth power and its reciprocal are the Apery/Catalan rails; their sum is 34.")
e(L+"sqrt2_ladder", L+"saddle_unit", "same-value", L+"saddle_unit", "Rung 2 of the T=6 ladder = 34 = t^4 + t^-4.")
e(L+"catalan_contains_apery", "X:Catalan2.5", "external", L+"catalan_contains_apery", "Official Lemma 17 polynomial factors through Apery's.")
e(L+"catalan_contains_apery", "X:Apery", "external", L+"catalan_contains_apery", "Apery's l^2-34l+1 sits inside Catalan's cubic.")
e(L+"antipalindromic_rest", L+"catalan_contains_apery", "generalizes", L+"antipalindromic_rest", "The rest mode l=1 is forced by odd degree + anti-palindrome (a = 35).")
e(L+"apery_middle", "X:Apery", "external", L+"apery_middle", "34n^3+51n^2+27n+5 = (2n+1)(17n^2+17n+5): sec psi = 17.")
e(L+"pell_34", L+"sqrt2_ladder", "same-value", L+"pell_34", "17^2 - 2*12^2 = 1 and 2*17 = 34.")
e(L+"band_edge_merge", L+"ladder_law", "boundary", L+"band_edge_merge", "|T| = 2: the rails merge (exceptional point), between the trefoil band T=1 and the figure-eight gap T=3.")
e(L+"regular_squared", G+"regular_cubed", "square-of", L+"regular_squared", "Regular root squared is a primitive cube root of unity.")
e(R+"trace_ab", L+"ladder_law", "analogy-only", R+"trace_ab",
  "tr(ab) = 2 + c places the Riley pair off the band edge; a structural pointer only, no theorem joins them.")
e(C+"chiral_31", "X:votkp-chiral-vortex", "external", C+"chiral_31",
  "The chiral anchor proved here is the established-math counterpart for his 'chiral vortex knot' asymmetry source; the identification itself is his reading, not proved here.")
e(E+"w_sixth", "X:ramanujan-challenge-lean", "external", E+"w_sixth", "Eisenstein ring is the coefficient ring of Riley's representation; repos linked, no shared Lean import.")

# Remaining connections (every theorem must carry at least one edge)
e(C+"P41_unimodular", C+"amphichiral_41", "proof-step", C+"amphichiral_41", "The mirror certificate is an honest change of basis (det -1).")
e(C+"det_congr", C+"amphichiral_41", "proof-step", C+"det_congr", "Congruence scales det(S) by det(P)^2 = 1: the determinant is a mirror invariant.")
e(C+"det_41", C+"alex_41", "same-value", C+"det_41", "Knot determinant 5 = |Delta_41(-1)| = |-1 - 3 - 1|.")
e(C+"det_31", C+"alex_31", "same-value", C+"det_31", "Knot determinant 3 = |Delta_31(-1)| = |1 + 1 + 1|.")
e(C+"S41_indefinite", C+"S31_neg_definite", "contrast", C+"S31_neg_definite", "Signature 0 (amphichiral allowed) vs -2 (mirror forbidden).")
e(C+"S31_neg_definite", C+"S31_form", "generalizes", C+"S31_form", "Leading-minor test vs the explicit form on every nonzero integer vector.")
e(C+"chiral_31", C+"chiral_31_basic", "proof-step", C+"chiral_31_basic", "Seifert-matrix form of the chirality obstruction.")
e(E+"w_shape", G+"cycle_fixed_regular", "same-polynomial", E+"w_shape", "w^2 - w + 1 = 0 is the regular-tetrahedron polynomial in Z[w].")
e(E+"w_shape", E+"w_cubed", "proof-step", E+"w_cubed", "Shape equation gives w^3 = -1.")
e(E+"w_cubed", E+"w_sixth", "square-of", E+"w_sixth", "(w^3)^2 = 1.")
e(E+"w_not_real", G+"no_integer_regular", "same-root", G+"no_integer_regular", "The regular root is not real, so no integer solves z^2 - z + 1 = 0.")
e(E+"mul_comm'", E+"norm_mul", "proof-step", E+"norm_mul", "Ring laws of Z[w] behind the norm identities.")
e(E+"mul_assoc'", E+"norm_mul", "proof-step", E+"norm_mul", "Ring laws of Z[w] behind the norm identities.")
e(E+"mul_conj", E+"norm_mul", "proof-step", E+"mul_conj", "N(x) = x * conj(x): the norm is a squared modulus.")
e(E+"four_norm", E+"mul_conj", "kept-difference", E+"four_norm", "4N = (2a+b)^2 + 3b^2: the 3 is the discriminant |-3| of z^2 - z + 1, kept explicit.")
e(G+"eis_half", G+"regular_half", "evaluates-in", G+"eis_half", "Each tetrahedron contributes -1, evaluated at w.")
e(G+"eis_cycle_fixed", G+"regular_cycle_fixed", "evaluates-in", G+"eis_cycle_fixed", "Cycle-fixed shape, evaluated at w.")
e(G+"regular_half", G+"regular_solves_edge", "proof-step", G+"regular_solves_edge", "(-1)(-1) = 1: two regular tetrahedra close the edge.")
e(G+"regular_solves_edge", G+"golden_solves_edge", "contrast", G+"golden_solves_edge", "Both factors solve the bare edge equation; only the regular one is cycle-fixed.")
e(G+"no_integer_regular", G+"no_integer_golden", "contrast", G+"no_integer_golden", "Neither branch has an integer shape (discriminants -3 and 5).")
e(G+"no_integer_golden", M+"h41_not_periodic", "kept-difference", M+"h41_not_periodic", "Golden roots are irrational units; the cat map never returns to I.")
e(M+"h31_cubed", M+"h31_order6", "square-of", M+"h31_order6", "(h^3)^2 = (-I)^2 = I.")
e(M+"h41_hyperbolic", L+"band_edge_merge", "boundary", M+"h41_hyperbolic", "T = 3 > 2: gap side of the band edge.")
e(R+"A_inv", R+"relation_defect", "proof-step", R+"A_inv", "a^-1 is needed to form the word w.")
e(R+"B_inv", R+"relation_defect", "proof-step", R+"B_inv", "b^-1 is needed to form the word w.")
e(R+"A_parabolic", L+"band_edge_merge", "boundary", R+"A_parabolic", "Meridians sit exactly at trace 2: the parabolic band edge, cusp of the hyperbolic structure.")
e(R+"B_parabolic", R+"A_parabolic", "mirror", R+"B_parabolic", "Upper and lower parabolic meridians.")
e(R+"trace_commutator", R+"trace_ab", "proof-step", R+"trace_commutator", "Peripheral trace data of the Riley pair.")
# A-polynomial
e(AP+"A_expanded", AP+"palindromic", "proof-step", AP+"palindromic", "Coefficients a, b, a: the polynomial reads the same forwards and backwards in L.")
e(AP+"palindromic", C+"amphichiral_41", "same-root", AP+"palindromic", "L -> 1/L on the character curve is the amphichiral symmetry; the Seifert certificate is the same symmetry seen on the surface.")
e(AP+"palindromic", "X:Borot-Eynard", "external", AP+"palindromic", "Involution = amphichiral symmetry (Borot-Eynard).")
e(AP+"disc_split", AP+"plus_factor", "proof-step", AP+"plus_factor", "Discriminant = (b+2a)(b-2a).")
e(AP+"disc_split", AP+"minus_factor", "proof-step", AP+"minus_factor", "Discriminant = (b+2a)(b-2a).")
e(AP+"plus_factor", L+"golden_squared", "same-polynomial", AP+"plus_factor", "The L=+1 ramification factor x^2 - 3x + 1 is the golden branch squared.")
e(AP+"minus_factor", L+"regular_squared", "same-polynomial", AP+"minus_factor", "The L=-1 ramification factor x^2 + x + 1 is the regular branch squared.")
e(AP+"plus_factor", M+"h41_charpoly", "same-polynomial", AP+"plus_factor", "Same x^2 - 3x + 1 as the figure-eight monodromy (cat map).")
e(AP+"slice_plus", AP+"golden_ramifies", "proof-step", AP+"golden_ramifies", "On L = 1, A and dA/dL both equal b + 2a.")
e(AP+"slice_minus", AP+"regular_ramifies", "proof-step", AP+"regular_ramifies", "On L = -1, A and dA/dL are +-(b - 2a).")
e(G+"golden_solves_edge", AP+"golden_ramifies", "kept-difference", AP+"golden_ramifies",
  "THE THROWN-AWAY BRANCH IS A BRANCH POINT: the golden shape, used as a meridian eigenvalue, is exactly a ramification point of the A-polynomial at L = +1.")
e(G+"regular_solves_edge", AP+"regular_ramifies", "same-root", AP+"regular_ramifies",
  "The regular shape, used as a meridian eigenvalue, is exactly a ramification point at L = -1.")
e(AP+"golden_ramifies", AP+"regular_ramifies", "mirror", AP+"regular_ramifies", "The two shape branches ramify on the two fixed slices L = +1 and L = -1 of the involution.")
e(AP+"node_at_one", AP+"golden_ramifies", "contrast", AP+"node_at_one", "Double factors (x -+ 1)^2 are nodes; simple factors are ramification points.")
e(AP+"golden_ramifies", "X:Hessian-July", "external", AP+"golden_ramifies", "Recovers his July paper's corrected discriminant and reads its ramification factors as the squared shape branches.")
e(AP+"node_at_one", "X:Hessian-July", "external", AP+"node_at_one", "The nodes his July paper shows have axis-aligned tangent cones.")
# ---------------------------------------------------------------------------------------------
# Combined project (D29): D25 (chiral eta, Alexander walls on S^1, circle odometer), D27 (BHL 2010
# q-series benchmark) and CMaOBridge. Same conventions: every theorem is a node with rule tags,
# every edge names an audited witness theorem. Hand-written semantic edges first; then every new
# theorem still without an edge gets ONE proof-step edge read from the Lean source (the first new
# theorem whose proof cites it, else the first new theorem its own proof cites), so each such edge
# is witnessed by the theorem whose proof text contains the citation.
import re as _re
D, BH, BR = "DiracTimeD25.", "DiracTimeD25.BHL.", "DiracTimeD25.Bridge."
NEW_SRC = [(D, "DiracTimeD25/ChiralEta.lean"), (D, "DiracTimeD25/AlexanderWall.lean"),
           (D, "DiracTimeD25/CircleOdometer.lean"), (BH, "DiracTimeD25/BhlBoundaryTest.lean"),
           (BR, "CMaOBridge.lean"), ("D28.", "D28/Easy.lean"), ("D28.", "D28/Algebra.lean"), ("D28.", "D28/RawDiff.lean"), ("D28.", "D28/FastModel.lean"), ("D28.", "D28/RawDiffPos.lean"), ("D28.", "D28/FastPsi.lean"), ("D28.", "D28/Qq2Table.lean"), ("D28.", "D28/Eq15.lean"), ("D28.", "D28/Eq17.lean")]
_THM = _re.compile(r"^theorem\s+([^\s:({\[]+)", _re.M)
blocks = []
for pre, path in NEW_SRC:
    code = (ROOT / path).read_text()
    code = _re.sub(r"/-.*?-/", "", code, flags=_re.S); code = _re.sub(r"--.*", "", code)
    ms = list(_THM.finditer(code))
    for i, mt in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(code)
        blocks.append((pre + mt.group(1), mt.group(1), code[mt.end():end], path))
chiral3 = {"eta_neg", "charpoly_neg_eq", "eta_eq_zero_of_anticommute", "eta_eq_zero_of_chiral",
           "eta_eq_zero_of_unitary_conj", "eta_eq_zero_of_unitary_chiral", "pauliSymbol_isHermitian",
           "σ₃_mul_self", "σ₃_pauliSymbol_σ₃", "pauli_eta_eq_zero"}
wall3 = {"alex31_circle", "cos_two_pi_eq_half_iff", "alex31_circle_eq_zero_iff", "alex31_circle_eq_zero_iff'",
         "alex31_poly_circle_eq_zero_iff", "alex31_wall_at_sixth"}
odo2 = {"odometer_identity", "card_crossings_eq_odometer", "etaCircle_of_not_int", "etaCircle_intCast",
        "etaCircle_add_one", "etaCircle_quarter"}
bhl2 = {"coeff_one_phi0", "coeff_one_bhlM", "phi0_ne_bhlM", "rep17_phi0_sub_bhlM"}
for full, short_, _, path in blocks:
    tags = ["rule1"]
    if path.endswith("ChiralEta.lean") and short_ in chiral3: tags.append("rule3")
    if path.endswith("AlexanderWall.lean") and short_ in wall3: tags.append("rule3")
    if path.endswith("CircleOdometer.lean") and short_ in odo2: tags.append("rule2")
    if path.endswith("BhlBoundaryTest.lean") and short_ in bhl2: tags.append("rule2")
    if path == "CMaOBridge.lean" and short_.startswith("wall_"): tags.append("rule3")
    n(full, *tags)
external.update({
 "X:DT-audit": "Ink, dirac_builds_audit_v1 (Dirac Time / VOTKP old-chats pipeline): the three exact DT-O14 survivors -- chiral eta killing law, Alexander wall criterion on S^1, circle odometer DT-E15.",
 "X:BHL2010": "K. Bringmann, K. Hikami, J. Lovejoy, 'On the modularity of the unified WRT invariants of certain Seifert manifolds' (M(2,3,8), M(2,3,4) from +-2 surgery on the trefoil), Thms 1.1-1.2, Eqs. (1.3)-(1.7).",
 "X:APS": "Atiyah-Patodi-Singer spectral asymmetry: eta(D) = signed eigenvalue count; finite-dimensional version formalized here.",
})
# ChiralEta
e(D+"charpoly_neg_eq", D+"eta_neg", "mirror", D+"eta_neg", "Orientation reversal D -> -D negates every eigenvalue, so eta(-D) = -eta(D).")
e(D+"eta_eq_card_sub_card", D+"eta_eq_roots", "same-value", D+"eta_eq_card_sub_card", "eta as #positive - #negative eigenvalues equals the signed count of charpoly roots: one integer, two constructions.")
e(D+"eta_eq_zero_of_chiral", D+"eta_one", "contrast", D+"eta_one", "A chiral D (Gamma D Gamma = -D) is killed, eta = 0; the identity has eta = n: the killing law is not vacuous.")
e(D+"eta_eq_zero_of_chiral", D+"eta_eq_zero_of_unitary_chiral", "generalizes", D+"eta_eq_zero_of_unitary_chiral", "Unitary chiral grading is a special case of the involutive one.")
e(D+"eta_eq_zero_of_chiral", D+"pauli_eta_eq_zero", "evaluates-in", D+"pauli_eta_eq_zero", "Killing law evaluated at the 2x2 Pauli symbol with Gamma = sigma_3.")
e(D+"eta_eq_zero_of_chiral", "X:APS", "anchor", D+"eta_eq_zero_of_chiral", "Spectral asymmetry vanishes under a chiral grading (finite-dimensional APS eta).")
e(D+"eta_eq_zero_of_chiral", "X:DT-audit", "external", D+"eta_eq_zero_of_chiral", "DT-O14 survivor 1 (killing law and sign flip).")
e(D+"eta_neg", C+"chiral_31", "analogy-only", D+"eta_neg", "Both are orientation-sign statements (spectral eta flips under D -> -D; the trefoil Seifert form is not congruent to its mirror). NO Lean theorem links them.")
# AlexanderWall + Bridge
e(D+"alex31_circle_eq_zero_iff", D+"alex41_circle_ne_zero", "contrast", D+"alex41_circle_ne_zero", "The chiral trefoil has walls on S^1 at alpha = +-1/6 (mod 1); the amphichiral figure-eight has none, Delta_41 = 3 - 2cos >= 1.")
e(D+"one_le_alex41_real", D+"alex41_circle", "boundary", D+"one_le_alex41_real", "Delta_41 on S^1 never drops below 1: the figure-eight stays strictly off the wall.")
e(D+"alex31_circle_eq_zero_iff", "X:DT-audit", "external", D+"alex31_circle_eq_zero_iff", "DT-O14 survivor 2 (Alexander wall criterion).")
e(D+"alex31_poly", C+"alex_31", "same-polynomial", BR+"alex31_eq_seifert", "D25's t*Delta_31(t) = t^2 - t + 1 is CMaO's Seifert-matrix polynomial alex V31 = (1, -1, 1).")
e(D+"alex41_poly", C+"alex_41", "same-polynomial", BR+"alex41_eq_seifert", "D25's t*Delta_41(t) = -t^2 + 3t - 1 is CMaO's alex V41 = (-1, 3, -1).")
e(G+"regular_solves_edge", BR+"wall_solves_edge", "evaluates-in", BR+"wall_solves_edge", "CMaO's ring-generic edge theorem evaluated in C at every trefoil wall on S^1.")
e(G+"regular_half", BR+"wall_half", "evaluates-in", BR+"wall_half", "Each tetrahedron contributes -1 at a trefoil wall.")
e(G+"regular_cubed", BR+"wall_cubed", "evaluates-in", BR+"wall_cubed", "A trefoil wall is a sixth root of unity, z^3 = -1.")
e(BR+"wall_cubed", E+"w_cubed", "same-root", BR+"wall_cubed", "The S^1 walls of the trefoil satisfy w^3 = -1 like the Eisenstein root w = exp(i pi/3).")
e(D+"alex31_wall_at_sixth", BR+"sixth_solves_edge", "same-root", BR+"sixth_solves_edge", "The wall at alpha = 1/6 is Thurston's regular shape exp(i pi/3).")
e(D+"alex31_poly", BR+"wall_regular_poly", "proof-step", BR+"wall_regular_poly", "A wall Delta_31 = 0 gives z^2 - z + 1 = 0 via t*Delta_31(t) = t^2 - t + 1.")
# CircleOdometer
e(D+"odometer_identity", D+"etaCircle_quarter", "kept-difference", D+"etaCircle_quarter", "The eta boundary term is kept, and is nonzero (1/2 at a = 1/4).")
e(D+"etaCircle_add_one", D+"floor_add_one_sub_floor", "contrast", D+"floor_add_one_sub_floor", "eta is 1-periodic while the floor count jumps by exactly 1: windings counted, boundary measured.")
e(D+"odometer_identity", "X:DT-audit", "external", D+"odometer_identity", "DT-E15 circle-odometer identity (DT-O14 survivor 3).")
# BHL
e(BH+"coeff_one_phi0", BH+"coeff_one_bhlM", "kept-difference", BH+"phi0_ne_bhlM", "Signed boundary: coeff_q1 phi0 = 2 vs coeff_q1 M = 1, so phi0 - M is a kept, nonzero difference.")
e(BH+"rep17_phi0_sub_bhlM", BH+"phi0_ne_bhlM", "kept-difference", BH+"rep17_phi0_sub_bhlM", "Raw difference phi0 - M tabulated exactly through q^16.")
e(BH+"eq15_iff_coeff", BH+"eq15_mod_q49", "proof-step", BH+"eq15_reduced_le23", "All-degree parity reduction of Eq. (1.5), then exact check through q^48.")
e(BH+"eq15_mod_q49", "X:BHL2010", "anchor", BH+"eq15_mod_q49", "BHL Eq. (1.5) 2q^2 phi0(q^2) = psi(q) + psi(-q), exact through q^48.")
e(BH+"eq17_mod_q49", "X:BHL2010", "anchor", BH+"eq17_mod_q49", "BHL Eq. (1.7) 2 + 2q^2 M(q) = (-q)_inf + false theta, exact through q^48.")
e(BH+"phi0_ne_bhlM", "X:BHL2010", "external", BH+"phi0_ne_bhlM", "Strict separation of the two BHL q-series at q^1; the WRT Laplace-transform link (Eqs. 2.1-2.6) is NOT formalized.")
# D28 (new_lean_statements_v1)
Q = "D28."
external.update({"X:D28-statements": "Ink, D28 new_lean_statements_v1: exact claims of combined_paper_v1.tex not previously proved in Lean."})
e(Q+"dirac_cmao_LM6", "X:D28-statements", "external", Q+"dirac_cmao_LM6", "N37: Dirac Time L = -M^-6 is CMaO L*M^6 = -1.")
e(Q+"odometer_no_crossing", Q+"odometer_one_crossing", "contrast", Q+"odometer_one_crossing", "N22: no crossing yet Delta eta = -1; one crossing yet Delta eta = 0, so Delta eta != 2 SF.")
e(D+"etaCircle_quarter", Q+"odometer_no_crossing", "proof-step", Q+"odometer_no_crossing", "Uses eta(1/4) = 1/2.")
e(D+"etaCircle_add_one", Q+"etaCircle_five_quarter", "proof-step", Q+"etaCircle_five_quarter", "eta is 1-periodic: eta(5/4) = eta(1/4).")
e(Q+"etaCircle_three_quarter", Q+"odometer_no_crossing", "proof-step", Q+"odometer_no_crossing", "Uses eta(3/4) = -1/2.")
e(Q+"etaCircle_five_quarter", Q+"odometer_one_crossing", "proof-step", Q+"odometer_one_crossing", "Uses eta(5/4) = 1/2.")
e(Q+"moser_fibre_orders", "X:BHL2010", "anchor", Q+"moser_fibre_orders", "N31: +-2 surgery on the trefoil gives exceptional fibre orders 4 and 8 (M(2,3,4), M(2,3,8)).")
e(Q+"moser_fibre_orders", Q+"orbifold_euler", "same-value", Q+"orbifold_euler", "N33: fibre orders 4, 8 give orbifold Euler characteristics 1/12 and -1/24.")
e(Q+"lens_L21", Q+"moser_fibre_orders", "contrast", Q+"lens_L21", "N33: lens control L(2,1), q^2 = -1 mod p.")
e(Q+"shell_sum", "X:D28-statements", "external", Q+"shell_sum", "N41: S^2 shell sum 2n^2.")
e(Q+"golden_pow_ten", "X:Q1", "anchor", Q+"golden_pow_ten", "K16: phi^10 = (123 + 55 sqrt5)/2, the Q1 convergence ratio.")
e(Q+"q1_ratio", Q+"golden_pow_ten", "same-value", Q+"q1_ratio", "K16: the Q1 companion-root ratio (297+135 sqrt5)/(135 sqrt5-297) equals phi^10.")
e(Q+"q1_char_roots", Q+"q1_ratio", "same-root", Q+"q1_char_roots", "K16: the two companion roots (-297 +- 135 sqrt5)/4 whose ratio is phi^10.")
e(Q+"golden_pow_ten", Q+"golden_pow_ten_add_inv", "proof-step", Q+"golden_pow_ten_add_inv", "phi^10 + phi^-10 = 123.")
e(L+"golden_squared", Q+"golden_sq", "same-polynomial", Q+"golden_sq", "phi^2 = phi + 1 in R (CMaO golden ladder).")
e(Q+"alexT34_factor_ring", D+"alex31_poly_circle_eq_zero_iff", "same-polynomial", Q+"alexT34_circle_eq_zero_iff", "N15: Delta_{T(3,4)} = (t^2 - t + 1)(t^4 - t^2 + 1): the trefoil factor carries the walls at +-1/6.")
e(Q+"alexT34_circle_eq_zero_iff", Q+"alexT34_circle_eq_zero_iff_fract", "proof-step", Q+"alexT34_circle_eq_zero_iff_fract", "N15: the six unit-circle walls of 8_19 = T(3,4).")
e(Q+"alexT34_cos", Q+"alexT34_circle_eq_zero_iff", "same-polynomial", Q+"alexT34_cos", "N15: on S^1, z^-3 Delta = 2cos3x - 2cos2x + 1 = (2cos x - 1)(4cos^2 x - 3).")
e(Q+"alexT34_torus_formula", Q+"alexT34_factor", "same-polynomial", Q+"alexT34_factor", "N15: torus-knot formula and its trefoil factorisation of one polynomial.")
e(Q+"lt23_window", D+"alex31_circle_eq_zero_iff", "boundary", Q+"lt23_window", "N16/N17: the trefoil Litherland window jumps exactly at the Alexander walls alpha = 1/6, 5/6.")
e(Q+"lt23_values", Q+"lt34_values", "contrast", Q+"lt34_values", "N16/N17: Litherland counts for T(2,3) and T(3,4).")
e(Q+"lt23_values", "X:D28-statements", "external", Q+"lt23_values", "Litherland 1979: the count equals the Levine-Tristram signature (cited, not formalised).")
e(D+"pauli_eta_eq_zero", Q+"blockPauli_eta_eq_zero", "generalizes", Q+"blockPauli_eta_eq_zero", "N11: the 2x2 killing law extended to any block-diagonal sum of flat-torus symbols.")
e(D+"eta_eq_zero_of_chiral", Q+"blockPauli_eta_eq_zero", "evaluates-in", Q+"blockPauli_eta_eq_zero", "Killing law with Gamma = blockdiag(sigma_3).")
e(Q+"pauliSymbol_det_eq_zero_iff", D+"pauliSymbol_isHermitian", "contrast", Q+"pauliSymbol_det_eq_zero_iff", "N10: zero modes of the flat-torus symbol only at a = b = 0 (codimension two).")
e(Q+"rawDiff_term", BH+"rep17_phi0_sub_bhlM", "kept-difference", Q+"rawDiff_term", "N30: term identity behind the raw difference phi0 - M.")
e(BH+"eq17_mod_q49", Q+"eq17_le128", "generalizes", Q+"eq17_le128", "BHL Eq. (1.7) extended from q^48 to q^128.")
e(Q+"eq17_le128", "X:BHL2010", "anchor", Q+"eq17_le128", "BHL Eq. (1.7) exact through q^128.")
e(BH+"eq15_reduced_le23", Q+"eq15_reduced_le128", "generalizes", Q+"eq15_reduced_le128", "BHL Eq. (1.5) reduced form extended from k <= 23 to k <= 128.")
e(Q+"eq15_reduced_le128", "X:BHL2010", "anchor", Q+"eq15_reduced_le128", "BHL Eq. (1.5) reduced, exact for k <= 128.")
e(Q+"eq15_reduced_le128", Q+"eq15_reduced_le64", "generalizes", Q+"eq15_reduced_le64", "k <= 64 as a corollary of k <= 128.")
e(BH+"eq15_mod_q49", Q+"eq15_mod_q259", "generalizes", Q+"eq15_mod_q259", "BHL Eq. (1.5) unreduced, extended from q^48 to q^258.")
e(Q+"eq15_reduced_le128", Q+"eq15_mod_q259", "proof-step", Q+"eq15_mod_q259", "Reduced form k <= 128 plus all-degree parity lemmas give Eq. (1.5) mod q^259.")
e(Q+"eq15_mod_q259", "X:BHL2010", "anchor", Q+"eq15_mod_q259", "BHL Eq. (1.5) 2q^2 phi0(q^2) = psi(q) + psi(-q), exact through q^258.")
e(Q+"rep_geomInv_mul", Q+"rep_qq2Inv_fast", "proof-step", Q+"rep_qq2Inv_fast", "1/(1-q^a) as the recurrence g_k = f_k + g_(k-a).")
e(BH+"rep17_phi0_sub_bhlM", Q+"phi0_sub_bhlM_pos", "kept-difference", Q+"phi0_sub_bhlM_pos", "N30: the raw difference phi0 - M stays positive through q^128 (was q^16).")
e(Q+"rawDiff_term", Q+"phi0_sub_bhlM_pos", "kept-difference", Q+"phi0_sub_bhlM_pos", "N30: term identity and finite positivity of the same raw difference.")
e(Q+"fNegPoch_eq", Q+"rep_bhlM_fast", "proof-step", Q+"rep_bhlM_fast", "Linear-time model of (-q)_m, proved equal to the D27 model.")
# Coverage: one proof-step edge for each new theorem still without an edge.
_short = {b[1]: b[0] for b in blocks}
def _cites(body, s): return _re.search(r"(?<![\w.'])" + _re.escape(s) + r"(?![\w'])", body) is not None
_touched = {x for ed in edges for x in (ed["from"], ed["to"])}
for full, short_, body, _p in blocks:
    if full in _touched: continue
    citer = next((b for b in blocks if b[0] != full and _cites(b[2], short_)), None)
    if citer:
        e(full, citer[0], "proof-step", citer[0], "Cited in the proof of " + citer[1] + ".")
    else:
        used = next((b for b in blocks if b[0] != full and _cites(body, b[1])), None)
        if used is None: raise SystemExit("no edge available for " + full)
        e(used[0], full, "proof-step", full, "Its proof cites " + used[1] + ".")
    _touched |= {edges[-1]["from"], edges[-1]["to"]}

doc = {"rules": rules, "nodes": nodes, "external": external, "edges": edges,
       "kinds": {
  "same-polynomial": "both sides are governed by one explicit polynomial (proved)",
  "same-root": "the same algebraic root realised in two places (proved)",
  "same-value": "the same integer arises from two constructions (proved)",
  "square-of": "one object is the square of the other (proved)",
  "converse": "the two statements are the two directions of an iff",
  "evaluates-in": "a general-ring identity evaluated at a concrete element",
  "mirror": "orientation reversal",
  "kept-difference": "a defect or sign kept as a measurement (rule 2)",
  "contrast": "two objects differing in a proved invariant",
  "proof-step": "one theorem is used to obtain the other",
  "ladder-step": "a rung of the trace ladder",
  "generalizes": "one statement is a special case of the other",
  "boundary": "marks the band edge between regimes",
  "anchor": "ties a theorem to a named classical source",
  "external": "links to his other work or the literature; the link is recorded, not proved here",
  "analogy-only": "structural pointer with NO theorem behind it -- flagged so it is never cited as proved"}}
(ROOT / "RELATIONS.json").write_text(json.dumps(doc, indent=1))
print(len(nodes), "nodes,", len(edges), "edges")
