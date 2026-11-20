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
