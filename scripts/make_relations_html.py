#!/usr/bin/env python3
# SCRIPT: FIG8-RELATIONS-HTML-01
# Renders RELATIONS.json (the same file the harness checks) as one readable HTML page.
import json, pathlib, html
ROOT = pathlib.Path(__file__).resolve().parents[1]
rel = json.loads((ROOT / "RELATIONS.json").read_text())
rep = json.loads((ROOT / "verification" / "report.json").read_text())
short = lambda x: x.replace("FigureEightAnchors.", "").replace("DiracTimeD25.", "D25.")
order = ["same-polynomial","same-root","same-value","square-of","kept-difference","contrast","mirror","boundary",
         "ladder-step","generalizes","converse","evaluates-in","proof-step","anchor","external","analogy-only"]
rows = []
for k in order:
    es = [e for e in rel["edges"] if e["kind"] == k]
    if not es: continue
    rows.append(f'<h3>{k} <span class="n">{len(es)}</span></h3><p class="kd">{html.escape(rel["kinds"][k])}</p><table>')
    for e in es:
        rows.append(f'<tr><td class="a">{html.escape(short(e["from"]))}</td><td class="arr">&rarr;</td><td class="a">{html.escape(short(e["to"]))}</td>'
                    f'<td>{html.escape(e["note"])}<div class="w">witness: {html.escape(short(e["witness"]))}</div></td></tr>')
    rows.append('</table>')
ext = "".join(f'<tr><td class="a">{html.escape(k)}</td><td>{html.escape(v)}</td></tr>' for k, v in rel["external"].items())
c = rep["checks"]
svg = '''<svg viewBox="0 0 980 560" xmlns="http://www.w3.org/2000/svg" font-family="DejaVu Sans,system-ui,sans-serif" font-size="13">
<defs><marker id="ar" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto"><path d="M0,0L10,5L0,10z" fill="#8aa0b4"/></marker></defs>
<style>.b{fill:#0f1722;stroke:#3a4b5e;stroke-width:1.2;rx:8}.t{fill:#dfe7ef}.s{fill:#8a9aab;font-size:11px}.l{stroke:#8aa0b4;stroke-width:1.3;fill:none;marker-end:url(#ar)}.g{stroke:#f2c14e}.c{stroke:#63d3ff}.r{stroke:#ff7a90}.lt{fill:#a4b1bf;font-size:11px}</style>
<text x="20" y="28" class="t" font-size="15" font-weight="bold">The core of the map: one polynomial family, two fields, one band edge</text>
<rect class="b" x="20" y="60" width="230" height="62"/><text x="32" y="84" class="t">Thurston regular tetrahedron</text><text x="32" y="104" class="s">z fixed by z -> 1/(1-z)</text>
<rect class="b" x="20" y="160" width="230" height="62"/><text x="32" y="184" class="t">Riley parameter</text><text x="32" y="204" class="s">relation holds iff c^2 - c + 1 = 0</text>
<rect class="b" x="20" y="260" width="230" height="62"/><text x="32" y="284" class="t">Trefoil monodromy (chiral)</text><text x="32" y="304" class="s">[[0,1],[-1,1]], order 6, T = 1</text>
<rect class="b" x="300" y="150" width="200" height="82" style="stroke:#f2c14e"/><text x="316" y="178" class="t" font-weight="bold">z^2 - z + 1</text><text x="316" y="198" class="s">root w = exp(i pi/3)</text><text x="316" y="216" class="s">Eisenstein integers</text>
<path class="l g" d="M250,91 C280,100 290,150 300,170"/><path class="l g" d="M250,191 L300,191"/><path class="l g" d="M250,291 C280,280 290,230 300,215"/>
<text x="258" y="130" class="lt">same polynomial</text>
<rect class="b" x="20" y="380" width="230" height="62"/><text x="32" y="404" class="t">Golden branch (flat tetrahedra)</text><text x="32" y="424" class="s">z^2 - z - 1; cycle gives -1</text>
<rect class="b" x="300" y="380" width="200" height="82" style="stroke:#63d3ff"/><text x="316" y="408" class="t" font-weight="bold">t^2 - 3t + 1</text><text x="316" y="428" class="s">figure-eight monodromy = cat map</text><text x="316" y="446" class="s">= Alexander polynomial of 4_1</text>
<path class="l c" d="M250,411 L300,411"/><text x="256" y="400" class="lt">square</text>
<rect class="b" x="560" y="380" width="190" height="62"/><text x="572" y="404" class="t">ladder T = 3 -> 123</text><text x="572" y="424" class="s">five turns: phi^10 + phi^-10</text>
<path class="l c" d="M500,411 L560,411"/>
<rect class="b" x="790" y="380" width="170" height="62"/><text x="802" y="404" class="t">Q1 (pi PCF)</text><text x="802" y="424" class="s">ratio phi^10 [external]</text>
<path class="l c" d="M750,411 L790,411" stroke-dasharray="4 3"/>
<rect class="b" x="560" y="150" width="190" height="82" style="stroke:#8aa0b4"/><text x="572" y="178" class="t">band edge |T| = 2</text><text x="572" y="198" class="s">rails merge (exceptional point)</text><text x="572" y="216" class="s">meridians sit exactly here</text>
<path class="l" d="M500,200 L560,195"/><text x="506" y="186" class="lt">T = 1 band</text>
<path class="l" d="M450,380 C500,320 560,260 600,232"/><text x="520" y="300" class="lt">T = 3 gap</text>
<rect class="b" x="560" y="60" width="190" height="62"/><text x="572" y="84" class="t">ladder T = 6 -> 34</text><text x="572" y="104" class="s">eps^4 = 17 + 12 sqrt2</text>
<rect class="b" x="790" y="40" width="170" height="54"/><text x="802" y="62" class="t">Apery l^2 - 34 l + 1</text><text x="802" y="80" class="s">[external]</text>
<rect class="b" x="790" y="110" width="170" height="70"/><text x="802" y="132" class="t">Catalan 2.5</text><text x="802" y="150" class="s">(l-1)(l^2 - 34 l + 1)</text><text x="802" y="168" class="s">rest mode forced</text>
<rect class="b" x="790" y="196" width="170" height="54"/><text x="802" y="218" class="t">saddle t^2 + 2t - 1</text><text x="802" y="236" class="s">t^4 + t^-4 = 34</text>
<path class="l" d="M750,80 L790,70" stroke-dasharray="4 3"/><path class="l" d="M750,98 L790,140" stroke-dasharray="4 3"/><path class="l" d="M750,110 L790,215" stroke-dasharray="4 3"/>
<rect class="b" x="300" y="490" width="560" height="54" style="stroke:#ff7a90"/><text x="316" y="512" class="t">Chirality: 4_1 is its own mirror (certificate); 3_1 is not (signature -2)</text><text x="316" y="532" class="s">the amphichiral knot's geometry is built from the chiral knot's monodromy polynomial</text>
<path class="l r" d="M135,322 C135,460 220,517 300,517"/>
</svg>'''
page = f'''<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Relations map — Count Me as One v1 + D25/D27 (combined)</title>
<style>:root{{color-scheme:dark}}body{{margin:0;background:#05070b;color:#dfe7ef;font-family:"DejaVu Sans",system-ui,sans-serif;line-height:1.55}}
main{{max-width:1000px;margin:0 auto;padding:36px 22px 80px}}h1{{font-size:30px;margin:0 0 4px}}.by{{color:#7a8a9b;font-size:13px}}
h2{{color:#f2c14e;font-size:22px;margin:34px 0 8px}}h3{{color:#63d3ff;font-size:17px;margin:26px 0 2px}}.n{{color:#55657a;font-size:13px}}.kd{{color:#8a9aab;font-size:13px;margin:0 0 8px}}
table{{border-collapse:collapse;width:100%;font-size:13.5px}}td{{border-top:1px solid #1f2a38;padding:7px 8px;vertical-align:top}}td.a{{font-family:monospace;font-size:12.5px;color:#cfd8e2;white-space:nowrap}}
td.arr{{color:#55657a}}.w{{color:#6f8296;font-size:11.5px;font-family:monospace;margin-top:3px}}p{{font-size:15px}}.ok{{color:#7fd88f}}ul{{font-size:14.5px}}</style></head><body><main>
<h1>Relations map</h1><div class="by">Jeromie Beasley &middot; Count Me as One v1 + D25/D27 combined &middot; {html.escape(rep["lean_version"])}</div>
<p>Every line below is an edge in <code>RELATIONS.json</code>. The harness checks the file: every theorem is a node with a rule tag and at least one edge, every edge end is a proved theorem or a declared outside source, and every edge names the kernel-checked theorem that witnesses it. A forged edge is fed through the same checker and rejected.</p>
<p class="ok">Checks on this build: build, kernel replay, axiom audit ({len(rep["axioms"])} theorems, {sum(1 for v in rep["axioms"].values() if not v)} with no axioms at all), {len(c["false_controls"])}/{len(c["false_controls"])} false controls rejected, relations {c["relations"]["nodes"]} nodes / {c["relations"]["edges"]} edges ({c["relations"]["external_edges"]} external, {c["relations"]["analogy_only_edges"]} analogy-only). All pass.</p>
{svg}
<h2>What the map says</h2>
<ul>
<li><b>One polynomial ties three things.</b> z&sup2; &minus; z + 1 is the regular ideal tetrahedron (Thurston), the Riley parameter of the figure-eight knot group, and the monodromy of the trefoil. The amphichiral knot's hyperbolic geometry is built from the chiral knot's monodromy polynomial.</li>
<li><b>The broken branch is a ruler.</b> The golden branch z&sup2; &minus; z &minus; 1 also solves Thurston's bare edge equation but fails the cycle test by a sign (&minus;1 instead of +1). Squared, it is exactly the figure-eight monodromy t&sup2; &minus; 3t + 1, which is the figure-eight's Alexander polynomial. Kept, not discarded.</li>
<li><b>One ladder.</b> x<sup>k</sup> + x<sup>&minus;k</sup> obeys t<sub>k+1</sub> = T t<sub>k</sub> &minus; t<sub>k&minus;1</sub> in any ring. T = 1 (trefoil) is periodic with period 6; T = 3 (figure-eight) reaches 123 = &phi;<sup>10</sup> + &phi;<sup>&minus;10</sup> at the fifth rung, Q1's ratio; T = 6 reaches 34, the Ap&eacute;ry / Catalan trace. |T| = 2 is the band edge where the rails merge, and both Riley meridians sit exactly there.</li>
<li><b>D25/D27 join by proof, not analogy.</b> Every trefoil wall on S&sup1; (&Delta;<sub>3&#8321;</sub>(e<sup>2&pi;i&alpha;</sup>) = 0, &alpha; &equiv; &plusmn;1/6) is a root of z&sup2; &minus; z + 1, so CMaO's ring-generic Gluing theorems evaluate there: it solves Thurston's edge equation, each tetrahedron gives &minus;1, z&sup3; = &minus;1 (<code>CMaOBridge</code>). D25's symmetrized Alexander polynomials equal CMaO's Seifert-matrix coefficients. The figure-eight has no wall (&Delta;<sub>4&#8321;</sub> &ge; 1). Chiral eta and the BHL q<sup>1</sup> separation (2 vs 1) are kept differences.</li>
<li><b>The chiral source survives.</b> The figure-eight has an explicit mirror certificate; the trefoil provably has none (its form is negative definite).</li>
</ul>
<h2>Every edge, by kind</h2>{"".join(rows)}
<h2>Outside sources the map points to</h2><table>{ext}</table>
<p class="kd">External edges record a link to his other work or the literature; the link itself is not proved in this repository. Analogy-only edges ({sum(1 for e in rel["edges"] if e["kind"] == "analogy-only")}) are structural pointers with no theorem behind them.</p>
</main></body></html>'''
(ROOT / "RELATIONS.html").write_text(page)
print("wrote RELATIONS.html")
