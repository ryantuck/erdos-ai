import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset

open Filter Asymptotics

noncomputable section

namespace Erdos1178

/-!
# Erdős Problem #1178

For r ≥ 3, let d_r(e) be the minimal d such that ex_r(n, F) = o(n²),
where F is the family of r-uniform hypergraphs on d vertices with e edges.

Prove that d_r(e) = (r-2)e + 3 for all r, e ≥ 3.

Status: OPEN (erdosproblems.com/1178; page last edited 26 January 2026,
accessed 2026-02-23; the github.com/teorth/erdosproblems metadata mirror
agrees: state "open", last updated 2026-01-25).

A conjecture of Brown, Erdős, and Sós [BES73], who proved the lower bound
d_r(e) ≥ (r-2)e + 3 (see also erdosproblems.com/1076).

Known partial results (from the source page):
- Ruzsa and Szemerédi [RuSz78] proved d_3(3) = 6 (see erdosproblems.com/716).
- Erdős, Frankl, and Rödl [EFR86] proved d_r(3) = (r-2)·3 + 3 for all r ≥ 3.
- Sárközy and Selkow [SaSe05] proved d_r(e) ≤ (r-2)e + 2 + ⌊log₂ e⌋ for all
  r, e ≥ 3 (in particular, the set defining `minD` below is nonempty, so its
  sInf is an attained minimum). Not formalized as a variant: ⌊log₂ e⌋ would
  need `Nat.log`, a construct not otherwise present in this file.
- Solymosi and Solymosi [SoSo17] proved d_3(10) ≤ 14.
- Conlon, Gishboliner, Levanzov, and Shapira [CGLS23] proved
  d_3(e) ≤ e + O(log e / log log e) for all e ≥ 3. Not formalized as a
  variant (asymptotic in e, would need an O(·) encoding over e → ∞).

In [Er75b] Erdős further asks whether, if F is the family of 3-uniform
hypergraphs on k vertices with k-3 edges, ex_3(n, F) ≍ n·r_{k-3}(n), where
r_{k-3}(n) is the maximal size of a subset of {1,…,n} without a non-trivial
arithmetic progression of length k-3. He states that Ruzsa has proved the
lower bound for k = 6, 7, 8. (Not formalized here — it needs AP-free-set
machinery not present in this file.)

See erdosproblems.com/1157 for the general Brown-Erdős-Sós conjecture:
this problem is its t = 2 case (there, f_r(n; k, s) = o(n^t) is conjectured
whenever k ≥ (r-t)s + t + 1, which at t = 2 gives the threshold (r-2)s + 3).

References (recovered from the archived erdosproblems.com/latex/1178 fetch;
journal volume numbers are absent from the recovered extraction and are
deliberately not invented):

[BES73] Brown, W.G., Erdős, P., and Sós, V.T., "Some extremal problems on
r-graphs". New Directions in the Theory of Graphs (1973), 53-63.

[Er75b] Erdős, P., "Problems and results in combinatorial number theory".
Journées Arithmétiques de Bordeaux (Conference, University of Bordeaux,
1974) (1975), 295-310.

[Er81] Erdős, P., "On the combinatorial problems which I would most like to
see solved". Combinatorica (1981), 25-42. (Stub: this key is cited on the
page but has no entry in the recovered /latex/1178 extraction; the expansion
follows sibling files carrying the same key.)

[RuSz78] Ruzsa, I.Z. and Szemerédi, E., "Triple systems with no six points
carrying three triangles". Combinatorics (Proc. Fifth Hungarian Colloq.,
Keszthely, 1976), Vol. II (1978), 939-945.

[EFR86] Erdős, P., Frankl, P., and Rödl, V., "The asymptotic number of
graphs not containing a fixed subgraph and a problem for hypergraphs having
no exponent". Graphs and Combinatorics (1986), 113-121.

[SaSe05] Sárközy, G.N. and Selkow, S., "An extension of the Ruzsa-Szemerédi
theorem". Combinatorica (2005), 77-84.

[SoSo17] Solymosi, D. and Solymosi, J., "Small cores in 3-uniform
hypergraphs". Journal of Combinatorial Theory Series B (2017), 897-910.

[CGLS23] Conlon, D., Gishboliner, L., Levanzov, Y., and Shapira, A., "A new
bound for the Brown-Erdős-Sós problem". Journal of Combinatorial Theory
Series B (2023), 1-35.

Tags: graph theory, hypergraphs
-/

/-- An r-uniform hypergraph on vertex type V is a set of r-element subsets of V. -/
def IsRUniform (r : ℕ) {V : Type*} (E : Finset (Finset V)) : Prop :=
  ∀ e ∈ E, e.card = r

/-- The hypergraph E on Fin n contains a (d, e)-configuration: there exist d
    vertices spanning at least e edges of E. Since the Brown-Erdős-Sós family
    F_r(d, e) consists of *all* r-uniform hypergraphs on d vertices with e
    edges (isolated vertices allowed), E contains a member of F_r(d, e) as a
    sub-hypergraph iff this predicate holds; equivalently, avoiding F_r(d, e)
    means no d vertices span e or more edges. (For n < d no d-element
    S ⊆ Fin n exists and the predicate is false, matching the embedding
    convention — a copy needs d distinct host vertices; only n → ∞ matters
    in the statements below.) -/
def ContainsConfig (d e n : ℕ) (E : Finset (Finset (Fin n))) : Prop :=
  ∃ S : Finset (Fin n), S.card = d ∧ e ≤ (E.filter (fun edge => edge ⊆ S)).card

/-- The r-uniform Turán number ex_r(n; d, e): the maximum number of edges in an
    r-uniform hypergraph on n vertices that contains no r-uniform sub-hypergraph
    on d vertices with e edges (i.e., avoids the Brown-Erdős-Sós family F_r(d,e)).

    For e ≥ 1 the defining set is nonempty (the empty hypergraph avoids every
    configuration) and bounded above by C(n, r) (an r-uniform edge set is a
    family of r-subsets of Fin n), so `sSup` is the honest, attained maximum. -/
noncomputable def turanNumber (r n d e : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ E : Finset (Finset (Fin n)),
    IsRUniform r E ∧ ¬ ContainsConfig d e n E ∧ E.card = m}

/-- The minimal d such that the r-uniform Turán number ex_r(n; d, e) = o(n²)
    as n → ∞.

    The defining set is upward closed in d: for n > d, any d vertices spanning
    e edges extend to d+1 vertices spanning them, so avoiding (d+1, e)-configs
    implies avoiding (d, e)-configs, ex_r(n; d+1, e) ≤ ex_r(n; d, e)
    eventually, and o(n²) transfers upward — hence `sInf` really is "the
    minimal such d". For r, e ≥ 3 the set is moreover provably nonempty
    (Sárközy-Selkow [SaSe05]: d = (r-2)e + 2 + ⌊log₂ e⌋ works), so the sInf
    is an attained minimum, not the ℕ junk value sInf ∅ = 0; independently,
    any equality `minD r e = c` with c > 0 already forces nonemptiness. -/
noncomputable def minD (r e : ℕ) : ℕ :=
  sInf {d : ℕ | (fun n : ℕ => (turanNumber r n d e : ℝ)) =o[atTop]
                (fun n : ℕ => (n : ℝ) ^ 2)}

/--
Erdős Problem #1178 [BES73] [Er75b] [Er81] (OPEN):

For r, e ≥ 3, the minimal d such that the r-uniform Turán number
ex_r(n, F) = o(n²) (where F is the family of all r-uniform hypergraphs on d vertices
with e edges) equals (r-2)·e + 3.

Here turanNumber r n d e is the maximum number of edges in an r-uniform hypergraph
on n vertices avoiding all configurations on d vertices with e edges: formally, there
is no d-element set S ⊆ Fin n with e or more r-uniform edges in S. minD r e is the
least such d.

The source phrases the problem as "Prove that d_r(e) = (r-2)e + 3", so the
direct-assertion form (no answer-wrapper) is the intended shape.

Brown, Erdős, and Sós [BES73] proved the lower bound d_r(e) ≥ (r-2)·e + 3.
Ruzsa and Szemerédi [RuSz78] proved d_3(3) = 6.
Erdős, Frankl, and Rödl [EFR86] proved the case e = 3: d_r(3) = 3(r-2)+3 for all r ≥ 3.
-/
theorem erdos_problem_1178 (r e : ℕ) (hr : 3 ≤ r) (he : 3 ≤ e) :
    minD r e = (r - 2) * e + 3 :=
  sorry

/--
Erdős, Frankl, and Rödl [EFR86] proved the case e = 3 of the conjecture:
d_r(3) = (r-2)·3 + 3 for all r ≥ 3.

(The equality's right-hand side is positive, so it forces the set defining
`minD r 3` to be nonempty — no ℕ-sInf junk-value reading is possible.)

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1178.variants.efr86 (r : ℕ) (hr : 3 ≤ r) :
    minD r 3 = (r - 2) * 3 + 3 :=
  sorry

/--
Ruzsa and Szemerédi [RuSz78] proved d_3(3) = 6 — the (6,3)-theorem
(see erdosproblems.com/716); the case r = e = 3 of the conjecture,
consistent with (3-2)·3 + 3 = 6.

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1178.variants.ruzsa_szemeredi :
    minD 3 3 = 6 :=
  sorry

/--
Solymosi and Solymosi [SoSo17] proved d_3(10) ≤ 14. Stated in membership
form — ex_3(n; 14, 10) = o(n²) — which, by the upward closure of the set
defining `minD` (see its docstring), is exactly d_3(10) ≤ 14, and does not
lean on the ℕ-sInf junk value.

Added by the fable-review pass from page-confirmed content; not
compile-verified.
-/
theorem erdos_problem_1178.variants.solymosi_solymosi :
    (fun n : ℕ => (turanNumber 3 n 14 10 : ℝ)) =o[atTop]
      (fun n : ℕ => (n : ℝ) ^ 2) :=
  sorry

end Erdos1178

end
