import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open SimpleGraph Classical

/-!
# Erdős Problem #60

Does every graph on n vertices with > ex(n; C₄) edges contain ≫ n^{1/2} many
copies of C₄?

Conjectured by Erdős and Simonovits [Er90][Er93, p.335], who could not even
prove that at least 2 copies of C₄ are guaranteed (formalized as a variant
below).

The behaviour of ex(n; C₄) is the subject of problem [765].

He, Ma, and Yang [HeMaYa21] have proved this conjecture when n = q² + q + 1
for some even integer q (formalized as a variant below).

**Status: OPEN** ("This is open, and cannot be resolved with a finite
computation." — erdosproblems.com/60, page edition 18 November 2025, accessed
2026-02-22; status re-confirmed open against the teorth/erdosproblems metadata
mirror, `data/problems.yaml` entry 60, last update 2025-08-31, mirror HEAD
2026-08-14; the upstream google-deepmind/formal-conjectures file
`FormalConjectures/ErdosProblems/60.lean` at HEAD dd1c2beb (2026-08-16) also
tags the main statement `research open`).

References:

- [Er90] Erdős, P., _Some of my favourite unsolved problems_. A tribute to
  Paul Erdős (1990), 467–478. (Corpus-consensus entry for this key; not in the
  archived /latex/60 extraction — DEFERRED against the live source.)
- [Er93] Erdős, P., _Some of my favorite solved and unsolved problems in graph
  theory_. Quaestiones Mathematicae 16 (1993), 333–350. (Corpus-consensus
  entry, recovered from sibling /latex fetches preserved in the session logs;
  the page's pointer [Er93, p.335] falls inside this page range, corroborating
  the identification — still DEFERRED against the live source. NB: the styled
  sibling `deepmind/deepmind/60.lean` instead expands [Er93] as "On some of my
  favourite theorems", Combinatorics, Paul Erdős is eighty, Vol. 2 (Keszthely,
  1993), 97–132 — inconsistent with the p.335 pointer; that expansion belongs
  to a different site key.)
- [HeMaYa21] He, J., Ma, J., Yang, T., _Some extremal results on 4-cycles_.
  Journal of Combinatorial Theory, Series B (2021). (Title/journal/year from
  the archived /latex/60 fetch; volume and pages absent from the capture —
  DEFERRED, not fabricated.)

Related OEIS sequence (from the metadata mirror; the page itself lists none):
A006855 — the values of ex(n; C₄).

Tags: graph theory, cycles
https://www.erdosproblems.com/60
-/

/-- The cycle graph C_m on m vertices (m ≥ 3). -/
def cycleGraph60 (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/-- G contains H as a subgraph (via an injective homomorphism). -/
def ContainsSubgraph60 {V U : Type*} (G : SimpleGraph V) (H : SimpleGraph U) : Prop :=
  ∃ f : U → V, Function.Injective f ∧ ∀ u v : U, H.Adj u v → G.Adj (f u) (f v)

/-- ex(n; H): maximum number of edges in an H-free simple graph on n vertices.

(`sSup` well-definedness for the instantiation used in this file, H = C₄: the
value set is nonempty — the empty graph on `Fin n` is C₄-free with 0 edges —
and bounded above by `Fintype.card (Sym2 (Fin n))`, since every edge set of a
graph on `Fin n` lives inside that finite ambient type; hence `sSup` is the
genuine maximum. Boundedness never fails for any `H`; the only degenerate case
is an `H` contained in *every* graph on `Fin n` — e.g. an edgeless `H` — where
the value set is empty and `sSup ∅ = 0`. That case does not arise for H = C₄.) -/
noncomputable def extremalNumber60 {U : Type*} (H : SimpleGraph U) (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∃ G : SimpleGraph (Fin n),
    ¬ContainsSubgraph60 G H ∧ G.edgeSet.ncard = m}

/-- The number of labeled copies of C₄ in G: injective maps f : Fin 4 → Fin n
    preserving C₄ adjacency. Each unordered C₄ subgraph yields 8 labeled copies
    (4 rotations × 2 reflections). -/
noncomputable def labeledC4Count (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  (Finset.univ.filter (fun (f : Fin 4 → Fin n) =>
    Function.Injective f ∧
    ∀ i : Fin 4, G.Adj (f i) (f (i + 1)))).card

/--
Erdős Problem #60 [Er90][Er93, p.335]:

Does every graph on n vertices with more than ex(n; C₄) edges contain
≫ n^{1/2} copies of C₄?

Formally: there exist c > 0 and N₀ such that for all n ≥ N₀, every graph G on
n vertices with more than ex(n; C₄) edges has at least c · n^{1/2} labeled
copies of C₄.

The problem is an OPEN yes/no question; following this corpus's convention for
open questions in the raw pipeline (direct assertion of the conjectured
direction, with the belief documented), this theorem asserts the
Erdős–Simonovits "yes" direction. Encoding notes: labeled copies are exactly
8 × unlabeled copies (each 4-cycle subgraph admits 8 injective adjacency-
preserving parametrizations), a constant factor absorbed into c; and the
"eventually" (N₀) form is equivalent to the all-n form, because any graph with
more than ex(n; C₄) edges contains at least one C₄ (by definition of the
extremal number), hence at least 8 labeled copies, so the finitely many
n < N₀ can be absorbed by shrinking c.
-/
theorem erdos_problem_60 :
    ∃ (c : ℝ) (_ : c > 0) (N₀ : ℕ),
    ∀ n : ℕ, N₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > extremalNumber60 (cycleGraph60 4 (by omega)) n →
      (labeledC4Count n G : ℝ) ≥ c * (n : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
**Variant (He–Ma–Yang [HeMaYa21], solved):** the conjecture holds when
n = q² + q + 1 for some even integer q: there is a c > 0 such that for every
even q, every graph on n = q² + q + 1 vertices with more than ex(n; C₄) edges
has at least c · n^{1/2} labeled copies of C₄.

(The single-constant, all-even-q form is equivalent to an "eventually in q"
reading: any graph with more than ex(n; C₄) edges contains a C₄ and hence at
least 8 labeled copies, so the finitely many small q are absorbed by shrinking
c. Page-confirmed remark; added by the fable-review pass; not
compile-verified.)
-/
theorem erdos_problem_60.variants.he_ma_yang :
    ∃ (c : ℝ) (_ : c > 0),
    ∀ q : ℕ, Even q →
    ∀ G : SimpleGraph (Fin (q ^ 2 + q + 1)),
      G.edgeSet.ncard > extremalNumber60 (cycleGraph60 4 (by omega)) (q ^ 2 + q + 1) →
      (labeledC4Count (q ^ 2 + q + 1) G : ℝ) ≥
        c * ((q ^ 2 + q + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) :=
  sorry

/--
**Variant (weak form, open):** for all sufficiently large n, every graph on n
vertices with more than ex(n; C₄) edges contains at least 2 unlabeled copies
of C₄ — equivalently, at least 16 labeled copies, since the labeled count is
exactly 8 per unlabeled copy. Erdős and Simonovits could not even prove this
weaker statement (remark on the archived page).

The N₀ is essential — the all-n form is false at n = 4: ex(4; C₄) = 4 (a
triangle with a pendant edge is C₄-free with 4 edges, and the unique 5-edge
graph on 4 vertices, K₄ minus an edge, contains a C₄), yet K₄ minus an edge
contains exactly one unlabeled C₄, i.e. 8 < 16 labeled copies. (Added by the
fable-review pass; not compile-verified.)
-/
theorem erdos_problem_60.variants.at_least_two :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
    ∀ G : SimpleGraph (Fin n),
      G.edgeSet.ncard > extremalNumber60 (cycleGraph60 4 (by omega)) n →
      labeledC4Count n G ≥ 16 :=
  sorry

end
