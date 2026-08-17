import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card

open SimpleGraph Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
# Erdős Problem #86

**Status: OPEN** (prize: $100). Source: erdosproblems.com/86, page edition
27 December 2025 (archived capture accessed 2026-02-22); status cross-checked
against the teorth/erdosproblems metadata mirror (commit a09c7a2, 2026-08-14:
state open, last update 2025-08-31, formalized: no).

Let $Q_n$ be the $n$-dimensional hypercube graph (so that $Q_n$ has $2^n$ vertices
and $n \cdot 2^{n-1}$ edges). Is it true that every subgraph of $Q_n$ with
$\geq (\frac{1}{2} + o(1)) n \cdot 2^{n-1}$ many edges contains a $C_4$?

Equivalently, let $f(n)$ be the maximum number of edges in a subgraph of $Q_n$
without a $C_4$. The conjecture is that $f(n) \leq (\frac{1}{2} + o(1)) n \cdot 2^{n-1}$.

Erdős [Er91] showed that $f(n) \geq (\frac{1}{2} + c/n) n \cdot 2^{n-1}$ for some
constant $c > 0$, and wrote it is "perhaps not hopeless" to determine $f(n)$
exactly. Brass, Harborth, and Nienborg [BHN95] improved the lower bound to
$f(n) \geq (\frac{1}{2} + c/\sqrt{n}) n \cdot 2^{n-1}$.

Balogh, Hu, Lidicky, and Liu [BHLL14] proved $f(n) \leq 0.6068 \cdot n \cdot 2^{n-1}$.
This was improved to $\leq 0.60318 \cdot n \cdot 2^{n-1}$ by Baber [Ba12b].
Note these are asymptotic (flag-algebra) density bounds: the literal pointwise
inequality fails at small $n$ — brute-force search gives $f(1), f(2), f(3) =
1, 3, 9$, and $f(3) = 9 > 0.60318 \cdot 3 \cdot 2^2 \approx 7.24$ — so the
variants below state them in eventual $(+\delta)$ form.

A similar question can be asked for other even cycles; see Erdős Problem #666
for the $C_6$ analogue (disproved per the metadata mirror, 2026-02-06, with a
Lean-verified proof). Related OEIS sequence: A245762 (maximum number of edges in
a $C_4$-free subgraph of $Q_n$; the values $f(1..3) = 1, 3, 9$ above were
verified by exhaustive search during review).

Tags: graph theory

## References

The first four entries were recovered from an archived fetch of
`erdosproblems.com/latex/86` (2026-03-15 pipeline session log); volume numbers
were not present in that capture and remain DEFERRED. The remaining keys are
cited by the page header without bibliographic data; sibling-corpus expansions
for them conflict, so they are kept as honest key-only stubs (nothing is
fabricated).

- [Er91] Erdős, P., *Problems and results in combinatorial analysis and
  combinatorial number theory*. Graph Theory, Combinatorics, and Applications,
  Vol. 1 (Kalamazoo, MI, 1988) (1991), 397–406.
- [BHN95] Brass, P., Harborth, H., and Nienborg, H., *On the maximum number of
  edges in a $C_4$-free subgraph of $Q_n$*. J. Graph Theory (1995), 17–23.
- [BHLL14] Balogh, J., Hu, P., Lidický, B., and Liu, H., *Upper bounds on the
  size of 4- and 6-cycle-free subgraphs of the hypercube*. European J. Combin.
  (2014), 75–85.
- [Ba12b] Baber, R., *Turán densities of hypercubes*. arXiv:1201.3587 (2012).
- [Er90] Erdős, P. (1990). (Key-only stub; full data DEFERRED.)
- [Er92b] Erdős, P. (1992). (Key-only stub; full data DEFERRED.)
- [Er93] Erdős, P. (1993). (Cited by the page as [Er93, p.343]; key-only stub,
  full data DEFERRED.)
- [Er94b] Erdős, P. (1994). (Key-only stub; full data DEFERRED.)
- [Er95] Erdős, P. (1995). (Key-only stub; full data DEFERRED.)
- [Er97f] Erdős, P. (1997). (Key-only stub; full data DEFERRED.)
-/

/-- The n-dimensional hypercube graph Q_n. Vertices are functions Fin n → Bool,
    and two vertices are adjacent iff they differ in exactly one coordinate. -/
def hypercubeGraph86 (n : ℕ) : SimpleGraph (Fin n → Bool) where
  Adj u v := u ≠ v ∧ (Finset.univ.filter (fun i => u i ≠ v i)).card = 1
  symm u v := by
    rintro ⟨hne, hcard⟩
    refine ⟨hne.symm, ?_⟩
    have heq : (Finset.univ.filter fun i => v i ≠ u i) =
               (Finset.univ.filter fun i => u i ≠ v i) :=
      Finset.filter_congr (fun i _ => ne_comm)
    rw [heq]
    exact hcard
  loopless := fun v ⟨hne, _⟩ => hne rfl

/-- The cycle graph C_m on m vertices (m ≥ 3). Vertex i is adjacent to vertex
    i + 1 (mod m) and vertex i - 1 (mod m). -/
def cycleGraph86 (m : ℕ) (_ : m ≥ 3) : SimpleGraph (Fin m) where
  Adj i j := i ≠ j ∧ (j.val = (i.val + 1) % m ∨ i.val = (j.val + 1) % m)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim Or.inr Or.inl⟩
  loopless := fun _ ⟨h, _⟩ => h rfl

/--
Erdős Problem #86 [Er90][Er91][Er92b][Er93,p.343][Er94b][Er95][Er97f]:

For every ε > 0, if n is sufficiently large, every subgraph of Q_n with at least
(1/2 + ε) · n · 2^{n-1} edges contains a C_4.

The source poses this as a yes/no question ("Is it true that…?"); the problem is
OPEN, and the statement is asserted here in the conjectured (affirmative)
direction, the corpus convention for open questions in this pipeline. The
`∃ N₀` eventuality is essential, not decorative: for any fixed ε < 1/4 the
instance at n = 3 is genuinely false (f(3) = 9 > (1/2 + ε) · 12, brute-force
verified), as are the degenerate instances n = 0, 1, 2 for small ε; the [BHN95]
lower bound (1/2 + c/√n) · n · 2^{n-1} forces N₀ → ∞ as ε → 0.
-/
theorem erdos_problem_86 :
    ∀ ε : ℝ, ε > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : SimpleGraph (Fin n → Bool),
      (∀ u v : Fin n → Bool, H.Adj u v → (hypercubeGraph86 n).Adj u v) →
      (↑(H.edgeFinset.card) : ℝ) ≥ (1 / 2 + ε) * ↑n * (2 : ℝ) ^ (n - 1 : ℕ) →
      ∃ f : Fin 4 → (Fin n → Bool), Function.Injective f ∧
        ∀ i j, (cycleGraph86 4 (by omega)).Adj i j → H.Adj (f i) (f j) :=
  sorry

/--
Variant (solved) [Er91]: Erdős showed that Q_n has a C_4-free subgraph with at
least (1/2 + c/n) · n · 2^{n-1} edges, for some constant c > 0. Stated in
eventual form (the page states the bound asymptotically; the constant c is
quantified before n, as required — c is uniform). C_4-freeness is expressed by
negating the same containment encoding used in the main statement.

NOTE: statement added during review from the recovered source page; NOT
compile-verified in this container.
-/
theorem erdos_problem_86.variants.lower_bound_erdos :
    ∃ c : ℝ, c > 0 ∧ ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∃ H : SimpleGraph (Fin n → Bool),
      (∀ u v : Fin n → Bool, H.Adj u v → (hypercubeGraph86 n).Adj u v) ∧
      ¬(∃ f : Fin 4 → (Fin n → Bool), Function.Injective f ∧
          ∀ i j, (cycleGraph86 4 (by omega)).Adj i j → H.Adj (f i) (f j)) ∧
      (↑(H.edgeFinset.card) : ℝ) ≥ (1 / 2 + c / ↑n) * ↑n * (2 : ℝ) ^ (n - 1 : ℕ) :=
  sorry

/--
Variant (solved) [BHLL14]: Balogh, Hu, Lidický, and Liu proved
f(n) ≤ 0.6068 · n · 2^{n-1}. Their bound is a flag-algebra bound on the limiting
edge density of C_4-free subgraphs, and the literal pointwise inequality fails
at small n (f(2) = 3 > 0.6068 · 2 · 2 ≈ 2.43 and f(3) = 9 > 0.6068 · 3 · 4 ≈
7.28, brute-force verified), so it is stated here in eventual (+δ) form, which
the density bound implies. The constant is written 6068/10000 to match the
file's fraction style.

NOTE: statement added during review from the recovered source page; NOT
compile-verified in this container.
-/
theorem erdos_problem_86.variants.upper_bound_balogh_hu_lidicky_liu :
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : SimpleGraph (Fin n → Bool),
      (∀ u v : Fin n → Bool, H.Adj u v → (hypercubeGraph86 n).Adj u v) →
      ¬(∃ f : Fin 4 → (Fin n → Bool), Function.Injective f ∧
          ∀ i j, (cycleGraph86 4 (by omega)).Adj i j → H.Adj (f i) (f j)) →
      (↑(H.edgeFinset.card) : ℝ) ≤ (6068 / 10000 + δ) * ↑n * (2 : ℝ) ^ (n - 1 : ℕ) :=
  sorry

/--
Variant (solved) [Ba12b]: Baber improved the upper bound to
f(n) ≤ 0.60318 · n · 2^{n-1}. As with [BHLL14] this is a flag-algebra density
bound (false pointwise at small n: f(3) = 9 > 0.60318 · 3 · 4 ≈ 7.24), so it is
stated in eventual (+δ) form; the constant is written 60318/100000.

NOTE: statement added during review from the recovered source page; NOT
compile-verified in this container.
-/
theorem erdos_problem_86.variants.upper_bound_baber :
    ∀ δ : ℝ, δ > 0 →
    ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    ∀ H : SimpleGraph (Fin n → Bool),
      (∀ u v : Fin n → Bool, H.Adj u v → (hypercubeGraph86 n).Adj u v) →
      ¬(∃ f : Fin 4 → (Fin n → Bool), Function.Injective f ∧
          ∀ i j, (cycleGraph86 4 (by omega)).Adj i j → H.Adj (f i) (f j)) →
      (↑(H.edgeFinset.card) : ℝ) ≤ (60318 / 100000 + δ) * ↑n * (2 : ℝ) ^ (n - 1 : ℕ) :=
  sorry

end
