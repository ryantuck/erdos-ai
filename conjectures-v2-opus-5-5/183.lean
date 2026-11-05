-- [AI - Claude Opus 5.5]: Erdős Problem 183 — second-pass formalization
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Filter Topology

noncomputable section

/-!
# Erdős Problem #183

*Source:* [erdosproblems.com/183](https://www.erdosproblems.com/183) (status **OPEN** at capture,
with a \$250 prize: "This is open, and cannot be resolved with a finite computation."; captured
2026-02-20). [Er61]

Let $R(3;k)$ be the minimal $n$ such that if the edges of $K_n$ are coloured with $k$ colours then
there must exist a monochromatic triangle. Determine $\lim_{k\to \infty}R(3;k)^{1/k}$.

Remarks recorded on the page (abridged): Erdős offers \$100 for showing that this limit is finite.
An easy pigeonhole argument shows that $R(3;k)\leq 2+k(R(3;k-1)-1)$, from which
$R(3;k)\leq \lceil e k!\rceil$ immediately follows. The best-known upper bounds are all of the form
$ck!+O(1)$. The best-known lower bound (coming from lower bounds for Schur numbers) is
$R(3;k)\geq (380)^{k/5}-O(1)$, due to [ACPPRT21] (improving [Ex94] and [FrSw00]); note
$380^{1/5}\approx 3.2806$. See also [483]. OEIS A003323. This is #21 in Ramsey Theory in the graphs
problem collection.

## Status after capture

Upstream `formal-conjectures` (`2befc3a`) records the problem as **solved**: there is no finite
limit, $R(3;k)^{1/k}\to\infty$, established by [OpenAI26] with an explicit lower bound
$R(3;k)\geq\bigl(k^{1/3}/(6e^{38}\log k)\bigr)^k$ for $k\ge2$, and a linked Lean proof
(`openai/ten-proofs`, `MulticolorTriangleRamsey.lean`). The metadata mirror (`c443d8c`) records
"solved (Lean)" (2026-08-01). Neither the preprint nor the Lean proof was read in this review.

The input asserted that the limit exists and is **finite** (the \$100 direction). By the
post-capture result that statement is false, so v2 replaces it by the recorded answer,
`Tendsto … atTop atTop`, and proves in Lean that this answer refutes the input's statement
(`not_finite_of_tendsto`).

## Encoding notes

* `multicolorRamseyTriangle` colours ordered pairs, diagonal included, by a symmetric function.
  Only off-diagonal values matter for triangles, but with no colours (`k = 0`) even `Fin 1` has no
  colouring, so `R(3;0) = 1` rather than the conventional `2`; `R(3;1) = 3` (both PROVED in Lean).
  As a consequence the page's recursion fails at `k = 1` for this definition
  (`variants.recursion_fails_at_one`, PROVED) and is stated here for `k ≥ 2`. The limit is
  unaffected.
* The set defining `R(3;k)` is nonempty for every `k`, by the pigeonhole recursion (not formalized
  here); otherwise `sInf` would return the junk value `0`.

## References

From the site's `/latex/183` bibliography:
* [ACPPRT21] Ageron, R., Casteras, P., Pellerin, T., Portella, Y., Rimmel, A. and Tomasik, J.,
  _New lower bounds for Schur and weak Schur numbers_. arXiv:2112.03175 (2021).
* [Ex94] Exoo, G., _A lower bound for Schur numbers and multicolor Ramsey numbers_. Electron. J.
  Combin. (1994).
* [FrSw00] Fredricksen, Harold and Sweet, Melvin M., _Symmetric sum-free partitions and lower
  bounds for Schur numbers_. Electron. J. Combin. (2000), Research Paper 32, 9.

Other sources:
* [Er61] Erdős, Paul, _Some unsolved problems_. Magyar Tud. Akad. Mat. Kutató Int. Közl. (1961),
  221–254. (Site `/latex/511`; the `/latex/183` fetch lists no entry for it. Upstream's Problem 183
  file instead gives _Graph theory and probability. II_, Canad. J. Math. (1961), 346–352.)
* [OpenAI26] OpenAI, _Ten advances in mathematics and theoretical computer science_ (2026). (From
  upstream's Problem 183 file; not read.)

*Provenance:* second pass of `conjectures/183.lean` (Opus 5.5 review, `opus-5-5-review/183.md`).
-/

/-- The multicolor Ramsey number R(3;k): the minimum n such that every
    k-colouring of the edges of K_n contains a monochromatic triangle.
    A k-colouring is a symmetric function c : Fin n → Fin n → Fin k,
    and a monochromatic triangle is three pairwise distinct vertices
    whose three edges all receive the same colour. -/
noncomputable def multicolorRamseyTriangle (k : ℕ) : ℕ :=
  sInf {n : ℕ | ∀ (c : Fin n → Fin n → Fin k),
    (∀ i j, c i j = c j i) →
    ∃ (a b d : Fin n), a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      c a b = c a d ∧ c a b = c b d}

/--
Erdős Problem #183 [Er61], as answered after the capture [OpenAI26]:

$R(3;k)^{1/k}\to\infty$, so the limit is infinite.

(Status: OPEN at capture; recorded as solved by upstream and the mirror, unverified here. The
input instead asserted a finite limit, which this refutes: `not_finite_of_tendsto`.)
-/
theorem erdos_problem_183 :
    Tendsto (fun k : ℕ => (multicolorRamseyTriangle k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop :=
  sorry

/-- The recorded answer refutes the input's statement that the limit exists and is finite
(PROVED in Lean). -/
theorem erdos_problem_183.not_finite_of_tendsto
    (h : Tendsto (fun k : ℕ => (multicolorRamseyTriangle k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
      atTop atTop) :
    ¬ ∃ L : ℝ,
      Tendsto (fun k : ℕ => (multicolorRamseyTriangle k : ℝ) ^ ((1 : ℝ) / (k : ℝ)))
        atTop (nhds L) := by
  rintro ⟨L, hL⟩
  exact not_tendsto_nhds_of_tendsto_atTop h L hL

/-- With no colours, `Fin 1` already has no colouring (the diagonal must be coloured too), so the
definition gives `R(3;0) = 1` (PROVED in Lean). -/
theorem erdos_problem_183.multicolorRamseyTriangle_zero : multicolorRamseyTriangle 0 = 1 := by
  unfold multicolorRamseyTriangle
  have h1 : (1 : ℕ) ∈ {n : ℕ | ∀ (c : Fin n → Fin n → Fin 0), (∀ i j, c i j = c j i) →
      ∃ (a b d : Fin n), a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d} := by
    intro c _
    exact (c 0 0).elim0
  refine le_antisymm (Nat.sInf_le h1) (le_csInf ⟨1, h1⟩ fun n hn => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · obtain ⟨a, -⟩ := hn (fun a _ => a.elim0) (fun i _ => i.elim0)
    exact a.elim0
  · exact hpos

/-- With one colour, `R(3;1) = 3` (PROVED in Lean). -/
theorem erdos_problem_183.multicolorRamseyTriangle_one : multicolorRamseyTriangle 1 = 3 := by
  unfold multicolorRamseyTriangle
  have h3 : (3 : ℕ) ∈ {n : ℕ | ∀ (c : Fin n → Fin n → Fin 1), (∀ i j, c i j = c j i) →
      ∃ (a b d : Fin n), a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ c a b = c a d ∧ c a b = c b d} := by
    intro c _
    exact ⟨0, 1, 2, by decide, by decide, by decide, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  refine le_antisymm (Nat.sInf_le h3) (le_csInf ⟨3, h3⟩ fun n hn => ?_)
  obtain ⟨a, b, d, hab, had, hbd, -⟩ := hn (fun _ _ => 0) (fun _ _ => rfl)
  have h1 : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have h2 : a.val ≠ d.val := fun h => had (Fin.ext h)
  have h3 : b.val ≠ d.val := fun h => hbd (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := d.isLt
  omega

/-- For this definition the page's recursion $R(3;k)\le2+k(R(3;k-1)-1)$ fails at `k = 1`, because
`R(3;0) = 1` here (PROVED in Lean). -/
theorem erdos_problem_183.variants.recursion_fails_at_one :
    ¬ multicolorRamseyTriangle 1 ≤ 2 + 1 * (multicolorRamseyTriangle 0 - 1) := by
  rw [erdos_problem_183.multicolorRamseyTriangle_zero, erdos_problem_183.multicolorRamseyTriangle_one]
  decide

/-- The page's pigeonhole recursion (SOLVED; not proved here), for `k ≥ 2`. -/
theorem erdos_problem_183.variants.recursion (k : ℕ) (hk : 2 ≤ k) :
    multicolorRamseyTriangle k ≤ 2 + k * (multicolorRamseyTriangle (k - 1) - 1) :=
  sorry

/-- The page's upper bound $R(3;k)\le\lceil e\,k!\rceil$ for `k ≥ 1` (SOLVED; not proved here). -/
theorem erdos_problem_183.variants.upper (k : ℕ) (hk : 1 ≤ k) :
    multicolorRamseyTriangle k ≤ ⌈Real.exp 1 * (k.factorial : ℝ)⌉₊ :=
  sorry

/-- The lower bound $R(3;k)\ge380^{k/5}-O(1)$ of [ACPPRT21] (SOLVED; not proved here). -/
theorem erdos_problem_183.variants.acpprt :
    ∃ C : ℝ, ∀ k : ℕ, (380 : ℝ) ^ ((k : ℝ) / 5) - C ≤ (multicolorRamseyTriangle k : ℝ) :=
  sorry

/-- The explicit lower bound recorded by upstream for [OpenAI26] (SOLVED per upstream; not proved
or checked here): $R(3;k)\geq\bigl(k^{1/3}/(6e^{38}\log k)\bigr)^k$ for `k ≥ 2`. It implies the
main theorem. -/
theorem erdos_problem_183.variants.openai_lower_bound :
    ∀ k : ℕ, 2 ≤ k →
      (((1 : ℝ) / (6 * Real.exp 38)) * (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (multicolorRamseyTriangle k : ℝ) :=
  sorry

end
