import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.LiminfLimsup
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Filter

/--
Erdős Problem #1051 [ErGr80,p.64] [Er88c,p.106]:

Is it true that if 1 ≤ a₁ < a₂ < ⋯ is a sequence of integers with
  liminf aₙ^{1/2ⁿ} > 1
then
  ∑ 1/(aₙ · aₙ₊₁)
is irrational?

Solved in the affirmative by Aletheia [Fe26]. The problem page status is
PROVED (LEAN): "This has been solved in the affirmative and the proof verified
in Lean." The authoritative formal statement lives upstream in
google-deepmind/formal-conjectures (FormalConjectures/ErdosProblems/1051.lean).

In [Er88c] Erdős notes this is true if aₙ → ∞ 'rapidly'. In [ErGr80] they
further ask 'what the strongest theorem of this type' would be. Barreto, Kang,
Kim, Kovač, and Zhang [BKKKZ26] extended [Fe26] and essentially give a complete
answer in terms of the golden ratio φ = (1+√5)/2: see the variants below.

Encoding note: the growth hypothesis is stated as "∃ c > 1 with aₙ^{1/2ⁿ} ≥ c
eventually", which is exactly "liminf aₙ^{1/2ⁿ} > 1" with the liminf read in
the extended reals, as the source intends. An ℝ-valued `Filter.liminf … > 1`
hypothesis would silently be *false* (Mathlib junk value 0 for `sSup` of a set
unbounded above) whenever aₙ^{1/2ⁿ} → ∞, wrongly excluding exactly the
fastest-growing sequences.

References:
- [ErGr80] Erdős, P. and Graham, R., Old and new problems and results in
  combinatorial number theory. Monographies de L'Enseignement Mathématique
  (1980).
- [Er88c] Erdős, P., On the irrationality of certain series: problems and
  results. New advances in transcendence theory (Durham, 1986) (1988), 102–109.
- [Fe26] T. Feng et al., Semi-Autonomous Mathematics Discovery with Gemini: A
  Case Study on the Erdős Problems. arXiv:2601.22401 (2026).
- [BKKKZ26] K. Barreto, J. Kang, S.-H. Kim, V. Kovač, and S. Zhang,
  Irrationality of rapidly converging series: a problem of Erdős and Graham.
  arXiv:2601.21442 (2026).
-/
theorem erdos_problem_1051
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 1 ≤ a n)
    (ha_strict_mono : StrictMono a)
    (ha_growth : ∃ c : ℝ, 1 < c ∧
      ∀ᶠ n in atTop, c ≤ (a n : ℝ) ^ ((2 : ℝ) ^ (n : ℝ))⁻¹) :
    Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
  sorry

/--
Erdős [Er88c,p.106] notes the conclusion of #1051 holds if aₙ → ∞ 'rapidly';
following the upstream formal-conjectures interpretation
(`erdos_1051.variants.rapid_growth`), 'rapidly' is encoded as
aₙ₊₁ ≥ C·aₙ² for some constant C > 0.
-/
theorem erdos_problem_1051.variants.rapid_growth
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 1 ≤ a n)
    (ha_strict_mono : StrictMono a)
    (ha_rapid : ∃ C : ℝ, 0 < C ∧ ∀ n, C * (a n : ℝ) ^ 2 ≤ (a (n + 1) : ℝ)) :
    Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
  sorry

/--
Barreto, Kang, Kim, Kovač, and Zhang [BKKKZ26], extending [Fe26]: if
φ = (1+√5)/2 is the golden ratio and 1 ≤ a₁ < a₂ < ⋯ is a monotonically
increasing sequence of integers such that limsup aₙ^{1/φⁿ} = ∞, then
∑ 1/(aₙ·aₙ₊₁) is irrational.

Encoding note: "limsup = ∞" is encoded as "frequently ≥ M, for every M" — an
ℝ-valued `Filter.limsup` would return the junk value 0 on precisely such
sequences.
-/
theorem erdos_problem_1051.variants.golden_ratio_limsup
    (a : ℕ → ℕ)
    (ha_pos : ∀ n, 1 ≤ a n)
    (ha_strict_mono : StrictMono a)
    (ha_growth : ∀ M : ℝ, ∃ᶠ n in atTop,
      M ≤ (a n : ℝ) ^ (((1 + Real.sqrt 5) / 2) ^ (n : ℝ))⁻¹) :
    Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
  sorry

/--
Conversely [BKKKZ26]: for any 1 < C < ∞ there exists a sequence of integers
1 ≤ a₁ < a₂ < ⋯ with lim aₙ^{1/φⁿ} = C for which ∑ 1/(aₙ·aₙ₊₁) is rational
(φ = (1+√5)/2 the golden ratio).

(The exponent here is 0-indexed while the source is 1-indexed; since C ↦ C^φ
is a bijection of (1, ∞), the ∀-C statement is equivalent to its 1-indexed
form.)
-/
theorem erdos_problem_1051.variants.golden_ratio_converse
    (C : ℝ) (hC : 1 < C) :
    ∃ a : ℕ → ℕ, (∀ n, 1 ≤ a n) ∧ StrictMono a ∧
      Tendsto (fun n => (a n : ℝ) ^ (((1 + Real.sqrt 5) / 2) ^ (n : ℝ))⁻¹)
        atTop (nhds C) ∧
      ¬ Irrational (∑' n, (1 : ℝ) / ((a n : ℝ) * (a (n + 1) : ℝ))) :=
  sorry
