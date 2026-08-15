import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Ordinal

noncomputable section
open Ordinal Cardinal

namespace Erdos1169

/-- ω₁, the first uncountable ordinal. -/
noncomputable def omega1 : Ordinal := (aleph 1).ord

/-- The ordinal partition relation α → (β, γ)² for 2-colorings of pairs.
    For every 2-coloring of the pairs of ordinals below α, there is either
    a homogeneous set of order type β in color 0, or a homogeneous set of
    order type γ in color 1. Formalized via strictly monotone embeddings:
    a subset of order type β corresponds to a strictly monotone function
    from {x | x < β} to {x | x < α}. -/
def OrdinalPartitionPair (α β γ : Ordinal) : Prop :=
  ∀ f : {x : Ordinal // x < α} → {x : Ordinal // x < α} → Bool,
    (∃ g : {x : Ordinal // x < β} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < β}, i < j → f (g i) (g j) = true) ∨
    (∃ g : {x : Ordinal // x < γ} → {x : Ordinal // x < α},
      StrictMono g ∧
      ∀ i j : {x : Ordinal // x < γ}, i < j → f (g i) (g j) = false)

/--
Erdős Problem #1169 (Erdős and Hajnal):

Is it true that, for all finite k ≥ 3,
  ω₁² ↛ (ω₁², k)²?

That is, for every natural number k ≥ 3, there exists a 2-coloring of the pairs
of ordinals below ω₁² such that no subset of order type ω₁² is monochromatic
in the first color and no subset of order type k is monochromatic in the
second color.

Note: The restriction to k ≥ 3 is essential. For k ≤ 2, the partition relation
OrdinalPartitionPair(ω₁², ω₁², k) is trivially true:
- k = 0: The domain {x < 0} is empty, making the monochromaticity condition vacuous.
- k = 1: A singleton has no pairs i < j, so monochromaticity is vacuous.
- k = 2: For any 2-coloring, the pigeonhole principle ensures both colors appear,
  satisfying the partition relation. The negation is provably false for k ≤ 2.

Hajnal proved this holds assuming the Continuum Hypothesis.
The problem is "not disprovable": open in ZFC, but true in some models.

Related: See Problem [592] for a similar question about countable ordinals.

Citation: [Va99, 7.85] — Hajnal and Larson, Partition relations (Handbook of Set Theory).
          [Ha71] — Hajnal's CH result (1971).

Tags: set theory, ramsey theory
-/
theorem erdos_1169 : answer(sorry) ↔
    ∀ k : ℕ, 3 ≤ k → ¬ OrdinalPartitionPair (omega1 ^ 2) (omega1 ^ 2) (↑k) := by
  sorry

end Erdos1169
