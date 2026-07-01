import Mathlib
import stacks_project.Chap10.Lemma_10_72_2
import stacks_project.Chap10.Definition_10_102_5
import stacks_project.Chap10.Situation_10_102_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory HomologicalComplex
open RingTheory

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

/- Domain triage:
* primary domain: Buchsbaum-Eisenbud acyclicity criteria in local commutative algebra, where the
  minor ideals are controlled by regular sequences and equivalently by depth;
* sampled owner declarations of the same kind: `Ideal.depth`,
  `Ideal.depth_eq_sSup_lengths_of_isWeaklyRegular`,
  `Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth`, and `moduleDepth`;
* best owner abstraction: `Ideal.depth` is the core/canonical owner for the ideal-theoretic lower
  bound, while Proposition `10.102.9` itself is `source-facing` and should keep the textbook
  regular-sequence clause as its main public statement;
* layer: the depth inequality is only the `bridge/view` reformulation of the source-facing
  Buchsbaum-Eisenbud criterion.
* primitive vs derived split: the primitive data are the complex, its differentials, and the
  rank-minor ideals `I(C.diffAt i)`; the owner depth inequalities are derived bridge API for those
  source-facing regular-sequence conditions.
-/

namespace FiniteFreeComplex

/-- A bounded finite free complex is exact in the positive degrees `e, …, 1` when its underlying
chain complex is exact at every degree `1, …, e`. -/
def ExactInPositiveDegrees (C : _root_.FiniteFreeComplex R e) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ e → C.toChainComplex.ExactAt j

-- Proof sketch: for the forward implication, localize at the associated primes and apply the
-- depth-zero decomposition lemmas to deduce the alternating rank formulas and that each minor ideal
-- avoids every associated prime; prime avoidance then produces a nonzerodivisor allowing
-- induction on the length of the complex to build the required regular sequences. For the reverse
-- implication, localize at nonmaximal primes to invoke the inductive hypothesis on dimension,
-- deduce that any homology is supported only at the maximal ideal, and then apply the acyclicity
-- lemma using the depth bounds supplied by the regular sequences in the minor ideals.
/-- Proposition 10.102.9: for a bounded finite free complex over a local Noetherian ring, exactness
in degrees `e, …, 1` is equivalent to the Buchsbaum-Eisenbud criterion that each differential has
the expected alternating rank and its rank-minor ideal is either the unit ideal or contains a
regular sequence of the corresponding length. -/
theorem exactInPositiveDegrees_iff_buchsbaumEisenbud_criterion
    (C : _root_.FiniteFreeComplex R e) :
    C.ExactInPositiveDegrees ↔
      ∀ i : Fin e,
        (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
          (I(C.diffAt i) = ⊤ ∨
            ∃ rs : List R,
              RingTheory.Sequence.IsRegular R rs ∧
                Ideal.ofList rs ≤ I(C.diffAt i) ∧ rs.length = i.1 + 1) := sorry

/-- Companion bridge: Proposition `10.102.9` rewritten through the owner depth condition on the
rank-minor ideals. -/
theorem exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion
    (C : _root_.FiniteFreeComplex R e) :
    C.ExactInPositiveDegrees ↔
      ∀ i : Fin e,
        (LinearMap.exteriorRank (C.diffAt i) : ℤ) = C.alternatingRank i ∧
          (i.1 + 1 : WithTop ℕ) ≤ (I(C.diffAt i)).depth R := by
  constructor
  · intro hExact i
    rcases (exactInPositiveDegrees_iff_buchsbaumEisenbud_criterion C).mp hExact i with
      ⟨hrank, hcriterion⟩
    refine ⟨hrank, ?_⟩
    exact (Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth (I(C.diffAt i))
      (i.1 + 1)).mp hcriterion
  · intro hDepth
    refine (exactInPositiveDegrees_iff_buchsbaumEisenbud_criterion C).2 ?_
    intro i
    rcases hDepth i with ⟨hrank, hdepth⟩
    refine ⟨hrank, ?_⟩
    exact (Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth (I(C.diffAt i))
      (i.1 + 1)).mpr hdepth

end FiniteFreeComplex

end
