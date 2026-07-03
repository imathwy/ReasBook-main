import Mathlib
import StacksProject_2024.Chap10.Proposition_10_102_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {e : ℕ}

namespace FiniteFreeComplex

/- Domain triage:
* primary domain: Buchsbaum-Eisenbud exactness criteria for bounded finite free complexes over a
  Noetherian local ring, with the threshold behavior of the rank-minor ideals `I(C.diffAt i)`;
* sampled owner declarations of the same kind:
  `FiniteFreeComplex.ExactInPositiveDegrees`,
  `FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_criterion`,
  `FiniteFreeComplex.exactInPositiveDegrees_iff_buchsbaumEisenbud_depth_criterion`, and
  `Ideal.eq_top_or_exists_regularSequence_of_length_iff_le_depth`;
* best owner abstraction: `ExactInPositiveDegrees` is the source-facing owner hypothesis, while
  `Ideal.depth` is the core/canonical owner controlling when a proper rank-minor ideal can no
  longer support the required regular sequences;
* layer: this remark remains `source-facing`, because the threshold conclusion is additional
  mathematical content, not just a restatement of the depth owner.

Primitive data are only the bounded finite free complex `C`, its displayed differentials
`C.diffAt i`, and the exactness owner `C.ExactInPositiveDegrees`. The depth inequalities for the
ideals `I(C.diffAt i)` are derived bridge API coming from Proposition `10.102.9`.
-/

-- Proof sketch: apply Proposition `10.102.9` to convert exactness into the Buchsbaum--Eisenbud
-- criterion. If some `I(C.diffAt j)` is not the unit ideal for arbitrarily large `j`, the
-- criterion gives arbitrarily long regular sequences contained in a proper ideal of the Noetherian
-- local ring, which is impossible. Conversely, once `I(C.diffAt j) = ⊤`, the tail complex ending
-- in `C.diffAt j = 0` forces every later minor ideal to be the unit ideal as in the remark.
/-- Remark 10.102.10: if the equivalent conditions of Proposition `10.102.9` hold for a bounded
finite free complex, then there is a threshold `j` such that the rank-minor ideal `I(C.diffAt i)`
is the unit ideal exactly for the differentials with index `i ≥ j`. -/
theorem rankMinorIdeal_eq_top_iff_ge_threshold
    (C : _root_.FiniteFreeComplex R e)
    (hExact : C.ExactInPositiveDegrees) :
    ∃ j : Fin (e + 1),
      ∀ i : Fin e,
        I(C.diffAt i) = ⊤ ↔ j ≤ i.castSucc := sorry

end FiniteFreeComplex

end
