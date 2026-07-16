import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_1
import StacksProject_2024.stacks_project.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Algebra

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {Sbar : Type v} [CommRing Sbar] [Algebra (R ⧸ I) Sbar]

-- Proof sketch: apply Lemma `10.136.15` to obtain a cover of `Spec S̄` by basic opens on which
-- the localization is a relative global complete intersection over `R ⧸ I`. For each such
-- localization, choose a presentation from Definition `10.136.5`, lift the defining equations to
-- `R`, form the corresponding quotient algebra over `R`, and then use Lemma `10.136.10` to shrink
-- once more so that this lift is itself a relative global complete intersection over `R`.
/-- Lemma 10.136.18: a syntomic `(R ⧸ I)`-algebra admits a unit-ideal cover by basic opens whose
localizations are reductions modulo `I` of relative global complete intersections over `R`. -/
theorem exists_relativeGlobalCompleteIntersection_lift_cover_of_quotient_syntomic
    (hSbar : (algebraMap (R ⧸ I) Sbar).Syntomic) :
    ∃ s : Set Sbar, Ideal.span s = ⊤ ∧
      ∀ g ∈ s, ∃ (S : Type (max u v)) (_ : CommRing S) (_ : Algebra R S)
        (_ : IsRelativeGlobalCompleteIntersection R S),
          Nonempty ((Localization.Away g) ≃ₐ[R ⧸ I] (S ⧸ Ideal.map (algebraMap R S) I)) := sorry

end

end Algebra
