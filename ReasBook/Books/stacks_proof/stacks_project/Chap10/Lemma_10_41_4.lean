import Mathlib.Tactic.Recall
import stacks_proof.stacks_project.Chap10.Definition_10_41_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} {T : Type w}
variable [CommRing R] [CommRing S] [CommRing T]
variable [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]

/- Lemma 10.41.4 (1): if `R → S` and `S → T` satisfy going down, then `R → T` satisfies going
down. This is exactly the canonical mathlib theorem `Algebra.HasGoingDown.trans`. -/
recall Algebra.HasGoingDown.trans

/- Lemma 10.41.4 (2): by Definition 10.41.1, going up for `R → S` is the specializing-map
property of `PrimeSpectrum.comap (algebraMap R S)`. Since `PrimeSpectrum.comap (algebraMap R T)` is
the composite of `PrimeSpectrum.comap (algebraMap S T)` and `PrimeSpectrum.comap (algebraMap R S)`,
the source-facing stability statement is the specialization of the canonical theorem
`SpecializingMap.comp` to these spectrum maps. -/
#check
  (show SpecializingMap (comap (algebraMap R S)) →
      SpecializingMap (comap (algebraMap S T)) →
      SpecializingMap (comap (algebraMap R T)) from
    fun hRS hST ↦ by
      simpa [Function.comp, comap_comp, IsScalarTower.algebraMap_eq R S T] using
        SpecializingMap.comp hST hRS)

end
