import Mathlib
import StacksProject_2024.Chap15.Lemma_15_67_20
import StacksProject_2024.Chap15.Lemma_15_75_2
import StacksProject_2024.Chap15.Lemma_15_76_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

/- Domain-style sampling for Lemma 15.79.4:
- primary domain: perfect complexes in derived categories of commutative rings and their
  nilpotent-thickening base change;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `K ⊗[R]^L[(R ⧸ I)]`,
  `DerivedCategory.IsPerfect`,
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`;
- best owner abstraction:
  the source-facing statement already lives on the chapter's canonical base-change owner
  `derivedTensorWithAlgebra`, with public surface notation `K ⊗[R]^L[(R ⧸ I)]`;
- primitive vs. derived:
  primitive data are the commutative ring `R`, the nilpotent ideal `I`, and the object
  `K : D(R)`;
  the quotient perfectness hypothesis and the conclusion are derived API over the existing owners
  `derivedTensorWithAlgebra` and `DerivedCategory.IsPerfect`, so no extra public reduction package
  should be introduced;
- source/core/bridge triage:
  `source-facing`: perfectness descends from the derived quotient modulo a nilpotent ideal;
  `core/canonical`: `derivedTensorWithAlgebra` and `DerivedCategory.IsPerfect`;
  `bridge/view`: the notation `K ⊗[R]^L[(R ⧸ I)]` for the owner applied to `K`.
-/

-- Proof sketch: combine the pseudo-coherence descent theorem for nilpotent thickenings
-- (Lemma `15.76.4`) and the corresponding tor-amplitude descent theorem (Lemma `15.67.20`) with
-- the characterization of perfect objects from Lemma `15.75.2`.
/-- Lemma 15.79.4: let `R` be a commutative ring, let `I ⊆ R` be a nilpotent ideal, and let
`K ∈ D(R)`. If the derived reduction
`K \otimes_R^{\mathbf L} (R / I)` is perfect in `D(R / I)`, then `K` is perfect in `D(R)`. -/
theorem isPerfect_of_derivedTensorWithAlgebra_quotient_isPerfect_of_isNilpotent
    (K : DerivedCategory (ModuleCat.{u} R))
    (hbase : (K ⊗[R]^L[(R ⧸ I)]).IsPerfect) (hI : IsNilpotent I) :
    K.IsPerfect := by
  let Kbar : DerivedCategory (ModuleCat.{u} (R ⧸ I)) :=
    (derivedTensorWithAlgebra (algebraMap R (R ⧸ I))).obj K
  have hsurj : Function.Surjective (algebraMap R (R ⧸ I)) := by
    simpa using (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
  have hker :
      IsNilpotent (RingHom.ker (algebraMap R (R ⧸ I))) := by
    have hker_eq : RingHom.ker (algebraMap R (R ⧸ I)) = I := by
      ext x
      change Ideal.Quotient.mk I x = 0 ↔ x ∈ I
      rw [Ideal.Quotient.eq_zero_iff_mem]
    simpa [hker_eq] using hI
  have hbase' :=
    (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension Kbar).1
      (by simpa [Kbar] using hbase)
  refine (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension K).2 ?_
  refine ⟨?_, ?_⟩
  · exact
      (isPseudoCoherent_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
        hsurj hker K).1 hbase'.1
  · rcases (hasFiniteTorDimension_iff Kbar).1 hbase'.2 with ⟨a, b, hab⟩
    exact
      ((hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
        hsurj hker K a b).1 hab).hasFiniteTorDimension

end

end CategoryTheory
