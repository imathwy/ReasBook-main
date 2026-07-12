import Mathlib.RingTheory.Ideal.Cotangent
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Ideal IsLocalRing

section

/-
Layering for this item:
* source-facing statement: a finite local ring homomorphism is surjective once the induced maps on
  residue fields and cotangent spaces are surjective and the target maximal ideal is finitely
  generated.
* core/canonical owners: `surjective_of_quotientMap_surjective_of_le_ring_jacobson`,
  `ResidueField.map`, and `Ideal.mapCotangent`.
* bridge/view: the residue-field and cotangent-space maps are the quotient maps to which the owner
  Nakayama criterion is applied.
-/

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

/-- Lemma 10.20.3: a finite local ring homomorphism is surjective if the target maximal ideal is
finitely generated, the induced map on residue fields is surjective, and the induced map on
cotangent spaces `CotangentSpace A → CotangentSpace B`, given by the canonical map
`mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
  (maximalIdeal_comap (algebraMap A B)).symm.le`, is surjective. -/
-- Proof sketch: apply
-- `surjective_of_quotientMap_surjective_of_le_ring_jacobson` from Lemma `10.20.1` to the
-- `A`-linear map `algebraMap A B`; surjectivity on residue fields identifies the needed quotient
-- map with `ResidueField.map (algebraMap A B)`. Apply the same owner theorem again to the induced
-- map `maximalIdeal A →ₗ[A] maximalIdeal B`; the quotient map in this second step is exactly the
-- canonical cotangent map `mapCotangent ...`, and `hfg` supplies the finite-generation input for
-- `maximalIdeal B`.
theorem surjective_of_localHom_finite_surjective_residueFieldMap_surjective_maximalIdealCotangentMap
    (hf : Module.Finite A B) (hfg : (maximalIdeal B).FG)
    (hres : Function.Surjective (ResidueField.map (algebraMap A B)))
    (hcot :
      Function.Surjective
        (mapCotangent (maximalIdeal A) (maximalIdeal B) (Algebra.ofId A B)
          (maximalIdeal_comap (algebraMap A B)).symm.le)) :
    Function.Surjective (algebraMap A B) := sorry

end
