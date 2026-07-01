import stacks_project.Chap15.Lemma_15_90_1
import stacks_project.Chap15.Lemma_15_89_9

-- Declarations for this item will be appended below by the statement pipeline.

open ModuleCat
open scoped TensorProduct

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling:
- primary domain: change of rings on module categories, especially the base-change unit and
  quotient maps modulo ideals;
- inspected same-domain owners:
  `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules`,
  `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`,
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`,
  `idealPowerTorsionRestrictedBaseChange`,
  `Module.IsIdealPowerTorsion`,
  `TensorProduct.mk`,
  `Ideal.quotientMap`;
- best owner abstraction: this file should stay a source-facing bridge theorem, but its ambient
  owner is the chapter theorem
  `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules` together with the
  module-level tensor base-change map `TensorProduct.mk R S M 1 : M →ₗ[R] S ⊗[R] M`; faithfulness
  on `I`-power torsion modules is carried by the chapter owner
  `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I`, and the quotient comparison
  `R ⧸ I → S ⧸ IS` is identified by the canonical tensor/quotient owner
  `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`; the textbook map `M → M ⊗[R] S` is only
  the tensor-symmetry view.

Source/core/bridge triage:
- `source-facing`: the bijectivity criterion for the canonical map `M → M ⊗[R] S` on ordinary
  `I`-power torsion `R`-modules;
- `core/canonical`: extension of scalars along `algebraMap R S`;
- `bridge/view`: the induced quotient map `R ⧸ I → S ⧸ IS` and the restricted base-change functor
  `idealPowerTorsionRestrictedBaseChange (algebraMap R S) I`.
-/

/-- If the canonical tensor base-change unit is bijective on every `I`-power torsion `R`-module,
then the induced quotient map `R ⧸ I → S ⧸ IS` is bijective. This is the source-facing forward
bridge used in Lemma `15.90.2`. -/
theorem quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion
    (I : Ideal R)
    (hbij : ∀ M : ModuleCat R,
      Module.IsIdealPowerTorsion I M →
        Function.Bijective (TensorProduct.mk R S M 1)) :
    Function.Bijective
      (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  -- Apply the pointwise tensor-unit bijectivity hypothesis to `R ⧸ I`, then identify
  -- `S ⊗[R] (R ⧸ I)` with `S ⧸ IS` via `quotIdealMapEquivTensorQuot`.
  sorry

/-- Lemma 15.90.2: under the flatness and faithful restricted base-change hypothesis supplied by
Lemma `15.90.1`, the following are equivalent: every `I`-power torsion `R`-module `M` is
unchanged by the canonical base-change unit `M → S ⊗[R] M`, and the induced map
`R ⧸ I → S ⧸ IS` is bijective. The forward implication is the atomic quotient-recovery theorem
`quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion`, while the converse
uses the chapter owners `idealPowerTorsionRestrictedBaseChange` and
`tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`. -/
theorem tensorBaseChange_bijective_iff_quotientMap_bijective_of_baseChangeFaithfulOnIdealPowerTorsion
    (I : Ideal R)
    (hflat : (algebraMap R S).Flat)
    (hfaithful : (idealPowerTorsionRestrictedBaseChange (algebraMap R S) I).Faithful) :
    (∀ M : ModuleCat R,
      Module.IsIdealPowerTorsion I M →
        Function.Bijective (TensorProduct.mk R S M 1)) ↔
    Function.Bijective
        (Ideal.quotientMap
        (I.map (algebraMap R S))
        (algebraMap R S)
        Ideal.le_comap_map) := by
  constructor
  · exact quotientMap_bijective_of_tensorBaseChange_bijective_on_idealPowerTorsion I
  · intro hquot M hM
    -- View the torsion statement through the chapter owner
    -- `flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules`, then combine
    -- the quotient-map hypothesis with the canonical base-change criterion from Lemma `15.89.9`.
    sorry

end
