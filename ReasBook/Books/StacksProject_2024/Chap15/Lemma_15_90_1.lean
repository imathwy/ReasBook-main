import Mathlib.Data.List.TFAE
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import stacks_project.Chap15.Lemma_15_89_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ModuleCat

universe u v

noncomputable section

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain-style sampling:
- primary domain: ideal extension and change of rings on module categories, with canonical owner
  abstractions given by `Ideal.map`, `Ideal.quotientMap`, `ModuleCat (R ⧸ I)`, `extendScalars`,
  and the canonical `ObjectProperty` view `fun M ↦ Module.IsIdealPowerTorsion I M`;
- inspected same-domain owners:
  `Ideal.map`,
  `Ideal.quotientMap`,
  `extendScalars`,
  `restrictScalars`,
  `ModuleCat (R ⧸ I)`,
  `ObjectProperty.lift`,
  `Module.IsIdealPowerTorsion`;
- best owner abstraction: the ideal-side construction is the canonical owner `Ideal.map φ I`; for
  modules annihilated by `I`, the owner category is `ModuleCat (R ⧸ I)` and base change is
  `extendScalars` along the quotient map `R ⧸ I →+* S ⧸ Ideal.map φ I`; the `I`-power torsion
  clause remains the source-facing restricted functor
  `(ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)`,
  while the bridge to the target torsion full subcategory is the canonical restricted functor
  `idealPowerTorsionRestrictedBaseChange φ I` built from `ObjectProperty.lift`.

Source/core/bridge triage:
- `source-facing`: the TFAE for faithful base change on modules cut out by `I`;
- `core/canonical`: `Ideal.map φ I` on ideals and
  `extendScalars (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map)` on quotient-module
  categories, together with the direct restricted base-change functor
  `(ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)`;
- `bridge/view`: the induced quotient map `R ⧸ I → S ⧸ IS` and the restricted functor
  `idealPowerTorsionRestrictedBaseChange φ I` into the target torsion full subcategory.
-/

/-- Extension of scalars along `φ` carries `I`-power torsion modules to `IS`-power torsion
modules. -/
theorem Module.IsIdealPowerTorsion.extendScalars
    (φ : R →+* S) (I : Ideal R) (M : ModuleCat R)
    (hM : Module.IsIdealPowerTorsion I M) :
    Module.IsIdealPowerTorsion (Ideal.map φ I) ((extendScalars φ).obj M) :=
  sorry

/-- Base change along `φ` on the full subcategories of `I`-power torsion and `IS`-power torsion
modules. -/
noncomputable abbrev idealPowerTorsionRestrictedBaseChange
    (φ : R →+* S) (I : Ideal R) :
    ObjectProperty.FullSubcategory (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⥤
      ObjectProperty.FullSubcategory
        (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M) :=
  ObjectProperty.lift
    (fun M : ModuleCat S ↦ Module.IsIdealPowerTorsion (Ideal.map φ I) M)
    (ObjectProperty.ι (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) ⋙ extendScalars φ)
    (fun M ↦ Module.IsIdealPowerTorsion.extendScalars φ I M.obj M.property)

-- Proof sketch: identify the quotient map `R ⧸ I →+* S ⧸ IS` with the base change of `φ`
-- along `R → R ⧸ I`, so Lemmas `10.39.7` and `10.39.16` give the equivalence of the faithfully
-- flat and spectrum-surjective quotient conditions. Clause `(3)` is the canonical quotient-module
-- formulation: for modules annihilated by `I`, work in `ModuleCat (R ⧸ I)` and rewrite base
-- change along `φ` as extension of scalars along `R ⧸ I →+* S ⧸ IS`, then apply Lemma `10.39.14`.
-- Clause `(4)` is the canonical restricted base-change functor
-- `idealPowerTorsionRestrictedBaseChange φ I` on the full subcategory of `I`-power torsion
-- modules. The implication from `I`-power torsion modules to `I`-annihilated
-- modules is immediate, and the converse is obtained by filtering an `I`-power torsion module by
-- its submodules annihilated by powers of `I` and using preservation of colimits by tensor
-- product.
/-- Lemma 15.90.1: for a ring map `φ : R →+* S` and an ideal `I ⊆ R`, the following are
equivalent: `φ` is flat and the induced quotient map `R ⧸ I → S ⧸ IS` is faithfully flat; `φ` is
flat and `Spec (S ⧸ IS) → Spec (R ⧸ I)` is surjective; `φ` is flat and extension of scalars along
`R ⧸ I → S ⧸ IS` is faithful on quotient-ring modules, equivalently on `R`-modules annihilated by
`I`; and `φ` is flat and base change along `φ` is faithful on `I`-power torsion `R`-modules. -/
theorem flat_quotientFaithfullyFlat_tfae_baseChangeFaithfulOnIdealTorsionModules
    (φ : R →+* S) (I : Ideal R) :
    List.TFAE
      [ φ.Flat ∧ (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map).FaithfullyFlat
      , φ.Flat ∧
          Function.Surjective
            (PrimeSpectrum.comap (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map))
      , φ.Flat ∧
          (extendScalars (Ideal.quotientMap (Ideal.map φ I) φ Ideal.le_comap_map)).Faithful
      , φ.Flat ∧
          (idealPowerTorsionRestrictedBaseChange φ I).Faithful
      ] := sorry

end
