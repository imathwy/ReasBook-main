import Mathlib
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Monoidal.Internal.Module
import Mathlib.CategoryTheory.Monoidal.Transport
import stacks_proof.stacks_project.Chap15.Proposition_15_90_16
import stacks_proof.stacks_project.Chap15.Theorem_15_90_18
import stacks_proof.stacks_project.Chap15.Proposition_15_90_19

open CategoryTheory CategoryTheory.Limits ModuleCat
open scoped TensorProduct

noncomputable section

universe u w

private noncomputable abbrev formalGlueingCanEquivalence
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {t : ℕ} (f : Fin t → R) [Module.Flat R S]
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map)) :
    ModuleCat R ≌ Glue S f := by
  letI : Functor.IsEquivalence (formalGlueingCan S f) :=
    formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective f hquot
  exact (formalGlueingCan S f).asEquivalence

private abbrev FormalGlueingSingleTarget
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (f : R) :=
  Limits.CategoricalPullback
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
    (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f))

private noncomputable abbrev formalGlueingSingleEquivalence
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (f : R) [Module.Flat R S]
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) (Ideal.span ({f} : Set R)))
          (algebraMap R S)
          Ideal.le_comap_map)) :
    ModuleCat R ≌ FormalGlueingSingleTarget R S f := by
  letI : Functor.IsEquivalence (formalGlueingSingleFunctor S f) :=
    formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective f hquot
  exact (formalGlueingSingleFunctor S f).asEquivalence

private abbrev PrincipalAdicFGGlueTarget
    (R : Type u) [CommRing R] (f : R) [IsNoetherianRing R] :=
  let RHat := principalAdicCompletion f
  let RHatf := Localization.Away (algebraMap R RHat f)
  Limits.CategoricalPullback
    (FGModuleCat.extendScalars (algebraMap RHat RHatf))
    (FGModuleCat.extendScalars (Localization.awayMap (algebraMap R RHat) f))

private noncomputable abbrev principalAdicFormalGlueingFGEquivalence
    {R : Type u} [CommRing R] (f : R) [IsNoetherianRing R] :
    FGModuleCat R ≌ PrincipalAdicFGGlueTarget R f := by
  letI : Functor.IsEquivalence (principalAdicFormalGlueingFGFunctor f) :=
    principalAdicFormalGlueingFGFunctor_isEquivalence f
  exact (principalAdicFormalGlueingFGFunctor f).asEquivalence

section FormalGlueingEquivalences

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable [Module.Flat R S]
variable
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))

/- Domain-style sampling for Remark 15.90.20:
- primary domain: formal glueing equivalences for module categories, together with the monoidal
  structures they transport and the induced tensor-built categories;
- sampled owner declarations:
  `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`,
  `formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective`,
  `principalAdicFormalGlueingFGFunctor_isEquivalence`,
  `CategoryTheory.Monoidal.transport`,
  `CategoryTheory.Equivalence.mapMon`,
  `ModuleCat.monModuleEquivalenceAlgebra`;
- best owner abstraction: the three canonical equivalences from Proposition `15.90.16`,
  Theorem `15.90.18`, and Proposition `15.90.19`; the tensor and algebra statements should be
  derived from those equivalences rather than exposed only as four independent objectwise tests;
- primitive data: the formal-glueing functors themselves, together with the flatness and
  quotient-bijectivity hypotheses, or the Noetherian completion hypothesis in the principal-adic
  case;
- derived API: transported monoidal structures on the glueing-side targets, induced equivalences on
  monoid objects, induced algebra equivalences when the source is `ModuleCat`, and the companion
  module-property reflection criteria below.

Source/core/bridge triage:
- `source-facing`: Remark `15.90.20` is about the actual equivalences from `15.90.16/18/19`,
  their preservation of the listed module properties, and their compatibility with tensor
  products;
- `core/canonical`: `Functor.IsEquivalence`, `Functor.asEquivalence`, `Monoidal.transport`,
  `Equivalence.mapMon`, `ModuleCat.monModuleEquivalenceAlgebra`, and the monoidal owner on
  `FGModuleCat`;
- `bridge/view`: the transported monoidal structures on the glueing-side target categories and the
  resulting monoid/algebra comparison functors.
-/

/- Remark 15.90.20, Proposition 15.90.16 monoidal form: direct canonical reuse of the
transported monoidal equivalence attached to the source-facing equivalence from
`formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`. -/
#check (Monoidal.equivalenceTransported (formalGlueingCanEquivalence f hquot) :
  ModuleCat R ≌ Monoidal.Transported (formalGlueingCanEquivalence f hquot))

/- Remark 15.90.20, Proposition 15.90.16 monoid-object form: direct canonical reuse of
`Equivalence.mapMon` applied to the transported formal-glueing equivalence. -/
#check ((Monoidal.equivalenceTransported (formalGlueingCanEquivalence f hquot)).symm.mapMon.symm :
  Mon (ModuleCat R) ≌ Mon (Monoidal.Transported (formalGlueingCanEquivalence f hquot)))

/- Remark 15.90.20, Proposition 15.90.16 algebra form: direct reuse of
`monModuleEquivalenceAlgebra` together with the induced monoid-object equivalence above. -/
#check (monModuleEquivalenceAlgebra.symm.trans
    ((Monoidal.equivalenceTransported (formalGlueingCanEquivalence f hquot)).symm.mapMon.symm) :
  AlgCat R ≌ Mon (Monoidal.Transported (formalGlueingCanEquivalence f hquot)))

end FormalGlueingEquivalences

section SingleFormalGlueingEquivalences

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.Flat R S]
variable (f : R)
variable
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) (Ideal.span ({f} : Set R)))
          (algebraMap R S)
          Ideal.le_comap_map))

/- Remark 15.90.20, Theorem 15.90.18 monoidal form: direct canonical reuse of the transported
monoidal equivalence attached to the single formal-glueing equivalence. -/
#check (Monoidal.equivalenceTransported (formalGlueingSingleEquivalence f hquot) :
  ModuleCat R ≌ Monoidal.Transported (formalGlueingSingleEquivalence f hquot))

/- Remark 15.90.20, Theorem 15.90.18 monoid-object form: direct canonical reuse of
`Equivalence.mapMon` applied to the transported single formal-glueing equivalence. -/
#check ((Monoidal.equivalenceTransported (formalGlueingSingleEquivalence f hquot)).symm.mapMon.symm :
  Mon (ModuleCat R) ≌ Mon (Monoidal.Transported (formalGlueingSingleEquivalence f hquot)))

/- Remark 15.90.20, Theorem 15.90.18 algebra form: direct reuse of
`monModuleEquivalenceAlgebra` together with the induced monoid-object equivalence above. -/
#check (monModuleEquivalenceAlgebra.symm.trans
    ((Monoidal.equivalenceTransported (formalGlueingSingleEquivalence f hquot)).symm.mapMon.symm) :
  AlgCat R ≌ Mon (Monoidal.Transported (formalGlueingSingleEquivalence f hquot)))

end SingleFormalGlueingEquivalences

section PrincipalAdicFormalGlueing

variable {R : Type u} [CommRing R] (f : R) [IsNoetherianRing R]

/- Remark 15.90.20, Proposition 15.90.19 monoidal form: direct canonical reuse of the
transported monoidal equivalence attached to `principalAdicFormalGlueingFGFunctor_isEquivalence`.
-/
#check (Monoidal.equivalenceTransported (principalAdicFormalGlueingFGEquivalence f) :
  FGModuleCat R ≌ Monoidal.Transported (principalAdicFormalGlueingFGEquivalence f))

/- Remark 15.90.20, Proposition 15.90.19 monoid-object form: direct canonical reuse of
`Equivalence.mapMon` applied to the transported finitely generated formal-glueing equivalence. -/
#check ((Monoidal.equivalenceTransported (principalAdicFormalGlueingFGEquivalence f)).symm.mapMon.symm :
  Mon (FGModuleCat R) ≌ Mon (Monoidal.Transported (principalAdicFormalGlueingFGEquivalence f)))

end PrincipalAdicFormalGlueing

section ModulePropertyCriteria

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {t : ℕ} (f : Fin t → R)
variable [Module.Flat R S]
variable
    (hquot :
      let I : Ideal R := Ideal.span (Set.range f)
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) I)
          (algebraMap R S)
          Ideal.le_comap_map))

local notation "Away" => LocalizedModule.Away

variable {M : Type w} [AddCommMonoid M] [Module R M]

-- Proof sketch: Proposition `15.90.16` identifies `Mod_R` with the formal glueing category for
-- the data `(R → S, f₁, \ldots, fₜ)`. The cited faithfully flat ascent/descent results for
-- finite generation, finite presentation, flatness, and projectivity then translate each module
-- property on `M` into the same property on the base-change module `S ⊗[R] M` together with all
-- localizations `Away (f i) M`.
/-- Remark 15.90.20, finite case: under the hypotheses of Proposition `15.90.16`, an `R`-module
`M` is finite if and only if its base change `S ⊗[R] M` is finite over `S` and every
localization `Away (f i) M` is finite over `Localization.Away (f i)`. This is the module-property
companion to the owner equivalence and its monoidal consequences above. -/
@[stacks 05EU]
theorem moduleFinite_iff_finite_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.Finite R M ↔
      Module.Finite S (S ⊗[R] M) ∧
        ∀ i : Fin t, Module.Finite (Localization.Away (f i)) (Away (f i) M) := by
  sorry

/-- Remark 15.90.20, finite-presentation case: under the same hypotheses, an `R`-module `M` is
finitely presented if and only if `S ⊗[R] M` is finitely presented over `S` and every
localization `Away (f i) M` is finitely presented over `Localization.Away (f i)`. -/
@[stacks 05EU]
theorem
    moduleFinitePresentation_iff_finitePresentation_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.FinitePresentation R M ↔
      Module.FinitePresentation S (S ⊗[R] M) ∧
        ∀ i : Fin t,
          Module.FinitePresentation (Localization.Away (f i)) (Away (f i) M) := by
  sorry

/-- Remark 15.90.20, flat case: under the same hypotheses, an `R`-module `M` is flat if and only
if `S ⊗[R] M` is flat over `S` and every localization `Away (f i) M` is flat over
`Localization.Away (f i)`. -/
@[stacks 05EU]
theorem moduleFlat_iff_flat_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.Flat R M ↔
      Module.Flat S (S ⊗[R] M) ∧
        ∀ i : Fin t, Module.Flat (Localization.Away (f i)) (Away (f i) M) := by
  sorry

/-- Remark 15.90.20, projective case: under the same hypotheses, an `R`-module `M` is projective
if and only if `S ⊗[R] M` is projective over `S` and every localization `Away (f i) M` is
projective over `Localization.Away (f i)`. -/
@[stacks 05EU]
theorem moduleProjective_iff_projective_tensor_and_localizedAway_of_flat_of_quotientMap_bijective :
    Module.Projective R M ↔
      Module.Projective S (S ⊗[R] M) ∧
        ∀ i : Fin t, Module.Projective (Localization.Away (f i)) (Away (f i) M) := by
  sorry

end ModulePropertyCriteria
