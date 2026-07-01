import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Flat.Basic
import stacks_project.Chap04.Definition_4_31_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

section

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/- Domain-style sampling for Theorem 15.90.18:
- primary domain: single-element formal glueing for module categories, expressed as a categorical
  pullback over the localization square `R → S`, `R_f → S_f`;
- sampled owner declarations:
  `Localization.awayMap`,
  `CategoricalPullback.CatCommSqOver`,
  `CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback`,
  `formalGlueingCan_isEquivalence_of_flat_of_quotientMap_bijective`;
- best owner abstraction:
  the public source-facing object in this file is the single-element pullback functor
  `formalGlueingSingleFunctor`; the localization map itself is already canonically owned by
  `Localization.awayMap`, while the comparison isomorphism and commutative-square packaging are
  bridge-level implementation data for producing the pullback functor;
- primitive data:
  the ring map `Localization.awayMap (algebraMap R S) f`, the induced commutative square of ring
  homomorphisms, and the two extension-of-scalars functors into `ModuleCat`;
- derived API:
  the pullback functor `formalGlueingSingleFunctor` and the equivalence statement under flatness
  and quotient-bijectivity.

Source/core/bridge triage:
- `source-facing`: `formalGlueingSingleFunctor` and
  `formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective`;
- `core/canonical`: `Localization.awayMap`, `CatCommSqOver`, and `CategoricalPullback`;
- `bridge/view`: the commutative-square theorem and the internal comparison/square data below.
-/

/-- The commutative square of ring maps underlying the single-element formal glueing functor. -/
-- Proof sketch: both composites are the canonical map `R → S_f`; evaluate on `r : R` and use the
-- defining formula for `Localization.awayMap`.
theorem formalGlueingSingleAwaySquare_commutes (f : R) :
    (algebraMap S (Localization.Away (algebraMap R S f))).comp (algebraMap R S) =
      (Localization.awayMap (algebraMap R S) f).comp
        (algebraMap R (Localization.Away f)) := sorry

/-- The comparison isomorphism between the two ways of extending scalars from `R` to `S_f` in the
single-element formal glueing square. -/
private noncomputable def formalGlueingSingleComparison (f : R) :
    ModuleCat.extendScalars (algebraMap R S) ⋙
        ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))) ≅
      ModuleCat.extendScalars (algebraMap R (Localization.Away f)) ⋙
        ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f) :=
  (ModuleCat.extendScalarsComp (algebraMap R S)
      (algebraMap S (Localization.Away (algebraMap R S f)))).symm ≪≫
    eqToIso
      (congrArg
        (fun u ↦ ModuleCat.extendScalars u)
        (formalGlueingSingleAwaySquare_commutes f)) ≪≫
    ModuleCat.extendScalarsComp
      (algebraMap R (Localization.Away f))
      (Localization.awayMap (algebraMap R S) f)

/-- The commutative-square datum whose associated categorical-pullback functor is the
single-element formal glueing functor. -/
private noncomputable def formalGlueingSingleSquare (f : R) :
    CategoricalPullback.CatCommSqOver
      (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
      (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f))
      (ModuleCat R) where
  fst := ModuleCat.extendScalars (algebraMap R S)
  snd := ModuleCat.extendScalars (algebraMap R (Localization.Away f))
  iso := formalGlueingSingleComparison f

/-- The canonical functor sending an `R`-module `M` to the triple
`(M ⊗[R] S, M_f, can)` in the categorical pullback
`Mod_S ×_{Mod_{S_f}} Mod_{R_f}`. -/
noncomputable abbrev formalGlueingSingleFunctor (S : Type u) [CommRing S] [Algebra R S] (f : R) :
    ModuleCat R ⥤
      CategoricalPullback
        (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
        (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f)) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (ModuleCat.extendScalars (algebraMap S (Localization.Away (algebraMap R S f))))
    (ModuleCat.extendScalars (Localization.awayMap (algebraMap R S) f))
    (ModuleCat R)).obj
    (formalGlueingSingleSquare f)

-- Proof sketch: identify the target pullback category with the category of triples
-- `(M', M₁, α₁)` from Example `4.31.3`, then specialize Proposition `15.90.16` to the one-element
-- family `f : Fin 1 → R` given by the constant value `f`.
/-- Theorem 15.90.18: if `R → S` is flat and the induced quotient map
`R / fR → S / fS` is bijective, then the canonical functor
`Mod_R ⥤ Mod_S ×_{Mod_{S_f}} Mod_{R_f}` sending `M` to `(M ⊗[R] S, M_f, can)` is an
equivalence. -/
theorem formalGlueingSingleFunctor_isEquivalence_of_flat_of_quotientMap_bijective
    (f : R) [Module.Flat R S]
    (hquot :
      Function.Bijective
        (Ideal.quotientMap
          (Ideal.map (algebraMap R S) (Ideal.span ({f} : Set R)))
          (algebraMap R S)
          Ideal.le_comap_map)) :
    Functor.IsEquivalence (formalGlueingSingleFunctor S f) := sorry

end
