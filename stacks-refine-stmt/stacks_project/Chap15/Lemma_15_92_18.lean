import Mathlib
import stacks_project.Chap15.Lemma_15_92_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A] {r : ℕ}

open DerivedCategory

local notation "DMod" => DerivedCategory (ModuleCat A)
variable (f : Fin r → A)

local notation "I" => Ideal.span (Set.range f)

/- Domain-style sampling for Lemma 15.92.18:
- primary domain: reflective full subcategories in the derived category, expressed through the
  canonical comparison map to the derived limit of the powered Koszul tensor tower and the
  resulting adjunction with the inclusion of derived-complete objects;
- sampled owner declarations:
  `IsDerivedCompletionKoszulPowerTensorComparison`,
  `IsDerivedCompletionKoszulPowerTensorComparison.isDerivedLimit`,
  `isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison`,
  `derivedCompleteObjectProperty`,
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`,
  `Adjunction.mkOfHomEquiv`;
- best owner abstraction: the source-facing owner here is the actual adjunction `L ⊣ ι`, not the
  weaker proposition `L.IsLeftAdjoint`; the comparison predicate
  `IsDerivedCompletionKoszulPowerTensorComparison` and the isomorphism criterion from
  Lemma `15.92.17` are the bridge data used to build the canonical Hom-equivalence for that
  adjunction;
- primitive data: the functor `L`, the natural transformation `η`, and the fact that each
  `η.app K` is the canonical comparison map to the powered Koszul derived limit;
- derived API: the induced adjunction `L ⊣ ι` and its consequence `L.IsLeftAdjoint`.

Source/core/bridge triage:
- `source-facing`: the adjunction `L ⊣ ι` for the powered Koszul derived-completion functor;
- `core/canonical`: `derivedCompleteObjectProperty` and
  `IsDerivedCompletionKoszulPowerTensorComparison`, together with the canonical owner
  `Adjunction`;
- `bridge/view`: the comparison morphism `η.app K`, viewed through the owner predicate above and
  the induced Hom-equivalence into derived-complete targets. -/

-- Proof sketch: the primitive input is that `η.app K` is the canonical comparison morphism to the
-- powered Koszul derived limit, encoded by
-- `IsDerivedCompletionKoszulPowerTensorComparison`. Lemma `15.92.17` then supplies both the
-- derived-limit witness and the isomorphism criterion on already derived-complete sources. The
-- usual reflective-subcategory argument therefore shows that precomposition with `η.app K`
-- induces a Hom-equivalence on morphisms into every derived-complete object, giving the required
-- adjunction with the inclusion from Lemma `15.92.10`. The proposition `L.IsLeftAdjoint` is then
-- only the derived typeclass consequence.
private theorem eta_app_isIso_of_derivedComplete
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    IsIso (η.app E.obj) := by
  exact
    (isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison
      f (η.app E.obj) (hη E.obj)).1 E.property

private noncomputable def derivedLimitOfKoszulPowerTensorFunctorCounitApp
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    L.obj E.obj ⟶ E := by
  letI := eta_app_isIso_of_derivedComplete f L η hη E
  exact (DerivedCategory.derivedCompleteObjectProperty I).ι.preimage
    (asIso (η.app E.obj)).inv

private noncomputable def derivedLimitOfKoszulPowerTensorFunctorHomEquiv
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (K : DMod)
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    (L.obj K ⟶ E) ≃
      (K ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E) where
  toFun φ := η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ
  invFun ψ := L.map ψ ≫ derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E
  left_inv φ := by
    sorry
  right_inv ψ := by
    sorry

/-- Lemma 15.92.18: in Situation `15.92.15`, let `L : D(A) ⥤ D_{comp}(A, I)` be a functor to the
full subcategory of objects derived complete with respect to `I = (f_1, \ldots, f_r)`. Assume
that, for every `K : D(A)`, the component `η.app K` of a natural transformation
`η : 𝟭 ⟶ L ⋙ ι` is the canonical comparison map
`K \to R\!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)` in the source-facing sense of
`IsDerivedCompletionKoszulPowerTensorComparison`. Then `L` is left adjoint to the inclusion
`D_{comp}(A, I) ⥤ D(A)` constructed in Lemma `15.92.10`, with unit given by the supplied
comparison map `η`. This is the library-facing form of the statement that the functor
`K ↦ R\!\varprojlim (K \otimes_A^{\mathbf L} K_n^\bullet)` is the reflector onto
derived-complete objects. -/
noncomputable def derivedLimitOfKoszulPowerTensorFunctorAdjunction
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K)) :
    L ⊣ (DerivedCategory.derivedCompleteObjectProperty I).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv := derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη
      homEquiv_naturality_left_symm := by
        sorry
      homEquiv_naturality_right := by
        sorry }

/-- Derived consequence of Lemma `15.92.18`: the functor realizing the powered Koszul derived
limit is a left adjoint. The source-facing content is the adjunction
`derivedLimitOfKoszulPowerTensorFunctorAdjunction`. -/
theorem derivedLimitOfKoszulPowerTensorFunctor_isLeftAdjoint
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K)) :
    L.IsLeftAdjoint :=
  (derivedLimitOfKoszulPowerTensorFunctorAdjunction f L η hη).isLeftAdjoint

end

end CategoryTheory
