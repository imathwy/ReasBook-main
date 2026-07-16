import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_92_17

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
/-- Helper for Lemma 15.92.18: the comparison component is an isomorphism for any source object
already known to be derived complete. -/
private theorem eta_app_isIso_of_isDerivedComplete
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    {K : DMod}
    (hK : K.IsDerivedCompleteWithRespectTo I) :
    IsIso (η.app K) := by
  -- Proof comment: Lemma `15.92.17` applies directly once the source object is known to be
  -- derived complete with respect to `I`.
  exact
    (isDerivedCompleteWithRespectTo_spanRange_iff_isIso_derivedCompletionComparison
      f (η.app K) (hη K)).1 hK

/-- Helper for Lemma 15.92.18: every comparison morphism into the chosen reflected object is an
isomorphism. -/
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
  -- Proof comment: the reflected object is derived complete by definition of the full
  -- subcategory, so the general comparison-isomorphism criterion applies.
  exact eta_app_isIso_of_isDerivedComplete f L η hη E.property

/-- Helper for Lemma 15.92.18: every comparison morphism into the chosen reflected object is an
isomorphism. -/
private noncomputable def eta_app_iso
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (K : DMod) : K ≅ (L.obj K).obj :=
  @asIso _ _ _ _ (η.app K) (eta_app_isIso_of_derivedComplete f L η hη (L.obj K))

/-- Helper for Lemma 15.92.18: the counit on a derived-complete object is the inverse of the
comparison isomorphism lifted back to the full subcategory. -/
private noncomputable def derivedLimitOfKoszulPowerTensorFunctorCounitApp
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    L.obj E.obj ⟶ E :=
  (DerivedCategory.derivedCompleteObjectProperty I).ι.preimage
    ((eta_app_iso f L η hη E.obj).symm.hom)

/-- Helper for Lemma 15.92.18: forgetting the counit morphism recovers the inverse comparison
map in the ambient derived category. -/
private theorem derivedLimitOfKoszulPowerTensorFunctorCounitApp_map
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
        (derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E) =
      (eta_app_iso f L η hη E.obj).symm.hom := by
  -- Proof comment: `preimage` was chosen exactly so that the inclusion functor forgets it to the
  -- ambient inverse morphism.
  rw [derivedLimitOfKoszulPowerTensorFunctorCounitApp]
  rw [(DerivedCategory.derivedCompleteObjectProperty I).ι.map_preimage]

/-- Helper for Lemma 15.92.18: the counit is natural on the derived-complete full subcategory. -/
private theorem derivedLimitOfKoszulPowerTensorFunctorCounit_natural
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    {E₁ E₂ : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory}
    (φ : E₁ ⟶ E₂) :
    L.map (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) ≫
        derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E₂ =
      derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E₁ ≫ φ := by
  apply ObjectProperty.hom_ext
  -- Proof comment: after forgetting to the ambient derived category, this is the inverse-form of
  -- naturality for the comparison transformation `η`.
  simp only [Functor.map_comp, derivedLimitOfKoszulPowerTensorFunctorCounitApp_map,
    Category.assoc]
  apply (cancel_mono (eta_app_iso f L η hη E₁.obj).hom).1
  simpa [eta_app_iso, Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (eta_app_iso f L η hη E₂.obj).symm.hom)
      (η.naturality (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ))

/-- Helper for Lemma 15.92.18: the reflector triangle identity holds on the image of `L`. -/
private theorem derivedLimitOfKoszulPowerTensorFunctorTriangle
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (K : DMod) :
    L.map (η.app K) ≫
        derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη (L.obj K) =
      𝟙 (L.obj K) := by
  apply ObjectProperty.hom_ext
  -- Proof comment: forget to `D(A)`, insert `η.app K` together with its inverse, and use
  -- naturality of `η` at the morphism `η.app K`.
  simp only [Functor.map_comp, derivedLimitOfKoszulPowerTensorFunctorCounitApp_map,
    Category.assoc]
  apply (cancel_mono (eta_app_iso f L η hη K).hom).1
  simpa [eta_app_iso, Category.assoc] using
    congrArg
      (fun k ↦ k ≫ (eta_app_iso f L η hη (L.obj K).obj).symm.hom)
      (η.naturality (η.app K))

/-- Helper for Lemma 15.92.18: the explicit inverse formula is a left inverse to precomposition
by the comparison map. -/
private theorem derivedLimitOfKoszulPowerTensorFunctorHom_left_inv
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (K : DMod)
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    Function.LeftInverse
      (fun ψ : K ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E ↦
        L.map ψ ≫ derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E)
      (fun φ : L.obj K ⟶ E ↦
        η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) := by
  intro φ
  -- Proof comment: move the postcomposition past the counit by naturality, then finish with the
  -- reflector triangle identity at `L.obj K`.
  calc
    L.map (η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) ≫
        derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E
        =
      (L.map (η.app K) ≫
        L.map (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ)) ≫
          derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E := by
            rw [Functor.map_comp]
    _ =
      L.map (η.app K) ≫
        (L.map (((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) ≫
          derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E) := by
            simp [Category.assoc]
    _ =
      L.map (η.app K) ≫
        (derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη (L.obj K) ≫ φ) := by
            rw [derivedLimitOfKoszulPowerTensorFunctorCounit_natural f L η hη φ]
    _ =
      (L.map (η.app K) ≫
        derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη (L.obj K)) ≫ φ := by
            simp [Category.assoc]
    _ = φ := by
            rw [derivedLimitOfKoszulPowerTensorFunctorTriangle f L η hη K]
            simp

/-- Helper for Lemma 15.92.18: the same explicit inverse formula is also a right inverse. -/
private theorem derivedLimitOfKoszulPowerTensorFunctorHom_right_inv
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    (K : DMod)
    (E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory) :
    Function.RightInverse
      (fun ψ : K ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E ↦
        L.map ψ ≫ derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E)
      (fun φ : L.obj K ⟶ E ↦
        η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map φ) := by
  intro ψ
  -- Proof comment: ambient naturality of `η` rewrites the composite to `ψ ≫ η.app E.obj`, and
  -- the counit is the inverse of that comparison isomorphism.
  calc
    η.app K ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          (L.map ψ ≫ derivedLimitOfKoszulPowerTensorFunctorCounitApp f L η hη E)
        =
      η.app K ≫
        (((L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι).map ψ) ≫
          (eta_app_iso f L η hη E.obj).symm.hom) := by
            simp [derivedLimitOfKoszulPowerTensorFunctorCounitApp_map, Category.assoc]
    _ =
      (ψ ≫ (eta_app_iso f L η hη E.obj).hom) ≫
        (eta_app_iso f L η hη E.obj).symm.hom := by
            simpa [eta_app_iso, Category.assoc] using η.naturality ψ
    _ = ψ := by
            simp [Category.assoc]

/-- Helper for Lemma 15.92.18: morphisms from the reflected object into a derived-complete object
are equivalent to morphisms from the original object into the ambient target. -/
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
  left_inv := derivedLimitOfKoszulPowerTensorFunctorHom_left_inv f L η hη K E
  right_inv := derivedLimitOfKoszulPowerTensorFunctorHom_right_inv f L η hη K E

/-- Helper for Lemma 15.92.18: the Hom-equivalence is natural in the source object. -/
private theorem derivedLimitOfKoszulPowerTensorFunctorHomEquiv_naturality_left_symm
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    {K₁ K₂ : DMod}
    {E : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory}
    (a : K₁ ⟶ K₂)
    (g : K₂ ⟶ ((DerivedCategory.derivedCompleteObjectProperty I).ι).obj E) :
    (derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₁ E).symm (a ≫ g) =
      L.map a ≫ (derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₂ E).symm g := by
  apply (derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₁ E).injective
  -- Proof comment: both candidate inverses become the same map after precomposition with
  -- `η.app K₁`, so injectivity of the Hom-equivalence finishes the comparison.
  calc
    η.app K₁ ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          ((derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₁ E).symm (a ≫ g))
        =
      a ≫ g := by
        exact (derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₁ E).apply_symm_apply _ 
    _ =
      a ≫
        (η.app K₂ ≫
          ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
            ((derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₂ E).symm g)) := by
              rw [(derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₂ E).apply_symm_apply]
    _ =
      (η.app K₁ ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map (L.map a)) ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          ((derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₂ E).symm g) := by
            rw [η.naturality a]
            simp [Category.assoc]
    _ =
      η.app K₁ ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map
          (L.map a ≫
            (derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K₂ E).symm g) := by
              simp [Category.assoc]

/-- Helper for Lemma 15.92.18: the Hom-equivalence is natural in the derived-complete target. -/
private theorem derivedLimitOfKoszulPowerTensorFunctorHomEquiv_naturality_right
    (L : DMod ⥤ (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory)
    (η :
      𝟭 DMod ⟶
        L ⋙ (DerivedCategory.derivedCompleteObjectProperty I).ι)
    (hη :
      ∀ K : DMod,
        IsDerivedCompletionKoszulPowerTensorComparison f K (L.obj K).obj (η.app K))
    {K : DMod}
    {E₁ E₂ : (DerivedCategory.derivedCompleteObjectProperty I).FullSubcategory}
    (g : L.obj K ⟶ E₁)
    (h : E₁ ⟶ E₂) :
    derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K E₂ (g ≫ h) =
      derivedLimitOfKoszulPowerTensorFunctorHomEquiv f L η hη K E₁ g ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map h := by
  -- Proof comment: expanding the forward map reduces the claim to associativity and functoriality
  -- of the inclusion.
  change
    η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map (g ≫ h) =
      (η.app K ≫ ((DerivedCategory.derivedCompleteObjectProperty I).ι).map g) ≫
        ((DerivedCategory.derivedCompleteObjectProperty I).ι).map h
  simp [Category.assoc]

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
@[stacks 0920]
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
      homEquiv_naturality_left_symm :=
        derivedLimitOfKoszulPowerTensorFunctorHomEquiv_naturality_left_symm f L η hη
      homEquiv_naturality_right :=
        derivedLimitOfKoszulPowerTensorFunctorHomEquiv_naturality_right f L η hη }

/-- Derived consequence of Lemma `15.92.18`: the functor realizing the powered Koszul derived
limit is a left adjoint. The source-facing content is the adjunction
`derivedLimitOfKoszulPowerTensorFunctorAdjunction`. -/
@[stacks 0920]
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
