import Mathlib
import StacksProject_2024.stacks_project.Chap12.Lemma_12_32_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_31_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open HomologicalComplex

noncomputable section

universe w v u

namespace CategoryTheory

/- 
Domain-style sampling for Lemma 13.34.2:
- primary domain: countable products in derived categories of abelian categories, with exactness
  of countable products in the underlying abelian category;
- inspected declarations:
  * `CountableAB4Star`
  * `CountableAB4Star.ofShape`
  * `CategoryTheory.derivedCategory_Q_preserves_product_of_kInjective`
  * `CategoryTheory.Limits.isLimitOfHasProductOfPreservesLimit`
  * `CategoryTheory.ShortComplex.pi_homologyIso`
  * `DerivedCategory.homologyFunctorFactors`
- best owner abstraction:
  * for the exact-product hypothesis in this chapter, the source-facing owner is
    `CountableAB4Star 𝒜`; the exactness instance
    `HasExactLimitsOfShape (Discrete ℕ) 𝒜` is only the canonical bridge recovered from it;
  * for represented families in the derived category, the chapter owner is the preservation
    statement `derivedCategory_Q_preserves_product_of_kInjective`; the specialized termwise
    product statement here should only recover the induced `IsLimit` witness by
    `isLimitOfHasProductOfPreservesLimit` and then transport it along the chosen identifications
    `eK`;
  * for the homology comparison: `ShortComplex.pi_homologyIso` applied to the short-complex model
    of the termwise product complex;
- primitive data:
  * a countable family of complexes `K : ℕ → CochainComplex 𝒜 ℤ`;
  * exact countable products in `𝒜`, canonically expressed by
    `[HasCountableProducts 𝒜] [CountableAB4Star 𝒜]`;
  * when comparing with products in `DerivedCategory 𝒜`, K-injectivity of the chosen
    representatives `K i`;
- derived API:
  * the preservation witness `PreservesLimit (Discrete.functor K) Q` for a represented
    K-injective family;
  * the product witness on `Q.obj (∏ᶜ K)` recovered from that owner in `DerivedCategory 𝒜`;
  * the resulting homology/product comparison.

Source/core/bridge triage:
- core/canonical:
  `CountableAB4Star 𝒜`,
  `derivedCategory_Q_preserves_product_of_kInjective`,
  `isLimitOfHasProductOfPreservesLimit`,
  `ShortComplex.pi_homologyIso`, and
  `DerivedCategory.homologyFunctorFactors`;
- source-facing:
  `termwise_product_represents_product` and
  `homology_termwise_product_iso`, both stated for countable represented termwise products;
- bridge/view:
  the recovered exactness instance `HasExactLimitsOfShape (Discrete ℕ) 𝒜`, and
  the transport of the product cone in `termwise_product_represents_product` along chosen
  isomorphisms `eK`.
-/

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
  [HasCountableProducts 𝒜]

local notation "Q" => DerivedCategory.Q

/-- Lemma 13.34.2: if `K n` represents `X n`, then the termwise product complex `∏ K n`
represents the countable product of the family `X n` in the derived category, provided the chosen
representatives are K-injective. -/
noncomputable def termwise_product_represents_product
    (X : ℕ → DerivedCategory 𝒜) (K : ℕ → CochainComplex 𝒜 ℤ)
    [∀ i, (K i).IsKInjective]
    (eK : ∀ i, Q.obj (K i) ≅ X i) :
    IsLimit
      (Fan.mk (Q.obj (∏ᶜ K)) fun i ↦ Q.map (Pi.π K i) ≫ (eK i).hom) := by
  let e : Discrete.functor (fun i ↦ Q.obj (K i)) ≅ Discrete.functor X :=
    Discrete.natIso fun i : Discrete ℕ ↦ eK i.as
  letI := derivedCategory_Q_preserves_product_of_kInjective K
  simpa using
    (IsLimit.postcomposeHomEquiv e (Fan.mk (Q.obj (∏ᶜ K)) fun i ↦ Q.map (Pi.π K i))).symm
      (isLimitOfHasProductOfPreservesLimit Q K)

variable [CountableAB4Star 𝒜]

/-- The canonical comparison map from the homology of the termwise product representative to the
product of the homology objects is an isomorphism under exact countable products. -/
noncomputable def homology_termwise_product_iso
    (p : ℤ) (K : ℕ → CochainComplex 𝒜 ℤ) :
    (homologyFunctor 𝒜 p).obj (Q.obj (∏ᶜ K)) ≅
      ∏ᶜ fun i ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K i)) := by
  let hsc :
      IsLimit
        (Fan.mk ((∏ᶜ K).sc p) fun i ↦
          (shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K i)) := by
    refine ShortComplex.isLimitOfIsLimitπ _ ?_ ?_ ?_
    · exact
        (Fan.isLimitMapConeEquiv ShortComplex.π₁ _ _).symm <|
          isLimitOfHasProductOfPreservesLimit
            (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((ComplexShape.up ℤ).prev p)) K
    · exact
        (Fan.isLimitMapConeEquiv ShortComplex.π₂ _ _).symm <|
          isLimitOfHasProductOfPreservesLimit
            (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) p) K
    · exact
        (Fan.isLimitMapConeEquiv ShortComplex.π₃ _ _).symm <|
          isLimitOfHasProductOfPreservesLimit
            (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((ComplexShape.up ℤ).next p)) K
  let eSc : ((∏ᶜ K).sc p) ≅ ∏ᶜ fun i ↦ (K i).sc p :=
    hsc.conePointUniqueUpToIso (limit.isLimit _)
  let eH :
      Discrete.functor (fun i ↦ (K i).homology p) ≅
        Discrete.functor (fun i ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K i))) :=
    Discrete.natIso fun i : Discrete ℕ ↦
      ((homologyFunctorFactors 𝒜 p).app (K i.as)).symm
  exact
    (homologyFunctorFactors 𝒜 p).app (∏ᶜ K) ≪≫
      (ShortComplex.homologyFunctor 𝒜).mapIso eSc ≪≫
        ShortComplex.pi_homologyIso (fun i ↦ (K i).sc p) ≪≫
          lim.mapIso eH

/-- Helper for Lemma 13.34.2: the projection from the limit functor on countable discrete
diagrams to evaluation at the `i`-th factor is natural. -/
lemma discrete_limit_projection_naturality (i : ℕ)
    {X Y : Discrete ℕ ⥤ 𝒜} (f : X ⟶ Y) :
    (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜).map f ≫ limit.π Y (Discrete.mk i) =
      limit.π X (Discrete.mk i) ≫ ((evaluation (Discrete ℕ) 𝒜).obj (Discrete.mk i)).map f := by
  simpa using limMap_π (α := f) (j := Discrete.mk i)

/-- Helper for Lemma 13.34.2: the canonical natural transformation from countable products to the
`i`-th evaluation functor. -/
noncomputable def discrete_limit_projection (i : ℕ) :
    (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜) ⟶ (evaluation (Discrete ℕ) 𝒜).obj (Discrete.mk i) where
  app X := limit.π X (Discrete.mk i)
  naturality _ _ f := discrete_limit_projection_naturality (𝒜 := 𝒜) i f

/-- Helper for Lemma 13.34.2: the projection produced by the short-complex functor-equivalence
model agrees with the ordinary `i`-th product projection. -/
lemma ShortComplex.functor_equivalence_projection
    (S : ℕ → ShortComplex 𝒜) (i : ℕ) :
    let F : Discrete ℕ ⥤ ShortComplex 𝒜 := Discrete.functor S
    let e := ShortComplex.functorEquivalence (Discrete ℕ) 𝒜
    let T : ShortComplex (Discrete ℕ ⥤ 𝒜) := e.inverse.obj F
    ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
        T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
          ((e.counitIso.app F).app (Discrete.mk i)).hom =
      Pi.π S i := by
  -- The cone-point comparison is characterized by the `i`-th cone projection.
  let F : Discrete ℕ ⥤ ShortComplex 𝒜 := Discrete.functor S
  let e := ShortComplex.functorEquivalence (Discrete ℕ) 𝒜
  let T : ShortComplex (Discrete ℕ ⥤ 𝒜) := e.inverse.obj F
  change ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
      T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
        ((e.counitIso.app F).app (Discrete.mk i)).hom =
    Pi.π S i
  have h_cone_projection :
      T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
          ((e.counitIso.app F).app (Discrete.mk i)).hom =
        (ShortComplex.limitCone F).π.app (Discrete.mk i) := by
    ext <;> simp [T, e, F, discrete_limit_projection, ShortComplex.limitCone,
      ShortComplex.functorEquivalence, ShortComplex.mapNatTrans,
      ShortComplex.FunctorEquivalence.functor, ShortComplex.FunctorEquivalence.inverse,
      ShortComplex.FunctorEquivalence.counitIso]
  have h_first :
      ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
          T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
            ((e.counitIso.app F).app (Discrete.mk i)).hom =
        ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
          (ShortComplex.limitCone F).π.app (Discrete.mk i) := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫ f)
        h_cone_projection
  have h_second :
      ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
          (ShortComplex.limitCone F).π.app (Discrete.mk i) =
        Pi.π S i := by
    simpa [F] using
      IsLimit.conePointUniqueUpToIso_hom_comp
        (limit.isLimit F)
        (ShortComplex.isLimitLimitCone F)
        (Discrete.mk i)
  exact h_first.trans h_second

/-- Helper for Lemma 13.34.2: the homology comparison for a product of short complexes has the
expected middle factor after rewriting the `i`-th product projection through the Chap12
construction. -/
lemma ShortComplex.pi_homologyIso_middle_component
    (S : ℕ → ShortComplex 𝒜) (i : ℕ) :
    let F : Discrete ℕ ⥤ ShortComplex 𝒜 := Discrete.functor S
    let e := ShortComplex.functorEquivalence (Discrete ℕ) 𝒜
    let T : ShortComplex (Discrete ℕ ⥤ 𝒜) := e.inverse.obj F
    let H : Discrete ℕ ⥤ 𝒜 := Discrete.functor fun j ↦ (S j).homology
    let termwiseHomologyIso : T.homology ≅ H :=
      Discrete.natIso fun j ↦
        (T.mapHomologyIso ((evaluation (Discrete ℕ) 𝒜).obj j)).symm ≪≫
          (ShortComplex.homologyFunctor 𝒜).mapIso ((e.counitIso.app F).app j)
    (T.mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
        limit.π T.homology (Discrete.mk i) ≫
          termwiseHomologyIso.hom.app (Discrete.mk i) =
      ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
        ((ShortComplex.homologyFunctor 𝒜).mapIso
          ((e.counitIso.app F).app (Discrete.mk i))).hom := by
  -- Rewrite the homology-level projection using the naturality square of `mapHomologyIso`.
  dsimp
  have h_projection_naturality :
      limit.π ((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
          (Discrete.functor S)).homology (Discrete.mk i) =
        (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
              (Discrete.functor S)).mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).inv ≫
          ShortComplex.homologyMap
            (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                  (Discrete.functor S)).mapNatTrans
              (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
            (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                  (Discrete.functor S)).mapHomologyIso
                ((evaluation (Discrete ℕ) 𝒜).obj (Discrete.mk i))).hom := by
    simpa [discrete_limit_projection] using
      (NatTrans.app_homology (τ := discrete_limit_projection (𝒜 := 𝒜) i)
        (S := ((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
          (Discrete.functor S))))
  -- The evaluation-side comparison isomorphism now cancels against its inverse.
  have h_rewrite :
      (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
            (Discrete.functor S)).mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
          limit.π ((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
              (Discrete.functor S)).homology (Discrete.mk i) ≫
            (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                  (Discrete.functor S)).mapHomologyIso
                ((evaluation (Discrete ℕ) 𝒜).obj (Discrete.mk i))).inv ≫
              ShortComplex.homologyMap
                (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).counitIso.app
                    (Discrete.functor S)).app (Discrete.mk i)).hom =
        (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
              (Discrete.functor S)).mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
          ((((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                  (Discrete.functor S)).mapHomologyIso
                (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).inv ≫
              ShortComplex.homologyMap
                (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                      (Discrete.functor S)).mapNatTrans
                  (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                      (Discrete.functor S)).mapHomologyIso
                    ((evaluation (Discrete ℕ) 𝒜).obj (Discrete.mk i))).hom) ≫
            (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                  (Discrete.functor S)).mapHomologyIso
                ((evaluation (Discrete ℕ) 𝒜).obj (Discrete.mk i))).inv ≫
              ShortComplex.homologyMap
                (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).counitIso.app
                    (Discrete.functor S)).app (Discrete.mk i)).hom := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦
          (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                (Discrete.functor S)).mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
            f ≫
              (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).inverse.obj
                    (Discrete.functor S)).mapHomologyIso
                  ((evaluation (Discrete ℕ) 𝒜).obj (Discrete.mk i))).inv ≫
                ShortComplex.homologyMap
                  (((ShortComplex.functorEquivalence (Discrete ℕ) 𝒜).counitIso.app
                      (Discrete.functor S)).app (Discrete.mk i)).hom)
        h_projection_naturality
  exact h_rewrite.trans (by simp [Category.assoc])

/-- Helper for Lemma 13.34.2: the homology comparison for a product of short complexes has the
expected `i`-th projection. -/
lemma ShortComplex.pi_homologyIso_hom_π
    (S : ℕ → ShortComplex 𝒜) (i : ℕ) :
    (ShortComplex.pi_homologyIso S).hom ≫ Pi.π (fun j ↦ (S j).homology) i =
      ShortComplex.homologyMap (Pi.π S i) := by
  let F : Discrete ℕ ⥤ ShortComplex 𝒜 := Discrete.functor S
  let e := ShortComplex.functorEquivalence (Discrete ℕ) 𝒜
  let T : ShortComplex (Discrete ℕ ⥤ 𝒜) := e.inverse.obj F
  let H : Discrete ℕ ⥤ 𝒜 := Discrete.functor fun j ↦ (S j).homology
  let termwiseHomologyIso : T.homology ≅ H :=
    Discrete.natIso fun j ↦
      (T.mapHomologyIso ((evaluation (Discrete ℕ) 𝒜).obj j)).symm ≪≫
        (ShortComplex.homologyFunctor 𝒜).mapIso ((e.counitIso.app F).app j)
  -- Route correction: rewrite the Chap12 comparison through the middle-component lemma, then
  -- map the short-complex projection identity through homology.
  have h_middle :
      (T.mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
          limit.π T.homology (Discrete.mk i) ≫
            termwiseHomologyIso.hom.app (Discrete.mk i) =
        ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            ((e.counitIso.app F).app (Discrete.mk i))).hom := by
    simpa [F, e, T, H, termwiseHomologyIso] using
      ShortComplex.pi_homologyIso_middle_component (𝒜 := 𝒜) (S := S) i
  have h_projection :
      ShortComplex.homologyMap
          ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
            ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
              ((ShortComplex.homologyFunctor 𝒜).mapIso
                ((e.counitIso.app F).app (Discrete.mk i))).hom =
        ShortComplex.homologyMap (Pi.π S i) := by
    -- The short-complex projection identity from the functor-equivalence survives under homology.
    have h_projection_eq :
        ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
            T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
              ((e.counitIso.app F).app (Discrete.mk i)).hom =
          Pi.π S i := by
      simpa [F, e, T] using
        (ShortComplex.functor_equivalence_projection (𝒜 := 𝒜) (S := S) i)
    have h_projection_raw :
        ShortComplex.homologyMap
            (((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
              T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
                ((e.counitIso.app F).app (Discrete.mk i)).hom) =
          ShortComplex.homologyMap (Pi.π S i) := by
      exact
        congrArg
          (fun f : limit (Discrete.functor S) ⟶ S i => ShortComplex.homologyMap f)
          h_projection_eq
    have h_projection_expand :
        ShortComplex.homologyMap
            ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
              ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                ((ShortComplex.homologyFunctor 𝒜).mapIso
                  ((e.counitIso.app F).app (Discrete.mk i))).hom =
          ShortComplex.homologyMap
              (((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
                T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
                  ((e.counitIso.app F).app (Discrete.mk i)).hom) := by
      calc
        ShortComplex.homologyMap
            ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
              ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                ((ShortComplex.homologyFunctor 𝒜).mapIso
                  ((e.counitIso.app F).app (Discrete.mk i))).hom =
          ShortComplex.homologyMap
              ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
                ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                  ShortComplex.homologyMap ((e.counitIso.hom.app F).app (Discrete.mk i)) := by
                    rfl
        _ =
          (ShortComplex.homologyMap
              ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
            ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i))) ≫
              ShortComplex.homologyMap ((e.counitIso.hom.app F).app (Discrete.mk i)) := by
                simp [Category.assoc]
        _ =
          ShortComplex.homologyMap
              (((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
                T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                  ShortComplex.homologyMap ((e.counitIso.hom.app F).app (Discrete.mk i)) := by
                    exact
                      congrArg
                        (fun f ↦ f ≫ ShortComplex.homologyMap ((e.counitIso.hom.app F).app (Discrete.mk i)))
                        (ShortComplex.homologyMap_comp
                          ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom
                          (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i))).symm
        _ = ShortComplex.homologyMap
              ((((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
                  T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                (e.counitIso.hom.app F).app (Discrete.mk i)) := by
                  exact
                    (ShortComplex.homologyMap_comp
                      (((limit.isLimit F).conePointUniqueUpToIso
                          (ShortComplex.isLimitLimitCone F)).hom ≫
                        T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i))
                      ((e.counitIso.hom.app F).app (Discrete.mk i))).symm
        _ = ShortComplex.homologyMap
              (((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
                T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i) ≫
                  ((e.counitIso.app F).app (Discrete.mk i)).hom) := by
                    simp [Category.assoc]
    exact h_projection_expand.trans h_projection_raw
  -- Rewrite the rightmost factor through `Pi.isoLimit_inv_π` and `limMap_π`.
  have h_unfold :
      (ShortComplex.pi_homologyIso S).hom ≫ Pi.π (fun j ↦ (S j).homology) i =
        ShortComplex.homologyMap
            ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
              (T.mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
                limMap termwiseHomologyIso.hom ≫
                  (Pi.isoLimit H).inv ≫ Pi.π (fun j ↦ (S j).homology) i := by
    simp [ShortComplex.pi_homologyIso, F, e, T, H, termwiseHomologyIso, Category.assoc]
  have h_tail :
      limMap termwiseHomologyIso.hom ≫
          (Pi.isoLimit H).inv ≫ Pi.π (fun j ↦ (S j).homology) i =
        limit.π T.homology (Discrete.mk i) ≫ termwiseHomologyIso.hom.app (Discrete.mk i) := by
    have h_isoLimit_proj :
        (Pi.isoLimit H).inv ≫ Pi.π (fun j ↦ (S j).homology) i = limit.π H (Discrete.mk i) := by
      simpa [H] using (Pi.isoLimit_inv_π (X := H) i)
    have h_limMap_proj :
        limMap termwiseHomologyIso.hom ≫ limit.π H (Discrete.mk i) =
          limit.π T.homology (Discrete.mk i) ≫ termwiseHomologyIso.hom.app (Discrete.mk i) := by
      simpa using limMap_π (α := termwiseHomologyIso.hom) (j := Discrete.mk i)
    calc
      limMap termwiseHomologyIso.hom ≫
          (Pi.isoLimit H).inv ≫ Pi.π (fun j ↦ (S j).homology) i =
        limMap termwiseHomologyIso.hom ≫
            ((Pi.isoLimit H).inv ≫ Pi.π (fun j ↦ (S j).homology) i) := by
              simp [Category.assoc]
      _ = limMap termwiseHomologyIso.hom ≫ limit.π H (Discrete.mk i) := by
            rw [h_isoLimit_proj]
            rfl
      _ = limit.π T.homology (Discrete.mk i) ≫ termwiseHomologyIso.hom.app (Discrete.mk i) :=
        h_limMap_proj
  have h_tail_comp :
      ShortComplex.homologyMap
          ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
            (T.mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
              limMap termwiseHomologyIso.hom ≫
                (Pi.isoLimit H).inv ≫ Pi.π (fun j ↦ (S j).homology) i =
        ShortComplex.homologyMap
            ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
              (T.mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
                (limit.π T.homology (Discrete.mk i) ≫
                  termwiseHomologyIso.hom.app (Discrete.mk i)) := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦
          ShortComplex.homologyMap
              ((limit.isLimit F).conePointUniqueUpToIso
                (ShortComplex.isLimitLimitCone F)).hom ≫
            (T.mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
              f)
        h_tail
  have h_middle_comp :
      ShortComplex.homologyMap
          ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
            (T.mapHomologyIso (lim : (Discrete ℕ ⥤ 𝒜) ⥤ 𝒜)).hom ≫
              (limit.π T.homology (Discrete.mk i) ≫
                termwiseHomologyIso.hom.app (Discrete.mk i)) =
        ShortComplex.homologyMap
            ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
              (ShortComplex.homologyMap
                (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                  ((ShortComplex.homologyFunctor 𝒜).mapIso
                    ((e.counitIso.app F).app (Discrete.mk i))).hom) := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦
          ShortComplex.homologyMap
              ((limit.isLimit F).conePointUniqueUpToIso
                (ShortComplex.isLimitLimitCone F)).hom ≫
            f)
        h_middle
  have h_assoc :
      ShortComplex.homologyMap
          ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
            (ShortComplex.homologyMap
              (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                ((ShortComplex.homologyFunctor 𝒜).mapIso
                  ((e.counitIso.app F).app (Discrete.mk i))).hom) =
        ShortComplex.homologyMap
            ((limit.isLimit F).conePointUniqueUpToIso (ShortComplex.isLimitLimitCone F)).hom ≫
              ShortComplex.homologyMap (T.mapNatTrans (discrete_limit_projection (𝒜 := 𝒜) i)) ≫
                ((ShortComplex.homologyFunctor 𝒜).mapIso
                  ((e.counitIso.app F).app (Discrete.mk i))).hom := by
    simp [Category.assoc]
  exact h_unfold.trans (h_tail_comp.trans (h_middle_comp.trans (h_assoc.trans h_projection)))

/-- Helper for Lemma 13.34.2: the cone-point identification between the short complex of the
termwise product and the product of the short complexes has the expected `i`-th projection. -/
lemma termwise_product_sc_iso_hom_π
    (p : ℤ) (K : ℕ → CochainComplex 𝒜 ℤ)
    (hsc :
      IsLimit
        (Fan.mk ((∏ᶜ K).sc p) fun j ↦
          (shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K j)))
    (i : ℕ) :
    (hsc.conePointUniqueUpToIso (limit.isLimit (Discrete.functor fun j ↦ (K j).sc p))).hom ≫
      Pi.π (fun j ↦ (K j).sc p) i =
        (shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K i) := by
  -- The cone-point transport is characterized by its compositions with the product projections.
  simpa using
    IsLimit.conePointUniqueUpToIso_hom_comp hsc
      (limit.isLimit (Discrete.functor fun j ↦ (K j).sc p)) (Discrete.mk i)

theorem homology_termwise_product_iso_hom
    (p : ℤ) (K : ℕ → CochainComplex 𝒜 ℤ) :
    (homology_termwise_product_iso p K).hom =
      Pi.lift fun i ↦
        (homologyFunctor 𝒜 p).map (Q.map (Pi.π K i)) := by
  let hsc :
      IsLimit
        (Fan.mk ((∏ᶜ K).sc p) fun j ↦
          (shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K j)) := by
    refine ShortComplex.isLimitOfIsLimitπ _ ?_ ?_ ?_
    · exact
        (Fan.isLimitMapConeEquiv ShortComplex.π₁ _ _).symm <|
          isLimitOfHasProductOfPreservesLimit
            (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((ComplexShape.up ℤ).prev p)) K
    · exact
        (Fan.isLimitMapConeEquiv ShortComplex.π₂ _ _).symm <|
          isLimitOfHasProductOfPreservesLimit
            (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) p) K
    · exact
        (Fan.isLimitMapConeEquiv ShortComplex.π₃ _ _).symm <|
          isLimitOfHasProductOfPreservesLimit
            (HomologicalComplex.eval 𝒜 (ComplexShape.up ℤ) ((ComplexShape.up ℤ).next p)) K
  let eSc : ((∏ᶜ K).sc p) ≅ ∏ᶜ fun j ↦ (K j).sc p :=
    hsc.conePointUniqueUpToIso (limit.isLimit _)
  let eH :
      Discrete.functor (fun j ↦ (K j).homology p) ≅
        Discrete.functor (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) :=
    Discrete.natIso fun j : Discrete ℕ ↦
      ((homologyFunctorFactors 𝒜 p).app (K j.as)).symm
  ext i
  -- The last factor is the limit map induced by the termwise identifications `eH`.
  have h_eH :
      limMap eH.hom ≫ Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i =
        Pi.π (fun j ↦ (K j).homology p) i ≫ ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    simpa [eH] using limMap_π (α := eH.hom) (j := Discrete.mk i)
  -- The middle two factors become the homology map of the `i`-th termwise projection.
  have h_sc_comp :
      ShortComplex.homologyMap eSc.hom ≫ ShortComplex.homologyMap (Pi.π (fun j ↦ (K j).sc p) i) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv =
        ShortComplex.homologyMap (eSc.hom ≫ Pi.π (fun j ↦ (K j).sc p) i) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ f ≫ ((homologyFunctorFactors 𝒜 p).app (K i)).inv)
        (ShortComplex.homologyMap_comp eSc.hom (Pi.π (fun j ↦ (K j).sc p) i)).symm
  have h_homological :
      ShortComplex.homologyMap ((shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K i)) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv =
        HomologicalComplex.homologyMap (Pi.π K i) p ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    rfl
  have h_pi_component :
      (((ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫
          Pi.π (fun j ↦ ((K j).sc p).homology) i) ≫
            ((homologyFunctorFactors 𝒜 p).app (K i)).inv) =
        ShortComplex.homologyMap (Pi.π (fun j ↦ (K j).sc p) i) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    exact
      congrArg
        (fun f ↦ f ≫ ((homologyFunctorFactors 𝒜 p).app (K i)).inv)
        (ShortComplex.pi_homologyIso_hom_π (S := fun j ↦ (K j).sc p) i)
  have h_termwise :
      ShortComplex.homologyMap (eSc.hom ≫ Pi.π (fun j ↦ (K j).sc p) i) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv =
        ShortComplex.homologyMap ((shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K i)) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    simpa using
      congrArg
        (fun f ↦
          ShortComplex.homologyMap f ≫
            ((homologyFunctorFactors 𝒜 p).app (K i)).inv)
        (termwise_product_sc_iso_hom_π (p := p) (K := K) hsc i)
  have h_middle :
      ShortComplex.homologyMap eSc.hom ≫
          (ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫
            limMap eH.hom ≫
              Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i =
        HomologicalComplex.homologyMap (Pi.π K i) p ≫ ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    have h_middle_termwise :
        ShortComplex.homologyMap eSc.hom ≫
            (ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫
              limMap eH.hom ≫
                Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i =
          ShortComplex.homologyMap ((shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K i)) ≫
            ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
      calc
      ShortComplex.homologyMap eSc.hom ≫
          (ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫
            limMap eH.hom ≫
              Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i =
        ShortComplex.homologyMap eSc.hom ≫
          (ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫
            (Pi.π (fun j ↦ (K j).homology p) i ≫
              ((homologyFunctorFactors 𝒜 p).app (K i)).inv) := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦
                    ShortComplex.homologyMap eSc.hom ≫
                      (ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫ f)
                  h_eH
      _ =
        ShortComplex.homologyMap eSc.hom ≫
          (ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫
            Pi.π (fun j ↦ ((K j).sc p).homology) i ≫
              ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
              rfl
      _ =
        ShortComplex.homologyMap eSc.hom ≫
          (ShortComplex.pi_homologyIso fun j ↦ (K j).sc p).hom ≫
            Pi.π (fun j ↦ (K j).homology p) i ≫
              ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
              rfl
      _ =
        ShortComplex.homologyMap eSc.hom ≫
          ShortComplex.homologyMap (Pi.π (fun j ↦ (K j).sc p) i) ≫
            ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦ ShortComplex.homologyMap eSc.hom ≫ f)
                  h_pi_component
      _ =
        ShortComplex.homologyMap (eSc.hom ≫ Pi.π (fun j ↦ (K j).sc p) i) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv := h_sc_comp
      _ =
        ShortComplex.homologyMap ((shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Pi.π K i)) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv := h_termwise
    exact h_middle_termwise.trans (by simpa [Category.assoc] using h_homological)
  -- The remaining comparison is exactly the naturality square for `homologyFunctorFactors`.
  have h_nat :
      ((homologyFunctorFactors 𝒜 p).hom.app (∏ᶜ K) ≫ HomologicalComplex.homologyMap (Pi.π K i) p) ≫
          ((homologyFunctorFactors 𝒜 p).app (K i)).inv =
        (homologyFunctor 𝒜 p).map (Q.map (Pi.π K i)) ≫
          (homologyFunctorFactors 𝒜 p).hom.app (K i) ≫
            ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    simpa [Category.assoc] using
      congrArg
        (fun f ↦ f ≫ ((homologyFunctorFactors 𝒜 p).app (K i)).inv)
        (DerivedCategory.homologyFunctorFactors_hom_naturality (Pi.π K i) p).symm
  -- Componentwise equality against the product projections determines the morphism.
  have h_component :
      (homology_termwise_product_iso p K).hom ≫
          Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i =
        ((homologyFunctorFactors 𝒜 p).hom.app (∏ᶜ K) ≫
          HomologicalComplex.homologyMap (Pi.π K i) p) ≫
            ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
    simpa [homology_termwise_product_iso, hsc, eSc, eH, Category.assoc] using
      congrArg
        (fun f ↦ (homologyFunctorFactors 𝒜 p).hom.app (∏ᶜ K) ≫ f)
        h_middle
  have h_projection :
      (homology_termwise_product_iso p K).hom ≫
          Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i =
        (Pi.lift fun j ↦ (homologyFunctor 𝒜 p).map (Q.map (Pi.π K j))) ≫
          Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i := by
    have h_nat' :
        ((homologyFunctorFactors 𝒜 p).hom.app (∏ᶜ K) ≫ HomologicalComplex.homologyMap (Pi.π K i) p) ≫
            ((homologyFunctorFactors 𝒜 p).app (K i)).inv =
          (homologyFunctor 𝒜 p).map (Q.map (Pi.π K i)) ≫
            (homologyFunctorFactors 𝒜 p).hom.app (K i) ≫
              ((homologyFunctorFactors 𝒜 p).app (K i)).inv := by
      simpa [Category.assoc] using h_nat
    have h_lift :
        (homologyFunctor 𝒜 p).map (Q.map (Pi.π K i)) ≫
            (homologyFunctorFactors 𝒜 p).hom.app (K i) ≫
              ((homologyFunctorFactors 𝒜 p).app (K i)).inv =
          (Pi.lift fun j ↦ (homologyFunctor 𝒜 p).map (Q.map (Pi.π K j))) ≫
            Pi.π (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i := by
      simpa [Pi.lift_π, Category.assoc] using
        congrArg
          (fun f ↦ (homologyFunctor 𝒜 p).map (Q.map (Pi.π K i)) ≫ f)
          (((homologyFunctorFactors 𝒜 p).app (K i)).hom_inv_id)
    exact
      h_component.trans (h_nat'.trans h_lift)
  simpa using h_projection

end

end CategoryTheory
