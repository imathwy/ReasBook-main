import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open DerivedCategory

universe w v u uI

namespace CategoryTheory

/-
Domain-style sampling for Lemma 13.33.5:
- primary domain: coproducts in derived categories, with the colimit structure owned by
  `IsColimit` and transported along a functor through preservation of the corresponding discrete
  colimit;
- inspected owner declarations:
  `CategoryTheory.Limits.coproductIsCoproduct`,
  `CategoryTheory.Limits.isColimitCofanMkObjOfIsColimit`,
  `CategoryTheory.Limits.isColimitOfHasCoproductOfPreservesColimit`,
  `CategoryTheory.Limits.hasCoproducts_of_colimit_cofans`,
  `CategoryTheory.CountableAB4`;
- best owner abstraction: `PreservesColimit (Discrete.functor K) DerivedCategory.Q`, together with
  the induced canonical `IsColimit` witness on `DerivedCategory.Q.obj (∐ K)` and the resulting
  countable-coproduct owner on `DerivedCategory 𝒜`;
- primitive-vs-derived split:
  the primitive data in this item are the countable family `K` and the exactness hypothesis
  encoded by `CountableAB4 𝒜`, which already carries countable coproducts; the explicit
  `IsColimit` witness for the canonical cofan and the ambient countable-coproduct structure on
  `DerivedCategory 𝒜` are derived API and should be obtained from the owner preservation
  predicate rather than stored primitively.
-/

/-
Source/core/bridge triage for Lemma 13.33.5:
- source-facing: the Stacks lemma says that `DerivedCategory.Q.obj (∐ K)` with the canonical maps
  from the summands is a coproduct of the images of `K`, so the file should expose the resulting
  canonical `IsColimit` witness directly and package it into the ambient countable-coproduct owner
  for `DerivedCategory 𝒜`;
- core/canonical: coproduct preservation for `DerivedCategory.Q`, expressed as
  `PreservesColimit (Discrete.functor K) DerivedCategory.Q`;
- bridge/view: the source-facing coproduct witness is obtained by applying
  `Limits.isColimitOfHasCoproductOfPreservesColimit DerivedCategory.Q K` after establishing the
  owner instance below, and arbitrary countable derived families are then handled by choosing
  representatives with `DerivedCategory.Q.objPreimage`; downstream files should reuse these
  bridges instead of rebuilding bespoke `HasCoproduct` witnesses.
-/

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
variable {α : Type uI}

local notation "Qis" => HomologicalComplex.quasiIso 𝒜 (ComplexShape.up ℤ)

section

variable [HasCoproductsOfShape α 𝒜] [HasExactColimitsOfShape (Discrete α) 𝒜]

/-- Helper for Lemma 13.33.5: every morphism into a derived object can be represented by a roof
whose target is the chosen `Q.objPreimage` model of that object. -/
private theorem exists_quasiIso_fraction_to_preimage
    {K : CochainComplex 𝒜 ℤ} {L : DerivedCategory 𝒜} (α : Q.obj K ⟶ L) :
    ∃ (M : CochainComplex 𝒜 ℤ) (σ : M ⟶ K) (_ : QuasiIso σ)
      (f : M ⟶ Q.objPreimage L),
      Q.map σ ≫ α = Q.map f ≫ (Q.objObjPreimageIso L).hom := by
  -- Move the target to the chosen complex representative so that `right_fac` applies directly.
  let β : Q.obj K ⟶ Q.obj (Q.objPreimage L) := α ≫ (Q.objObjPreimageIso L).inv
  obtain ⟨M, σ, hσ, f, hβ⟩ := DerivedCategory.right_fac β
  refine ⟨M, σ, ?_, f, ?_⟩
  · rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hσ
    exact hσ
  -- Cancel the inverse denominator from `right_fac` to recover the usual roof identity.
  calc
    Q.map σ ≫ α
        = Q.map σ ≫ (α ≫ (Q.objObjPreimageIso L).inv) ≫ (Q.objObjPreimageIso L).hom := by
            simp [β, Category.assoc]
    _ = Q.map σ ≫ β ≫ (Q.objObjPreimageIso L).hom := by
          rfl
    _ = Q.map σ ≫ (inv (Q.map σ) ≫ Q.map f) ≫ (Q.objObjPreimageIso L).hom := by
          rw [hβ]
    _ = Q.map f ≫ (Q.objObjPreimageIso L).hom := by
          simp [Category.assoc]

/-- Helper for Lemma 13.33.5: exact coproducts identify the homology of the termwise coproduct
complex with the coproduct of the homology objects. -/
private noncomputable abbrev shortComplex_coproduct_homology_iso
    (p : ℤ) (K : α → CochainComplex 𝒜 ℤ) :
    ((ShortComplex.homologyFunctor 𝒜).obj
      ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).obj (∐ K))) ≅
      ∐ fun i ↦ ((K i).sc p).homology :=
  let S : α → ShortComplex 𝒜 := fun i ↦ (K i).sc p
  let F : Discrete α ⥤ ShortComplex 𝒜 := Discrete.functor S
  let e := ShortComplex.functorEquivalence (Discrete α) 𝒜
  let T : ShortComplex (Discrete α ⥤ 𝒜) := e.inverse.obj F
  let H : Discrete α ⥤ 𝒜 := Discrete.functor fun i ↦ (S i).homology
  let termwiseHomologyIso : T.homology ≅ H :=
    Discrete.natIso fun i : Discrete α ↦
      (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj i)).symm ≪≫
        (ShortComplex.homologyFunctor 𝒜).mapIso ((e.counitIso.app F).app i)
  let eSc :
      (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).obj (∐ K) ≅
        ∐ fun i ↦ (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).obj (K i) :=
    PreservesCoproduct.iso (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K
  -- Compare the short complex of the termwise coproduct with the coproduct short complex,
  -- then apply the functor-category homology comparison and the sigma-colimit comparison.
  (ShortComplex.homologyFunctor 𝒜).mapIso eSc ≪≫
    ((ShortComplex.homologyFunctor 𝒜).mapIso
        ((colimit.isColimit F).coconePointUniqueUpToIso
          (ShortComplex.isColimitColimitCocone F)) ≪≫
      (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜) ≪≫
        colim.mapIso termwiseHomologyIso ≪≫
        (Sigma.isoColimit H).symm))

/-- Helper for Lemma 13.33.5: the short-complex coproduct comparison sends the `i`-th summand
map to the `i`-th coproduct inclusion of short complexes. -/
private theorem shortComplex_coproduct_inclusion_comp_preservesCoproductIso_hom
    (p : ℤ) (K : α → CochainComplex 𝒜 ℤ) (i : α) :
    (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Sigma.ι K i) ≫
        (PreservesCoproduct.iso
          (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K).hom =
      Sigma.ι (fun j ↦ ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).obj
        (K j))) i := by
  let e :=
    PreservesCoproduct.iso (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K
  -- Route correction: first cancel the coproduct comparison itself; the remaining blocker is the
  -- homology transport through the short-complex colimit model.
  have hhom : e.hom =
      inv (sigmaComparison
        (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [e, PreservesCoproduct.inv_hom] using (Iso.inv_hom_id e)
  rw [hhom]
  exact
    Limits.map_ι_comp_inv_sigmaComparison
      (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K i

/-- Helper for Lemma 13.33.5: exact coproducts identify the homology of the termwise coproduct
complex with the coproduct of the homology objects. -/
private noncomputable abbrev coproduct_homology_iso_of_exact
    (p : ℤ) (K : α → CochainComplex 𝒜 ℤ) :
    (homologyFunctor 𝒜 p).obj (Q.obj (∐ K)) ≅
      ∐ fun i ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K i)) :=
  ((homologyFunctorFactors 𝒜 p).app (∐ K)).symm ≪≫
    shortComplex_coproduct_homology_iso (𝒜 := 𝒜) (α := α) p K ≪≫
    Sigma.mapIso fun i ↦ ((homologyFunctorFactors 𝒜 p).app (K i)).symm

/-- Helper for Lemma 13.33.5: evaluation at the `i`-th factor maps naturally into the discrete
coproduct colimit functor. -/
private theorem discrete_colimit_inclusion_naturality
    (i : α) {X Y : Discrete α ⥤ 𝒜} (f : X ⟶ Y) :
    ((evaluation (Discrete α) 𝒜).obj (Discrete.mk i)).map f ≫ colimit.ι Y (Discrete.mk i) =
      colimit.ι X (Discrete.mk i) ≫ (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜).map f := by
  -- This is the standard colimit-cocone naturality on the `i`-th evaluation component.
  simpa using (colimit.ι_map f (Discrete.mk i)).symm

/-- Helper for Lemma 13.33.5: the universal coproduct cocone gives a natural transformation from
evaluation at `i` to the colimit functor on discrete diagrams. -/
private def discrete_colimit_inclusion
    (i : α) :
    ((evaluation (Discrete α) 𝒜).obj (Discrete.mk i)) ⟶
      (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜) where
  app X := colimit.ι X (Discrete.mk i)
  naturality _ _ f := discrete_colimit_inclusion_naturality (𝒜 := 𝒜) (α := α) i f

/-- Helper for Lemma 13.33.5: the short-complex functor-equivalence model transports the `i`-th
discrete coproduct inclusion to the ordinary coproduct inclusion of short complexes. -/
private theorem ShortComplex.functor_equivalence_inclusion
    (S : α → ShortComplex 𝒜) (i : α) :
    let F : Discrete α ⥤ ShortComplex 𝒜 := Discrete.functor S
    let e := ShortComplex.functorEquivalence (Discrete α) 𝒜
    let T : ShortComplex (Discrete α ⥤ 𝒜) := e.inverse.obj F
    ((e.counitIso.app F).app (Discrete.mk i)).inv ≫
        T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i) =
      (ShortComplex.colimitCocone F).ι.app (Discrete.mk i) := by
  -- Check the transported inclusion on the three short-complex terms componentwise.
  ext <;> simp [discrete_colimit_inclusion, ShortComplex.colimitCocone,
    ShortComplex.functorEquivalence, ShortComplex.mapNatTrans,
    ShortComplex.FunctorEquivalence.functor, ShortComplex.FunctorEquivalence.inverse,
    ShortComplex.FunctorEquivalence.counitIso]

/-- Helper for Lemma 13.33.5: after isolating the colimit-side transport, the middle component of
the short-complex homology comparison sends the `i`-th summand to the `i`-th homology summand. -/
private theorem shortComplex_coproduct_homology_iso_middle_component
    (p : ℤ) (K : α → CochainComplex 𝒜 ℤ) (i : α) :
    let S : α → ShortComplex 𝒜 := fun j ↦ (K j).sc p
    let F : Discrete α ⥤ ShortComplex 𝒜 := Discrete.functor S
    let e := ShortComplex.functorEquivalence (Discrete α) 𝒜
    let T : ShortComplex (Discrete α ⥤ 𝒜) := e.inverse.obj F
    let H : Discrete α ⥤ 𝒜 := Discrete.functor fun j ↦ (S j).homology
    let termwiseHomologyIso : T.homology ≅ H :=
      Discrete.natIso fun j : Discrete α ↦
        (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj j)).symm ≪≫
          (ShortComplex.homologyFunctor 𝒜).mapIso ((e.counitIso.app F).app j)
    ShortComplex.homologyMap (Sigma.ι S i) ≫
        ((ShortComplex.homologyFunctor 𝒜).mapIso
          ((colimit.isColimit F).coconePointUniqueUpToIso
            (ShortComplex.isColimitColimitCocone F))).hom ≫
        (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
        (colim.mapIso termwiseHomologyIso).hom ≫
        (Sigma.isoColimit H).symm.hom =
      Sigma.ι (fun j ↦ (S j).homology) i := by
  let S : α → ShortComplex 𝒜 := fun j ↦ (K j).sc p
  let F : Discrete α ⥤ ShortComplex 𝒜 := Discrete.functor S
  let e := ShortComplex.functorEquivalence (Discrete α) 𝒜
  let T : ShortComplex (Discrete α ⥤ 𝒜) := e.inverse.obj F
  let H : Discrete α ⥤ 𝒜 := Discrete.functor fun j ↦ (S j).homology
  let termwiseHomologyIso : T.homology ≅ H :=
    Discrete.natIso fun j : Discrete α ↦
      (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj j)).symm ≪≫
        (ShortComplex.homologyFunctor 𝒜).mapIso ((e.counitIso.app F).app j)
  -- Route correction: first rewrite the colimit-model cocone leg through the functor-equivalence,
  -- then apply `NatTrans.app_homology` only to the evaluation-to-colimit natural transformation.
  have h_leg :
      Sigma.ι S i ≫
          ((colimit.isColimit F).coconePointUniqueUpToIso
            (ShortComplex.isColimitColimitCocone F)).hom =
        ((e.counitIso.app F).app (Discrete.mk i)).inv ≫
          T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i) := by
    calc
      Sigma.ι S i ≫
          ((colimit.isColimit F).coconePointUniqueUpToIso
            (ShortComplex.isColimitColimitCocone F)).hom =
        (ShortComplex.colimitCocone F).ι.app (Discrete.mk i) := by
          simpa using
            IsColimit.comp_coconePointUniqueUpToIso_hom
              (colimit.isColimit F)
              (ShortComplex.isColimitColimitCocone F)
              (Discrete.mk i)
      _ =
        ((e.counitIso.app F).app (Discrete.mk i)).inv ≫
          T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i) := by
            simpa [F, e, T] using
              (ShortComplex.functor_equivalence_inclusion (𝒜 := 𝒜) (α := α) (S := S) i).symm
  have h_homology_leg :
      ShortComplex.homologyMap (Sigma.ι S i) ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            ((colimit.isColimit F).coconePointUniqueUpToIso
              (ShortComplex.isColimitColimitCocone F))).hom =
        ShortComplex.homologyMap
          (((e.counitIso.app F).app (Discrete.mk i)).inv ≫
            T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) := by
    -- Apply homology to the cocone-leg identity obtained above.
    calc
      ShortComplex.homologyMap (Sigma.ι S i) ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            ((colimit.isColimit F).coconePointUniqueUpToIso
              (ShortComplex.isColimitColimitCocone F))).hom =
        ShortComplex.homologyMap
          (Sigma.ι S i ≫
            ((colimit.isColimit F).coconePointUniqueUpToIso
              (ShortComplex.isColimitColimitCocone F)).hom) := by
              exact (ShortComplex.homologyMap_comp _ _).symm
      _ =
        ShortComplex.homologyMap
          (((e.counitIso.app F).app (Discrete.mk i)).inv ≫
            T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) := by
              rw [h_leg]
  have h_nat :
      colimit.ι T.homology (Discrete.mk i) =
        (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj (Discrete.mk i))).inv ≫
          ShortComplex.homologyMap
            (T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom := by
    -- This is `NatTrans.app_homology` for the universal evaluation-to-colimit transformation.
    simpa [discrete_colimit_inclusion] using
      (NatTrans.app_homology
        (τ := discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)
        (S := T))
  have h_nat' :
      (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj (Discrete.mk i))).hom ≫
          colimit.ι T.homology (Discrete.mk i) =
        ShortComplex.homologyMap
            (T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom := by
    -- Compose with the inverse evaluation comparison so that the left transport cancels.
    simpa [Category.assoc] using
      congrArg
        (fun f ↦
          (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj (Discrete.mk i))).hom ≫ f)
        h_nat
  have h_transport :
      ShortComplex.homologyMap ((e.counitIso.app F).app (Discrete.mk i)).inv ≫
          ShortComplex.homologyMap
            (T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom =
        termwiseHomologyIso.inv.app (Discrete.mk i) ≫
          colimit.ι T.homology (Discrete.mk i) := by
    -- The remaining evaluation-side transport is exactly the inverse component of the
    -- termwise homology identification.
    calc
      ShortComplex.homologyMap ((e.counitIso.app F).app (Discrete.mk i)).inv ≫
          ShortComplex.homologyMap
            (T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom =
        ShortComplex.homologyMap ((e.counitIso.app F).app (Discrete.mk i)).inv ≫
          (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj (Discrete.mk i))).hom ≫
            colimit.ι T.homology (Discrete.mk i) := by
              rw [← h_nat']
              simp [Category.assoc]
      _ =
        termwiseHomologyIso.inv.app (Discrete.mk i) ≫
          colimit.ι T.homology (Discrete.mk i) := by
            simp [termwiseHomologyIso, Category.assoc]
  have h_colimit_map :
      colimit.ι T.homology (Discrete.mk i) ≫ (colim.mapIso termwiseHomologyIso).hom =
        termwiseHomologyIso.hom.app (Discrete.mk i) ≫
          colimit.ι H (Discrete.mk i) := by
    -- Move the colimit map across the `i`-th cocone leg.
    simpa using
      (colimit.ι_map termwiseHomologyIso.hom (Discrete.mk i))
  have h_sigma :
      colimit.ι H (Discrete.mk i) ≫ (Sigma.isoColimit H).symm.hom =
        Sigma.ι (fun j ↦ (S j).homology) i := by
    -- Cancel the canonical sigma/colimit comparison on the `i`-th summand.
    have h_sigma_hom :
        Sigma.ι (fun j ↦ (S j).homology) i ≫ (Sigma.isoColimit H).hom =
          colimit.ι H (Discrete.mk i) := by
      simpa [H] using (Sigma.ι_isoColimit_hom (X := H) i)
    simpa [Category.assoc] using
      congrArg (fun f ↦ f ≫ (Sigma.isoColimit H).symm.hom) h_sigma_hom
  calc
    ShortComplex.homologyMap (Sigma.ι S i) ≫
        ((ShortComplex.homologyFunctor 𝒜).mapIso
          ((colimit.isColimit F).coconePointUniqueUpToIso
            (ShortComplex.isColimitColimitCocone F))).hom ≫
        (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
        (colim.mapIso termwiseHomologyIso).hom ≫
        (Sigma.isoColimit H).symm.hom =
        ShortComplex.homologyMap
          (((e.counitIso.app F).app (Discrete.mk i)).inv ≫
            T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
          (colim.mapIso termwiseHomologyIso).hom ≫
          (Sigma.isoColimit H).symm.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦
                  f ≫ (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
                    (colim.mapIso termwiseHomologyIso).hom ≫
                    (Sigma.isoColimit H).symm.hom)
                h_homology_leg
    _ =
      ShortComplex.homologyMap ((e.counitIso.app F).app (Discrete.mk i)).inv ≫
          ShortComplex.homologyMap
            (T.mapNatTrans (discrete_colimit_inclusion (𝒜 := 𝒜) (α := α) i)) ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
          (colim.mapIso termwiseHomologyIso).hom ≫
          (Sigma.isoColimit H).symm.hom := by
            rw [ShortComplex.homologyMap_comp]
            simp [Category.assoc]
    _ =
      termwiseHomologyIso.inv.app (Discrete.mk i) ≫
          colimit.ι T.homology (Discrete.mk i) ≫
          (colim.mapIso termwiseHomologyIso).hom ≫
          (Sigma.isoColimit H).symm.hom := by
            rw [h_transport]
            simp [Category.assoc]
    _ =
      colimit.ι H (Discrete.mk i) ≫ (Sigma.isoColimit H).symm.hom := by
        rw [Category.assoc, h_colimit_map]
        simp [Category.assoc]
    _ = Sigma.ι (fun j ↦ (S j).homology) i := h_sigma

/-- Helper for Lemma 13.33.5: the short-complex homology comparison for a termwise coproduct has
the expected `i`-th coproduct inclusion. -/
private theorem shortComplex_coproduct_homology_iso_hom_ι
    (p : ℤ) (K : α → CochainComplex 𝒜 ℤ) (i : α) :
    ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map
          (Sigma.ι K i)) ≫
        (shortComplex_coproduct_homology_iso (𝒜 := 𝒜) (α := α) p K).hom =
      Sigma.ι (fun j ↦ ((K j).sc p).homology) i := by
  let S : α → ShortComplex 𝒜 := fun j ↦ (K j).sc p
  let F : Discrete α ⥤ ShortComplex 𝒜 := Discrete.functor S
  let e := ShortComplex.functorEquivalence (Discrete α) 𝒜
  let T : ShortComplex (Discrete α ⥤ 𝒜) := e.inverse.obj F
  let H : Discrete α ⥤ 𝒜 := Discrete.functor fun j ↦ (S j).homology
  let termwiseHomologyIso : T.homology ≅ H :=
    Discrete.natIso fun j : Discrete α ↦
      (T.mapHomologyIso ((evaluation (Discrete α) 𝒜).obj j)).symm ≪≫
        (ShortComplex.homologyFunctor 𝒜).mapIso ((e.counitIso.app F).app j)
  have h_sc :
      (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map (Sigma.ι K i) ≫
          (PreservesCoproduct.iso
            (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K).hom =
        Sigma.ι S i := by
    simpa [S] using
      shortComplex_coproduct_inclusion_comp_preservesCoproductIso_hom
        (𝒜 := 𝒜) (α := α) p K i
  have h_sc_homology :
      ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map
            (Sigma.ι K i)) ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            (PreservesCoproduct.iso
              (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K)).hom =
        ShortComplex.homologyMap (Sigma.ι S i) := by
    -- First collapse the short-complex coproduct comparison itself.
    calc
      ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map
            (Sigma.ι K i)) ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            (PreservesCoproduct.iso
              (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K)).hom =
        ShortComplex.homologyMap
          (((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map
              (Sigma.ι K i)) ≫
            (PreservesCoproduct.iso
              (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K).hom) := by
              exact (ShortComplex.homologyMap_comp _ _).symm
      _ = ShortComplex.homologyMap (Sigma.ι S i) := by
            rw [h_sc]
  -- Route correction: peel off the outer `PreservesCoproduct.iso` first, then invoke the middle
  -- colimit transport lemma proved above.
  calc
    ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map
          (Sigma.ι K i)) ≫
        (shortComplex_coproduct_homology_iso (𝒜 := 𝒜) (α := α) p K).hom =
      ShortComplex.homologyMap
          ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p).map
            (Sigma.ι K i)) ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            (PreservesCoproduct.iso
              (HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) p) K)).hom ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            ((colimit.isColimit F).coconePointUniqueUpToIso
              (ShortComplex.isColimitColimitCocone F))).hom ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
          (colim.mapIso termwiseHomologyIso).hom ≫
          (Sigma.isoColimit H).symm.hom := by
            rfl
    _ =
      ShortComplex.homologyMap (Sigma.ι S i) ≫
          ((ShortComplex.homologyFunctor 𝒜).mapIso
            ((colimit.isColimit F).coconePointUniqueUpToIso
              (ShortComplex.isColimitColimitCocone F))).hom ≫
          (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
          (colim.mapIso termwiseHomologyIso).hom ≫
          (Sigma.isoColimit H).symm.hom := by
            simpa [Category.assoc] using
              congrArg
                (fun f ↦
                  f ≫ ((ShortComplex.homologyFunctor 𝒜).mapIso
                      ((colimit.isColimit F).coconePointUniqueUpToIso
                        (ShortComplex.isColimitColimitCocone F))).hom ≫
                    (T.mapHomologyIso (colim : (Discrete α ⥤ 𝒜) ⥤ 𝒜)).hom ≫
                    (colim.mapIso termwiseHomologyIso).hom ≫
                    (Sigma.isoColimit H).symm.hom)
                h_sc_homology
    _ = Sigma.ι (fun j ↦ ((K j).sc p).homology) i := by
      simpa [S, F, e, T, H, termwiseHomologyIso] using
        shortComplex_coproduct_homology_iso_middle_component
          (𝒜 := 𝒜) (α := α) p K i

/-- Helper for Lemma 13.33.5: the previous homology comparison sends the localized `i`-th
coproduct injection to the `i`-th coproduct injection on homology. -/
private theorem coproduct_homology_iso_hom_ι
    (p : ℤ) (K : α → CochainComplex 𝒜 ℤ) (i : α) :
    (homologyFunctor 𝒜 p).map (Q.map (Sigma.ι K i)) ≫
        (coproduct_homology_iso_of_exact (𝒜 := 𝒜) (α := α) (p := p) K).hom =
      Sigma.ι (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i := by
  let eH :
      ∀ j, (K j).homology p ≅ (homologyFunctor 𝒜 p).obj (Q.obj (K j)) :=
    fun j ↦ ((homologyFunctorFactors 𝒜 p).app (K j)).symm
  have h_nat :
      ((homologyFunctorFactors 𝒜 p).hom.app (K i) ≫
          HomologicalComplex.homologyMap (Sigma.ι K i) p) ≫
        ((homologyFunctorFactors 𝒜 p).app (∐ K)).inv =
      (homologyFunctor 𝒜 p).map (Q.map (Sigma.ι K i)) := by
    -- Strip off the outer derived-homology transport using the standard naturality square.
    calc
      ((homologyFunctorFactors 𝒜 p).hom.app (K i) ≫
          HomologicalComplex.homologyMap (Sigma.ι K i) p) ≫
        ((homologyFunctorFactors 𝒜 p).app (∐ K)).inv =
      (homologyFunctor 𝒜 p).map (Q.map (Sigma.ι K i)) ≫
          (homologyFunctorFactors 𝒜 p).hom.app (∐ K) ≫
            ((homologyFunctorFactors 𝒜 p).app (∐ K)).inv := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦ f ≫ ((homologyFunctorFactors 𝒜 p).app (∐ K)).inv)
                  (DerivedCategory.homologyFunctorFactors_hom_naturality (Sigma.ι K i) p)
      _ = (homologyFunctor 𝒜 p).map (Q.map (Sigma.ι K i)) := by
            simp [Category.assoc]
  have h_short :
      HomologicalComplex.homologyMap (Sigma.ι K i) p ≫
          (shortComplex_coproduct_homology_iso (𝒜 := 𝒜) (α := α) p K).hom =
        Sigma.ι (fun j ↦ (K j).homology p) i := by
    -- Reuse the short-complex coproduct comparison proved just above.
    simpa using
      shortComplex_coproduct_homology_iso_hom_ι
        (𝒜 := 𝒜) (α := α) p K i
  -- Route correction: after the naturality square removes the outer derived transport, the
  -- remaining coproduct-inclusion statement is exactly the short-complex formula plus `Sigma.map`.
  calc
    (homologyFunctor 𝒜 p).map (Q.map (Sigma.ι K i)) ≫
        (coproduct_homology_iso_of_exact (𝒜 := 𝒜) (α := α) (p := p) K).hom =
      (((homologyFunctorFactors 𝒜 p).hom.app (K i) ≫
            HomologicalComplex.homologyMap (Sigma.ι K i) p) ≫
          ((homologyFunctorFactors 𝒜 p).app (∐ K)).inv) ≫
            (shortComplex_coproduct_homology_iso (𝒜 := 𝒜) (α := α) p K).hom ≫
            (Sigma.mapIso eH).hom := by
              rw [← h_nat]
              rfl
    _ =
      (homologyFunctorFactors 𝒜 p).hom.app (K i) ≫
          Sigma.ι (fun j ↦ (K j).homology p) i ≫
            (Sigma.mapIso eH).hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun f ↦ ((homologyFunctorFactors 𝒜 p).hom.app (K i) ≫ f) ≫
                    (Sigma.mapIso eH).hom)
                  h_short
    _ = Sigma.ι (fun j ↦ (homologyFunctor 𝒜 p).obj (Q.obj (K j))) i := by
          rw [Category.assoc, Sigma.ι_map_assoc]
          simp [eH, Category.assoc]

/-- Helper for Lemma 13.33.5: exact coproducts send a termwise quasi-isomorphism of complexes to
another quasi-isomorphism on the coproduct. -/
private theorem coproduct_quasiIso_of_termwise
    {M K : α → CochainComplex 𝒜 ℤ}
    (σ : ∀ i, M i ⟶ K i) (hσ : ∀ i, QuasiIso (σ i)) :
    QuasiIso (Limits.Sigma.desc (fun i ↦ σ i ≫ Limits.Sigma.ι K i)) := by
  let s : ∐ M ⟶ ∐ K := Limits.Sigma.desc (fun i ↦ σ i ≫ Limits.Sigma.ι K i)
  rw [quasiIso_iff]
  intro p
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := homologyFunctor 𝒜 p
  let eM : H.obj (Q.obj (∐ M)) ≅ ∐ fun i ↦ H.obj (Q.obj (M i)) :=
    coproduct_homology_iso_of_exact (𝒜 := 𝒜) (α := α) (p := p) M
  let eK : H.obj (Q.obj (∐ K)) ≅ ∐ fun i ↦ H.obj (Q.obj (K i)) :=
    coproduct_homology_iso_of_exact (𝒜 := 𝒜) (α := α) (p := p) K
  let eσ :
      ∐ (fun i ↦ H.obj (Q.obj (M i))) ≅ ∐ (fun i ↦ H.obj (Q.obj (K i))) :=
    Limits.Sigma.mapIso fun i ↦
      letI : IsIso (Q.map (σ i)) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso (𝒜 := 𝒜) (σ i)).2 (hσ i)
      H.mapIso (asIso (Q.map (σ i)))
  have h_conj :
      eM.inv ≫ H.map (Q.map s) ≫ eK.hom = eσ.hom := by
    -- Compare the conjugated derived-homology map on each coproduct summand.
    apply Limits.Sigma.hom_ext
    intro i
    have hιM :
        Sigma.ι (fun j ↦ H.obj (Q.obj (M j))) i ≫ eM.inv =
          H.map (Q.map (Sigma.ι M i)) := by
      simpa [eM, Category.assoc] using
        congrArg
          (fun f ↦ f ≫ eM.inv)
          (coproduct_homology_iso_hom_ι (𝒜 := 𝒜) (α := α) (p := p) M i)
    calc
      Sigma.ι (fun j ↦ H.obj (Q.obj (M j))) i ≫ eM.inv ≫ H.map (Q.map s) ≫ eK.hom =
        H.map (Q.map (Sigma.ι M i)) ≫ H.map (Q.map s) ≫ eK.hom := by
          rw [hιM]
      _ =
        H.map (Q.map ((Sigma.ι M i) ≫ s)) ≫ eK.hom := by
          simp [Functor.map_comp, Category.assoc]
      _ =
        H.map (Q.map (σ i ≫ Sigma.ι K i)) ≫ eK.hom := by
          rw [Limits.Sigma.ι_desc_assoc]
      _ =
        H.map (Q.map (σ i)) ≫ H.map (Q.map (Sigma.ι K i)) ≫ eK.hom := by
          simp [Functor.map_comp, Category.assoc]
      _ =
        H.map (Q.map (σ i)) ≫ Sigma.ι (fun j ↦ H.obj (Q.obj (K j))) i := by
          rw [coproduct_homology_iso_hom_ι (𝒜 := 𝒜) (α := α) (p := p) K i]
      _ =
        Sigma.ι (fun j ↦ H.obj (Q.obj (M j))) i ≫ eσ.hom := by
          simp [eσ, Category.assoc]
  have hHmapIso : IsIso (H.map (Q.map s)) := by
    -- The conjugated map is the coproduct of the pointwise homology isomorphisms.
    have hconjIso : IsIso (eM.inv ≫ H.map (Q.map s) ≫ eK.hom) := by
      rw [h_conj]
      infer_instance
    letI : IsIso (eM.inv ≫ H.map (Q.map s) ≫ eK.hom) := hconjIso
    let e : H.obj (Q.obj (∐ M)) ≅ H.obj (Q.obj (∐ K)) :=
      eM ≪≫ asIso (eM.inv ≫ H.map (Q.map s) ≫ eK.hom) ≪≫ eK.symm
    have he : e.hom = H.map (Q.map s) := by
      simp [e, Category.assoc]
    rw [← he]
    infer_instance
  let eHM : (∐ M).homology p ≅ H.obj (Q.obj (∐ M)) := (homologyFunctorFactors 𝒜 p).app (∐ M)
  let eHK : (∐ K).homology p ≅ H.obj (Q.obj (∐ K)) := (homologyFunctorFactors 𝒜 p).app (∐ K)
  have h_nat :
      eHM.hom ≫ HomologicalComplex.homologyMap s p =
        H.map (Q.map s) ≫ eHK.hom := by
    simpa [eHM, eHK, Category.assoc] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality s p)
  have h_homologyMap :
      HomologicalComplex.homologyMap s p = eHM.inv ≫ H.map (Q.map s) ≫ eHK.hom := by
    -- Strip off the source and target homology-factor identifications.
    calc
      HomologicalComplex.homologyMap s p =
        eHM.inv ≫ eHM.hom ≫ HomologicalComplex.homologyMap s p := by
          simp [Category.assoc]
      _ = eHM.inv ≫ (H.map (Q.map s) ≫ eHK.hom) := by
            rw [h_nat]
            simp [Category.assoc]
      _ = eHM.inv ≫ H.map (Q.map s) ≫ eHK.hom := by
            simp [Category.assoc]
  rw [h_homologyMap]
  infer_instance

/-- Helper for Lemma 13.33.5: if a summand composite of a fixed roof vanishes in the derived
category, then after refining the denominator it vanishes by an actual complex map. -/
private theorem summand_zero_lift_through_denominator
    (K : α → CochainComplex 𝒜 ℤ) {M L₀ : CochainComplex 𝒜 ℤ}
    (s : M ⟶ ∐ K) (hs : QuasiIso s) (f : M ⟶ L₀) (i : α)
    (hi : Q.map (Sigma.ι K i) ≫ inv (Q.map s) ≫ Q.map f = 0) :
    ∃ (P : CochainComplex 𝒜 ℤ) (σ : P ⟶ K i) (_ : QuasiIso σ) (g : P ⟶ M),
      σ ≫ Sigma.ι K i = g ≫ s ∧ g ≫ f = 0 := by
  let β : Q.obj (K i) ⟶ Q.obj M := Q.map (Sigma.ι K i) ≫ inv (Q.map s)
  obtain ⟨P₀, σ₀, hσ₀Iso, g₀, hβ⟩ := DerivedCategory.right_fac β
  have hσ₀ : QuasiIso σ₀ := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hσ₀Iso
    exact hσ₀Iso
  have hmap :
      Q.map (σ₀ ≫ Sigma.ι K i) = Q.map (g₀ ≫ s) := by
    -- Clear the fixed denominator `s` to compare the two numerators in the localization.
    calc
      Q.map (σ₀ ≫ Sigma.ι K i) = Q.map σ₀ ≫ (Q.map (Sigma.ι K i) ≫ inv (Q.map s)) ≫ Q.map s := by
        simp [β, Functor.map_comp, Category.assoc]
      _ = Q.map σ₀ ≫ β ≫ Q.map s := by
        rfl
      _ = Q.map σ₀ ≫ (inv (Q.map σ₀) ≫ Q.map g₀) ≫ Q.map s := by
        rw [hβ]
      _ = Q.map g₀ ≫ Q.map s := by
        simp [Category.assoc]
      _ = Q.map (g₀ ≫ s) := by
        simp [Functor.map_comp, Category.assoc]
  obtain ⟨P₁, τ₁, hτ₁, hτ₁eq⟩ :=
    (MorphismProperty.map_eq_iff_precomp Q Qis (σ₀ ≫ Sigma.ι K i) (g₀ ≫ s)).mp hmap
  have hzero_g₀ : Q.map (g₀ ≫ f) = 0 := by
    -- The vanishing hypothesis becomes a numerator equality after refining the first roof once.
    calc
      Q.map (g₀ ≫ f) = Q.map g₀ ≫ Q.map f := by
        simp [Functor.map_comp]
      _ = Q.map σ₀ ≫ β ≫ Q.map f := by
        rw [hβ]
        simp [Category.assoc]
      _ = Q.map σ₀ ≫ (Q.map (Sigma.ι K i) ≫ inv (Q.map s)) ≫ Q.map f := by
        rfl
      _ = Q.map σ₀ ≫ 0 := by
        rw [hi]
      _ = 0 := by
        simp
  have hzero_τ₁ :
      Q.map (τ₁ ≫ g₀ ≫ f) = Q.map (0 : P₁ ⟶ L₀) := by
    -- Precompose the vanishing numerator equality by the refinement `τ₁`.
    calc
      Q.map (τ₁ ≫ g₀ ≫ f) = Q.map τ₁ ≫ Q.map (g₀ ≫ f) := by
        simp [Functor.map_comp, Category.assoc]
      _ = Q.map τ₁ ≫ 0 := by
        rw [hzero_g₀]
      _ = Q.map (0 : P₁ ⟶ L₀) := by
        simp
  obtain ⟨P, τ₂, hτ₂, hτ₂zero⟩ :=
    (MorphismProperty.map_eq_iff_precomp Q Qis (τ₁ ≫ g₀ ≫ f) (0 : P₁ ⟶ L₀)).mp hzero_τ₁
  let σ : P ⟶ K i := τ₂ ≫ τ₁ ≫ σ₀
  let g : P ⟶ M := τ₂ ≫ τ₁ ≫ g₀
  have hσ : QuasiIso σ := by
    let _ : QuasiIso τ₂ := hτ₂
    let _ : QuasiIso τ₁ := hτ₁
    let _ : QuasiIso σ₀ := hσ₀
    simpa [σ, Category.assoc] using (inferInstance : QuasiIso (τ₂ ≫ τ₁ ≫ σ₀))
  refine ⟨P, σ, hσ, g, ?_, ?_⟩
  · -- The refined denominator now equalizes the two maps into the coproduct on the nose.
    calc
      σ ≫ Sigma.ι K i = τ₂ ≫ (τ₁ ≫ (σ₀ ≫ Sigma.ι K i)) := by
        simp [σ, Category.assoc]
      _ = τ₂ ≫ (τ₁ ≫ (g₀ ≫ s)) := by
        rw [hτ₁eq]
      _ = g ≫ s := by
        simp [g, Category.assoc]
  · -- A second refinement forces the numerator to vanish already in the complex category.
    calc
      g ≫ f = τ₂ ≫ (τ₁ ≫ g₀ ≫ f) := by
        simp [g, Category.assoc]
      _ = τ₂ ≫ (0 : P₁ ⟶ L₀) := hτ₂zero
      _ = 0 := by
        simp

/-- Helper for Lemma 13.33.5: a morphism from the localized termwise coproduct to a represented
target is zero as soon as all summand composites vanish. -/
private theorem derived_coproduct_zero_of_vanish_on_summands
    (K : α → CochainComplex 𝒜 ℤ) {L₀ : CochainComplex 𝒜 ℤ}
    {γ : Q.obj (∐ K) ⟶ Q.obj L₀}
    (hγ : ∀ i, Q.map (Sigma.ι K i) ≫ γ = 0) :
    γ = 0 := by
  classical
  obtain ⟨M, s, hsIso, f, hroof⟩ := DerivedCategory.right_fac γ
  have hs : QuasiIso s := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hsIso
    exact hsIso
  have hsummand :
      ∀ i, Q.map (Sigma.ι K i) ≫ inv (Q.map s) ≫ Q.map f = 0 := by
    intro i
    -- Rewrite each summand composite using the chosen roof for `γ`.
    calc
      Q.map (Sigma.ι K i) ≫ inv (Q.map s) ≫ Q.map f =
        Q.map (Sigma.ι K i) ≫ γ := by
          rw [hroof]
      _ = 0 := hγ i
  choose P σ hσ g hfac hzero using
    fun i ↦
      summand_zero_lift_through_denominator (𝒜 := 𝒜) (α := α) K s hs f i (hsummand i)
  let δ : ∐ P ⟶ ∐ K := Limits.Sigma.desc (fun i ↦ σ i ≫ Limits.Sigma.ι K i)
  let h : ∐ P ⟶ M := Limits.Sigma.desc g
  have hδ : δ = h ≫ s := by
    -- Assemble the termwise equalities into an equality of coproduct maps.
    apply Limits.Sigma.hom_ext
    intro i
    calc
      Limits.Sigma.ι P i ≫ δ = σ i ≫ Limits.Sigma.ι K i := by
        simp [δ, Category.assoc]
      _ = g i ≫ s := hfac i
      _ = Limits.Sigma.ι P i ≫ h ≫ s := by
        simp [h, Category.assoc]
  have hhf : h ≫ f = 0 := by
    -- The assembled numerator vanishes because each summand numerator already does.
    apply Limits.Sigma.hom_ext
    intro i
    calc
      Limits.Sigma.ι P i ≫ h ≫ f = g i ≫ f := by
        simp [h, Category.assoc]
      _ = 0 := hzero i
      _ = Limits.Sigma.ι P i ≫ (0 : ∐ P ⟶ L₀) := by
        simp
  have hδQ : QuasiIso δ :=
    coproduct_quasiIso_of_termwise (𝒜 := 𝒜) (α := α) σ hσ
  let _ : QuasiIso δ := hδQ
  have hinv :
      inv (Q.map s) = inv (Q.map δ) ≫ Q.map h := by
    -- Cancel the common postcomposition by `Q.map s` after using `δ = h ≫ s`.
    apply (cancel_mono (Q.map s)).1
    calc
      inv (Q.map s) ≫ Q.map s = 𝟙 _ := by
        simp
      _ = inv (Q.map δ) ≫ Q.map δ := by
        simp
      _ = inv (Q.map δ) ≫ (Q.map h ≫ Q.map s) := by
        rw [hδ]
        simp [Functor.map_comp, Category.assoc]
      _ = (inv (Q.map δ) ≫ Q.map h) ≫ Q.map s := by
        simp [Category.assoc]
  -- Replace the original roof by the refined denominator `δ`, whose numerator is already zero.
  calc
    γ = inv (Q.map s) ≫ Q.map f := hroof
    _ = (inv (Q.map δ) ≫ Q.map h) ≫ Q.map f := by
          rw [hinv]
    _ = inv (Q.map δ) ≫ Q.map (h ≫ f) := by
          simp [Functor.map_comp, Category.assoc]
    _ = 0 := by
          simp [hhf, Category.assoc]

/-- Helper for Lemma 13.33.5: a morphism out of the localized termwise coproduct is determined by
its composites with the coproduct injections. -/
private theorem derived_coproduct_hom_ext
    (K : α → CochainComplex 𝒜 ℤ)
    {L : DerivedCategory 𝒜} {β₁ β₂ : Q.obj (∐ K) ⟶ L}
    (hβ : ∀ i, Q.map (Sigma.ι K i) ≫ β₁ = Q.map (Sigma.ι K i) ≫ β₂) :
    β₁ = β₂ := by
  let e := Q.objObjPreimageIso L
  have hzero_repr :
      ((β₁ - β₂) ≫ e.hom) = 0 := by
    -- Route correction: reduce equality to the zero test for the difference morphism into the
    -- chosen represented target `Q.obj (Q.objPreimage L)`.
    apply derived_coproduct_zero_of_vanish_on_summands (𝒜 := 𝒜) (α := α) K
    intro i
    calc
      Q.map (Sigma.ι K i) ≫ ((β₁ - β₂) ≫ e.hom) =
        (Q.map (Sigma.ι K i) ≫ (β₁ - β₂)) ≫ e.hom := by
          simp [Category.assoc]
      _ =
        (Q.map (Sigma.ι K i) ≫ β₁ - Q.map (Sigma.ι K i) ≫ β₂) ≫ e.hom := by
          rw [Preadditive.comp_sub]
      _ = 0 := by
          rw [hβ i]
          simp
  apply sub_eq_zero.mp
  apply (cancel_mono e.hom).1
  simpa [Category.assoc] using hzero_repr

-- Proof sketch: exact countable coproducts imply that the localization functor to the derived
-- category preserves the coproduct of any countable family of cochain complexes.
private theorem derivedCategory_Q_preserves_coproduct_of_exact
    (K : α → CochainComplex 𝒜 ℤ) :
    PreservesColimit (Discrete.functor K) Q := by
  classical
  have hQc :
      IsColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i)) := by
    -- Build the coproduct lift exactly as in the source proof: choose roofs for each summand map,
    -- then take the termwise coproduct of the chosen numerators and denominators.
    refine mkCofanColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i)) (fun s ↦ ?_) ?_ ?_
    · let e := Q.objObjPreimageIso s.pt
      choose M σ hσ f hfac using
        fun i ↦ exists_quasiIso_fraction_to_preimage (𝒜 := 𝒜) (α := s.ι.app i)
      let σsum : ∐ M ⟶ ∐ K := Limits.Sigma.desc (fun i ↦ σ i ≫ Limits.Sigma.ι K i)
      let fsum : ∐ M ⟶ Q.objPreimage s.pt := Limits.Sigma.desc f
      let _ : QuasiIso σsum :=
        coproduct_quasiIso_of_termwise (𝒜 := 𝒜) (α := α) σ hσ
      exact inv (Q.map σsum) ≫ Q.map fsum ≫ e.hom
    · intro s i
      let e := Q.objObjPreimageIso s.pt
      choose M σ hσ f hfac using
        fun j ↦ exists_quasiIso_fraction_to_preimage (𝒜 := 𝒜) (α := s.ι.app j)
      let σsum : ∐ M ⟶ ∐ K := Limits.Sigma.desc (fun j ↦ σ j ≫ Limits.Sigma.ι K j)
      let fsum : ∐ M ⟶ Q.objPreimage s.pt := Limits.Sigma.desc f
      let _ : QuasiIso σsum :=
        coproduct_quasiIso_of_termwise (𝒜 := 𝒜) (α := α) σ hσ
      -- Clear the quasi-isomorphic denominator `σ i` to verify the required factorization.
      apply (cancel_epi (Q.map (σ i))).1
      calc
        Q.map (σ i) ≫
            (Q.map (Sigma.ι K i) ≫ (inv (Q.map σsum) ≫ Q.map fsum ≫ e.hom)) =
          Q.map (Limits.Sigma.ι M i) ≫ Q.map σsum ≫ inv (Q.map σsum) ≫ Q.map fsum ≫ e.hom := by
            simp [σsum, Functor.map_comp, Category.assoc, Limits.Sigma.ι_desc_assoc]
        _ = Q.map (Limits.Sigma.ι M i) ≫ Q.map fsum ≫ e.hom := by
              simp [Category.assoc]
        _ = Q.map (f i) ≫ e.hom := by
              simp [fsum, Functor.map_comp, Category.assoc, Limits.Sigma.ι_desc_assoc]
        _ = Q.map (σ i) ≫ s.ι.app i := by
              rw [hfac i]
    · intro s m hm
      let e := Q.objObjPreimageIso s.pt
      choose M σ hσ f hfac using
        fun j ↦ exists_quasiIso_fraction_to_preimage (𝒜 := 𝒜) (α := s.ι.app j)
      let σsum : ∐ M ⟶ ∐ K := Limits.Sigma.desc (fun j ↦ σ j ≫ Limits.Sigma.ι K j)
      let fsum : ∐ M ⟶ Q.objPreimage s.pt := Limits.Sigma.desc f
      let _ : QuasiIso σsum :=
        coproduct_quasiIso_of_termwise (𝒜 := 𝒜) (α := α) σ hσ
      apply derived_coproduct_hom_ext (𝒜 := 𝒜) (α := α) K
      intro i
      calc
        Q.map (Sigma.ι K i) ≫
            (inv (Q.map σsum) ≫ Q.map fsum ≫ e.hom) =
          s.ι.app i := by
            apply (cancel_epi (Q.map (σ i))).1
            calc
              Q.map (σ i) ≫
                  (Q.map (Sigma.ι K i) ≫
                    (inv (Q.map σsum) ≫ Q.map fsum ≫ e.hom)) =
                Q.map (Limits.Sigma.ι M i) ≫ Q.map σsum ≫ inv (Q.map σsum) ≫
                    Q.map fsum ≫ e.hom := by
                      simp [σsum, Functor.map_comp, Category.assoc, Limits.Sigma.ι_desc_assoc]
              _ = Q.map (Limits.Sigma.ι M i) ≫ Q.map fsum ≫ e.hom := by
                    simp [Category.assoc]
              _ = Q.map (f i) ≫ e.hom := by
                    simp [fsum, Functor.map_comp, Category.assoc, Limits.Sigma.ι_desc_assoc]
              _ = Q.map (σ i) ≫ s.ι.app i := by
                    rw [hfac i]
              _ = Q.map (σ i) ≫ (Q.map (Sigma.ι K i) ≫ m) := by
                    rw [hm i]
        _ = Q.map (Sigma.ι K i) ≫ m := by
              simpa [Category.assoc]
  exact preservesColimit_of_preserves_colimit_cocone (coproductIsCoproduct K) hQc

end

-- `CountableAB4.ofShape` is small-universe, so transport it across `Shrink` for arbitrary
-- countable index types.
private theorem hasExactColimitsOfShape_of_countable
    {C : Type u} [Category.{v} C] [HasCountableCoproducts C] [CountableAB4 C]
    (α : Type uI) [Countable α] :
    HasExactColimitsOfShape (Discrete α) C := by
  letI : Countable (Shrink.{0} α) := Countable.of_equiv α (equivShrink.{0} α)
  letI : HasExactColimitsOfShape (Discrete (Shrink.{0} α)) C :=
    CountableAB4.ofShape (Shrink.{0} α)
  exact HasExactColimitsOfShape.of_domain_equivalence C
    (Discrete.equivalence (equivShrink.{0} α)).symm

section

variable [HasCountableCoproducts 𝒜] [CountableAB4 𝒜] [Countable α]

-- Proof sketch: recover exactness of `α`-indexed coproducts from the countable `AB4` owner on
-- `𝒜`, then apply the exact-coproduct preservation lemma above.
/-- Exact countable direct sums make the localization functor `DerivedCategory.Q` preserve the
coproduct of any countable family of cochain complexes. -/
theorem derivedCategory_Q_preserves_countableCoproduct
    (K : α → CochainComplex 𝒜 ℤ) :
    PreservesColimit (Discrete.functor K) Q := by
  letI : HasExactColimitsOfShape (Discrete α) 𝒜 := hasExactColimitsOfShape_of_countable α
  exact derivedCategory_Q_preserves_coproduct_of_exact K

/-- The image in the derived category of the termwise direct sum of a countable family of
cochain complexes is a coproduct of the corresponding family of derived-category objects. -/
noncomputable def derivedCategory_coproduct_isColimit_of_termwise_countableDirectSums
    (K : α → CochainComplex 𝒜 ℤ) :
    IsColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i)) :=
  letI := derivedCategory_Q_preserves_countableCoproduct K
  isColimitOfHasCoproductOfPreservesColimit Q K

attribute [instance] derivedCategory_Q_preserves_countableCoproduct

end

section

variable [HasCountableCoproducts 𝒜] [CountableAB4 𝒜]

-- Proof sketch: for each countable index type `α`, transport the small-universe owner
-- `CountableAB4.ofShape` across `Shrink` to recover exactness of `α`-indexed coproducts in `𝒜`,
-- then apply the canonical cofan theorem above to each family of complexes.
/-- Exact countable coproducts in `𝒜` induce `α`-indexed coproducts in `D(\mathcal A)`. -/
noncomputable instance derivedCategory_hasCoproductsOfShape_of_exactCountableCoproducts
    (α : Type uI) [Countable α] :
    HasCoproductsOfShape α (DerivedCategory 𝒜) where
  has_colimit F := by
    letI : HasExactColimitsOfShape (Discrete α) 𝒜 := hasExactColimitsOfShape_of_countable α
    let X : α → DerivedCategory 𝒜 := fun i ↦ F.obj ⟨i⟩
    let K : α → CochainComplex 𝒜 ℤ := fun i ↦ Q.objPreimage (X i)
    let eK : ∀ i, Q.obj (K i) ≅ X i := fun i ↦ Q.objObjPreimageIso (X i)
    let e : Discrete.functor (fun i ↦ Q.obj (K i)) ≅ Discrete.functor X :=
      Discrete.natIso fun i : Discrete α ↦ eK i.as
    have hX :
        IsColimit (Cofan.mk (Q.obj (∐ K)) fun i ↦ (eK i).inv ≫ Q.map (Sigma.ι K i)) := by
      exact (IsColimit.precomposeInvEquiv e
        (Cofan.mk (Q.obj (∐ K)) fun i ↦ Q.map (Sigma.ι K i))).symm
        (derivedCategory_coproduct_isColimit_of_termwise_countableDirectSums K)
    refine HasColimit.mk
      ⟨(Cocone.precompose Discrete.natIsoFunctor.hom).obj
          (Cofan.mk (Q.obj (∐ K)) fun i ↦ (eK i).inv ≫ Q.map (Sigma.ι K i)),
        ?_⟩
    exact (IsColimit.precomposeHomEquiv _ _).symm hX

/-- Exact countable coproducts in `𝒜` induce countable coproducts in `D(\mathcal A)`. -/
noncomputable instance derivedCategory_hasCountableCoproducts_of_exactCountableCoproducts :
    HasCountableCoproducts (DerivedCategory 𝒜) where
  out _ := inferInstance

end

end

end CategoryTheory
