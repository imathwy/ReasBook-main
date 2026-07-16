import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Lemma_15_67_4
import stacks_proof.stacks_project.Chap15.Lemma_15_67_13
import stacks_proof.stacks_project.Chap15.Lemma_15_60_3
import stacks_proof.stacks_project.Chap15.Lemma_15_77_1
import stacks_proof.stacks_project.Chap15.Definition_15_75_1
import stacks_proof.stacks_project.Chap10.Lemma_10_79_4

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: localization of pseudo-coherent derived objects, truncation triangles in the
  standard `t`-structure, and control of the localized upper truncation by the chapter owners for
  perfectness, tor-amplitude, and compatible biproduct splittings;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `HasTorAmplitudeGE`,
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraHomologyComparison`,
  `t.triangleLEGE_distinguished`,
  `existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge`;
- best owner abstraction: the source-facing localization theorem should state its conclusions
  directly in terms of the owner truncation triangle for
  `K ⊗[R]^L[Localization.Away f]`, together with the canonical owners
  `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and
  `derivedTensorWithAlgebraHomologyComparison`, not via a second public package or local wrapper
  alias;
- primitive data: the localized object `K ⊗_R^{\mathbf L} R_f`, the canonical truncation triangle
  from `t.triangleLEGE_distinguished`, and its truncation maps;
- derived API: perfectness and tor-amplitude of `τ_{\ge i + 1}`, together with the
  unique compatible splitting of the localized truncation triangle.

Source/core/bridge triage:
- `source-facing`: the existential localization theorem below;
- `core/canonical`: `DerivedCategory.IsPerfect`, `HasTorAmplitudeGE`, and
  `derivedTensorWithAlgebraHomologyComparison`, with the truncation triangle owned by
  `t.triangleLEGE_distinguished`;
- `bridge/view`: the residue-field specialization of
  `derivedTensorWithAlgebraHomologyComparison`, together with the native compatibility equations
  on the canonical truncation maps; the splitting itself should stay in the owner-level `∃! e`
  form from Lemma `15.77.1`.
-/

section

variable (𝔭 : PrimeSpectrum R)

local notation "κ" => 𝔭.asIdeal.ResidueField
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

/-- Helper for Lemma 15.77.2: a pseudo-coherent derived object admits a bounded-above finite
projective `Q.objPreimage`-style model together with explicit termwise finiteness and
projectivity data. -/
private theorem bounded_above_finite_projective_model_of_isPseudoCoherent
    (K : DMod) (hK : K.IsPseudoCoherent) :
    ∃ P : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R),
      ∃ b : ℤ, ∃ eK : K ≅ DerivedCategory.Q.obj (P : Cpx),
        (P : Cpx).IsStrictlyLE b ∧
          (∀ n : ℤ, Module.Finite R ((P : Cpx).X n)) ∧
            ∀ n : ℤ, Module.Projective R ((P : Cpx).X n) := by
  rcases hK with ⟨E, ⟨b, hEb⟩, hEfree, α, hα⟩
  let P : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R) :=
    ⟨⟨E, (CochainComplex.minus_iff (ModuleCat R) E).2 ⟨b, hEb⟩⟩, fun n ↦ by
      rcases hEfree n with ⟨hfree, hfinite⟩
      let _ : Module.Free R (E.X n) := hfree
      exact ⟨hfinite, inferInstance⟩⟩
  let _ : IsIso α := hα
  refine ⟨P, b, (asIso α).symm, hEb, ?_, ?_⟩
  · intro n
    -- Proof comment: the owner package on `P` already records finite projectivity termwise.
    exact (P.term_mem n).1
  · intro n
    -- Proof comment: keep the projective half of the same termwise finite-projective witness.
    exact (P.term_mem n).2

/-- Helper for Lemma 15.77.2: termwise projective complexes are termwise flat. -/
private theorem isTermwiseFlat_of_projective_terms
    (P : Cpx) (hPprojective : ∀ n : ℤ, Module.Projective R (P.X n)) :
    P.IsTermwiseFlat := by
  intro n
  exact Module.Flat.of_projective (R := R) (M := P.X n)

/-- Helper for Lemma 15.77.2: the derived homology map of `Q.map β` is the ordinary homology map
conjugated by the standard comparison isomorphisms `homologyFunctorFactors.app`. -/
private theorem homologyFunctor_map_Q_eq_conjugate_homologyMap
    {E L : Cpx} (β : E ⟶ L) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) i).map (DerivedCategory.Q.map β) =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E).hom ≫
        HomologicalComplex.homologyMap β i ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L).inv := by
  let eE := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app E
  let eL := (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app L
  have hnat :
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map (DerivedCategory.Q.map β) ≫ eL.hom =
        eE.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Proof comment: naturality of `homologyFunctorFactors` is exactly the bridge from the
    -- derived homology map of `Q.map β` to the cochain-level homology map of `β`.
    simpa using
      (DerivedCategory.homologyFunctorFactors_hom_naturality (C := ModuleCat R) β i)
  have hpost :
      ((DerivedCategory.homologyFunctor (ModuleCat R) i).map (DerivedCategory.Q.map β) ≫ eL.hom) ≫
          eL.inv =
        eE.hom ≫ HomologicalComplex.homologyMap β i ≫ eL.inv := by
    -- Proof comment: postcomposing by the inverse target comparison exposes the desired
    -- conjugated form.
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ eL.inv) hnat
  -- Proof comment: the target comparison iso cancels on the left, leaving the conjugated
  -- ordinary homology map.
  simpa [Category.assoc] using hpost

/-- Helper for Lemma 15.77.2: the homology map of an arbitrary representative roof conjugates to
the derived homology map of the represented morphism. -/
private theorem q_representative_homologyMap_conjugated
    {T : Type u} [CommRing T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (f : K ⟶ L)
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let eSrc : (HT i).obj K ≅ Y.homology i :=
      ((HT i).mapIso eY).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
    let L' := DerivedCategory.Q.objPreimage L
    let eL : (HT i).obj L ≅ L'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
    HomologicalComplex.homologyMap β i =
      eSrc.inv ≫ (HT i).map f ≫ eL.hom := by
  let HT := DerivedCategory.homologyFunctor (ModuleCat T)
  let eSrc : (HT i).obj K ≅ Y.homology i :=
    ((HT i).mapIso eY).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let L' := DerivedCategory.Q.objPreimage L
  let eL : (HT i).obj L ≅ L'.homology i :=
    ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  let eQL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  let ηY := (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let ηL := (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  have hnat :
      (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        ηY.hom ≫ HomologicalComplex.homologyMap β i := by
    -- Proof comment: naturality of `homologyFunctorFactors` identifies the represented derived
    -- homology map with the chain-level homology map on `β`.
    simpa [ηY, ηL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat T) β i)
  have hconj :
      HomologicalComplex.homologyMap β i =
        ηY.inv ≫ (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom := by
    have hpre :
        ηY.inv ≫ (ηY.hom ≫ HomologicalComplex.homologyMap β i) =
          ηY.inv ≫ ((HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom) := by
      -- Proof comment: precompose by the inverse source comparison to isolate the chain-level
      -- homology map.
      simpa [Category.assoc] using
        congrArg (fun k ↦ ηY.inv ≫ k) hnat.symm
    simpa [Category.assoc] using hpre
  have hf :
      f = eY.inv ≫ DerivedCategory.Q.map β ≫ eQL.hom := by
    -- Proof comment: rewrite the represented roof back to the actual target morphism `f`.
    simpa [eQL, Category.assoc] using
      (congrArg (fun k ↦ eY.inv ≫ k ≫ eQL.hom) hβ).symm
  have hstep :
      ηY.inv ≫ (HT i).map (DerivedCategory.Q.map β) ≫ ηL.hom =
        eSrc.inv ≫ (HT i).map f ≫ eL.hom := by
    -- Proof comment: after replacing `Q.map β` by `f`, the remaining terms are exactly the
    -- source and target comparison isomorphisms in the statement.
    rw [hf]
    simp [HT, eSrc, eL, eQL, ηY, ηL, Functor.map_comp, Category.assoc]
  -- Proof comment: substitute the represented morphism `f` into the conjugated homology formula.
  exact hconj.trans hstep

/-- Helper for Lemma 15.77.2: under restriction of scalars, the homology map of a short-complex
morphism rewrites into the forward `mapHomologyIso` form used by the transport square. -/
private theorem shortComplexFunctor_homologyMap_eq
    {T : Type u} [CommRing T]
    {Y Z : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor (ModuleCat T) (up ℤ) i).map β) =
      HomologicalComplex.homologyMap β i := by
  -- Proof comment: the degree-`i` short-complex model computes the ordinary homology map by
  -- definition.
  rfl

/-- Helper for Lemma 15.77.2: restriction of scalars commutes definitionally with the degree-`i`
short-complex functor on cochain complexes. -/
private theorem restrict_scalars_shortComplexFunctor_map_eq
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {Y Z : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    (((ModuleCat.restrictScalars (algebraMap S T)).mapShortComplex).map
        ((HomologicalComplex.shortComplexFunctor (ModuleCat T) (up ℤ) i).map β)) =
      ((HomologicalComplex.shortComplexFunctor (ModuleCat S) (up ℤ) i).map
        (((ModuleCat.restrictScalars (algebraMap S T)).mapHomologicalComplex (up ℤ)).map β)) := by
  -- Proof comment: both sides are literally the same short-complex morphism after unfolding the
  -- functorial definitions.
  rfl

/-- Helper for Lemma 15.77.2: under restriction of scalars, the homology map of a short-complex
morphism rewrites into the forward `mapHomologyIso` form used by the transport square. -/
private theorem restrict_scalars_mapHomologyIso_hom_formula
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {S₁ S₂ : ShortComplex (ModuleCat T)}
    (φ : S₁ ⟶ S₂) :
    (ModuleCat.restrictScalars (algebraMap S T)).map (ShortComplex.homologyMap φ) =
      (S₁.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).inv ≫
        ShortComplex.homologyMap
          (((ModuleCat.restrictScalars (algebraMap S T)).mapShortComplex).map φ) ≫
        (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom := by
  calc
    (ModuleCat.restrictScalars (algebraMap S T)).map (ShortComplex.homologyMap φ) =
        (ModuleCat.restrictScalars (algebraMap S T)).map (ShortComplex.homologyMap φ) ≫
          (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).inv ≫
            (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom := by
      simp
    _ =
        (S₁.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).inv ≫
          ShortComplex.homologyMap
            (((ModuleCat.restrictScalars (algebraMap S T)).mapShortComplex).map φ) ≫
          (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom := by
      -- Proof comment: postcompose the inverse-form naturality square by the target comparison
      -- isomorphism to obtain the forward transport formula.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (S₂.mapHomologyIso (ModuleCat.restrictScalars (algebraMap S T))).hom)
          (ShortComplex.mapHomologyIso_inv_naturality
            (F := ModuleCat.restrictScalars (algebraMap S T)) (φ := φ))

/-- Helper for Lemma 15.77.2: after restricting scalars, the source `mapHomologyIso` comparison
cancels and leaves the cochain-level homology transport in the forward orientation. -/
private theorem restrict_scalars_mapHomologyIso_source_cancel
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {Y Z : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ Z) (i : ℤ) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    ((Y.sc i).mapHomologyIso res).hom ≫
        res.map (HomologicalComplex.homologyMap β i) =
      HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
        ((Z.sc i).mapHomologyIso res).hom := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  have hformula :
      res.map (HomologicalComplex.homologyMap β i) =
        ((Y.sc i).mapHomologyIso res).inv ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((Z.sc i).mapHomologyIso res).hom := by
    -- Proof comment: rewrite the short-complex comparison into the cochain-level homology map
    -- attached to the degree-`i` short complex of `β`.
    simpa [shortComplexFunctor_homologyMap_eq, restrict_scalars_shortComplexFunctor_map_eq] using
      (restrict_scalars_mapHomologyIso_hom_formula
        (S := S) (T := T)
        (S₁ := Y.sc i) (S₂ := Z.sc i)
        ((HomologicalComplex.shortComplexFunctor (ModuleCat T) (up ℤ) i).map β))
  change ((Y.sc i).mapHomologyIso res).hom ≫
      res.map (HomologicalComplex.homologyMap β i) =
    HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
      ((Z.sc i).mapHomologyIso res).hom
  have hpre :
      ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) =
        ((Y.sc i).mapHomologyIso res).hom ≫
          (((Y.sc i).mapHomologyIso res).inv ≫
            HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
              ((Z.sc i).mapHomologyIso res).hom) :=
    congrArg (fun k ↦ ((Y.sc i).mapHomologyIso res).hom ≫ k) hformula
  -- Proof comment: the source comparison cancels against its inverse, leaving the forward
  -- cochain-level homology transport.
  simpa [Category.assoc] using hpre

/-- Helper for Lemma 15.77.2: after restricting scalars, the homology transport for an arbitrary
representative roof is controlled by the forward `mapHomologyIso` formula. -/
private theorem restrict_scalars_q_representative_homology_transport
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (β : Y ⟶ DerivedCategory.Q.objPreimage L) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let L' := DerivedCategory.Q.objPreimage L
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom =
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        res.map (HomologicalComplex.homologyMap β i) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let HS := DerivedCategory.homologyFunctor (ModuleCat S)
  let L' := DerivedCategory.Q.objPreimage L
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  have hnat :
      (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i := by
    -- Proof comment: naturality of `homologyFunctorFactors` computes the derived homology map of
    -- the restricted representative roof.
    simpa [FY, FL] using
      (DerivedCategory.homologyFunctorFactors_hom_naturality
        (C := ModuleCat S)
        ((res.mapHomologicalComplex (up ℤ)).map β) i)
  have hmap :
      ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) =
        HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
          ((L'.sc i).mapHomologyIso res).hom :=
    restrict_scalars_mapHomologyIso_source_cancel
      (S := S) (T := T) (β := β) (i := i)
  have hnat' :
      (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom := by
    -- Proof comment: postcompose the derived naturality square by the target `mapHomologyIso`.
    simpa [Category.assoc] using
      congrArg (fun k ↦ k ≫ ((L'.sc i).mapHomologyIso res).hom) hnat
  have hmap' :
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          HomologicalComplex.homologyMap ((res.mapHomologicalComplex (up ℤ)).map β) i ≫
            ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
            res.map (HomologicalComplex.homologyMap β i) := by
    -- Proof comment: precompose the forward `mapHomologyIso` transport by the source comparison
    -- on the restricted representative.
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫ k)
        hmap.symm
  -- Proof comment: splice the derived naturality square with the forward `mapHomologyIso`
  -- transport for the representative roof.
  exact hnat'.trans hmap'

/-- Helper for Lemma 15.77.2: surjectivity is preserved by conjugating a module map with source
and target isomorphisms. -/
private theorem Function.Surjective.of_iso_conjugate
    {M M' N N' : ModuleCat R}
    (eM : M ≅ M') (eN : N ≅ N')
    {f : M' ⟶ N'} (hf : Function.Surjective f.hom) :
    Function.Surjective ((eM.inv ≫ f ≫ eN.hom).hom) := by
  intro y
  rcases hf (eN.inv y) with ⟨x, hx⟩
  refine ⟨eM.hom x, ?_⟩
  -- Proof comment: choose a preimage after transporting `y` back along the target isomorphism,
  -- then return it to the original source object.
  change eN.hom (f (eM.inv (eM.hom x))) = y
  simpa using congrArg (fun z ↦ eN.hom z) hx

/-- Helper for Lemma 15.77.2: restricting scalars along `R → κ(𝔭)` commutes with taking derived
homology. -/
private noncomputable def restrict_scalars_homology_iso
    (L : DerivedCategory (ModuleCat κ)) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) n).obj
        (((ModuleCat.restrictScalars (algebraMap R κ)).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars (algebraMap R κ)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat κ) n).obj L) :=
  let K := DerivedCategory.Q.objPreimage L
  let FK :=
    ((ModuleCat.restrictScalars (algebraMap R κ)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
  let eκ :
      ((DerivedCategory.homologyFunctor (ModuleCat κ) n).obj L) ≅
        K.homology n :=
    ((DerivedCategory.homologyFunctor (ModuleCat κ) n).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat κ) n).app K
  -- Proof comment: move to a chosen complex representative of `L`, compute homology before and
  -- after restriction of scalars there, and then transport back to the derived category.
  (DerivedCategory.homologyFunctor (ModuleCat R) n).mapIso
      (((((ModuleCat.restrictScalars (algebraMap R κ)).mapDerivedCategory).mapIso
          (DerivedCategory.Q.objObjPreimageIso L)).symm) ≪≫
        ((ModuleCat.restrictScalars (algebraMap R κ)).mapDerivedCategoryFactors.app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app FK ≪≫
    (K.sc n).mapHomologyIso (ModuleCat.restrictScalars (algebraMap R κ)) ≪≫
      (ModuleCat.restrictScalars (algebraMap R κ)).mapIso eκ.symm

/-- Helper for Lemma 15.77.2: after applying the scalar-extension/restriction adjunction, the
canonical homology comparison unfolds to the derived adjunction unit followed by the
restriction-of-scalars homology transport. -/
private theorem derived_tensor_homology_comparison_adjoint_eq
    (K : DMod) (i : ℤ) :
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap R κ)).homEquiv _ _)
        (derivedTensorWithAlgebraHomologyComparison κ K i) =
      (DerivedCategory.homologyFunctor (ModuleCat R) i).map
          ((derivedTensorWithAlgebraAdjunction (R := R) (A := κ)).unit.app K) ≫
        (restrict_scalars_homology_iso (𝔭 := 𝔭)
          ((derivedTensorWithAlgebra (algebraMap R κ)).obj K) i).hom := by
  -- Proof comment: unfold the owner comparison once; the adjoint-side description is
  -- definitionally the unit-on-homology composite used below.
  rw [derivedTensorWithAlgebraHomologyComparison]
  simp only [Equiv.apply_symm_apply]
  rfl

/-- Helper for Lemma 15.77.2: postcomposing the homology image of the derived adjunction-unit
naturality square gives the exact source-side equality needed for the comparison transport. -/
private theorem derived_adjunction_unit_homology_naturality_postcompose
    (i : ℤ)
    {K L : DMod}
    (f : K ⟶ L)
    (g :
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          (((ModuleCat.restrictScalars (algebraMap R κ)).mapDerivedCategory).obj
            ((derivedTensorWithAlgebra (algebraMap R κ)).obj L)) ⟶
        (ModuleCat.restrictScalars (algebraMap R κ)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
            ((derivedTensorWithAlgebra (algebraMap R κ)).obj L))) :
    let HR := DerivedCategory.homologyFunctor (ModuleCat R) i
    let η := (derivedTensorWithAlgebraAdjunction (R := R) (A := κ)).unit
    HR.map f ≫ HR.map (η.app L) ≫ g =
      HR.map (η.app K) ≫
        HR.map
          (((ModuleCat.restrictScalars (algebraMap R κ)).mapDerivedCategory).map
            ((derivedTensorWithAlgebra (algebraMap R κ)).map f)) ≫
          g := by
  let HR := DerivedCategory.homologyFunctor (ModuleCat R) i
  let η := (derivedTensorWithAlgebraAdjunction (R := R) (A := κ)).unit
  have hη :
      HR.map f ≫ HR.map (η.app L) =
        HR.map (η.app K) ≫
          HR.map
            (((ModuleCat.restrictScalars (algebraMap R κ)).mapDerivedCategory).map
              ((derivedTensorWithAlgebra (algebraMap R κ)).map f)) := by
    -- Proof comment: naturality of the adjunction unit moves `f` across the derived tensor unit.
    simpa [HR, Functor.map_comp] using congrArg (fun h ↦ HR.map h) (η.naturality f)
  -- Proof comment: postcompose the unit square by the later restriction-of-scalars comparison.
  simpa [HR, η, Category.assoc] using congrArg (fun h ↦ h ≫ g) hη

/-- Helper for Lemma 15.77.2: the restriction-of-scalars transport square is equally valid for an
arbitrary source representative `Y` of a derived morphism. -/
private theorem restrict_scalars_q_representative_transport_bridge
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    {K L : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (f : K ⟶ L)
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let L' := DerivedCategory.Q.objPreimage L
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let L' := DerivedCategory.Q.objPreimage L
  let eL : DerivedCategory.Q.obj L' ≅ L := DerivedCategory.Q.objObjPreimageIso L
  have hf :
      f = eY.inv ≫ DerivedCategory.Q.map β ≫ eL.hom := by
    -- Proof comment: rewrite the derived morphism `f` through the chosen representative roof
    -- `β` before applying `mapDerivedCategoryFactors`.
    simpa [eL, Category.assoc] using
      (congrArg (fun k ↦ eY.inv ≫ k ≫ eL.hom) hβ).symm
  -- Proof comment: after conjugating `f` by the source and target `Q`-model isomorphisms, the
  -- remaining statement is exactly the naturality square for `mapDerivedCategoryFactors`.
  calc
    res.mapDerivedCategory.map f ≫
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          (res.mapDerivedCategoryFactors.app L')).hom) =
      (((res.mapDerivedCategory).mapIso eY).symm).hom ≫
        (res.mapDerivedCategory.map (DerivedCategory.Q.map β) ≫
          (res.mapDerivedCategoryFactors.app L').hom) := by
        rw [hf]
        simp [res, L', eL, Functor.map_comp, Category.assoc]
    _ =
      (((res.mapDerivedCategory).mapIso eY).symm).hom ≫
        ((res.mapDerivedCategoryFactors.app Y).hom ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (((res.mapDerivedCategory).mapIso eY).symm).hom ≫ k)
            (res.mapDerivedCategoryFactors.hom.naturality β)
    _ =
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)).hom) ≫
        DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) := by
        simp [res, Category.assoc]

/-- Helper for Lemma 15.77.2: every morphism into a derived object can be represented by a roof
whose target is the chosen `Q.objPreimage` model of that object. -/
private theorem exists_quasi_iso_fraction_to_preimage
    {T : Type u}
    [CommRing T]
    {K₀ : CochainComplex (ModuleCat T) ℤ}
    {L : DerivedCategory (ModuleCat T)}
    (α : DerivedCategory.Q.obj K₀ ⟶ L) :
    ∃ (Y : CochainComplex (ModuleCat T) ℤ) (σ : Y ⟶ K₀) (_ : QuasiIso σ)
      (β : Y ⟶ DerivedCategory.Q.objPreimage L),
      DerivedCategory.Q.map σ ≫ α =
        DerivedCategory.Q.map β ≫ (DerivedCategory.Q.objObjPreimageIso L).hom := by
  let γ :
      DerivedCategory.Q.obj K₀ ⟶
        DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage L) :=
    α ≫ (DerivedCategory.Q.objObjPreimageIso L).inv
  obtain ⟨Y, σ, hσ, β, hγ⟩ := DerivedCategory.right_fac γ
  refine ⟨Y, σ, ?_, β, ?_⟩
  · -- Proof comment: `right_fac` returns a denominator whose image under `Q` is invertible, which
    -- is exactly the quasi-isomorphism condition on `σ`.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hσ
    exact hσ
  -- Proof comment: cancel the target preimage isomorphism introduced in the transported
  -- right-fraction factorization.
  calc
    DerivedCategory.Q.map σ ≫ α =
        DerivedCategory.Q.map σ ≫
          (α ≫ (DerivedCategory.Q.objObjPreimageIso L).inv) ≫
            (DerivedCategory.Q.objObjPreimageIso L).hom := by
          simp [Category.assoc]
    _ = DerivedCategory.Q.map σ ≫ γ ≫
          (DerivedCategory.Q.objObjPreimageIso L).hom := by
          rfl
    _ = DerivedCategory.Q.map σ ≫
          (inv (DerivedCategory.Q.map σ) ≫ DerivedCategory.Q.map β) ≫
            (DerivedCategory.Q.objObjPreimageIso L).hom := by
          rw [hγ]
    _ = DerivedCategory.Q.map β ≫
          (DerivedCategory.Q.objObjPreimageIso L).hom := by
          simp [Category.assoc]

/-- Helper for Lemma 15.77.2: once the source morphism is represented by a roof, the
restriction-of-scalars homology square becomes fully explicit. -/
private theorem restrict_scalars_homology_iso_naturality_of_representative
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L)
    {Y : CochainComplex (ModuleCat T) ℤ}
    (eY : DerivedCategory.Q.obj Y ≅ K)
    (β : Y ⟶ DerivedCategory.Q.objPreimage L)
    (hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫
          (DerivedCategory.Q.objObjPreimageIso L).inv) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let L' := DerivedCategory.Q.objPreimage L
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    let eSrc : (HT i).obj K ≅ Y.homology i :=
      ((HT i).mapIso eY).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
    let eL : (HT i).obj L ≅ L'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
    (HS i).map (res.mapDerivedCategory.map f) ≫
        ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eL.symm).hom =
      ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eSrc.symm).hom ≫
        res.map ((HT i).map f) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let HS := DerivedCategory.homologyFunctor (ModuleCat S)
  let HT := DerivedCategory.homologyFunctor (ModuleCat T)
  let L' := DerivedCategory.Q.objPreimage L
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  let eSrc : (HT i).obj K ≅ Y.homology i :=
    ((HT i).mapIso eY).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let eL : (HT i).obj L ≅ L'.homology i :=
    ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  have hbridge :
      res.mapDerivedCategory.map f ≫
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')).hom) =
        ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)).hom) ≫
          DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β) :=
    restrict_scalars_q_representative_transport_bridge
      (S := S) (T := T) (f := f) (eY := eY) (β := β) hβ
  have hbridge_homology :
      (HS i).map (res.mapDerivedCategory.map f) ≫
          ((HS i).mapIso
            ((((res.mapDerivedCategory).mapIso
                (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
              (res.mapDerivedCategoryFactors.app L')))).hom =
        ((HS i).mapIso
            ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
              (res.mapDerivedCategoryFactors.app Y)))).hom ≫
          (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) := by
    -- Proof comment: applying degree-`i` homology to the transport bridge exposes the chosen
    -- representative roof on the restricted derived side.
    simpa [Functor.map_comp, Functor.mapIso_hom, Category.assoc] using
      congrArg (fun k ↦ (HS i).map k) hbridge
  have htransport :
      (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom =
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) :=
    restrict_scalars_q_representative_homology_transport
      (S := S) (T := T) (i := i) (K := K) (L := L) (β := β)
  have hβ_homology :
      res.map (HomologicalComplex.homologyMap β i) ≫ (res.mapIso eL.symm).hom =
        (res.mapIso eSrc.symm).hom ≫ res.map ((HT i).map f) := by
    -- Proof comment: rewrite the representative cochain-level homology map by the conjugated
    -- derived homology map of `f`.
    have hconj :
        HomologicalComplex.homologyMap β i =
          eSrc.inv ≫ (HT i).map f ≫ eL.hom :=
      q_representative_homologyMap_conjugated
        (T := T) (i := i) (f := f) (eY := eY) (β := β) hβ
    rw [hconj]
    simp [Functor.map_comp, Category.assoc]
  let sourceComparison :
      (HS i).obj (res.mapDerivedCategory.obj K) ⟶
        (HS i).obj (DerivedCategory.Q.obj ((res.mapHomologicalComplex (up ℤ)).obj Y)) :=
    ((HS i).mapIso
      ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
        (res.mapDerivedCategoryFactors.app Y)))).hom
  have hstep₁ :
      (HS i).map (res.mapDerivedCategory.map f) ≫
          ((HS i).mapIso
            ((((res.mapDerivedCategory).mapIso
                (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
              (res.mapDerivedCategoryFactors.app L')))).hom ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom := by
    -- Proof comment: append the remaining tail to the homology image of the derived-side bridge.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ k ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom)
        hbridge_homology
  have hstep₂ :
      sourceComparison ≫
          (HS i).map (DerivedCategory.Q.map ((res.mapHomologicalComplex (up ℤ)).map β)) ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
          ((L'.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) ≫
          (res.mapIso eL.symm).hom := by
    -- Proof comment: replace the transported chain-level homology map by the forward
    -- representative transport on the restricted complex.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ sourceComparison ≫ k ≫ (res.mapIso eL.symm).hom)
        htransport
  have hstep₃ :
      sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          res.map (HomologicalComplex.homologyMap β i) ≫
          (res.mapIso eL.symm).hom =
        sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫
          (res.mapIso eSrc.symm).hom ≫
          res.map ((HT i).map f) := by
    -- Proof comment: replace the representative homology map by the derived homology map of `f`.
    simpa [sourceComparison, Category.assoc] using
      congrArg
        (fun k ↦ sourceComparison ≫
          ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
          ((Y.sc i).mapHomologyIso res).hom ≫ k)
        hβ_homology
  -- Proof comment: expose the chosen representative roof on the restricted derived side and then
  -- replace its chain-level homology map by the conjugated derived homology map of `f`.
  exact hstep₁.trans (hstep₂.trans hstep₃)

/-- Helper for Lemma 15.77.2: specializing the representative naturality theorem to an identity
target removes the denominator transport. -/
private theorem restrict_scalars_homology_iso_denominator_cancel
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K : DerivedCategory (ModuleCat T)}
    {Y : CochainComplex (ModuleCat T) ℤ}
    (σ : Y ⟶ DerivedCategory.Q.objPreimage K)
    [QuasiIso σ] :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let K' := DerivedCategory.Q.objPreimage K
    let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
    let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
    let eY : DerivedCategory.Q.obj Y ≅ K :=
      (asIso (DerivedCategory.Q.map σ)) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    let eSrc : (HT i).obj K ≅ Y.homology i :=
      ((HT i).mapIso eY).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
    let eK : (HT i).obj K ≅ K'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
    ((HS i).mapIso
        ((((res.mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
          (res.mapDerivedCategoryFactors.app K')))).hom ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK).hom ≫
      ((K'.sc i).mapHomologyIso res).hom ≫
      (res.mapIso eK.symm).hom =
    ((HS i).mapIso
        ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
          (res.mapDerivedCategoryFactors.app Y)))).hom ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
      ((Y.sc i).mapHomologyIso res).hom ≫
      (res.mapIso eSrc.symm).hom := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let K' := DerivedCategory.Q.objPreimage K
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
  letI : IsIso (DerivedCategory.Q.map σ) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let eY : DerivedCategory.Q.obj Y ≅ K :=
    (asIso (DerivedCategory.Q.map σ)) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  let eSrc :
      ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj K) ≅
        Y.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso eY).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y
  let eK :
      ((DerivedCategory.homologyFunctor (ModuleCat T) i).obj K) ≅
        K'.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat T) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
  have hσ :
      DerivedCategory.Q.map σ =
        eY.hom ≫ (𝟙 K) ≫ (DerivedCategory.Q.objObjPreimageIso K).inv := by
    -- Proof comment: the chosen denominator roof represents the identity of `K` after
    -- conjugating by the standard `Q.objPreimage` isomorphism.
    simp [eY, Category.assoc]
  have hcancel :=
    restrict_scalars_homology_iso_naturality_of_representative
      (S := S) (T := T) (i := i)
      (K := K) (L := K) (f := 𝟙 K)
      (eY := eY) (β := σ) hσ
  -- Proof comment: specializing the representative naturality square to the identity morphism
  -- removes the denominator and recovers the canonical source-side comparison.
  simpa [res, K', FY, FK, eY, eSrc, eK, Functor.mapIso_hom, Iso.trans_hom,
    Functor.map_comp, Category.assoc] using hcancel

/-- Helper for Lemma 15.77.2: the restriction-of-scalars homology comparison is natural in the
derived source morphism. -/
private theorem restrict_scalars_homology_iso_naturality_expanded
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L) :
    let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
    let HS := DerivedCategory.homologyFunctor (ModuleCat S)
    let HT := DerivedCategory.homologyFunctor (ModuleCat T)
    let K' := DerivedCategory.Q.objPreimage K
    let L' := DerivedCategory.Q.objPreimage L
    let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
    let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
    let eK : (HT i).obj K ≅ K'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
    let eL : (HT i).obj L ≅ L'.homology i :=
      ((HT i).mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
    (HS i).map (res.mapDerivedCategory.map f) ≫
        ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
            (res.mapDerivedCategoryFactors.app L')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FL).hom ≫
        ((L'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eL.symm).hom =
      ((HS i).mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
            (res.mapDerivedCategoryFactors.app K')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK).hom ≫
        ((K'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eK.symm).hom ≫
        res.map ((HT i).map f) := by
  let res : ModuleCat T ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S T)
  let HS := DerivedCategory.homologyFunctor (ModuleCat S) i
  let HT := DerivedCategory.homologyFunctor (ModuleCat T) i
  let K' := DerivedCategory.Q.objPreimage K
  let L' := DerivedCategory.Q.objPreimage L
  let FK := (res.mapHomologicalComplex (up ℤ)).obj K'
  let FL := (res.mapHomologicalComplex (up ℤ)).obj L'
  let eK : HT.obj K ≅ K'.homology i :=
    (HT.mapIso (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app K'
  let eL : HT.obj L ≅ L'.homology i :=
    (HT.mapIso (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app L'
  obtain ⟨Y, σ, hσ, β, hβfac⟩ :=
    exists_quasi_iso_fraction_to_preimage
      (T := T) (K₀ := K') (L := L)
      ((DerivedCategory.Q.objObjPreimageIso K).hom ≫ f)
  let FY := (res.mapHomologicalComplex (up ℤ)).obj Y
  letI : QuasiIso σ := hσ
  letI : IsIso (DerivedCategory.Q.map σ) := by
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso]
    infer_instance
  let eY : DerivedCategory.Q.obj Y ≅ K :=
    (asIso (DerivedCategory.Q.map σ)) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have hβ :
      DerivedCategory.Q.map β =
        eY.hom ≫ f ≫ (DerivedCategory.Q.objObjPreimageIso L).inv := by
    have hβ' :
        DerivedCategory.Q.map σ ≫
            ((DerivedCategory.Q.objObjPreimageIso K).hom ≫ f) ≫
            (DerivedCategory.Q.objObjPreimageIso L).inv =
          DerivedCategory.Q.map β := by
      -- Proof comment: postcompose the chosen right-fraction equality by the inverse target
      -- preimage isomorphism to isolate the numerator roof.
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ k ≫ (DerivedCategory.Q.objObjPreimageIso L).inv)
          hβfac
    calc
      DerivedCategory.Q.map β =
          DerivedCategory.Q.map σ ≫
              ((DerivedCategory.Q.objObjPreimageIso K).hom ≫ f) ≫
                (DerivedCategory.Q.objObjPreimageIso L).inv := hβ'.symm
      _ = eY.hom ≫ f ≫ (DerivedCategory.Q.objObjPreimageIso L).inv := by
        simp [eY, Category.assoc]
  have hrep :=
    restrict_scalars_homology_iso_naturality_of_representative
      (S := S) (T := T) (i := i)
      (K := K) (L := L) (f := f)
      (eY := eY) (β := β) hβ
  have hcancel :=
    restrict_scalars_homology_iso_denominator_cancel
      (S := S) (T := T) (i := i)
      (K := K) (σ := σ)
  have hcancel_post :
      (HS.mapIso
          ((((res.mapDerivedCategory).mapIso eY).symm ≪≫
            (res.mapDerivedCategoryFactors.app Y)))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FY).hom ≫
        ((Y.sc i).mapHomologyIso res).hom ≫
        (res.mapIso
          (((HT.mapIso eY).symm ≪≫
            (DerivedCategory.homologyFunctorFactors (ModuleCat T) i).app Y).symm)).hom ≫
        res.map (HT.map f) =
      (HS.mapIso
          ((((res.mapDerivedCategory).mapIso
              (DerivedCategory.Q.objObjPreimageIso K)).symm ≪≫
            (res.mapDerivedCategoryFactors.app K')))).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat S) i).app FK).hom ≫
        ((K'.sc i).mapHomologyIso res).hom ≫
        (res.mapIso eK.symm).hom ≫
        res.map (HT.map f) := by
    -- Proof comment: cancel the denominator roof once and then postcompose by the actual degree
    -- `i` derived homology map of `f`.
    simpa [res, HS, HT, K', FY, FK, eY, eK, Functor.mapIso_hom, Iso.trans_hom,
      Functor.map_comp, Category.assoc] using
      congrArg (fun k ↦ k ≫ res.map (HT.map f)) hcancel.symm
  -- Proof comment: represent `f` by a right fraction into `Q.objPreimage L`, then splice the
  -- numerator roof with the identity-case denominator cancellation on `K`.
  exact hrep.trans hcancel_post

/-- Helper for Lemma 15.77.2: restricting scalars commutes naturally with taking derived
homology. -/
private theorem restrict_scalars_homology_iso_naturality
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat T)}
    (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor (ModuleCat S) i).map
        (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).map f) ≫
        (restrict_scalars_homology_iso (𝔭 := 𝔭) L i).hom =
        (restrict_scalars_homology_iso (𝔭 := 𝔭) K i).hom ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            ((DerivedCategory.homologyFunctor (ModuleCat T) i).map f) := by
  -- Proof comment: the condensed public-looking naturality square is exactly the expanded roof
  -- calculation above with the intermediate transports folded back into `restrict_scalars_homology_iso`.
  simpa [restrict_scalars_homology_iso, Category.assoc, Iso.trans_hom, Functor.mapIso_hom] using
    (restrict_scalars_homology_iso_naturality_expanded
      (S := S) (T := T) (i := i) (f := f))

/-- Helper for Lemma 15.77.2: the owner homology comparison is natural in the source derived
object. -/
private theorem derived_tensor_homology_comparison_naturality
    {S T : Type u} [CommRing S] [CommRing T] [Algebra S T]
    (i : ℤ)
    {K L : DerivedCategory (ModuleCat S)}
    (f : K ⟶ L) :
    (ModuleCat.extendScalars (algebraMap S T)).map
        ((DerivedCategory.homologyFunctor (ModuleCat S) i).map f) ≫
      derivedTensorWithAlgebraHomologyComparison T L i =
        derivedTensorWithAlgebraHomologyComparison T K i ≫
          (DerivedCategory.homologyFunctor (ModuleCat T) i).map
            ((derivedTensorWithAlgebra (algebraMap S T)).map f) := by
  let HS := DerivedCategory.homologyFunctor (ModuleCat S) i
  let η := (derivedTensorWithAlgebraAdjunction (R := S) (A := T)).unit
  -- Proof comment: after passing to the scalar-extension/restriction adjunction, only the
  -- restriction-of-scalars homology naturality square remains.
  refine ((ModuleCat.extendRestrictScalarsAdj (algebraMap S T)).homEquiv _ _).injective ?_
  rw [CategoryTheory.Adjunction.homEquiv_naturality_left]
  rw [CategoryTheory.Adjunction.homEquiv_naturality_right]
  rw [derived_tensor_homology_comparison_adjoint_eq (𝔭 := 𝔭) (K := L) (i := i)]
  rw [derived_tensor_homology_comparison_adjoint_eq (𝔭 := 𝔭) (K := K) (i := i)]
  calc
    HS.map f ≫ HS.map (η.app L) ≫
        (restrict_scalars_homology_iso (𝔭 := 𝔭)
          ((derivedTensorWithAlgebra (algebraMap S T)).obj L) i).hom =
      HS.map (η.app K) ≫
          HS.map
            (((ModuleCat.restrictScalars (algebraMap S T)).mapDerivedCategory).map
              ((derivedTensorWithAlgebra (algebraMap S T)).map f)) ≫
        (restrict_scalars_homology_iso (𝔭 := 𝔭)
          ((derivedTensorWithAlgebra (algebraMap S T)).obj L) i).hom := by
        simpa using
          (derived_adjunction_unit_homology_naturality_postcompose
            (𝔭 := 𝔭) (i := i) (f := f)
            (g := (restrict_scalars_homology_iso (𝔭 := 𝔭)
              ((derivedTensorWithAlgebra (algebraMap S T)).obj L) i).hom))
    _ = HS.map (η.app K) ≫
          ((restrict_scalars_homology_iso (𝔭 := 𝔭)
              ((derivedTensorWithAlgebra (algebraMap S T)).obj K) i).hom ≫
            (ModuleCat.restrictScalars (algebraMap S T)).map
              ((DerivedCategory.homologyFunctor (ModuleCat T) i).map
                ((derivedTensorWithAlgebra (algebraMap S T)).map f))) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ HS.map (η.app K) ≫ k)
            (restrict_scalars_homology_iso_naturality
              (𝔭 := 𝔭) (S := S) (T := T) (i := i)
              (f := (derivedTensorWithAlgebra (algebraMap S T)).map f))
    _ = HS.map (η.app K) ≫
          (restrict_scalars_homology_iso (𝔭 := 𝔭)
            ((derivedTensorWithAlgebra (algebraMap S T)).obj K) i).hom ≫
          (ModuleCat.restrictScalars (algebraMap S T)).map
            ((DerivedCategory.homologyFunctor (ModuleCat T) i).map
              ((derivedTensorWithAlgebra (algebraMap S T)).map f)) := by
        simp

/-- Helper for Lemma 15.77.2: the source-side transport from residue-field homology of `K` to the
ordinary degree-`i` homology of the chosen bounded-above finite-projective model. -/
private noncomputable def comparison_transport_source_iso
    (K : DMod) (i : ℤ)
    (P : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R))
    (eK : K ≅ DerivedCategory.Q.obj (P : Cpx))
    (hPsourceHomology :
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (DerivedCategory.Q.obj (P : Cpx)) ≅
        (P : Cpx).homology i) :
    (ModuleCat.extendScalars (algebraMap R κ)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj K) ≅
      (ModuleCat.extendScalars (algebraMap R κ)).obj ((P : Cpx).homology i) :=
  (ModuleCat.extendScalars (algebraMap R κ)).mapIso
    (((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eK) ≪≫ hPsourceHomology)

/-- Helper for Lemma 15.77.2: the target transport from the residue-field homology of `K` to the
ordinary degree-`i` homology of the scalar-extended bounded-above finite-projective model. -/
private noncomputable def comparison_transport_target_iso
    (K : DMod) (i : ℤ)
    (P : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R))
    (eK : K ≅ DerivedCategory.Q.obj (P : Cpx))
    (hPbaseChange :
      ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : Cpx)))
    (hPtargetHomology :
      (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
          ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (P : Cpx)).homology i) :
    (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj (K ⊗[R]^L[κ]) ≅
      (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (P : Cpx)).homology i :=
  ((DerivedCategory.homologyFunctor (ModuleCat κ) i).mapIso
      (((derivedTensorWithAlgebra (algebraMap R κ)).mapIso eK) ≪≫ hPbaseChange)) ≪≫
    hPtargetHomology

/-- Helper for Lemma 15.77.2: transporting source and target homology through the chosen
bounded-above finite-projective model turns surjectivity of the residue-field comparison on `K`
into surjectivity of the corresponding model-side comparison morphism. -/
private theorem surjective_transported_comparison_on_finite_projective_model
    (K : DMod) (i : ℤ)
    (P : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R))
    (eK : K ≅ DerivedCategory.Q.obj (P : Cpx))
    (hPbaseChange :
      ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : Cpx)))
    (hPsourceHomology :
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (DerivedCategory.Q.obj (P : Cpx)) ≅
        (P : Cpx).homology i)
    (hPtargetHomology :
      (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
          ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (P : Cpx)).homology i)
    (hsurj : Epi (derivedTensorWithAlgebraHomologyComparison κ K i)) :
    Function.Surjective
      (((comparison_transport_source_iso
            (𝔭 := 𝔭) K i P eK hPsourceHomology).inv ≫
          derivedTensorWithAlgebraHomologyComparison κ K i) ≫
            (comparison_transport_target_iso
              (𝔭 := 𝔭) K i P eK hPbaseChange hPtargetHomology).hom).hom := by
  let eSource :=
    comparison_transport_source_iso (𝔭 := 𝔭) K i P eK hPsourceHomology
  let eTarget :=
    comparison_transport_target_iso (𝔭 := 𝔭) K i P eK hPbaseChange hPtargetHomology
  have hsurj_comp :
      Function.Surjective (derivedTensorWithAlgebraHomologyComparison κ K i).hom := by
    -- Proof comment: in `ModuleCat`, epi is exactly surjectivity of the underlying linear map.
    exact (ModuleCat.epi_iff_surjective _).1 hsurj
  -- Proof comment: surjectivity survives conjugation by the source and target homology
  -- transports attached to the chosen model.
  exact Function.Surjective.of_iso_conjugate eSource eTarget hsurj_comp

/-- Helper for Lemma 15.77.2: once the transported degree-`i` residue-field comparison on a
bounded-above finite-projective model is surjective, the source proof's degree-window
localization argument produces the full upper-truncation package after shrinking away from `𝔭`. -/
private theorem exists_localizationAway_upper_truncation_package_of_model_mapHomology_surjective
    (K : DMod) (i : ℤ)
    (P : CochainComplex.MinusWithTermsIn (finiteProjectiveModuleProperty R))
    (b : ℤ) (eK : K ≅ DerivedCategory.Q.obj (P : Cpx))
    (hPle : (P : Cpx).IsStrictlyLE b)
    (hPfinite : ∀ n : ℤ, Module.Finite R ((P : Cpx).X n))
    (hPprojective : ∀ n : ℤ, Module.Projective R ((P : Cpx).X n))
    (hPbaseChange :
      ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : Cpx)))
    (hPsourceHomology :
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (DerivedCategory.Q.obj (P : Cpx)) ≅
        (P : Cpx).homology i)
    (hPtargetHomology :
      (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
          ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (P : Cpx)).homology i)
    (hsurj_model :
      Function.Surjective
        (((comparison_transport_source_iso
              (𝔭 := 𝔭) K i P eK hPsourceHomology).inv ≫
            derivedTensorWithAlgebraHomologyComparison κ K i) ≫
              (comparison_transport_target_iso
                (𝔭 := 𝔭) K i P eK hPbaseChange hPtargetHomology).hom).hom) :
    ∃ f : R, ∃ c : ℤ, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          HasProjectiveAmplitudeIn
            ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
            (i + 1) c := by
  -- Proof comment: this is the source-faithful degree-window linear-algebra step. Starting from
  -- surjectivity on the scalar-extended model in degree `i`, choose the `x_a`, `y_b`, `z_c`
  -- basis data, localize via Lemma `10.79.4`, identify the localized cokernel in degree `i + 1`,
  -- and package the resulting bounded finite-projective upper tail as `t.truncGE (i + 1)`.
  let _ := b
  let _ := eK
  let _ := hPle
  let _ := hPfinite
  let _ := hPprojective
  let _ := hPbaseChange
  let _ := hPsourceHomology
  let _ := hPtargetHomology
  let _ := hsurj_model
  -- TODO for Lemma 15.77.2: from the transported comparison surjectivity above, first recover the
  -- textbook surjectivity statement on
  -- `H^i(P) ⊗_R κ(𝔭) ⟶ H^i(((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
  --   (ComplexShape.up ℤ)).obj (P : Cpx))`
  -- and then execute the degree-window argument on `P.X (i - 1) → P.X i → P.X (i + 1)`.
  -- The remaining source-faithful blocker is the explicit extraction of the `x_a`, `y_b`, `z_c`
  -- basis package from this transported homology map, followed by the localization step that
  -- identifies the localized cutoff cokernel with the degree-`i + 1` term of `t.truncGE (i + 1)`.
  sorry

/-- Helper for Lemma 15.77.2: after shrinking away from `𝔭`, the localized upper truncation
already carries the projective-amplitude, perfectness, and lower tor-amplitude package produced
by the source proof's degree-`i` linear-algebra argument. -/
private theorem exists_localizationAway_upper_truncation_package_of_residueField_homology_surjective
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj : Epi (derivedTensorWithAlgebraHomologyComparison κ K i)) :
    ∃ f : R, ∃ b : ℤ, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          HasProjectiveAmplitudeIn
            ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
            (i + 1) b := by
  -- Route correction: the remaining blocker is not the final truncation-triangle split. The
  -- source-faithful hard step is first to build, from a bounded-above finite-projective
  -- representative of `K`, one localization away from `𝔭` where the degree-`i` differential
  -- splits off a finite projective cokernel. That package is exactly what supplies the upper
  -- truncation with projective amplitude starting in degree `i + 1`, and hence the perfectness
  -- and tor-amplitude data consumed by the main theorem below.
  obtain ⟨P, b, eK, hPle, hPfinite, hPprojective⟩ :=
    bounded_above_finite_projective_model_of_isPseudoCoherent (R := R) K hK
  have hPflat : (P : Cpx).IsTermwiseFlat :=
    isTermwiseFlat_of_projective_terms (R := R) (P := (P : Cpx)) hPprojective
  have hPbaseChange :
      ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        DerivedCategory.Q.obj
          (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : Cpx)) :=
    derivedTensorWithAlgebra_obj_iso_of_termwiseFlat_of_isStrictlyLE
      (A := R) (B := κ) hPflat hPle
  have hPsourceHomology :
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (DerivedCategory.Q.obj (P : Cpx)) ≅
        (P : Cpx).homology i := by
    -- Proof comment: the chosen complex model computes the source homology directly.
    exact (DerivedCategory.homologyFunctorFactors (ModuleCat R) i).app (P : Cpx)
  have hPtargetHomology :
      (DerivedCategory.homologyFunctor (ModuleCat κ) i).obj
          ((DerivedCategory.Q.obj (P : Cpx)) ⊗[R]^L[κ]) ≅
        (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj (P : Cpx)).homology i := by
    -- Proof comment: after the bounded-above flat comparison, the target homology is computed by
    -- the scalar-extended complex itself.
    exact
      (DerivedCategory.homologyFunctor (ModuleCat κ) i).mapIso hPbaseChange ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat κ) i).app
          (((ModuleCat.extendScalars (algebraMap R κ)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (P : Cpx))
  have hsurj_model :
      Function.Surjective
        (((comparison_transport_source_iso
              (𝔭 := 𝔭) K i P eK hPsourceHomology).inv ≫
            derivedTensorWithAlgebraHomologyComparison κ K i) ≫
              (comparison_transport_target_iso
                (𝔭 := 𝔭) K i P eK hPbaseChange hPtargetHomology).hom).hom := by
    -- Proof comment: transport the original residue-field comparison surjectivity to the chosen
    -- bounded-above finite-projective model via the source and target homology isomorphisms.
    exact
      surjective_transported_comparison_on_finite_projective_model
        (𝔭 := 𝔭) (K := K) (i := i) (P := P) (eK := eK)
        (hPbaseChange := hPbaseChange) (hPsourceHomology := hPsourceHomology)
        (hPtargetHomology := hPtargetHomology) hsurj
  -- Proof comment: the remaining source-faithful step is the explicit degree-window localization
  -- argument on the finite-projective model `P`.
  exact
    exists_localizationAway_upper_truncation_package_of_model_mapHomology_surjective
      (𝔭 := 𝔭) (K := K) (i := i) (P := P) b eK hPle hPfinite hPprojective
      hPbaseChange hPsourceHomology hPtargetHomology hsurj_model

-- Proof sketch: apply the Stacks argument after replacing `K` by a bounded-above finite-free
-- representative supplied by pseudo-coherence. The surjectivity hypothesis yields a basis of the
-- middle cohomology after tensoring with `κ(𝔭)` that can be lifted to cycles. Use Algebra,
-- Lemma `10.79.4`, to localize away from some `f ∉ 𝔭` so that the degree-`i` differential splits
-- off a finite projective cokernel, which makes `τ_{\ge i + 1}` perfect with tor-amplitude in
-- `[i + 1, ∞]`. Then apply the canonical truncation triangle together with Lemma `15.77.1` to
-- obtain the unique compatible biproduct decomposition of the localized truncation triangle,
-- while keeping any auxiliary projective-amplitude bound internal to that construction.
/-- Lemma 15.77.2: let `R` be a commutative ring, let `𝔭` be a prime ideal of `R` represented by
`𝔭 : PrimeSpectrum R`, and let `K^•` be a pseudo-coherent object of `D(R)`. Assume the
canonical base-change map
`H^i(K^•) ⊗_R κ(𝔭) ⟶ H^i(K^• \otimes_R^{\mathbf L} κ(𝔭))`
is surjective in degree `i`. Then there exists `f ∈ R` with `f ∉ 𝔭` such that the upper
truncation `τ_{\ge i + 1}(K^• \otimes_R^{\mathbf L} R_f)` is perfect and has tor-amplitude in
`[i + 1, ∞]`; moreover, the localized truncation triangle admits a unique splitting compatible
with the standard truncation maps. -/
@[stacks 0A1U]
theorem exists_localizationAway_split_of_residueField_homology_surjective
    (K : DMod) (i : ℤ) (hK : K.IsPseudoCoherent)
    (hsurj : Epi (derivedTensorWithAlgebraHomologyComparison κ K i)) :
    ∃ f : R, f ∉ 𝔭.asIdeal ∧
      ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f])).IsPerfect ∧
        HasTorAmplitudeGE
          ((t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]))
          (i + 1) ∧
          ∃! e :
              K ⊗[R]^L[Localization.Away f] ≅
                (t.truncLE i).obj (K ⊗[R]^L[Localization.Away f]) ⊞
                  (t.truncGE (i + 1)).obj (K ⊗[R]^L[Localization.Away f]),
            ((t.truncLEι i).app (K ⊗[R]^L[Localization.Away f])) ≫ e.hom = biprod.inl ∧
              e.hom ≫ biprod.snd =
                ((t.truncGEπ (i + 1)).app (K ⊗[R]^L[Localization.Away f])) := by
  rcases
      exists_localizationAway_upper_truncation_package_of_residueField_homology_surjective
        (𝔭 := 𝔭) K i hK hsurj with
    ⟨f, b, hf, hPerf, hTor, hAmp⟩
  let Kf := K ⊗[R]^L[Localization.Away f]
  let T : Triangle (DerivedCategory (ModuleCat (Localization.Away f))) :=
    (t.triangleLEGE i (i + 1) rfl).obj Kf
  have hT : T ∈ distTriang (DerivedCategory (ModuleCat (Localization.Away f))) := by
    -- Proof comment: use the canonical truncation triangle on the localized object.
    simpa [T, Kf] using t.triangleLEGE_distinguished i (i + 1) rfl Kf
  have hLower :
      ∀ j : ℤ, i + 1 ≤ j → IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat (Localization.Away f)) j).obj T.obj₁) := by
    intro j hj
    -- Proof comment: the lower truncation has no cohomology in degrees strictly above `i`.
    simpa [T, Kf] using
      (DerivedCategory.isZero_of_isLE ((t.truncLE i).obj Kf) i j (by omega))
  have hSplit :
      ∃! e : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃,
        T.mor₁ ≫ e.hom = biprod.inl ∧
          e.hom ≫ biprod.snd = T.mor₂ :=
    existsUnique_biprod_iso_of_distinguishedTriangle_of_projectiveAmplitude_of_homology_vanishing_ge
      (K := T.obj₁) (L := T.obj₃) (M := T.obj₂) (a := i + 1) (b := b) hAmp hLower hT
  refine ⟨f, hf, hPerf, hTor, ?_⟩
  -- Proof comment: unfold the canonical truncation triangle so the compatibility equations match
  -- the source-facing truncation maps in the statement.
  simpa [T, Kf] using hSplit

end

end

end CategoryTheory
