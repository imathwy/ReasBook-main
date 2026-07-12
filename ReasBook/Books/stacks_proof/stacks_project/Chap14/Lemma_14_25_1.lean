import Mathlib
import StacksProject_2024.Chap14.Lemma_14_23_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open Opposite
open scoped DoldKan

noncomputable section

universe u v

namespace CategoryTheory.CosimplicialObject

variable {A : Type u} [Category.{v} A]

/- Domain-style sampling for Lemma 14.25.1:
- primary domain: the cosimplicial Dold-Kan correspondence, viewed as the dual transport of the
  simplicial normalized Moore complex, the degenerate subcomplex, and the alternating face map
  complex;
- sampled same-kind declarations:
  `CategoryTheory.Abelian.DoldKan.equivalence`,
  `AlgebraicTopology.alternatingCofaceMapComplex`,
  `AlgebraicTopology.DoldKan.degenerateComplexFunctor`,
  `AlgebraicTopology.DoldKan.QInftyToDegenerateComplexNatTrans`,
  `AlgebraicTopology.DoldKan.PInftyToNormalizedMooreComplex`;
- best owner abstraction: the source-facing owners are the degenerate cochain complex
  `degenerateCochainComplexFunctor`, obtained by transport of the simplicial degenerate complex,
  and the quotient functor `normalizedCochainComplexFunctor`, defined as the cokernel of
  `D(U) ⟶ s(U)` under the ambient cokernel hypotheses; the transported Dold-Kan equivalence is
  only the core comparison model and enters later under abelian hypotheses;
- primitive data: the simplicial degenerate-complex functor, the projection
  `QInftyToDegenerateComplex`, the retraction `PInftyToNormalizedMooreComplex`, and the
  opposite/unop transport;
- derived API: the canonical equivalence `CoSimp(A) ≌ CoCh_{≥ 0}(A)`, the quotient map
  `s(U) ⟶ Q(U)`, the section `Q(U) ⟶ s(U)`, and the resulting splitting/quasi-isomorphism
  statements.

Source/core/bridge triage:
- `source-facing`: `degenerateCochainComplexFunctor`, `normalizedCochainComplexFunctor`,
  `degenerateCochainComplexToAlternatingCofaceMapComplex`,
  `alternatingCofaceMapComplexToNormalizedCochainComplex`, and the splitting statements;
- `core/canonical`: `CategoryTheory.Abelian.DoldKan.equivalence`,
  `AlgebraicTopology.alternatingCofaceMapComplex`, `degenerateComplexFunctor`,
  `QInftyToDegenerateComplexNatTrans`, and `PInftyToNormalizedMooreComplex`;
- `bridge/view`: the opposite simplicial object, the right-op/unop transport, the comparison
  isomorphism between `alternatingCofaceMapComplex A` and the transported simplicial model, and
  the comparison isomorphism from the quotient-defined `Q(U)` to the transported Dold-Kan model. -/

/-- The simplicial object in `Aᵒᵖ` corresponding to a cosimplicial object of `A` under the
standard anti-equivalence. -/
private abbrev oppositeSimplicialObject (U : CosimplicialObject A) : SimplicialObject Aᵒᵖ :=
  (CategoryTheory.cosimplicialSimplicialEquiv A).functor.obj (op U)

section SourceFacing

variable [Preadditive A]

scoped notation:max "s(" X ")" => AlternatingCofaceMapComplex.obj X

/-- The alternating coface map complex obtained by transporting the alternating face map complex of
the opposite simplicial object back to `A`. -/
private abbrev alternatingCofaceMapComplexViaOpposite :
    CosimplicialObject A ⥤ CochainComplex A ℕ :=
  ((CategoryTheory.cosimplicialSimplicialEquiv A).functor ⋙
      (AlgebraicTopology.alternatingFaceMapComplex Aᵒᵖ)).rightOp ⋙
    (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))

-- Proof sketch: both complexes have the same objects degreewise, and
-- `AlternatingCofaceMapComplex.d_eq_unop_d` identifies their differentials. This is exactly the
-- compatibility needed to assemble the identity components into an isomorphism of cochain
-- complexes.
/-- The identity degreewise components commute with the two models of the alternating coface
complex. -/
private theorem alternatingCofaceMapComplexIsoViaOpposite_comm
    (U : CosimplicialObject A) (i j : ℕ) (h : (ComplexShape.up ℕ).Rel i j) :
    ((Iso.refl ((s(U)).X i)).hom ≫
        (alternatingCofaceMapComplexViaOpposite.obj U).d i j) =
      (s(U)).d i j ≫
        (Iso.refl ((s(U)).X j)).hom :=
  by
    -- The two differential formulas agree once we identify the unique nonzero cochain differential.
    have h' : i + 1 = j := by
      simpa using h
    subst h'
    simpa [alternatingCofaceMapComplexViaOpposite, AlternatingCofaceMapComplex.obj] using
      (AlternatingCofaceMapComplex.d_eq_unop_d (C := A) U i).symm

/-- The canonical identification between the alternating coface map complex and its
opposite-simplicial realization. -/
private def alternatingCofaceMapComplexIsoViaOpposite (U : CosimplicialObject A) :
    s(U) ≅
      (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤ CochainComplex A ℕ).obj U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun _ ↦ Iso.refl _)
    (alternatingCofaceMapComplexIsoViaOpposite_comm U)

/-- Helper for Lemma 14.25.1: the transported alternating coface functor acts degreewise by the
same component map as the source-facing alternating coface functor. -/
private theorem alternatingCofaceMapComplexViaOpposite_map_f
    {U V : CosimplicialObject A} (f : U ⟶ V) (n : ℕ) :
    (alternatingCofaceMapComplexViaOpposite.map f).f n = f.app { len := n } := by
  rfl

/-- Helper for Lemma 14.25.1: the comparison isomorphism between the source-facing alternating
coface complex and its opposite-simplicial transport is degreewise the identity. -/
private theorem alternatingCofaceMapComplexIsoViaOpposite_component_identities
    (U : CosimplicialObject A) (n : ℕ) :
    ((alternatingCofaceMapComplexIsoViaOpposite U).hom.f n = 𝟙 _) ∧
      ((alternatingCofaceMapComplexIsoViaOpposite U).inv.f n = 𝟙 _) := by
  constructor
  · -- The forward comparison is assembled from identity components.
    simpa [alternatingCofaceMapComplexIsoViaOpposite] using
      (HomologicalComplex.Hom.isoOfComponents_hom_f
        (C₁ := s(U))
        (C₂ := (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤
          CochainComplex A ℕ).obj U)
        (fun _ ↦ Iso.refl _) (alternatingCofaceMapComplexIsoViaOpposite_comm U) n)
  · -- The inverse comparison is assembled from the same identity components.
    simpa [alternatingCofaceMapComplexIsoViaOpposite, AlternatingCofaceMapComplex.obj] using
      (HomologicalComplex.Hom.isoOfComponents_inv_f
        (C₁ := s(U))
        (C₂ := (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤
          CochainComplex A ℕ).obj U)
        (fun _ ↦ Iso.refl _) (alternatingCofaceMapComplexIsoViaOpposite_comm U) n)

section Degenerate

variable [HasZeroObject Aᵒᵖ] [HasBinaryCoproducts Aᵒᵖ] [HasImages Aᵒᵖ]

variable (A) in
/-- The degenerate cochain complex `D(U)` obtained by transporting the simplicial degenerate
subcomplex of the opposite simplicial object. -/
abbrev degenerateCochainComplexFunctor : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  ((CategoryTheory.cosimplicialSimplicialEquiv A).functor ⋙
      degenerateComplexFunctor).rightOp ⋙
    (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ))

/-- The object-level degenerate cochain complex `D(U)` attached to a cosimplicial object `U`. -/
abbrev degenerateCochainComplex (U : CosimplicialObject A) : CochainComplex A ℕ :=
  (degenerateCochainComplexFunctor A).obj U

notation:max "D(" X ")" => degenerateCochainComplex X

/-- The canonical morphism from the transported degenerate cochain complex to the transported
alternating coface map complex, dual to the simplicial projection `K(U) ⟶ D(U)`. -/
private def degenerateCochainComplexToAlternatingCofaceViaOpposite
    (U : CosimplicialObject A) :
    D(U) ⟶
      (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤ CochainComplex A ℕ).obj U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((QInftyToDegenerateComplex (oppositeSimplicialObject U)).op)

/-- The source-facing inclusion `D(U) ⟶ s(U)` in the cosimplicial Dold-Kan correspondence. -/
def degenerateCochainComplexToAlternatingCofaceMapComplex
    (U : CosimplicialObject A) :
    D(U) ⟶ s(U) :=
  degenerateCochainComplexToAlternatingCofaceViaOpposite U ≫
    (alternatingCofaceMapComplexIsoViaOpposite U).inv

/-- Helper for Lemma 14.25.1: the transported morphism `D(U) ⟶ s(U)` is natural before rewriting
through the comparison isomorphism with the source-facing alternating coface complex. -/
@[reassoc]
private theorem degenerateCochainComplexToAlternatingCofaceViaOpposite_naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    (degenerateCochainComplexFunctor A).map f ≫
        degenerateCochainComplexToAlternatingCofaceViaOpposite V =
      degenerateCochainComplexToAlternatingCofaceViaOpposite U ≫
        alternatingCofaceMapComplexViaOpposite.map f := by
  ext n
  -- This is the opposite/unop transport of the simplicial naturality of
  -- `QInftyToDegenerateComplex`.
  simpa [degenerateCochainComplexFunctor, degenerateCochainComplexToAlternatingCofaceViaOpposite,
    alternatingCofaceMapComplexViaOpposite, HomologicalComplex.comp_f] using
    congrArg (fun g => ((HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map g.op).f n)
      (QInftyToDegenerateComplex_naturality
        ((CategoryTheory.cosimplicialSimplicialEquiv A).functor.map f.op)).symm

/-- Helper for Lemma 14.25.1: the inverse comparison from the transported alternating coface
complex to the source-facing one is natural. -/
@[reassoc]
private theorem alternatingCofaceMapComplexIsoViaOpposite_inv_naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    alternatingCofaceMapComplexViaOpposite.map f ≫
        (alternatingCofaceMapComplexIsoViaOpposite V).inv =
      (alternatingCofaceMapComplexIsoViaOpposite U).inv ≫
        (alternatingCofaceMapComplex A).map f := by
  ext n
  rcases alternatingCofaceMapComplexIsoViaOpposite_component_identities U n with ⟨_, hU⟩
  rcases alternatingCofaceMapComplexIsoViaOpposite_component_identities V n with ⟨_, hV⟩
  -- After exposing that the comparison is identity degreewise, both sides are the same component
  -- map `f.app ⦋n⦌`.
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    alternatingCofaceMapComplexViaOpposite_map_f, hU, hV]
  calc
    f.app { len := n } ≫ 𝟙 (V.obj { len := n }) = f.app { len := n } := Category.comp_id _
    _ = 𝟙 (U.obj { len := n }) ≫ f.app { len := n } := (Category.id_comp _).symm

-- Proof sketch: after rewriting both source and target through the opposite-simplicial models,
-- this is the naturality of `QInftyToDegenerateComplex` on the simplicial side.
/-- Naturality of the canonical inclusion `D(U) ⟶ s(U)` with respect to maps of cosimplicial
objects. -/
@[reassoc]
theorem degenerateCochainComplexToAlternatingCofaceMapComplex_naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    (degenerateCochainComplexFunctor A).map f ≫
        degenerateCochainComplexToAlternatingCofaceMapComplex V =
      degenerateCochainComplexToAlternatingCofaceMapComplex U ≫
        (alternatingCofaceMapComplex A).map f :=
  by
    -- Route correction: first transport the simplicial naturality square to the opposite model,
    -- then rewrite that model back to the source-facing alternating coface complex.
    calc
      (degenerateCochainComplexFunctor A).map f ≫
          degenerateCochainComplexToAlternatingCofaceMapComplex V =
        (degenerateCochainComplexFunctor A).map f ≫
          degenerateCochainComplexToAlternatingCofaceViaOpposite V ≫
            (alternatingCofaceMapComplexIsoViaOpposite V).inv := by
          simp [degenerateCochainComplexToAlternatingCofaceMapComplex]
      _ =
        degenerateCochainComplexToAlternatingCofaceViaOpposite U ≫
          alternatingCofaceMapComplexViaOpposite.map f ≫
            (alternatingCofaceMapComplexIsoViaOpposite V).inv := by
          simpa [Category.assoc] using
            (degenerateCochainComplexToAlternatingCofaceViaOpposite_naturality_assoc
              (A := A) f ((alternatingCofaceMapComplexIsoViaOpposite V).inv))
      _ =
        degenerateCochainComplexToAlternatingCofaceViaOpposite U ≫
          (alternatingCofaceMapComplexIsoViaOpposite U).inv ≫
            (alternatingCofaceMapComplex A).map f := by
          simpa [Category.assoc] using
            congrArg
              (fun k => degenerateCochainComplexToAlternatingCofaceViaOpposite U ≫ k)
              (alternatingCofaceMapComplexIsoViaOpposite_inv_naturality (A := A) f)
      _ =
        degenerateCochainComplexToAlternatingCofaceMapComplex U ≫
          (alternatingCofaceMapComplex A).map f := by
          simp [degenerateCochainComplexToAlternatingCofaceMapComplex, Category.assoc]

/-- The canonical natural transformation `D ⟶ s` in the cosimplicial Dold-Kan correspondence. -/
def degenerateCochainComplexToAlternatingCofaceMapComplexNatTrans :
    degenerateCochainComplexFunctor A ⟶ alternatingCofaceMapComplex A where
  app U := degenerateCochainComplexToAlternatingCofaceMapComplex U
  naturality _ _ f := degenerateCochainComplexToAlternatingCofaceMapComplex_naturality f

/-- The arrow-valued functor sending `U` to the canonical inclusion `D(U) ⟶ s(U)`. -/
private def degenerateToAlternatingCofaceArrowFunctor :
    CosimplicialObject A ⥤ Arrow (CochainComplex A ℕ) where
  obj U := Arrow.mk (degenerateCochainComplexToAlternatingCofaceMapComplex U)
  map := fun f ↦
    Arrow.homMk'
      ((degenerateCochainComplexFunctor A).map f)
      ((alternatingCofaceMapComplex A).map f)
      (degenerateCochainComplexToAlternatingCofaceMapComplex_naturality f)
  map_id U := by
    apply Arrow.hom_ext
    · ext n
      simp
    · ext n
      simp [AlternatingCofaceMapComplex.obj]
  map_comp f g := by
    apply Arrow.hom_ext
    · ext n
      simp
    · ext n
      simp [AlternatingCofaceMapComplex.obj]

end Degenerate

section Normalized

variable [HasZeroObject Aᵒᵖ] [HasBinaryCoproducts Aᵒᵖ] [HasImages Aᵒᵖ]
  [HasCokernels (CochainComplex A ℕ)]

/-- The normalized cochain complex functor `Q`, defined source-faithfully as the cokernel of the
canonical inclusion `D(U) ⟶ s(U)`. -/
abbrev normalizedCochainComplexFunctor : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  degenerateToAlternatingCofaceArrowFunctor ⋙
    Limits.coker (CochainComplex A ℕ)

/-- The object-level normalized cochain complex `Q(U)` associated to a cosimplicial object `U`. -/
abbrev normalizedCochainComplex (U : CosimplicialObject A) : CochainComplex A ℕ :=
  normalizedCochainComplexFunctor.obj U

notation:max "Q(" X ")" => normalizedCochainComplex X

-- Proof sketch: this is the natural cokernel projection attached to the defining arrow
-- `D(U) ⟶ s(U)`.
/-- The canonical quotient map `s(U) ⟶ Q(U)` in the cosimplicial Dold-Kan correspondence. -/
def alternatingCofaceMapComplexToNormalizedCochainComplex
    (U : CosimplicialObject A) :
    s(U) ⟶ Q(U) :=
  cokernel.π (degenerateCochainComplexToAlternatingCofaceMapComplex U)

-- Proof sketch: this is the naturality of `Limits.coker.π` evaluated on the arrow-valued functor
-- defined above.
/-- Naturality of the canonical quotient map `s(U) ⟶ Q(U)` with respect to maps of cosimplicial
objects. -/
@[reassoc]
theorem alternatingCofaceMapComplexToNormalizedCochainComplex_naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    (alternatingCofaceMapComplex A).map f ≫ alternatingCofaceMapComplexToNormalizedCochainComplex V =
      alternatingCofaceMapComplexToNormalizedCochainComplex U ≫
        normalizedCochainComplexFunctor.map f := by
  -- This is exactly the naturality of the universal cokernel projection on the defining arrow.
  simpa [normalizedCochainComplexFunctor, alternatingCofaceMapComplexToNormalizedCochainComplex,
    degenerateToAlternatingCofaceArrowFunctor] using
    (Limits.coker.π (C := CochainComplex A ℕ)).naturality
      ((degenerateToAlternatingCofaceArrowFunctor : CosimplicialObject A ⥤
        Arrow (CochainComplex A ℕ)).map f)

/-- The canonical natural quotient map `s ⟶ Q` in the cosimplicial Dold-Kan correspondence. -/
def alternatingCofaceMapComplexToNormalizedCochainComplexNatTrans :
    alternatingCofaceMapComplex A ⟶ normalizedCochainComplexFunctor where
  app U := alternatingCofaceMapComplexToNormalizedCochainComplex U
  naturality _ _ f := alternatingCofaceMapComplexToNormalizedCochainComplex_naturality f

end Normalized

end SourceFacing

section Abelian

variable [Abelian A]

private noncomputable def normalizedCochainComplexEquivalenceCore :
    CosimplicialObject A ≌ CochainComplex A ℕ :=
  (((cosimplicialSimplicialEquiv A).trans
      (Abelian.DoldKan.equivalence : SimplicialObject Aᵒᵖ ≌ ChainComplex Aᵒᵖ ℕ)).rightOp).trans
    (HomologicalComplex.unopEquivalence A (ComplexShape.down ℕ))

private abbrev normalizedCochainComplexFunctorCore : CosimplicialObject A ⥤ CochainComplex A ℕ :=
  (normalizedCochainComplexEquivalenceCore : CosimplicialObject A ≌ CochainComplex A ℕ).functor

/-- Helper for Lemma 14.25.1: the transported normalized projection from the opposite-simplicial
alternating face map complex to the core normalized cochain complex. -/
private def alternatingCofaceViaOppositeToNormalizedCochainComplexCore
    (U : CosimplicialObject A) :
    (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤ CochainComplex A ℕ).obj U ⟶
      normalizedCochainComplexFunctorCore.obj U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((inclusionOfMooreComplexMap (oppositeSimplicialObject U)).op)

/-- Helper for Lemma 14.25.1: the transported projection from the opposite-simplicial alternating
face map complex to the degenerate cochain complex. -/
private def alternatingCofaceViaOppositeToDegenerateCochainComplex
    (U : CosimplicialObject A) :
    (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤ CochainComplex A ℕ).obj U ⟶
      D(U) :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((degenerateComplexι (oppositeSimplicialObject U)).op)

/-- The canonical section from the transported Dold-Kan normalized complex to the transported
alternating coface map complex. -/
private def normalizedCochainComplexCoreToAlternatingCofaceViaOpposite
    (U : CosimplicialObject A) :
    normalizedCochainComplexFunctorCore.obj U ⟶
      (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤ CochainComplex A ℕ).obj U :=
  (HomologicalComplex.unopFunctor A (ComplexShape.down ℕ)).map
    ((PInftyToNormalizedMooreComplex (oppositeSimplicialObject U)).op)

/-- The transported Dold-Kan section from the core normalized cochain complex model to `s(U)`. -/
private def normalizedCochainComplexCoreToAlternatingCofaceMapComplex
    (U : CosimplicialObject A) :
    normalizedCochainComplexFunctorCore.obj U ⟶ s(U) :=
  normalizedCochainComplexCoreToAlternatingCofaceViaOpposite U ≫
    (alternatingCofaceMapComplexIsoViaOpposite U).inv

/-- Helper for Lemma 14.25.1: on the simplicial side, the Dold-Kan decomposition sends the
normalized inclusion to the left biproduct inclusion. -/
private theorem inclusionOfMooreComplexMap_comp_decomposition_hom
    (U : CosimplicialObject A) :
    inclusionOfMooreComplexMap (oppositeSimplicialObject U) ≫
        (decomposition (oppositeSimplicialObject U)).hom =
      biprod.inl := by
  -- TODO: compare `decomposition.hom` with `biprod.lift P∞ Q∞` through the transported
  -- simplicial decomposition identity, then cancel the decomposition inverse.
  sorry

/-- Helper for Lemma 14.25.1: on the simplicial side, the Dold-Kan decomposition sends the
degenerate inclusion to the right biproduct inclusion. -/
private theorem degenerateComplexι_comp_decomposition_hom
    (U : CosimplicialObject A) :
    degenerateComplexι (oppositeSimplicialObject U) ≫
        (decomposition (oppositeSimplicialObject U)).hom =
      biprod.inr := by
  -- TODO: as above, transport the simplicial decomposition identity and isolate the degenerate
  -- summand by cancellation.
  sorry

/-- Helper for Lemma 14.25.1: the transported simplicial section lands on the left biproduct
summand, and the transported degenerate inclusion lands on the right biproduct summand, before
rewriting back to the source-facing alternating coface complex. -/
private theorem alternatingCofaceMapComplexViaOpposite_component_formulas
    (U : CosimplicialObject A) :
    (normalizedCochainComplexCoreToAlternatingCofaceViaOpposite U ≫
        biprod.lift
          (alternatingCofaceViaOppositeToNormalizedCochainComplexCore U)
          (alternatingCofaceViaOppositeToDegenerateCochainComplex U) =
      biprod.inl) ∧
      (degenerateCochainComplexToAlternatingCofaceViaOpposite U ≫
          biprod.lift
            (alternatingCofaceViaOppositeToNormalizedCochainComplexCore U)
            (alternatingCofaceViaOppositeToDegenerateCochainComplex U) =
        biprod.inr) := by
  -- TODO: transport the four simplicial identities
  -- `inclusion ≫ P = 𝟙`, `ι ≫ P = 0`, `inclusion ≫ Q = 0`, and `ι ≫ Q = 𝟙`
  -- through `unopFunctor`, then close by biproduct extensionality.
  sorry

/-- Helper for Lemma 14.25.1: the transported Dold-Kan decomposition of the opposite simplicial
alternating face map complex, oriented so that its hom starts at `s(U)`. -/
private def alternatingCofaceMapComplexViaOppositeIsoCoreDegenerate
    (U : CosimplicialObject A) :
    (alternatingCofaceMapComplexViaOpposite : CosimplicialObject A ⥤ CochainComplex A ℕ).obj U ≅
      normalizedCochainComplexFunctorCore.obj U ⊞ D(U) where
  hom := biprod.lift
    (alternatingCofaceViaOppositeToNormalizedCochainComplexCore U)
    (alternatingCofaceViaOppositeToDegenerateCochainComplex U)
  inv := biprod.desc
    (normalizedCochainComplexCoreToAlternatingCofaceViaOpposite U)
    (degenerateCochainComplexToAlternatingCofaceViaOpposite U)
  hom_inv_id := by
    -- TODO: transport `decomposition.hom_inv_id` degreewise through `unopFunctor`.
    sorry
  inv_hom_id := by
    -- TODO: use `alternatingCofaceMapComplexViaOpposite_component_formulas` and `biprod.hom_ext'`
    -- to identify both biproduct summands.
    sorry

/-- Helper for Lemma 14.25.1: the source-facing decomposition of `s(U)` into the transported
normalized core and the degenerate summand. -/
private def alternatingCofaceMapComplexIsoCoreDegenerate
    (U : CosimplicialObject A) :
    s(U) ≅ normalizedCochainComplexFunctorCore.obj U ⊞ D(U) :=
  alternatingCofaceMapComplexIsoViaOpposite U ≪≫
    alternatingCofaceMapComplexViaOppositeIsoCoreDegenerate U

/-- Helper for Lemma 14.25.1: the transported normalized section is the left biproduct inclusion,
and the transported degenerate section is the right biproduct inclusion. -/
private theorem alternatingCofaceMapComplexIsoCoreDegenerate_component_formulas
    (U : CosimplicialObject A) :
    (normalizedCochainComplexCoreToAlternatingCofaceMapComplex U ≫
        (alternatingCofaceMapComplexIsoCoreDegenerate U).hom =
      biprod.inl) ∧
      (degenerateCochainComplexToAlternatingCofaceMapComplex U ≫
          (alternatingCofaceMapComplexIsoCoreDegenerate U).hom =
        biprod.inr) := by
  -- TODO: rewrite the via-opposite component formulas through
  -- `alternatingCofaceMapComplexIsoViaOpposite`.
  sorry

/-- The comparison morphism from the transported Dold-Kan model to the source-facing quotient
model `Q(U)`. -/
private def normalizedCochainComplexCoreToNormalizedCochainComplex
    (U : CosimplicialObject A) :
    normalizedCochainComplexFunctorCore.obj U ⟶ Q(U) :=
  normalizedCochainComplexCoreToAlternatingCofaceMapComplex U ≫
    alternatingCofaceMapComplexToNormalizedCochainComplex U

-- Proof sketch: on the opposite simplicial side, `Q_\infty : K(U) ⟶ D(U)` splits the inclusion of
-- the degenerate summand, so the quotient-defined `Q(U)` identifies canonically with the
-- transported normalized Moore complex.
/-- The source-facing quotient model `Q(U)` is canonically isomorphic to the transported Dold-Kan
normalized cochain complex. -/
private theorem normalizedCochainComplexCoreToNormalizedCochainComplex_isIso
    (U : CosimplicialObject A) :
    IsIso (normalizedCochainComplexCoreToNormalizedCochainComplex U) :=
  sorry

private def normalizedCochainComplexIsoViaDoldKan (U : CosimplicialObject A) :
    normalizedCochainComplexFunctorCore.obj U ≅ Q(U) :=
  letI := normalizedCochainComplexCoreToNormalizedCochainComplex_isIso U
  asIso (normalizedCochainComplexCoreToNormalizedCochainComplex U)

private theorem normalizedCochainComplexIsoViaDoldKan_naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedCochainComplexFunctorCore.map f ≫ (normalizedCochainComplexIsoViaDoldKan V).hom =
      (normalizedCochainComplexIsoViaDoldKan U).hom ≫ normalizedCochainComplexFunctor.map f :=
  sorry

private def normalizedCochainComplexFunctorCoreIso :
    (normalizedCochainComplexFunctorCore : CosimplicialObject A ⥤ CochainComplex A ℕ) ≅
      normalizedCochainComplexFunctor :=
  NatIso.ofComponents
    (fun U ↦ normalizedCochainComplexIsoViaDoldKan U)
    (fun {_ _} f ↦ normalizedCochainComplexIsoViaDoldKan_naturality f)

/-- Lemma 14.25.1: the quotient-defined normalized cochain complex functor `Q` on cosimplicial
objects of an abelian category gives an equivalence `CoSimp(A) ≌ CoCh_{≥ 0}(A)`. -/
@[stacks 019I]
noncomputable def normalizedCochainComplexEquivalence :
    CosimplicialObject A ≌ CochainComplex A ℕ :=
  normalizedCochainComplexEquivalenceCore.changeFunctor normalizedCochainComplexFunctorCoreIso

/-- The canonical section `Q(U) ⟶ s(U)` in the cosimplicial Dold-Kan correspondence. -/
def normalizedCochainComplexToAlternatingCofaceMapComplex
    (U : CosimplicialObject A) :
    Q(U) ⟶ s(U) :=
  (normalizedCochainComplexIsoViaDoldKan U).inv ≫
    normalizedCochainComplexCoreToAlternatingCofaceMapComplex U

-- Proof sketch: the transported section from the simplicial Dold-Kan equivalence is natural, and
-- the comparison isomorphism from the core normalized model to the quotient model is a natural
-- isomorphism.
/-- Naturality of the canonical section `Q(U) ⟶ s(U)` with respect to maps of cosimplicial
objects. -/
@[reassoc]
theorem normalizedCochainComplexToAlternatingCofaceMapComplex_naturality
    {U V : CosimplicialObject A} (f : U ⟶ V) :
    normalizedCochainComplexFunctor.map f ≫
        normalizedCochainComplexToAlternatingCofaceMapComplex V =
      normalizedCochainComplexToAlternatingCofaceMapComplex U ≫
        (alternatingCofaceMapComplex A).map f := by
  sorry

/-- The canonical natural section `Q ⟶ s` in the cosimplicial Dold-Kan correspondence. -/
def normalizedCochainComplexToAlternatingCofaceMapComplexNatTrans :
    normalizedCochainComplexFunctor ⟶ alternatingCofaceMapComplex A where
  app U := normalizedCochainComplexToAlternatingCofaceMapComplex U
  naturality _ _ f := normalizedCochainComplexToAlternatingCofaceMapComplex_naturality f

/-- The canonical comparison from `D(U) ⊞ Q(U)` to `s(U)` induced by the inclusion of the
degenerate summand and the canonical section `Q(U) ⟶ s(U)`. -/
def degenerateNormalizedBiprodToAlternatingCofaceMapComplex (U : CosimplicialObject A) :
    D(U) ⊞ Q(U) ⟶ s(U) :=
  biprod.desc
    (degenerateCochainComplexToAlternatingCofaceMapComplex U)
    (normalizedCochainComplexToAlternatingCofaceMapComplex U)

/-- The canonical natural transformation `(D ⊞ Q) ⟶ s` giving the functorial splitting of the
alternating coface map complex. -/
def degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatTrans :
    (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ⟶
      alternatingCofaceMapComplex A :=
  biprod.desc
    degenerateCochainComplexToAlternatingCofaceMapComplexNatTrans
    normalizedCochainComplexToAlternatingCofaceMapComplexNatTrans

private noncomputable def degenerateNormalizedBiprodObjIso (U : CosimplicialObject A) :
    ((degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor).obj U ≅
      D(U) ⊞ Q(U) := by
  let E :
      (CosimplicialObject A ⥤ CochainComplex A ℕ) ⥤ CochainComplex A ℕ :=
    (evaluation (CosimplicialObject A) (CochainComplex A ℕ)).obj U
  letI : PreservesBinaryBiproducts E :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts E
  exact E.mapBiprod (degenerateCochainComplexFunctor A) normalizedCochainComplexFunctor

/-- The component of the functorial splitting map at `U` is the objectwise comparison
`D(U) ⊞ Q(U) ⟶ s(U)`. -/
theorem degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatTrans_app
    (U : CosimplicialObject A) :
    degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatTrans.app U =
      (degenerateNormalizedBiprodObjIso U).hom ≫
        degenerateNormalizedBiprodToAlternatingCofaceMapComplex U := by
  let α : degenerateCochainComplexFunctor A ⟶ alternatingCofaceMapComplex A :=
    degenerateCochainComplexToAlternatingCofaceMapComplexNatTrans
  let β : normalizedCochainComplexFunctor ⟶ alternatingCofaceMapComplex A :=
    normalizedCochainComplexToAlternatingCofaceMapComplexNatTrans
  let E :
      (CosimplicialObject A ⥤ CochainComplex A ℕ) ⥤ CochainComplex A ℕ :=
    (evaluation (CosimplicialObject A) (CochainComplex A ℕ)).obj U
  letI : PreservesBinaryBiproducts E :=
    Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts E
  simpa [degenerateNormalizedBiprodObjIso, E, α, β,
    degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatTrans,
    degenerateNormalizedBiprodToAlternatingCofaceMapComplex] using
    (show
        (E.mapBiprod (degenerateCochainComplexFunctor A) normalizedCochainComplexFunctor).hom ≫
          biprod.desc (E.map α) (E.map β) =
            E.map (biprod.desc α β) from by
      rw [Functor.mapBiprod_hom, biprod.lift_desc, biprod.desc_eq, Functor.map_add,
        Functor.map_comp, Functor.map_comp]).symm

-- Proof sketch: exactness of the alternating coface map complex is the cosimplicial dual of
-- Lemma 14.23.1, and in an abelian target it is again detected degreewise.
/-- The alternating coface map complex functor `s` is exact on cosimplicial objects of an abelian
category. -/
theorem alternatingCofaceMapComplex_exact :
    exactFunctor (CosimplicialObject A) (CochainComplex A ℕ)
      (alternatingCofaceMapComplex A) :=
  sorry

-- Proof sketch: `normalizedCochainComplexEquivalence` has functor exactly
-- `normalizedCochainComplexFunctor`, and equivalence functors preserve finite limits and finite
-- colimits.
/-- The normalized cochain complex functor `Q` is exact. -/
theorem normalizedCochainComplexFunctor_exact :
    exactFunctor (CosimplicialObject A) (CochainComplex A ℕ)
      normalizedCochainComplexFunctor := by
  let e :
      (normalizedCochainComplexFunctorCore : CosimplicialObject A ⥤ CochainComplex A ℕ) ≅
        normalizedCochainComplexFunctor :=
    normalizedCochainComplexFunctorCoreIso
  letI : PreservesFiniteLimits normalizedCochainComplexFunctor :=
    preservesFiniteLimits_of_natIso e
  letI : PreservesFiniteColimits normalizedCochainComplexFunctor :=
    preservesFiniteColimits_of_natIso e
  exact (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩

-- Proof sketch: on the opposite simplicial side, `K(U) ≅ N(U) ⊞ D(U)` by Dold-Kan. Transporting
-- that decomposition gives the direct sum decomposition `s(U) ≅ D(U) ⊞ Q(U)` on the cosimplicial
-- side.
/-- The canonical comparison `D(U) ⊞ Q(U) ⟶ s(U)` is an isomorphism. -/
theorem degenerateNormalizedBiprodToAlternatingCofaceMapComplex_isIso
    (U : CosimplicialObject A) :
    IsIso (degenerateNormalizedBiprodToAlternatingCofaceMapComplex U) :=
  sorry

/-- The functorial direct sum decomposition `D ⊞ Q ≅ s` of the alternating coface map complex. -/
noncomputable def degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatIso :
    (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor ≅
      alternatingCofaceMapComplex A :=
  NatIso.ofComponents
    (fun U ↦ by
      letI : IsIso (degenerateNormalizedBiprodToAlternatingCofaceMapComplex U) :=
        degenerateNormalizedBiprodToAlternatingCofaceMapComplex_isIso U
      let e :=
        degenerateNormalizedBiprodObjIso U ≪≫
            asIso (degenerateNormalizedBiprodToAlternatingCofaceMapComplex U)
      exact e)
    (fun {_ _} f ↦ by
      simpa [degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatTrans_app] using
        degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatTrans.naturality f)

/-- The alternating coface map complex splits functorially as `s ≅ D ⊞ Q`. -/
noncomputable def alternatingCofaceMapComplexIsoDegenerateNormalizedBiprod :
    alternatingCofaceMapComplex A ≅
      (degenerateCochainComplexFunctor A) ⊞ normalizedCochainComplexFunctor :=
  degenerateNormalizedBiprodToAlternatingCofaceMapComplexNatIso.symm

-- Proof sketch: compare the quotient-defined map `s(U) ⟶ Q(U)` with the transported Dold-Kan map
-- `s(U) ⟶ N(U)` via the comparison isomorphism `normalizedCochainComplexIsoViaDoldKan U`; the
-- transported Dold-Kan map is a quasi-isomorphism on the opposite simplicial side.
/-- The canonical morphism `s(U) ⟶ Q(U)` is a quasi-isomorphism. -/
theorem alternatingCofaceMapComplexToNormalizedCochainComplex_quasiIso
    (U : CosimplicialObject A) :
    QuasiIso (alternatingCofaceMapComplexToNormalizedCochainComplex U) :=
  sorry

end Abelian

end CategoryTheory.CosimplicialObject
