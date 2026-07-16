import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_5_3
import StacksProject_2024.stacks_project.Chap13.Definition_13_15_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_14_14
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_2
import StacksProject_2024.stacks_project.Chap13.Lemma_13_15_5
import StacksProject_2024.stacks_project.Chap13.Lemma_13_32_2
import StacksProject_2024.stacks_project.Chap13.Situation_13_15_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory
open DerivedCategory.TStructure
open Opposite

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

local notation "Qis" => HomotopyCategory.quasiIso 𝒜 (up ℤ)
local notation "KtoD" => mapHomotopyCategoryToDerived F
local notation "LeftAcyclic" => IsLeftAcyclicForAdditiveFunctor F
local notation "QisOp" => HomotopyCategory.quasiIso 𝒜ᵒᵖ (up ℤ)
local notation "KtoDOp" => mapHomotopyCategoryToDerived F.op

/- Domain-style sampling for Lemma 13.32.3:
- primary domain: unbounded left derived functors of additive functors, left-acyclic objects, and
  derived-category truncation maps;
- sampled owner declarations:
  `IsLeftAcyclicForAdditiveFunctor`,
  `ObjectProperty.HasEpiCover`,
  `Functor.HasLeftDerivedFunctor`,
  `Functor.ComputesLeftDerivedAt`,
  `Functor.totalLeftDerived`,
  `H^i`;
- best owner abstraction: `LeftAcyclic` is the source-facing acyclicity owner, and the canonical
  quotient-generating hypothesis is `HasEpiCover LeftAcyclic`;
- primitive data: the acyclicity object property, the epi-cover owner for that property, and the
  vanishing hypothesis on `F.leftDerived n` when higher derived functors appear explicitly;
- derived API: `(mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis`,
  `(mapHomotopyCategoryToDerived F).ComputesLeftDerivedAt Qis`, the total-derived owner
  `(mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis`, and the truncation-isomorphism
  statements below expressed on cohomology via `(H^i)`.

Source/core/bridge triage:
- `source-facing`: the six theorems in this file;
- `core/canonical`: `IsLeftAcyclicForAdditiveFunctor`, `ObjectProperty.HasEpiCover`,
  `Functor.HasLeftDerivedFunctor`, `Functor.ComputesLeftDerivedAt`, `Functor.totalLeftDerived`,
  and `H^i`;
- `bridge/view`: the truncation morphisms in `DerivedCategory.TStructure`, which remain companions
  to the unbounded left-derived owner rather than a second owner abstraction.
-/

section

variable (n : ℕ)
  [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
  [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
  (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))

/-- Helper for Lemma 13.32.3: an epi-cover hypothesis on `𝒜` transports to a mono-embedding
hypothesis on the opposite category by reversing the chosen epimorphism. -/
private instance hasMonoEmbedding_unop_of_hasEpiCover
    (P : ObjectProperty 𝒜) [P.HasEpiCover] :
    HasMonoEmbedding (fun X : 𝒜ᵒᵖ ↦ P X.unop) where
  exists_mono X := by
    -- Proof comment: choose an epi cover of `X.unop` in `𝒜` and opposite it to obtain the
    -- required mono embedding on `𝒜ᵒᵖ`.
    obtain ⟨Y, hY, f, hf⟩ := (inferInstance : P.HasEpiCover).exists_epi X.unop
    refine ⟨Opposite.op Y, ?_, f.op, inferInstance⟩
    simpa using hY

/-- Helper for Lemma 13.32.3: transport an opposite-side cochain complex back to `𝒜` through the
canonical opposite equivalence. -/
private noncomputable abbrev transported_complex_from_opposite
    {Q : CochainComplex 𝒜ᵒᵖ ℤ} :
    CochainComplex 𝒜 ℤ :=
  ((CochainComplex.opEquivalence 𝒜).inverse.obj Q).unop

/-- Helper for Lemma 13.32.3: transport a map out of the opposite image of `K` back to a map with
target `K` on the original side. -/
private noncomputable abbrev transported_map_to_source
    (K : CochainComplex 𝒜 ℤ)
    {Q : CochainComplex 𝒜ᵒᵖ ℤ}
    (β : (CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K) ⟶ Q) :
    transported_complex_from_opposite (𝒜 := 𝒜) (Q := Q) ⟶ K :=
  (((CochainComplex.opEquivalence 𝒜).inverse.map β).unop) ≫
    (((CochainComplex.opEquivalence 𝒜).unitIso.app (Opposite.op K)).unop).hom

/-- Helper for Lemma 13.32.3: quasi-isomorphisms remain quasi-isomorphisms after transporting the
opposite-side comparison map back to `𝒜`. -/
private theorem quasiIso_transported_map_to_source
    (K : CochainComplex 𝒜 ℤ)
    {Q : CochainComplex 𝒜ᵒᵖ ℤ}
    (β : (CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K) ⟶ Q)
    (hβ : QuasiIso β) :
    QuasiIso (transported_map_to_source (𝒜 := 𝒜) K β) := by
  -- Proof comment: the transport is the composite of the unop image of `β` with a unit
  -- isomorphism component of `CochainComplex.opEquivalence`.
  let _ : QuasiIso β := hβ
  dsimp [transported_map_to_source]
  infer_instance

/-- Helper for Lemma 13.32.3: transporting the canonical opposite image of a cochain complex back
to `𝒜` recovers the original complex. -/
private theorem transported_complex_from_opposite_functor_obj_op
    (K : CochainComplex 𝒜 ℤ) :
    transported_complex_from_opposite (𝒜 := 𝒜)
      (Q := (CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K)) = K := by
  -- Proof comment: `CochainComplex.opEquivalence` is an equivalence, so transporting `op K`
  -- across its inverse/unop description returns `K` componentwise.
  ext i
  simp [transported_complex_from_opposite, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence]

/-- Helper for Lemma 13.32.3: transporting the identity map on the opposite image of `K` back to
`𝒜` gives the identity on `K`. -/
private theorem transported_map_to_source_id
    (K : CochainComplex 𝒜 ℤ) :
    transported_map_to_source (𝒜 := 𝒜) K
      (𝟙 ((CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K))) = 𝟙 K := by
  -- Proof comment: after expanding the transport, the map is the inverse image of the identity
  -- followed by the unit isomorphism component, which simplifies to the identity.
  ext i
  simp [transported_map_to_source, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence]

/-- Helper for Lemma 13.32.3: after passing to the homotopy category, transporting the opposite
image of `K` back to `𝒜` recovers the original homotopy object. -/
private theorem transported_homotopy_object_functor_obj_op
    (K : CochainComplex 𝒜 ℤ) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).obj
        (transported_complex_from_opposite (𝒜 := 𝒜)
          (Q := (CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K))) =
      (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K := by
  -- Proof comment: the homotopy quotient preserves the earlier cochain-level identification
  -- between the transported opposite image of `K` and `K` itself.
  simpa [transported_complex_from_opposite_functor_obj_op]

/-- Helper for Lemma 13.32.3: the homotopy-category image of the transported opposite identity is
the identity on the source homotopy object. -/
private theorem transported_homotopy_map_id
    (K : CochainComplex 𝒜 ℤ) :
    (HomotopyCategory.quotient 𝒜 (up ℤ)).map
        (transported_map_to_source (𝒜 := 𝒜) K
          (𝟙 ((CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K)))) =
      𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Proof comment: once the transported cochain map is identified with `𝟙 K`, the quotient
  -- functor sends it to the identity of the corresponding homotopy object.
  simpa [transported_map_to_source_id]

/-- Helper for Lemma 13.32.3: localizing the transported opposite identity gives the identity on
the source derived object. -/
private theorem transported_derived_map_id
    (K : CochainComplex 𝒜 ℤ) :
    Qis.Q.map
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).map
          (transported_map_to_source (𝒜 := 𝒜) K
            (𝟙 ((CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K))))) =
      𝟙 (Qis.Q.obj ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K)) := by
  -- Proof comment: after the homotopy-level transport is the identity, applying the localization
  -- functor preserves that identity on the derived object of `K`.
  simpa [transported_homotopy_map_id]

/-- Helper for Lemma 13.32.3: the opposite image of `K` defines a canonical homotopy-category
object on the source of the right-derived problem for `F.op`. -/
private noncomputable abbrev opposite_homotopy_object
    (K : CochainComplex 𝒜 ℤ) :
    HomotopyCategory 𝒜ᵒᵖ (up ℤ) :=
  (HomotopyCategory.quotient 𝒜ᵒᵖ (up ℤ)).obj
    ((CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K))

/-- Helper for Lemma 13.32.3: localizing the opposite homotopy object of `K` gives the target
object of the pointwise right-derived comma diagram for `F.op`. -/
private noncomputable abbrev opposite_derived_object
    (K : CochainComplex 𝒜 ℤ) :
    DerivedCategory 𝒜ᵒᵖ :=
  QisOp.Q.obj (opposite_homotopy_object (𝒜 := 𝒜) K)

/-- Helper for Lemma 13.32.3: the opposite transport of the degree-zero complex `A[0]` is the
degree-zero complex `(op A)[0]` in the opposite category. -/
private theorem opposite_homotopy_object_single
    (A : 𝒜) :
    opposite_homotopy_object (𝒜 := 𝒜) ((CochainComplex.singleFunctor 𝒜 0).obj A) =
      ((HomotopyCategory.singleFunctor 𝒜ᵒᵖ 0).obj (Opposite.op A)) := by
  -- Proof comment: the cochain-level opposite equivalence sends the single complex on `A`
  -- directly to the single complex on `op A`, and the homotopy quotient preserves that
  -- identification.
  simp [opposite_homotopy_object, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence]

/-- Helper for Lemma 13.32.3: localizing the opposite transport of the degree-zero complex `A[0]`
recovers the canonical degree-zero object of `D(𝒜ᵒᵖ)`. -/
private theorem opposite_derived_object_single
    (A : 𝒜) :
    opposite_derived_object (𝒜 := 𝒜) ((CochainComplex.singleFunctor 𝒜 0).obj A) =
      QisOp.Q.obj ((HomotopyCategory.singleFunctor 𝒜ᵒᵖ 0).obj (Opposite.op A)) := by
  -- Proof comment: after the previous normalization in the homotopy category, the derived object
  -- is obtained by applying the same localization functor `QisOp.Q`.
  simp [opposite_derived_object, opposite_homotopy_object_single]

/-- Helper for Lemma 13.32.3: the comma category indexing the opposite-side pointwise
right-derived value is canonically the opposite of a structured-arrow category. -/
private noncomputable abbrev opposite_right_index_equivalence
    (K : CochainComplex 𝒜 ℤ) :
    (CostructuredArrow QisOp.Q (opposite_derived_object (𝒜 := 𝒜) K))ᵒᵖ ≌
      StructuredArrow (Opposite.op (opposite_derived_object (𝒜 := 𝒜) K)) QisOp.Q.op :=
  CostructuredArrow.costructuredArrowOpEquivalence QisOp.Q
    (opposite_derived_object (𝒜 := 𝒜) K)

/-- Helper for Lemma 13.32.3: the opposite right-derived indexing category remembers only the
source object of each denominator, viewed in the opposite homotopy category. -/
private noncomputable def opposite_right_index_source_projection
    (K : CochainComplex 𝒜 ℤ) :
    (CostructuredArrow QisOp.Q (opposite_derived_object (𝒜 := 𝒜) K))ᵒᵖ ⥤
      (HomotopyCategory 𝒜ᵒᵖ (up ℤ))ᵒᵖ where
  obj g := Opposite.op g.unop.left
  map f := f.unop.left.op

/-- Helper for Lemma 13.32.3: the canonical comma-category op equivalence preserves the
projection to the underlying source object on the nose. -/
private theorem opposite_right_index_projection_functor_eq
    (K : CochainComplex 𝒜 ℤ) :
    (opposite_right_index_equivalence (𝒜 := 𝒜) K).functor ⋙
        StructuredArrow.proj (Opposite.op (opposite_derived_object (𝒜 := 𝒜) K)) QisOp.Q.op =
      opposite_right_index_source_projection (𝒜 := 𝒜) K := rfl

/-- Helper for Lemma 13.32.3: under the canonical comma-category op equivalence, an
opposite-side denominator is remembered only by the opposite of its source object. -/
private theorem opposite_right_index_equivalence_proj_obj
    (K : CochainComplex 𝒜 ℤ)
    (g : (CostructuredArrow QisOp.Q (opposite_derived_object (𝒜 := 𝒜) K))ᵒᵖ) :
    (StructuredArrow.proj (Opposite.op (opposite_derived_object (𝒜 := 𝒜) K)) QisOp.Q.op).obj
        ((opposite_right_index_equivalence (𝒜 := 𝒜) K).functor.obj g) =
      Opposite.op g.unop.left := by
  -- Proof comment: `CostructuredArrow.costructuredArrowOpEquivalence` sends
  -- `QisOp.Q.obj Y ⟶ opposite_derived_object K` to the structured arrow
  -- `op (opposite_derived_object K) ⟶ QisOp.Q.op.obj (op Y)`, so projecting forgets exactly to
  -- `op Y`.
  simpa [opposite_right_index_projection_functor_eq,
    opposite_right_index_source_projection]

/-- Helper for Lemma 13.32.3: if the opposite transport of `K` computes the unbounded right
derived functor of `F.op`, then `K` computes the unbounded left derived functor of `F`. -/
private theorem hasPointwiseLeftDerivedFunctorAt_of_opposite_right
    (K : CochainComplex 𝒜 ℤ)
    [Functor.HasPointwiseRightDerivedFunctorAt KtoDOp QisOp
      (opposite_homotopy_object (𝒜 := 𝒜) K)] :
    Functor.HasPointwiseLeftDerivedFunctorAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Proof comment: the source-faithful remaining task is to transport the opposite right-derived
  -- costructured-arrow colimit diagram at `opposite_homotopy_object K` to the source left-derived
  -- structured-arrow limit diagram at `((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K)`.
  -- TODO: use `opposite_right_index_equivalence` together with the fixed-`K` transport package
  -- above to identify the opposite costructured-arrow diagram with the source structured-arrow
  -- diagram, then convert the opposite colimit cocone to the required source limit cone.
  sorry

/-- Helper for Lemma 13.32.3: once the opposite right-derived value at `opposite_homotopy_object
K` computes `F.op`, the identity denominator leg transports to the source left-derived identity
projection for `K`. -/
private theorem isIso_leftDerivedValueProjection_of_opposite_right
    (K : CochainComplex 𝒜 ℤ)
    [Functor.ComputesRightDerivedAt KtoDOp QisOp
      (opposite_homotopy_object (𝒜 := 𝒜) K)]
    [Functor.HasPointwiseLeftDerivedFunctorAt KtoD Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K)] :
    IsIso
      (Functor.leftDerivedValueProjection Qis KtoD
        (𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K))
        (MorphismProperty.id_mem Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K))) := by
  -- Proof comment: after the fixed-object pointwise transport is in place, the only remaining
  -- source-faithful comparison is the equality between the transported opposite identity leg and
  -- `leftDerivedValueProjection` for the identity denominator on `K`.
  -- TODO: compare the transported opposite identity leg with
  -- `Functor.leftDerivedValueProjection` by reducing both sides to the identity denominator object
  -- and using `transported_derived_map_id` as the fixed-`K` localization identity.
  sorry

/-- Helper for Lemma 13.32.3: if the opposite transport of `K` computes the unbounded right
derived functor of `F.op`, then `K` computes the unbounded left derived functor of `F`. -/
private theorem computesRightDerivedAt_opposite_implies_computesLeftDerivedAt
    (K : CochainComplex 𝒜 ℤ) :
    Functor.ComputesRightDerivedAt KtoDOp QisOp
        ((HomotopyCategory.quotient 𝒜ᵒᵖ (up ℤ)).obj
          ((CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K))) →
      Functor.ComputesLeftDerivedAt KtoD Qis
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Route correction: the indexing category has now been normalized by
  -- `opposite_right_index_equivalence`, so the remaining work is the actual value/leg transport
  -- from the opposite-side right-derived comma diagram to the source-side left-derived one.
  intro h
  letI :
      Functor.ComputesRightDerivedAt KtoDOp QisOp
        (opposite_homotopy_object (𝒜 := 𝒜) K) := h
  letI :
      Functor.HasPointwiseLeftDerivedFunctorAt KtoD Qis
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) :=
    hasPointwiseLeftDerivedFunctorAt_of_opposite_right (F := F) K
  have hProjection :
      IsIso
        (Functor.leftDerivedValueProjection Qis KtoD
          (𝟙 ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K))
          (MorphismProperty.id_mem Qis ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K))) := by
    -- Proof comment: after separating the pointwise-existence transport from the identity-leg
    -- comparison, the final step is exactly the transported invertibility of the identity
    -- denominator projection.
    exact isIso_leftDerivedValueProjection_of_opposite_right (F := F) K
  exact ⟨hProjection⟩

/-- Helper for Lemma 13.32.3: an object is right acyclic for `F.op` exactly when its unop is left
acyclic for `F`. -/
private theorem right_acyclic_op_iff_left_acyclic
    (A : 𝒜) :
    IsRightAcyclicForAdditiveFunctor F.op (Opposite.op A) ↔ LeftAcyclic A := by
  -- Proof comment: this is the degree-zero specialization of the global opposite computation
  -- bridge above.
  simpa [IsRightAcyclicForAdditiveFunctor, IsLeftAcyclicForAdditiveFunctor,
    HomotopyCategory.quotient_obj_as, CochainComplex.opEquivalence,
    ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence] using
    (computesRightDerivedAt_opposite_implies_computesLeftDerivedAt
      (F := F) ((CochainComplex.singleFunctor 𝒜 0).obj A))

/-- Helper for Lemma 13.32.3: the opposite of a projective resolution of `X.unop` is an
injective resolution of `X`. -/
private noncomputable def injectiveResolution_of_op_projectiveResolution
    {X : 𝒜ᵒᵖ} (P : ProjectiveResolution X.unop) :
    InjectiveResolution X where
  cocomplex := P.complex.op
  ι := P.π.op

/-- Helper for Lemma 13.32.3: the `n`-th right derived functor of `F.op` on `X` identifies with
the opposite of the `n`-th left derived functor of `F` on `X.unop`. -/
private noncomputable def rightDerived_op_obj_iso_op_leftDerived_obj
    (X : 𝒜ᵒᵖ) :
    ((F.op).rightDerived n).obj X ≅ Opposite.op ((F.leftDerived n).obj X.unop) := by
  classical
  let P : ProjectiveResolution X.unop :=
    Classical.choice (show Nonempty (ProjectiveResolution X.unop) from
      (inferInstance : HasProjectiveResolution X.unop).out)
  let I : InjectiveResolution X :=
    injectiveResolution_of_op_projectiveResolution (P := P)
  calc
    ((F.op).rightDerived n).obj X ≅
        (HomologicalComplex.homologyFunctor ℬᵒᵖ (ComplexShape.up ℕ) n).obj
          (((F.op).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) :=
      I.isoRightDerivedObj (F := F.op) n
    _ ≅ Opposite.op
        ((HomologicalComplex.homologyFunctor ℬ (ComplexShape.down ℕ) n).obj
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)) := by
      -- Proof comment: opposite transports send the cochain complex `F.op (P.op)` back to the
      -- opposite of the chain complex `F(P)`, and homology commutes with this opposite passage.
      simpa [I, injectiveResolution_of_op_projectiveResolution] using
        (HomologicalComplex.homologyOp
          (((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)) n)
    _ ≅ Opposite.op ((F.leftDerived n).obj X.unop) := by
      -- Proof comment: the chosen projective resolution `P` computes the left derived functor of
      -- `F` on `X.unop`, so opposite the resulting comparison isomorphism.
      exact (P.isoLeftDerivedObj F n).op

/-- Helper for Lemma 13.32.3: vanishing of `L^n F` transports to vanishing of `R^n(F.op)` on the
opposite category. -/
private theorem isZero_rightDerived_op_obj_of_isZero_leftDerived_obj
    (X : 𝒜ᵒᵖ) :
    IsZero (((F.op).rightDerived n).obj X) := by
  -- Proof comment: compare `((F.op).rightDerived n).obj X` with the opposite of
  -- `(F.leftDerived n).obj X.unop`, then transport the given zero object witness along that iso.
  exact IsZero.of_iso
    (IsZero.op (hn X.unop))
    (rightDerived_op_obj_iso_op_leftDerived_obj (F := F) (n := n) X).symm

/-- Helper for Lemma 13.32.3: every cochain complex admits a quasi-isomorphic source complex whose
terms are left acyclic for `F`. -/
private theorem termwise_leftAcyclic_replacement
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : L ⟶ K), QuasiIso α ∧
      ∀ i : ℤ, LeftAcyclic (L.X i) := by
  -- Proof comment: apply Lemma `13.32.2 (3)` to the opposite complex and then transport the
  -- resulting right-acyclic replacement back to `𝒜`.
  let _ : HasMonoEmbedding (fun X : 𝒜ᵒᵖ ↦ IsRightAcyclicForAdditiveFunctor F.op X) :=
    { exists_mono := fun X ↦ by
        -- Proof comment: reverse an epi cover of `X.unop` and rewrite the acyclicity owner via
        -- `right_acyclic_op_iff_left_acyclic`.
        obtain ⟨Y, hY, f, hf⟩ :=
          (inferInstance :
            HasMonoEmbedding (fun Z : 𝒜ᵒᵖ ↦ LeftAcyclic Z.unop)).exists_mono X
        refine ⟨Y, ?_, f, hf⟩
        simpa using
          (right_acyclic_op_iff_left_acyclic (F := F) (A := Y.unop)).2 hY }
  let Kop : CochainComplex 𝒜ᵒᵖ ℤ :=
    (CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K)
  rcases
      exists_quasiIso_to_termwise_higherRightDerivedVanishes
        (F := F.op) (n := n)
        (hn := isZero_rightDerived_op_obj_of_isZero_leftDerived_obj (F := F) (n := n)) Kop with
    ⟨Q, β, hβ, hQ⟩
  refine
    ⟨transported_complex_from_opposite (𝒜 := 𝒜) (Q := Q),
      transported_map_to_source (𝒜 := 𝒜) K β,
      quasiIso_transported_map_to_source (𝒜 := 𝒜) K β hβ,
      ?_⟩
  intro i
  have hQi :
      IsRightAcyclicForAdditiveFunctor F.op
        (Opposite.op ((transported_complex_from_opposite (𝒜 := 𝒜) (Q := Q)).X i)) := by
    -- Proof comment: term `i` of the transported source is term `-i` of the opposite complex.
    simpa [transported_complex_from_opposite, CochainComplex.opEquivalence,
      ChainComplex.cochainComplexEquivalence, HomologicalComplex.opEquivalence] using hQ (-i)
  exact
    (right_acyclic_op_iff_left_acyclic (F := F)
      (A := (transported_complex_from_opposite (𝒜 := 𝒜) (Q := Q)).X i)).1 hQi

/-- Helper for Lemma 13.32.3: a cochain complex whose terms are left acyclic for `F` computes the
unbounded left derived functor at its image in the homotopy category. -/
private theorem termwise_leftAcyclic_computes_totalLeftDerived
    (K : CochainComplex 𝒜 ℤ)
    (hK : ∀ i : ℤ, LeftAcyclic (K.X i)) :
    (mapHomotopyCategoryToDerived F).ComputesLeftDerivedAt Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Proof comment: equip the opposite category with the transported right-acyclic mono-embedding
  -- hypothesis, compute on the opposite complex via Lemma `13.32.2 (2)`, and then invoke the
  -- opposite computation bridge.
  let _ : HasMonoEmbedding (fun X : 𝒜ᵒᵖ ↦ IsRightAcyclicForAdditiveFunctor F.op X) :=
    { exists_mono := fun X ↦ by
        -- Proof comment: this is the same epi-cover-to-mono-envelope transport used in the
        -- replacement theorem above.
        obtain ⟨Y, hY, f, hf⟩ :=
          (inferInstance :
            HasMonoEmbedding (fun Z : 𝒜ᵒᵖ ↦ LeftAcyclic Z.unop)).exists_mono X
        refine ⟨Y, ?_, f, hf⟩
        simpa using
          (right_acyclic_op_iff_left_acyclic (F := F) (A := Y.unop)).2 hY }
  let _ : Functor.HasRightDerivedFunctor KtoDOp QisOp :=
    has_unbounded_rightDerivedFunctor_of_mono_into_higherRightDerivedVanishes
      (F := F.op) (n := n)
      (hn := isZero_rightDerived_op_obj_of_isZero_leftDerived_obj (F := F) (n := n))
  let Kop : CochainComplex 𝒜ᵒᵖ ℤ :=
    (CochainComplex.opEquivalence 𝒜).functor.obj (Opposite.op K)
  have hKop : ∀ i : ℤ, IsRightAcyclicForAdditiveFunctor F.op (Kop.X i) := by
    intro i
    -- Proof comment: term `i` of `Kop` is `op (K.X (-i))`, so the given left acyclicity
    -- hypothesis rewrites to the opposite right acyclicity required by Lemma `13.32.2 (2)`.
    simpa [Kop, CochainComplex.opEquivalence, ChainComplex.cochainComplexEquivalence,
      HomologicalComplex.opEquivalence] using
      (right_acyclic_op_iff_left_acyclic (F := F) (A := K.X (-i))).2 (hK (-i))
  have hcompOp :
      Functor.ComputesRightDerivedAt KtoDOp QisOp
        ((HomotopyCategory.quotient 𝒜ᵒᵖ (up ℤ)).obj Kop) :=
    computes_unbounded_rightDerived_of_termwise_higherRightDerivedVanishes
      (F := F.op) Kop hKop
  exact
    computesRightDerivedAt_opposite_implies_computesLeftDerivedAt
      (F := F) K hcompOp

/-- Helper for Lemma 13.32.3: the termwise left-acyclic replacement and computation lemmas
globalize to an everywhere-defined unbounded left derived functor. -/
private theorem has_unbounded_leftDerivedFunctor_from_replacement_and_computation :
    (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis := by
  -- Proof comment: first use Lemma `13.14.14` to turn the source-faithful replacement/computation
  -- package into pointwise left-derived existence at every homotopy-category object.
  let _ : (mapHomotopyCategoryToDerived F).HasPointwiseLeftDerivedFunctor Qis :=
    (mapHomotopyCategoryToDerived F).hasPointwiseLeftDerivedFunctor_of_exists_computesLeftDerivedAt
      Qis fun X ↦ by
        -- Proof comment: resolve the underlying complex of `X` by a quasi-isomorphic termwise
        -- left-acyclic complex, then pass the quasi-isomorphism into the homotopy category.
        rcases termwise_leftAcyclic_replacement (F := F) (n := n) hn X.as with
          ⟨L, α, hα, hL⟩
        refine ⟨(HomotopyCategory.quotient 𝒜 (up ℤ)).obj L,
          (HomotopyCategory.quotient 𝒜 (up ℤ)).map α, ?_, ?_⟩
        · -- Proof comment: the quotient functor detects quasi-isomorphisms termwise.
          rw [HomotopyCategory.quotient_map_mem_quasiIso_iff]
          exact hα
        · -- Proof comment: the replacement complex itself is the computing object.
          simpa using
            termwise_leftAcyclic_computes_totalLeftDerived (F := F) L hL
  -- Proof comment: once pointwise left-derived values exist everywhere, the canonical bridge
  -- supplies the total left derived functor.
  infer_instance

-- Proof sketch: use the epi-cover hypothesis and the vanishing `L^n F = 0` to dimension-shift
-- higher left derived functors to zero, then apply the dual cofinality criterion to left-acyclic
-- complexes in the homotopy category.
/-- Lemma 13.32.3 (1): if every object of `𝒜` is a quotient of an object that is left acyclic for
the right exact functor `F`, formalized here by the canonical owner
`HasEpiCover LeftAcyclic`, and if
`L^n F = 0` for some `n ≥ 0`, then the unbounded left derived functor exists. -/
theorem has_unbounded_leftDerivedFunctor_of_epi_from_higherLeftDerivedVanishes
    :
    (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis := by
  -- Proof comment: expose the cofinality-based globalization step through the dedicated helper
  -- above so the remaining blocker is isolated to one structural statement.
  exact has_unbounded_leftDerivedFunctor_from_replacement_and_computation

end

-- Proof sketch: a complex of left-acyclic objects already computes the derived value because
-- termwise application of `F` is a left-derived model on such complexes, so the canonical counit
-- comparison is an isomorphism.
/-- Lemma 13.32.3 (2): after choosing the unbounded left derived functor from part (1), any
cochain complex whose terms are left acyclic for `F`, formalized by
`IsLeftAcyclicForAdditiveFunctor`, computes `LF`. -/
theorem computes_unbounded_leftDerived_of_termwise_higherLeftDerivedVanishes
    [(mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis]
    (K : CochainComplex 𝒜 ℤ)
    (hK : ∀ i : ℤ, LeftAcyclic (K.X i)) :
    (mapHomotopyCategoryToDerived F).ComputesLeftDerivedAt Qis
      ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj K) := by
  -- Proof comment: this is exactly the structural computation helper isolated above.
  exact termwise_leftAcyclic_computes_totalLeftDerived (F := F) K hK

section

variable (n : ℕ)
  [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
  [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
  (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))

-- Proof sketch: construct a quasi-isomorphic replacement by resolving each term by a left-acyclic
-- epi-cover, arranged compatibly with the differentials; the resulting complex maps by a
-- quasi-isomorphism to the original one.
/-- Lemma 13.32.3 (3): every cochain complex in `𝒜` is the target of a quasi-isomorphism from a
cochain complex all of whose terms are left acyclic for `F`, expressed by the canonical owner
`IsLeftAcyclicForAdditiveFunctor`. -/
theorem exists_quasiIso_from_termwise_higherLeftDerivedVanishes
    (K : CochainComplex 𝒜 ℤ) :
    ∃ (L : CochainComplex 𝒜 ℤ) (α : L ⟶ K), QuasiIso α ∧
      ∀ i : ℤ, LeftAcyclic (L.X i) := by
  -- Proof comment: expose the shared replacement helper as the public source-facing statement.
  exact termwise_leftAcyclic_replacement (F := F) (n := n) hn K

end

variable [HasDerivedCategory.{w} 𝒜]

/-- Helper for Lemma 13.32.3: under the vanishing `L^n F = 0`, total left derived functors shift
lower cohomological bounds upward by `n - 1`. -/
private theorem totalLeftDerived_shifts_lower_bound
    (n : ℕ)
    [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
    [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
    (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))
    (E : DerivedCategory 𝒜) (a : ℤ) (hGE : E.IsGE a) :
    let _ : (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis :=
      has_unbounded_leftDerivedFunctor_of_epi_from_higherLeftDerivedVanishes F n hn
    (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).obj E).IsGE
      (a - (n : ℤ) + 1) := by
  -- TODO: apply the source-faithful truncation argument to a left-acyclic replacement and use the
  -- vanishing of `L^n F` to obtain the shifted lower bound.
  sorry

/-- Helper for Lemma 13.32.3: the total left derived functor preserves upper cohomological
bounds. -/
private theorem totalLeftDerived_preserves_upper_bound
    [(mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis]
    (E : DerivedCategory 𝒜) (b : ℤ) (hLE : E.IsLE b) :
    (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).obj E).IsLE b := by
  -- TODO: reduce to a bounded-above representative of `E` and compute `LF` by a bounded-above
  -- left-acyclic resolution whose image under `F` stays bounded above in the same degree range.
  sorry

-- Proof sketch: first replace `E` by a quasi-isomorphic complex of left-acyclic objects using
-- part (3). The dual spectral-sequence argument shows that truncating above degree `a + n - 1`
-- does not affect the cohomology of `LF(E)` in degrees `≤ a`.
/-- Lemma 13.32.3 (4): assuming the hypotheses of parts (1) and (3), for `E ∈ D(\mathcal A)`
the canonical morphism `LF(τ_{\le a + n - 1} E) ⟶ LF(E)` induces an isomorphism on `H^i` for
every `i ≤ a`. -/
theorem homologyMap_unboundedLeftDerived_isIso_of_derivedTruncLE
    (n : ℕ)
    [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
    [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
    (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))
    (E : DerivedCategory 𝒜) (a i : ℤ) (hi : i ≤ a) :
    let _ : (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis :=
      has_unbounded_leftDerivedFunctor_of_epi_from_higherLeftDerivedVanishes F
    IsIso
      ((H^i).map
        (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).map
          ((t.truncLEι (a + (n : ℤ) - 1)).app E))) := by
  let LF := (mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis
  let c : ℤ := a + (n : ℤ) - 1
  let H := DerivedCategory.homologyFunctor ℬ
  let T : Triangle (DerivedCategory ℬ) := LF.mapTriangle.obj ((t.triangleLEGT c).obj E)
  have hT : T ∈ distTriang (DerivedCategory ℬ) := by
    -- Proof comment: apply `LF` to the standard truncation triangle
    -- `τ≤c E ⟶ E ⟶ τ≥(c + 1) E ⟶`.
    simpa [T] using
      LF.map_distinguished ((t.triangleLEGT c).obj E) (t.triangleLEGT_distinguished c E)
  have h₃ : T.obj₃.IsGE (a + 1) := by
    -- Proof comment: the third vertex is `LF(τ≥(a + n) E)`, so the shifted lower-bound helper
    -- puts it in degrees `≥ a + 1`.
    have hGE : ((t.truncGE (c + 1)).obj E).IsGE (c + 1) := by infer_instance
    simpa [T, c] using totalLeftDerived_shifts_lower_bound (F := F) n hn
      ((t.truncGE (c + 1)).obj E) (c + 1) hGE
  have hmor₂_zero : (H i).map T.mor₂ = 0 := by
    -- Proof comment: the discarded high-degree piece has no cohomology in degrees `≤ a`.
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (a + 1) i (by omega)).eq_of_tgt _ _
  have hδ_zero : HomologySequence.δ T (i - 1) i (by omega) = 0 := by
    -- Proof comment: the connecting morphism lands in another vanishing degree of that same
    -- high-degree piece.
    exact (DerivedCategory.isZero_of_isGE T.obj₃ (a + 1) (i - 1) (by omega)).eq_of_src _ _
  letI : Epi ((H i).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 hmor₂_zero
  letI : Mono ((H i).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (i - 1) i (by omega)).2 hδ_zero
  simpa [T, c] using isIso_of_mono_of_epi ((H i).map T.mor₁)

-- Proof sketch: apply the left-derived functor to the truncation triangle for a cochain-complex
-- representative of `E`; the quotient complex has no cohomology in degrees `≥ b`, so `LF`
-- preserves cohomology in those degrees.
/-- Lemma 13.32.3 (5): for `E ∈ D(\mathcal A)`, the canonical morphism
`LF(E) ⟶ LF(τ_{\ge b} E)` induces an isomorphism on `H^i` for every `i ≥ b`. -/
theorem homologyMap_unboundedLeftDerived_isIso_of_derivedTruncGE
    [(mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis]
    (E : DerivedCategory 𝒜) (b i : ℤ) (hi : b ≤ i) :
    IsIso
      ((H^i).map
        (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).map
          ((t.truncGEπ b).app E))) := by
  let LF := (mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis
  let H := DerivedCategory.homologyFunctor ℬ
  let T : Triangle (DerivedCategory ℬ) := LF.mapTriangle.obj ((t.triangleLEGT (b - 1)).obj E)
  have hT : T ∈ distTriang (DerivedCategory ℬ) := by
    -- Proof comment: apply `LF` to the standard truncation triangle
    -- `τ≤(b - 1) E ⟶ E ⟶ τ≥b E ⟶`.
    simpa [T] using
      LF.map_distinguished ((t.triangleLEGT (b - 1)).obj E)
        (t.triangleLEGT_distinguished (b - 1) E)
  have h₁ : T.obj₁.IsLE (b - 1) := by
    -- Proof comment: the first vertex is `LF(τ≤(b - 1) E)`, and the upper-bound helper shows
    -- that `LF` preserves the upper truncation cutoff.
    have hLE : ((t.truncLE (b - 1)).obj E).IsLE (b - 1) := by infer_instance
    simpa [T] using totalLeftDerived_preserves_upper_bound (F := F)
      ((t.truncLE (b - 1)).obj E) (b - 1) hLE
  have hmor₁_zero : (H i).map T.mor₁ = 0 := by
    -- Proof comment: the low-degree truncation term has no cohomology in degrees `≥ b`.
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) i (by omega)).eq_of_src _ _
  have hδ_zero : HomologySequence.δ T i (i + 1) rfl = 0 := by
    -- Proof comment: the connecting morphism starts in another vanishing degree of the same
    -- low-degree truncation term.
    exact (DerivedCategory.isZero_of_isLE T.obj₁ (b - 1) (i + 1) (by omega)).eq_of_tgt _ _
  letI : Epi ((H i).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl).2 hδ_zero
  letI : Mono ((H i).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT i).2 hmor₁_zero
  simpa [T] using isIso_of_mono_of_epi ((H i).map T.mor₂)

-- Proof sketch: combine part (4) on the left with part (5) on the right. If `E` has no
-- cohomology outside `[a, b]`, then the truncation isomorphisms identify `LF(E)` with an object
-- whose cohomology is forced to vanish outside `[a - n + 1, b]`.
/-- Lemma 13.32.3 (6): assuming the hypotheses of parts (1) and (3), if
`H^i(E) = 0` for `i ∉ [a, b]`, then `H^i(LF(E)) = 0` for `i ∉ [a - n + 1, b]`. -/
theorem unboundedLeftDerivedVanishesOutside_shifted_range
    (n : ℕ)
    [ObjectProperty.HasEpiCover (IsLeftAcyclicForAdditiveFunctor F)]
    [PreservesFiniteColimits F] [HasProjectiveResolutions 𝒜]
    (hn : ∀ A : 𝒜, IsZero ((F.leftDerived n).obj A))
    (E : DerivedCategory 𝒜) (a b : ℤ)
    (hGE : E.IsGE a) (hLE : E.IsLE b) :
    let _ : (mapHomotopyCategoryToDerived F).HasLeftDerivedFunctor Qis :=
      has_unbounded_leftDerivedFunctor_of_epi_from_higherLeftDerivedVanishes F
    (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).obj E).IsGE
      (a - (n : ℤ) + 1) ∧
      (((mapHomotopyCategoryToDerived F).totalLeftDerived Qh Qis).obj E).IsLE b := by
  -- Proof comment: the final amplitude statement is exactly the conjunction of the shifted lower
  -- bound and preserved upper bound established in the two structural helpers.
  constructor
  · exact totalLeftDerived_shifts_lower_bound (F := F) n hn E a hGE
  · exact totalLeftDerived_preserves_upper_bound (F := F) E b hLE

end

end CategoryTheory
