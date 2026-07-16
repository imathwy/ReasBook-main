import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_5_3
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3
import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_4
import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_11
import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_13
import StacksProject_2024.stacks_project.Chap13.Definition_13_13_1
import StacksProject_2024.stacks_project.Chap13.Lemma_13_13_8

open CategoryTheory
open CategoryTheory.Limits
open FilteredObject.Hom
open scoped CategoryTheory ZeroObject

noncomputable section

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "FilF" => Fil^f(𝒜)

/- Domain-style sampling for Lemma `13.26.3`.
- primary domain: finite filtered objects and strict monomorphisms in an abelian category;
- sampled owner declarations:
  `finiteFilteredObjectCat`,
  `Injective`,
  `CochainComplex.PlusWithTermsIn`,
  `CochainComplex.FilteredInjectivePlus`,
  `CochainComplex.IsKInjective`,
  `FilteredObject.Hom.Strict`,
  `gr^{p}`;
- best owner abstraction: the source-facing chapter owner is `finiteFilteredObjectCat 𝒜` with
  notation `Fil^f(𝒜)` for finite filtered objects, and filtered injectivity should be owned by a
  reusable class parallel to `Injective` and `CochainComplex.IsKInjective`; the bounded-below
  filtered-injective cochain complexes are then canonically owned by
  `CochainComplex.FilteredInjectivePlus 𝒜`;
- primitive data: a finite filtered object `I : FilF`;
- derived API: the split-mono theorem for strict monomorphisms out of a filtered-injective source;
- source/core/bridge triage:
  `source-facing`: filtered injectivity on `FilF` and the split-mono theorem;
  `core/canonical`: the class owner `IsFilteredInjective`, together with
    `FilteredObject.Hom.Strict`;
  `bridge/view`: the graded-piece characterization built directly into `IsFilteredInjective`. -/

/-- A finite filtered object is filtered injective if each of its graded pieces is injective in
the ambient abelian category. -/
class IsFilteredInjective (I : FilF) : Prop where
  injective (p : ℤ) : Injective (gr^{p} I.obj)

attribute [instance] IsFilteredInjective.injective

namespace CochainComplex

variable [Abelian (finiteFilteredObjectCat 𝒜)]

/-- Helper for Lemma 13.26.3: bounded-below cochain complexes whose terms satisfy the object
property `P`. -/
abbrev PlusWithTermsIn (P : ObjectProperty 𝒜) :=
  ObjectProperty.FullSubcategory fun K : CochainComplex.Plus 𝒜 ↦
    ∀ n : ℤ, P (K.obj.X n)

/-- The bounded-below cochain complexes of finite filtered objects whose terms are filtered
injective. -/
abbrev FilteredInjectivePlus (𝒜 : Type u) [Category.{v} 𝒜] [Abelian 𝒜] :=
  CochainComplex.PlusWithTermsIn
    (IsFilteredInjective : ObjectProperty FilF)

end CochainComplex

namespace IsFilteredInjective

/-- Helper for Lemma 13.26.3: the canonical short complex
`0 ⟶ F^(p + 1) X ⟶ F^p X ⟶ gr^p(X) ⟶ 0`. -/
private abbrev stage_row (X : FilteredObject 𝒜) (p : ℤ) : ShortComplex 𝒜 :=
  ShortComplex.mk (X.filtration.stageInclusion p)
    (Limits.cokernel.π (X.filtration.stageInclusion p))
    (Limits.cokernel.condition _)

/-- Helper for Lemma 13.26.3: the canonical stage row is short exact. -/
private theorem stage_row_shortExact (X : FilteredObject 𝒜) (p : ℤ) :
    (stage_row X p).ShortExact := by
  -- Proof comment: this is the standard short exact row attached to a cokernel of a mono.
  refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
  exact ShortComplex.exact_cokernel (X.filtration.stageInclusion p)

/-- Helper for Lemma 13.26.3: the bottom stage has the canonical zero-subobject description. -/
private theorem stage_eq_mk_zero_of_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    X.filtration.obj p = Subobject.mk (0 : (0 : 𝒜) ⟶ X.obj) := by
  -- Proof comment: rewrite the bottom subobject into the explicit zero-arrow model.
  simpa [Subobject.bot_eq_zero] using hp

/-- Helper for Lemma 13.26.3: a zero filtration stage has zero underlying object. -/
private theorem stage_isZero_of_stage_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (hp : X.filtration.obj p = ⊥) :
    IsZero (F^{p} X) := by
  let e : F^{p} X ≅ 0 :=
    Subobject.isoOfEqMk (X.filtration.obj p) (0 : (0 : 𝒜) ⟶ X.obj)
      (stage_eq_mk_zero_of_eq_bot X p hp)
  -- Proof comment: transport the standard zero-object witness across the canonical stage isomorphism.
  exact Limits.IsZero.of_iso (Limits.isZero_zero 𝒜) e

/-- Helper for Lemma 13.26.3: a retract of an injective object is injective. -/
theorem injective_of_retract {C : Type*} [Category C] {X Y : C}
    (i : X ⟶ Y) (r : Y ⟶ X) (hir : i ≫ r = 𝟙 X) [Injective Y] :
    Injective X where
  factors g f := by
    -- Proof comment: extend `g ≫ i` across `f`, then postcompose with the retraction.
    refine ⟨Injective.factorThru (g ≫ i) f ≫ r, ?_⟩
    calc
      f ≫ (Injective.factorThru (g ≫ i) f ≫ r)
          = (f ≫ Injective.factorThru (g ≫ i) f) ≫ r := by
              simp [Category.assoc]
      _ = (g ≫ i) ≫ r := by
            rw [Injective.comp_factorThru]
      _ = g := by
            simpa [Category.assoc] using congrArg (fun k ↦ g ≫ k) hir

/-- Helper for Lemma 13.26.3: the induced map on a filtration stage preserves identities. -/
private theorem filtered_stageMap_id (X : FilteredObject 𝒜) (p : ℤ) :
    stageMap (𝟙 X) p = 𝟙 (F^{p} X) := by
  -- Proof comment: compare both stage maps after postcomposing with the mono stage inclusion.
  apply (cancel_mono (X.filtration.obj p).arrow).1
  rw [stageMap_comm]
  simp

/-- Helper for Lemma 13.26.3: the induced map on a filtration stage preserves composition. -/
private theorem filtered_stageMap_comp
    {X Y Z : FilteredObject 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    stageMap (f ≫ g) p = stageMap f p ≫ stageMap g p := by
  -- Proof comment: compare both candidates after the target stage inclusion.
  apply (cancel_mono (Z.filtration.obj p).arrow).1
  calc
    stageMap (f ≫ g) p ≫ (Z.filtration.obj p).arrow
        = (X.filtration.obj p).arrow ≫ (f ≫ g).hom := by
            rw [stageMap_comm]
    _ = ((X.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
          simp [Category.assoc]
    _ = (stageMap f p ≫ (Y.filtration.obj p).arrow) ≫ g.hom := by
          rw [stageMap_comm]
    _ = stageMap f p ≫ (stageMap g p ≫ (Z.filtration.obj p).arrow) := by
          rw [stageMap_comm]
          simp [Category.assoc]
    _ = (stageMap f p ≫ stageMap g p) ≫ (Z.filtration.obj p).arrow := by
          simp [Category.assoc]

/-- Helper for Lemma 13.26.3: a filtered morphism induces the canonical map on the `p`-th graded
piece. -/
private abbrev gradedPieceMap {X Y : FilteredObject 𝒜} (f : X ⟶ Y) (p : ℤ) :
    gr^{p} X ⟶ gr^{p} Y :=
  cokernel.map (X.filtration.stageInclusion p) (Y.filtration.stageInclusion p)
    (stageMap f (p + 1)) (stageMap f p)
    (stageInclusion_naturality f p)

/-- Helper for Lemma 13.26.3: graded-piece maps preserve identities. -/
private theorem gradedPieceMap_id (X : FilteredObject 𝒜) (p : ℤ) :
    gradedPieceMap (𝟙 X) p = 𝟙 (gr^{p} X) := by
  -- Proof comment: compare both morphisms after precomposing with the canonical cokernel
  -- projection of `F^p X ⟶ gr^p(X)`.
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    -- Proof comment: once the stage maps are normalized, the cokernel-map identity is formal.
    simp [gradedPieceMap, filtered_stageMap_id])

/-- Helper for Lemma 13.26.3: graded-piece maps respect composition of filtered morphisms. -/
private theorem gradedPieceMap_comp {X Y Z : FilteredObject 𝒜} (f : X ⟶ Y) (g : Y ⟶ Z) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  -- Proof comment: compare after the source cokernel projection and use stagewise functoriality
  -- of `stageMap`.
  exact (cancel_epi (cokernel.π (X.filtration.stageInclusion p))).1 (by
    -- Proof comment: the induced cokernel map respects composition once the stage maps do.
    simp [gradedPieceMap, Category.assoc, filtered_stageMap_comp])

/-- Helper for Lemma 13.26.3: retracts of filtered injective finite filtered objects remain
filtered injective. -/
theorem isFilteredInjective_of_retract {X Y : FilF}
    (i : X.obj ⟶ Y.obj) (r : Y.obj ⟶ X.obj) (hir : i ≫ r = 𝟙 X.obj)
    [IsFilteredInjective Y] :
    IsFilteredInjective X := by
  -- Proof comment: apply the `p`-th graded-piece functor to the retract diagram
  -- `X.obj ⟶ Y.obj ⟶ X.obj`; each degree is again a retract, so injectivity descends degreewise.
  refine ⟨fun p ↦ ?_⟩
  let iₚ : gr^{p} X.obj ⟶ gr^{p} Y.obj := gradedPieceMap i p
  let rₚ : gr^{p} Y.obj ⟶ gr^{p} X.obj := gradedPieceMap r p
  have hirₚ : iₚ ≫ rₚ = 𝟙 (gr^{p} X.obj) := by
    -- Proof comment: functoriality of `gradedPieceMap` turns the ambient retract identity into a
    -- graded retract identity.
    calc
      iₚ ≫ rₚ = gradedPieceMap (i ≫ r) p := by
        symm
        exact gradedPieceMap_comp i r p
      _ = gradedPieceMap (𝟙 X.obj) p := by simpa [hir]
      _ = 𝟙 (gr^{p} X.obj) := gradedPieceMap_id X.obj p
  exact injective_of_retract iₚ rₚ hirₚ

/-- Helper for Lemma 13.26.3: if the `(p + 1)`-st filtration stage of a filtered injective object
vanishes, then the top surviving stage `F^p` is injective. -/
theorem injective_top_stage_of_succ_eq_bot {I : FilF} [IsFilteredInjective I] {p : ℤ}
    (hp : I.obj.filtration.obj (p + 1) = ⊥) :
    Injective (F^{p} I.obj) := by
  let S : ShortComplex 𝒜 := stage_row I.obj p
  have hzero : IsZero S.X₁ := by
    -- Proof comment: the first term is `F^(p + 1) I`, which is zero by the hypothesis.
    simpa [S, stage_row] using stage_isZero_of_stage_eq_bot I.obj (p + 1) hp
  have hshort : S.ShortExact := by
    -- Proof comment: use the canonical short exact row
    -- `0 ⟶ F^(p + 1) I ⟶ F^p I ⟶ gr^p(I) ⟶ 0`.
    simpa [S] using stage_row_shortExact I.obj p
  letI : IsIso S.g := (ShortComplex.ShortExact.isIso_g_iff hshort).2 hzero
  let e : F^{p} I.obj ≅ gr^{p} I.obj := asIso S.g
  -- Proof comment: transport injectivity of `gr^p(I)` back across this canonical isomorphism.
  exact Injective.of_iso e.symm (IsFilteredInjective.injective (I := I) p)

/-- Helper for Lemma 13.26.3: strictness and vanishing of the next source stage make the top
stage map into the quotient `A / F^(p + 1)A` monic. -/
theorem mono_to_quotient_of_strict_top_stage
    {I : FilF} {A : FilteredObject 𝒜} (u : I.obj ⟶ A) [Mono u] (hu : Strict u) {p : ℤ}
    (hp : I.obj.filtration.obj (p + 1) = ⊥) :
    Mono (stageMap u p ≫ cokernel.π (A.filtration.stageInclusion p)) := by
  -- Route correction: follow the source route through the Chapter 12 graded exactness bridge,
  -- rather than replacing it with a local filtration computation.
  letI : IsIso (coimageImageComparison u) :=
    (strict_iff_coimageImageComparison_isIso u).1 hu
  letI : IsIso (associatedGradedMap (coimageImageComparison u)) := by infer_instance
  letI : IsIso (gradedPieceMap (coimageImageComparison u) p) :=
    gradedPieceMap_isIso_of_associatedGradedMap_isIso (coimageImageComparison u) p
  have hExact :
      (kernelSourceTargetShortComplex u p).Exact :=
    kernel_source_target_exact_of_gradedPiece_coimageImageComparison_isIso u p
  have hzeroKernelObj : IsZero (kernelFilteredObject u).obj := by
    -- Proof comment: the ambient kernel of a monomorphism is zero, and `kernelFilteredObject`
    -- uses the canonical kernel subobject as its underlying object.
    have hzeroKernel : IsZero (kernel u.hom) :=
      (mono_iff_isZero_kernel u.hom).1 inferInstance
    exact Limits.IsZero.of_iso hzeroKernel (kernelSubobjectIso u.hom)
  have hkernelStageBot : (kernelFilteredObject u).filtration.obj p = ⊥ := by
    -- Proof comment: every subobject of a zero object is equal, so the `p`-th stage is bottom.
    let _ : Subsingleton (Subobject (kernelFilteredObject u).obj) :=
      Subobject.subsingleton_of_isZero hzeroKernelObj
    exact Subsingleton.elim _ _
  have hzeroKernelGraded : IsZero (gr^{p} (kernelFilteredObject u)) := by
    -- Proof comment: the kernel stage and its successor are both zero, so the stage quotient is
    -- canonically isomorphic to a zero stage.
    have hzeroKernelStage : IsZero (F^{p} (kernelFilteredObject u)) := by
      exact stage_isZero_of_eq_bot (kernelFilteredObject u) p hkernelStageBot
    have hkernelStageSuccBot : (kernelFilteredObject u).filtration.obj (p + 1) = ⊥ := by
      exact filtration_eq_bot_of_le (show p ≤ p + 1 by omega) hkernelStageBot
    let S : ShortComplex 𝒜 := stageShortComplex (kernelFilteredObject u) p
    have hzeroKernelStageSucc : IsZero S.X₁ := by
      simpa [S, stageShortComplex] using
        stage_isZero_of_eq_bot (kernelFilteredObject u) (p + 1) hkernelStageSuccBot
    have hshortKernelStage : S.ShortExact := by
      simpa [S] using stage_shortExact (kernelFilteredObject u) p
    letI : IsIso S.g := (ShortComplex.ShortExact.isIso_g_iff hshortKernelStage).2
      hzeroKernelStageSucc
    exact Limits.IsZero.of_iso hzeroKernelStage (asIso S.g).symm
  have hmonoGraded : Mono (gradedPieceMap u p) := by
    -- Proof comment: exactness with zero source upgrades the degree-`p` graded map to a mono.
    exact ((kernelSourceTargetShortComplex u p).exact_iff_mono
      (hzeroKernelGraded.eq_of_src _ _)).1 hExact
  let S : ShortComplex 𝒜 := stageShortComplex I.obj p
  have hzeroStageSucc : IsZero S.X₁ := by
    -- Proof comment: the source `(p + 1)`-st stage is zero by hypothesis.
    simpa [S, stageShortComplex] using stage_isZero_of_eq_bot I.obj (p + 1) hp
  have hshortStage : S.ShortExact := by
    -- Proof comment: use the canonical short exact row
    -- `0 ⟶ F^(p + 1)I ⟶ F^p I ⟶ gr^p(I) ⟶ 0`.
    simpa [S] using stage_shortExact I.obj p
  letI : IsIso (cokernel.π (I.obj.filtration.stageInclusion p)) :=
    (ShortComplex.ShortExact.isIso_g_iff hshortStage).2 hzeroStageSucc
  have hrewrite :
      stageMap u p ≫ cokernel.π (A.filtration.stageInclusion p) =
        cokernel.π (I.obj.filtration.stageInclusion p) ≫ gradedPieceMap u p := by
    -- Proof comment: this is exactly the right square of the stage-row morphism.
    simpa [Category.assoc] using (stageShortComplexMap_right_comm u p).symm
  -- Proof comment: compose the monomorphism on `gr^p(I)` with the source stage isomorphism.
  simpa [hrewrite] using (inferInstance :
    Mono (cokernel.π (I.obj.filtration.stageInclusion p) ≫ gradedPieceMap u p))

/-- Helper for Lemma 13.26.3: the `p`-th graded piece maps canonically into the ambient quotient
`A / F^(p + 1)A`. -/
private abbrev graded_piece_to_ambient_quotient (A : FilteredObject 𝒜) (p : ℤ) :
    gr^{p} A ⟶ cokernel (A.filtration.obj (p + 1)).arrow :=
  cokernel.map (A.filtration.stageInclusion p) (A.filtration.obj (p + 1)).arrow
    (𝟙 _) (A.filtration.obj p).arrow (by
      simp [DecreasingFiltration.stageInclusion, Category.assoc])

/-- Helper for Lemma 13.26.3: the canonical map from `gr^p(A)` to `A / F^(p + 1)A` is obtained by
the expected quotient factorization. -/
private theorem graded_piece_to_ambient_quotient_comm (A : FilteredObject 𝒜) (p : ℤ) :
    cokernel.π (A.filtration.stageInclusion p) ≫ graded_piece_to_ambient_quotient A p =
      (A.filtration.obj p).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow := by
  -- Proof comment: this is the defining compatibility of the induced cokernel map.
  simp [graded_piece_to_ambient_quotient, Category.assoc]

/-- Helper for Lemma 13.26.3: the canonical map `gr^p(A) ⟶ A / F^(p + 1)A` is monic. -/
private theorem graded_piece_to_ambient_quotient_mono (A : FilteredObject 𝒜) (p : ℤ) :
    Mono (graded_piece_to_ambient_quotient A p) := by
  have hpullback :
      IsPullback
        (A.filtration.stageInclusion p)
        (𝟙 (F^{p + 1} A))
        (A.filtration.obj p).arrow
        (A.filtration.obj (p + 1)).arrow := by
    -- Proof comment: `F^(p + 1)A` is the pullback of its own subobject along `F^p A ↪ A`.
    simpa [DecreasingFiltration.stageInclusion] using
      (Subobject.isPullback (A.filtration.obj p).arrow (A.filtration.obj (p + 1))).flip
  -- Proof comment: in an abelian category, the induced map on cokernels of a pullback square is
  -- monic.
  simpa [graded_piece_to_ambient_quotient] using
    (Abelian.mono_cokernel_map_of_isPullback hpullback)

/-- Helper for Lemma 13.26.3: strictness plus vanishing of `F^(p + 1)I` gives the textbook mono
`F^p(I) ⟶ A / F^(p + 1)A`. -/
private theorem mono_to_ambient_quotient_of_strict_top_stage
    {I : FilF} {A : FilteredObject 𝒜} (u : I.obj ⟶ A) [Mono u] (hu : Strict u) {p : ℤ}
    (hp : I.obj.filtration.obj (p + 1) = ⊥) :
    Mono ((((I.obj.filtration.obj p).arrow ≫ u.hom) ≫
      cokernel.π (A.filtration.obj (p + 1)).arrow)) := by
  letI : Mono (stageMap u p ≫ cokernel.π (A.filtration.stageInclusion p)) :=
    mono_to_quotient_of_strict_top_stage u hu hp
  letI : Mono (graded_piece_to_ambient_quotient A p) :=
    graded_piece_to_ambient_quotient_mono A p
  have hrewrite :
      (((I.obj.filtration.obj p).arrow ≫ u.hom) ≫
          cokernel.π (A.filtration.obj (p + 1)).arrow) =
        (stageMap u p ≫ cokernel.π (A.filtration.stageInclusion p)) ≫
          graded_piece_to_ambient_quotient A p := by
    -- Proof comment: rewrite the direct ambient quotient map through the graded quotient.
    calc
      (((I.obj.filtration.obj p).arrow ≫ u.hom) ≫
          cokernel.π (A.filtration.obj (p + 1)).arrow)
          = stageMap u p ≫
              ((A.filtration.obj p).arrow ≫
                cokernel.π (A.filtration.obj (p + 1)).arrow) := by
              rw [stageMap_comm]
              simp [Category.assoc]
      _ = stageMap u p ≫
            (cokernel.π (A.filtration.stageInclusion p) ≫
              graded_piece_to_ambient_quotient A p) := by
            rw [graded_piece_to_ambient_quotient_comm]
      _ = (stageMap u p ≫ cokernel.π (A.filtration.stageInclusion p)) ≫
            graded_piece_to_ambient_quotient A p := by
            simp [Category.assoc]
  -- Proof comment: the direct ambient quotient map is a composite of two monomorphisms.
  simpa [hrewrite] using (inferInstance :
    Mono ((stageMap u p ≫ cokernel.π (A.filtration.stageInclusion p)) ≫
      graded_piece_to_ambient_quotient A p))

/-- Helper for Lemma 13.26.3: if a filtered morphism is the identity on `F^p`, then the `p`-th
stage of its filtered kernel is zero. -/
theorem kernel_stage_eq_bot_of_stage_retraction
    {X Y : FilteredObject 𝒜} (f : X ⟶ Y) {p : ℤ}
    (hp : stageMap f p = 𝟙 (F^{p} X)) :
    (kernelFilteredObject f).filtration.obj p = ⊥ := by
  have hstageZero : stageMap (kernelι f) p = 0 := by
    -- Proof comment: compose the kernel stage map with the identity stage map of `f`.
    calc
      stageMap (kernelι f) p
          = stageMap (kernelι f) p ≫ stageMap f p := by simpa [hp]
      _ = stageMap (kernelι f ≫ f) p := by
            rw [← stageMap_comp]
      _ = 0 := by simp [kernelι_comp]
  have harrowZero :
      ((kernelFilteredObject f).filtration.obj p).arrow = 0 := by
    -- Proof comment: compare the zero stage map after postcomposing with the ambient kernel mono.
    apply (cancel_mono (kernelSubobject f.hom).arrow).1
    calc
      ((kernelFilteredObject f).filtration.obj p).arrow ≫ (kernelSubobject f.hom).arrow
          = stageMap (kernelι f) p ≫ (X.filtration.obj p).arrow := by
              symm
              simpa [kernelι] using stageMap_comm (kernelι f) p
      _ = 0 := by simp [hstageZero]
  -- Proof comment: a subobject is bottom exactly when its defining arrow is zero.
  exact (Subobject.mk_eq_bot_iff_zero _).2 harrowZero

/-- Helper for Lemma 13.26.3: sort the finite filtration witnesses into an ordered window whose
left endpoint is already top and whose successor to the right endpoint is already zero. -/
private theorem ordered_window_of_isFinite (I : FilF) :
    ∃ a b : ℤ, a ≤ b ∧ I.obj.filtration a = ⊤ ∧ I.obj.filtration (b + 1) = ⊥ := by
  rcases I.property with ⟨t, m, htop, hbot⟩
  refine ⟨min t m, max t m, min_le_max _ _, ?_, ?_⟩
  · -- Proof comment: moving left from a top stage keeps the filtration equal to `⊤`.
    exact filtration_eq_top_of_le (X := I.obj) (min_le_left _ _) htop
  · -- Proof comment: moving right from a zero stage keeps the filtration equal to `⊥`.
    exact filtration_eq_bot_of_le (X := I.obj) (le_trans (le_max_right _ _) (by omega)) hbot

/-- Helper for Lemma 13.26.3: if the underlying object of a stage is zero, then that stage is the
bottom subobject. -/
private theorem stage_eq_bot_of_isZero_stage (X : FilteredObject 𝒜) (p : ℤ)
    (hzero : IsZero (F^{p} X)) :
    X.filtration.obj p = ⊥ := by
  apply (Subobject.mk_eq_bot_iff_zero _).2
  have hid : 𝟙 (F^{p} X) = 0 := (IsZero.iff_id_eq_zero (F^{p} X)).1 hzero
  calc
    (X.filtration.obj p).arrow = 𝟙 (F^{p} X) ≫ (X.filtration.obj p).arrow := by
      simp
    _ = 0 := by
      simpa [hid]

/-- Helper for Lemma 13.26.3: a stage that is simultaneously top and bottom forces the underlying
filtered object to be zero. -/
private theorem isZero_obj_of_stage_eq_top_eq_bot (X : FilteredObject 𝒜) (p : ℤ)
    (htop : X.filtration.obj p = ⊤) (hbot : X.filtration.obj p = ⊥) :
    IsZero X.obj := by
  refine (IsZero.iff_id_eq_zero X.obj).2 ?_
  have htop_arrow : (X.filtration.obj p).arrow = 𝟙 X.obj := by
    simpa [Subobject.top_eq_id] using congrArg Subobject.arrow htop
  have hbot_arrow : (X.filtration.obj p).arrow = 0 := by
    simpa [Subobject.bot_eq_zero] using congrArg Subobject.arrow hbot
  exact htop_arrow.symm.trans hbot_arrow

/-- Helper for Lemma 13.26.3: either the finite filtered source is already zero, or there is a
last nonzero stage whose successor stage vanishes. -/
private theorem exists_last_nonzero_stage_or_isZero (I : FilF) :
    (∃ p : ℤ, I.obj.filtration.obj (p + 1) = ⊥ ∧ ¬ IsZero (F^{p} I.obj)) ∨ IsZero I.obj := by
  rcases ordered_window_of_isFinite I with ⟨a, b, hab, ha, hb⟩
  by_cases hI : IsZero I.obj
  · exact Or.inr hI
  · refine Or.inl ⟨b, hb, ?_⟩
    intro hzeroStage
    have hbot_b : I.obj.filtration.obj b = ⊥ :=
      stage_eq_bot_of_isZero_stage I.obj b hzeroStage
    have hbot_a : I.obj.filtration.obj a = ⊥ :=
      filtration_eq_bot_of_le (X := I.obj) hab hbot_b
    exact hI (isZero_obj_of_stage_eq_top_eq_bot I.obj a ha hbot_a)

/-- Helper for Lemma 13.26.3: a morphism out of a zero object is automatically split monic. -/
private theorem isSplitMono_of_zero_source {X Y : FilteredObject 𝒜} (f : X ⟶ Y) [IsZero X] :
    IsSplitMono f := by
  refine IsSplitMono.mk' ⟨0, ?_⟩
  have hid : 𝟙 X = 0 := (IsZero.iff_id_eq_zero X).1 inferInstance
  simpa [hid]

/-- Helper for Lemma 13.26.3: an injective ambient object splits any monomorphism into it. -/
private theorem section_of_mono_into_injective {X Y : 𝒜} [Injective X] (f : X ⟶ Y) [Mono f] :
    ∃ s : Y ⟶ X, f ≫ s = 𝟙 X := by
  -- Proof comment: injectivity of `X` extends the identity morphism across the monomorphism `f`.
  refine ⟨Injective.factorThru (𝟙 X) f, ?_⟩
  simpa using (Injective.comp_factorThru (g := 𝟙 X) (f := f))

/-- Helper for Lemma 13.26.3: the literal one-stage filtered object supported in degrees `q ≤ p`
with underlying object `X`. -/
private def top_stage_filtered_object (p : ℤ) (X : 𝒜) : FilteredObject 𝒜 where
  obj := X
  filtration :=
    { toFun := fun q ↦ if q ≤ p then ⊤ else ⊥
      monotone' := by
        intro q r hqr
        by_cases hq : q ≤ p
        · have hr : r ≤ p := le_trans hqr hq
          simp [hq, hr]
        · have hr : ¬ r ≤ p := fun hr ↦ hq (le_trans hqr hr)
          simp [hq, hr] }

/-- Helper for Lemma 13.26.3: the canonical inclusion of the top stage `F^p(I)` into `I`, viewed
as a morphism from the literal one-stage filtered object. -/
private def top_stage_inclusion {I : FilteredObject 𝒜} (p : ℤ) :
    top_stage_filtered_object p (F^{p} I) ⟶ I where
  hom := (I.filtration.obj p).arrow
  preserves q := by
    -- Proof comment: below degree `p` the source filtration is the whole top stage, while above
    -- degree `p` it is already zero.
    by_cases hq : q ≤ p
    · rw [show (top_stage_filtered_object p (F^{p} I)).filtration.obj q = ⊤ by
          simp [top_stage_filtered_object, hq]]
      refine (Subobject.factors_iff (I.filtration.obj q) ((I.filtration.obj p).arrow)).2 ?_
      refine ⟨Subobject.ofLE (I.filtration.obj p) (I.filtration.obj q)
        (I.filtration.antitone_obj hq), ?_⟩
      simpa using
        (Subobject.ofLE_arrow (h := I.filtration.antitone_obj hq) :
          Subobject.ofLE (I.filtration.obj p) (I.filtration.obj q)
              (I.filtration.antitone_obj hq) ≫ (I.filtration.obj q).arrow =
            (I.filtration.obj p).arrow)
    · rw [show (top_stage_filtered_object p (F^{p} I)).filtration.obj q = ⊥ by
          simp [top_stage_filtered_object, hq]]
      simpa [Subobject.bot_eq_zero] using
        (Subobject.factors_zero :
          (I.filtration.obj q).Factors (0 : (0 : 𝒜) ⟶ I.obj))

/-- Helper for Lemma 13.26.3: on the top surviving degree, the literal top-stage inclusion induces
the identity map on filtration stages. -/
private theorem stageMap_top_stage_inclusion {I : FilteredObject 𝒜} (p : ℤ) :
    stageMap (top_stage_inclusion (I := I) p) p = 𝟙 (F^{p} I) := by
  -- Proof comment: at degree `p`, the source stage is the whole object `F^p(I)`, so cancelling
  -- the ambient stage inclusion identifies the induced stage map with the identity.
  apply (cancel_mono (I.filtration.obj p).arrow).1
  calc
    stageMap (top_stage_inclusion (I := I) p) p ≫ (I.filtration.obj p).arrow
        = (((top_stage_filtered_object p (F^{p} I)).filtration.obj p).arrow) ≫
            (top_stage_inclusion (I := I) p).hom := by
              rw [stageMap_comm]
    _ = (𝟙 (F^{p} I)) ≫ (I.filtration.obj p).arrow := by
          simp [top_stage_inclusion, top_stage_filtered_object]
    _ = (I.filtration.obj p).arrow := by simp

/-- Helper for Lemma 13.26.3: the `(p + 1)`-st stage of the quotient filtration by `F^(p + 1)A`
is already zero. -/
private theorem quotient_stage_succ_eq_bot (A : FilteredObject 𝒜) (p : ℤ) :
    (A.quotientFilteredObject (A.filtration.obj (p + 1))).filtration.obj (p + 1) = ⊥ := by
  let k : (A.filtration.obj (p + 1) : 𝒜) ⟶
      cokernel (A.filtration.obj (p + 1)).arrow :=
    (A.filtration.obj (p + 1)).arrow ≫ cokernel.π (A.filtration.obj (p + 1)).arrow
  rw [show (A.quotientFilteredObject (A.filtration.obj (p + 1))).filtration (p + 1) =
      imageSubobject k by
    simpa [FilteredObject.quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (cokernel.π (A.filtration.obj (p + 1)).arrow) (p + 1))]
  simp [k, Limits.imageSubobject_zero]

/-- Helper for Lemma 13.26.3: every stage above `p` in the quotient filtration by `F^(p + 1)A`
is zero. -/
private theorem quotient_stage_eq_bot_of_gt (A : FilteredObject 𝒜) {p q : ℤ} (hq : p < q) :
    (A.quotientFilteredObject (A.filtration.obj (p + 1))).filtration.obj q = ⊥ := by
  -- Proof comment: once the quotient filtration vanishes at `p + 1`, all later stages also
  -- vanish by monotonicity of the filtration.
  exact filtration_eq_bot_of_le (X := A.quotientFilteredObject (A.filtration.obj (p + 1)))
    (by omega) (quotient_stage_succ_eq_bot A p)

/-- Helper for Lemma 13.26.3: an ambient section of
`F^p(I) ⟶ A / F^(p + 1)A` packages into a filtered retraction onto the literal top-stage summand.
-/
private theorem filtered_split_of_top_stage_section
    {I : FilF} {A : FilteredObject 𝒜} (u : I.obj ⟶ A) {p : ℤ}
    (sigmaQ : cokernel (A.filtration.obj (p + 1)).arrow ⟶ F^{p} I.obj)
    (hsigmaQ :
      ((((I.obj.filtration.obj p).arrow ≫ u.hom) ≫
          cokernel.π (A.filtration.obj (p + 1)).arrow) ≫ sigmaQ) =
        𝟙 (F^{p} I.obj)) :
    let T := top_stage_filtered_object p (F^{p} I.obj)
    let j : T ⟶ I.obj := top_stage_inclusion (I := I.obj) p
    ∃ sQ : A.quotientFilteredObject (A.filtration.obj (p + 1)) ⟶ T,
      let s' := A.toQuotient (A.filtration.obj (p + 1)) ≫ sQ
      (j ≫ u) ≫ s' = 𝟙 T := by
  let T := top_stage_filtered_object p (F^{p} I.obj)
  let j : T ⟶ I.obj := top_stage_inclusion (I := I.obj) p
  let sQ : A.quotientFilteredObject (A.filtration.obj (p + 1)) ⟶ T :=
    { hom := sigmaQ
      preserves := fun q ↦ by
        -- Proof comment: below `p` the target stage is top, while above `p` the quotient
        -- filtration is already zero.
        by_cases hq : q ≤ p
        · rw [show T.filtration.obj q = ⊤ by
              simp [T, top_stage_filtered_object, hq]]
          refine (Subobject.factors_iff (⊤ : Subobject T.obj)
            (((A.quotientFilteredObject (A.filtration.obj (p + 1))).filtration.obj q).arrow ≫
              sigmaQ)).2 ?_
          refine ⟨((A.quotientFilteredObject (A.filtration.obj (p + 1))).filtration.obj q).arrow ≫
              sigmaQ, ?_⟩
          simp
        · have hbotQ :
            (A.quotientFilteredObject (A.filtration.obj (p + 1))).filtration.obj q = ⊥ := by
            exact quotient_stage_eq_bot_of_gt A (p := p) (q := q) (lt_of_not_ge hq)
          rw [show T.filtration.obj q = ⊥ by
              simp [T, top_stage_filtered_object, hq], hbotQ]
          simpa [Subobject.bot_eq_zero] using
            (Subobject.factors_zero :
              ((⊥ : Subobject T.obj)).Factors (0 : (0 : 𝒜) ⟶ T.obj)) }
  refine ⟨sQ, ?_⟩
  -- Proof comment: on underlying objects this is exactly the chosen ambient section.
  apply FilteredObject.Hom.ext
  change ((((I.obj.filtration.obj p).arrow ≫ u.hom) ≫
      cokernel.π (A.filtration.obj (p + 1)).arrow) ≫ sigmaQ) = 𝟙 T.obj
  simpa [T, j, sQ, top_stage_inclusion, Category.assoc] using hsigmaQ

/-- Helper for Lemma 13.26.3: the source kernel of `u ≫ s'` maps to the target kernel of `s'`
because its defining composite with `s'` is zero. -/
private theorem kernel_remainder_map_comp_zero
    {I : FilF} {A T : FilteredObject 𝒜} (u : I.obj ⟶ A) (s' : A ⟶ T) :
    (kernelι (u ≫ s') ≫ u) ≫ s' = 0 := by
  -- Proof comment: reassociate to the composite `kernelι (u ≫ s') ≫ (u ≫ s')`.
  simpa [Category.assoc] using kernelι_comp (u ≫ s')

/-- Helper for Lemma 13.26.3: the canonical morphism from the kernel remainder on the source side
to the kernel remainder on the target side after splitting the top-stage quotient. -/
private abbrev kernel_remainder_map
    {I : FilF} {A T : FilteredObject 𝒜} (u : I.obj ⟶ A) (s' : A ⟶ T) :
    kernelFilteredObject (u ≫ s') ⟶ kernelFilteredObject s' :=
  liftToKernel s' (kernelι (u ≫ s') ≫ u) (kernel_remainder_map_comp_zero u s')

/-- Helper for Lemma 13.26.3: the kernel remainder morphism followed by the target kernel
inclusion is the obvious composite through `u`. -/
private theorem kernel_remainder_map_kernelι
    {I : FilF} {A T : FilteredObject 𝒜} (u : I.obj ⟶ A) (s' : A ⟶ T) :
    kernel_remainder_map u s' ≫ kernelι s' = kernelι (u ≫ s') ≫ u := by
  -- Proof comment: this is exactly the defining compatibility of `liftToKernel`.
  simpa [kernel_remainder_map] using
    liftToKernel_kernelι s' (kernelι (u ≫ s') ≫ u) (kernel_remainder_map_comp_zero u s')

/-- Helper for Lemma 13.26.3: the source kernel remainder is the pullback of the target kernel
along `u`. -/
private theorem kernel_remainder_square_isPullback_after_top_stage_split
    {I : FilF} {A T : FilteredObject 𝒜} (u : I.obj ⟶ A) [Mono u] (s' : A ⟶ T) :
    IsPullback (kernelι (u ≫ s')) (kernel_remainder_map u s') u (kernelι s') := by
  -- Proof comment: use the universal property of the filtered kernel of `u ≫ s'`.
  refine IsPullback.mk'
    ?_
    (fun {_X} {_φ _ψ} _ hkernel ↦ by
      exact (cancel_mono (kernelι (u ≫ s'))).1 hkernel)
    (fun {_X} a b hab ↦ by
      have ha_zero : a ≫ (u ≫ s') = 0 := by
        calc
          a ≫ (u ≫ s') = (a ≫ u) ≫ s' := by simp [Category.assoc]
          _ = (b ≫ kernelι s') ≫ s' := by rw [hab]
          _ = 0 := by simp [Category.assoc, kernelι_comp]
      let l : _ ⟶ kernelFilteredObject (u ≫ s') := liftToKernel (u ≫ s') a ha_zero
      refine ⟨l, ?_, liftToKernel_kernelι (u ≫ s') a ha_zero⟩
      apply (cancel_mono (kernelι s')).1
      calc
        (l ≫ kernel_remainder_map u s') ≫ kernelι s'
            = l ≫ (kernel_remainder_map u s' ≫ kernelι s') := by
                simp [Category.assoc]
        _ = l ≫ (kernelι (u ≫ s') ≫ u) := by
              rw [kernel_remainder_map_kernelι]
        _ = (l ≫ kernelι (u ≫ s')) ≫ u := by
              simp [Category.assoc]
        _ = a ≫ u := by rw [liftToKernel_kernelι]
        _ = b ≫ kernelι s' := hab)
  -- Proof comment: the square commutes by the defining equation of `kernel_remainder_map`.
  simpa [Category.assoc] using (kernel_remainder_map_kernelι u s').symm

/-- Helper for Lemma 13.26.3: after splitting the top stage, strictness of the original mono
descends across the kernel pullback square to the kernel remainder map. -/
private theorem kernel_remainder_strict_of_top_stage_split
    {I : FilF} {A T : FilteredObject 𝒜} (u : I.obj ⟶ A) [Mono u] (hu : Strict u)
    (s' : A ⟶ T) :
    Strict (kernel_remainder_map u s') := by
  -- Proof comment: the remainder map is the second projection in the filtered pullback square over
  -- `u`, so strictness transports through the pullback criterion.
  exact FilteredObject.Hom.strict_snd_of_isPullback_of_strict
    u (kernelι s') (kernel_remainder_square_isPullback_after_top_stage_split u s') hu

/-- Helper for Lemma 13.26.3: after splitting the top stage, the kernel remainder map is again a
monomorphism. -/
private theorem kernel_remainder_mono_of_top_stage_split
    {I : FilF} {A T : FilteredObject 𝒜} (u : I.obj ⟶ A) [Mono u] (s' : A ⟶ T) :
    Mono (kernel_remainder_map u s') := by
  let k := kernel_remainder_map u s'
  have hk_comp : k ≫ kernelι s' = kernelι (u ≫ s') ≫ u := by
    simpa [k] using kernel_remainder_map_kernelι u s'
  -- Proof comment: the composite `k ≫ kernelι s'` is mono, so `k` is mono.
  simpa [k] using (show Mono k from mono_of_mono_fac hk_comp)

/-- Helper for Lemma 13.26.3: once a top-stage summand splits off, the filtered kernel of the
retraction map is a retract of the original source. -/
private theorem kernel_retract_of_section {X T : FilteredObject 𝒜} (f : X ⟶ T) (j : T ⟶ X)
    (hfj : j ≫ f = 𝟙 T) :
    ∃ ρ : X ⟶ kernelFilteredObject f, kernelι f ≫ ρ = 𝟙 _ := by
  have hcomp : (𝟙 X - f ≫ j) ≫ f = 0 := by
    -- Proof comment: `𝟙 - f ≫ j` kills the split summand because `j ≫ f = 𝟙`.
    calc
      (𝟙 X - f ≫ j) ≫ f = f - (f ≫ j ≫ f) := by
        simp [Category.assoc, sub_comp]
      _ = f - f := by
        simp [hfj, Category.assoc]
      _ = 0 := by simp
  refine ⟨liftToKernel f (𝟙 X - f ≫ j) hcomp, ?_⟩
  -- Proof comment: compare after postcomposing with the kernel inclusion; the split identity
  -- forces the lifted endomorphism of the kernel to be the identity.
  apply (cancel_mono (kernelι f)).1
  calc
    (kernelι f ≫ liftToKernel f (𝟙 X - f ≫ j) hcomp) ≫ kernelι f
        = kernelι f ≫ (liftToKernel f (𝟙 X - f ≫ j) hcomp ≫ kernelι f) := by
            simp [Category.assoc]
    _ = kernelι f ≫ (𝟙 X - f ≫ j) := by
          rw [liftToKernel_kernelι]
    _ = kernelι f := by
          simp [sub_eq_add_neg, Category.assoc, kernelι_comp]
    _ = 𝟙 _ ≫ kernelι f := by simp

-- Proof sketch: choose the largest filtration index with nonzero graded piece, use strictness and
-- Lemma 12.19.13 to obtain a monomorphism on the top graded piece, split that monomorphism by
-- injectivity of the graded piece, decompose source and target into that top piece and its kernel,
-- and conclude by induction on the finite filtration length of `I`.
/-- Lemma 13.26.3: if `u : I.obj ⟶ A` is a strict monomorphism in `Fil(𝒜)` with finite filtered-
injective source `I : Fil^f(𝒜)`, then `u` is a split injection. -/
theorem isSplitMono_of_strict
    {I : FilF} {A : FilteredObject 𝒜} (u : I.obj ⟶ A) [IsFilteredInjective I] [Mono u]
    (hu : Strict u) :
    IsSplitMono u := by
  -- Route correction: the proof must split off the top stage via the quotient
  -- `F^p I ⟶ A / F^(p + 1)A`, then recurse on the filtered kernel remainder.
  -- Proof comment: first isolate the source-faithful top-stage dichotomy. Either `I` is already
  -- zero, in which case any map out of it is split monic, or there is a last nonzero stage
  -- `F^p I` with `F^(p + 1) I = 0`, which is exactly the top-stage input used in the Stacks
  -- Project induction.
  rcases exists_last_nonzero_stage_or_isZero I with htop | hzero
  · rcases htop with ⟨p, hp, hp_nonzero⟩
    let T : FilteredObject 𝒜 := top_stage_filtered_object p (F^{p} I.obj)
    let j : T ⟶ I.obj := top_stage_inclusion (I := I.obj) p
    have hmonoAmbient :
        Mono ((((I.obj.filtration.obj p).arrow ≫ u.hom) ≫
          cokernel.π (A.filtration.obj (p + 1)).arrow)) := by
      -- Proof comment: strictness plus the vanishing next source stage gives the textbook mono
      -- `F^p(I) ⟶ A / F^(p + 1)A`.
      exact mono_to_ambient_quotient_of_strict_top_stage u hu hp
    have hinjectiveTop : Injective T.obj := by
      -- Proof comment: the top surviving stage `F^p I` is injective because `F^(p + 1) I = 0`.
      simpa [T] using injective_top_stage_of_succ_eq_bot (I := I) hp
    obtain ⟨sigmaQ, hsigmaQ⟩ :=
      section_of_mono_into_injective
        (((I.obj.filtration.obj p).arrow ≫ u.hom) ≫
          cokernel.π (A.filtration.obj (p + 1)).arrow)
    obtain ⟨sQ, hsQ⟩ :=
      filtered_split_of_top_stage_section (u := u) (p := p) sigmaQ hsigmaQ
    let s' : A ⟶ T := A.toQuotient (A.filtration.obj (p + 1)) ≫ sQ
    have hsection : (j ≫ u) ≫ s' = 𝟙 T := by
      -- Proof comment: the ambient quotient section packages exactly into the filtered retraction.
      simpa [s'] using hsQ
    let k : kernelFilteredObject (u ≫ s') ⟶ kernelFilteredObject s' :=
      kernel_remainder_map u s'
    have hk_mono : Mono k := by
      -- Proof comment: the remainder map is the second leg of the pullback square over the mono
      -- `u`, so it is again monic.
      simpa [k] using kernel_remainder_mono_of_top_stage_split u s'
    have hk_strict : Strict k := by
      -- Proof comment: the explicit pullback square transports strictness from `u` to the
      -- recursive remainder mono.
      simpa [k] using kernel_remainder_strict_of_top_stage_split u hu s'
    obtain ⟨ρ, hρ⟩ := kernel_retract_of_section (f := u ≫ s') (j := j) (by
      simpa [Category.assoc] using hsection)
    let K : FilF :=
      ⟨kernelFilteredObject (u ≫ s'), finite_kernelFilteredObject_isFinite (u ≫ s') I.property⟩
    have hK_injective : IsFilteredInjective K := by
      -- Proof comment: retracts of filtered injective finite filtered objects stay filtered
      -- injective degreewise.
      exact isFilteredInjective_of_retract
        (X := K) (Y := I) (kernelι (u ≫ s')) ρ hρ
    -- TODO: the remaining blocker is now exactly the source-faithful induction on filtration
    -- window width. The recursive source `K` is a finite filtered injective object, the map
    -- `k : K.obj ⟶ kernelFilteredObject s'` is monic. What remains is to prove the pullback
    -- description and strictness of `k`, package the width-decreasing recursion, and then
    -- recombine with the split top-stage summand.
    let _ := hp_nonzero
    let _ := hmonoAmbient
    let _ := hinjectiveTop
    let _ := sigmaQ
    let _ := hsigmaQ
    let _ := sQ
    let _ := hsQ
    let _ := s'
    let _ := hsection
    let _ := hk_mono
    let _ := hk_strict
    let _ := hK_injective
    sorry
  · letI : IsZero I.obj := hzero
    -- Proof comment: the zero-source base case closes immediately by the unique zero retraction.
    exact isSplitMono_of_zero_source u

end IsFilteredInjective

end CategoryTheory
