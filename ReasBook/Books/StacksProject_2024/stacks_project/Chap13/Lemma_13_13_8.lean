import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import StacksProject_2024.stacks_project.Chap12.Lemma_12_16_2
import StacksProject_2024.stacks_project.Chap12.Lemma_12_19_12
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_1
import StacksProject_2024.stacks_project.Chap12.Definition_12_19_3
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_1
import StacksProject_2024.stacks_project.Chap12.Lemma_12_24_11
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_5

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex
open scoped CategoryTheory ZeroObject

noncomputable section

universe v u

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Helper for Lemma 13.13.8: any morphism factors through its image, so composing with the
cokernel projection of the image mono is zero. -/
theorem imageSubobject_comp_cokernelPi_eq_zero {X Y : 𝒜} (g : X ⟶ Y) :
    g ≫ cokernel.π (imageSubobject g).arrow = 0 := by
  -- Proof comment: rewrite `g` through its image factorization and then use the cokernel
  -- relation of the image inclusion.
  calc
    g ≫ cokernel.π (imageSubobject g).arrow
        = factorThruImageSubobject g ≫
            ((imageSubobject g).arrow ≫ cokernel.π (imageSubobject g).arrow) := by
              rw [← Category.assoc, imageSubobject_arrow_comp]
    _ = factorThruImageSubobject g ≫ 0 := by
          rw [cokernel.condition (imageSubobject g).arrow]
    _ = 0 := by simp

namespace FilteredObject.Hom

open FilteredObject

/-- Helper for Lemma 13.13.8: postcomposing an epimorphism does not change the image subobject. -/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : 𝒜} (g : X ⟶ Y) [Epi g] (h : Y ⟶ Z) :
    imageSubobject (g ≫ h) = imageSubobject h := by
  -- Proof comment: first restrict the composite to the literal image of `g`, then identify that
  -- image with the top subobject because `g` is epi.
  calc
    imageSubobject (g ≫ h) = imageSubobject ((imageSubobject g).arrow ≫ h) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction g h]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ h) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ h))
        (Limits.imageSubobject_eq_top_of_epi g)
    _ = imageSubobject h := by
      simpa using Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) h

/-- Helper for Lemma 13.13.8: the induced filtered object on a subobject of a filtered object. -/
private def inducedSubobjectFilteredObject (A : FilteredObject 𝒜) (X : Subobject A.obj) :
    FilteredObject 𝒜 where
  obj := X
  filtration := A.filtration.induced X

/-- Helper for Lemma 13.13.8: the induced filtration on a subobject is preserved by the ambient
inclusion. -/
private theorem inducedSubobjectInclusion_preserves (A : FilteredObject 𝒜)
    (X : Subobject A.obj) (i : ℤ) :
    (A.filtration i).Factors
      (((inducedSubobjectFilteredObject A X).filtration i).arrow ≫ X.arrow) := by
  -- Proof comment: the induced stage is a pullback stage, so the ambient inclusion is the
  -- canonical pullback factorization.
  change (A.filtration i).Factors
    (((Subobject.pullback X.arrow).obj (A.filtration i)).arrow ≫ X.arrow)
  rw [← pullback_factors_iff (f := X.arrow) (y := A.filtration i)
    (h := ((Subobject.pullback X.arrow).obj (A.filtration i)).arrow)]
  exact Subobject.factors_self _

/-- Helper for Lemma 13.13.8: the canonical filtered inclusion of an induced filtered subobject.
-/
private def inducedSubobjectInclusion (A : FilteredObject 𝒜) (X : Subobject A.obj) :
    inducedSubobjectFilteredObject A X ⟶ A where
  hom := X.arrow
  preserves := inducedSubobjectInclusion_preserves A X

/-- Helper for Lemma 13.13.8: the quotient filtered object by a subobject of the ambient object.
-/
private def quotientFilteredObject (A : FilteredObject 𝒜) (X : Subobject A.obj) :
    FilteredObject 𝒜 where
  obj := cokernel X.arrow
  filtration := A.filtration.quotient (cokernel.π X.arrow)

/-- Helper for Lemma 13.13.8: the quotient filtration is preserved by the canonical projection. -/
private theorem quotientFilteredProjection_preserves (A : FilteredObject 𝒜)
    (X : Subobject A.obj) (i : ℤ) :
    ((quotientFilteredObject A X).filtration i).Factors
      ((A.filtration i).arrow ≫ cokernel.π X.arrow) := by
  -- Proof comment: by definition the quotient stage is the image of the composite into the
  -- quotient object.
  let k : (A.filtration i : 𝒜) ⟶ cokernel X.arrow :=
    (A.filtration.obj i).arrow ≫ cokernel.π X.arrow
  rw [show (quotientFilteredObject A X).filtration i = imageSubobject k by
    simpa [quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (cokernel.π X.arrow) i)]
  simpa [k, imageSubobject_arrow_comp] using
    (Subobject.factors_comp_arrow (factorThruImageSubobject k))

/-- Helper for Lemma 13.13.8: the canonical filtered projection onto the quotient by a subobject.
-/
private def toFilteredQuotient (A : FilteredObject 𝒜) (X : Subobject A.obj) :
    A ⟶ quotientFilteredObject A X where
  hom := cokernel.π X.arrow
  preserves := quotientFilteredProjection_preserves A X

/-- Helper for Lemma 13.13.8: pulling back the zero subobject along a monomorphism stays zero. -/
private theorem pullback_bot_of_mono {X Y : 𝒜} (f : X ⟶ Y) [Mono f] :
    (Subobject.pullback f).obj (⊥ : Subobject Y) = (⊥ : Subobject X) := by
  -- Proof comment: after rewriting the pullback stage as `pullback.snd`, the pullback square
  -- shows the composite with the mono `f` is zero, so cancellation forces the pullback arrow to
  -- vanish.
  rw [Subobject.pullback_obj]
  apply (Subobject.mk_eq_bot_iff_zero).2
  apply (cancel_mono f).1
  simpa using (pullback.condition (f := (⊥ : Subobject Y).arrow) (g := f)).symm


/-- Helper for Lemma 13.13.8: a filtered morphism out of the cokernel cutoff term induced by a
vanishing composite. -/
noncomputable def descToCokernel {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) :
    cokernelFilteredObject f ⟶ C where
  hom := cokernel.desc f.hom g.hom (congrArg FilteredObject.Hom.hom hfg)
  preserves := by
    intro i
    let q : (B.filtration i : 𝒜) ⟶ cokernel f.hom := (B.filtration.obj i).arrow ≫ cokernel.π f.hom
    let δ : cokernel f.hom ⟶ C.obj := cokernel.desc f.hom g.hom (congrArg FilteredObject.Hom.hom hfg)
    have hstage :
        (cokernelFilteredObject f).filtration i = imageSubobject q := by
      -- Proof comment: the quotient stage is by definition the image of the stage composite into
      -- the ambient cokernel cutoff object.
      simpa [cokernelFilteredObject, q] using
        (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
          (cokernel.π f.hom) i)
    have hqδ :
        q ≫ δ = (B.filtration.obj i).arrow ≫ g.hom := by
      -- Proof comment: the defining equation of `cokernel.desc` identifies the descended map on
      -- the stage composite with the original stagewise map of `g`.
      simp [q, δ, Category.assoc]
    let u : (imageSubobject q : 𝒜) ⟶ C.obj := (imageSubobject q).arrow ≫ δ
    rw [hstage]
    rw [Subobject.factors_iff]
    have hle : imageSubobject u ≤ C.filtration i := by
      -- Proof comment: the image of the descended stage map agrees with the image of the original
      -- stagewise composite for `g`, which lies in `C.filtration i`.
      have hImage :
          imageSubobject u = imageSubobject ((B.filtration.obj i).arrow ≫ g.hom) := by
        calc
          imageSubobject u = imageSubobject (factorThruImageSubobject q ≫ u) := by
            symm
            simpa [u, Category.assoc] using
              imageSubobject_comp_eq_of_epi (factorThruImageSubobject q) u
          _ = imageSubobject ((factorThruImageSubobject q ≫ (imageSubobject q).arrow) ≫ δ) := by
                simp [u]
          _ = imageSubobject (q ≫ δ) := by
                rw [imageSubobject_arrow_comp]
          _ = imageSubobject ((B.filtration.obj i).arrow ≫ g.hom) := by
                rw [hqδ]
      rw [hImage]
      exact imageSubobject_le _ _ (Subobject.factorThru_arrow _ _ (g.preserves i))
    refine ⟨factorThruImageSubobject u ≫ Subobject.ofLE _ _ hle, ?_⟩
    calc
      (factorThruImageSubobject u ≫ Subobject.ofLE _ _ hle) ≫ (C.filtration i).arrow
          = factorThruImageSubobject u ≫
              (Subobject.ofLE (imageSubobject u) (C.filtration i) hle ≫
                (C.filtration i).arrow) := by
                  simp [Category.assoc]
      _ = factorThruImageSubobject u ≫ (imageSubobject u).arrow := by
            simp [Subobject.ofLE_arrow]
      _ = u := by
            simpa using imageSubobject_arrow_comp u

/-- Helper for Lemma 13.13.8: the canonical quotient map composed with the descended cokernel
arrow recovers the original morphism. -/
theorem toCokernel_descToCokernel {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) :
    toCokernel f ≫ descToCokernel f g hfg = g := by
  -- Proof comment: after forgetting the filtration this is exactly the defining equation of
  -- `cokernel.desc`.
  apply FilteredObject.forget.map_injective
  change cokernel.π f.hom ≫ (descToCokernel f g hfg).hom = g.hom
  simpa [descToCokernel] using
    cokernel.π_desc f.hom g.hom (congrArg FilteredObject.Hom.hom hfg)

/-- Helper for Lemma 13.13.8: a filtered morphism into the kernel cutoff term induced by a
vanishing composite. -/
noncomputable def liftToKernel {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : C ⟶ A)
    (hgf : g ≫ f = 0) :
    C ⟶ kernelFilteredObject f where
  hom := (kernelSubobject f.hom).factorThru g.hom <| by
    rw [kernelSubobject_factors_iff]
    exact congrArg FilteredObject.Hom.hom hgf
  preserves := by
    intro i
    -- Proof comment: the target stage is a pullback stage of `A.filtration i` along the kernel
    -- inclusion, so the desired factorization follows from the stagewise factorization of `g`.
    change ((Subobject.pullback (kernelSubobject f.hom).arrow).obj (A.filtration i)).Factors
      ((C.filtration i).arrow ≫
        (kernelSubobject f.hom).factorThru g.hom (by
          rw [kernelSubobject_factors_iff]
          exact congrArg FilteredObject.Hom.hom hgf))
    rw [pullback_factors_iff]
    simpa [Category.assoc] using g.preserves i

/-- Helper for Lemma 13.13.8: the induced kernel lift followed by the kernel inclusion recovers
the original morphism. -/
theorem liftToKernel_kernelι {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : C ⟶ A)
    (hgf : g ≫ f = 0) :
    liftToKernel f g hgf ≫ kernelι f = g := by
  -- Proof comment: after forgetting the filtration this is the defining equation of
  -- the factorization through the kernel subobject.
  apply FilteredObject.forget.map_injective
  simpa [liftToKernel, kernelι] using
    Subobject.factorThru_arrow (kernelSubobject f.hom) g.hom (by
      rw [kernelSubobject_factors_iff]
      exact congrArg FilteredObject.Hom.hom hgf)

/-- Helper for Lemma 13.13.8: the induced filtration on the kernel cutoff term remains finite
when the source filtration is finite. -/
theorem finite_kernelFilteredObject_isFinite {A B : FilteredObject 𝒜} (f : A ⟶ B)
    (hA : A.IsFinite) :
    (kernelFilteredObject f).IsFinite := by
  -- Proof comment: the induced kernel filtration keeps the same cutoff indices as the source
  -- filtration because pullback preserves `⊤`, and pullback of `⊥` along the kernel mono is `⊥`.
  rcases hA with ⟨n, m, hn, hm⟩
  refine ⟨n, m, ?_, ?_⟩
  · change (Subobject.pullback (kernelSubobject f.hom).arrow).obj (A.filtration n) = ⊤
    rw [hn, Subobject.pullback_top]
  · change (Subobject.pullback (kernelSubobject f.hom).arrow).obj (A.filtration m) = ⊥
    rw [hm, pullback_bot_of_mono (kernelSubobject f.hom).arrow]

/-- Helper for Lemma 13.13.8: the quotient filtration on the cokernel cutoff term remains finite
when the target filtration is finite. -/
theorem finite_cokernelFilteredObject_isFinite {A B : FilteredObject 𝒜} (f : A ⟶ B)
    (hB : B.IsFinite) :
    (cokernelFilteredObject f).IsFinite := by
  -- Proof comment: the quotient filtration uses the same witness indices as the target
  -- filtration; stagewise it is an image subobject, which is `⊤` at the top witness because the
  -- quotient map is epi, and `⊥` at the bottom witness because the composite is zero.
  rcases hB with ⟨n, m, hn, hm⟩
  refine ⟨n, m, ?_, ?_⟩
  · rw [show (cokernelFilteredObject f).filtration n =
        imageSubobject ((B.filtration n).arrow ≫ cokernel.π f.hom) by
          simpa [cokernelFilteredObject] using
            (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
              (cokernel.π f.hom) n)]
    rw [hn]
    simpa using
      (Limits.imageSubobject_eq_top_of_epi
        (((⊤ : Subobject B.obj).arrow) ≫ cokernel.π f.hom))
  · rw [show (cokernelFilteredObject f).filtration m =
        imageSubobject ((B.filtration m).arrow ≫ cokernel.π f.hom) by
          simpa [cokernelFilteredObject] using
            (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
              (cokernel.π f.hom) m)]
    rw [hm]
    have hzero :
        ((⊥ : Subobject B.obj).arrow ≫ cokernel.π f.hom) = 0 := by
      simp
    rw [hzero, Limits.imageSubobject_zero]
    rfl

end FilteredObject.Hom

namespace FilteredComplex

open FilteredObject

-- Route correction: `Definition_12_24_5`, `Lemma_12_19_12`, and `Lemma_12_19_15` currently pass
-- through broken earlier filtered-object branches in this workspace. For this item we therefore
-- rebuild only the small owner API needed for `underlying`, `associatedGraded`, and finite
-- filtrations from the stable files `Definition_12_24_1` and `Definition_12_19_1`.

/-
Domain-style sampling for Lemma `13.13.8`.
- primary domain: filtered cochain complexes with finite filtrations, their associated graded
  complexes, and canonical truncation maps on the underlying cochain complex;
- sampled owner declarations in this domain:
  `FilteredComplex`,
  `FilteredComplex.HasFiniteFiltrations`,
  `FilteredComplex.associatedGraded`,
  `FilteredComplex.associatedGradedMap`,
  `FilteredComplex.underlyingMap`,
  `QuasiIso`,
  `CochainComplex.πTruncGE`,
  `CochainComplex.ιTruncLE`,
  `CochainComplex.truncGEMap`;
- best owner abstraction: the Chapter `12` owner `FilteredComplex 𝒜`, with the finite-filtration
  hypothesis `K.HasFiniteFiltrations`; the associated-graded comparison lives intrinsically on
  filtered-complex morphisms via `associatedGradedMap`, while the canonical truncations live on
  the underlying cochain complex `K.underlying`;
- primitive data: a filtered complex `K : FilteredComplex 𝒜`;
- derived API: the associated graded complex `K.associatedGraded`, the associated-graded map
  `associatedGradedMap f`, the owner-level underlying map `underlyingMap f`, and the canonical
  truncation objects/maps on `K.underlying`, `K.underlying.truncGE a`, `K.underlying.truncLE b`,
  `K.underlying.πTruncGE a`, `K.underlying.ιTruncLE b`, and
  `truncGEMap (K.underlying.ιTruncLE b) a`;
- source/core/bridge triage:
  `source-facing`: vanishing of the cohomology of `gr(K^•)` and the bounded filtered truncation
    replacements;
  `core/canonical`: `FilteredComplex`, `HasFiniteFiltrations`, `associatedGraded`,
    `associatedGradedMap`, `QuasiIso`, and the ordinary cochain-complex truncation owners on
    `K.underlying`;
  `bridge/view`: the comparison from a filtered replacement to the canonical underlying
    truncation.

This file therefore keeps the public statements on the intrinsic owner `FilteredComplex 𝒜`,
retains the finite-filtration hypothesis explicitly, and expresses filtered quasi-isomorphism data
by the canonical condition `QuasiIso (associatedGradedMap f)`. The ordinary truncation owners on
`K.underlying` remain proof-level bridge data rather than part of the public API surface. -/

/-- Helper for Lemma 13.13.8: stage maps induced by filtered morphisms preserve identities. -/
private theorem filtered_stageMap_id (A : FilteredObject 𝒜) (p : ℤ) :
    CategoryTheory.FilteredObject.Hom.stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  -- Proof comment: compare both maps after postcomposing with the mono stage inclusion.
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    rw [CategoryTheory.FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 13.13.8: stage maps induced by filtered morphisms respect composition. -/
private theorem filtered_stageMap_comp {A B D : FilteredObject 𝒜}
    (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    CategoryTheory.FilteredObject.Hom.stageMap (f ≫ g) p =
      CategoryTheory.FilteredObject.Hom.stageMap f p ≫
        CategoryTheory.FilteredObject.Hom.stageMap g p := by
  -- Proof comment: cancel the mono inclusion into the target stage and compare with the ambient
  -- composite.
  exact (cancel_mono (D.filtration.obj p).arrow).1 (by
    calc
      CategoryTheory.FilteredObject.Hom.stageMap (f ≫ g) p ≫ (D.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f ≫ g).hom := by
              rw [CategoryTheory.FilteredObject.Hom.stageMap_comm]
      _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
            simp [Category.assoc]
      _ = (CategoryTheory.FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow) ≫ g.hom := by
            rw [CategoryTheory.FilteredObject.Hom.stageMap_comm]
      _ = CategoryTheory.FilteredObject.Hom.stageMap f p ≫
            (CategoryTheory.FilteredObject.Hom.stageMap g p ≫ (D.filtration.obj p).arrow) := by
              rw [CategoryTheory.FilteredObject.Hom.stageMap_comm]
              simp [Category.assoc]
      _ = (CategoryTheory.FilteredObject.Hom.stageMap f p ≫
            CategoryTheory.FilteredObject.Hom.stageMap g p) ≫ (D.filtration.obj p).arrow := by
              simp [Category.assoc])

/-- Helper for Lemma 13.13.8: stage maps induced by filtered morphisms send zero morphisms to
zero. -/
private theorem filtered_stageMap_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    CategoryTheory.FilteredObject.Hom.stageMap (0 : A ⟶ B) p = 0 := by
  -- Proof comment: cancel the target stage inclusion and reduce to the ambient zero composite.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [CategoryTheory.FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 13.13.8: the map induced on the `p`-th graded piece by a filtered morphism.
-/
private abbrev filtered_gradedPieceMap {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (CategoryTheory.FilteredObject.Hom.stageMap f (p + 1))
    (CategoryTheory.FilteredObject.Hom.stageMap f p)
    (CategoryTheory.FilteredObject.Hom.stageInclusion_naturality f p)

/-- Helper for Lemma 13.13.8: the map on associated graded objects induced by a filtered
morphism. -/
private def filtered_associatedGradedMap {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    A.associatedGraded ⟶ B.associatedGraded :=
  fun p ↦ filtered_gradedPieceMap f p

/-- Helper for Lemma 13.13.8: graded-piece maps preserve identities. -/
private theorem filtered_gradedPieceMap_id (A : FilteredObject 𝒜) (p : ℤ) :
    filtered_gradedPieceMap (𝟙 A) p = 𝟙 (gr^{p} A) := by
  -- Proof comment: cancel the source cokernel projection and use the stage-map identity.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_gradedPieceMap, filtered_stageMap_id])

/-- Helper for Lemma 13.13.8: graded-piece maps respect composition. -/
private theorem filtered_gradedPieceMap_comp {A B D : FilteredObject 𝒜}
    (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    filtered_gradedPieceMap (f ≫ g) p =
      filtered_gradedPieceMap f p ≫ filtered_gradedPieceMap g p := by
  -- Proof comment: after cancelling the source cokernel projection, the induced maps differ only
  -- by stage-map composition.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_gradedPieceMap, filtered_stageMap_comp, Category.assoc])

/-- Helper for Lemma 13.13.8: graded-piece maps send zero morphisms to zero. -/
private theorem filtered_gradedPieceMap_zero (A B : FilteredObject 𝒜) (p : ℤ) :
    filtered_gradedPieceMap (0 : A ⟶ B) p = 0 := by
  -- Proof comment: the zero filtered morphism induces the zero square on stage quotients.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [filtered_gradedPieceMap, filtered_stageMap_zero])

/-- Helper for Lemma 13.13.8: the associated graded functor on filtered objects. -/
private def filtered_associatedGradedFunctor : FilteredObject 𝒜 ⥤ GradedObject ℤ 𝒜 where
  obj A := A.associatedGraded
  map f := filtered_associatedGradedMap f
  map_id A := by
    -- Proof comment: equality of graded morphisms is checked degreewise.
    ext p
    simpa using filtered_gradedPieceMap_id A p
  map_comp f g := by
    -- Proof comment: again, reduce to the componentwise graded-piece comparison.
    ext p
    simpa using filtered_gradedPieceMap_comp f g p

private instance :
    (filtered_associatedGradedFunctor : FilteredObject 𝒜 ⥤ GradedObject ℤ 𝒜).PreservesZeroMorphisms where
  map_zero A B := by
    ext p
    simpa using filtered_gradedPieceMap_zero A B p

/-- Helper for Lemma 13.13.8: vanishing of the associated graded cohomology below `a` gives the
ordinary `IsGE a` hypothesis for the graded complex. -/
theorem associatedGraded_isGE_of_homology_vanishesBelow
    (K : FilteredComplex 𝒜) (a : ℤ)
    (hgr : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n)) :
    K.associatedGraded.IsGE a := by
  -- Proof comment: the ordinary truncation criterion for cochain complexes only needs exactness
  -- below `a`, and `exactAt_iff_isZero_homology` turns the graded homology hypothesis into that
  -- exactness statement degreewise.
  rw [isGE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hgr n hn

/-- Helper for Lemma 13.13.8: vanishing of the associated graded cohomology above `b` gives the
ordinary `IsLE b` hypothesis for the graded complex. -/
theorem associatedGraded_isLE_of_homology_vanishesAbove
    (K : FilteredComplex 𝒜) (b : ℤ)
    (hgr : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    K.associatedGraded.IsLE b := by
  -- Proof comment: this is the dual degreewise exactness package used for the upper truncation
  -- route in the source proof.
  rw [isLE_iff]
  intro n hn
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hgr n hn

/-- Helper for Lemma 13.13.8: vanishing of the associated graded cohomology at degree `n`
identifies the degree-`n` short complex of the associated graded complex as exact. -/
theorem associatedGraded_shortComplex_exact_of_zero_homology
    (K : FilteredComplex 𝒜) (n : ℤ)
    (hzero : IsZero (K.associatedGraded.homology n)) :
    (K.associatedGraded.sc n).Exact := by
  -- Proof comment: this is exactly the canonical reformulation of vanishing homology as
  -- exactness of the degree-`n` short complex of the associated graded complex itself.
  rw [← HomologicalComplex.exactAt_iff]
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact hzero

/-- Helper for Lemma 13.13.8: a filtered object with zero underlying object has a finite
filtration. -/
private theorem filteredObject_isFinite_of_isZero (A : FilteredObject 𝒜) (hA : IsZero A.obj) :
    A.IsFinite := by
  -- Proof comment: every subobject of a zero object is equal, so every stage is simultaneously
  -- top and bottom.
  let _ : Subsingleton (Subobject A.obj) := Subobject.subsingleton_of_isZero hA
  refine ⟨0, 0, ?_, ?_⟩
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

/-- Helper for Lemma 13.13.8: a term below a strict lower bound has a finite filtration because
its underlying object is zero. -/
private theorem term_isFinite_of_underlying_isStrictlyGE
    (K : FilteredComplex 𝒜) (a n : ℤ) (hK : K.underlying.IsStrictlyGE a) (hn : n < a) :
    (K.X n).IsFinite := by
  -- Proof comment: rewrite the strict-support hypothesis as degreewise vanishing on the
  -- underlying complex and apply the previous zero-object finiteness lemma.
  rw [isStrictlyGE_iff] at hK
  exact filteredObject_isFinite_of_isZero (A := K.X n) (by
    simpa [underlying] using hK n hn)

/-- Helper for Lemma 13.13.8: a term above a strict upper bound has a finite filtration because
its underlying object is zero. -/
private theorem term_isFinite_of_underlying_isStrictlyLE
    (K : FilteredComplex 𝒜) (b n : ℤ) (hK : K.underlying.IsStrictlyLE b) (hn : b < n) :
    (K.X n).IsFinite := by
  -- Proof comment: the dual strict-support hypothesis again turns the underlying term into a
  -- zero object, and zero filtered objects have finite filtrations.
  rw [isStrictlyLE_iff] at hK
  exact filteredObject_isFinite_of_isZero (A := K.X n) (by
    simpa [underlying] using hK n hn)

-- The next block freezes the degreewise lower-truncation API for the current proof attempt.
/-- Helper for Lemma 13.13.8: the degree-`n` term of the lower filtered truncation. -/
private noncomputable def lower_filtered_truncation_obj
    (K : FilteredComplex 𝒜) (a n : ℤ) : FilteredObject 𝒜 :=
  if _ : n < a then
    0
  else if _ : n = a then
    FilteredObject.Hom.cokernelFilteredObject (K.d (a - 1) a)
  else
    K.X n

/-- Helper for Lemma 13.13.8: below the cutoff, the lower truncation term is zero. -/
private theorem lower_filtered_truncation_obj_eq_zero_of_lt
    (K : FilteredComplex 𝒜) (a n : ℤ) (hn : n < a) :
    lower_filtered_truncation_obj K a n = 0 := by
  -- Proof comment: the degree lies strictly below the cutoff, so the explicit owner takes the
  -- zero branch by definition.
  simp [lower_filtered_truncation_obj, hn]

/-- Helper for Lemma 13.13.8: at the cutoff, the lower truncation term is the filtered cokernel.
-/
private theorem lower_filtered_truncation_obj_eq_cokernel
    (K : FilteredComplex 𝒜) (a : ℤ) :
    lower_filtered_truncation_obj K a a =
      FilteredObject.Hom.cokernelFilteredObject (K.d (a - 1) a) := by
  -- Proof comment: at the cutoff itself, the first branch is impossible and the second branch is
  -- exactly the filtered cokernel owner.
  simp [lower_filtered_truncation_obj]

/-- Helper for Lemma 13.13.8: rewriting the lower cutoff term after specializing a degree to the
cutoff. -/
private theorem lower_filtered_truncation_obj_eq_cokernel_of_eq
    (K : FilteredComplex 𝒜) (a n : ℤ) (hna : n = a) :
    lower_filtered_truncation_obj K a n =
      FilteredObject.Hom.cokernelFilteredObject (K.d (a - 1) a) := by
  -- Proof comment: substitute the specialized degree into the cutoff formula already proved at
  -- degree `a`.
  subst n
  exact lower_filtered_truncation_obj_eq_cokernel K a

/-- Helper for Lemma 13.13.8: above the cutoff, the lower truncation keeps the original term. -/
private theorem lower_filtered_truncation_obj_eq_self_of_lt
    (K : FilteredComplex 𝒜) (a n : ℤ) (han : a < n) :
    lower_filtered_truncation_obj K a n = K.X n := by
  -- Proof comment: above the cutoff both special branches are excluded, so the explicit owner
  -- keeps the original degree term of `K`.
  have hna : n ≠ a := by omega
  simp [lower_filtered_truncation_obj, hna, not_lt.mpr (le_of_lt han)]

/-- Helper for Lemma 13.13.8: the target of a cochain differential leaving the cutoff lies above
the cutoff. -/
private theorem cutoff_lt_target_of_rel_source_eq_cutoff
    (a i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hia : i = a) :
    a < j := by
  -- Proof comment: along `ComplexShape.up`, the target is the successor of the source degree.
  subst i
  change a + 1 = j at hij
  omega

/-- Helper for Lemma 13.13.8: the target of a cochain differential from a degree above the cutoff
also lies above the cutoff. -/
private theorem cutoff_lt_target_of_rel_source_gt_cutoff
    (a i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hai : a < i) :
    a < j := by
  -- Proof comment: the relation `i + 1 = j` preserves the strict inequality `a < i`.
  change i + 1 = j at hij
  omega

/-- Helper for Lemma 13.13.8: the cutoff outgoing differential already satisfies the square-zero
relation before passing to the filtered cokernel. -/
private theorem lower_filtered_truncation_cutoff_comp_zero
    (K : FilteredComplex 𝒜) (a j : ℤ) :
    K.d (a - 1) a ≫ K.d a j = 0 := by
  -- Proof comment: this is the ordinary square-zero relation of the ambient complex `K`.
  simpa using K.d_comp_d (a - 1) a j

/-- Helper for Lemma 13.13.8: the differential of the lower filtered truncation. -/
private noncomputable def lower_filtered_truncation_d
    (K : FilteredComplex 𝒜) (a i j : ℤ) :
    lower_filtered_truncation_obj K a i ⟶ lower_filtered_truncation_obj K a j :=
  if hij : (ComplexShape.up ℤ).Rel i j then
    if hia : i = a then
      eqToHom (lower_filtered_truncation_obj_eq_cokernel_of_eq K a i hia) ≫
        FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (K.d a j)
          (lower_filtered_truncation_cutoff_comp_zero K a j) ≫
        eqToHom
          (lower_filtered_truncation_obj_eq_self_of_lt K a j
            (cutoff_lt_target_of_rel_source_eq_cutoff a i j hij hia)).symm
    else if hai : a < i then
      eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a i hai) ≫
        K.d i j ≫
        eqToHom
          (lower_filtered_truncation_obj_eq_self_of_lt K a j
            (cutoff_lt_target_of_rel_source_gt_cutoff a i j hij hai)).symm
    else
      0
  else
    0

/-- Helper for Lemma 13.13.8: the lower-truncation differential vanishes off the cochain shape.
-/
private theorem lower_filtered_truncation_shape
    (K : FilteredComplex 𝒜) (a i j : ℤ)
    (hij : ¬ (ComplexShape.up ℤ).Rel i j) :
    lower_filtered_truncation_d K a i j = 0 := by
  -- Proof comment: the explicit differential is defined to be zero away from the cochain shape.
  rw [lower_filtered_truncation_d, dif_neg hij]

/-- Helper for Lemma 13.13.8: the lower-truncation differential squares to zero. -/
private theorem lower_filtered_truncation_d_comp_d
    (K : FilteredComplex 𝒜) (a i j k : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    lower_filtered_truncation_d K a i j ≫ lower_filtered_truncation_d K a j k = 0 := by
  -- TODO: the remaining constructor-level blocker is the cutoff composition at `i = a`, where
  -- one must compare `descToCokernel` with the inherited differential through an owner-stable
  -- epi-cancellation bridge for `FilteredObject.Hom.toCokernel`; the below-cutoff and
  -- above-cutoff branches are already stabilized by the explicit differential formula.
  sorry

/-- Helper for Lemma 13.13.8: the source-faithful lower filtered truncation of `K` at degree
`a`, whose associated graded should model the ordinary truncation `τ_{\ge a}(gr(K))`. -/
noncomputable def lower_filtered_truncation (K : FilteredComplex 𝒜) (a : ℤ) :
    FilteredComplex 𝒜 where
  X := lower_filtered_truncation_obj K a
  d := lower_filtered_truncation_d K a
  shape := lower_filtered_truncation_shape K a
  d_comp_d' := lower_filtered_truncation_d_comp_d K a

-- The next block freezes the degreewise lower-truncation projection API for the current attempt.
/-- Helper for Lemma 13.13.8: the degreewise component of the lower-truncation projection. -/
private noncomputable def lower_filtered_truncation_pi_f
    (K : FilteredComplex 𝒜) (a n : ℤ) :
    K.X n ⟶ lower_filtered_truncation_obj K a n :=
  if hn : n < a then
    0
  else if hna : n = a then
    eqToHom (congrArg (fun m : ℤ ↦ K.X m) hna) ≫
      FilteredObject.Hom.toCokernel (K.d (a - 1) a) ≫
      eqToHom (lower_filtered_truncation_obj_eq_cokernel_of_eq K a n hna).symm
  else if han : a < n then
    eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a n han).symm
  else
    0

/-- Helper for Lemma 13.13.8: the lower-truncation projection is a chain map. -/
private theorem lower_filtered_truncation_pi_comm
    (K : FilteredComplex 𝒜) (a i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    lower_filtered_truncation_pi_f K a i ≫ lower_filtered_truncation_d K a i j =
      K.d i j ≫ lower_filtered_truncation_pi_f K a j := by
  -- TODO: the structural cutoff cases are `i = a - 1` and `i = a`; they should be closed by
  -- `comp_toCokernel` and `toCokernel_descToCokernel`, while all other cases are inherited from
  -- identities or zero maps.
  sorry

/-- Helper for Lemma 13.13.8: the canonical map from `K` to its lower filtered truncation. -/
noncomputable def lower_filtered_truncation_pi (K : FilteredComplex 𝒜) (a : ℤ) :
    K ⟶ lower_filtered_truncation K a where
  f := lower_filtered_truncation_pi_f K a
  comm' := lower_filtered_truncation_pi_comm K a

/-- Helper for Lemma 13.13.8: the lower filtered truncation inherits finite filtrations from `K`.
-/
theorem lower_filtered_truncation_hasFiniteFiltrations
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (a : ℤ) :
    (lower_filtered_truncation K a).HasFiniteFiltrations := by
  -- Proof comment: degreewise the lower truncation is either zero, the cutoff cokernel, or the
  -- original term, so the finite-filtration claim follows from those three explicit branches.
  intro n
  by_cases hn : n < a
  · rw [show (lower_filtered_truncation K a).X n = lower_filtered_truncation_obj K a n by rfl]
    rw [lower_filtered_truncation_obj_eq_zero_of_lt K a n hn]
    simpa using
      filteredObject_isFinite_of_isZero (A := (0 : FilteredObject 𝒜))
        (Functor.map_isZero FilteredObject.forget (isZero_zero (FilteredObject 𝒜)))
  · by_cases han : a < n
    · rw [show (lower_filtered_truncation K a).X n = lower_filtered_truncation_obj K a n by rfl]
      rw [lower_filtered_truncation_obj_eq_self_of_lt K a n han]
      exact hKfin n
    · have hna : n = a := by omega
      rw [show (lower_filtered_truncation K a).X n = lower_filtered_truncation_obj K a n by rfl]
      rw [hna, lower_filtered_truncation_obj_eq_cokernel]
      exact FilteredObject.Hom.finite_cokernelFilteredObject_isFinite
        (K.d (a - 1) a) (hKfin a)

/-- Helper for Lemma 13.13.8: exactness of `gr(K)` below `a` makes the lower-truncation map a
filtered quasi-isomorphism. -/
theorem quasiIso_associatedGradedMap_lower_filtered_truncation_pi
    (K : FilteredComplex 𝒜) (a : ℤ)
    (hgr : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n)) :
    QuasiIso (associatedGradedMap (lower_filtered_truncation_pi K a)) := by
  -- TODO: compare `gr(lower_filtered_truncation K a)` with `K.associatedGraded.truncGE a`, using
  -- exactness of the degree-`a - 1` row to identify the cutoff cokernel term.
  sorry

/-- Helper for Lemma 13.13.8: the lower filtered truncation is bounded below by `a` on the
underlying cochain complex. -/
theorem lower_filtered_truncation_isStrictlyGE
    (K : FilteredComplex 𝒜) (a : ℤ) :
    (lower_filtered_truncation K a).underlying.IsStrictlyGE a := by
  -- Route correction: the generic `truncGE` API on homological complexes cannot be used here,
  -- because `Fil(𝒜)` does not carry the needed homology package in this dependency closure.
  -- Proof comment: below the cutoff the explicit lower truncation literally has zero filtered
  -- objects, hence its underlying complex is zero in those degrees.
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  change IsZero ((lower_filtered_truncation_obj K a n).obj)
  rw [lower_filtered_truncation_obj_eq_zero_of_lt K a n hn]
  simpa using Functor.map_isZero FilteredObject.forget (isZero_zero (FilteredObject 𝒜))

-- The next block freezes the degreewise upper-truncation API for the current proof attempt.
/-- Helper for Lemma 13.13.8: the degree-`n` term of the upper filtered truncation. -/
private noncomputable def upper_filtered_truncation_obj
    (K : FilteredComplex 𝒜) (b n : ℤ) : FilteredObject 𝒜 :=
  if _ : n < b then
    K.X n
  else if _ : n = b then
    FilteredObject.Hom.kernelFilteredObject (K.d b (b + 1))
  else
    0

/-- Helper for Lemma 13.13.8: below the cutoff, the upper truncation keeps the original term. -/
private theorem upper_filtered_truncation_obj_eq_self_of_lt
    (K : FilteredComplex 𝒜) (b n : ℤ) (hnb : n < b) :
    upper_filtered_truncation_obj K b n = K.X n := by
  -- Proof comment: below the cutoff the upper truncation keeps the original term by definition.
  simp [upper_filtered_truncation_obj, hnb]

/-- Helper for Lemma 13.13.8: at the cutoff, the upper truncation term is the filtered kernel. -/
private theorem upper_filtered_truncation_obj_eq_kernel
    (K : FilteredComplex 𝒜) (b : ℤ) :
    upper_filtered_truncation_obj K b b =
      FilteredObject.Hom.kernelFilteredObject (K.d b (b + 1)) := by
  -- Proof comment: at the cutoff the lower branch is impossible and the middle branch is the
  -- filtered kernel owner.
  simp [upper_filtered_truncation_obj]

/-- Helper for Lemma 13.13.8: rewriting the upper cutoff term after specializing a degree to the
cutoff. -/
private theorem upper_filtered_truncation_obj_eq_kernel_of_eq
    (K : FilteredComplex 𝒜) (b n : ℤ) (hnb : n = b) :
    upper_filtered_truncation_obj K b n =
      FilteredObject.Hom.kernelFilteredObject (K.d b (b + 1)) := by
  -- Proof comment: substitute the specialized degree into the cutoff formula already proved at
  -- degree `b`.
  subst n
  exact upper_filtered_truncation_obj_eq_kernel K b

/-- Helper for Lemma 13.13.8: above the cutoff, the upper truncation term is zero. -/
private theorem upper_filtered_truncation_obj_eq_zero_of_lt
    (K : FilteredComplex 𝒜) (b n : ℤ) (hbn : b < n) :
    upper_filtered_truncation_obj K b n = 0 := by
  -- Proof comment: above the cutoff the explicit upper truncation lands in the zero branch.
  have hnb : n ≠ b := by omega
  simp [upper_filtered_truncation_obj, hnb, not_lt.mpr (le_of_lt hbn)]

/-- Helper for Lemma 13.13.8: the source of a cochain differential entering the cutoff lies below
the cutoff. -/
private theorem source_lt_cutoff_of_rel_target_eq_cutoff
    (b i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hjb : j = b) :
    i < b := by
  -- Proof comment: along `ComplexShape.up`, the source is one less than the target degree.
  have hrel : i + 1 = b := by
    simpa [ComplexShape.up, hjb] using hij
  omega

/-- Helper for Lemma 13.13.8: if the target of a cochain differential is below the cutoff, then
the source is also below the cutoff. -/
private theorem source_lt_cutoff_of_rel_target_lt_cutoff
    (b i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) (hjb : j < b) :
    i < b := by
  -- Proof comment: the relation `i + 1 = j` forces `i < j`, hence also `i < b`.
  change i + 1 = j at hij
  omega

/-- Helper for Lemma 13.13.8: the cutoff incoming differential already satisfies the square-zero
relation before passing to the filtered kernel. -/
private theorem upper_filtered_truncation_cutoff_comp_zero
    (K : FilteredComplex 𝒜) (i b : ℤ) :
    K.d i b ≫ K.d b (b + 1) = 0 := by
  -- Proof comment: this is again the ordinary square-zero relation in the ambient complex `K`.
  simpa using K.d_comp_d i b (b + 1)

/-- Helper for Lemma 13.13.8: the differential of the upper filtered truncation. -/
private noncomputable def upper_filtered_truncation_d
    (K : FilteredComplex 𝒜) (b i j : ℤ) :
    upper_filtered_truncation_obj K b i ⟶ upper_filtered_truncation_obj K b j :=
  if hij : (ComplexShape.up ℤ).Rel i j then
    if hjb : j = b then
      eqToHom
          (upper_filtered_truncation_obj_eq_self_of_lt K b i
            (source_lt_cutoff_of_rel_target_eq_cutoff b i j hij hjb)) ≫
        FilteredObject.Hom.liftToKernel (K.d b (b + 1)) (K.d i b)
          (upper_filtered_truncation_cutoff_comp_zero K i b) ≫
        eqToHom (upper_filtered_truncation_obj_eq_kernel_of_eq K b j hjb).symm
    else if hjlt : j < b then
      eqToHom
          (upper_filtered_truncation_obj_eq_self_of_lt K b i
            (source_lt_cutoff_of_rel_target_lt_cutoff b i j hij hjlt)) ≫
        K.d i j ≫
        eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b j hjlt).symm
    else
      0
  else
    0

/-- Helper for Lemma 13.13.8: the upper-truncation differential vanishes off the cochain shape. -/
private theorem upper_filtered_truncation_shape
    (K : FilteredComplex 𝒜) (b i j : ℤ)
    (hij : ¬ (ComplexShape.up ℤ).Rel i j) :
    upper_filtered_truncation_d K b i j = 0 := by
  -- Proof comment: the explicit differential is again zero by definition off the cochain shape.
  rw [upper_filtered_truncation_d, dif_neg hij]

/-- Helper for Lemma 13.13.8: the upper-truncation differential squares to zero. -/
private theorem upper_filtered_truncation_d_comp_d
    (K : FilteredComplex 𝒜) (b i j k : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    upper_filtered_truncation_d K b i j ≫ upper_filtered_truncation_d K b j k = 0 := by
  -- TODO: the stable branches are clear from the explicit formula: for `j < b` both maps are
  -- inherited from `K`, while for `j = b` the second map is definitionally zero. What remains is
  -- to package those arithmetic splits into a short proof without reintroducing transport noise.
  sorry

/-- Helper for Lemma 13.13.8: the source-faithful upper filtered truncation of `K` at degree
`b`, whose associated graded should model the ordinary truncation `τ_{\le b}(gr(K))`. -/
noncomputable def upper_filtered_truncation (K : FilteredComplex 𝒜) (b : ℤ) :
    FilteredComplex 𝒜 where
  X := upper_filtered_truncation_obj K b
  d := upper_filtered_truncation_d K b
  shape := upper_filtered_truncation_shape K b
  d_comp_d' := upper_filtered_truncation_d_comp_d K b

-- The next block freezes the degreewise upper-truncation inclusion API for the current attempt.
/-- Helper for Lemma 13.13.8: the degreewise component of the upper-truncation inclusion. -/
private noncomputable def upper_filtered_truncation_iota_f
    (K : FilteredComplex 𝒜) (b n : ℤ) :
    upper_filtered_truncation_obj K b n ⟶ K.X n :=
  if hnb : n < b then
    eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b n hnb)
  else if hbn : n = b then
    eqToHom (upper_filtered_truncation_obj_eq_kernel_of_eq K b n hbn) ≫
      FilteredObject.Hom.kernelι (K.d b (b + 1)) ≫
      eqToHom (congrArg (fun m : ℤ ↦ K.X m) hbn).symm
  else if _ : b < n then
    0
  else
    0

/-- Helper for Lemma 13.13.8: the upper-truncation inclusion is a chain map. -/
private theorem upper_filtered_truncation_iota_comm
    (K : FilteredComplex 𝒜) (b i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    upper_filtered_truncation_iota_f K b i ≫ K.d i j =
      upper_filtered_truncation_d K b i j ≫ upper_filtered_truncation_iota_f K b j := by
  -- TODO: the structural cutoff cases are `j = b` and `i = b`; they should be closed by
  -- `liftToKernel_kernelι` and `kernelι_comp`, while all other cases are inherited from
  -- identities or zero maps.
  sorry

/-- Helper for Lemma 13.13.8: the canonical inclusion of the upper filtered truncation into `K`.
-/
noncomputable def upper_filtered_truncation_iota (K : FilteredComplex 𝒜) (b : ℤ) :
    upper_filtered_truncation K b ⟶ K where
  f := upper_filtered_truncation_iota_f K b
  comm' := upper_filtered_truncation_iota_comm K b

/-- Helper for Lemma 13.13.8: the upper filtered truncation inherits finite filtrations from `K`.
-/
theorem upper_filtered_truncation_hasFiniteFiltrations
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (b : ℤ) :
    (upper_filtered_truncation K b).HasFiniteFiltrations := by
  -- Proof comment: degreewise the upper truncation is either the original term, the cutoff
  -- kernel, or zero, so finiteness is immediate from the explicit owner formulas.
  intro n
  by_cases hnb : n < b
  · rw [show (upper_filtered_truncation K b).X n = upper_filtered_truncation_obj K b n by rfl]
    rw [upper_filtered_truncation_obj_eq_self_of_lt K b n hnb]
    exact hKfin n
  · by_cases hbn : b < n
    · rw [show (upper_filtered_truncation K b).X n = upper_filtered_truncation_obj K b n by rfl]
      rw [upper_filtered_truncation_obj_eq_zero_of_lt K b n hbn]
      simpa using
        filteredObject_isFinite_of_isZero (A := (0 : FilteredObject 𝒜))
          (Functor.map_isZero FilteredObject.forget (isZero_zero (FilteredObject 𝒜)))
    · have hn_eq : n = b := by omega
      rw [show (upper_filtered_truncation K b).X n = upper_filtered_truncation_obj K b n by rfl]
      rw [hn_eq, upper_filtered_truncation_obj_eq_kernel]
      exact FilteredObject.Hom.finite_kernelFilteredObject_isFinite
        (K.d b (b + 1)) (hKfin b)

/-- Helper for Lemma 13.13.8: exactness of `gr(K)` above `b` makes the upper-truncation map a
filtered quasi-isomorphism. -/
theorem quasiIso_associatedGradedMap_upper_filtered_truncation_iota
    (K : FilteredComplex 𝒜) (b : ℤ)
    (hgr : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    QuasiIso (associatedGradedMap (upper_filtered_truncation_iota K b)) := by
  -- TODO: compare `gr(upper_filtered_truncation K b)` with `K.associatedGraded.truncLE b`, using
  -- exactness of the degree-`b` row to identify the cutoff kernel term.
  sorry

/-- Helper for Lemma 13.13.8: the upper filtered truncation is bounded above by `b` on the
underlying cochain complex. -/
theorem upper_filtered_truncation_isStrictlyLE
    (K : FilteredComplex 𝒜) (b : ℤ) :
    (upper_filtered_truncation K b).underlying.IsStrictlyLE b := by
  -- Route correction: the generic `truncLE` API has the same filtered-homology obstruction as
  -- `truncGE` in this file, so the support proof must wait for the explicit upper truncation.
  -- Proof comment: above the cutoff the explicit upper truncation literally has zero filtered
  -- objects, so its underlying complex vanishes there.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  change IsZero ((upper_filtered_truncation_obj K b n).obj)
  rw [upper_filtered_truncation_obj_eq_zero_of_lt K b n hn]
  simpa using Functor.map_isZero FilteredObject.forget (isZero_zero (FilteredObject 𝒜))

/-- Helper for Lemma 13.13.8: after fixing a bounded-above replacement `g : M ⟶ K` and a
bounded-below replacement `f : K ⟶ L`, the remaining square is obtained by lower-truncating `M`
and comparing it functorially with `L`. -/
theorem exists_bounded_square_of_filtered_replacements
    {K L M : FilteredComplex 𝒜} (hMfin : M.HasFiniteFiltrations) (a b : ℤ)
    (f : K ⟶ L) (g : M ⟶ K)
    (hf : QuasiIso (associatedGradedMap f))
    (hg : QuasiIso (associatedGradedMap g))
    (hL : L.underlying.IsStrictlyGE a)
    (hM : M.underlying.IsStrictlyLE b) :
    ∃ (N : FilteredComplex 𝒜) (_ : N.HasFiniteFiltrations)
      (u : M ⟶ N) (v : N ⟶ L),
      QuasiIso (associatedGradedMap u) ∧
        QuasiIso (associatedGradedMap v) ∧
        CommSq u g v f ∧
        N.underlying.IsStrictlyGE a ∧
        N.underlying.IsStrictlyLE b := by
  -- TODO: define the functorial lower truncation on `M`, use it for `u : M ⟶ N`, and construct
  -- `v : N ⟶ L` from the naturality square of lower truncation applied to `f ≫ g`.
  sorry

/-- Lemma 13.13.8 (1): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology in all degrees `< a`, then there exists a filtered
quasi-isomorphism from `K` to a filtered complex whose underlying complex is bounded below by
`a`. -/
theorem exists_filteredQuasiIso_to_boundedBelow_of_associatedGradedCohomologyVanishesBelow
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (a : ℤ)
    (hgr : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n)) :
    ∃ (L : FilteredComplex 𝒜) (_ : L.HasFiniteFiltrations) (f : K ⟶ L),
      QuasiIso (associatedGradedMap f) ∧ L.underlying.IsStrictlyGE a := by
  -- Proof comment: package the explicit lower filtered truncation promised by the source proof.
  refine ⟨lower_filtered_truncation K a,
    lower_filtered_truncation_hasFiniteFiltrations K hKfin a,
    lower_filtered_truncation_pi K a, ?_⟩
  -- Proof comment: the remaining two properties are exactly the graded quasi-isomorphism and the
  -- lower-support bound supplied by the truncation package.
  exact ⟨quasiIso_associatedGradedMap_lower_filtered_truncation_pi K a hgr,
    lower_filtered_truncation_isStrictlyGE K a⟩

/-- Lemma 13.13.8 (2): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology in all degrees `> b`, then there exists a filtered
quasi-isomorphism to `K` from a filtered complex whose underlying complex is bounded above by
`b`. -/
theorem exists_filteredQuasiIso_from_boundedAbove_of_associatedGradedCohomologyVanishesAbove
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations) (b : ℤ)
    (hgr : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ (M : FilteredComplex 𝒜) (_ : M.HasFiniteFiltrations) (g : M ⟶ K),
      QuasiIso (associatedGradedMap g) ∧ M.underlying.IsStrictlyLE b := by
  -- Proof comment: package the dual upper filtered truncation promised by the source proof.
  refine ⟨upper_filtered_truncation K b,
    upper_filtered_truncation_hasFiniteFiltrations K hKfin b,
    upper_filtered_truncation_iota K b, ?_⟩
  -- Proof comment: the upper-truncation package supplies both the graded quasi-isomorphism and
  -- the upper-support bound.
  exact ⟨quasiIso_associatedGradedMap_upper_filtered_truncation_iota K b hgr,
    upper_filtered_truncation_isStrictlyLE K b⟩

/-- Lemma 13.13.8 (3): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology for `|n| ≫ 0`, then there exists a commutative square of filtered
quasi-isomorphisms
`K ⟶ L`, `M ⟶ K`, `M ⟶ N`, `N ⟶ L`
with `L` bounded below, `M` bounded above, and `N` bounded. -/
theorem exists_filteredQuasiIso_square_with_boundedRepresentatives_of_associatedGradedCohomologyEventuallyVanishes
    (K : FilteredComplex 𝒜) (hKfin : K.HasFiniteFiltrations)
    (hgr : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.associatedGraded.homology n)) :
    ∃ a b : ℤ,
      ∃ (L : FilteredComplex 𝒜) (_ : L.HasFiniteFiltrations) (f : K ⟶ L)
        (M : FilteredComplex 𝒜) (_ : M.HasFiniteFiltrations) (g : M ⟶ K)
        (N : FilteredComplex 𝒜) (_ : N.HasFiniteFiltrations)
        (u : M ⟶ N) (v : N ⟶ L),
        QuasiIso (associatedGradedMap f) ∧
          QuasiIso (associatedGradedMap g) ∧
          QuasiIso (associatedGradedMap u) ∧
          QuasiIso (associatedGradedMap v) ∧
          CommSq u g v f ∧
          L.underlying.IsStrictlyGE a ∧
          M.underlying.IsStrictlyLE b ∧
          N.underlying.IsStrictlyGE a ∧
          N.underlying.IsStrictlyLE b := by
  -- Proof comment: first extract explicit lower and upper vanishing bounds from the eventual
  -- graded-homology hypothesis.
  rcases hgr with ⟨a, b, hgr⟩
  have hBelow : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n) := by
    intro n hn
    exact hgr n (Or.inl hn)
  have hAbove : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n) := by
    intro n hn
    exact hgr n (Or.inr hn)
  -- Proof comment: apply clauses `(1)` and `(2)` to get the bounded-below and bounded-above
  -- filtered replacements of `K`.
  obtain ⟨L, hLfin, f, hf, hL⟩ :=
    exists_filteredQuasiIso_to_boundedBelow_of_associatedGradedCohomologyVanishesBelow
      K hKfin a hBelow
  obtain ⟨M, hMfin, g, hg, hM⟩ :=
    exists_filteredQuasiIso_from_boundedAbove_of_associatedGradedCohomologyVanishesAbove
      K hKfin b hAbove
  -- Proof comment: the remaining formal square is isolated in a single helper whose proof should
  -- use the functorial lower truncation applied to the bounded-above replacement `M`.
  obtain ⟨N, hNfin, u, v, hu, hv, hsq, hNGE, hNLE⟩ :=
    exists_bounded_square_of_filtered_replacements
      (K := K) (L := L) (M := M) hMfin a b f g hf hg hL hM
  exact ⟨a, b, L, hLfin, f, M, hMfin, g, N, hNfin, u, v,
    hf, hg, hu, hv, hsq, hL, hM, hNGE, hNLE⟩

end FilteredComplex

end CategoryTheory
