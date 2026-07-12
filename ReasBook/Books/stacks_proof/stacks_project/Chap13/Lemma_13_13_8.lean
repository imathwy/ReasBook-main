import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import StacksProject_2024.Chap12.Lemma_12_16_2
import StacksProject_2024.Chap12.Definition_12_19_1
import StacksProject_2024.Chap12.Definition_12_19_3
import StacksProject_2024.Chap12.Definition_12_24_1
import StacksProject_2024.Chap13.Lemma_13_11_5

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


/-- Helper for Lemma 13.13.8: the filtered kernel cutoff term attached to a filtered morphism. -/
abbrev kernelFilteredObject {A B : FilteredObject 𝒜} (f : A ⟶ B) : FilteredObject 𝒜 :=
  inducedSubobjectFilteredObject A (kernelSubobject f.hom)

/-- Helper for Lemma 13.13.8: the canonical filtered inclusion of the kernel cutoff term. -/
abbrev kernelι {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    kernelFilteredObject f ⟶ A :=
  inducedSubobjectInclusion A (kernelSubobject f.hom)

/-- Helper for Lemma 13.13.8: the kernel cutoff inclusion followed by the original morphism is
zero. -/
theorem kernelι_comp {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    kernelι f ≫ f = 0 := by
  -- Proof comment: the filtered statement is checked on the ambient arrow, where this is exactly
  -- the kernel relation.
  apply FilteredObject.forget.map_injective
  change (kernelSubobject f.hom).arrow ≫ f.hom = 0
  simpa [kernelι] using kernelSubobject_arrow_comp f.hom

/-- Helper for Lemma 13.13.8: the filtered cokernel cutoff term attached to a filtered morphism.
-/
abbrev cokernelFilteredObject {A B : FilteredObject 𝒜} (f : A ⟶ B) : FilteredObject 𝒜 :=
  quotientFilteredObject B (imageSubobject f.hom)

/-- Helper for Lemma 13.13.8: the canonical filtered quotient map to the cokernel cutoff term. -/
abbrev toCokernel {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    B ⟶ cokernelFilteredObject f :=
  toFilteredQuotient B (imageSubobject f.hom)

/-- Helper for Lemma 13.13.8: the original morphism followed by the cokernel cutoff projection is
zero. -/
theorem comp_toCokernel {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    f ≫ toCokernel f = 0 := by
  -- Proof comment: forgetting to the ambient category reduces the statement to the owner-stable
  -- image-to-cokernel zero composite proved just above.
  apply FilteredObject.forget.map_injective
  change f.hom ≫ cokernel.π (imageSubobject f.hom).arrow = 0
  simpa [toCokernel, toFilteredQuotient] using
    imageSubobject_comp_cokernelPi_eq_zero f.hom

/-- Helper for Lemma 13.13.8: a filtered morphism out of the cokernel cutoff term induced by a
vanishing composite. -/
noncomputable def descToCokernel {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) :
    cokernelFilteredObject f ⟶ C where
  hom := cokernel.desc (imageSubobject f.hom).arrow g.hom <| by
    -- Proof comment: compose with the epimorphic image factor of `f.hom` and cancel it to reduce
    -- the claim to the given zero composite `f ≫ g = 0`.
    apply (cancel_epi (factorThruImageSubobject f.hom)).1
    simpa [Category.assoc, imageSubobject_arrow_comp] using
      congrArg FilteredObject.Hom.hom hfg
  preserves := by
    intro i
    let q : (B.filtration i : 𝒜) ⟶ cokernel (imageSubobject f.hom).arrow :=
      (B.filtration.obj i).arrow ≫ cokernel.π (imageSubobject f.hom).arrow
    let δ : cokernel (imageSubobject f.hom).arrow ⟶ C.obj :=
      cokernel.desc (imageSubobject f.hom).arrow g.hom (by
        apply (cancel_epi (factorThruImageSubobject f.hom)).1
        simpa [Category.assoc, imageSubobject_arrow_comp] using
          congrArg FilteredObject.Hom.hom hfg)
    have hstage :
        (cokernelFilteredObject f).filtration i = imageSubobject q := by
      -- Proof comment: the quotient stage is by definition the image of the stage composite into
      -- the ambient cokernel cutoff object.
      simpa [cokernelFilteredObject, quotientFilteredObject, q] using
        (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
          (cokernel.π (imageSubobject f.hom).arrow) i)
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
  simpa [descToCokernel, toCokernel, toFilteredQuotient] using
    cokernel.π_desc (imageSubobject f.hom).arrow g.hom (by
      apply (cancel_epi (factorThruImageSubobject f.hom)).1
      simpa [Category.assoc, imageSubobject_arrow_comp] using
        congrArg FilteredObject.Hom.hom hfg)

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
        imageSubobject ((B.filtration n).arrow ≫ cokernel.π (imageSubobject f.hom).arrow) by
          simpa [cokernelFilteredObject, quotientFilteredObject] using
            (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
              (cokernel.π (imageSubobject f.hom).arrow) n)]
    rw [hn]
    simpa using
      (Limits.imageSubobject_eq_top_of_epi
        (((⊤ : Subobject B.obj).arrow) ≫ cokernel.π (imageSubobject f.hom).arrow))
  · rw [show (cokernelFilteredObject f).filtration m =
        imageSubobject ((B.filtration m).arrow ≫ cokernel.π (imageSubobject f.hom).arrow) by
          simpa [cokernelFilteredObject, quotientFilteredObject] using
            (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
              (cokernel.π (imageSubobject f.hom).arrow) m)]
    rw [hm]
    have hzero :
        ((⊥ : Subobject B.obj).arrow ≫ cokernel.π (imageSubobject f.hom).arrow) = 0 := by
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

/-- Helper for Chap13 Lemma 13 13 8: the associated-graded map induced by a filtered identity
transport is an isomorphism on every graded piece. -/
private theorem filtered_gradedPieceMap_eqToHom_isIso
    {A B : FilteredObject 𝒜} (h : A = B) (p : ℤ) :
    IsIso (filtered_gradedPieceMap (eqToHom h) p) := by
  -- Proof comment: after substituting the equality of filtered objects, the induced graded-piece
  -- map is literally the identity.
  subst h
  simpa [filtered_gradedPieceMap_id] using (inferInstance : IsIso (𝟙 (gr^{p} A)))

/-- Helper for Chap13 Lemma 13 13 8: every stage map of the filtered cokernel projection is epic.
-/
private theorem stage_toCokernel_epi
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    Epi (CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.toCokernel f) p) := by
  -- TODO: normalize the quotient filtration stage to the literal image subobject owner, then
  -- identify the stage map with `factorThruImageSubobject` by a directed owner-side rewrite.
  sorry

/-- Helper for Chap13 Lemma 13 13 8: the induced map on the `p`-th graded piece of a filtered
cokernel projection is epic. -/
private theorem gradedPiece_toCokernel_epi
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    Epi (filtered_gradedPieceMap (FilteredObject.Hom.toCokernel f) p) := by
  -- TODO: once `stage_toCokernel_epi` is available in the literal image-subobject owner, derive
  -- this from the defining `cokernel.map` factorization by `epi_of_epi_fac`.
  sorry

/-- Helper for Chap13 Lemma 13 13 8: the stage map of the filtered kernel inclusion is the
canonical pullback projection onto the ambient stage. -/
private theorem stage_kernelι_eq_pullbackπ
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) p =
      Subobject.pullbackπ (kernelSubobject f.hom).arrow (A.filtration.obj p) := by
  -- Proof comment: both arrows are characterized by the pullback square defining the induced
  -- filtration on the kernel subobject.
  refine (cancel_mono (A.filtration.obj p).arrow).1 ?_
  calc
    CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) p ≫
        (A.filtration.obj p).arrow
        = ((FilteredObject.Hom.kernelFilteredObject f).filtration.obj p).arrow ≫
            (kernelSubobject f.hom).arrow := by
              simpa [FilteredObject.Hom.kernelι, FilteredObject.Hom.inducedSubobjectInclusion] using
                CategoryTheory.FilteredObject.Hom.stageMap_comm (FilteredObject.Hom.kernelι f) p
    _ = Subobject.pullbackπ (kernelSubobject f.hom).arrow (A.filtration.obj p) ≫
          (A.filtration.obj p).arrow := by
            simpa [FilteredObject.Hom.kernelFilteredObject,
              FilteredObject.Hom.inducedSubobjectFilteredObject, DecreasingFiltration.induced] using
              (Subobject.isPullback (kernelSubobject f.hom).arrow (A.filtration.obj p)).w.symm

/-- Helper for Chap13 Lemma 13 13 8: the induced map on the `p`-th graded piece of a filtered
kernel inclusion is monic. -/
private theorem gradedPiece_kernelι_mono
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (p : ℤ) :
    Mono (filtered_gradedPieceMap (FilteredObject.Hom.kernelι f) p) := by
  have hright :
      IsPullback
        (((FilteredObject.Hom.kernelFilteredObject f).filtration.obj p).arrow)
        (CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) p)
        (kernelSubobject f.hom).arrow
        (A.filtration.obj p).arrow := by
    -- Proof comment: the `p`-stage of the filtered kernel is the pullback of the ambient stage
    -- along the kernel inclusion.
    change IsPullback
      (((Subobject.pullback (kernelSubobject f.hom).arrow).obj (A.filtration.obj p)).arrow)
      (CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) p)
      (kernelSubobject f.hom).arrow
      (A.filtration.obj p).arrow
    simpa [stage_kernelι_eq_pullbackπ] using
      (Subobject.isPullback (kernelSubobject f.hom).arrow (A.filtration.obj p)).flip
  have hbig :
      IsPullback
        (((FilteredObject.Hom.kernelFilteredObject f).filtration.obj (p + 1)).arrow)
        (CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) (p + 1))
        (kernelSubobject f.hom).arrow
        (A.filtration.obj (p + 1)).arrow := by
    -- Proof comment: the same pullback description applies one stage lower.
    change IsPullback
      (((Subobject.pullback (kernelSubobject f.hom).arrow).obj (A.filtration.obj (p + 1))).arrow)
      (CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) (p + 1))
      (kernelSubobject f.hom).arrow
      (A.filtration.obj (p + 1)).arrow
    simpa [stage_kernelι_eq_pullbackπ] using
      (Subobject.isPullback (kernelSubobject f.hom).arrow (A.filtration.obj (p + 1))).flip
  have hpullback :
      IsPullback
        ((FilteredObject.Hom.kernelFilteredObject f).filtration.stageInclusion p)
        (CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) (p + 1))
        (CategoryTheory.FilteredObject.Hom.stageMap (FilteredObject.Hom.kernelι f) p)
        (A.filtration.stageInclusion p) := by
    -- Proof comment: paste the two pullback squares for consecutive stages of the filtered kernel.
    exact (hright.paste_horiz_iff
      (CategoryTheory.FilteredObject.Hom.stageInclusion_naturality
        (FilteredObject.Hom.kernelι f) p)).1 <| by
      simpa [DecreasingFiltration.stageInclusion, Category.assoc] using hbig
  -- Proof comment: a pullback square of stage inclusions induces a mono on the cokernel map.
  simpa [filtered_gradedPieceMap] using
    (Abelian.mono_cokernel_map_of_isPullback hpullback)

/-- Helper for Chap13 Lemma 13 13 8: a graded morphism is epic once each graded component is. -/
private theorem gradedObject_epi_of_epi {X Y : GradedObject ℤ 𝒜} (f : X ⟶ Y)
    [∀ p : ℤ, Epi (f p)] : Epi f := by
  refine ⟨?_⟩
  intro Z g h w
  ext p
  exact (cancel_epi (f p)).1 (by simpa using congrArg (fun k : X ⟶ Z ↦ k p) w)

/-- Helper for Chap13 Lemma 13 13 8: a graded morphism is monic once each graded component is. -/
private theorem gradedObject_mono_of_mono {X Y : GradedObject ℤ 𝒜} (f : X ⟶ Y)
    [∀ p : ℤ, Mono (f p)] : Mono f := by
  refine ⟨?_⟩
  intro Z g h w
  ext p
  exact (cancel_mono (f p)).1 (by simpa using congrArg (fun k : Z ⟶ Y ↦ k p) w)

/-- Helper for Chap13 Lemma 13 13 8: the associated-graded map induced by a filtered cokernel
projection is epic. -/
private theorem associatedGraded_toCokernel_epi
    {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    Epi (filtered_associatedGradedMap (FilteredObject.Hom.toCokernel f)) := by
  -- Proof comment: each graded component is the corresponding epic graded-piece map, so the
  -- whole graded morphism is epic degreewise.
  letI (p : ℤ) :
      Epi ((filtered_associatedGradedMap (FilteredObject.Hom.toCokernel f)) p) := by
    simpa [filtered_associatedGradedMap] using
      gradedPiece_toCokernel_epi (f := f) p
  exact gradedObject_epi_of_epi _

/-- Helper for Chap13 Lemma 13 13 8: the associated-graded map induced by a filtered kernel
inclusion is monic. -/
private theorem associatedGraded_kernelι_mono
    {A B : FilteredObject 𝒜} (f : A ⟶ B) :
    Mono (filtered_associatedGradedMap (FilteredObject.Hom.kernelι f)) := by
  -- Proof comment: each graded component is the corresponding monic graded-piece map, so the
  -- whole graded morphism is monic degreewise.
  letI (p : ℤ) :
      Mono ((filtered_associatedGradedMap (FilteredObject.Hom.kernelι f)) p) := by
    simpa [filtered_associatedGradedMap] using
      gradedPiece_kernelι_mono (f := f) p
  exact gradedObject_mono_of_mono _

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

/-- Bridge/view layer: forget the filtration on a filtered cochain complex. -/
abbrev underlying (K : FilteredComplex 𝒜) : CochainComplex 𝒜 ℤ :=
  (FilteredObject.forget.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Bridge/view layer: the associated graded complex of a filtered cochain complex. -/
noncomputable abbrev associatedGraded (K : FilteredComplex 𝒜) :
    CochainComplex (GradedObject ℤ 𝒜) ℤ :=
  (filtered_associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K

/-- Bridge/view layer: the map induced on associated graded complexes by a morphism of filtered
cochain complexes. -/
noncomputable abbrev associatedGradedMap {K L : FilteredComplex 𝒜} (f : K ⟶ L) :
    K.associatedGraded ⟶ L.associatedGraded :=
  (filtered_associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).map f

/-- A filtered cochain complex has finite filtrations when each degree object does. -/
abbrev HasFiniteFiltrations (K : FilteredComplex 𝒜) : Prop :=
  ∀ n : ℤ, (K.X n).IsFinite

/-- The associated graded complex of a filtered complex carries the canonical homology package. -/
noncomputable instance associatedGraded_hasHomology (K : FilteredComplex 𝒜) (n : ℤ) :
    HomologicalComplex.HasHomology K.associatedGraded n :=
  inferInstanceAs
    (HomologicalComplex.HasHomology
      ((filtered_associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) n)

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

/-- Helper for Chap13 Lemma 13 13 8: if the target complex is strictly bounded below by `a`,
then the degree-`a` component of any chain map kills the incoming differential from `a - 1`. -/
private theorem d_comp_component_eq_zero_of_target_isStrictlyGE
    {K L : FilteredComplex 𝒜} (φ : K ⟶ L) (a : ℤ) (hL : L.underlying.IsStrictlyGE a) :
    K.d (a - 1) a ≫ φ.f a = 0 := by
  -- Proof comment: the source degree `a - 1` of the target complex is zero, so the preceding
  -- component of the chain map vanishes; then the chain-map identity at `(a - 1, a)` gives the
  -- required zero composite.
  have hzeroObj : IsZero ((L.X (a - 1)).obj) := by
    rw [CochainComplex.isStrictlyGE_iff] at hL
    simpa [underlying] using hL (a - 1) (by omega)
  have hzeroMap : φ.f (a - 1) = 0 := by
    apply FilteredObject.forget.map_injective
    exact IsZero.eq_of_tgt hzeroObj _ _
  simpa [hzeroMap] using (φ.comm (a - 1) a).symm

/-- Helper for Chap13 Lemma 13 13 8: if the target complex is strictly bounded below by `a`,
then every component landing in a degree `< a` is zero. -/
private theorem component_eq_zero_of_target_isStrictlyGE
    {K L : FilteredComplex 𝒜} (φ : K ⟶ L) (a n : ℤ) (hL : L.underlying.IsStrictlyGE a)
    (hn : n < a) :
    φ.f n = 0 := by
  -- Proof comment: the target object itself vanishes below the lower bound, so any component into
  -- it is forced to be the zero filtered morphism.
  have hzeroObj : IsZero ((L.X n).obj) := by
    rw [CochainComplex.isStrictlyGE_iff] at hL
    simpa [underlying] using hL n hn
  apply FilteredObject.forget.map_injective
  exact IsZero.eq_of_tgt hzeroObj _ _

/-- Helper for Chap13 Lemma 13 13 8: if the source complex is strictly bounded above by `b`,
then the degree-`b` component of any chain map kills the outgoing differential to `b + 1`. -/
private theorem component_comp_d_eq_zero_of_source_isStrictlyLE
    {K L : FilteredComplex 𝒜} (φ : K ⟶ L) (b : ℤ) (hK : K.underlying.IsStrictlyLE b) :
    φ.f b ≫ L.d b (b + 1) = 0 := by
  -- Proof comment: the source degree `b + 1` vanishes under the strict upper bound, so the
  -- `(b + 1)`-component of the chain map is zero; the chain-map identity at `(b, b + 1)` then
  -- forces the desired composite to vanish.
  have hzeroObj : IsZero ((K.X (b + 1)).obj) := by
    rw [CochainComplex.isStrictlyLE_iff] at hK
    simpa [underlying] using hK (b + 1) (by omega)
  have hzeroMap : φ.f (b + 1) = 0 := by
    apply FilteredObject.forget.map_injective
    exact IsZero.eq_of_src hzeroObj _ _
  simpa [hzeroMap] using (φ.comm b (b + 1)).symm

/-- Helper for Chap13 Lemma 13 13 8: a filtered object with zero underlying object is already a
zero object in the filtered category. -/
private theorem filteredObject_isZero_of_isZero_obj
    (A : FilteredObject 𝒜) (hA : IsZero A.obj) :
    IsZero A := by
  -- Proof comment: filtered morphisms are determined by their underlying morphisms.
  rw [IsZero.iff_id_eq_zero]
  apply FilteredObject.forget.map_injective
  exact hA.eq_of_src _ _

/-- Helper for Chap13 Lemma 13 13 8: if the middle term of a cochain complex row is zero, that
row is exact. -/
private theorem exactAt_of_isZero_middle
    {K : CochainComplex (GradedObject ℤ 𝒜) ℤ} (n : ℤ) (hzero : IsZero (K.X n)) :
    K.ExactAt n := by
  -- Proof comment: once `ExactAt` is rewritten to the row short complex, exactness is exactly
  -- the owner theorem for a short complex with zero middle term.
  rw [HomologicalComplex.exactAt_iff]
  exact (K.sc n).exact_of_isZero_X₂ hzero

/-- Helper for Chap13 Lemma 13 13 8: a strict lower bound on the underlying filtered complex also
forces the associated graded complex to vanish in those degrees. -/
private theorem associatedGraded_isStrictlyGE_of_underlying_isStrictlyGE
    (K : FilteredComplex 𝒜) (a : ℤ) (hK : K.underlying.IsStrictlyGE a) :
    K.associatedGraded.IsStrictlyGE a := by
  -- Proof comment: below the cutoff the filtered term itself is zero, and the associated graded
  -- functor preserves zero objects.
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  have hzeroObj : IsZero ((K.X n).obj) := by
    rw [CochainComplex.isStrictlyGE_iff] at hK
    simpa [underlying] using hK n hn
  have hzeroFilt : IsZero (K.X n) :=
    filteredObject_isZero_of_isZero_obj (K.X n) hzeroObj
  simpa [associatedGraded] using
    Functor.map_isZero filtered_associatedGradedFunctor hzeroFilt

/-- Helper for Chap13 Lemma 13 13 8: a strict upper bound on the underlying filtered complex also
forces the associated graded complex to vanish in those degrees. -/
private theorem associatedGraded_isStrictlyLE_of_underlying_isStrictlyLE
    (K : FilteredComplex 𝒜) (b : ℤ) (hK : K.underlying.IsStrictlyLE b) :
    K.associatedGraded.IsStrictlyLE b := by
  -- Proof comment: above the cutoff the filtered term itself is zero, and the associated graded
  -- functor preserves zero objects.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have hzeroObj : IsZero ((K.X n).obj) := by
    rw [CochainComplex.isStrictlyLE_iff] at hK
    simpa [underlying] using hK n hn
  have hzeroFilt : IsZero (K.X n) :=
    filteredObject_isZero_of_isZero_obj (K.X n) hzeroObj
  simpa [associatedGraded] using
    Functor.map_isZero filtered_associatedGradedFunctor hzeroFilt

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

/-- Helper for Chap13 Lemma 13 13 8: the descended cutoff differential out of the lower filtered
cokernel still composes trivially with the next ambient differential. -/
private theorem lower_descToCokernel_comp_eq_zero
    (K : FilteredComplex 𝒜) (a j k : ℤ) :
    FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (K.d a j)
        (lower_filtered_truncation_cutoff_comp_zero K a j) ≫
      K.d j k = 0 := by
  -- Proof comment: forget the filtration, precompose with the cokernel projection, and reduce to
  -- the ambient square-zero relation `K.d_comp_d`.
  apply FilteredObject.forget.map_injective
  apply (cancel_epi (cokernel.π (imageSubobject (K.d (a - 1) a).hom).arrow)).1
  change
    cokernel.π (imageSubobject (K.d (a - 1) a).hom).arrow ≫
        (FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (K.d a j)
          (lower_filtered_truncation_cutoff_comp_zero K a j)).hom ≫
        (K.d j k).hom =
      cokernel.π (imageSubobject (K.d (a - 1) a).hom).arrow ≫ 0
  have hcomp : (K.d a j).hom ≫ (K.d j k).hom = 0 := by
    exact congrArg FilteredObject.Hom.hom (K.d_comp_d a j k)
  simpa [FilteredObject.Hom.descToCokernel, Category.assoc] using hcomp

/-- Helper for Lemma 13.13.8: the lower-truncation differential squares to zero. -/
private theorem lower_filtered_truncation_d_comp_d
    (K : FilteredComplex 𝒜) (a i j k : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) (hjk : (ComplexShape.up ℤ).Rel j k) :
    lower_filtered_truncation_d K a i j ≫ lower_filtered_truncation_d K a j k = 0 := by
  -- Proof comment: split on the source degree relative to the cutoff, so each branch reduces
  -- either to the descended cutoff-zero identity or to the ambient square-zero identity.
  by_cases hia : i = a
  · have haj : a < j := cutoff_lt_target_of_rel_source_eq_cutoff a i j hij hia
    have hak : a < k := cutoff_lt_target_of_rel_source_gt_cutoff a j k hjk haj
    have hjna : j ≠ a := by omega
    subst i
    change a + 1 = j at hij
    change j + 1 = k at hjk
    -- Proof comment: at the cutoff, the middle composite is the descended cokernel arrow.
    calc
      lower_filtered_truncation_d K a a j ≫ lower_filtered_truncation_d K a j k
          =
            eqToHom (lower_filtered_truncation_obj_eq_cokernel K a) ≫
              FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (K.d a j)
                (lower_filtered_truncation_cutoff_comp_zero K a j) ≫
              K.d j k ≫
              eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a k hak).symm := by
                simp [lower_filtered_truncation_d, hij, hjk, hjna, haj, hak, Category.assoc,
                  lower_filtered_truncation_obj_eq_cokernel]
      _ = 0 := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦
              eqToHom (lower_filtered_truncation_obj_eq_cokernel K a) ≫
                t ≫
                eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a k hak).symm)
            (lower_descToCokernel_comp_eq_zero K a j k)
  · by_cases hai : a < i
    · have haj : a < j := cutoff_lt_target_of_rel_source_gt_cutoff a i j hij hai
      have hak : a < k := cutoff_lt_target_of_rel_source_gt_cutoff a j k hjk haj
      have hjna : j ≠ a := by omega
      change i + 1 = j at hij
      change j + 1 = k at hjk
      -- Proof comment: strictly above the cutoff, lower truncation is just the ambient complex.
      calc
        lower_filtered_truncation_d K a i j ≫ lower_filtered_truncation_d K a j k
            =
              eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a i hai) ≫
                (K.d i j ≫ K.d j k) ≫
                eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a k hak).symm := by
                  simp [lower_filtered_truncation_d, hij, hjk, hia, hai, hjna, haj, hak,
                    Category.assoc]
        _ = 0 := by
          rw [K.d_comp_d]
          simp
    · -- Proof comment: below the cutoff, the first differential is definitionally zero.
      simpa [lower_filtered_truncation_d, hij, hjk, hia, hai]

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

/-- Helper for Chap13 Lemma 13 13 8: the cutoff component of the lower-truncation projection is
the filtered cokernel projection. -/
private theorem lower_filtered_truncation_pi_f_cutoff
    (K : FilteredComplex 𝒜) (a : ℤ) :
    lower_filtered_truncation_pi_f K a a =
      FilteredObject.Hom.toCokernel (K.d (a - 1) a) ≫
        eqToHom (lower_filtered_truncation_obj_eq_cokernel K a).symm := by
  -- Proof comment: at the cutoff, the lower branch is impossible and the defining projection is
  -- exactly the filtered cokernel map.
  simp [lower_filtered_truncation_pi_f, lower_filtered_truncation_obj_eq_cokernel]

/-- Helper for Lemma 13.13.8: the lower-truncation projection is a chain map. -/
private theorem lower_filtered_truncation_pi_comm
    (K : FilteredComplex 𝒜) (a i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    lower_filtered_truncation_pi_f K a i ≫ lower_filtered_truncation_d K a i j =
      K.d i j ≫ lower_filtered_truncation_pi_f K a j := by
  -- Proof comment: split on the source degree, so the three cutoff behaviors match the three
  -- owners `comp_toCokernel`, `toCokernel_descToCokernel`, and the identity branch.
  by_cases hilt : i < a
  · by_cases hja : j = a
    · have hi_eq : i = a - 1 := by
        change i + 1 = j at hij
        omega
      subst i
      subst j
      -- Proof comment: the unique map into the cutoff degree factors through the cokernel map.
      simpa [lower_filtered_truncation_pi_f, lower_filtered_truncation_d, Category.assoc,
        lower_filtered_truncation_obj_eq_cokernel] using
        congrArg
          (fun t ↦ t ≫ eqToHom (lower_filtered_truncation_obj_eq_cokernel K a).symm)
          (FilteredObject.Hom.comp_toCokernel (K.d (a - 1) a)).symm
    · have hjlt : j < a := by
        change i + 1 = j at hij
        omega
      -- Proof comment: strictly below the cutoff, both lower-truncation components are zero.
      simpa [lower_filtered_truncation_pi_f, lower_filtered_truncation_d, hij, hilt, hja, hjlt,
        Category.assoc]
  · by_cases hia : i = a
    · have haj : a < j := cutoff_lt_target_of_rel_source_eq_cutoff a i j hij hia
      have hjna : j ≠ a := by omega
      have hjnlt : ¬ j < a := by omega
      subst i
      change a + 1 = j at hij
      -- Proof comment: at the cutoff, the chain-map equation is the defining cokernel descent.
      simpa [lower_filtered_truncation_pi_f, lower_filtered_truncation_d, hij, haj, Category.assoc,
        lower_filtered_truncation_obj_eq_cokernel, hjna, hjnlt] using
        congrArg
          (fun t ↦ t ≫ eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a j haj).symm)
          (FilteredObject.Hom.toCokernel_descToCokernel
            (K.d (a - 1) a) (K.d a j) (lower_filtered_truncation_cutoff_comp_zero K a j))
    · have hai : a < i := by omega
      have haj : a < j := cutoff_lt_target_of_rel_source_gt_cutoff a i j hij hai
      have hjna : j ≠ a := by omega
      have hjnlt : ¬ j < a := by omega
      change i + 1 = j at hij
      -- Proof comment: above the cutoff, the projection is literally the identity.
      simpa [lower_filtered_truncation_pi_f, lower_filtered_truncation_d, hij, hilt, hia, hai,
        haj, hjna, hjnlt, Category.assoc]

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

/-- Helper for Chap13 Lemma 13 13 8: the degree-`n` row map induced on associated graded by the
lower truncation projection. -/
private noncomputable abbrev lowerAssociatedGradedShortComplexMap
    (K : FilteredComplex 𝒜) (a n : ℤ) :
    (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).obj
        K.associatedGraded ⟶
      (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).obj
        (lower_filtered_truncation K a).associatedGraded :=
  (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).map
    (associatedGradedMap (lower_filtered_truncation_pi K a))

/-- Helper for Chap13 Lemma 13 13 8: strictly above the lower cutoff, the associated-graded
projection should be a quasi-isomorphism on the degree-`n` row. -/
private theorem lowerAssociatedGradedQuasiIsoAt_of_twoStepAboveCutoff
    (K : FilteredComplex 𝒜) (a n : ℤ) (hfar : a + 1 < n) :
    ShortComplex.QuasiIso (lowerAssociatedGradedShortComplexMap K a n) := by
  -- Proof comment: two steps above the cutoff, all three lower-truncation components are the
  -- identity branch, so the associated-graded row map is an `epi/iso/mono` comparison.
  have hprev : a < n - 1 := by
    omega
  have hmid : a < n := by
    omega
  have hnext : a < n + 1 := by
    omega
  have hcomp₁ :
      IsIso ((associatedGradedMap (lower_filtered_truncation_pi K a)).f (n - 1)) := by
    -- Proof comment: evaluation at degree `n - 1` sees the above-cutoff identity branch.
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (lower_filtered_truncation_pi K a).f (n - 1) =
        lower_filtered_truncation_pi_f K a (n - 1) by rfl]
    have hnotlt_prev : ¬ (n - 1 < a) := by
      omega
    have hneq_prev : n - 1 ≠ a := by
      omega
    rw [show lower_filtered_truncation_pi_f K a (n - 1) =
        eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (n - 1) hprev).symm by
      simp [lower_filtered_truncation_pi_f, hnotlt_prev, hneq_prev, hprev]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (n - 1) hprev).symm))
  have hcomp₂ :
      IsIso ((associatedGradedMap (lower_filtered_truncation_pi K a)).f n) := by
    -- Proof comment: the middle degree is the same identity branch.
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (lower_filtered_truncation_pi K a).f n = lower_filtered_truncation_pi_f K a n by rfl]
    have hnotlt_mid : ¬ (n < a) := by
      omega
    have hneq_mid : n ≠ a := by
      omega
    rw [show lower_filtered_truncation_pi_f K a n =
        eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a n hmid).symm by
      simp [lower_filtered_truncation_pi_f, hnotlt_mid, hneq_mid, hmid]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a n hmid).symm))
  have hcomp₃ :
      IsIso ((associatedGradedMap (lower_filtered_truncation_pi K a)).f (n + 1)) := by
    -- Proof comment: the degree `n + 1` component is again the associated-graded image of an
    -- identity branch.
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (lower_filtered_truncation_pi K a).f (n + 1) =
        lower_filtered_truncation_pi_f K a (n + 1) by rfl]
    have hnotlt_next : ¬ (n + 1 < a) := by
      omega
    have hneq_next : n + 1 ≠ a := by
      omega
    rw [show lower_filtered_truncation_pi_f K a (n + 1) =
        eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (n + 1) hnext).symm by
      simp [lower_filtered_truncation_pi_f, hnotlt_next, hneq_next, hnext]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (n + 1) hnext).symm))
  let φ :=
    (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).map
      (associatedGradedMap (lower_filtered_truncation_pi K a))
  have hprevIndex : (ComplexShape.up ℤ).prev n = n - 1 := by
    simpa using
      (ComplexShape.prev_eq' (ComplexShape.up ℤ) (i := n - 1) (j := n) (by simp))
  have hnextIndex : (ComplexShape.up ℤ).next n = n + 1 := by
    simpa using
      (ComplexShape.next_eq' (ComplexShape.up ℤ) (i := n) (j := n + 1) (by simp))
  have hEpiPrev :
      Epi ((associatedGradedMap (lower_filtered_truncation_pi K a)).f ((ComplexShape.up ℤ).prev n)) := by
    haveI :
        IsIso
          ((associatedGradedMap (lower_filtered_truncation_pi K a)).f ((ComplexShape.up ℤ).prev n)) := by
      rw [hprevIndex]
      exact hcomp₁
    infer_instance
  letI : IsIso ((associatedGradedMap (lower_filtered_truncation_pi K a)).f n) := hcomp₂
  have hMonoNext :
      Mono ((associatedGradedMap (lower_filtered_truncation_pi K a)).f ((ComplexShape.up ℤ).next n)) := by
    haveI :
        IsIso
          ((associatedGradedMap (lower_filtered_truncation_pi K a)).f ((ComplexShape.up ℤ).next n)) := by
      rw [hnextIndex]
      exact hcomp₃
    infer_instance
  letI : Epi φ.τ₁ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.shortComplexFunctor_obj_X₁] using hEpiPrev
  letI : IsIso φ.τ₂ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f] using hcomp₂
  letI : Mono φ.τ₃ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.shortComplexFunctor_obj_X₃] using hMonoNext
  simpa [lowerAssociatedGradedShortComplexMap, φ] using
    (ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ)

/-- Helper for Chap13 Lemma 13 13 8: at the lower cutoff, the associated-graded cutoff row has
the same homology as the ambient degree-`a` row. -/
private theorem lowerAssociatedGradedQuasiIsoAtCutoff
    (K : FilteredComplex 𝒜) (a : ℤ) :
    ShortComplex.QuasiIso (lowerAssociatedGradedShortComplexMap K a a) := by
  -- Route correction: the cutoff term is not definitionally the ordinary `πTruncGE` cutoff
  -- object, so instance search cannot close this branch by simplification alone.
  -- TODO: build the degree-`a` left-homology comparison explicitly by identifying the target
  -- cutoff row with the kernel of the descended map on the filtered cokernel and then show the
  -- induced homology map is an isomorphism.
  sorry

/-- Helper for Chap13 Lemma 13 13 8: at the immediate successor of the lower cutoff, the
associated-graded row is the ordinary boundary row of the lower truncation. -/
private theorem lowerAssociatedGradedQuasiIsoAtSuccessorCutoff
    (K : FilteredComplex 𝒜) (a : ℤ) :
    ShortComplex.QuasiIso (lowerAssociatedGradedShortComplexMap K a (a + 1)) := by
  -- Proof comment: at degree `a`, the predecessor component is the associated-graded cokernel
  -- map, while the two higher components are identity branches of the truncation projection.
  have hcomp₁ :
      Epi ((associatedGradedMap (lower_filtered_truncation_pi K a)).f a) := by
    have hcutoff :
        ((associatedGradedMap (lower_filtered_truncation_pi K a)).f a) =
          filtered_associatedGradedMap (FilteredObject.Hom.toCokernel (K.d (a - 1) a)) ≫
            filtered_associatedGradedMap
              (eqToHom (lower_filtered_truncation_obj_eq_cokernel K a).symm) := by
      rw [Functor.mapHomologicalComplex_map_f]
      rw [show (lower_filtered_truncation_pi K a).f a = lower_filtered_truncation_pi_f K a a by
        rfl]
      rw [lower_filtered_truncation_pi_f_cutoff]
      ext p
      simp [filtered_associatedGradedMap, filtered_gradedPieceMap_comp]
    rw [hcutoff]
    letI :
        Epi (filtered_associatedGradedMap (FilteredObject.Hom.toCokernel (K.d (a - 1) a))) :=
      associatedGraded_toCokernel_epi (K.d (a - 1) a)
    letI :
        IsIso
          (filtered_associatedGradedMap
            (eqToHom (lower_filtered_truncation_obj_eq_cokernel K a).symm)) := by
      simpa [filtered_associatedGradedMap] using
        (Functor.map_isIso filtered_associatedGradedFunctor
          (eqToHom (lower_filtered_truncation_obj_eq_cokernel K a).symm))
    infer_instance
  have hcomp₂ :
      IsIso ((associatedGradedMap (lower_filtered_truncation_pi K a)).f (a + 1)) := by
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (lower_filtered_truncation_pi K a).f (a + 1) =
        lower_filtered_truncation_pi_f K a (a + 1) by rfl]
    rw [show lower_filtered_truncation_pi_f K a (a + 1) =
        eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (a + 1) (by omega)).symm by
      simp [lower_filtered_truncation_pi_f]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (a + 1) (by omega)).symm))
  have hcomp₃ :
      IsIso ((associatedGradedMap (lower_filtered_truncation_pi K a)).f (a + 2)) := by
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (lower_filtered_truncation_pi K a).f (a + 2) =
        lower_filtered_truncation_pi_f K a (a + 2) by rfl]
    rw [show lower_filtered_truncation_pi_f K a (a + 2) =
        eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (a + 2) (by omega)).symm by
      simp [lower_filtered_truncation_pi_f]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a (a + 2) (by omega)).symm))
  let φ :=
    (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) (a + 1)).map
      (associatedGradedMap (lower_filtered_truncation_pi K a))
  have hprevIndex : (ComplexShape.up ℤ).prev (a + 1) = a := by
    simpa using
      (ComplexShape.prev_eq' (ComplexShape.up ℤ) (i := a) (j := a + 1) (by simp))
  have hnextIndex : (ComplexShape.up ℤ).next (a + 1) = a + 2 := by
    simpa using
      (ComplexShape.next_eq' (ComplexShape.up ℤ) (i := a + 1) (j := a + 2) (by simp))
  letI : Epi φ.τ₁ := by
    rw [show φ.τ₁ = ((associatedGradedMap (lower_filtered_truncation_pi K a)).f
      ((ComplexShape.up ℤ).prev (a + 1))) by
      rfl]
    rw [hprevIndex]
    exact hcomp₁
  letI : IsIso φ.τ₂ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f] using hcomp₂
  letI : Mono φ.τ₃ := by
    haveI :
        IsIso
          ((associatedGradedMap (lower_filtered_truncation_pi K a)).f
            ((ComplexShape.up ℤ).next (a + 1))) := by
      rw [hnextIndex]
      exact hcomp₃
    simpa [φ, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.shortComplexFunctor_obj_X₃]
      using (inferInstance :
        Mono ((associatedGradedMap (lower_filtered_truncation_pi K a)).f
          ((ComplexShape.up ℤ).next (a + 1))))
  simpa [lowerAssociatedGradedShortComplexMap, φ] using
    (ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ)

/-- Helper for Lemma 13.13.8: exactness of `gr(K)` below `a` makes the lower-truncation map a
filtered quasi-isomorphism. -/

theorem quasiIso_associatedGradedMap_lower_filtered_truncation_pi
    (K : FilteredComplex 𝒜) (a : ℤ)
    (hgr : ∀ n : ℤ, n < a → IsZero (K.associatedGraded.homology n)) :
    QuasiIso (associatedGradedMap (lower_filtered_truncation_pi K a)) := by
  -- Proof comment: split the quasi-isomorphism test by cochain degree. Below the cutoff the
  -- target row has zero middle term, at the cutoff and above it remains to compare the explicit
  -- cokernel model with the ambient associated graded row.
  rw [quasiIso_iff]
  intro n
  by_cases hnlt : n < a
  · rw [quasiIsoAt_iff_exactAt']
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact hgr n hnlt
    · exact exactAt_of_isZero_middle n (by
        change
          IsZero
            (((filtered_associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (lower_filtered_truncation K a)).X n)
        rw [show
          ((filtered_associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (lower_filtered_truncation K a)).X n =
            filtered_associatedGradedFunctor.obj ((lower_filtered_truncation K a).X n) by
            rfl]
        rw [show (lower_filtered_truncation K a).X n = lower_filtered_truncation_obj K a n by rfl]
        rw [lower_filtered_truncation_obj_eq_zero_of_lt K a n hnlt]
        simpa [filtered_associatedGradedFunctor] using
          Functor.map_isZero filtered_associatedGradedFunctor (isZero_zero (FilteredObject 𝒜)))
  · by_cases hna : n = a
    · subst n
      rw [quasiIsoAt_iff]
      exact lowerAssociatedGradedQuasiIsoAtCutoff K a
    · have han : a < n := by omega
      by_cases hsuc : n = a + 1
      · subst n
        rw [quasiIsoAt_iff]
        exact lowerAssociatedGradedQuasiIsoAtSuccessorCutoff K a
      · have hfar : a + 1 < n := by omega
        rw [quasiIsoAt_iff]
        exact lowerAssociatedGradedQuasiIsoAt_of_twoStepAboveCutoff K a n hfar

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

/-- Helper for Chap13 Lemma 13 13 8: the degreewise component of the functorial map from the
lower filtered truncation to a target bounded below by `a`. -/
private noncomputable def lowerFilteredTruncationDesc_f
    {K L : FilteredComplex 𝒜} (a : ℤ) (φ : K ⟶ L) (hL : L.underlying.IsStrictlyGE a)
    (n : ℤ) :
    lower_filtered_truncation_obj K a n ⟶ L.X n :=
  if hn : n < a then
    0
  else if hna : n = a then
    eqToHom (lower_filtered_truncation_obj_eq_cokernel_of_eq K a n hna) ≫
      FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (φ.f a)
        (d_comp_component_eq_zero_of_target_isStrictlyGE φ a hL) ≫
      eqToHom (congrArg (fun m : ℤ ↦ L.X m) hna).symm
  else if han : a < n then
    eqToHom (lower_filtered_truncation_obj_eq_self_of_lt K a n han) ≫ φ.f n
  else
    0

/-- Helper for Chap13 Lemma 13 13 8: the functorial lower-truncation descent is a chain map. -/
private theorem lowerFilteredTruncationDesc_cutoff_comm
    {K L : FilteredComplex 𝒜} (a : ℤ) (φ : K ⟶ L) (hL : L.underlying.IsStrictlyGE a)
    {j : ℤ} (hij : (ComplexShape.up ℤ).Rel a j) :
    FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (K.d a j)
        (lower_filtered_truncation_cutoff_comp_zero K a j) ≫
      φ.f j =
    FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (φ.f a)
        (d_comp_component_eq_zero_of_target_isStrictlyGE φ a hL) ≫
      L.d a j := by
  -- Proof comment: compare the two descended maps after precomposing with the cokernel
  -- projection; both sides reduce to the `a → j` chain-map identity for `φ`.
  apply FilteredObject.forget.map_injective
  apply (cancel_epi (cokernel.π (imageSubobject (K.d (a - 1) a).hom).arrow)).1
  calc
    cokernel.π (imageSubobject (K.d (a - 1) a).hom).arrow ≫
        (FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (K.d a j)
          (lower_filtered_truncation_cutoff_comp_zero K a j)).hom ≫
        (φ.f j).hom
        =
      (K.d a j).hom ≫ (φ.f j).hom := by
        simp [FilteredObject.Hom.descToCokernel, Category.assoc]
    _ = (φ.f a).hom ≫ (L.d a j).hom := by
      exact (congrArg FilteredObject.Hom.hom (φ.comm a j)).symm
    _ =
      cokernel.π (imageSubobject (K.d (a - 1) a).hom).arrow ≫
        (FilteredObject.Hom.descToCokernel (K.d (a - 1) a) (φ.f a)
          (d_comp_component_eq_zero_of_target_isStrictlyGE φ a hL)).hom ≫
        (L.d a j).hom := by
        simp [FilteredObject.Hom.descToCokernel, Category.assoc]

/-- Helper for Chap13 Lemma 13 13 8: the functorial lower-truncation descent is a chain map. -/
private theorem lowerFilteredTruncationDesc_comm
    {K L : FilteredComplex 𝒜} (a : ℤ) (φ : K ⟶ L) (hL : L.underlying.IsStrictlyGE a)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    lower_filtered_truncation_d K a i j ≫ lowerFilteredTruncationDesc_f a φ hL j =
      lowerFilteredTruncationDesc_f a φ hL i ≫ L.d i j := by
  -- Proof comment: below the cutoff every source component is zero, at the cutoff the cokernel
  -- descent is characterized by `toCokernel_descToCokernel`, and above the cutoff everything is
  -- the original chain map `φ`.
  by_cases hilt : i < a
  · by_cases hja : j = a
    · have hia : i ≠ a := by omega
      have hai : ¬ a < i := by omega
      -- Proof comment: below the cutoff, both source components of the descent are definitionally
      -- zero, even in the unique branch landing in the cutoff degree.
      simpa [lower_filtered_truncation_d, lowerFilteredTruncationDesc_f, hij, hilt, hja, hia,
        hai, Category.assoc]
    · have hjlt : j < a := by
        change i + 1 = j at hij
        omega
      have hia : i ≠ a := by omega
      have hai : ¬ a < i := by omega
      -- Proof comment: strictly below the cutoff, every term is the zero branch.
      simpa [lower_filtered_truncation_d, lowerFilteredTruncationDesc_f, hij, hilt, hja, hjlt,
        hia, hai, Category.assoc]
  · by_cases hia : i = a
    · have haj : a < j := cutoff_lt_target_of_rel_source_eq_cutoff a i j hij hia
      have hjna : j ≠ a := by omega
      have hjnlt : ¬ j < a := by omega
      subst i
      change a + 1 = j at hij
      -- Proof comment: at the cutoff, the chain-map equation is exactly the descended cokernel
      -- compatibility recorded in the cutoff helper above.
      simpa [lower_filtered_truncation_d, lowerFilteredTruncationDesc_f, hij, haj, hjna, hjnlt,
        Category.assoc, lower_filtered_truncation_obj_eq_cokernel] using
        congrArg
          (fun t ↦ eqToHom (lower_filtered_truncation_obj_eq_cokernel K a) ≫ t)
          (lowerFilteredTruncationDesc_cutoff_comm (K := K) (L := L) a φ hL hij)
    · have hai : a < i := by omega
      have haj : a < j := cutoff_lt_target_of_rel_source_gt_cutoff a i j hij hai
      have hjna : j ≠ a := by omega
      have hjnlt : ¬ j < a := by omega
      change i + 1 = j at hij
      -- Proof comment: above the cutoff, lower truncation preserves the original chain map `φ`
      -- without any further quotienting.
      simpa [lower_filtered_truncation_d, lowerFilteredTruncationDesc_f, hij, hilt, hia, hai,
        haj, hjna, hjnlt, Category.assoc] using φ.comm i j

/-- Helper for Chap13 Lemma 13 13 8: the lower filtered truncation descends any map to a target
that is strictly bounded below by the cutoff. -/
noncomputable def lowerFilteredTruncationDesc
    {K L : FilteredComplex 𝒜} (a : ℤ) (φ : K ⟶ L) (hL : L.underlying.IsStrictlyGE a) :
    lower_filtered_truncation K a ⟶ L where
  f := lowerFilteredTruncationDesc_f a φ hL
  comm' := fun i j hij ↦ (lowerFilteredTruncationDesc_comm a φ hL i j hij).symm

/-- Helper for Chap13 Lemma 13 13 8: composing the canonical lower-truncation projection with the
functorial descent recovers the original map. -/
private theorem lower_filtered_truncation_pi_comp_lowerFilteredTruncationDesc
    {K L : FilteredComplex 𝒜} (a : ℤ) (φ : K ⟶ L) (hL : L.underlying.IsStrictlyGE a) :
    lower_filtered_truncation_pi K a ≫ lowerFilteredTruncationDesc a φ hL = φ := by
  -- Proof comment: split degreewise into the zero-below-cutoff, descended-cutoff, and
  -- identity-above-cutoff branches.
  ext n
  change lower_filtered_truncation_pi_f K a n ≫ lowerFilteredTruncationDesc_f a φ hL n = φ.f n
  by_cases hn : n < a
  · -- Proof comment: below the cutoff the projection and descent are both zero, and `φ.f n`
    -- also vanishes because the target is strictly bounded below by `a`.
    rw [component_eq_zero_of_target_isStrictlyGE φ a n hL hn]
    simp [lower_filtered_truncation_pi_f, lowerFilteredTruncationDesc_f, hn]
  · by_cases hna : n = a
    · subst n
      -- Proof comment: at the cutoff, composing the quotient map with the descended morphism
      -- recovers the original component by the owner cokernel computation.
      simp [lower_filtered_truncation_pi_f, lowerFilteredTruncationDesc_f, Category.assoc,
        lower_filtered_truncation_obj_eq_cokernel,
        FilteredObject.Hom.toCokernel_descToCokernel]
    · have han : a < n := by omega
      -- Proof comment: strictly above the cutoff, the projection is the identity and the descent
      -- is the original component of `φ`.
      simp [lower_filtered_truncation_pi_f, lowerFilteredTruncationDesc_f, hn, hna, han]

/-- Helper for Chap13 Lemma 13 13 8: if the cutoff object already vanishes, then the filtered
cokernel cutoff term also vanishes. -/
private theorem cokernelFilteredObject_isZero_of_isZero_codomain
    {A B : FilteredObject 𝒜} (f : A ⟶ B) (hB : IsZero B.obj) :
    IsZero (FilteredObject.Hom.cokernelFilteredObject f).obj := by
  -- Proof comment: the image inclusion lands in a zero target, hence is epi, so its cokernel is
  -- again zero.
  letI : Epi (imageSubobject f.hom).arrow :=
    Limits.epi_of_target_iso_zero (imageSubobject f.hom).arrow hB.isoZero
  change IsZero (cokernel (imageSubobject f.hom).arrow)
  simpa using (Limits.isZero_cokernel_of_epi (imageSubobject f.hom).arrow)

/-- Helper for Chap13 Lemma 13 13 8: a strict upper bound on the source is preserved by lower
filtered truncation. -/
private theorem lower_filtered_truncation_isStrictlyLE_of_isStrictlyLE
    (K : FilteredComplex 𝒜) (a b : ℤ) (hK : K.underlying.IsStrictlyLE b) :
    (lower_filtered_truncation K a).underlying.IsStrictlyLE b := by
  -- Proof comment: away from the cutoff this is either the original term or the zero term; at the
  -- cutoff, the filtered cokernel also vanishes because the target degree already vanishes.
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  change IsZero ((lower_filtered_truncation_obj K a n).obj)
  by_cases hna : n < a
  · rw [lower_filtered_truncation_obj_eq_zero_of_lt K a n hna]
    simpa using Functor.map_isZero FilteredObject.forget (isZero_zero (FilteredObject 𝒜))
  · by_cases han : a < n
    · rw [lower_filtered_truncation_obj_eq_self_of_lt K a n han]
      rw [CochainComplex.isStrictlyLE_iff] at hK
      simpa [underlying] using hK n hn
    · have hEq : n = a := by omega
      subst n
      have hzeroObj : IsZero ((K.X a).obj) := by
        rw [CochainComplex.isStrictlyLE_iff] at hK
        simpa [underlying] using hK a hn
      rw [lower_filtered_truncation_obj_eq_cokernel]
      exact cokernelFilteredObject_isZero_of_isZero_codomain (K.d (a - 1) a) hzeroObj

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

/-- Helper for Chap13 Lemma 13 13 8: composing into the lifted cutoff kernel map already
vanishes by the ambient square-zero relation. -/
private theorem upperCompLiftToKernel_eq_zero
    (K : FilteredComplex 𝒜) (b i j : ℤ) :
    K.d i j ≫
      FilteredObject.Hom.liftToKernel (K.d b (b + 1)) (K.d j b)
        (upper_filtered_truncation_cutoff_comp_zero K j b) = 0 := by
  -- Proof comment: cancel the filtered kernel inclusion and reduce the lifted composite to the
  -- ambient square-zero relation `K.d_comp_d i j b`.
  apply FilteredObject.forget.map_injective
  change
    (K.d i j ≫
        FilteredObject.Hom.liftToKernel (K.d b (b + 1)) (K.d j b)
          (upper_filtered_truncation_cutoff_comp_zero K j b)).hom =
      0
  apply (cancel_mono (kernelSubobject (K.d b (b + 1)).hom).arrow).1
  calc
    (K.d i j ≫
        (FilteredObject.Hom.liftToKernel (K.d b (b + 1)) (K.d j b)
          (upper_filtered_truncation_cutoff_comp_zero K j b))).hom ≫
        (kernelSubobject (K.d b (b + 1)).hom).arrow
        = (K.d i j).hom ≫ (K.d j b).hom := by
      simpa [Category.assoc, FilteredObject.Hom.kernelι] using
        congrArg (fun t ↦ (K.d i j).hom ≫ t)
          (congrArg FilteredObject.Hom.hom
            (FilteredObject.Hom.liftToKernel_kernelι (K.d b (b + 1)) (K.d j b)
              (upper_filtered_truncation_cutoff_comp_zero K j b)))
    _ = 0 := by
      exact congrArg FilteredObject.Hom.hom (K.d_comp_d i j b)
    _ = 0 ≫ (kernelSubobject (K.d b (b + 1)).hom).arrow := by
      simp

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
  -- Proof comment: split on the middle degree relative to the cutoff, so the three branches
  -- reduce to the outgoing-zero cutoff case, the ambient square-zero relation, or a
  -- definitionally-zero incoming differential above the cutoff.
  by_cases hjb : j = b
  · have hib : i < b := source_lt_cutoff_of_rel_target_eq_cutoff b i j hij hjb
    have hij' : i + 1 = b := by
      simpa [ComplexShape.up, hjb] using hij
    have hjk' : b + 1 = k := by
      simpa [ComplexShape.up, hjb] using hjk
    have hkne : k ≠ b := by
      omega
    have hknlt : ¬ k < b := by
      omega
    -- Proof comment: once the middle degree is the cutoff, the outgoing upper-truncation
    -- differential is definitionally zero because its target lies strictly above the cutoff.
    simpa [upper_filtered_truncation_d, hij', hjk', hjb, hib, hkne, hknlt, Category.assoc,
      upper_filtered_truncation_obj_eq_kernel]
  · by_cases hjlt : j < b
    · by_cases hkb : k = b
      · have hib : i < b := source_lt_cutoff_of_rel_target_lt_cutoff b i j hij hjlt
        have hjne : j ≠ b := by omega
        have hij' : i + 1 = j := by
          simpa [ComplexShape.up] using hij
        have hjk' : j + 1 = b := by
          simpa [ComplexShape.up, hkb] using hjk
        -- Proof comment: the only nontrivial branch factors through the cutoff kernel lift, so
        -- `upperCompLiftToKernel_eq_zero` finishes the ambient composite.
        calc
          upper_filtered_truncation_d K b i j ≫ upper_filtered_truncation_d K b j k
              =
                eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b i hib) ≫
                  K.d i j ≫
                  FilteredObject.Hom.liftToKernel (K.d b (b + 1)) (K.d j b)
                    (upper_filtered_truncation_cutoff_comp_zero K j b) ≫
                  eqToHom (upper_filtered_truncation_obj_eq_kernel_of_eq K b k hkb).symm := by
                    simp [upper_filtered_truncation_d, hij', hjk', hjb, hjlt, hjne, hkb, hib,
                      Category.assoc, upper_filtered_truncation_obj_eq_kernel]
          _ = 0 := by
            simpa [Category.assoc] using
              congrArg
                (fun t ↦
                  eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b i hib) ≫
                    t ≫
                    eqToHom (upper_filtered_truncation_obj_eq_kernel_of_eq K b k hkb).symm)
                (upperCompLiftToKernel_eq_zero K b i j)
      · by_cases hklt : k < b
        · have hib : i < b := source_lt_cutoff_of_rel_target_lt_cutoff b i j hij hjlt
          have hjne : j ≠ b := by omega
          have hij' : i + 1 = j := by
            simpa [ComplexShape.up] using hij
          have hjk' : j + 1 = k := by
            simpa [ComplexShape.up] using hjk
          -- Proof comment: strictly below the cutoff, the upper truncation is literally the
          -- original complex, so the composite is `K.d_comp_d`.
          calc
            upper_filtered_truncation_d K b i j ≫ upper_filtered_truncation_d K b j k
                =
                  eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b i hib) ≫
                    (K.d i j ≫ K.d j k) ≫
                    eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b k hklt).symm := by
                      simp [upper_filtered_truncation_d, hij', hjk', hjb, hjlt, hjne, hkb, hklt,
                        hib, Category.assoc]
            _ = 0 := by
              rw [K.d_comp_d]
              simp
        · -- Proof comment: if the target degree is neither below nor equal to the cutoff, the
          -- second differential is definitionally zero.
          have hjne : j ≠ b := by omega
          simpa [upper_filtered_truncation_d, hij, hjk, hjb, hjlt, hjne, hkb, hklt,
            Category.assoc]
    · -- Proof comment: above the cutoff, the first upper-truncation differential is already zero.
      simpa [upper_filtered_truncation_d, hij, hjk, hjb, hjlt]

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

/-- Helper for Chap13 Lemma 13 13 8: the cutoff component of the upper-truncation inclusion is
the filtered kernel inclusion. -/
private theorem upper_filtered_truncation_iota_f_cutoff
    (K : FilteredComplex 𝒜) (b : ℤ) :
    upper_filtered_truncation_iota_f K b b =
      eqToHom (upper_filtered_truncation_obj_eq_kernel K b) ≫
        FilteredObject.Hom.kernelι (K.d b (b + 1)) := by
  -- Proof comment: at the cutoff, the lower branch is impossible and the defining inclusion is
  -- exactly the filtered kernel map.
  simp [upper_filtered_truncation_iota_f, upper_filtered_truncation_obj_eq_kernel]

/-- Helper for Lemma 13.13.8: the upper-truncation inclusion is a chain map. -/
private theorem upper_filtered_truncation_iota_comm
    (K : FilteredComplex 𝒜) (b i j : ℤ)
    (hij : (ComplexShape.up ℤ).Rel i j) :
    upper_filtered_truncation_iota_f K b i ≫ K.d i j =
      upper_filtered_truncation_d K b i j ≫ upper_filtered_truncation_iota_f K b j := by
  -- Route correction: normalize the cutoff branch directly at `j = b`, so the lifted kernel map
  -- matches `liftToKernel_kernelι` without any extra `i + 1 = j` transport churn.
  -- Proof comment: split on the target degree relative to the cutoff. Below the cutoff the
  -- statement is definitional, at the cutoff it is the kernel-lift computation, and above the
  -- cutoff either the source is already zero or `i = b`, when `kernelι_comp` closes the branch.
  by_cases hjb : j = b
  · have hib : i < b := source_lt_cutoff_of_rel_target_eq_cutoff b i j hij hjb
    have hij' : i + 1 = b := by
      simpa [ComplexShape.up, hjb] using hij
    simpa [upper_filtered_truncation_iota_f, upper_filtered_truncation_d, hij', hjb, hib,
      Category.assoc, upper_filtered_truncation_obj_eq_kernel] using
      congrArg
        (fun t ↦
          eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b i hib) ≫
            t ≫ eqToHom (congrArg (fun m : ℤ ↦ K.X m) hjb).symm)
        (FilteredObject.Hom.liftToKernel_kernelι (K.d b (b + 1)) (K.d i b)
          (upper_filtered_truncation_cutoff_comp_zero K i b)).symm
  · by_cases hjlt : j < b
    · have hib : i < b := source_lt_cutoff_of_rel_target_lt_cutoff b i j hij hjlt
      have hjne : j ≠ b := by omega
      have hij' : i + 1 = j := by
        simpa [ComplexShape.up] using hij
      -- Proof comment: strictly below the cutoff, both truncation maps are ambient identities.
      simpa [upper_filtered_truncation_iota_f, upper_filtered_truncation_d, hij', hjb, hjlt,
        hib, hjne, Category.assoc]
    · have hbj : b < j := by
        omega
      by_cases hbi : b < i
      · have hibl : ¬ i < b := by omega
        have hine : i ≠ b := by omega
        have hij' : i + 1 = j := by
          simpa [ComplexShape.up] using hij
        -- Proof comment: above the cutoff, the source inclusion and the truncation differential
        -- are both definitionally zero.
        simpa [upper_filtered_truncation_iota_f, upper_filtered_truncation_d, hij', hjb, hjlt,
          hbi, hbj, hibl, hine, Category.assoc]
      · have hib : i = b := by
          change i + 1 = j at hij
          omega
        subst i
        have hj' : b + 1 = j := by
          simpa [ComplexShape.up] using hij
        subst j
        -- Proof comment: the only remaining branch is the cutoff source followed by the ambient
        -- differential, which vanishes by the filtered kernel inclusion relation.
        simpa [upper_filtered_truncation_iota_f, upper_filtered_truncation_d, Category.assoc,
          upper_filtered_truncation_obj_eq_kernel] using
          FilteredObject.Hom.kernelι_comp (K.d b (b + 1))

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

/-- Helper for Chap13 Lemma 13 13 8: the degree-`n` row map induced on associated graded by the
upper truncation inclusion. -/
private noncomputable abbrev upperAssociatedGradedShortComplexMap
    (K : FilteredComplex 𝒜) (b n : ℤ) :
    (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).obj
        (upper_filtered_truncation K b).associatedGraded ⟶
      (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).obj
        K.associatedGraded :=
  (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).map
    (associatedGradedMap (upper_filtered_truncation_iota K b))

/-- Helper for Chap13 Lemma 13 13 8: strictly below the upper cutoff, the associated-graded
inclusion should be a quasi-isomorphism on the degree-`n` row. -/
private theorem upperAssociatedGradedQuasiIsoAt_of_twoStepBelowCutoff
    (K : FilteredComplex 𝒜) (b n : ℤ) (hfar : n < b - 1) :
    ShortComplex.QuasiIso (upperAssociatedGradedShortComplexMap K b n) := by
  -- Proof comment: two steps below the cutoff, all three upper-truncation components are the
  -- identity branch, so the associated-graded row map is again an `epi/iso/mono` comparison.
  have hprev : n - 1 < b := by
    omega
  have hmid : n < b := by
    omega
  have hnext : n + 1 < b := by
    omega
  have hcomp₁ :
      IsIso ((associatedGradedMap (upper_filtered_truncation_iota K b)).f (n - 1)) := by
    -- Proof comment: evaluation at degree `n - 1` sees the below-cutoff identity branch.
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (upper_filtered_truncation_iota K b).f (n - 1) =
        upper_filtered_truncation_iota_f K b (n - 1) by rfl]
    rw [show upper_filtered_truncation_iota_f K b (n - 1) =
        eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (n - 1) hprev) by
      simp [upper_filtered_truncation_iota_f, hprev]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (n - 1) hprev)))
  have hcomp₂ :
      IsIso ((associatedGradedMap (upper_filtered_truncation_iota K b)).f n) := by
    -- Proof comment: the middle degree is the same identity branch.
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (upper_filtered_truncation_iota K b).f n = upper_filtered_truncation_iota_f K b n by rfl]
    rw [show upper_filtered_truncation_iota_f K b n =
        eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b n hmid) by
      simp [upper_filtered_truncation_iota_f, hmid]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b n hmid)))
  have hcomp₃ :
      IsIso ((associatedGradedMap (upper_filtered_truncation_iota K b)).f (n + 1)) := by
    -- Proof comment: the degree `n + 1` component is still below the cutoff, so it is also the
    -- associated-graded image of an identity branch.
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (upper_filtered_truncation_iota K b).f (n + 1) =
        upper_filtered_truncation_iota_f K b (n + 1) by rfl]
    rw [show upper_filtered_truncation_iota_f K b (n + 1) =
        eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (n + 1) hnext) by
      simp [upper_filtered_truncation_iota_f, hnext]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (n + 1) hnext)))
  let φ :=
    (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) n).map
      (associatedGradedMap (upper_filtered_truncation_iota K b))
  have hprevIndex : (ComplexShape.up ℤ).prev n = n - 1 := by
    simpa using
      (ComplexShape.prev_eq' (ComplexShape.up ℤ) (i := n - 1) (j := n) (by simp))
  have hnextIndex : (ComplexShape.up ℤ).next n = n + 1 := by
    simpa using
      (ComplexShape.next_eq' (ComplexShape.up ℤ) (i := n) (j := n + 1) (by simp))
  have hEpiPrev :
      Epi ((associatedGradedMap (upper_filtered_truncation_iota K b)).f ((ComplexShape.up ℤ).prev n)) := by
    haveI :
        IsIso
          ((associatedGradedMap (upper_filtered_truncation_iota K b)).f ((ComplexShape.up ℤ).prev n)) := by
      rw [hprevIndex]
      exact hcomp₁
    infer_instance
  letI : IsIso ((associatedGradedMap (upper_filtered_truncation_iota K b)).f n) := hcomp₂
  have hMonoNext :
      Mono ((associatedGradedMap (upper_filtered_truncation_iota K b)).f ((ComplexShape.up ℤ).next n)) := by
    haveI :
        IsIso
          ((associatedGradedMap (upper_filtered_truncation_iota K b)).f ((ComplexShape.up ℤ).next n)) := by
      rw [hnextIndex]
      exact hcomp₃
    infer_instance
  letI : Epi φ.τ₁ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.shortComplexFunctor_obj_X₁] using hEpiPrev
  letI : IsIso φ.τ₂ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f] using hcomp₂
  letI : Mono φ.τ₃ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.shortComplexFunctor_obj_X₃] using hMonoNext
  simpa [upperAssociatedGradedShortComplexMap, φ] using
    (ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ)

/-- Helper for Chap13 Lemma 13 13 8: at the upper cutoff, the associated-graded cutoff row has
the same homology as the ambient degree-`b` row. -/
private theorem upperAssociatedGradedQuasiIsoAtCutoff
    (K : FilteredComplex 𝒜) (b : ℤ) :
    ShortComplex.QuasiIso (upperAssociatedGradedShortComplexMap K b b) := by
  -- Route correction: this kernel-side cutoff branch is not an instance-search problem; it needs
  -- an explicit comparison between the ambient degree-`b` homology and the homology of the row
  -- obtained from the filtered kernel cutoff term.
  -- TODO: construct the degree-`b` right-homology comparison using the lifted kernel map and show
  -- that the induced homology morphism is an isomorphism.
  sorry

/-- Helper for Chap13 Lemma 13 13 8: at the immediate predecessor of the upper cutoff, the
associated-graded row is the ordinary boundary row of the upper truncation. -/
private theorem upperAssociatedGradedQuasiIsoAtPredecessorCutoff
    (K : FilteredComplex 𝒜) (b : ℤ) :
    ShortComplex.QuasiIso (upperAssociatedGradedShortComplexMap K b (b - 1)) := by
  -- Proof comment: the two lower degrees are identity branches, and the cutoff component is the
  -- associated-graded kernel inclusion.
  have hcomp₁ :
      IsIso ((associatedGradedMap (upper_filtered_truncation_iota K b)).f (b - 2)) := by
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (upper_filtered_truncation_iota K b).f (b - 2) =
        upper_filtered_truncation_iota_f K b (b - 2) by rfl]
    rw [show upper_filtered_truncation_iota_f K b (b - 2) =
        eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (b - 2) (by omega)) by
      simp [upper_filtered_truncation_iota_f]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (b - 2) (by omega))))
  have hcomp₂ :
      IsIso ((associatedGradedMap (upper_filtered_truncation_iota K b)).f (b - 1)) := by
    rw [Functor.mapHomologicalComplex_map_f]
    rw [show (upper_filtered_truncation_iota K b).f (b - 1) =
        upper_filtered_truncation_iota_f K b (b - 1) by rfl]
    rw [show upper_filtered_truncation_iota_f K b (b - 1) =
        eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (b - 1) (by omega)) by
      simp [upper_filtered_truncation_iota_f]]
    simpa [filtered_associatedGradedMap] using
      (Functor.map_isIso filtered_associatedGradedFunctor
        (eqToHom (upper_filtered_truncation_obj_eq_self_of_lt K b (b - 1) (by omega))))
  have hcomp₃ :
      Mono ((associatedGradedMap (upper_filtered_truncation_iota K b)).f b) := by
    have hcutoff :
        ((associatedGradedMap (upper_filtered_truncation_iota K b)).f b) =
          filtered_associatedGradedMap
              (eqToHom (upper_filtered_truncation_obj_eq_kernel K b)) ≫
            filtered_associatedGradedMap (FilteredObject.Hom.kernelι (K.d b (b + 1))) := by
      rw [Functor.mapHomologicalComplex_map_f]
      rw [show (upper_filtered_truncation_iota K b).f b = upper_filtered_truncation_iota_f K b b by
        rfl]
      rw [upper_filtered_truncation_iota_f_cutoff]
      ext p
      simp [filtered_associatedGradedMap, filtered_gradedPieceMap_comp]
    rw [hcutoff]
    letI :
        IsIso
          (filtered_associatedGradedMap (eqToHom (upper_filtered_truncation_obj_eq_kernel K b))) := by
      simpa [filtered_associatedGradedMap] using
        (Functor.map_isIso filtered_associatedGradedFunctor
          (eqToHom (upper_filtered_truncation_obj_eq_kernel K b)))
    letI :
        Mono (filtered_associatedGradedMap (FilteredObject.Hom.kernelι (K.d b (b + 1)))) :=
      associatedGraded_kernelι_mono (K.d b (b + 1))
    infer_instance
  let φ :=
    (HomologicalComplex.shortComplexFunctor (GradedObject ℤ 𝒜) (ComplexShape.up ℤ) (b - 1)).map
      (associatedGradedMap (upper_filtered_truncation_iota K b))
  have hprevIndex : (ComplexShape.up ℤ).prev (b - 1) = b - 2 := by
    simpa using
      (ComplexShape.prev_eq' (ComplexShape.up ℤ) (i := b - 2) (j := b - 1) (by simp))
  have hnextIndex : (ComplexShape.up ℤ).next (b - 1) = b := by
    simpa using
      (ComplexShape.next_eq' (ComplexShape.up ℤ) (i := b - 1) (j := b) (by simp))
  letI : Epi φ.τ₁ := by
    haveI :
        IsIso
          ((associatedGradedMap (upper_filtered_truncation_iota K b)).f
            ((ComplexShape.up ℤ).prev (b - 1))) := by
      rw [hprevIndex]
      exact hcomp₁
    simpa [φ, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.shortComplexFunctor_obj_X₁]
      using (inferInstance :
        Epi ((associatedGradedMap (upper_filtered_truncation_iota K b)).f
          ((ComplexShape.up ℤ).prev (b - 1))))
  letI : IsIso φ.τ₂ := by
    simpa [φ, Functor.mapHomologicalComplex_map_f] using hcomp₂
  letI : Mono φ.τ₃ := by
    rw [show φ.τ₃ = ((associatedGradedMap (upper_filtered_truncation_iota K b)).f
      ((ComplexShape.up ℤ).next (b - 1))) by
      rfl]
    rw [hnextIndex]
    exact hcomp₃
  simpa [upperAssociatedGradedShortComplexMap, φ] using
    (ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ)

/-- Helper for Lemma 13.13.8: exactness of `gr(K)` above `b` makes the upper-truncation map a
filtered quasi-isomorphism. -/

theorem quasiIso_associatedGradedMap_upper_filtered_truncation_iota
    (K : FilteredComplex 𝒜) (b : ℤ)
    (hgr : ∀ n : ℤ, b < n → IsZero (K.associatedGraded.homology n)) :
    QuasiIso (associatedGradedMap (upper_filtered_truncation_iota K b)) := by
  -- Proof comment: dual to the lower case, split by cochain degree. Above the cutoff the source
  -- row has zero middle term, while the cutoff and below-cutoff rows need the kernel comparison.
  rw [quasiIso_iff]
  intro n
  by_cases hbn : b < n
  · rw [quasiIsoAt_iff_exactAt]
    · rw [HomologicalComplex.exactAt_iff_isZero_homology]
      exact hgr n hbn
    · exact exactAt_of_isZero_middle n (by
        change
          IsZero
            (((filtered_associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (upper_filtered_truncation K b)).X n)
        rw [show
          ((filtered_associatedGradedFunctor.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (upper_filtered_truncation K b)).X n =
            filtered_associatedGradedFunctor.obj ((upper_filtered_truncation K b).X n) by
            rfl]
        rw [show (upper_filtered_truncation K b).X n = upper_filtered_truncation_obj K b n by rfl]
        rw [upper_filtered_truncation_obj_eq_zero_of_lt K b n hbn]
        simpa [filtered_associatedGradedFunctor] using
          Functor.map_isZero filtered_associatedGradedFunctor (isZero_zero (FilteredObject 𝒜)))
  · by_cases hnb : n = b
    · subst n
      rw [quasiIsoAt_iff]
      exact upperAssociatedGradedQuasiIsoAtCutoff K b
    · have hlt : n < b := by omega
      by_cases hpred : n = b - 1
      · subst n
        rw [quasiIsoAt_iff]
        exact upperAssociatedGradedQuasiIsoAtPredecessorCutoff K b
      · have hfar : n < b - 1 := by omega
        rw [quasiIsoAt_iff]
        exact upperAssociatedGradedQuasiIsoAt_of_twoStepBelowCutoff K b n hfar

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
  -- Proof comment: lower-truncate the bounded-above replacement `M`, and descend the composite
  -- `g ≫ f` through that lower truncation because the target `L` is already bounded below.
  letI : QuasiIso (associatedGradedMap f) := hf
  letI : QuasiIso (associatedGradedMap g) := hg
  have hgf : QuasiIso (associatedGradedMap (g ≫ f)) := by
    simpa [associatedGradedMap] using
      (show QuasiIso (associatedGradedMap g ≫ associatedGradedMap f) by infer_instance)
  have hLgr : L.associatedGraded.IsStrictlyGE a :=
    associatedGraded_isStrictlyGE_of_underlying_isStrictlyGE L a hL
  have hBelowM : ∀ n : ℤ, n < a → IsZero (M.associatedGraded.homology n) := by
    intro n hn
    have hExactL : L.associatedGraded.ExactAt n := by
      exact exactAt_of_isZero_middle n (by
        rw [CochainComplex.isStrictlyGE_iff] at hLgr
        exact hLgr n hn)
    have hExactM : M.associatedGraded.ExactAt n :=
      (exactAt_iff_of_quasiIsoAt (associatedGradedMap (g ≫ f)) n).2 hExactL
    exact (HomologicalComplex.exactAt_iff_isZero_homology (K := M.associatedGraded) (i := n)).1
      hExactM
  let N := lower_filtered_truncation M a
  let u : M ⟶ N := lower_filtered_truncation_pi M a
  let v : N ⟶ L := lowerFilteredTruncationDesc a (g ≫ f) hL
  have hu : QuasiIso (associatedGradedMap u) :=
    quasiIso_associatedGradedMap_lower_filtered_truncation_pi M a hBelowM
  letI : QuasiIso (associatedGradedMap u) := hu
  have huv_eq : u ≫ v = g ≫ f :=
    lower_filtered_truncation_pi_comp_lowerFilteredTruncationDesc a (g ≫ f) hL
  have huv : QuasiIso (associatedGradedMap (u ≫ v)) := by
    simpa [huv_eq] using hgf
  have huv_comp : QuasiIso (associatedGradedMap u ≫ associatedGradedMap v) := by
    simpa [associatedGradedMap] using huv
  letI : QuasiIso (associatedGradedMap u ≫ associatedGradedMap v) := huv_comp
  have hv : QuasiIso (associatedGradedMap v) :=
    quasiIso_of_comp_left (associatedGradedMap u) (associatedGradedMap v)
  refine ⟨N, lower_filtered_truncation_hasFiniteFiltrations M hMfin a, u, v, hu, hv, ?_, ?_, ?_⟩
  · -- Proof comment: the defining descent identity is exactly the commutative square relation.
    exact ⟨lower_filtered_truncation_pi_comp_lowerFilteredTruncationDesc a (g ≫ f) hL⟩
  · -- Proof comment: the lower truncation is constructed to vanish below the cutoff.
    exact lower_filtered_truncation_isStrictlyGE M a
  · -- Proof comment: the bounded-above hypothesis on `M` survives the lower truncation.
    exact lower_filtered_truncation_isStrictlyLE_of_isStrictlyLE M a b hM

/-- Lemma 13.13.8 (1): if the associated graded complex of a filtered complex with finite
filtrations has zero cohomology in all degrees `< a`, then there exists a filtered
quasi-isomorphism from `K` to a filtered complex whose underlying complex is bounded below by
`a`. -/
@[stacks 05S5]
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
@[stacks 05S5]
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
@[stacks 05S5]
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
