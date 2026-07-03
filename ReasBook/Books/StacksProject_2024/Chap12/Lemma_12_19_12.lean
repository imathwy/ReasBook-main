import StacksProject_2024.Chap12.Lemma_12_19_2
import StacksProject_2024.Chap12.Lemma_12_19_4

open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 12.19.12:
- primary domain: filtered objects in an abelian category, their stagewise quotients and
  associated graded objects, and short exact sequences on graded pieces;
- sampled owner declarations in this domain:
  `FilteredObject`,
  `FilteredObject.subobjectFilteredObject`,
  `FilteredObject.quotientFilteredObject`,
  `FilteredObject.Hom.coimage`,
  `FilteredObject.Hom.image`,
  `ShortComplex.ShortExact`;
- best owner abstraction: the source-facing owner remains `FilteredObject C`, while exactness of
  the graded three-term sequences is expressed canonically through `ShortComplex C` and
  `ShortComplex.ShortExact`;
- primitive data: the earlier chapter owners for filtered subobjects, filtered quotients, filtered
  coimages, and filtered images;
- derived API in this file: stage/quotient/graded maps, the corresponding functors, and the
  source-facing graded short complexes attached to subobjects, kernels, coimages, images, and
  cokernels;
- source/core/bridge triage:
  `source-facing`: the short exact graded sequences in parts `(1)` through `(3)`;
  `core/canonical`: `FilteredObject`, `ShortComplex`, and `ShortComplex.ShortExact`;
  `bridge/view`: the functorial maps on stages, quotients, and graded pieces used to assemble the
  source-facing short complexes. -/

section Quotients

variable [HasZeroMorphisms C] [HasCokernels C]

namespace FilteredObject

variable (A : FilteredObject C)

/-- The quotient object `A / F^p A`. -/
abbrev quotient (p : ℤ) : C :=
  cokernel (A.filtration.obj p).arrow

end FilteredObject

end Quotients

namespace FilteredObject.Hom

open FilteredObject

variable {A B D : FilteredObject C}

/-- The induced map on a filtration stage preserves identities. -/
private theorem stageMap_id (A : FilteredObject C) (p : ℤ) :
    stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

/-- The induced map on a filtration stage preserves composition. -/
private theorem stageMap_comp (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    stageMap (f ≫ g) p = stageMap f p ≫ stageMap g p := by
  exact (cancel_mono (D.filtration.obj p).arrow).1 (by
    calc
      stageMap (f ≫ g) p ≫ (D.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f ≫ g).hom := by rw [stageMap_comm]
      _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by simp [Category.assoc]
      _ = (stageMap f p ≫ (B.filtration.obj p).arrow) ≫ g.hom := by rw [stageMap_comm]
      _ = stageMap f p ≫ (stageMap g p ≫ (D.filtration.obj p).arrow) := by
            rw [stageMap_comm]
            simp [Category.assoc]
      _ = (stageMap f p ≫ stageMap g p) ≫ (D.filtration.obj p).arrow := by
            simp [Category.assoc])

end FilteredObject.Hom

section HomZeroMorphisms

variable [HasZeroMorphisms C]

namespace FilteredObject.Hom

open FilteredObject

variable {A B D : FilteredObject C}

/-- The induced map on a filtration stage preserves zero morphisms. -/
private theorem stageMap_zero (A B : FilteredObject C) (p : ℤ) :
    stageMap (0 : A ⟶ B) p = 0 := by
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

end FilteredObject.Hom

end HomZeroMorphisms

section HomGraded

variable [HasZeroMorphisms C] [HasCokernels C]

namespace FilteredObject.Hom

open FilteredObject

variable {A B D : FilteredObject C}

/-- The morphism induced by a filtered morphism on the `p`-th graded pieces. -/
abbrev gradedPieceMap (f : A ⟶ B) (p : ℤ) : gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (stageMap f (p + 1)) (stageMap f p)
    (stageInclusion_naturality f p)

/-- The morphism induced on associated graded objects by a filtered morphism. -/
def associatedGradedMap (f : A ⟶ B) : A.associatedGraded ⟶ B.associatedGraded :=
  fun p ↦ gradedPieceMap f p

/-- The induced map on graded pieces preserves identities. -/
private theorem gradedPieceMap_id (A : FilteredObject C) (p : ℤ) :
    gradedPieceMap (𝟙 A) p = 𝟙 (gr^{p} A) := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_id])

/-- The induced map on graded pieces preserves composition. -/
private theorem gradedPieceMap_comp (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, Category.assoc, stageMap_comp])

/-- The induced map on graded pieces preserves zero morphisms. -/
private theorem gradedPieceMap_zero (A B : FilteredObject C) (p : ℤ) :
    gradedPieceMap (0 : A ⟶ B) p = 0 := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_zero])

/-- The induced map on associated graded objects preserves identities. -/
private theorem associatedGradedMap_id (A : FilteredObject C) :
    associatedGradedMap (𝟙 A) = 𝟙 A.associatedGraded := by
  ext p
  simpa using gradedPieceMap_id A p

/-- The induced map on associated graded objects preserves composition. -/
private theorem associatedGradedMap_comp (f : A ⟶ B) (g : B ⟶ D) :
    associatedGradedMap (f ≫ g) = associatedGradedMap f ≫ associatedGradedMap g := by
  ext p
  simpa using gradedPieceMap_comp f g p

/-- The induced map on associated graded objects preserves zero morphisms. -/
private theorem associatedGradedMap_zero (A B : FilteredObject C) :
    associatedGradedMap (0 : A ⟶ B) = 0 := by
  ext p
  simpa using gradedPieceMap_zero A B p

/-- The induced map on filtration stages preserves addition. -/
private theorem stageMap_add [Preadditive C] (f g : A ⟶ B) (p : ℤ) :
    stageMap (f + g) p = stageMap f p + stageMap g p := sorry

/-- The induced map on graded pieces preserves addition. -/
private theorem gradedPieceMap_add [Preadditive C] (f g : A ⟶ B) (p : ℤ) :
    gradedPieceMap (f + g) p = gradedPieceMap f p + gradedPieceMap g p := sorry

/-- The induced map on associated graded objects preserves addition. -/
private theorem associatedGradedMap_add [Preadditive C] [Preadditive (GradedObject ℤ C)]
    (f g : A ⟶ B) :
    associatedGradedMap (f + g) = associatedGradedMap f + associatedGradedMap g := sorry

-- Proof sketch: after composing with the two cokernel projections, both sides are induced from the
-- zero composite `f ≫ g = 0` in the filtered category.
/-- A zero composite of filtered morphisms induces a zero composite on graded pieces. -/
theorem gradedPieceMap_comp_zero (f : A ⟶ B) (g : B ⟶ D) (hcomp : f ≫ g = 0) (p : ℤ) :
    gradedPieceMap f p ≫ gradedPieceMap g p = 0 := sorry

end FilteredObject.Hom

end HomGraded

section HomQuotients

variable [HasZeroMorphisms C] [HasCokernels C]

namespace FilteredObject.Hom

open FilteredObject

variable {A B D : FilteredObject C}

/-- The map induced by a filtered morphism on the quotients `A / F^p A ⟶ B / F^p B`. -/
abbrev quotientMap (f : A ⟶ B) (p : ℤ) : A.quotient p ⟶ B.quotient p :=
  cokernel.map (A.filtration.obj p).arrow (B.filtration.obj p).arrow (stageMap f p) f.hom
    (stageMap_comm f p).symm

/-- The map on quotients commutes with the cokernel projections. -/
theorem quotientMap_comm (f : A ⟶ B) (p : ℤ) :
    cokernel.π (A.filtration.obj p).arrow ≫ quotientMap f p =
      f.hom ≫ cokernel.π (B.filtration.obj p).arrow := by
  simp [quotientMap]

/-- The induced map on quotients preserves identities. -/
private theorem quotientMap_id (A : FilteredObject C) (p : ℤ) :
    quotientMap (𝟙 A) p = 𝟙 (A.quotient p) := by
  refine (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1 ?_
  have h₁ :
      cokernel.π (A.filtration.obj p).arrow ≫ quotientMap (𝟙 A) p =
        cokernel.π (A.filtration.obj p).arrow := by
    rw [quotientMap_comm]
    simp
  have h₂ :
      cokernel.π (A.filtration.obj p).arrow =
        cokernel.π (A.filtration.obj p).arrow ≫ 𝟙 (A.quotient p) := by
    simp
  exact h₁.trans h₂

/-- The induced map on quotients preserves composition. -/
private theorem quotientMap_comp (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    quotientMap (f ≫ g) p = quotientMap f p ≫ quotientMap g p := by
  refine (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1 ?_
  have h₁ :
      cokernel.π (A.filtration.obj p).arrow ≫ quotientMap (f ≫ g) p =
        (f ≫ g).hom ≫ cokernel.π (D.filtration.obj p).arrow :=
    quotientMap_comm (f ≫ g) p
  have h₂ :
      (f ≫ g).hom ≫ cokernel.π (D.filtration.obj p).arrow =
        f.hom ≫ (cokernel.π (B.filtration.obj p).arrow ≫ quotientMap g p) := by
    rw [quotientMap_comm]
    simp [Category.assoc]
  have h₃ :
      f.hom ≫ (cokernel.π (B.filtration.obj p).arrow ≫ quotientMap g p) =
        cokernel.π (A.filtration.obj p).arrow ≫ (quotientMap f p ≫ quotientMap g p) := by
    calc
      f.hom ≫ (cokernel.π (B.filtration.obj p).arrow ≫ quotientMap g p)
          = (f.hom ≫ cokernel.π (B.filtration.obj p).arrow) ≫ quotientMap g p := by
              simp [Category.assoc]
      _ = (cokernel.π (A.filtration.obj p).arrow ≫ quotientMap f p) ≫ quotientMap g p := by
            exact congrArg (fun k ↦ k ≫ quotientMap g p) (quotientMap_comm f p).symm
      _ = cokernel.π (A.filtration.obj p).arrow ≫ (quotientMap f p ≫ quotientMap g p) := by
            simp [Category.assoc]
  exact h₁.trans (h₂.trans h₃)

/-- The induced map on quotients preserves zero morphisms. -/
private theorem quotientMap_zero (A B : FilteredObject C) (p : ℤ) :
    quotientMap (0 : A ⟶ B) p = 0 := by
  refine (cancel_epi (cokernel.π (A.filtration.obj p).arrow)).1 ?_
  calc
    cokernel.π (A.filtration.obj p).arrow ≫ quotientMap (0 : A ⟶ B) p
        = (0 : A.obj ⟶ B.obj) ≫ cokernel.π (B.filtration.obj p).arrow :=
            quotientMap_comm (0 : A ⟶ B) p
  _ = 0 := by simp
  _ = cokernel.π (A.filtration.obj p).arrow ≫ 0 := by simp

end FilteredObject.Hom

end HomQuotients

namespace FilteredObject

open Hom

/- Source/core/bridge triage for the functorial filtered-object API:
- source-facing owner: filtration stages, quotients by stages, and associated graded objects
- core/canonical owner: the induced maps `stageMap`, `quotientMap`, and `associatedGradedMap`
  from `FilteredObject.Hom`
- derived API: the corresponding functors and natural comparison maps between stages -/

/-- The `p`-th filtration-stage functor on filtered objects. -/
def stageFunctor (p : ℤ) : FilteredObject C ⥤ C where
  obj A := F^{p} A
  map f := f.stageMap p
  map_id A := stageMap_id A p
  map_comp f g := stageMap_comp f g p

/-- The canonical inclusion of the `p`-th stage into the underlying object, functorially in the
filtered object. -/
def stageFunctorToForget (p : ℤ) :
    (stageFunctor p : FilteredObject C ⥤ C) ⟶
      (FilteredObject.forget : FilteredObject C ⥤ C) where
  app A := (A.filtration.obj p).arrow
  naturality {A B} f := by
    change stageMap f p ≫ (B.filtration.obj p).arrow = (A.filtration.obj p).arrow ≫ f.hom
    exact stageMap_comm f p

-- Proof sketch: compare both composites after postcomposing with the mono inclusion of the
-- target `p`-th filtration stage and use `stageMap_comm` together with `Subobject.ofLE_arrow`.
/-- For `p ≤ q`, the canonical comparison `F^q A ⟶ F^p A` is natural in the filtered object `A`.
-/
private theorem stageMapOfLE_naturality {A B : FilteredObject C} (f : A ⟶ B) {p q : ℤ}
    (hpq : p ≤ q) :
    Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p) (A.filtration.antitone_obj hpq) ≫
      stageMap f p =
        stageMap f q ≫
          Subobject.ofLE (B.filtration.obj q) (B.filtration.obj p)
            (B.filtration.antitone_obj hpq) := sorry

/-- For `p ≤ q`, the `q`-th stage functor maps naturally to the `p`-th stage functor. -/
def stageFunctorMapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (stageFunctor q : FilteredObject C ⥤ C) ⟶ stageFunctor p where
  app A := Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p) (A.filtration.antitone_obj hpq)
  naturality {A B} f := by
    change stageMap f q ≫
        Subobject.ofLE (B.filtration.obj q) (B.filtration.obj p) (B.filtration.antitone_obj hpq) =
      Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p) (A.filtration.antitone_obj hpq) ≫
        stageMap f p
    exact (stageMapOfLE_naturality f hpq).symm

/-- Successive stage comparisons compose to the direct stage comparison. -/
theorem stageFunctorMapOfLE_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    (stageFunctorMapOfLE hqr : (stageFunctor r : FilteredObject C ⥤ C) ⟶ stageFunctor q) ≫
      stageFunctorMapOfLE hpq =
      stageFunctorMapOfLE (le_trans hpq hqr) := by
  ext A
  change
    Subobject.ofLE (A.filtration.obj r) (A.filtration.obj q) (A.filtration.antitone_obj hqr) ≫
      Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p) (A.filtration.antitone_obj hpq) =
    Subobject.ofLE (A.filtration.obj r) (A.filtration.obj p)
      (A.filtration.antitone_obj (le_trans hpq hqr))
  exact
    Subobject.ofLE_comp_ofLE
      (A.filtration.obj r)
      (A.filtration.obj q)
      (A.filtration.obj p)
      (A.filtration.antitone_obj hqr)
      (A.filtration.antitone_obj hpq)

/-- The comparison `F^q A ⟶ F^p A` followed by inclusion into `A` is the usual inclusion
`F^q A ⟶ A`. -/
theorem stageFunctorMapOfLE_comp_stageFunctorToForget {p q : ℤ} (hpq : p ≤ q) :
    (stageFunctorMapOfLE hpq : (stageFunctor q : FilteredObject C ⥤ C) ⟶ stageFunctor p) ≫
      stageFunctorToForget p =
      stageFunctorToForget q := by
  ext A
  exact Subobject.ofLE_arrow (A.filtration.antitone_obj hpq)

section ZeroMorphisms

variable [HasZeroMorphisms C]

/-- Evaluation at a fixed degree preserves zero morphisms on graded objects. -/
instance GradedObject.eval_preservesZeroMorphisms (p : ℤ) :
    (GradedObject.eval p : GradedObject ℤ C ⥤ C).PreservesZeroMorphisms where
  map_zero _ _ := rfl

instance (p : ℤ) : ((stageFunctor p : FilteredObject C ⥤ C)).PreservesZeroMorphisms where
  map_zero A B := stageMap_zero A B p

instance : ((FilteredObject.forget : FilteredObject C ⥤ C)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

end ZeroMorphisms

section Quotients

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The quotient-by-`F^p` functor on filtered objects. -/
def quotientFunctor (p : ℤ) : FilteredObject C ⥤ C where
  obj A := A.quotient p
  map f := f.quotientMap p
  map_id A := quotientMap_id A p
  map_comp f g := quotientMap_comp f g p

instance (p : ℤ) : ((quotientFunctor p : FilteredObject C ⥤ C)).PreservesZeroMorphisms where
  map_zero A B := quotientMap_zero A B p

end Quotients

section Graded

variable [HasZeroMorphisms C] [HasCokernels C]

/-- The associated graded functor on filtered objects. -/
def associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C where
  obj A := A.associatedGraded
  map f := f.associatedGradedMap
  map_id A := associatedGradedMap_id A
  map_comp f g := associatedGradedMap_comp f g

instance [Preadditive C] [Preadditive (GradedObject ℤ C)] :
    (associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C).Additive where
  map_add := by
    intro A B f g
    exact associatedGradedMap_add f g

instance :
    ((associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C)).PreservesZeroMorphisms where
  map_zero A B := associatedGradedMap_zero A B

end Graded

section SubobjectGradedPiece

variable [HasPullbacks C] [HasZeroMorphisms C] [HasImages C] [HasCokernels C]

variable (A : FilteredObject C) (X : Subobject A.obj)

/-- The graded short complex associated to a filtered subobject and its quotient. -/
def subobjectGradedPieceShortComplex (p : ℤ) : ShortComplex C :=
  ShortComplex.mk
    (gradedPieceMap (A.subobjectInclusion X) p)
    (gradedPieceMap (A.toQuotient X) p)
    (gradedPieceMap_comp_zero (A.subobjectInclusion X) (A.toQuotient X)
      (A.subobjectInclusion_comp_toQuotient X) p)

end SubobjectGradedPiece

section Abelian

variable [Abelian C]

variable (A : FilteredObject C) (X : Subobject A.obj)

-- Proof sketch: compare the induced filtration on `X` with the quotient filtration on `A / X`,
-- then compute the middle kernel as `F^p X / F^{p + 1} X`.
/-- Lemma 12.19.12 (1): the induced filtration on a subobject `X ⊆ A` and the quotient
filtration on `A / X` give a short exact sequence
`0 ⟶ gr^p(X) ⟶ gr^p(A) ⟶ gr^p(A / X) ⟶ 0`. -/
theorem gradedPiece_subobject_shortExact (p : ℤ) :
    (subobjectGradedPieceShortComplex A X p).ShortExact := sorry

end Abelian

end FilteredObject

namespace FilteredObject.Hom

open FilteredObject

variable {A B D : FilteredObject C}

section Kernels

variable [HasPullbacks C] [HasZeroMorphisms C] [HasKernels C]

/-- The kernel filtered object, with the filtration induced from the source. -/
abbrev kernelFilteredObject (f : A ⟶ B) : FilteredObject C :=
  A.subobjectFilteredObject (kernelSubobject f.hom)

/-- The canonical inclusion of the filtered kernel into the source filtered object. -/
abbrev kernelι (f : A ⟶ B) : kernelFilteredObject f ⟶ A :=
  A.subobjectInclusion (kernelSubobject f.hom)

/-- The filtered kernel inclusion followed by `f` is zero. -/
theorem kernelι_comp (f : A ⟶ B) :
    kernelι f ≫ f = 0 := sorry

end Kernels

section Cokernels

variable [HasZeroMorphisms C] [HasImages C] [HasCokernels C]

/-- The filtered cokernel of `f`, with the quotient filtration induced by the canonical cokernel
projection `cokernel.π f.hom`. -/
def cokernelFilteredObject (f : A ⟶ B) : FilteredObject C where
  obj := cokernel f.hom
  filtration := B.filtration.quotient (cokernel.π f.hom)

/-- The canonical cokernel projection from the target filtered object to the filtered cokernel. -/
def toCokernel (f : A ⟶ B) : B ⟶ cokernelFilteredObject f where
  hom := cokernel.π f.hom
  preserves := by
    intro p
    sorry

/-- The filtered morphism `f` followed by the filtered cokernel projection is zero. -/
theorem comp_toCokernel (f : A ⟶ B) :
    f ≫ toCokernel f = 0 := sorry

/-- The graded sequence `gr^p(A) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f)`. -/
def sourceTargetCokernelShortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap f p) (gradedPieceMap (toCokernel f) p)
    (gradedPieceMap_comp_zero f (toCokernel f) (comp_toCokernel f) p)

end Cokernels

section KernelCoimage

variable [HasPullbacks C] [HasZeroMorphisms C] [HasKernels C] [HasImages C] [HasCokernels C]

/-- The graded sequence `gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(B)`. -/
def kernelSourceTargetShortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap (kernelι f) p) (gradedPieceMap f p)
    (gradedPieceMap_comp_zero (kernelι f) f (kernelι_comp f) p)

end KernelCoimage

section Abelian

variable [Abelian C]

/-- The filtered kernel inclusion followed by the canonical quotient map onto `coim(f)` is zero. -/
theorem kernelι_comp_toCoimage (f : A ⟶ B) :
    kernelι f ≫ A.toQuotient (kernelSubobject f.hom) = 0 := by
  simpa [kernelι, coimage] using
    A.subobjectInclusion_comp_toQuotient (kernelSubobject f.hom)

/-- The graded sequence `gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(\operatorname{coim} f)`. -/
abbrev kernelCoimageShortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  A.subobjectGradedPieceShortComplex (kernelSubobject f.hom) p

/-- The canonical inclusion of the filtered image into the target filtered object. -/
def imageInclusion (f : A ⟶ B) : image f ⟶ B where
  hom := Abelian.image.ι f.hom
  preserves := by
    intro p
    sorry

/-- The filtered image inclusion followed by the filtered cokernel projection is zero. -/
theorem imageInclusion_comp_toCokernel (f : A ⟶ B) :
    imageInclusion f ≫ toCokernel f = 0 := sorry

/-- The graded sequence `gr^p(\operatorname{im} f) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f)`. -/
def imageCokernelShortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  ShortComplex.mk (gradedPieceMap (imageInclusion f) p) (gradedPieceMap (toCokernel f) p)
    (gradedPieceMap_comp_zero (imageInclusion f) (toCokernel f)
      (imageInclusion_comp_toCokernel f) p)

-- Proof sketch: this is the generic short exact sequence for a filtered subobject and its
-- quotient, applied to the kernel subobject.
/-- Lemma 12.19.12 (2): the induced filtration on `ker(f)` and the quotient filtration on
`coim(f)` give a short exact sequence
`0 ⟶ gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(\operatorname{coim} f) ⟶ 0`. -/
theorem gradedPiece_kernel_coimage_shortExact (f : A ⟶ B) (p : ℤ) :
    (kernelCoimageShortComplex f p).ShortExact := by
  simpa [kernelCoimageShortComplex] using
    A.gradedPiece_subobject_shortExact (kernelSubobject f.hom) p

-- Proof sketch: this is the generic short exact sequence for a filtered subobject and its
-- quotient, applied to the image subobject.
/-- Lemma 12.19.12 (3): the induced filtration on `im(f)` and the quotient filtration on
`coker(f)` give a short exact sequence
`0 ⟶ gr^p(\operatorname{im} f) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f) ⟶ 0`. -/
theorem gradedPiece_image_cokernel_shortExact (f : A ⟶ B) (p : ℤ) :
    (imageCokernelShortComplex f p).ShortExact := sorry

end Abelian

end FilteredObject.Hom

end CategoryTheory
