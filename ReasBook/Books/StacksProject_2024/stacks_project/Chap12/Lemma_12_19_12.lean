import StacksProject_2024.Chap12.Lemma_12_19_2
import StacksProject_2024.Chap12.Lemma_12_19_4
import StacksProject_2024.Chap12.Lemma_12_5_16

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
    stageMap (f + g) p = stageMap f p + stageMap g p := by
  -- Compare both stage maps after postcomposing with the mono inclusion into `B`.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    calc
      stageMap (f + g) p ≫ (B.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f + g).hom := by
              rw [stageMap_comm]
      _ = (A.filtration.obj p).arrow ≫ f.hom + (A.filtration.obj p).arrow ≫ g.hom := by
            simp
      _ = (stageMap f p + stageMap g p) ≫ (B.filtration.obj p).arrow := by
            rw [Preadditive.add_comp, stageMap_comm, stageMap_comm])

/-- The induced map on graded pieces preserves addition. -/
private theorem gradedPieceMap_add [Preadditive C] (f g : A ⟶ B) (p : ℤ) :
    gradedPieceMap (f + g) p = gradedPieceMap f p + gradedPieceMap g p := by
  -- Compare after precomposing with the cokernel projection of `gr^p(A)`.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_add])

/-- The induced map on associated graded objects preserves addition. -/
private theorem associatedGradedMap_add [Preadditive C] [Preadditive (GradedObject ℤ C)]
    (f g : A ⟶ B) :
    associatedGradedMap (f + g) = associatedGradedMap f + associatedGradedMap g := by
  sorry

-- Proof sketch: after composing with the two cokernel projections, both sides are induced from the
-- zero composite `f ≫ g = 0` in the filtered category.
/-- A zero composite of filtered morphisms induces a zero composite on graded pieces. -/
theorem gradedPieceMap_comp_zero (f : A ⟶ B) (g : B ⟶ D) (hcomp : f ≫ g = 0) (p : ℤ) :
    gradedPieceMap f p ≫ gradedPieceMap g p = 0 := by
  -- Rewrite through composition and reduce to the graded map of the zero morphism.
  rw [← gradedPieceMap_comp f g p, hcomp, gradedPieceMap_zero]

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
            (B.filtration.antitone_obj hpq) := by
  -- Postcompose with the mono inclusion of `F^p B` and use the defining commutative squares.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    calc
      (Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p)
          (A.filtration.antitone_obj hpq) ≫
          stageMap f p) ≫
          (B.filtration.obj p).arrow
          = Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p)
              (A.filtration.antitone_obj hpq) ≫
              (A.filtration.obj p).arrow ≫ f.hom := by
                rw [Category.assoc, stageMap_comm]
      _ = (A.filtration.obj q).arrow ≫ f.hom := by
            simp
      _ = stageMap f q ≫ (B.filtration.obj q).arrow := by
            rw [stageMap_comm]
      _ =
          (stageMap f q ≫
            Subobject.ofLE (B.filtration.obj q) (B.filtration.obj p)
              (B.filtration.antitone_obj hpq)) ≫
            (B.filtration.obj p).arrow := by
              simp [Category.assoc, Subobject.ofLE_arrow])

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

/-- Helper for Lemma 12.19.12: the kernel of a composite is the pullback of the kernel of the
second morphism along the first morphism. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru (kernelSubobject (f ≫ g)).arrow
        ?_)
      ?_
    · exact
        (pullback_factors_iff f (kernelSubobject g) (kernelSubobject (f ≫ g)).arrow).2 <| by
        rw [kernelSubobject_factors_iff, Category.assoc]
        exact kernelSubobject_arrow_comp (f ≫ g)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

/-- Helper for Lemma 12.19.12: a subobject arrow identifies with the kernel of its cokernel. -/
private theorem subobject_eq_kernel_cokernel :
    X = kernelSubobject (cokernel.π X.arrow) := by
  calc
    X = imageSubobject X.arrow := by
      symm
      simpa using (Limits.imageSubobject_mono X.arrow)
    _ = kernelSubobject (cokernel.π X.arrow) := by
      simpa using
        (ShortComplex.exact_iff_image_eq_kernel
          (ShortComplex.mk X.arrow (cokernel.π X.arrow) (cokernel.condition X.arrow))).1
          (ShortComplex.exact_cokernel X.arrow)

/-- Helper for Lemma 12.19.12: on the induced filtration of `X`, the stage map into `F^p A`
is the canonical pullback projection. -/
private theorem stage_subobjectInclusion_eq_pullback_pi (p : ℤ) :
    stageMap (A.subobjectInclusion X) p =
      Subobject.pullbackπ X.arrow (A.filtration.obj p) := by
  -- Both arrows are characterized by the same pullback square into `A`.
  refine (cancel_mono (A.filtration.obj p).arrow).1 ?_
  calc
    stageMap (A.subobjectInclusion X) p ≫ (A.filtration.obj p).arrow
        = ((A.subobjectFilteredObject X).filtration.obj p).arrow ≫ X.arrow := by
            simpa [FilteredObject.subobjectInclusion] using stageMap_comm (A.subobjectInclusion X) p
    _ = Subobject.pullbackπ X.arrow (A.filtration.obj p) ≫ (A.filtration.obj p).arrow := by
          simpa using (Subobject.isPullback X.arrow (A.filtration.obj p)).w.symm

/-- Helper for Lemma 12.19.12: the stagewise subobject map followed by the stagewise quotient map
is zero. -/
private theorem stage_subobject_quotient_comp_zero (p : ℤ) :
    stageMap (A.subobjectInclusion X) p ≫ stageMap (A.toQuotient X) p = 0 := by
  rw [← FilteredObject.Hom.stageMap_comp (A.subobjectInclusion X) (A.toQuotient X) p]
  rw [A.subobjectInclusion_comp_toQuotient X, FilteredObject.Hom.stageMap_zero]

/-- Helper for Lemma 12.19.12: each stage quotient map `F^p A ⟶ F^p(A/X)` is an epimorphism. -/
private theorem stage_toQuotient_epi (p : ℤ) :
    Epi (stageMap (A.toQuotient X) p) := by
  sorry

/-- Helper for Lemma 12.19.12: the stage row
`F^p X ⟶ F^p A ⟶ F^p (A/X)` is a kernel sequence. -/
private theorem stage_subobject_quotient_isKernel (p : ℤ) :
    Nonempty
      (IsLimit
        (KernelFork.ofι
          (stageMap (A.subobjectInclusion X) p)
          (stage_subobject_quotient_comp_zero A X p))) := by
  sorry

/-- Helper for Lemma 12.19.12: each stage row
`0 ⟶ F^p X ⟶ F^p A ⟶ F^p(A/X) ⟶ 0` is short exact. -/
private theorem stage_subobject_quotient_shortExact (p : ℤ) :
    (ShortComplex.mk
      (stageMap (A.subobjectInclusion X) p)
      (stageMap (A.toQuotient X) p)
      (stage_subobject_quotient_comp_zero A X p)).ShortExact := by
  let S : ShortComplex C :=
    ShortComplex.mk
      (stageMap (A.subobjectInclusion X) p)
      (stageMap (A.toQuotient X) p)
      (stage_subobject_quotient_comp_zero A X p)
  -- The left map is a kernel, hence exact and mono.
  have hKernel : IsLimit (KernelFork.ofι S.f S.zero) := by
    exact (stage_subobject_quotient_isKernel A X p).some
  have hExactMono : S.Exact ∧ Mono S.f := by
    exact (S.exact_and_mono_f_iff_f_is_kernel).2 ⟨hKernel⟩
  -- The right map is an image factorization, hence an epimorphism.
  have hEpi : Epi S.g := by
    simpa [S] using stage_toQuotient_epi A X p
  exact ShortComplex.ShortExact.mk' hExactMono.1 hExactMono.2 hEpi

/-- Helper for Lemma 12.19.12: after passing from the `(p+1)` stage row to the `p` stage row,
the resulting cokernel row is exact. -/
private theorem gradedPiece_subobject_exact (p : ℤ) :
    (subobjectGradedPieceShortComplex A X p).Exact := by
  let Ssucc : ShortComplex C :=
    ShortComplex.mk
      (stageMap (A.subobjectInclusion X) (p + 1))
      (stageMap (A.toQuotient X) (p + 1))
      (stage_subobject_quotient_comp_zero A X (p + 1))
  let Scur : ShortComplex C :=
    ShortComplex.mk
      (stageMap (A.subobjectInclusion X) p)
      (stageMap (A.toQuotient X) p)
      (stage_subobject_quotient_comp_zero A X p)
  let φ : Ssucc ⟶ Scur :=
    ShortComplex.homMk
      ((A.subobjectFilteredObject X).filtration.stageInclusion p)
      (A.filtration.stageInclusion p)
      ((A.quotientFilteredObject X).filtration.stageInclusion p)
      (FilteredObject.Hom.stageInclusion_naturality (A.subobjectInclusion X) p)
      (FilteredObject.Hom.stageInclusion_naturality (A.toQuotient X) p)
  have hScur : Scur.ShortExact := by
    simpa [Scur] using stage_subobject_quotient_shortExact A X p
  have hSsucc : Ssucc.ShortExact := by
    simpa [Ssucc] using stage_subobject_quotient_shortExact A X (p + 1)
  letI : Epi Ssucc.g := hSsucc.epi_g
  simpa [subobjectGradedPieceShortComplex, FilteredObject.Hom.gradedPieceMap, Ssucc, Scur, φ] using
    CategoryTheory.cokernel_sequence_exact_of_exact_of_epi φ hScur.exact

/-- Helper for Lemma 12.19.12: the induced map `gr^p(X) ⟶ gr^p(A)` is monic. -/
private theorem gradedPiece_subobject_mono (p : ℤ) :
    Mono (FilteredObject.Hom.gradedPieceMap (A.subobjectInclusion X) p) := by
  have hright :
      IsPullback
        (((A.subobjectFilteredObject X).filtration.obj p).arrow)
        (stageMap (A.subobjectInclusion X) p)
        X.arrow
        (A.filtration.obj p).arrow := by
    -- Proof comment: `F^p X` is the pullback of `X ↪ A` along `F^p A ↪ A`.
    simpa [stage_subobjectInclusion_eq_pullback_pi] using
      (Subobject.isPullback X.arrow (A.filtration.obj p)).flip
  have hbig :
      IsPullback
        (((A.subobjectFilteredObject X).filtration.obj (p + 1)).arrow)
        (stageMap (A.subobjectInclusion X) (p + 1))
        X.arrow
        (A.filtration.obj (p + 1)).arrow := by
    -- Proof comment: the same pullback description applies one stage lower.
    simpa [stage_subobjectInclusion_eq_pullback_pi] using
      (Subobject.isPullback X.arrow (A.filtration.obj (p + 1))).flip
  have hpullback :
      IsPullback
        ((A.subobjectFilteredObject X).filtration.stageInclusion p)
        (stageMap (A.subobjectInclusion X) (p + 1))
        (stageMap (A.subobjectInclusion X) p)
        (A.filtration.stageInclusion p) := by
    -- Proof comment: paste the pullback squares for `F^{p + 1} X` and `F^p X`.
    exact (hright.paste_horiz_iff
      (FilteredObject.Hom.stageInclusion_naturality (A.subobjectInclusion X) p)).1 <| by
      simpa [DecreasingFiltration.stageInclusion, Category.assoc] using hbig
  -- Proof comment: a pullback square of stage inclusions induces a mono on the cokernel map.
  simpa [FilteredObject.Hom.gradedPieceMap] using
    (Abelian.mono_cokernel_map_of_isPullback hpullback)

/-- Helper for Lemma 12.19.12: the induced map `gr^p(A) ⟶ gr^p(A / X)` is epic. -/
private theorem gradedPiece_toQuotient_epi (p : ℤ) :
    Epi (FilteredObject.Hom.gradedPieceMap (A.toQuotient X) p) := by
  have hfac :
      cokernel.π (A.filtration.stageInclusion p) ≫
          FilteredObject.Hom.gradedPieceMap (A.toQuotient X) p =
        stageMap (A.toQuotient X) p ≫
          cokernel.π ((A.quotientFilteredObject X).filtration.stageInclusion p) := by
    -- Proof comment: this is the defining factorization equation of the induced graded map.
    simp [FilteredObject.Hom.gradedPieceMap]
  -- Proof comment: the target quotient projection is epi, so its factor through `gr^p(A / X)` is
  -- epi as well.
  letI : Epi (stageMap (A.toQuotient X) p) := stage_toQuotient_epi A X p
  exact epi_of_epi_fac hfac

-- Proof sketch: compare the induced filtration on `X` with the quotient filtration on `A / X`,
-- then compute the middle kernel as `F^p X / F^{p + 1} X`.
/-- Lemma 12.19.12 (1): the induced filtration on a subobject `X ⊆ A` and the quotient
filtration on `A / X` give a short exact sequence
`0 ⟶ gr^p(X) ⟶ gr^p(A) ⟶ gr^p(A / X) ⟶ 0`. -/
theorem gradedPiece_subobject_shortExact (p : ℤ) :
    (subobjectGradedPieceShortComplex A X p).ShortExact := by
  -- Route correction: after proving exactness of the graded row directly from the stage short
  -- exact rows, the remaining source-faithful work is only the injectivity and surjectivity of the
  -- endpoint maps.
  exact ShortComplex.ShortExact.mk'
    (gradedPiece_subobject_exact A X p)
    (gradedPiece_subobject_mono A X p)
    (gradedPiece_toQuotient_epi A X p)

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
    kernelι f ≫ f = 0 := by
  -- This is the ambient kernel identity, viewed in the filtered category.
  apply FilteredObject.forget.map_injective
  change (kernelSubobject f.hom).arrow ≫ f.hom = 0
  simpa using kernelSubobject_arrow_comp f.hom

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
    -- The quotient filtration stage is the image subobject of the stage composite into the
    -- cokernel, so its universal image factorization yields the required stagewise map.
    let k : (B.filtration p : C) ⟶ cokernel f.hom :=
      (B.filtration.obj p).arrow ≫ cokernel.π f.hom
    have hquotient :
        B.filtration.quotient (cokernel.π f.hom) p = imageSubobject k := by
      apply Subobject.eq_of_comm
        (Subobject.existsIsoImage (cokernel.π f.hom) (B.filtration p) ≪≫
          (imageSubobjectIso k).symm)
      calc
        ((Subobject.existsIsoImage (cokernel.π f.hom) (B.filtration p)).hom ≫
            (imageSubobjectIso k).inv) ≫
            (imageSubobject k).arrow
            = (Subobject.existsIsoImage (cokernel.π f.hom) (B.filtration p)).hom ≫ image.ι k := by
                simp [Category.assoc]
        _ = ((Subobject.exists (cokernel.π f.hom)).obj (B.filtration p)).arrow := by
              simpa [k, Subobject.existsIsoImage] using
                (Over.w ((Subobject.existsCompRepresentativeIso (cokernel.π f.hom)).app
                  (B.filtration p)).hom.hom)
    rw [show (cokernelFilteredObject f).filtration p = imageSubobject k by
      simpa [cokernelFilteredObject, DecreasingFiltration.quotient] using hquotient]
    simpa [k, imageSubobject_arrow_comp] using
      (Subobject.factors_comp_arrow (factorThruImageSubobject k))

/-- The filtered morphism `f` followed by the filtered cokernel projection is zero. -/
theorem comp_toCokernel (f : A ⟶ B) :
    f ≫ toCokernel f = 0 := by
  -- This is the ambient cokernel identity, viewed in the filtered category.
  apply FilteredObject.forget.map_injective
  change f.hom ≫ cokernel.π f.hom = 0
  simpa using cokernel.condition f.hom

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

/-- Helper for Lemma 12.19.12: the canonical image inclusion preserves the transported filtration
on the filtered image. -/
private theorem image_inclusion_preserves_filtration_stage (f : A ⟶ B) (p : ℤ) :
    (B.filtration p).Factors (((image f).filtration p).arrow ≫ Abelian.image.ι f.hom) := by
  sorry

/-- The canonical inclusion of the filtered image into the target filtered object. -/
def imageInclusion (f : A ⟶ B) : image f ⟶ B where
  hom := Abelian.image.ι f.hom
  preserves := image_inclusion_preserves_filtration_stage f

/-- The filtered image inclusion followed by the filtered cokernel projection is zero. -/
theorem imageInclusion_comp_toCokernel (f : A ⟶ B) :
    imageInclusion f ≫ toCokernel f = 0 := by
  -- This is the ambient image-to-cokernel zero composite, viewed in the filtered category.
  apply FilteredObject.forget.map_injective
  change Abelian.image.ι f.hom ≫ cokernel.π f.hom = 0
  simpa using Abelian.image_ι_comp_eq_zero (cokernel.condition f.hom)

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
    -- TODO: identify `imageCokernelShortComplex` with the generic subobject complex for the
    -- image subobject of `f.hom`, then transport `gradedPiece_subobject_shortExact` across that
    -- comparison isomorphism.
    (imageCokernelShortComplex f p).ShortExact := sorry

end Abelian

end FilteredObject.Hom

end CategoryTheory
