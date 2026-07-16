import stacks_proof.stacks_project.Chap12.Lemma_12_19_2
import stacks_proof.stacks_project.Chap12.Lemma_12_19_4
import stacks_proof.stacks_project.Chap12.Lemma_12_5_16
import stacks_proof.stacks_project.Chap12.Definition_12_16_1
import Mathlib.Tactic.StacksAttribute

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

section

omit [HasZeroMorphisms C] [HasCokernels C] in
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

end

/-- The induced map on graded pieces preserves addition. -/
private theorem gradedPieceMap_add [Preadditive C] (f g : A ⟶ B) (p : ℤ) :
    gradedPieceMap (f + g) p = gradedPieceMap f p + gradedPieceMap g p := by
  -- Compare after precomposing with the cokernel projection of `gr^p(A)`.
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_add])

/-- The induced map on associated graded objects preserves addition. -/
private theorem associatedGradedMap_add [Preadditive C]
    (f g : A ⟶ B) :
    associatedGradedMap (f + g) = associatedGradedMap f + associatedGradedMap g := by
  -- Proof comment: morphisms in `GradedObject ℤ C` are pointwise, so degreewise additivity is
  -- exactly the additivity of evaluation together with `gradedPieceMap_add`.
  ext p
  have happ :
      (associatedGradedMap f + associatedGradedMap g) p =
        associatedGradedMap f p + associatedGradedMap g p := by
    simpa using
      (Functor.map_add (F := GradedObject.eval p)
        (f := associatedGradedMap f) (g := associatedGradedMap g))
  rw [happ]
  simpa [associatedGradedMap] using gradedPieceMap_add f g p

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

instance [Preadditive C] :
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

/-- Helper for Lemma 12.19.12: the stage map `F^p X ⟶ F^p A` is monic. -/
private theorem stage_subobjectInclusion_mono (p : ℤ) :
    Mono (stageMap (A.subobjectInclusion X) p) := by
  -- Proof comment: cancel the stage map against the two ambient mono arrows defining the pullback
  -- stage of `X`.
  constructor
  intro Z g h w
  apply (cancel_mono (((A.subobjectFilteredObject X).filtration.obj p).arrow)).1
  apply (cancel_mono X.arrow).1
  have w' := congrArg (fun k => k ≫ (A.filtration.obj p).arrow) w
  have w'' :
      (g ≫ ((A.subobjectFilteredObject X).filtration.obj p).arrow) ≫ X.arrow =
        (h ≫ ((A.subobjectFilteredObject X).filtration.obj p).arrow) ≫ X.arrow := by
      simpa [FilteredObject.subobjectInclusion, Category.assoc] using w'
  exact w''

/-- Helper for Lemma 12.19.12: the stage of the induced filtration on `X`, viewed inside
`F^p A`, is the image subobject of the stage inclusion map. -/
private theorem stage_subobject_eq_image (p : ℤ) :
    (Subobject.pullback (A.filtration.obj p).arrow).obj X =
      imageSubobject (stageMap (A.subobjectInclusion X) p) := by
  letI : Mono (stageMap (A.subobjectInclusion X) p) := stage_subobjectInclusion_mono A X p
  have hpullback :
      IsPullback
        (((A.subobjectFilteredObject X).filtration.obj p).arrow)
        (stageMap (A.subobjectInclusion X) p)
        X.arrow
        (A.filtration.obj p).arrow := by
    -- Proof comment: the induced stage `F^p X` is the pullback of `X ↪ A` along `F^p A ↪ A`.
    simpa [stage_subobjectInclusion_eq_pullback_pi] using
      (Subobject.isPullback X.arrow (A.filtration.obj p)).flip
  have hmk :
      (Subobject.pullback (A.filtration.obj p).arrow).obj (Subobject.mk X.arrow) =
        Subobject.mk (stageMap (A.subobjectInclusion X) p) := by
    -- Proof comment: the canonical pullback square identifies the pulled-back subobject with the
    -- subobject cut out by the stage inclusion itself.
    simpa using
      (Subobject.pullback_obj_mk
        (f := (A.filtration.obj p).arrow)
        (i := X.arrow)
        (j := stageMap (A.subobjectInclusion X) p)
        (f' := ((A.subobjectFilteredObject X).filtration.obj p).arrow)
        hpullback)
  -- Proof comment: rewrite both sides in terms of the literal subobject built from the stage
  -- inclusion map.
  calc
    (Subobject.pullback (A.filtration.obj p).arrow).obj X
        = (Subobject.pullback (A.filtration.obj p).arrow).obj (Subobject.mk X.arrow) := by
            simp [Subobject.mk_arrow]
    _ = Subobject.mk (stageMap (A.subobjectInclusion X) p) := hmk
    _ = imageSubobject (stageMap (A.subobjectInclusion X) p) := by
          symm
          simpa using (Limits.imageSubobject_mono (stageMap (A.subobjectInclusion X) p))

/-- Helper for Lemma 12.19.12: the stagewise subobject map followed by the stagewise quotient map
is zero. -/
private theorem stage_subobject_quotient_comp_zero (p : ℤ) :
    stageMap (A.subobjectInclusion X) p ≫ stageMap (A.toQuotient X) p = 0 := by
  rw [← FilteredObject.Hom.stageMap_comp (A.subobjectInclusion X) (A.toQuotient X) p]
  rw [A.subobjectInclusion_comp_toQuotient X, FilteredObject.Hom.stageMap_zero]

/-- Helper for Lemma 12.19.12: each stage quotient map `F^p A ⟶ F^p(A/X)` is an epimorphism. -/
private theorem stage_toQuotient_epi (p : ℤ) :
    Epi (stageMap (A.toQuotient X) p) := by
  let k : (A.filtration p : C) ⟶ cokernel X.arrow :=
    (A.filtration.obj p).arrow ≫ cokernel.π X.arrow
  have hquotient :
      (A.quotientFilteredObject X).filtration p = imageSubobject k := by
    -- Proof comment: rewrite the quotient stage as the image of the stage composite into
    -- `cokernel X.arrow`.
    simpa [FilteredObject.quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp A.filtration
        (cokernel.π X.arrow) p)
  let e : (imageSubobject k : C) ≅ (A.quotientFilteredObject X).filtration p :=
    Subobject.isoOfEq _ _ hquotient.symm
  have he_arrow :
      e.hom ≫ ((A.quotientFilteredObject X).filtration.obj p).arrow =
        (imageSubobject k).arrow := by
    change
      Subobject.ofLE (imageSubobject k) ((A.quotientFilteredObject X).filtration p)
          hquotient.symm.le ≫
        ((A.quotientFilteredObject X).filtration.obj p).arrow =
      (imageSubobject k).arrow
    exact Subobject.ofLE_arrow (h := hquotient.symm.le)
  have hstage :
      factorThruImageSubobject k ≫ e.hom = stageMap (A.toQuotient X) p := by
    -- Proof comment: both maps become the same after postcomposing with the quotient-stage mono.
    have hcomp :
        factorThruImageSubobject k ≫ e.hom ≫ ((A.quotientFilteredObject X).filtration.obj p).arrow =
          stageMap (A.toQuotient X) p ≫ ((A.quotientFilteredObject X).filtration.obj p).arrow := by
      have hleft :
          factorThruImageSubobject k ≫ e.hom ≫ ((A.quotientFilteredObject X).filtration.obj p).arrow =
            k := by
        calc
          factorThruImageSubobject k ≫ e.hom ≫ ((A.quotientFilteredObject X).filtration.obj p).arrow
              = factorThruImageSubobject k ≫ (imageSubobject k).arrow := by
                  simpa [Category.assoc] using
                    congrArg (fun t : (imageSubobject k : C) ⟶ cokernel X.arrow ↦
                      factorThruImageSubobject k ≫ t) he_arrow
          _ = k := by
                exact imageSubobject_arrow_comp k
      have hright :
          k = stageMap (A.toQuotient X) p ≫ ((A.quotientFilteredObject X).filtration.obj p).arrow := by
        change
          (A.filtration.obj p).arrow ≫ cokernel.π X.arrow =
            stageMap (A.toQuotient X) p ≫ ((A.quotientFilteredObject X).filtration.obj p).arrow
        exact (stageMap_comm (A.toQuotient X) p).symm
      exact hleft.trans hright
    apply (cancel_mono ((A.quotientFilteredObject X).filtration.obj p).arrow).1
    simpa [Category.assoc] using hcomp
  rw [← hstage]
  infer_instance

/-- Helper for Lemma 12.19.12: each stage row
`0 ⟶ F^p X ⟶ F^p A ⟶ F^p(A/X) ⟶ 0` is short exact. -/
private theorem stage_subobject_quotient_shortExact (p : ℤ) :
    (ShortComplex.mk
      (stageMap (A.subobjectInclusion X) p)
      (stageMap (A.toQuotient X) p)
      (stage_subobject_quotient_comp_zero A X p)).ShortExact := by
  -- Route correction: compute exactness directly from the untransported kernel/image comparison
  -- at the stage level, then supply the already established mono/epi endpoint facts.
  refine ShortComplex.ShortExact.mk' ?_ (stage_subobjectInclusion_mono A X p) ?_
  · rw [ShortComplex.exact_iff_image_eq_kernel]
    calc
      imageSubobject (stageMap (A.subobjectInclusion X) p)
          = (Subobject.pullback (A.filtration.obj p).arrow).obj X := by
              symm
              exact stage_subobject_eq_image A X p
      _ = (Subobject.pullback (A.filtration.obj p).arrow).obj
            (kernelSubobject (cokernel.π X.arrow)) := by
            exact congrArg ((Subobject.pullback (A.filtration.obj p).arrow).obj)
              (subobject_eq_kernel_cokernel (A := A) (X := X))
      _ = kernelSubobject ((A.filtration.obj p).arrow ≫ cokernel.π X.arrow) := by
            symm
            simpa using
              (kernelSubobject_comp_eq_pullback
                ((A.filtration.obj p).arrow) (cokernel.π X.arrow))
      _ = kernelSubobject ((A.filtration.obj p).arrow ≫ (A.toQuotient X).hom) := by
            rfl
      _ = kernelSubobject (stageMap (A.toQuotient X) p) := by
            simpa using
              (Limits.kernelSubobject_comp_mono
                (stageMap (A.toQuotient X) p)
                (((A.quotientFilteredObject X).filtration.obj p).arrow))
  · exact stage_toQuotient_epi A X p

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
/-- The first exact sequence in Lemma 12.19.12: the induced filtration on a subobject `X ⊆ A` and
the quotient
filtration on `A / X` give a short exact sequence
`0 ⟶ gr^p(X) ⟶ gr^p(A) ⟶ gr^p(A / X) ⟶ 0`. -/
@[stacks 05SP]
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

variable [HasPullbacks C] [HasZeroMorphisms C] [HasImages C] [HasCokernels C]

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
        (cokernelFilteredObject f).filtration p = imageSubobject k := by
      simpa [cokernelFilteredObject, k] using
        (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
          (cokernel.π f.hom) p)
    rw [hquotient]
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

/-- Helper for Lemma 12.19.12: mapping a subobject across an isomorphism agrees with the image of
the composed arrow. -/
private theorem mapIso_obj_eq_imageSubobject {X Y : C} (e : X ≅ Y) (S : Subobject X) :
    (Subobject.map e.hom).obj S = imageSubobject (S.arrow ≫ e.hom) := by
  -- Proof comment: the composite `S ↪ X ⟶ Y` is mono, so its image is represented by that arrow.
  calc
    (Subobject.map e.hom).obj S = (Subobject.map e.hom).obj (Subobject.mk S.arrow) := by
      rw [Subobject.mk_arrow]
    _ = Subobject.mk (S.arrow ≫ e.hom) := by
      rw [Subobject.map_mk]
    _ = imageSubobject (S.arrow ≫ e.hom) := by
      symm
      simpa using Limits.imageSubobject_mono (S.arrow ≫ e.hom)

/-- Helper for Lemma 12.19.12: postcomposing an epimorphism does not change the image subobject.
-/
private theorem imageSubobject_comp_eq_of_epi {X Y Z : C} (g : X ⟶ Y) [Epi g] (h : Y ⟶ Z) :
    imageSubobject (g ≫ h) = imageSubobject h := by
  -- Proof comment: the image of an epimorphism is the top subobject, so only `h` matters.
  calc
    imageSubobject (g ≫ h) = imageSubobject ((imageSubobject g).arrow ≫ h) := by
      rw [Limits.imageSubobject_comp_eq_imageSubobject_restriction g h]
    _ = imageSubobject (((⊤ : Subobject Y)).arrow ≫ h) := by
      simpa using congrArg (fun S : Subobject Y ↦ imageSubobject (S.arrow ≫ h))
        (Limits.imageSubobject_eq_top_of_epi g)
    _ = imageSubobject h := by
      simpa using Limits.imageSubobject_iso_comp ((⊤ : Subobject Y).arrow) h

/-- Helper for Lemma 12.19.12: an ambient codomain isomorphism transports image-factorizations of
the same map. -/
private theorem imageSubobject_factors_of_iso_comp {X Y Y' : C} (k : X ⟶ Y) (e : Y ≅ Y')
    {k' : X ⟶ Y'} (hk : k ≫ e.hom = k') :
    (imageSubobject k').Factors ((imageSubobject k).arrow ≫ e.hom) := by
  -- Proof comment: compare both images after reintroducing the epimorphic factorization of `k`.
  rw [Subobject.factors_iff]
  refine ⟨factorThruImageSubobject ((imageSubobject k).arrow ≫ e.hom) ≫ Subobject.ofLE _ _ ?_, ?_⟩
  · refine le_of_eq ?_
    calc
      imageSubobject ((imageSubobject k).arrow ≫ e.hom)
          = imageSubobject (factorThruImageSubobject k ≫ (imageSubobject k).arrow ≫ e.hom) := by
              symm
              simpa [Category.assoc] using
                (imageSubobject_comp_eq_of_epi (factorThruImageSubobject k)
                  ((imageSubobject k).arrow ≫ e.hom))
      _ = imageSubobject ((factorThruImageSubobject k ≫ (imageSubobject k).arrow) ≫ e.hom) := by
            simp
      _ = imageSubobject (k ≫ e.hom) := by
            rw [imageSubobject_arrow_comp]
      _ = imageSubobject k' := by
            simpa [hk]
  · simp [Category.assoc, Subobject.ofLE_arrow]

/-- Helper for Lemma 12.19.12: the transport from the literal image-subobject owner to the public
`Abelian.image` owner followed by the public image inclusion is the literal inclusion. -/
private theorem imageSubobjectFilteredObjectIsoImage_hom_comp_image_ι (f : A ⟶ B) :
    (imageSubobjectFilteredObjectIsoImage f).hom.hom ≫ Abelian.image.ι f.hom =
      (imageSubobject f.hom).arrow := by
  let e : (imageSubobject f.hom : C) ≅ Abelian.image f.hom :=
    imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
  -- Proof comment: the chosen transport identifies the literal image mono with `Abelian.image.ι`.
  have himage :
      (Abelian.imageIsoImage f.hom).inv ≫ Abelian.image.ι f.hom = Limits.image.ι f.hom := by
    rw [Abelian.imageIsoImage_inv]
    simp
  calc
    (imageSubobjectFilteredObjectIsoImage f).hom.hom ≫ Abelian.image.ι f.hom
        = e.hom ≫ Abelian.image.ι f.hom := by
            rfl
    _ = (imageSubobjectIso f.hom).hom ≫
          ((Abelian.imageIsoImage f.hom).inv ≫ Abelian.image.ι f.hom) := by
            simp [e, Category.assoc]
    _ = (imageSubobjectIso f.hom).hom ≫ Limits.image.ι f.hom := by
          rw [himage]
    _ = (imageSubobject f.hom).arrow := by
          simpa using (Limits.imageSubobject_arrow (f := f.hom))

/-- Helper for Lemma 12.19.12: the inverse transport from the public `Abelian.image` owner back
to the literal image-subobject owner identifies the ambient image inclusion. -/
private theorem imageSubobjectFilteredObjectIsoImage_inv_comp_arrow (f : A ⟶ B) :
    (imageSubobjectFilteredObjectIsoImage f).inv.hom ≫ (imageSubobject f.hom).arrow =
      Abelian.image.ι f.hom := by
  -- Proof comment: expand the inverse transport and then rewrite the literal image-subobject
  -- inclusion as the standard `Limits.image.ι`.
  let e : (imageSubobject f.hom : C) ≅ Abelian.image f.hom :=
    imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm
  change e.inv ≫ (imageSubobject f.hom).arrow = Abelian.image.ι f.hom
  calc
    e.inv ≫ (imageSubobject f.hom).arrow
        = (Abelian.imageIsoImage f.hom).hom ≫
            ((imageSubobjectIso f.hom).inv ≫ (imageSubobject f.hom).arrow) := by
              simp [e, Category.assoc]
    _ = (Abelian.imageIsoImage f.hom).hom ≫ Limits.image.ι f.hom := by
          rw [Limits.imageSubobject_arrow']
    _ = Abelian.image.ι f.hom := by
          simpa using (Abelian.imageIsoImage_hom_comp_image_ι (f := f.hom))

/-- The filtered kernel inclusion followed by the canonical quotient map onto `coim(f)` is zero. -/
theorem kernelι_comp_toCoimage (f : A ⟶ B) :
    kernelι f ≫ A.toQuotient (kernelSubobject f.hom) = 0 := by
  simpa [kernelι] using
    A.subobjectInclusion_comp_toQuotient (kernelSubobject f.hom)

/-- The graded sequence `gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(\operatorname{coim} f)`. -/
abbrev kernelCoimageShortComplex (f : A ⟶ B) (p : ℤ) : ShortComplex C :=
  A.subobjectGradedPieceShortComplex (kernelSubobject f.hom) p

/-- Helper for Lemma 12.19.12: the quotient by the literal image subobject has the same
underlying cokernel as `cokernelFilteredObject f`. -/
private def quotientByImageCokernelIso (f : A ⟶ B) :
    cokernel (imageSubobject f.hom).arrow ≅ cokernel f.hom :=
  -- Proof comment: first replace the literal image-subobject owner by `Limits.image`, then use
  -- the standard ambient cokernel comparison for the image factorization.
  CategoryTheory.Limits.cokernel.mapIso (f := (imageSubobject f.hom).arrow) (f' := image.ι f.hom)
      (imageSubobjectIso f.hom) (Iso.refl _)
      (by simpa using (Limits.imageSubobject_arrow (f := f.hom))) ≪≫
    Limits.cokernelImageι f.hom

/-- Helper for Lemma 12.19.12: the forward cokernel comparison from the literal image-subobject
quotient identifies the two cokernel projections. -/
private theorem quotientByImageCokernelIso_hom_comm (f : A ⟶ B) :
    cokernel.π (imageSubobject f.hom).arrow ≫ (quotientByImageCokernelIso f).hom =
      cokernel.π f.hom := by
  -- Proof comment: both pieces of the cokernel comparison identify the universal quotient map.
  simp [quotientByImageCokernelIso]

/-- Helper for Lemma 12.19.12: the inverse cokernel comparison carries the target cokernel
projection back to the literal image-subobject quotient. -/
private theorem quotientByImageCokernelIso_inv_comm (f : A ⟶ B) :
    cokernel.π f.hom ≫ (quotientByImageCokernelIso f).inv =
      cokernel.π (imageSubobject f.hom).arrow := by
  -- Proof comment: the inverse comparison is the same identification in the opposite direction.
  simp [quotientByImageCokernelIso]

/-- Helper for Lemma 12.19.12: the forward quotient-by-image to cokernel comparison preserves the
quotient filtrations stagewise. -/
-- TODO: rewrite both filtrations as image subobjects of the same stage map and transport along
-- the cokernel comparison square.
private theorem quotientFilteredObjectImageIsoCokernel_hom_preserves (f : A ⟶ B) (p : ℤ) :
    ((cokernelFilteredObject f).filtration p).Factors
      (((B.quotientFilteredObject (imageSubobject f.hom)).filtration p).arrow ≫
        (quotientByImageCokernelIso f).hom) := by
  let k : (B.filtration p : C) ⟶ cokernel (imageSubobject f.hom).arrow :=
    (B.filtration.obj p).arrow ≫ cokernel.π (imageSubobject f.hom).arrow
  let k' : (B.filtration p : C) ⟶ cokernel f.hom :=
    (B.filtration.obj p).arrow ≫ cokernel.π f.hom
  have hstage :
      (B.quotientFilteredObject (imageSubobject f.hom)).filtration p = imageSubobject k := by
    -- Proof comment: rewrite the literal quotient stage as the image of the stage map into the
    -- literal quotient object.
    simpa [FilteredObject.quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
        (cokernel.π (imageSubobject f.hom).arrow) p)
  have hstage' : (cokernelFilteredObject f).filtration p = imageSubobject k' := by
    -- Proof comment: rewrite the public cokernel stage by the same image-subobject normal form.
    simpa [cokernelFilteredObject, k'] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
        (cokernel.π f.hom) p)
  have hk : k ≫ (quotientByImageCokernelIso f).hom = k' := by
    -- Proof comment: the ambient quotient comparison intertwines the two quotient projections.
    simpa [k, k', Category.assoc] using congrArg ((B.filtration.obj p).arrow ≫ ·)
      (quotientByImageCokernelIso_hom_comm f)
  rw [hstage, hstage']
  exact imageSubobject_factors_of_iso_comp k (quotientByImageCokernelIso f) hk

/-- Helper for Lemma 12.19.12: the inverse quotient-by-image to cokernel comparison preserves the
quotient filtrations stagewise. -/
private theorem quotientFilteredObjectImageIsoCokernel_inv_preserves (f : A ⟶ B) (p : ℤ) :
    ((B.quotientFilteredObject (imageSubobject f.hom)).filtration p).Factors
      (((cokernelFilteredObject f).filtration p).arrow ≫
        (quotientByImageCokernelIso f).inv) := by
  let k : (B.filtration p : C) ⟶ cokernel (imageSubobject f.hom).arrow :=
    (B.filtration.obj p).arrow ≫ cokernel.π (imageSubobject f.hom).arrow
  let k' : (B.filtration p : C) ⟶ cokernel f.hom :=
    (B.filtration.obj p).arrow ≫ cokernel.π f.hom
  have hstage :
      (B.quotientFilteredObject (imageSubobject f.hom)).filtration p = imageSubobject k := by
    -- Proof comment: use the literal quotient-stage normal form again.
    simpa [FilteredObject.quotientFilteredObject, k] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
        (cokernel.π (imageSubobject f.hom).arrow) p)
  have hstage' : (cokernelFilteredObject f).filtration p = imageSubobject k' := by
    -- Proof comment: the public cokernel stage has the analogous image-subobject description.
    simpa [cokernelFilteredObject, k'] using
      (DecreasingFiltration.quotient_eq_imageSubobject_comp B.filtration
        (cokernel.π f.hom) p)
  have hk : k' ≫ (quotientByImageCokernelIso f).inv = k := by
    -- Proof comment: the inverse ambient comparison recovers the literal quotient projection.
    simpa [k, k', Category.assoc] using congrArg ((B.filtration.obj p).arrow ≫ ·)
      (quotientByImageCokernelIso_inv_comm f)
  rw [hstage, hstage']
  exact imageSubobject_factors_of_iso_comp k' (quotientByImageCokernelIso f).symm hk

/-- Helper for Lemma 12.19.12: quotienting `B` by the literal image subobject produces the same
filtered object as `cokernelFilteredObject f`. -/
private def quotientFilteredObjectImageIsoCokernel (f : A ⟶ B) :
    B.quotientFilteredObject (imageSubobject f.hom) ≅ cokernelFilteredObject f where
  hom :=
    { hom := (quotientByImageCokernelIso f).hom
      preserves := quotientFilteredObjectImageIsoCokernel_hom_preserves f }
  inv :=
    { hom := (quotientByImageCokernelIso f).inv
      preserves := quotientFilteredObjectImageIsoCokernel_inv_preserves f }
  hom_inv_id := by
    -- Proof comment: the filtered identity is determined by the ambient cokernel identity.
    apply FilteredObject.Hom.ext
    exact (quotientByImageCokernelIso f).hom_inv_id
  inv_hom_id := by
    -- Proof comment: likewise for the inverse followed by the forward map.
    apply FilteredObject.Hom.ext
    exact (quotientByImageCokernelIso f).inv_hom_id

/-- Helper for Lemma 12.19.12: the ambient image inclusion preserves the induced filtration on
`image f`. -/
private theorem imageInclusion_preserves (f : A ⟶ B) (p : ℤ) :
    (B.filtration p).Factors (((image f).filtration p).arrow ≫ Abelian.image.ι f.hom) := by
  let g : image f ⟶ B :=
    (imageSubobjectFilteredObjectIsoImage f).inv ≫ B.subobjectInclusion (imageSubobject f.hom)
  have hg : g.hom = Abelian.image.ι f.hom := by
    -- Proof comment: the filtered composite has the desired ambient map by the owner comparison.
    change (imageSubobjectFilteredObjectIsoImage f).inv.hom ≫ (imageSubobject f.hom).arrow =
      Abelian.image.ι f.hom
    exact imageSubobjectFilteredObjectIsoImage_inv_comp_arrow f
  -- Proof comment: reuse the already filtered literal image inclusion after transporting back
  -- from the public image owner.
  simpa [g, hg] using g.preserves p

/-- The canonical inclusion of the filtered image into the target filtered object. -/
def imageInclusion (f : A ⟶ B) : image f ⟶ B where
  hom := Abelian.image.ι f.hom
  preserves := imageInclusion_preserves f

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

/-- Helper for Lemma 12.19.12: the graded row for the literal image subobject transports to the
public `image/cokernel` row. -/
private def imageCokernelShortComplexIso (f : A ⟶ B) (p : ℤ) :
    B.subobjectGradedPieceShortComplex (imageSubobject f.hom) p ≅ imageCokernelShortComplex f p := by
  let e₁ : gr^{p} (B.subobjectFilteredObject (imageSubobject f.hom)) ≅ gr^{p} (image f) :=
    (GradedObject.eval p).mapIso
      ((associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C).mapIso
        (imageSubobjectFilteredObjectIsoImage f))
  let e₃ : gr^{p} (B.quotientFilteredObject (imageSubobject f.hom)) ≅
      gr^{p} (cokernelFilteredObject f) :=
    (GradedObject.eval p).mapIso
      ((associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C).mapIso
        (quotientFilteredObjectImageIsoCokernel f))
  have hleft :
      (imageSubobjectFilteredObjectIsoImage f).hom ≫ imageInclusion f =
        B.subobjectInclusion (imageSubobject f.hom) := by
    -- Proof comment: after transporting to the public image owner, the inclusion into `B` is the
    -- literal subobject inclusion.
    apply FilteredObject.Hom.ext
    simpa [imageInclusion, FilteredObject.subobjectInclusion] using
      imageSubobjectFilteredObjectIsoImage_hom_comp_image_ι f
  have hright :
      B.toQuotient (imageSubobject f.hom) ≫ (quotientFilteredObjectImageIsoCokernel f).hom =
        toCokernel f := by
    -- Proof comment: the ambient quotient comparison identifies the public cokernel projection
    -- with the literal quotient projection.
    apply FilteredObject.Hom.ext
    simpa [FilteredObject.toQuotient, toCokernel] using
      quotientByImageCokernelIso_hom_comm f
  have hleft_grad :
      e₁.hom ≫ gradedPieceMap (imageInclusion f) p =
        gradedPieceMap (B.subobjectInclusion (imageSubobject f.hom)) p := by
    -- Proof comment: apply the graded-piece functor to the filtered equality on the left.
    simpa [e₁, gradedPieceMap_comp] using
      congrArg (fun k : B.subobjectFilteredObject (imageSubobject f.hom) ⟶ B ↦ gradedPieceMap k p)
        hleft
  have hright_grad :
      gradedPieceMap (toCokernel f) p =
        gradedPieceMap (B.toQuotient (imageSubobject f.hom)) p ≫ e₃.hom := by
    -- Proof comment: likewise on the quotient side.
    simpa [e₃, gradedPieceMap_comp] using
      (congrArg (fun k : B ⟶ cokernelFilteredObject f ↦ gradedPieceMap k p) hright).symm
  refine ShortComplex.isoMk e₁ (Iso.refl _) e₃ ?_ ?_
  · simpa [imageCokernelShortComplex, FilteredObject.subobjectGradedPieceShortComplex] using
      hleft_grad
  · simpa [imageCokernelShortComplex, FilteredObject.subobjectGradedPieceShortComplex] using
      hright_grad

-- Proof sketch: this is the generic short exact sequence for a filtered subobject and its
-- quotient, applied to the kernel subobject.
/-- The second exact sequence in Lemma 12.19.12: the induced filtration on `ker(f)` and the
quotient filtration on
`coim(f)` give a short exact sequence
`0 ⟶ gr^p(\ker f) ⟶ gr^p(A) ⟶ gr^p(\operatorname{coim} f) ⟶ 0`. -/
@[stacks 05SP]
theorem gradedPiece_kernel_coimage_shortExact (f : A ⟶ B) (p : ℤ) :
    (kernelCoimageShortComplex f p).ShortExact := by
  simpa [kernelCoimageShortComplex] using
    A.gradedPiece_subobject_shortExact (kernelSubobject f.hom) p

-- Proof sketch: this is the generic short exact sequence for a filtered subobject and its
-- quotient, applied to the image subobject.
/-- Lemma 12.19.12 (3): the induced filtration on `im(f)` and the quotient filtration on
`coker(f)` give a short exact sequence
`0 ⟶ gr^p(\operatorname{im} f) ⟶ gr^p(B) ⟶ gr^p(\operatorname{coker} f) ⟶ 0`. -/
@[stacks 05SP]
-- TODO: transport `B.gradedPiece_subobject_shortExact (imageSubobject f.hom) p` through
-- `imageSubobjectFilteredObjectIsoImage f` on the left and
-- `quotientFilteredObjectImageIsoCokernel f` on the right.
theorem gradedPiece_image_cokernel_shortExact (f : A ⟶ B) (p : ℤ) :
    (imageCokernelShortComplex f p).ShortExact := by
  -- Route correction: transport the already-proved literal subobject row through the filtered
  -- image-owner and cokernel-owner isomorphisms, then read it on graded pieces.
  exact ShortComplex.shortExact_of_iso (imageCokernelShortComplexIso f p)
    (B.gradedPiece_subobject_shortExact (imageSubobject f.hom) p)

end Abelian

end FilteredObject.Hom

end CategoryTheory
