import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_12_19_9 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem subobjectSubquotientProjection_condition {A : C} {X Y : Subobject A}
    (hXY : X ≤ Y) :
    (Y.arrow ≫ cokernel.π X.arrow) ≫ subobjectQuotientMap hXY = 0 := by
  simp [subobjectQuotientMap, Category.assoc]

namespace FilteredObject

variable (A : FilteredObject C)
variable {X Y : Subobject A.obj}

/-
Source/core/bridge triage for Lemma 12.19.9:
- source-facing: the filtered subquotient `Y / X` for `X ≤ Y ≤ A` and the canonical filtered map
  `Y ⟶ Y / X`
- core/canonical owners: `subobjectFilteredObject`, `quotientFilteredObject`,
  `FilteredObject.Hom.Strict`, `strict_iff_induced_filtration_of_mono`,
  `strict_iff_quotient_filtration_of_epi`, `strict_comp_of_mono`, `strict_comp_of_epi`
- bridge/view: the induced filtered map `X ⟶ Y`; the maps `Y ⟶ A / X` and `Y / X ⟶ A / X`
  are expressed directly by the ambient owner maps `subobjectInclusion` and `toQuotient`
- primitive data: the inclusion `hXY : X ≤ Y` and the canonical subobject
  `subobjectSubquotientSubobject hXY ⊆ A / X`
- derived API: the strictness lemmas for the canonical maps in this subquotient square
-/

/-- The canonical map of filtered subobjects induced by an inclusion `X ≤ Y` inside `A`. -/
def subobjectInclusionOfLE (hXY : X ≤ Y) :
    A.subobjectFilteredObject X ⟶ A.subobjectFilteredObject Y where
  hom := Subobject.ofLE X Y hXY
  preserves := by
    intro p
    sorry

/-- The canonical filtered object on the subquotient `Y / X = subobjectSubquotient hXY`, viewed
as the canonical subobject `subobjectSubquotientSubobject hXY` of `A / X` with the induced
filtration from the quotient filtration on `A / X`. -/
abbrev subobjectSubquotientFilteredObject (hXY : X ≤ Y) :
    FilteredObject C :=
  (A.quotientFilteredObject X).subobjectFilteredObject (subobjectSubquotientSubobject hXY)

/-- The canonical filtered projection `Y ⟶ Y / X`. -/
def subobjectToSubquotient (hXY : X ≤ Y) :
    A.subobjectFilteredObject Y ⟶ A.subobjectSubquotientFilteredObject hXY where
  hom :=
    factorThruKernelSubobject (subobjectQuotientMap hXY) (Y.arrow ≫ cokernel.π X.arrow)
      (subobjectSubquotientProjection_condition hXY)
  preserves := by
    intro p
    sorry

-- Proof sketch: on each stage, the quotient filtration from `Y` computes
-- `(Y ∩ F^p A) / (X ∩ F^p A)`, while the induced filtration from `A / X` computes the kernel of
-- `(F^p A / (X ∩ F^p A)) ⟶ (F^p A / (Y ∩ F^p A))`; these are the same subobject of `Y / X`.
/-- Lemma 12.19.9: on the canonical subquotient `Y / X`, the quotient filtration from the induced
filtration on `Y` agrees stagewise with the filtration induced from the quotient filtration on
`A / X`. -/
theorem subquotient_quotient_filtration_eq_induced_filtration (hXY : X ≤ Y) :
    (A.filtration.induced Y).quotient (A.subobjectToSubquotient hXY).hom =
      (A.subobjectSubquotientFilteredObject hXY).filtration := by
  sorry

end FilteredObject

namespace FilteredObject.Hom

open FilteredObject

variable (A : FilteredObject C)
variable {X Y : Subobject A.obj}

/-- Lemma 12.19.9: the canonical map `X ⟶ Y` between induced filtered subobjects is strict. -/
theorem strict_subobjectInclusionOfLE (hXY : X ≤ Y) :
    Strict (A.subobjectInclusionOfLE hXY) := by
  sorry

/-- Lemma 12.19.9: the canonical projection `Y ⟶ Y / X` is strict for the induced and subquotient
filtrations. -/
theorem strict_subobjectToSubquotient (hXY : X ≤ Y) :
    Strict (A.subobjectToSubquotient hXY) := by
  sorry

/-- Lemma 12.19.9: the canonical inclusion `Y / X ⟶ A / X` is strict for the induced
filtrations. -/
theorem strict_subobjectSubquotientInclusion (hXY : X ≤ Y) :
    Strict
      ((A.quotientFilteredObject X).subobjectInclusion (subobjectSubquotientSubobject hXY)) := by
  sorry

/-- Lemma 12.19.9: when `X ≤ Y`, the canonical map `Y ⟶ A / X` is strict for the induced and
quotient filtrations. -/
theorem strict_subobjectToQuotient (hXY : X ≤ Y) :
    Strict (A.subobjectInclusion Y ≫ A.toQuotient X) := by
  sorry

end FilteredObject.Hom

end CategoryTheory

/-! ### Lemma_12_19_10 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

open FilteredObject.Hom

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.10:
- source-facing: strictness of the right map in a filtered pushout square, and the resulting
  existence statement
- core/canonical owner: `IsPushout f g g' f'`, specialized to `HasPushout f g` and `pushout.inr f g`
- bridge/view: the stagewise-image filtration model on the ambient pushout of `f.hom` and `g.hom`
-/

private noncomputable def pushoutStageMap (f : A ⟶ B) (g : A ⟶ C) (p : ℤ) :
    ((B.filtration p : 𝒜) ⊞ (C.filtration p : 𝒜)) ⟶ pushout f.hom g.hom :=
  biprod.desc
    ((B.filtration p).arrow ≫ pushout.inl f.hom g.hom)
    ((C.filtration p).arrow ≫ pushout.inr f.hom g.hom)

private theorem pushoutFiltration_antitone (f : A ⟶ B) (g : A ⟶ C) :
    Antitone fun p ↦ imageSubobject (pushoutStageMap f g p) := by
  sorry

private noncomputable def pushoutModel (f : A ⟶ B) (g : A ⟶ C) : FilteredObject 𝒜 where
  obj := pushout f.hom g.hom
  filtration :=
    { toFun := fun p ↦ imageSubobject (pushoutStageMap f g p)
      monotone' := by
        intro p q hpq
        exact pushoutFiltration_antitone f g hpq }

private theorem pushoutModelInl_preserves (f : A ⟶ B) (g : A ⟶ C) :
    ∀ p : ℤ,
      ((pushoutModel f g).filtration p).Factors
        ((B.filtration p).arrow ≫ pushout.inl f.hom g.hom) :=
  by
    sorry

private theorem pushoutModelInr_preserves (f : A ⟶ B) (g : A ⟶ C) :
    ∀ p : ℤ,
      ((pushoutModel f g).filtration p).Factors
        ((C.filtration p).arrow ≫ pushout.inr f.hom g.hom) :=
  by
    sorry

private noncomputable def pushoutModelInl (f : A ⟶ B) (g : A ⟶ C) : B ⟶ pushoutModel f g where
  hom := pushout.inl f.hom g.hom
  preserves := pushoutModelInl_preserves f g

private noncomputable def pushoutModelInr (f : A ⟶ B) (g : A ⟶ C) : C ⟶ pushoutModel f g where
  hom := pushout.inr f.hom g.hom
  preserves := pushoutModelInr_preserves f g

private theorem pushoutModel_isPushout (f : A ⟶ B) (g : A ⟶ C) :
    IsPushout f g (pushoutModelInl f g) (pushoutModelInr f g) := by
  sorry

noncomputable instance hasPushout (f : A ⟶ B) (g : A ⟶ C) : HasPushout f g :=
  (pushoutModel_isPushout f g).hasPushout

/-- In a pushout square of filtered objects, strictness of the left map forces strictness of the
right map. -/
theorem strict_inr_of_isPushout_of_strict
    {P : FilteredObject 𝒜} {g' : B ⟶ P} {f' : C ⟶ P}
    (sq : IsPushout f g g' f') (hf : Strict f) :
    Strict f' := by
  sorry

/-- In the canonical pushout square of filtered objects, strictness of the left map forces
strictness of the induced map on the right. -/
theorem strict_pushout_inr_of_strict (f : A ⟶ B) (g : A ⟶ C) (hf : Strict f) :
    Strict (pushout.inr f g : C ⟶ pushout f g) := by
  exact strict_inr_of_isPushout_of_strict (IsPushout.of_hasPushout f g) hf

end FilteredObject.Hom

-- Proof sketch: first realize the filtered pushout by endowing the ambient pushout of `f.hom` and
-- `g.hom` with the stagewise image filtration coming from `F^p B ⊕ F^p C`; this yields the
-- canonical `HasPushout f g` instance. The strictness statement is proved first for an arbitrary
-- pushout square via `strict_inr_of_isPushout_of_strict`, then specialized to `pushout.inr f g`.
/-- Lemma 12.19.10: for morphisms `f : A ⟶ B` and `g : A ⟶ C` of filtered objects in an abelian
category, there exists a pushout square in the filtered category, and if `f` is strict, then the
induced morphism `f' : C ⟶ C ⨿_A B` is strict. -/
theorem exists_filtered_pushout_preserving_strictness
    {A B C : FilteredObject 𝒜} (f : A ⟶ B) (g : A ⟶ C) :
    ∃ (P : FilteredObject 𝒜) (g' : B ⟶ P) (f' : C ⟶ P),
      IsPushout f g g' f' ∧ (Strict f → Strict f') := by
  refine ⟨pushout f g, pushout.inl f g, pushout.inr f g, IsPushout.of_hasPushout f g, ?_⟩
  exact strict_pushout_inr_of_strict f g

end CategoryTheory

/-! ### Lemma_12_19_11 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

open FilteredObject.Hom

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.11:
- source-facing: existence of a filtered pullback square with strict projection to `C`
- core/canonical owner: `IsPullback g' f' f g`, together with the chosen `HasPullback f g`
- primitive data: the canonical comparison morphism `B ⊞ C ⟶ A`
  induced by `(f, -g)`
- bridge/view: the kernel model of that comparison morphism inside `B ⊞ C`,
  together with the derived projections to `B` and `C`
-/

private abbrev pullbackDifference (f : B ⟶ A) (g : C ⟶ A) :
    (B ⊞ C : FilteredObject 𝒜) ⟶ A :=
  biprod.desc f (show C ⟶ A from -g)

private abbrev kernelPullback (f : B ⟶ A) (g : C ⟶ A) : FilteredObject 𝒜 :=
  ((B ⊞ C : FilteredObject 𝒜)).subobjectFilteredObject
    (kernelSubobject (pullbackDifference f g).hom)

private abbrev kernelPullbackι (f : B ⟶ A) (g : C ⟶ A) :
    kernelPullback f g ⟶ (B ⊞ C : FilteredObject 𝒜) :=
  ((B ⊞ C : FilteredObject 𝒜)).subobjectInclusion
    (kernelSubobject (pullbackDifference f g).hom)

private abbrev kernelPullbackFst (f : B ⟶ A) (g : C ⟶ A) : kernelPullback f g ⟶ B :=
  kernelPullbackι f g ≫ biprod.fst

private abbrev kernelPullbackSnd (f : B ⟶ A) (g : C ⟶ A) : kernelPullback f g ⟶ C :=
  kernelPullbackι f g ≫ biprod.snd

private theorem kernelPullback_isPullback (f : B ⟶ A) (g : C ⟶ A) :
    IsPullback (kernelPullbackFst f g) (kernelPullbackSnd f g) f g := by
  sorry

noncomputable instance hasPullback (f : B ⟶ A) (g : C ⟶ A) : HasPullback f g :=
  (kernelPullback_isPullback f g).hasPullback

/-- In a pullback square of filtered objects, strictness of the left map forces strictness of the
right map. -/
theorem strict_snd_of_isPullback_of_strict
    (f : B ⟶ A) (g : C ⟶ A) {P : FilteredObject 𝒜} {g' : P ⟶ B} {f' : P ⟶ C}
    (sq : IsPullback g' f' f g) (hf : Strict f) :
    Strict f' := by
  sorry

/-- In the canonical pullback square of filtered objects, strictness of the left map forces
strictness of the induced projection to the right factor. -/
theorem strict_pullback_snd_of_strict (f : B ⟶ A) (g : C ⟶ A) (hf : Strict f) :
    Strict (pullback.snd f g : pullback f g ⟶ C) := by
  exact strict_snd_of_isPullback_of_strict f g (IsPullback.of_hasPullback f g) hf

end FilteredObject.Hom

-- Proof sketch: realize the pullback in `FilteredObject` via the owner-level `HasPullback f g`
-- instance coming from the kernel presentation inside `B ⊞ C`; then package
-- the canonical pullback object and projections. The strictness clause is the square-level theorem
-- `strict_snd_of_isPullback_of_strict` applied to the canonical pullback square.
/-- Lemma 12.19.11: for morphisms `f : B ⟶ A` and `g : C ⟶ A` of filtered objects in an abelian
category, there exists a fibre product square in the filtered category, and if `f` is strict, then
the induced morphism `f' : B ×[A] C ⟶ C` is strict. -/
theorem exists_filtered_pullback_preserving_strictness
    {A B C : FilteredObject 𝒜} (f : B ⟶ A) (g : C ⟶ A) :
    ∃ (P : FilteredObject 𝒜) (g' : P ⟶ B) (f' : P ⟶ C),
      IsPullback g' f' f g ∧ (Strict f → Strict f') := by
  refine ⟨pullback f g, pullback.fst f g, pullback.snd f g, IsPullback.of_hasPullback f g, ?_⟩
  exact strict_pullback_snd_of_strict f g

end CategoryTheory

/-! ### Lemma_12_19_12 (from Chap12) -/
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

/-! ### Lemma_12_19_13 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace FilteredObject.Hom

open FilteredObject

variable {A B : FilteredObject C}

-- Proof sketch: the equivalence `(1) ↔ (2)` is `strict_iff_coimageImageComparison_isIso`, the
-- kernel/coimage and image/cokernel short exact sequences from Lemma `12.19.12` identify `(3)`
-- with `(4)`, `(5)`, and `(6)`, and finiteness of the filtrations lets one recover `(2)` from
-- `(3)` by descending induction on the filtration degree.
/-- Lemma 12.19.13: for a morphism `f : A ⟶ B` of finite filtered objects in an abelian category,
the following are equivalent: `f` is strict; the filtered coimage-image comparison
`coim(f) ⟶ im(f)` is an isomorphism; the induced morphism
`gr(coim(f)) ⟶ gr(im(f))` is an isomorphism; the sequence
`gr(\ker(f)) ⟶ gr(A) ⟶ gr(B)` is exact in every degree; the sequence
`gr(A) ⟶ gr(B) ⟶ gr(\operatorname{coker}(f))` is exact in every degree; and the sequence
`0 ⟶ gr(\ker(f)) ⟶ gr(A) ⟶ gr(B) ⟶ gr(\operatorname{coker}(f)) ⟶ 0` is exact in every
degree. -/
theorem strict_tfae_coimageImageComparison_isIso_and_graded_exactness
    (f : A ⟶ B) (hA : IsFinite A) (hB : IsFinite B) :
    List.TFAE
      [ Strict f
      , IsIso (coimageImageComparison f)
      , IsIso (associatedGradedMap (coimageImageComparison f))
      , ∀ p : ℤ, (kernelSourceTargetShortComplex f p).Exact
      , ∀ p : ℤ, (sourceTargetCokernelShortComplex f p).Exact
      , ∀ p : ℤ,
          (ComposableArrows.mk₅
            (0 : 0 ⟶ (kernelFilteredObject f).gradedPiece p)
            (gradedPieceMap (kernelι f) p)
            (gradedPieceMap f p)
            (gradedPieceMap (toCokernel f) p)
            (0 : (cokernelFilteredObject f).gradedPiece p ⟶ 0)).Exact
      ] := sorry

end FilteredObject.Hom

end CategoryTheory

/-! ### Lemma_12_19_14 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace FilteredObject.Hom

open FilteredObject

variable {A B C : FilteredObject 𝒜}

/-
Source/core/bridge triage for Lemma 12.19.14:
- source-facing: the graded complex `gr^p(A) ⟶ gr^p(B) ⟶ gr^p(C)` and the quotient
  `gr^p(\ker β / \operatorname{im} α)`
- core/canonical owner: `ShortComplex 𝒜` and its homology API
- bridge/view: the canonical filtered projection
  `kernelFilteredObject β ⟶ B.subobjectSubquotientFilteredObject (image_le_kernel α.hom β.hom hcomp)`
  and the induced left-homology data on that owner short complex
-/

/-- Lemma 12.19.14: for a complex `A ⟶ B ⟶ C` of filtered objects in an abelian category with
strict maps `α` and `β`, the associated graded of `ker β / im α` is canonically isomorphic to the
homology of the graded complex `gr A ⟶ gr B ⟶ gr C`. -/
noncomputable def graded_homology_iso_graded_complex_homology
    (α : A ⟶ B) (β : B ⟶ C) (hcomp : α ≫ β = 0)
    (hα : Strict α) (hβ : Strict β) (p : ℤ) :
    let hcomp_hom : α.hom ≫ β.hom = 0 := congrArg FilteredObject.Hom.hom hcomp
    (B.subobjectSubquotientFilteredObject (image_le_kernel α.hom β.hom hcomp_hom)).gradedPiece p ≅
      (ShortComplex.mk (gradedPieceMap α p) (gradedPieceMap β p)
        (gradedPieceMap_comp_zero α β hcomp p)).homology :=
  let hcomp_hom : α.hom ≫ β.hom = 0 := congrArg FilteredObject.Hom.hom hcomp
  let S : ShortComplex 𝒜 :=
    ShortComplex.mk (gradedPieceMap α p) (gradedPieceMap β p)
      (gradedPieceMap_comp_zero α β hcomp p)
  let hS : S.LeftHomologyData :=
    { K := (kernelFilteredObject β).gradedPiece p
      H := (B.subobjectSubquotientFilteredObject (image_le_kernel α.hom β.hom hcomp_hom)).gradedPiece p
      i := gradedPieceMap (kernelι β) p
      π := gradedPieceMap (B.subobjectToSubquotient (image_le_kernel α.hom β.hom hcomp_hom)) p
      wi := gradedPieceMap_comp_zero (kernelι β) β (kernelι_comp β) p
      hi := by
        sorry
      wπ := by
        sorry
      hπ := by
        sorry }
  hS.homologyIso.symm

end FilteredObject.Hom

end CategoryTheory

/-! ### Lemma_12_19_15 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace ShortComplex

open FilteredObject FilteredObject.Hom

/- Domain-style sampling for Lemma 12.19.15:
- primary domain: filtered objects in an abelian category, viewed through short-complex exactness
- sampled owner declarations:
  `FilteredObject.IsFinite`,
  `FilteredObject.Hom.Strict`,
  `associatedGradedFunctor`,
  `GradedObject.eval`,
  `ShortComplex.Exact.map`
- owner abstraction used here: exactness of a short complex after applying the canonical filtered
  functors `associatedGradedFunctor`, `stageFunctor`, and `quotientFunctor`
- primitive data: a short complex `S : ShortComplex (FilteredObject 𝒜)` and finiteness of its
  three filtered terms
- derived API: degreewise exactness, stage exactness, quotient exactness, strictness, and
  exactness of the underlying short complex
- source/core/bridge triage:
  `(1)` is a `source-facing` bridge theorem obtained from the canonical owner
  `ShortComplex.Exact.map` by evaluating the associated graded short complex in degree `p`;
  `(2)` through `(5)` are `source-facing` bridge theorems for filtered short complexes. 
-/

variable {S : ShortComplex (FilteredObject 𝒜)}

/-- Lemma 12.19.15 (1): if the associated graded complex is exact, then
`gr^p(A) ⟶ gr^p(B) ⟶ gr^p(C)` is exact for every `p`. This is the source-facing specialization of
the owner theorem `ShortComplex.Exact.map` along the evaluation functor `GradedObject.eval p`. -/
theorem gradedPiece_exact_of_associatedGraded_exact
    (hgr : ShortComplex.Exact (S.map associatedGradedFunctor)) (p : ℤ) :
    ShortComplex.Exact (S.map (associatedGradedFunctor ⋙ GradedObject.eval p)) := by
  let E := piEquivalenceFunctorDiscrete ℤ 𝒜
  letI : Functor.PreservesHomology (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜) :=
    { preservesKernels := by
        intro X Y f
        simpa [E, GradedObject.eval] using
          (inferInstance : PreservesLimit (parallelPair f 0)
            (E.functor ⋙ (evaluation (Discrete ℤ) 𝒜).obj (Discrete.mk p)))
      preservesCokernels := by
        intro X Y f
        simpa [E, GradedObject.eval] using
          (inferInstance : PreservesColimit (parallelPair f 0)
            (E.functor ⋙ (evaluation (Discrete ℤ) 𝒜).obj (Discrete.mk p))) }
  simpa using hgr.map (GradedObject.eval p : GradedObject ℤ 𝒜 ⥤ 𝒜)

section FiniteFiltrations

variable (hX₁fin : S.X₁.IsFinite) (hX₂fin : S.X₂.IsFinite) (hX₃fin : S.X₃.IsFinite)
  (hgr : ShortComplex.Exact (S.map associatedGradedFunctor))

-- Proof sketch: argue by induction on the common finite length of the filtrations, peeling off the
-- top nonzero step and applying the short exact sequence relating `F^p` to the associated graded
-- piece and the quotient filtration.
/-- Lemma 12.19.15 (2): if the filtrations are finite and the associated graded complex is exact,
then `F^p(A) ⟶ F^p(B) ⟶ F^p(C)` is exact for every `p`. -/
theorem stage_exact_of_associatedGraded_exact
    (p : ℤ) :
    ShortComplex.Exact (S.map (stageFunctor p)) := sorry

-- Proof sketch: perform the same finite-length induction on the quotient filtrations
-- `A / F^n A`, `B / F^n B`, and `C / F^n C`, using exactness of the graded pieces to identify the
-- successive quotients.
/-- Lemma 12.19.15 (3): if the filtrations are finite and the associated graded complex is exact,
then `A / F^p(A) ⟶ B / F^p(B) ⟶ C / F^p(C)` is exact for every `p`. -/
theorem quotient_exact_of_associatedGraded_exact
    (p : ℤ) :
    ShortComplex.Exact (S.map (quotientFunctor p)) := sorry

-- Proof sketch: apply the stage exactness and the underlying exactness to identify the images of
-- `S.f` and `S.g` on each filtration level with the intersections required in the
-- definition of strictness.
/-- Lemma 12.19.15 (4): if the filtrations are finite and the associated graded complex is exact,
then both maps of filtered objects are strict. -/
theorem strict_of_associatedGraded_exact
    : Strict S.f ∧ Strict S.g := sorry

-- Proof sketch: apply the quotient exactness at a stage above the top nonzero filtration step, so
-- the quotients identify with the original objects and the quotient complex becomes the underlying
-- short complex.
/-- Lemma 12.19.15 (5): if the filtrations are finite and the associated graded complex is exact,
then the underlying sequence `A.obj ⟶ B.obj ⟶ C.obj` is exact. -/
theorem underlying_exact_of_associatedGraded_exact
    : ShortComplex.Exact (S.map FilteredObject.forget) := sorry

end FiniteFiltrations

end ShortComplex

end CategoryTheory
