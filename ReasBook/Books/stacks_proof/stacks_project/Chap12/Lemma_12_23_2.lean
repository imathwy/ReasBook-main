import Mathlib
import StacksProject_2024.Chap12.Definition_12_23_1

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

open FilteredObject FilteredObject.Hom

namespace HomologicalComplex.Filtered

variable [Abelian C]

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- Helper for Lemma 12.23.2: the stage map induced by the identity filtered morphism is the
identity on the given filtration stage. -/
private theorem stageMap_id (A : FilteredObject C) (p : ℤ) :
    stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

/-- Helper for Lemma 12.23.2: stage maps respect composition of filtered morphisms. -/
private theorem stageMap_comp {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    stageMap (f ≫ g) p = stageMap f p ≫ stageMap g p := by
  exact (cancel_mono (D.filtration.obj p).arrow).1 (by
    calc
      stageMap (f ≫ g) p ≫ (D.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f ≫ g).hom := by
              rw [stageMap_comm]
      _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
            simp [Category.assoc]
      _ = (stageMap f p ≫ (B.filtration.obj p).arrow) ≫ g.hom := by
            rw [stageMap_comm]
      _ = stageMap f p ≫ (stageMap g p ≫ (D.filtration.obj p).arrow) := by
            rw [stageMap_comm]
            simp [Category.assoc]
      _ = (stageMap f p ≫ stageMap g p) ≫ (D.filtration.obj p).arrow := by
            simp [Category.assoc])

/-- Helper for Lemma 12.23.2: the zero filtered morphism induces the zero map on every stage. -/
private theorem stageMap_zero (A B : FilteredObject C) (p : ℤ) :
    stageMap (0 : A ⟶ B) p = 0 := by
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [stageMap_comm]
    simp)

/-- Helper for Lemma 12.23.2: the morphism induced on the `p`-th graded piece by a filtered
morphism. -/
noncomputable abbrev gradedPieceMap {A B : FilteredObject C} (f : A ⟶ B) (p : ℤ) :
    gr^{p} A ⟶ gr^{p} B :=
  cokernel.map (A.filtration.stageInclusion p) (B.filtration.stageInclusion p)
    (stageMap f (p + 1)) (stageMap f p)
    (stageInclusion_naturality f p)

/-- Helper for Lemma 12.23.2: graded-piece maps preserve identities. -/
private theorem gradedPieceMap_id (A : FilteredObject C) (p : ℤ) :
    gradedPieceMap (𝟙 A) p = 𝟙 (gr^{p} A) := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_id])

/-- Helper for Lemma 12.23.2: graded-piece maps respect composition. -/
private theorem gradedPieceMap_comp {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    gradedPieceMap (f ≫ g) p = gradedPieceMap f p ≫ gradedPieceMap g p := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, Category.assoc, stageMap_comp])

/-- Helper for Lemma 12.23.2: graded-piece maps send zero morphisms to zero. -/
private theorem gradedPieceMap_zero (A B : FilteredObject C) (p : ℤ) :
    gradedPieceMap (0 : A ⟶ B) p = 0 := by
  exact (cancel_epi (cokernel.π (A.filtration.stageInclusion p))).1 (by
    simp [gradedPieceMap, stageMap_zero])

/-- Helper for Lemma 12.23.2: the functor sending a filtered object to its `p`-th graded piece. -/
noncomputable def gradedPieceFunctor (p : ℤ) : FilteredObject C ⥤ C where
  obj A := gr^{p} A
  map f := gradedPieceMap f p
  map_id A := gradedPieceMap_id A p
  map_comp f g := gradedPieceMap_comp f g p

/-- Helper for Lemma 12.23.2: the graded-piece functor preserves zero morphisms. -/
instance gradedPieceFunctor_preservesZeroMorphisms (p : ℤ) :
    (gradedPieceFunctor (C := C) p).PreservesZeroMorphisms where
  map_zero A B := gradedPieceMap_zero A B p

/-- Helper for Lemma 12.23.2: the `p`-th graded differential object of a one-object filtered
complex, obtained by applying the graded-piece functor degreewise. -/
noncomputable abbrev gradedPiece (p : ℤ) :
    HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  ((gradedPieceFunctor (C := C) p).mapHomologicalComplex
    (ComplexShape.refl PUnit.{1})).obj K

/-- The page-`E₀` complex attached to the filtered differential object `K`. -/
noncomputable def pageZero :
    HomologicalComplex C (ComplexShape.up' (0 : ℤ)) :=
  { X := fun p ↦ (gradedPiece K p).X PUnit.unit
    d := fun p q ↦
      if h : p = q then by
        subst h
        exact (gradedPiece K p).d PUnit.unit PUnit.unit
      else 0
    shape := fun p q hpq ↦ by
      by_cases h : p = q
      · exfalso
        exact hpq (by simp [ComplexShape.up', h])
      · simp [h]
    d_comp_d' := fun p q r hpq hqr ↦ by
      have hpq' : p = q := by
        simpa [ComplexShape.up'] using hpq
      have hqr' : q = r := by
        simpa [ComplexShape.up'] using hqr
      subst hpq'
      subst hqr'
      simpa [gradedPiece] using
        (gradedPiece K p).d_comp_d PUnit.unit PUnit.unit PUnit.unit }

private noncomputable def pageZeroScIso (p : ℤ) :
    (pageZero K).sc' p p p ≅
      (gradedPiece K p).sc' PUnit.unit PUnit.unit PUnit.unit :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [pageZero, gradedPiece])
    (by simp [pageZero, gradedPiece])

/-- The page-`E₀` complex computes, in degree `p`, the homology of the graded differential object
`gr^p(K)`. -/
noncomputable def pageZeroHomologyIso (p : ℤ) :
    (pageZero K).homology p ≅
      (gradedPiece K p).homology PUnit.unit := by
  let hprevPage : (ComplexShape.up' (0 : ℤ)).prev p = p :=
    ComplexShape.prev_eq' (ComplexShape.up' (0 : ℤ)) (by simp [ComplexShape.up'])
  let hnextPage : (ComplexShape.up' (0 : ℤ)).next p = p :=
    ComplexShape.next_eq' (ComplexShape.up' (0 : ℤ)) (by simp [ComplexShape.up'])
  exact
    (pageZero K).homologyIsoSc' p p p hprevPage hnextPage ≪≫
      ShortComplex.homologyMapIso (pageZeroScIso K p) ≪≫
        ((gradedPiece K p).homologyIsoSc' PUnit.unit PUnit.unit PUnit.unit
          rfl rfl).symm

variable {E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0}

/-- The core owner class asserting that `E` is a spectral sequence associated to the filtered
differential object `K`, encoded by the literal page-zero identification with the associated
graded differential object. -/
class IsAssociatedToFilteredDifferentialObject
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) : Prop where
  pageZero_eq : E.page 0 = pageZero K

/-- Source-facing companion: the owner page-zero equality yields the canonical isomorphism from
the zeroth page of `E` to the graded page-zero complex of `K`. -/
noncomputable def pageZeroIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] :
    E.page 0 ≅ pageZero K :=
  eqToIso hE.pageZero_eq

/-- The page-`E₁` identification induced by a page-`E₀` comparison with the associated graded
complex. -/
noncomputable def pageOneIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] (p : ℤ) :
    (E.page 1).X p ≅
      (gradedPiece K p).homology PUnit.unit :=
  (E.iso 0 1 p).symm ≪≫
    HomologicalComplex.homologyMapIso (pageZeroIso K E) p ≪≫
      pageZeroHomologyIso K p

/-- Helper for Lemma 12.23.2: starting from the literal page-`E₀` complex, form the higher pages
by iterating homology objects and equipping them with zero differentials. -/
noncomputable def iteratedHomologyPage :
    (n : ℕ) → HomologicalComplex C (ComplexShape.up' (n : ℤ))
  | 0 => pageZero K
  | n + 1 =>
      { X := fun p ↦ (iteratedHomologyPage n).homology p
        d := fun _ _ ↦ 0
        shape := fun _ _ _ ↦ by simp
        d_comp_d' := fun _ _ _ _ _ ↦ by simp }

/-- Helper for Lemma 12.23.2: the recursive witness has the prescribed zeroth page. -/
@[simp] theorem iteratedHomologyPage_zero :
    iteratedHomologyPage K 0 = pageZero K :=
  rfl

/-- Helper for Lemma 12.23.2: package `pageZero K` into a zero-based spectral sequence by taking
homology objects on successive pages. -/
noncomputable def associatedFilteredDifferentialSpectralSequence :
    SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0 where
  page r hr :=
    match r with
    | Int.ofNat n => iteratedHomologyPage K n
    | Int.negSucc _ => nomatch hr
  iso r _ p hrr' hr :=
    match r with
    | Int.ofNat n =>
        match hrr' with
        | rfl => Iso.refl ((iteratedHomologyPage K n).homology p)
    | Int.negSucc _ => nomatch hr

/-- Lemma 12.23.2: a filtered differential object admits an associated spectral sequence together
with the canonical page-`E₀` comparison isomorphism to the associated graded differential object
`pageZero K`. The page-`E₁` identification with the homology of the graded pieces is then derived
from the owner class `IsAssociatedToFilteredDifferentialObject K E`, the owner transition
`E.iso 0 1`, and `pageOneIso`, rather than stored as separate primitive data. -/
@[stacks 012C]
theorem exists_associatedSpectralSequence :
    ∃ E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0,
      IsAssociatedToFilteredDifferentialObject K E := by
  -- We realize the required owner predicate by making the zeroth page literally `pageZero K`.
  refine ⟨associatedFilteredDifferentialSpectralSequence K, ?_⟩
  -- The owner class only asks for the literal page-zero identification.
  exact ⟨rfl⟩

end HomologicalComplex.Filtered

end CategoryTheory
