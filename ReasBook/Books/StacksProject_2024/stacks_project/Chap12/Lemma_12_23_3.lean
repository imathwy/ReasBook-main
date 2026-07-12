import Mathlib
import StacksProject_2024.Chap12.Definition_12_23_1

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

namespace HomologicalComplex.Filtered

variable {C : Type u} [Category.{v} C] [Abelian C]

open FilteredObject FilteredObject.Hom

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/-- Helper for Lemma 12.23.3: the stage map induced by the identity filtered morphism is the
identity on the stage. -/
private theorem stageMap_id (A : FilteredObject C) (p : ℤ) :
    FilteredObject.Hom.stageMap (𝟙 A) p = 𝟙 (F^{p} A) := by
  -- Proof comment: compare both candidates after postcomposing with the mono stage inclusion.
  exact (cancel_mono (A.filtration.obj p).arrow).1 (by
    rw [FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 12.23.3: stage maps respect composition of filtered morphisms. -/
private theorem stageMap_comp {A B D : FilteredObject C} (f : A ⟶ B) (g : B ⟶ D) (p : ℤ) :
    FilteredObject.Hom.stageMap (f ≫ g) p =
      FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p := by
  -- Proof comment: cancel the target stage inclusion and reduce to the ambient composite.
  exact (cancel_mono (D.filtration.obj p).arrow).1 (by
    calc
      FilteredObject.Hom.stageMap (f ≫ g) p ≫ (D.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f ≫ g).hom := by
              rw [FilteredObject.Hom.stageMap_comm]
      _ = ((A.filtration.obj p).arrow ≫ f.hom) ≫ g.hom := by
            simp [Category.assoc]
      _ = (FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow) ≫ g.hom := by
            rw [FilteredObject.Hom.stageMap_comm]
      _ = FilteredObject.Hom.stageMap f p ≫
            (FilteredObject.Hom.stageMap g p ≫ (D.filtration.obj p).arrow) := by
            rw [FilteredObject.Hom.stageMap_comm]
            simp [Category.assoc]
      _ = (FilteredObject.Hom.stageMap f p ≫ FilteredObject.Hom.stageMap g p) ≫
            (D.filtration.obj p).arrow := by
            simp [Category.assoc])

/-- Helper for Lemma 12.23.3: the zero filtered morphism induces the zero map on every stage. -/
private theorem stageMap_zero (A B : FilteredObject C) (p : ℤ) :
    FilteredObject.Hom.stageMap (0 : A ⟶ B) p = 0 := by
  -- Proof comment: cancel the mono stage inclusion and reduce to the ambient zero composite.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    rw [FilteredObject.Hom.stageMap_comm]
    simp)

/-- Helper for Lemma 12.23.3: the `p`-th stage functor on filtered objects, specialized to the
filtered-object owner. -/
abbrev stageFunctor (p : ℤ) : FilteredObject C ⥤ C :=
  { obj := fun A ↦ F^{p} A
    map := fun f ↦ FilteredObject.Hom.stageMap f p
    map_id := fun A ↦ stageMap_id A p
    map_comp := fun f g ↦ stageMap_comp f g p }

/-- Helper for Lemma 12.23.3: the stage functor preserves zero morphisms. -/
instance stageFunctor_preservesZeroMorphisms (p : ℤ) :
    ((stageFunctor (C := C) p : FilteredObject C ⥤ C)).PreservesZeroMorphisms where
  map_zero A B := stageMap_zero A B p

/-- Helper for Lemma 12.23.3: the canonical inclusion of the `p`-th stage into the ambient
object, natural in the filtered object. -/
private def stageFunctorToForget (p : ℤ) :
    (stageFunctor (C := C) p : FilteredObject C ⥤ C) ⟶
      (FilteredObject.forget : FilteredObject C ⥤ C) where
  app A := (A.filtration.obj p).arrow
  naturality {A B} f := by
    -- Proof comment: this is exactly the defining commutative square for the restricted stage map.
    change FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow =
      (A.filtration.obj p).arrow ≫ f.hom
    exact FilteredObject.Hom.stageMap_comm f p

/-- Helper for Lemma 12.23.3: for `p ≤ q`, the comparison `F^q A ⟶ F^p A` is natural in the
filtered object `A`. -/
private theorem stageMapOfLE_naturality {A B : FilteredObject C} (f : A ⟶ B) {p q : ℤ}
    (hpq : p ≤ q) :
    Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p) (A.filtration.antitone_obj hpq) ≫
      FilteredObject.Hom.stageMap f p =
        FilteredObject.Hom.stageMap f q ≫
          Subobject.ofLE (B.filtration.obj q) (B.filtration.obj p)
            (B.filtration.antitone_obj hpq) := by
  -- Proof comment: cancel the mono inclusion of `F^p B` and compare both composites in `B`.
  exact (cancel_mono (B.filtration.obj p).arrow).1 (by
    calc
      (Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p)
          (A.filtration.antitone_obj hpq) ≫
          FilteredObject.Hom.stageMap f p) ≫
          (B.filtration.obj p).arrow
          = Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p)
              (A.filtration.antitone_obj hpq) ≫
              (A.filtration.obj p).arrow ≫ f.hom := by
                rw [Category.assoc, FilteredObject.Hom.stageMap_comm]
      _ = (A.filtration.obj q).arrow ≫ f.hom := by
            simp [Category.assoc, Subobject.ofLE_arrow]
      _ = FilteredObject.Hom.stageMap f q ≫ (B.filtration.obj q).arrow := by
            rw [FilteredObject.Hom.stageMap_comm]
      _ =
          (FilteredObject.Hom.stageMap f q ≫
            Subobject.ofLE (B.filtration.obj q) (B.filtration.obj p)
              (B.filtration.antitone_obj hpq)) ≫
            (B.filtration.obj p).arrow := by
              simp [Category.assoc, Subobject.ofLE_arrow])

/-- Helper for Lemma 12.23.3: for `p ≤ q`, the `q`-th stage functor maps naturally to the
`p`-th stage functor. -/
def stageFunctorMapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (stageFunctor (C := C) q : FilteredObject C ⥤ C) ⟶ stageFunctor (C := C) p where
  app A := Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p) (A.filtration.antitone_obj hpq)
  naturality {A B} f := by
    -- Proof comment: this is the stagewise naturality square from `stageMapOfLE_naturality`.
    change FilteredObject.Hom.stageMap f q ≫
        Subobject.ofLE (B.filtration.obj q) (B.filtration.obj p) (B.filtration.antitone_obj hpq) =
      Subobject.ofLE (A.filtration.obj q) (A.filtration.obj p) (A.filtration.antitone_obj hpq) ≫
        FilteredObject.Hom.stageMap f p
    exact (stageMapOfLE_naturality f hpq).symm

/-- Helper for Lemma 12.23.3: the one-object complex of `p`-th filtration stages. -/
abbrev stage (p : ℤ) : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  ((stageFunctor (C := C) p).mapHomologicalComplex (ComplexShape.refl PUnit.{1})).obj K

/-- Helper for Lemma 12.23.3: for `p ≤ q`, the canonical map `F^q K ⟶ F^p K` of one-object
complexes. -/
abbrev stageMapOfLE {p q : ℤ} (hpq : p ≤ q) : stage K q ⟶ stage K p :=
  (NatTrans.mapHomologicalComplex (stageFunctorMapOfLE (C := C) hpq)
    (ComplexShape.refl PUnit.{1})).app K

/-- Helper for Lemma 12.23.3: successive stage comparisons compose to the direct comparison. -/
theorem stageFunctorMapOfLE_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    (stageFunctorMapOfLE (C := C) hqr :
        (stageFunctor (C := C) r : FilteredObject C ⥤ C) ⟶ stageFunctor (C := C) q) ≫
      stageFunctorMapOfLE (C := C) hpq =
      stageFunctorMapOfLE (C := C) (le_trans hpq hqr) := by
  ext A
  -- Proof comment: the composite comparison of subobject inclusions is the direct inclusion.
  simpa [stageFunctorMapOfLE, Category.assoc] using
    congrArg
      (fun φ ↦ φ ≫ (A.filtration.obj p).arrow)
      (Subobject.ofLE_comp_ofLE
        (A.filtration.obj r)
        (A.filtration.obj q)
        (A.filtration.obj p)
        (A.filtration.antitone_obj hqr)
        (A.filtration.antitone_obj hpq))

/-- Helper for Lemma 12.23.3: every integer is bounded above by its successor. -/
theorem le_succ_int (p : ℤ) : p ≤ p + 1 := by
  omega

/-- Helper for Lemma 12.23.3: the `p`-th graded differential object of a one-object filtered
complex. -/
noncomputable abbrev gradedPiece (p : ℤ) :
    HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  cokernel (stageMapOfLE K (le_succ_int p))

/-- Helper for Lemma 12.23.3: the canonical graded piece agrees with the cokernel presentation
`F^p K / F^{p + 1} K`. -/
private theorem gradedPiece_eq_cokernel (p : ℤ) :
    gradedPiece K p = cokernel (stageMapOfLE K (le_succ_int p)) := by
  -- Proof comment: both sides are the same degreewise cokernel model of the graded piece.
  rfl

/-- Helper for Lemma 12.23.3: the graded piece is canonically isomorphic to its cokernel
presentation. -/
private noncomputable def gradedPieceCokernelIso (p : ℤ) :
    gradedPiece K p ≅ cokernel (stageMapOfLE K (le_succ_int p)) :=
  eqToIso (gradedPiece_eq_cokernel K p)

/-- Helper for Lemma 12.23.3: the page-`E₀` complex attached to the filtered differential object
`K`. -/
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

/-- Helper for Lemma 12.23.3: compare the page-`E₀` short complex with the underlying graded-piece
short complex at degree `p`. -/
private noncomputable def pageZeroScIso (p : ℤ) :
    (pageZero K).sc' p p p ≅
      (gradedPiece K p).sc' PUnit.unit PUnit.unit PUnit.unit :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [pageZero, gradedPiece])
    (by simp [pageZero, gradedPiece])

/-- Helper for Lemma 12.23.3: the page-`E₀` homology in degree `p` is the homology of the graded
piece `gr^p(K)`. -/
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

/-- Helper for Lemma 12.23.3: the owner class asserting that `E` is the spectral sequence
associated to `K`, encoded by the literal page-zero identification. -/
class IsAssociatedToFilteredDifferentialObject
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0) : Prop where
  pageZero_eq : E.page 0 = pageZero K

/-- Helper for Lemma 12.23.3: the canonical page-`E₀` isomorphism attached to an associated
spectral sequence. -/
noncomputable def pageZeroIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] :
    E.page 0 ≅ pageZero K :=
  eqToIso hE.pageZero_eq

/-- Helper for Lemma 12.23.3: the page-`E₁` identification with the homology of the graded
pieces. -/
noncomputable def pageOneIso
    (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [hE : IsAssociatedToFilteredDifferentialObject K E] (p : ℤ) :
    (E.page 1).X p ≅
      (gradedPiece K p).homology PUnit.unit :=
  (E.iso 0 1 p).symm ≪≫
    HomologicalComplex.homologyMapIso (pageZeroIso K E) p ≪≫
      pageZeroHomologyIso K p

/-- The two-step successor inequality on `ℤ`. -/
-- Proof sketch: compose the inequalities `p ≤ p + 1` and `p + 1 ≤ p + 2`.
private theorem int_le_add_two (p : ℤ) : p ≤ p + 1 + 1 := by
  -- Proof comment: this is the integer inequality needed to compare `F^{p + 2} K` directly with
  -- `F^p K`.
  omega

/-- Successive stage-comparison maps compose to the direct comparison map. -/
private theorem stageMapOfLE_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    stageMapOfLE K hqr ≫ stageMapOfLE K hpq = stageMapOfLE K (le_trans hpq hqr) := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.refl PUnit.{1})).app K)
      (stageFunctorMapOfLE_comp (C := C) hpq hqr)
  simpa [stageMapOfLE, NatTrans.mapHomologicalComplex_comp] using h

/-- The one-object differential object `F^p K / F^{p + 2} K`. -/
private noncomputable def twoStepQuotientDifferentialObject (p : ℤ) :
    HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  cokernel (stageMapOfLE K (int_le_add_two p))

/-- The quotient map `gr^{p + 1} K ⟶ F^p K / F^{p + 2} K` induced by the inclusion
`F^{p + 1} K ⟶ F^p K`. -/
private theorem gradedPieceSuccToTwoStepQuotient_condition (p : ℤ) :
    stageMapOfLE K (le_succ_int (p + 1)) ≫ stageMapOfLE K (le_succ_int p) =
      (𝟙 _) ≫ stageMapOfLE K (int_le_add_two p) := by
  have hproof :
      le_trans (le_succ_int p) (le_succ_int (p + 1)) = int_le_add_two p := by
    apply Subsingleton.elim
  simpa [hproof] using stageMapOfLE_comp K (le_succ_int p) (le_succ_int (p + 1))

/-- The morphism of one-object differential objects `gr^{p + 1} K ⟶ F^p K / F^{p + 2} K`. -/
private noncomputable def gradedPieceSuccToTwoStepQuotientHom (p : ℤ) :
    gradedPiece K (p + 1) ⟶ twoStepQuotientDifferentialObject K p :=
  (gradedPieceCokernelIso K (p + 1)).hom ≫
    cokernel.map
      (stageMapOfLE K (le_succ_int (p + 1)))
      (stageMapOfLE K (int_le_add_two p))
      (𝟙 _)
      (stageMapOfLE K (le_succ_int p))
      (gradedPieceSuccToTwoStepQuotient_condition K p)

/-- The projection `F^p K / F^{p + 2} K ⟶ gr^p K`. -/
private theorem twoStepQuotientToGradedPiece_condition (p : ℤ) :
    stageMapOfLE K (int_le_add_two p) ≫ (𝟙 _) =
      stageMapOfLE K (le_succ_int (p + 1)) ≫ stageMapOfLE K (le_succ_int p) := by
  simpa using (gradedPieceSuccToTwoStepQuotient_condition K p).symm

/-- The morphism of one-object differential objects `F^p K / F^{p + 2} K ⟶ gr^p K`. -/
private noncomputable def twoStepQuotientToGradedPieceHom (p : ℤ) :
    twoStepQuotientDifferentialObject K p ⟶ gradedPiece K p :=
  cokernel.map
      (stageMapOfLE K (int_le_add_two p))
      (stageMapOfLE K (le_succ_int p))
      (stageMapOfLE K (le_succ_int (p + 1)))
      (𝟙 _)
      (twoStepQuotientToGradedPiece_condition K p) ≫
    (gradedPieceCokernelIso K p).inv

/-- Helper for Lemma 12.23.3: the object-level map
`gr^{p + 1}(K) ⟶ F^p K / F^{p + 2} K` before transporting through the graded-piece isomorphism. -/
private noncomputable def twoStepGradedObjectRawLeft (p : ℤ) :
    cokernel ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit) ⟶
      cokernel ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit) :=
  cokernel.map
    ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit)
    ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit)
    (𝟙 _)
    ((stageMapOfLE K (le_succ_int p)).f PUnit.unit)
    (by
      -- Proof comment: this is the unique-component version of the stage-comparison square used
      -- to define `gradedPieceSuccToTwoStepQuotientHom`.
      simpa using congrArg (fun φ ↦ φ.f PUnit.unit)
        (gradedPieceSuccToTwoStepQuotient_condition K p))

/-- Helper for Lemma 12.23.3: the object-level map
`F^p K / F^{p + 2} K ⟶ gr^p(K)` before transporting through the graded-piece isomorphism. -/
private noncomputable def twoStepGradedObjectRawRight (p : ℤ) :
    cokernel ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit) ⟶
      cokernel ((stageMapOfLE K (le_succ_int p)).f PUnit.unit) :=
  cokernel.map
    ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit)
    ((stageMapOfLE K (le_succ_int p)).f PUnit.unit)
    ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit)
    (𝟙 _)
    (by
      -- Proof comment: this is the unique-component version of the quotient-to-graded square used
      -- to define `twoStepQuotientToGradedPieceHom`.
      simpa using congrArg (fun φ ↦ φ.f PUnit.unit)
        (twoStepQuotientToGradedPiece_condition K p))

/-- Helper for Lemma 12.23.3: evaluation at the unique object identifies the owner-level cokernel
of a one-object complex morphism with the ordinary cokernel of its unique component. -/
private noncomputable def one_object_cokernel_component_iso
    {K L : HomologicalComplex C (ComplexShape.refl PUnit.{1})} (φ : K ⟶ L) :
    ((cokernel φ).X PUnit.unit) ≅ cokernel (φ.f PUnit.unit) :=
  PreservesCokernel.iso (HomologicalComplex.eval C (ComplexShape.refl PUnit.{1}) PUnit.unit) φ

/-- Helper for Lemma 12.23.3: under the componentwise cokernel identification, the owner-level
cokernel projection becomes the ordinary cokernel projection. -/
private theorem one_object_cokernel_component_iso_hom_π
    {K L : HomologicalComplex C (ComplexShape.refl PUnit.{1})} (φ : K ⟶ L) :
    (cokernel.π φ).f PUnit.unit ≫ (one_object_cokernel_component_iso (C := C) φ).hom =
      cokernel.π (φ.f PUnit.unit) := by
  -- Proof comment: this is the `WalkingParallelPair.one` leg of the universal cokernel cocone.
  simpa [CategoryTheory.Limits.PreservesCokernel.iso] using
    (IsColimit.comp_coconePointUniqueUpToIso_hom
      (isColimitOfHasCokernelOfPreservesColimit
        (HomologicalComplex.eval C (ComplexShape.refl PUnit.{1}) PUnit.unit) φ)
      (colimit.isColimit (parallelPair (φ.f PUnit.unit) 0))
      WalkingParallelPair.one)

/-- Helper for Lemma 12.23.3: the inverse componentwise cokernel identification sends the ordinary
cokernel projection back to the owner-level projection. -/
private theorem one_object_cokernel_component_iso_inv_π
    {K L : HomologicalComplex C (ComplexShape.refl PUnit.{1})} (φ : K ⟶ L) :
    cokernel.π (φ.f PUnit.unit) ≫ (one_object_cokernel_component_iso (C := C) φ).inv =
      (cokernel.π φ).f PUnit.unit := by
  -- Proof comment: this is the inverse cocone-point comparison for the evaluated cokernel.
  simpa [CategoryTheory.Limits.PreservesCokernel.iso] using
    (IsColimit.comp_coconePointUniqueUpToIso_inv
      (isColimitOfHasCokernelOfPreservesColimit
        (HomologicalComplex.eval C (ComplexShape.refl PUnit.{1}) PUnit.unit) φ)
      (colimit.isColimit (parallelPair (φ.f PUnit.unit) 0))
      WalkingParallelPair.one)

/-- Helper for Lemma 12.23.3: evaluating a `cokernel.map` in a one-object complex agrees with the
ordinary `cokernel.map` after transporting source and target through the componentwise cokernel
identifications. -/
private theorem one_object_cokernel_map_component
    {K₁ K₂ L₁ L₂ : HomologicalComplex C (ComplexShape.refl PUnit.{1})}
    (f : K₁ ⟶ K₂) (g : L₁ ⟶ L₂) (α : K₁ ⟶ L₁) (β : K₂ ⟶ L₂)
    (w : f ≫ β = α ≫ g) :
    ((cokernel.map f g α β w).f PUnit.unit) ≫
        (one_object_cokernel_component_iso (C := C) g).hom =
      (one_object_cokernel_component_iso (C := C) f).hom ≫
        cokernel.map
          (f.f PUnit.unit)
          (g.f PUnit.unit)
          (α.f PUnit.unit)
          (β.f PUnit.unit)
          (by
            -- Proof comment: evaluate the commutative square at the unique object.
            simpa using congrArg (fun ζ ↦ ζ.f PUnit.unit) w) := by
  -- Proof comment: both candidate maps out of the evaluated source cokernel are determined by
  -- their composites with the source cokernel projection.
  refine (cancel_epi ((cokernel.π f).f PUnit.unit)).1 ?_
  have hmap :
      cokernel.π f ≫ cokernel.map f g α β w = β ≫ cokernel.π g := by
    simp [cokernel.map, Category.assoc]
  have hmap_f :
      ((cokernel.π f ≫ cokernel.map f g α β w).f PUnit.unit) =
        ((β ≫ cokernel.π g).f PUnit.unit) :=
    congrArg (fun ζ ↦ ζ.f PUnit.unit) hmap
  have hmap_component :
      (cokernel.π f).f PUnit.unit ≫ (cokernel.map f g α β w).f PUnit.unit =
        β.f PUnit.unit ≫ (cokernel.π g).f PUnit.unit := by
    exact hmap_f
  calc
    ((cokernel.π f).f PUnit.unit) ≫
        ((cokernel.map f g α β w).f PUnit.unit ≫
          (one_object_cokernel_component_iso (C := C) g).hom)
        =
      ((cokernel.π f).f PUnit.unit ≫ (cokernel.map f g α β w).f PUnit.unit) ≫
        (one_object_cokernel_component_iso (C := C) g).hom := by
          simp [Category.assoc]
    _ =
      (β.f PUnit.unit ≫ (cokernel.π g).f PUnit.unit) ≫
        (one_object_cokernel_component_iso (C := C) g).hom := by
          rw [hmap_component]
    _ = β.f PUnit.unit ≫
        (cokernel.π g).f PUnit.unit ≫
          (one_object_cokernel_component_iso (C := C) g).hom := by
            simp [Category.assoc]
    _ = β.f PUnit.unit ≫ cokernel.π (g.f PUnit.unit) := by
          simpa [Category.assoc] using
            congrArg
              (fun ζ ↦ β.f PUnit.unit ≫ ζ)
              (one_object_cokernel_component_iso_hom_π (C := C) g)
    _ = ((cokernel.π f).f PUnit.unit ≫
          (one_object_cokernel_component_iso (C := C) f).hom) ≫
            cokernel.map
              (f.f PUnit.unit)
              (g.f PUnit.unit)
              (α.f PUnit.unit)
            (β.f PUnit.unit)
            (by
              -- Proof comment: this is the evaluated commutative square from `w`.
              simpa using congrArg (fun ζ ↦ ζ.f PUnit.unit) w) := by
            rw [one_object_cokernel_component_iso_hom_π (C := C) f]
            simp [Category.assoc]
    _ =
      ((cokernel.π f).f PUnit.unit) ≫
        ((one_object_cokernel_component_iso (C := C) f).hom ≫
          cokernel.map
            (f.f PUnit.unit)
            (g.f PUnit.unit)
            (α.f PUnit.unit)
            (β.f PUnit.unit)
            (by
              -- Proof comment: this is the same evaluated square, only reassociated.
              simpa using congrArg (fun ζ ↦ ζ.f PUnit.unit) w)) := by
              simp [Category.assoc]

/-- Helper for Lemma 12.23.3: the source graded piece is identified with the pointwise cokernel
model used in the raw object row. -/
private noncomputable def gradedPiece_component_iso (p : ℤ) :
    (gradedPiece K p).X PUnit.unit ≅
      cokernel ((stageMapOfLE K (le_succ_int p)).f PUnit.unit) :=
  one_object_cokernel_component_iso (C := C) (stageMapOfLE K (le_succ_int p))

/-- Helper for Lemma 12.23.3: the middle two-step quotient differential object is identified with
its pointwise cokernel model. -/
private noncomputable def twoStepQuotient_component_iso (p : ℤ) :
    (twoStepQuotientDifferentialObject K p).X PUnit.unit ≅
      cokernel ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit) :=
  one_object_cokernel_component_iso (C := C) (stageMapOfLE K (int_le_add_two p))

/-- Helper for Lemma 12.23.3: after transporting source and target to pointwise cokernels, the
left map of the owner-level row is the raw left cokernel map. -/
private theorem gradedPieceSuccToTwoStepQuotient_component (p : ℤ) :
    (gradedPiece_component_iso K (p + 1)).inv ≫
        (gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit ≫
        (twoStepQuotient_component_iso K p).hom =
      twoStepGradedObjectRawLeft K p := by
  -- Proof comment: expand the owner-level map to the underlying `cokernel.map`, then use the
  -- evaluated `cokernel.map` transport lemma to identify it with the raw left map.
  have hcomponent :=
    one_object_cokernel_map_component (C := C)
      (stageMapOfLE K (le_succ_int (p + 1)))
      (stageMapOfLE K (int_le_add_two p))
      (𝟙 _)
      (stageMapOfLE K (le_succ_int p))
      (gradedPieceSuccToTwoStepQuotient_condition K p)
  -- Proof comment: after rewriting the owner map through its cokernel presentation, the source
  -- component isomorphism cancels and leaves the raw induced cokernel map.
  simpa [gradedPieceSuccToTwoStepQuotientHom, gradedPieceCokernelIso, gradedPiece_eq_cokernel,
    gradedPiece_component_iso, twoStepQuotient_component_iso, Category.assoc] using
    congrArg (fun ζ ↦ (gradedPiece_component_iso K (p + 1)).inv ≫ ζ) hcomponent

/-- Helper for Lemma 12.23.3: after transporting source and target to pointwise cokernels, the
right map of the owner-level row is the raw right cokernel map. -/
private theorem twoStepQuotientToGradedPiece_component (p : ℤ) :
    (twoStepQuotient_component_iso K p).inv ≫
        (twoStepQuotientToGradedPieceHom K p).f PUnit.unit ≫
        (gradedPiece_component_iso K p).hom =
      twoStepGradedObjectRawRight K p := by
  -- Proof comment: as on the left map, reduce to the evaluated `cokernel.map` and conjugate by
  -- the componentwise cokernel identifications.
  have hcomponent :=
    one_object_cokernel_map_component (C := C)
      (stageMapOfLE K (int_le_add_two p))
      (stageMapOfLE K (le_succ_int p))
      (stageMapOfLE K (le_succ_int (p + 1)))
      (𝟙 _)
      (twoStepQuotientToGradedPiece_condition K p)
  -- Proof comment: after rewriting the owner map through its cokernel presentation, the middle
  -- component isomorphism cancels and leaves the raw quotient projection.
  refine (cancel_epi (twoStepQuotient_component_iso K p).hom).1 ?_
  calc
    (twoStepQuotient_component_iso K p).hom ≫
        ((twoStepQuotient_component_iso K p).inv ≫
          (twoStepQuotientToGradedPieceHom K p).f PUnit.unit ≫
          (gradedPiece_component_iso K p).hom)
        =
      (twoStepQuotientToGradedPieceHom K p).f PUnit.unit ≫
        (gradedPiece_component_iso K p).hom := by
          simp [Category.assoc]
    _ = (twoStepQuotient_component_iso K p).hom ≫
          twoStepGradedObjectRawRight K p := by
            simpa [twoStepQuotientToGradedPieceHom, gradedPieceCokernelIso,
              gradedPiece_eq_cokernel, Category.assoc] using hcomponent

-- The composite `gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K` is zero because the quotient to
-- `gr^p K` kills the image of the preceding stage.
-- Proof sketch: the projection to `gr^p K` kills the image of `F^{p + 1} K ⟶ F^p K`, and the
-- first map is induced by that inclusion.
/-- Helper for Lemma 12.23.3: at the object level, the projection to `gr^p(K)` kills the image of
`gr^{p + 1}(K) ⟶ F^p K / F^{p + 2} K`. -/
private theorem two_step_graded_object_raw_comp_zero (p : ℤ) :
    twoStepGradedObjectRawLeft K p ≫ twoStepGradedObjectRawRight K p = 0 := by
  -- Proof comment: precompose with the source cokernel projection; the first induced cokernel map
  -- becomes the stage inclusion `F^{p + 1} K ⟶ F^p K`, which the second induced cokernel map sends
  -- to zero by the defining cokernel relation.
  refine (cancel_epi (cokernel.π ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit))).1 ?_
  calc
    cokernel.π ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit) ≫
        twoStepGradedObjectRawLeft K p ≫ twoStepGradedObjectRawRight K p
        =
          (stageMapOfLE K (le_succ_int p)).f PUnit.unit ≫
            cokernel.π ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit) ≫
              twoStepGradedObjectRawRight K p := by
                simp [twoStepGradedObjectRawLeft, Category.assoc, cokernel.map]
    _ = (stageMapOfLE K (le_succ_int p)).f PUnit.unit ≫
          (𝟙 _) ≫
            cokernel.π ((stageMapOfLE K (le_succ_int p)).f PUnit.unit) := by
              simp [twoStepGradedObjectRawRight, Category.assoc, cokernel.map]
    _ = 0 := by
          simpa [Category.assoc] using
            (cokernel.condition ((stageMapOfLE K (le_succ_int p)).f PUnit.unit))
    _ = cokernel.π ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit) ≫ 0 := by
          symm
          simpa using
            (show
              cokernel.π ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit) ≫
                  (0 :
                    cokernel ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit) ⟶
                      cokernel ((stageMapOfLE K (le_succ_int p)).f PUnit.unit)) =
                0 from comp_zero)

private theorem twoStepGradedShortComplex_zero (p : ℤ) :
    gradedPieceSuccToTwoStepQuotientHom K p ≫ twoStepQuotientToGradedPieceHom K p = 0 := by
  -- Proof comment: compare the unique component after precomposing with the source cokernel
  -- projection; the resulting object-level composite is the defining cokernel relation.
  ext n
  cases n
  -- Proof comment: after transporting the unique component to the raw cokernel row, the owner
  -- composite is exactly the raw composite already known to vanish.
  apply (cancel_mono (gradedPiece_component_iso K p).hom).1
  have hleft :
      ((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit) ≫
          (twoStepQuotient_component_iso K p).hom =
        (gradedPiece_component_iso K (p + 1)).hom ≫
          twoStepGradedObjectRawLeft K p := by
    simpa [Category.assoc] using
      congrArg
        (fun ζ ↦ (gradedPiece_component_iso K (p + 1)).hom ≫ ζ)
        (gradedPieceSuccToTwoStepQuotient_component (C := C) K p)
  have hright :
      ((twoStepQuotientToGradedPieceHom K p).f PUnit.unit) ≫
          (gradedPiece_component_iso K p).hom =
        (twoStepQuotient_component_iso K p).hom ≫
          twoStepGradedObjectRawRight K p := by
    simpa [Category.assoc] using
      congrArg
        (fun ζ ↦ (twoStepQuotient_component_iso K p).hom ≫ ζ)
        (twoStepQuotientToGradedPiece_component (C := C) K p)
  simpa [Category.assoc] using
    calc
      (((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit) ≫
          ((twoStepQuotientToGradedPieceHom K p).f PUnit.unit)) ≫
          (gradedPiece_component_iso K p).hom
          =
        ((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit) ≫
          (((twoStepQuotientToGradedPieceHom K p).f PUnit.unit) ≫
            (gradedPiece_component_iso K p).hom) := by
              simp [Category.assoc]
      _ =
        ((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit) ≫
          ((twoStepQuotient_component_iso K p).hom ≫
            twoStepGradedObjectRawRight K p) := by
              rw [hright]
      _ =
        (((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit) ≫
            (twoStepQuotient_component_iso K p).hom) ≫
          twoStepGradedObjectRawRight K p := by
            simp [Category.assoc]
      _ =
        ((gradedPiece_component_iso K (p + 1)).hom ≫
            twoStepGradedObjectRawLeft K p) ≫
          twoStepGradedObjectRawRight K p := by
            rw [hleft]
      _ =
        (gradedPiece_component_iso K (p + 1)).hom ≫
          (twoStepGradedObjectRawLeft K p ≫ twoStepGradedObjectRawRight K p) := by
            simp [Category.assoc]
      _ = (gradedPiece_component_iso K (p + 1)).hom ≫ 0 := by
            rw [two_step_graded_object_raw_comp_zero]
      _ = 0 := by
            simpa using
              (show
                (gradedPiece_component_iso K (p + 1)).hom ≫
                    (0 :
                      cokernel ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit) ⟶
                        cokernel ((stageMapOfLE K (le_succ_int p)).f PUnit.unit)) =
                  0 from comp_zero)

/-- Helper for Lemma 12.23.3: evaluating the owner short complex at the unique object produces the
object-level zero relation needed for degreewise exactness. -/
private theorem twoStepGradedShortComplex_zero_f (p : ℤ) :
    ((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit) ≫
        ((twoStepQuotientToGradedPieceHom K p).f PUnit.unit) =
      0 := by
  -- Proof comment: this is the component at `PUnit.unit` of the owner-level zero-composite.
  simpa using congrArg (fun φ ↦ φ.f PUnit.unit) (twoStepGradedShortComplex_zero K p)

/-- The short complex of one-object differential objects
`gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K`. -/
private noncomputable def twoStepGradedShortComplex (p : ℤ) :
    ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1})) :=
  ShortComplex.mk
    (gradedPieceSuccToTwoStepQuotientHom K p)
    (twoStepQuotientToGradedPieceHom K p)
    (twoStepGradedShortComplex_zero K p)

/-- Helper for Lemma 12.23.3: evaluating the owner two-step row at the unique object identifies
it with the raw cokernel row used for the pointwise short-exactness proof. -/
private noncomputable def owner_row_to_raw_shortComplex_iso (p : ℤ) :
    ShortComplex.mk
        ((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit)
        ((twoStepQuotientToGradedPieceHom K p).f PUnit.unit)
        (twoStepGradedShortComplex_zero_f K p) ≅
      ShortComplex.mk
        (twoStepGradedObjectRawLeft K p)
        (twoStepGradedObjectRawRight K p)
        (two_step_graded_object_raw_comp_zero K p) := by
  -- Proof comment: package the left and right component identifications into one reusable
  -- short-complex isomorphism, so later exactness transport can avoid repeating reassociations.
  refine ShortComplex.isoMk
    (gradedPiece_component_iso K (p + 1))
    (twoStepQuotient_component_iso K p)
    (gradedPiece_component_iso K p)
    ?_ ?_
  · simpa [Category.assoc] using
      (congrArg
        (fun ζ ↦ (gradedPiece_component_iso K (p + 1)).hom ≫ ζ)
        (gradedPieceSuccToTwoStepQuotient_component (C := C) K p)).symm
  · simpa [Category.assoc] using
      (congrArg
        (fun ζ ↦ (twoStepQuotient_component_iso K p).hom ≫ ζ)
        (twoStepQuotientToGradedPiece_component (C := C) K p)).symm

/-- Helper for Lemma 12.23.3: the raw left map is monomorphic because it is the cokernel map of
the pullback square coming from the nested inclusions
`F^{p + 2} K ⟶ F^{p + 1} K ⟶ F^p K`. -/
private theorem two_step_graded_object_raw_left_mono (p : ℤ) :
    Mono (twoStepGradedObjectRawLeft K p) := by
  -- Proof comment: the nested-stage square
  -- `F^{p + 2} K -> F^{p + 1} K`
  -- `|                 |`
  -- `v                 v`
  -- `F^{p + 2} K -> F^p K`
  -- is a pullback, so the induced cokernel map is monic.
  -- TODO: rebuild the pullback square in the exact orientation consumed by
  -- `Abelian.mono_cokernel_map_of_isPullback`, first for the owner component
  -- `((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit)`, and then conjugate that mono
  -- statement through `gradedPieceSuccToTwoStepQuotient_component`.
  sorry

/-- Helper for Lemma 12.23.3: the raw quotient projection
`F^p K / F^{p + 2} K ⟶ gr^p(K)` is the cokernel of the raw inclusion
`gr^{p + 1}(K) ⟶ F^p K / F^{p + 2} K`. -/
private noncomputable def two_step_graded_object_raw_right_is_cokernel (p : ℤ) :
    IsColimit
      (CokernelCofork.ofπ
        (twoStepGradedObjectRawRight K p)
        (two_step_graded_object_raw_comp_zero K p)) := by
  let a := ((stageMapOfLE K (le_succ_int (p + 1))).f PUnit.unit)
  let b := ((stageMapOfLE K (le_succ_int p)).f PUnit.unit)
  let c := ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit)
  let leftRaw : cokernel a ⟶ cokernel c :=
    cokernel.map a c (𝟙 _) b (by
      simpa using congrArg (fun α ↦ α.f PUnit.unit)
        (gradedPieceSuccToTwoStepQuotient_condition K p))
  have hfac :
      cokernel.π c ≫ twoStepGradedObjectRawRight K p = cokernel.π b := by
    -- Proof comment: the raw right map is defined by factoring the quotient map to `gr^p(K)`.
    simp [twoStepGradedObjectRawRight, a, b, c, Category.assoc]
  letI : Epi (twoStepGradedObjectRawRight K p) := epi_of_epi_fac hfac
  -- Proof comment: as in the degreewise proof for complexes, any map out of the two-step
  -- quotient that kills `gr^{p + 1}(K)` descends uniquely through the quotient by `F^{p + 1}K`.
  refine CokernelCofork.IsColimit.ofπ'
    (twoStepGradedObjectRawRight K p)
    (two_step_graded_object_raw_comp_zero K p)
    ?_
  intro Z k hk
  have hkRaw : leftRaw ≫ k = 0 := by
    simpa [leftRaw, twoStepGradedObjectRawLeft, a, b, c] using hk
  have hdesc :
      b ≫ (cokernel.π c ≫ k) = 0 := by
    calc
      b ≫ (cokernel.π c ≫ k) = cokernel.π a ≫ leftRaw ≫ k := by
        simp [leftRaw, a, b, c, Category.assoc]
      _ = cokernel.π a ≫ 0 := by
        rw [hkRaw]
      _ = 0 := by
        simpa using
          (show cokernel.π a ≫ (0 : cokernel a ⟶ Z) = 0 from comp_zero)
  -- Proof comment: after precomposing with `F^p K ⟶ F^p K / F^{p + 2} K`, the factorization is
  -- exactly the defining equation of `cokernel.desc`.
  refine ⟨cokernel.desc b (cokernel.π c ≫ k) hdesc, ?_⟩
  apply (cancel_epi (cokernel.π c)).1
  simp [twoStepGradedObjectRawRight, a, b, c, Category.assoc, hdesc]

/-- Helper for Lemma 12.23.3: the raw object-level row
`gr^{p + 1}(K) ⟶ F^p K / F^{p + 2} K ⟶ gr^p(K)` is exact. -/
private theorem two_step_graded_object_raw_exact (p : ℤ) :
    (ShortComplex.mk
      (twoStepGradedObjectRawLeft K p)
      (twoStepGradedObjectRawRight K p)
      (two_step_graded_object_raw_comp_zero K p)).Exact := by
  -- Proof comment: prove directly that the raw projection
  -- `F^p K / F^{p + 2} K ⟶ gr^p(K)` is the cokernel of the raw inclusion
  -- `gr^{p + 1}(K) ⟶ F^p K / F^{p + 2} K`.
  let S : ShortComplex C :=
    ShortComplex.mk
      (twoStepGradedObjectRawLeft K p)
      (twoStepGradedObjectRawRight K p)
      (two_step_graded_object_raw_comp_zero K p)
  have hS :
      IsColimit (CokernelCofork.ofπ S.g S.zero) := by
    simpa [S] using
      (two_step_graded_object_raw_right_is_cokernel (C := C) K p)
  exact ShortComplex.exact_of_g_is_cokernel S hS

/-- Helper for Lemma 12.23.3: the raw right map is epimorphic because the quotient
`F^p K ⟶ gr^p(K)` factors through `F^p K / F^{p + 2} K`. -/
private theorem two_step_graded_object_raw_right_epi (p : ℤ) :
    Epi (twoStepGradedObjectRawRight K p) := by
  have hfac :
      cokernel.π ((stageMapOfLE K (int_le_add_two p)).f PUnit.unit) ≫
          twoStepGradedObjectRawRight K p =
        cokernel.π ((stageMapOfLE K (le_succ_int p)).f PUnit.unit) := by
    -- Proof comment: this is the defining cokernel-factorization equation for the induced map.
    simp [twoStepGradedObjectRawRight]
  -- Proof comment: the target quotient map is epi, so its factor through the intermediate
  -- quotient is epi as well.
  exact epi_of_epi_fac hfac

/-- The short complex
`0 ⟶ gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K ⟶ 0`
is short exact in one-object differential objects. -/
-- Proof sketch: evaluate the complex at the unique object `PUnit.unit`; this gives the usual
-- graded-piece short exact sequence of cokernels associated to the filtration stages.
private theorem twoStepGradedShortExact (p : ℤ) :
    (twoStepGradedShortComplex K p).ShortExact := by
  -- Proof comment: evaluate the one-object complex at `PUnit.unit` and prove the resulting row of
  -- objects is short exact, then lift back to the homological-complex owner.
  -- Route correction: the owner/raw component identifications are now packaged into
  -- `owner_row_to_raw_shortComplex_iso`. The remaining blocker is to finish the raw pointwise
  -- mono/exact package, then transport those three short-exact ingredients back to one-object
  -- complexes.
  -- TODO: build the owner/raw short-complex isomorphism from
  -- `gradedPieceSuccToTwoStepQuotient_component` and
  -- `twoStepQuotientToGradedPiece_component`, then lift
  -- `two_step_graded_object_raw_exact K p`, `two_step_graded_object_raw_left_mono K p`, and
  -- `two_step_graded_object_raw_right_epi K p` through
  -- `HomologicalComplex.exact_iff_degreewise_exact`,
  -- `HomologicalComplex.mono_of_mono_f`, and `HomologicalComplex.epi_of_epi_f`.
  have hrawShort :
      (ShortComplex.mk
        (twoStepGradedObjectRawLeft K p)
        (twoStepGradedObjectRawRight K p)
        (two_step_graded_object_raw_comp_zero K p)).ShortExact := by
    -- Proof comment: the raw row is short exact once exactness, left-monicity, and right-epicity
    -- are proved directly on the cokernel presentation.
    exact ShortComplex.ShortExact.mk'
      (two_step_graded_object_raw_exact (C := C) K p)
      (two_step_graded_object_raw_left_mono (C := C) K p)
      (two_step_graded_object_raw_right_epi (C := C) K p)
  have hownerEvalShort :
      (ShortComplex.mk
        ((gradedPieceSuccToTwoStepQuotientHom K p).f PUnit.unit)
        ((twoStepQuotientToGradedPieceHom K p).f PUnit.unit)
        (twoStepGradedShortComplex_zero_f K p)).ShortExact := by
    -- Proof comment: transport the raw short exact row back through the owner/raw componentwise
    -- identifications, so the unique evaluated row inherits the same short exactness package.
    exact ShortComplex.shortExact_of_iso
      (owner_row_to_raw_shortComplex_iso (C := C) K p).symm hrawShort
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · -- Proof comment: exactness of one-object complexes is detected at the unique object.
    rw [HomologicalComplex.exact_iff_degreewise_exact]
    intro n
    cases n
    simpa [twoStepGradedShortComplex] using hownerEvalShort.exact
  · -- Proof comment: monomorphy of the owner left map is detected on its unique component.
    exact HomologicalComplex.mono_of_mono_f _ (fun n ↦ by
      cases n
      simpa [twoStepGradedShortComplex] using hownerEvalShort.mono_f)
  · -- Proof comment: epimorphy of the owner right map is detected on its unique component.
    exact HomologicalComplex.epi_of_epi_f _ (fun n ↦ by
      cases n
      simpa [twoStepGradedShortComplex] using hownerEvalShort.epi_g)

/-- The boundary map
`H(gr^p K) ⟶ H(gr^{p + 1} K)`
attached to the short exact sequence
`0 ⟶ gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K ⟶ 0`. -/
noncomputable def pageOneBoundaryMap (p : ℤ) :
    (gradedPiece K p).homology PUnit.unit ⟶
      (gradedPiece K (p + 1)).homology PUnit.unit :=
  (twoStepGradedShortExact K p).δ PUnit.unit PUnit.unit rfl

-- Proof sketch: for an associated spectral sequence `E` of `K`, the page-`E₁` comparison is the
-- owner isomorphism `pageOneIso K E`, and the source-facing statement is that under this
-- identification the `d₁` differential is the connecting morphism of the graded short exact
-- sequence.
/-- Lemma 12.23.3: for an associated spectral sequence `E` of the filtered differential object
`K`, the differential `d_1^p : E₁^p ⟶ E₁^{p + 1}` agrees, under the canonical page-`E₁`
identifications from Lemma `12.23.2`, with the boundary map in homology attached to the short
exact sequence of differential objects
`0 ⟶ gr^{p + 1} K ⟶ F^p K / F^{p + 2} K ⟶ gr^p K ⟶ 0`. -/
theorem pageOne_differential_eq_boundary_map
    (E : SpectralSequence C (fun r ↦ ComplexShape.up' (r : ℤ)) 0)
    [IsAssociatedToFilteredDifferentialObject K E]
    (p : ℤ) :
    (E.page 1).d p (p + 1) ≫ (pageOneIso K E (p + 1)).hom =
      (pageOneIso K E p).hom ≫ pageOneBoundaryMap K p := by
  -- Proof comment: transport the owner page-one differential through `E.iso 0 1`, the page-zero
  -- identification, and the page-zero homology comparison, then apply the bridge lemma above.
  -- TODO: first prove the bridge
  -- `((pageZero K).homology.d p (p + 1)) ≫ (pageZeroHomologyIso K (p + 1)).hom =
  --   (pageZeroHomologyIso K p).hom ≫ pageOneBoundaryMap K p`
  -- from the short exact row above, then rewrite `pageOneIso` as
  -- `(E.iso 0 1 p).symm ≪≫ HomologicalComplex.homologyMapIso (pageZeroIso K E) p ≪≫
  --   pageZeroHomologyIso K p`
  -- and transport `(E.page 1).d` through `E.iso 0 1` and `pageZeroIso`.
  -- TODO: after the bridge lemma above is proved, transport `(E.page 1).d` through `E.iso 0 1`
  -- and `pageZeroIso K E`, then finish with
  -- `pageZero_homology_d_eq_pageOneBoundaryMap K p`.
  -- TODO: transport `(E.page 1).d` through `(E.iso 0 1).symm` and
  -- `HomologicalComplex.homologyMapIso (pageZeroIso K E)`, then close with
  -- `pageZero_homology_d_eq_pageOneBoundaryMap K p`.
  sorry

end HomologicalComplex.Filtered

end CategoryTheory
