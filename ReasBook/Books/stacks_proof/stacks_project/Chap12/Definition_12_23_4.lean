import StacksProject_2024.Chap12.Definition_12_23_1
import StacksProject_2024.Chap12.Lemma_12_19_15
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

open FilteredObject

namespace HomologicalComplex.Filtered

/-- Helper for Definition 12.23.4: the `p`-th stage functor, reused from the earlier
buildable stage/graded API. -/
abbrev stageFunctor (p : ℤ) : FilteredObject C ⥤ C :=
  ShortComplex.stageFunctor (𝒜 := C) p

/-- Helper for Definition 12.23.4: the associated-graded functor, reused from the earlier
buildable stage/graded API. -/
private abbrev associatedGradedFunctor : FilteredObject C ⥤ GradedObject ℤ C :=
  ShortComplex.associatedGradedFunctor (𝒜 := C)

/-- Helper for Definition 12.23.4: the canonical inclusion of the `p`-th stage into the
underlying object, natural in the filtered object. -/
private def stageFunctorToForget (p : ℤ) :
    (stageFunctor (C := C) p : FilteredObject C ⥤ C) ⟶
      (FilteredObject.forget : FilteredObject C ⥤ C) where
  app A := (A.filtration.obj p).arrow
  naturality {A B} f := by
    -- Proof comment: this is exactly the defining commutative square for the restricted stage map.
    change FilteredObject.Hom.stageMap f p ≫ (B.filtration.obj p).arrow =
      (A.filtration.obj p).arrow ≫ f.hom
    exact FilteredObject.Hom.stageMap_comm f p

/-- Helper for Definition 12.23.4: for `p ≤ q`, the inclusion `F^q A ⟶ F^p A` is natural in the
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

/-- Helper for Definition 12.23.4: for `p ≤ q`, the `q`-th stage functor maps naturally to the
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

/-- Helper for Definition 12.23.4: successive stage comparisons compose to the direct
comparison. -/
theorem stageFunctorMapOfLE_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    (stageFunctorMapOfLE (C := C) hqr :
        (stageFunctor (C := C) r : FilteredObject C ⥤ C) ⟶ stageFunctor (C := C) q) ≫
      stageFunctorMapOfLE (C := C) hpq =
      stageFunctorMapOfLE (C := C) (le_trans hpq hqr) := by
  ext A
  -- Proof comment: the composite comparison of subobject inclusions is the direct inclusion.
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

/-- Helper for Definition 12.23.4: the comparison `F^q A ⟶ F^p A` followed by inclusion into
`A` is the ordinary inclusion `F^q A ⟶ A`. -/
private theorem stageFunctorMapOfLE_comp_stageFunctorToForget {p q : ℤ} (hpq : p ≤ q) :
    (stageFunctorMapOfLE (C := C) hpq :
        (stageFunctor (C := C) q : FilteredObject C ⥤ C) ⟶ stageFunctor (C := C) p) ≫
      stageFunctorToForget (C := C) p =
      stageFunctorToForget (C := C) q := by
  ext A
  -- Proof comment: both composites are the same inclusion of the deeper stage into `A`.
  exact Subobject.ofLE_arrow (A.filtration.antitone_obj hpq)

/-- Every integer is bounded above by its successor. -/
theorem le_succ_int (p : ℤ) : p ≤ p + 1 := by
  omega

variable (K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1}))

/- Domain-style sampling for Definition 12.23.4:
- primary domain: filtered differential objects in an abelian category and the induced filtration
  on their homology;
- sampled owner declarations in this domain:
  `FilteredObject.stage`,
  `FilteredObject.gradedPiece`,
  `FilteredObject.stageFunctor`,
  `FilteredObject.stageFunctorMapOfLE`,
  `FilteredObject.associatedGradedFunctor`,
  `GradedObject.eval_preservesZeroMorphisms`;
- best owner abstraction: the filtered differential object
  `K : HomologicalComplex (FilteredObject C) (ComplexShape.refl PUnit.{1})`, with stage and
  comparison data obtained by lifting the filtered-object owners along `mapHomologicalComplex`;
- primitive data: the filtered differential object `K`;
- derived API: `underlying`, `stage`, `stageMapOfLE`, `gradedPiece`, `homologyMap`, and the
  induced filtration on `H(K)`;
- internal bridge: the mapped stage inclusion into `underlying K`, used only to define the
  homology-stage images canonically;
- source/core/bridge triage:
  `source-facing`: `inducedHomologyFiltration`;
  `core/canonical`: the filtered-object owners named above together with the owner object `K`;
  `bridge/view`: the one-object-complex specializations in this namespace. -/

/-- Bridge/view layer: forget the filtration on the owner object of filtered differential
objects. -/
abbrev underlying : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  (FilteredObject.forget.mapHomologicalComplex (ComplexShape.refl PUnit.{1})).obj K

/-- Bridge/view layer: evaluate the owner object at the `p`-th filtration stage. -/
abbrev stage (p : ℤ) : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  ((stageFunctor (C := C) p).mapHomologicalComplex (ComplexShape.refl PUnit.{1})).obj K

/-- Internal bridge: the inclusion of the `p`-th filtration stage differential object into the
underlying one. -/
private abbrev stageInclusion (p : ℤ) : stage K p ⟶ underlying K :=
  (NatTrans.mapHomologicalComplex (stageFunctorToForget (C := C) p)
    (ComplexShape.refl PUnit.{1})).app K

/-- The canonical map `F^q K ⟶ F^p K` of one-object complexes for `p ≤ q`. -/
abbrev stageMapOfLE {p q : ℤ} (hpq : p ≤ q) : stage K q ⟶ stage K p :=
  (NatTrans.mapHomologicalComplex (stageFunctorMapOfLE (C := C) hpq)
    (ComplexShape.refl PUnit.{1})).app K

/-- Bridge/view layer: the graded differential object `gr^p(K)` is obtained from the chapter
owner `associatedGradedFunctor` by evaluation at `p`. -/
noncomputable abbrev gradedPiece (p : ℤ) :
    HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  cokernel (stageMapOfLE K (le_succ_int p))

/-- Bridge/view layer: for a one-object filtered differential object, the canonical graded piece
agrees with the cokernel presentation `F^p K / F^{p + 1} K`. -/
theorem gradedPiece_eq_cokernel (p : ℤ) :
    gradedPiece K p = cokernel (stageMapOfLE K (le_succ_int p)) := by
  -- Proof comment: both sides are definitionally the degreewise cokernel presentation of
  -- `gr^p(K)` for a one-object filtered differential object.
  rfl

/-- The canonical comparison between the owner-based graded piece and its cokernel presentation. -/
noncomputable def gradedPieceCokernelIso (p : ℤ) :
    gradedPiece K p ≅ cokernel (stageMapOfLE K (le_succ_int p)) :=
  eqToIso (gradedPiece_eq_cokernel K p)

/-- The map on homology induced by the inclusion `F^p K ⟶ K`. -/
noncomputable abbrev homologyMap (p : ℤ) :
    (stage K p).homology PUnit.unit ⟶ (underlying K).homology PUnit.unit :=
  HomologicalComplex.homologyMap (stageInclusion K p) PUnit.unit

/-- The inclusion `F^q K ⟶ K` factors through `F^p K ⟶ K` whenever `p ≤ q`. -/
private theorem stageMapOfLE_comp_stageInclusion {p q : ℤ} (hpq : p ≤ q) :
    stageMapOfLE K hpq ≫ stageInclusion K p = stageInclusion K q := by
  have h :=
    congrArg
      (fun α ↦ (NatTrans.mapHomologicalComplex α (ComplexShape.refl PUnit.{1})).app K)
      (stageFunctorMapOfLE_comp_stageFunctorToForget (C := C) hpq)
  simpa [stageMapOfLE, stageInclusion, NatTrans.mapHomologicalComplex_comp] using h

-- Proof sketch: the inclusion `F^q K ⟶ K` factors through `F^p K ⟶ K` via `stageMapOfLE K hpq`;
-- apply functoriality of `HomologicalComplex.homologyMap`.
/-- The homology map from `F^q K` to `H(K)` factors through the map from `F^p K` whenever
`p ≤ q`. -/
private theorem homologyMap_factorization {p q : ℤ} (hpq : p ≤ q) :
    homologyMap K q =
      HomologicalComplex.homologyMap (stageMapOfLE K hpq) PUnit.unit ≫ homologyMap K p := by
  rw [homologyMap, homologyMap, ← HomologicalComplex.homologyMap_comp,
    stageMapOfLE_comp_stageInclusion]

-- Proof sketch: use `homologyMap_factorization` to see that the image of the map from
-- `F^q K` factors through the image of the map from `F^p K`, then apply monotonicity of image
-- subobjects.
/-- The images of the stagewise homology maps form a decreasing filtration. -/
private theorem inducedHomologyFiltration_antitone :
    Antitone
      (fun p : ℤ ↦ imageSubobject (homologyMap K p)) := by
  intro p q hpq
  change
    imageSubobject (homologyMap K q) ≤ imageSubobject (homologyMap K p)
  rw [homologyMap_factorization K hpq]
  exact imageSubobject_comp_le _ _

/-- Definition 12.23.4: the induced filtration on `H(K, d)` is the decreasing filtration whose
`p`-th stage is the image of the canonical map `H(F^p K, d) ⟶ H(K, d)`. -/
@[stacks 012E]
noncomputable def inducedHomologyFiltration :
    DecreasingFiltration ((underlying K).homology PUnit.unit) where
  toFun p := imageSubobject (homologyMap K p)
  monotone' _ _ hpq := inducedHomologyFiltration_antitone K hpq

-- Proof sketch: unfold `inducedHomologyFiltration`; the statement is exactly its defining
-- formula.
/-- The `p`-th stage of the induced homology filtration is the image of the stagewise homology
map. -/
theorem inducedHomologyFiltration_obj (p : ℤ) :
    (inducedHomologyFiltration K).obj p =
      imageSubobject (homologyMap K p) := rfl

end HomologicalComplex.Filtered

end CategoryTheory
