import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_24_5
import StacksProject_2024.stacks_project.Chap13.Lemma_13_11_2
import StacksProject_2024.stacks_project.Chap19.Theorem_19_12_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe w v u

namespace CategoryTheory

section

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] HasDerivedCategory.standard

/-
Domain-style sampling for Lemma 19.13.12:
- primary domain: filtered complexes in a Grothendieck abelian category and their realization in
  the derived category;
- sampled owner declarations:
  `Cocone`,
  `FilteredComplex`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.stageInclusion`,
  `FilteredComplex.stageMapOfLE`,
  `DerivedCategory.Q`,
  `Cocone.precompose`;
- best owner abstraction: `FilteredComplex A`;
- primitive data: a filtered complex `K : FilteredComplex A`;
- derived API: the stage tower `K.stageTower : ℤᵒᵖ ⥤ DerivedCategory A`, its canonical cocone
  `K.stageTowerCocone`, and the comparison to a given cocone `c : Cocone system` via
  `Cocone.precompose`;
- source/core/bridge triage:
  `source-facing`: `FilteredComplex.RealizesInverseSystem` and the existence theorem below;
  `core/canonical`: the owner object `FilteredComplex A`;
  `bridge/view`: the derived-category functor `stageTower`, the cocone `stageTowerCocone`, and
    cocone isomorphisms against a prescribed inverse-system cocone.

The previous version still unpacked realization as objectwise isomorphisms plus manually stated
compatibility squares. This file keeps the owner public and records the compatible target family at
the canonical functor/cocone layer. -/

namespace FilteredComplex

/-- The inverse-system tower in `D(A)` attached to the filtration stages of `K`. -/
noncomputable def stageTower (K : FilteredComplex A) : ℤᵒᵖ ⥤ DerivedCategory A where
  obj i := DerivedCategory.Q.obj (K.stage i.unop)
  map {i j} f := DerivedCategory.Q.map (K.stageMapOfLE f.unop.le)
  map_id i := by
    simp [FilteredComplex.stageMapOfLE_refl]
  map_comp f g := by
    rw [← DerivedCategory.Q.map_comp, FilteredComplex.stageMapOfLE_comp]

/-- The canonical cocone from the stage tower of `K` to the derived object represented by its
underlying complex. -/
noncomputable def stageTowerCocone (K : FilteredComplex A) : Cocone K.stageTower where
  pt := DerivedCategory.Q.obj K.underlying
  ι :=
    { app := fun i ↦ DerivedCategory.Q.map (K.stageInclusion i.unop)
      naturality := by
        intro i j f
        change
          DerivedCategory.Q.map (K.stageMapOfLE f.unop.le) ≫
              DerivedCategory.Q.map (K.stageInclusion j.unop) =
            DerivedCategory.Q.map (K.stageInclusion i.unop)
        rw [← DerivedCategory.Q.map_comp, FilteredComplex.stageMapOfLE_comp_stageInclusion] }

/-- A filtered complex realizes an inverse system in the derived category if its stage tower is
naturally isomorphic to the system and its canonical cocone identifies with the prescribed cocone
after transport along that natural isomorphism. -/
def RealizesInverseSystem
    (K : FilteredComplex A) {system : ℤᵒᵖ ⥤ DerivedCategory A} (c : Cocone system) : Prop :=
  ∃ stageIso : K.stageTower ≅ system,
    ∃ coconeHom : K.stageTowerCocone ⟶ (Cocone.precompose stageIso.hom).obj c,
      IsIso coconeHom

end FilteredComplex

variable [IsGrothendieckAbelian.{w} A]

/-- Helper for Lemma 19.13.12: an acyclic cochain complex represents the zero object of the
derived category. -/
private theorem qObjIsZeroOfAcyclic
    (L : CochainComplex A ℤ) (hL : L.Acyclic) :
    IsZero (DerivedCategory.Q.obj L) := by
  let KL : HomotopyCategory A (ComplexShape.up ℤ) :=
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj L
  let eQh :
      DerivedCategory.Qh.obj KL ≅ DerivedCategory.Q.obj L := by
    simpa [KL, HomotopyCategory.quotient_obj_as] using
      (DerivedCategory.quotientCompQhIso A).app L
  have hker :
      Functor.kernel
        (DerivedCategory.Qh :
          HomotopyCategory A (ComplexShape.up ℤ) ⥤ DerivedCategory A)
        KL := by
    have hAcyclicKL : (HomotopyCategory.subcategoryAcyclic A) KL := by
      simpa [KL] using
        (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
          (C := A) L).2 hL
    -- Proof comment: the Verdier kernel of `Qh` is exactly the acyclic subcategory.
    rw [subcategoryAcyclic_kernel_Qh (A := A)]
    simpa [Functor.kernel, ObjectProperty.prop_inverseImage_iff] using hAcyclicKL
  exact eQh.isZero_iff.2 hker

/-- Helper for Lemma 19.13.12: once the target is K-injective, a derived isomorphism can be
represented by an actual quasi-isomorphism of cochain complexes. -/
private lemma existsQuasiIsoToKInjectiveOfPointIso
    (L K : CochainComplex A ℤ) [K.IsKInjective]
    (e : DerivedCategory.Q.obj L ≅ DerivedCategory.Q.obj K) :
    ∃ u : L ⟶ K, QuasiIso u ∧ DerivedCategory.Q.map u = e.hom := by
  let KQ := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let eQh :
      DerivedCategory.Qh.obj (KQ.obj L) ≅ DerivedCategory.Qh.obj (KQ.obj K) :=
    (DerivedCategory.quotientCompQhIso A).app L ≪≫
      e ≪≫
        ((DerivedCategory.quotientCompQhIso A).app K).symm
  obtain ⟨uQ, huQh⟩ :=
    (CochainComplex.IsKInjective.Qh_map_bijective (KQ.obj L) K).surjective eQh.hom
  obtain ⟨u, rfl⟩ := KQ.map_surjective uQ
  refine ⟨u, ?_, ?_⟩
  · -- Proof comment: identifying `Q.map u` with the isomorphism `e.hom` upgrades `u` to a
    -- quasi-isomorphism by the standard derived-category criterion.
    have hQmap : DerivedCategory.Q.map u = e.hom := by
      have hcongr := congrArg
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
          ((DerivedCategory.quotientCompQhIso A).app K)) huQh
      have hmap :
          (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
            ((DerivedCategory.quotientCompQhIso A).app K))
              (DerivedCategory.Qh.map (KQ.map u)) =
            DerivedCategory.Q.map u := by
        -- Proof comment: this is the naturality square for `quotientCompQhIso`, rewritten as a
        -- conjugation identity on morphisms.
        change
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              DerivedCategory.Qh.map (KQ.map u) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
            DerivedCategory.Q.map u
        have hnat :
            DerivedCategory.Qh.map (KQ.map u) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
              (DerivedCategory.quotientCompQhIso A).hom.app L ≫
                DerivedCategory.Q.map u := by
          simpa [Functor.comp_map] using
            ((DerivedCategory.quotientCompQhIso A).hom.naturality u)
        calc
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              DerivedCategory.Qh.map (KQ.map u) ≫
                (DerivedCategory.quotientCompQhIso A).hom.app K =
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
              ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                DerivedCategory.Q.map u) := by
                  simpa [Category.assoc] using
                    congrArg
                      (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app L ≫ k) hnat
          _ = DerivedCategory.Q.map u := by
            simpa using
              (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
                (DerivedCategory.Q.map u))
      calc
        DerivedCategory.Q.map u =
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
              ((DerivedCategory.quotientCompQhIso A).app K))
                (DerivedCategory.Qh.map (KQ.map u)) := by
              simpa using hmap.symm
        _ =
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
              ((DerivedCategory.quotientCompQhIso A).app K)) eQh.hom := by
              simpa using hcongr
        _ = e.hom := by
          change
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                  e.hom ≫
                    (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K =
              e.hom
          have hleft :
              (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                  ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                    e.hom ≫
                      (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K =
                e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K := by
            simpa [Category.assoc] using
              (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
                (e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K))
          calc
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                  e.hom ≫
                    (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K =
              e.hom ≫
                (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K := hleft
            _ = e.hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ e.hom ≫ k)
                  (Iso.inv_hom_id ((DerivedCategory.quotientCompQhIso A).app K))
    letI : IsIso (DerivedCategory.Q.map u) := by
      rw [hQmap]
      infer_instance
    exact (DerivedCategory.isIso_Q_map_iff_quasiIso A u).1 inferInstance
  · -- Proof comment: the chosen map represents `e.hom` by construction.
    have hcongr := congrArg
      (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
        ((DerivedCategory.quotientCompQhIso A).app K)) huQh
    have hmap :
        (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
          ((DerivedCategory.quotientCompQhIso A).app K))
            (DerivedCategory.Qh.map (KQ.map u)) =
          DerivedCategory.Q.map u := by
      -- Proof comment: conjugating the `Qh`-image of `u` across `quotientCompQhIso` recovers
      -- the ordinary derived-category image.
      change
        (DerivedCategory.quotientCompQhIso A).inv.app L ≫
            DerivedCategory.Qh.map (KQ.map u) ≫
              (DerivedCategory.quotientCompQhIso A).hom.app K =
          DerivedCategory.Q.map u
      have hnat :
          DerivedCategory.Qh.map (KQ.map u) ≫
              (DerivedCategory.quotientCompQhIso A).hom.app K =
            (DerivedCategory.quotientCompQhIso A).hom.app L ≫
              DerivedCategory.Q.map u := by
        simpa [Functor.comp_map] using
          ((DerivedCategory.quotientCompQhIso A).hom.naturality u)
      calc
        (DerivedCategory.quotientCompQhIso A).inv.app L ≫
            DerivedCategory.Qh.map (KQ.map u) ≫
              (DerivedCategory.quotientCompQhIso A).hom.app K =
          (DerivedCategory.quotientCompQhIso A).inv.app L ≫
            ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
              DerivedCategory.Q.map u) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k ↦ (DerivedCategory.quotientCompQhIso A).inv.app L ≫ k) hnat
        _ = DerivedCategory.Q.map u := by
          simpa using
            (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
              (DerivedCategory.Q.map u))
    exact
      calc
        DerivedCategory.Q.map u =
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
              ((DerivedCategory.quotientCompQhIso A).app K))
                (DerivedCategory.Qh.map (KQ.map u)) := by
              simpa using hmap.symm
        _ =
            (Iso.homCongr ((DerivedCategory.quotientCompQhIso A).app L)
              ((DerivedCategory.quotientCompQhIso A).app K)) eQh.hom := by
                simpa using hcongr
        _ = e.hom := by
          change
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                  e.hom ≫
                    (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K =
              e.hom
          have hleft :
              (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                  ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                    e.hom ≫
                      (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K =
                e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K := by
            simpa [Category.assoc] using
              (Iso.inv_hom_id_assoc ((DerivedCategory.quotientCompQhIso A).app L)
                (e.hom ≫
                  (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                    (DerivedCategory.quotientCompQhIso A).hom.app K))
          calc
            (DerivedCategory.quotientCompQhIso A).inv.app L ≫
                ((DerivedCategory.quotientCompQhIso A).hom.app L ≫
                  e.hom ≫
                    (DerivedCategory.quotientCompQhIso A).inv.app K) ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K =
              e.hom ≫
                (DerivedCategory.quotientCompQhIso A).inv.app K ≫
                  (DerivedCategory.quotientCompQhIso A).hom.app K := hleft
            _ = e.hom := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ e.hom ≫ k)
                  (Iso.inv_hom_id ((DerivedCategory.quotientCompQhIso A).app K))

/-- Helper for Lemma 19.13.12: after fixing one K-injective representative of the cocone point,
any derived map into that point can be strictified to an actual roof landing in the fixed target.
-/
private lemma existsComplexMapToFixedKInjective
    (I : CochainComplex A ℤ) [I.IsKInjective]
    {E X : DerivedCategory A} (eI : DerivedCategory.Q.obj I ≅ E) (α : X ⟶ E) :
    ∃ (G : CochainComplex A ℤ) (σ : G ⟶ DerivedCategory.Q.objPreimage X) (_ : QuasiIso σ)
      (φ : G ⟶ I),
      DerivedCategory.Q.map σ ≫ (DerivedCategory.Q.objObjPreimageIso X).hom ≫ α =
        DerivedCategory.Q.map φ ≫ eI.hom := by
  let β : DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage X) ⟶ DerivedCategory.Q.obj I :=
    (DerivedCategory.Q.objObjPreimageIso X).hom ≫ α ≫ eI.inv
  obtain ⟨G, σ, hσ, φ, hβ⟩ := DerivedCategory.right_fac β
  refine ⟨G, σ, ?_, φ, ?_⟩
  · -- Proof comment: the denominator supplied by `right_fac` is inverted by `Q`, hence it is a
    -- quasi-isomorphism of cochain complexes.
    rw [DerivedCategory.isIso_Q_map_iff_quasiIso] at hσ
    exact hσ
  · -- Proof comment: rewrite the strictified roof through the fixed target isomorphism `eI`.
    calc
      DerivedCategory.Q.map σ ≫ (DerivedCategory.Q.objObjPreimageIso X).hom ≫ α =
          DerivedCategory.Q.map σ ≫ β ≫ eI.hom := by
            simp [β, Category.assoc]
      _ =
          DerivedCategory.Q.map σ ≫
            (inv (DerivedCategory.Q.map σ) ≫ DerivedCategory.Q.map φ) ≫ eI.hom := by
              rw [hβ]
      _ = DerivedCategory.Q.map φ ≫ eI.hom := by
            simp [Category.assoc]

/-- Helper for Lemma 19.13.12: each cocone leg `system.obj (op i) ⟶ c.pt` admits a strict roof
landing in one fixed K-injective representative of `c.pt`. -/
private lemma existsStageRoofToFixedKInjective
    (system : ℤᵒᵖ ⥤ DerivedCategory A) (c : Cocone system)
    (I : CochainComplex A ℤ) [I.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ c.pt) (i : ℤ) :
    ∃ (G : CochainComplex A ℤ) (σ : G ⟶ DerivedCategory.Q.objPreimage (system.obj (op i)))
      (_ : QuasiIso σ) (φ : G ⟶ I),
      DerivedCategory.Q.map σ ≫
          (DerivedCategory.Q.objObjPreimageIso (system.obj (op i))).hom ≫ c.ι.app (op i) =
        DerivedCategory.Q.map φ ≫ eI.hom := by
  -- Proof comment: this is the fixed-target strictification lemma applied to the `i`-th cocone
  -- morphism.
  simpa using
    existsComplexMapToFixedKInjective (A := A) I (E := c.pt)
      (X := system.obj (op i)) eI (c.ι.app (op i))

/-- Helper for Lemma 19.13.12: the cocone point admits a fixed K-injective representative. -/
private lemma existsKInjectiveModelOfCoconePoint
    (system : ℤᵒᵖ ⥤ DerivedCategory A) (c : Cocone system) :
    ∃ (I : CochainComplex A ℤ) (_ : I.IsKInjective),
      Nonempty (DerivedCategory.Q.obj I ≅ c.pt) := by
  -- Route correction: use the earlier Chapter 19 owner theorem that gives a functorial
  -- K-injective replacement of every complex, then specialize it to the chosen `Q.objPreimage`
  -- representative of the cocone point.
  obtain ⟨J, -, hKinj⟩ := CochainComplex.exists_functorial_kInjective_resolution A
  let I : CochainComplex A ℤ := J.toFunctor.obj (DerivedCategory.Q.objPreimage c.pt)
  let f : DerivedCategory.Q.objPreimage c.pt ⟶ I := J.ι.app (DerivedCategory.Q.objPreimage c.pt)
  have hI : I.IsKInjective := by
    simpa [I] using hKinj (DerivedCategory.Q.objPreimage c.pt)
  have hf : QuasiIso f := by
    simpa [f] using J.quasiIso_app (DerivedCategory.Q.objPreimage c.pt)
  have hQf : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A f).2 hf
  let eI : DerivedCategory.Q.obj I ≅ c.pt :=
    (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso c.pt
  exact ⟨I, hI, ⟨eI⟩⟩

-- Proof sketch: choose a K-injective complex representing `c.pt`, realize the inverse system by a
-- compatible tower of complexes mapping to that representative, and then build a filtered
-- cochain complex whose `i`-th stage is the chosen complex for `E^i`. The compatibility of the
-- tower maps with the cocone legs into `c.pt` gives the stated stagewise identifications in the derived
-- category.
/-- Lemma 19.13.12: for a compatible inverse system
`... ⟶ E^{i + 1} ⟶ E^i ⟶ E^{i - 1} ⟶ ... ⟶ E` in the derived category of a Grothendieck abelian
category, encoded by a cocone `c : Cocone system`, there exists a filtered complex whose
underlying complex represents `c.pt` and whose
filtration stages `F^i K^•` represent the objects `E^i` compatibly with the given cocone legs. -/
theorem exists_filteredCochainComplexRealization_of_inverseSystem
    (system : ℤᵒᵖ ⥤ DerivedCategory A) (c : Cocone system) :
    ∃ K : FilteredComplex A, K.RealizesInverseSystem c := by
  obtain ⟨I, hI, heI⟩ := existsKInjectiveModelOfCoconePoint (A := A) system c
  letI : I.IsKInjective := hI
  let eI : DerivedCategory.Q.obj I ≅ c.pt := Classical.choice heI
  have hstage :
      ∀ i : ℤ,
        ∃ (G : CochainComplex A ℤ)
          (σ : G ⟶ DerivedCategory.Q.objPreimage (system.obj (op i)))
          (_ : QuasiIso σ) (φ : G ⟶ I),
          DerivedCategory.Q.map σ ≫
              (DerivedCategory.Q.objObjPreimageIso (system.obj (op i))).hom ≫
                c.ι.app (op i) =
            DerivedCategory.Q.map φ ≫ eI.hom := by
    intro i
    -- Proof comment: once the fixed target `I` exists, each cocone leg strictifies to an actual
    -- roof landing in `I`.
    exact existsStageRoofToFixedKInjective (A := A) system c I eI i
  -- Proof comment: the fixed K-injective target is now available by the new helper, so the
  -- verified prefix of the source proof is the stagewise strict roof family `hstage` into `I`.
  -- TODO: strictify the negative
  -- transition maps on the nose, add the canonical acyclic envelopes, and package the resulting
  -- image filtration inside one ambient complex representing `c.pt` via `eI`.
  sorry

end

end CategoryTheory
