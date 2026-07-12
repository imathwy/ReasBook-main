import StacksProject_2024.Chap12.Lemma_12_19_12
import StacksProject_2024.Chap12.Definition_12_16_1
import StacksProject_2024.Chap12.Definition_12_24_5
import StacksProject_2024.Chap13.Definition_13_9_4
import StacksProject_2024.Chap15.Definition_15_59_1

noncomputable section

universe u

namespace CategoryTheory
namespace FilteredCochainComplex

open FilteredComplex
open FilteredObject
open CategoryTheory.Limits
open scoped ZeroObject

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/- Domain-style sampling for Lemma `15.64.2`.
- primary domain: filtered cochain complexes of `R`-modules, their underlying, stage, and
  graded-piece cochain complexes, and filtered free K-flat resolutions;
- sampled owner/canonical declarations in this domain:
  `FilteredComplex (ModuleCat R)`,
  `FilteredComplex.underlying`,
  `FilteredComplex.stage`,
  `FilteredComplex.gradedPiece`,
  `FilteredComplex.underlyingMap`,
  `FilteredComplex.stageMap`,
  `FilteredComplex.gradedPieceMap`,
  `CochainComplex.IsTermwiseFree`,
  `CochainComplex.IsKFlat`;
- best owner abstraction:
  `source-facing`: `FilteredCochainComplex (ModuleCat R)` together with the Chapter `12`
    stage notation `F^{p} K` and graded-piece notation `gr^{p} K`;
  `core/canonical`: `FilteredComplex (ModuleCat R)` with `underlying`, `F^{p}(-)`, `gr^{p}(-)`,
    `underlyingMap`, `stageMap`, `gradedPieceMap`, and the Chapter `15` owner
    `CochainComplex.IsKFlat` on the resulting cochain complexes;
- primitive data: a filtered cochain complex `P`, a filtered cochain complex `K`, and a morphism
  `φ : P ⟶ K`, plus the termwise-freeness clauses on `P.underlying`, `F^{p} P`, and `gr^{p} P`;
- derived API: the owner-level K-flatness clauses on `P.underlying`, `F^{p} P`, and `gr^{p} P`,
  together with the comparison maps induced by `φ`.
- source/core/bridge triage:
  `source-facing`: `exists_filteredFreeResolution`;
  `core/canonical`: the Chapter `12` owner `FilteredComplex (ModuleCat R)`, together with
    `underlying`, `F^{p}(-)`, `gr^{p}(-)`, `underlyingMap`, `stageMap`, `gradedPieceMap`, and
    the Chapter `15` owner `CochainComplex.IsKFlat`;
  `bridge/view`: the induced comparison morphisms `underlyingMap`, `stageMap`, and
    `gradedPieceMap` attached to `φ`.

This file therefore keeps the source-facing filtered-resolution statement on
`FilteredCochainComplex (ModuleCat R)` and reuses the Chapter `12` and Chapter `15` owners
directly for the induced filtered-complex maps and the K-flatness content, without introducing a
parallel local wrapper for filtered K-flat data.
-/

section

variable {R : Type u} [CommRing R]

/-- Helper for Lemma 15.64.2: each filtration index is bounded by its successor. -/
lemma int_le_add_one (p : ℤ) : p ≤ p + 1 := by
  omega

/-- Helper for Lemma 15.64.2: a zero `R`-module is free. -/
lemma moduleCat_free_of_isZero (M : ModuleCat R) (hM : IsZero M) :
    Module.Free R (M : Type u) := by
  let _ : Subsingleton (M : Type u) := (ModuleCat.isZero_iff_subsingleton).1 hM
  exact Module.Free.of_subsingleton (R := R) (N := (M : Type u))

/-- Helper for Lemma 15.64.2: a morphism out of a zero `R`-module is automatically split
monic. -/
lemma moduleCat_isSplitMono_of_isZero_source {X Y : ModuleCat R} (f : X ⟶ Y) (hX : IsZero X) :
    IsSplitMono f := by
  -- Proof comment: the zero retraction already witnesses the split-mono structure because the
  -- identity of a zero source object vanishes.
  refine IsSplitMono.mk' ⟨0, ?_⟩
  have hid : 𝟙 X = 0 := (IsZero.iff_id_eq_zero X).1 hX
  simpa [hid]

/-- Helper for Lemma 15.64.2: the filtered-object property used by the source route records the
split successor-stage maps and freeness of the underlying object, of every stage, and of every
graded piece. -/
def split_free_filtered_object :
    CategoryTheory.ObjectProperty (FilteredObject (ModuleCat R)) :=
  -- Route correction: the source proof uses basic filtered modules with a free unfiltered summand,
  -- so this owner property must not impose exhaustivity.
  fun A ↦
    (∀ p : ℤ,
      IsSplitMono
        (((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app A))) ∧
    Module.Free R ((A.obj : ModuleCat R) : Type u) ∧
    (∀ p : ℤ, Module.Free R ((FilteredObject.stage (C := ModuleCat R) A p : ModuleCat R) : Type u)) ∧
    (∀ p : ℤ,
      Module.Free R ((FilteredObject.gradedPiece (C := ModuleCat R) A p : ModuleCat R) : Type u))

/-- Helper for Lemma 15.64.2: the zero filtered `R`-module already satisfies the split-free
object property. -/
lemma split_free_filtered_object_zero :
    split_free_filtered_object (R := R) (0 : FilteredObject (ModuleCat R)) := by
  let hZeroFiltered : IsZero (0 : FilteredObject (ModuleCat R)) :=
    Limits.isZero_zero (FilteredObject (ModuleCat R))
  let hZeroUnderlying :
      IsZero (((FilteredObject.forget : FilteredObject (ModuleCat R) ⥤ ModuleCat R).obj
        (0 : FilteredObject (ModuleCat R)))) :=
    (FilteredObject.forget : FilteredObject (ModuleCat R) ⥤ ModuleCat R).map_isZero hZeroFiltered
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: each successor-stage map has zero source, hence splits via the zero
    -- retraction.
    intro p
    let hZeroStage :
        IsZero (FilteredObject.stage (C := ModuleCat R) (0 : FilteredObject (ModuleCat R)) (p + 1)) :=
      (FilteredObject.stageFunctor (C := ModuleCat R) (p + 1)).map_isZero hZeroFiltered
    exact
      moduleCat_isSplitMono_of_isZero_source (R := R)
        (((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app
          (0 : FilteredObject (ModuleCat R)))) hZeroStage
  · -- Proof comment: the underlying module of the zero filtered object is zero.
    exact
      moduleCat_free_of_isZero (R := R)
        (M := ((0 : FilteredObject (ModuleCat R)).obj : ModuleCat R)) hZeroUnderlying
  · -- Proof comment: every stage of the zero filtered object is again zero.
    intro p
    let hZeroStage :
        IsZero (FilteredObject.stage (C := ModuleCat R) (0 : FilteredObject (ModuleCat R)) p) :=
      (FilteredObject.stageFunctor (C := ModuleCat R) p).map_isZero hZeroFiltered
    exact
      moduleCat_free_of_isZero (R := R)
        (M := FilteredObject.stage (C := ModuleCat R) (0 : FilteredObject (ModuleCat R)) p)
        hZeroStage
  · -- Proof comment: every graded piece of the zero filtered object is again zero.
    intro p
    let G :
        FilteredObject (ModuleCat R) ⥤ ModuleCat R :=
      (FilteredObject.associatedGradedFunctor (C := ModuleCat R)) ⋙ GradedObject.eval p
    let hZeroGraded :
        IsZero
          (FilteredObject.gradedPiece (C := ModuleCat R) (0 : FilteredObject (ModuleCat R)) p) :=
      G.map_isZero hZeroFiltered
    exact
      moduleCat_free_of_isZero (R := R)
        (M := FilteredObject.gradedPiece (C := ModuleCat R) (0 : FilteredObject (ModuleCat R)) p)
        hZeroGraded

/-- Helper for Lemma 15.64.2: the split-free filtered-object property contains the zero object. -/
local instance split_free_filtered_object_containsZero :
    CategoryTheory.ObjectProperty.ContainsZero (split_free_filtered_object (R := R)) where
  exists_zero := ⟨0, Limits.isZero_zero _, split_free_filtered_object_zero (R := R)⟩

/-- Helper for Lemma 15.64.2: the split successor-stage condition transports across filtered
isomorphisms. -/
lemma split_successor_stageMap_of_iso
    {A B : FilteredObject (ModuleCat R)} (e : A ≅ B) (p : ℤ)
    (hA :
      IsSplitMono
        (((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app A))) :
    IsSplitMono
      (((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app B)) := by
  let fA :
      FilteredObject.stage (C := ModuleCat R) A (p + 1) ⟶
        FilteredObject.stage (C := ModuleCat R) A p :=
    ((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app A)
  let fB :
      FilteredObject.stage (C := ModuleCat R) B (p + 1) ⟶
        FilteredObject.stage (C := ModuleCat R) B p :=
    ((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app B)
  let eSucc :
      FilteredObject.stage (C := ModuleCat R) A (p + 1) ≅
        FilteredObject.stage (C := ModuleCat R) B (p + 1) :=
    (FilteredObject.stageFunctor (C := ModuleCat R) (p + 1)).mapIso e
  let eStage :
      FilteredObject.stage (C := ModuleCat R) A p ≅
        FilteredObject.stage (C := ModuleCat R) B p :=
    (FilteredObject.stageFunctor (C := ModuleCat R) p).mapIso e
  letI : IsSplitMono fA := hA
  let rA :
      FilteredObject.stage (C := ModuleCat R) A p ⟶
        FilteredObject.stage (C := ModuleCat R) A (p + 1) :=
    @retraction (ModuleCat R) _ _ _ fA ‹IsSplitMono fA›
  have hNatHom :
      ((FilteredObject.stageFunctor (C := ModuleCat R) (p + 1)).map e.hom) ≫ fB =
        fA ≫ ((FilteredObject.stageFunctor (C := ModuleCat R) p).map e.hom) :=
    (FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).naturality e.hom
  have hNatHom' : eSucc.hom ≫ fB = fA ≫ eStage.hom := by
    -- Proof comment: the successor-stage comparison is a natural transformation in the filtered
    -- object, so the forward isomorphism intertwines the two stage maps.
    simpa [eSucc, eStage, fA, fB] using hNatHom
  have hNatInv :
      ((FilteredObject.stageFunctor (C := ModuleCat R) (p + 1)).map e.inv) ≫ fA =
        fB ≫ ((FilteredObject.stageFunctor (C := ModuleCat R) p).map e.inv) :=
    (FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).naturality e.inv
  have hNatInv' : eSucc.inv ≫ fA = fB ≫ eStage.inv := by
    -- Proof comment: the same naturality square for `e.inv` gives the transport formula needed
    -- to move the chosen retraction from `A` to `B`.
    simpa [eSucc, eStage, fA, fB] using hNatInv
  refine IsSplitMono.mk' ⟨eStage.inv ≫ rA ≫ eSucc.hom, ?_⟩
  -- Proof comment: conjugate the chosen retraction of `fA` by the stage isomorphisms.
  calc
    fB ≫ (eStage.inv ≫ rA ≫ eSucc.hom)
        = (fB ≫ eStage.inv) ≫ rA ≫ eSucc.hom := by simp [Category.assoc]
    _ = (eSucc.inv ≫ fA) ≫ rA ≫ eSucc.hom := by rw [← hNatInv']
    _ = eSucc.inv ≫ (fA ≫ rA) ≫ eSucc.hom := by simp [Category.assoc]
    _ = eSucc.inv ≫ eSucc.hom := by simp [rA]
    _ = 𝟙 _ := by simpa using eSucc.inv_hom_id

/-- Helper for Lemma 15.64.2: the split-free filtered-object property is stable under filtered
isomorphisms. -/
local instance split_free_filtered_object_isClosedUnderIsomorphisms :
    CategoryTheory.ObjectProperty.IsClosedUnderIsomorphisms
      (split_free_filtered_object (R := R)) where
  of_iso {A B} e hA := by
    rcases hA with ⟨hSplit, hUnderlying, hStage, hGraded⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- Proof comment: transport each chosen successor-stage splitting through the stage
      -- isomorphisms induced by `e`.
      intro p
      exact split_successor_stageMap_of_iso (R := R) e p (hSplit p)
    · -- Proof comment: the forgetful functor sends `e` to an isomorphism of `R`-modules, and
      -- freeness is invariant under module isomorphism.
      let U : FilteredObject (ModuleCat R) ⥤ ModuleCat R := FilteredObject.forget
      let _ :
          Module.Free R (((U.obj A : ModuleCat R) : Type u)) := by
        simpa [U] using hUnderlying
      exact Module.Free.of_equiv
        ((U.mapIso e).toLinearEquiv)
    · -- Proof comment: the same transport works stagewise after applying `stageFunctor p`.
      intro p
      let Fp : FilteredObject (ModuleCat R) ⥤ ModuleCat R :=
        FilteredObject.stageFunctor (C := ModuleCat R) p
      let _ :
          Module.Free R (((Fp.obj A : ModuleCat R) : Type u)) := by
        simpa [Fp] using hStage p
      exact Module.Free.of_equiv
        ((Fp.mapIso e).toLinearEquiv)
    · -- Proof comment: graded pieces are functorial in filtered isomorphisms, so freeness moves
      -- across the induced isomorphism on `gr^p`.
      intro p
      let G : FilteredObject (ModuleCat R) ⥤ ModuleCat R :=
        (FilteredObject.associatedGradedFunctor (C := ModuleCat R)) ⋙ GradedObject.eval p
      let _ :
          Module.Free R (((G.obj A : ModuleCat R) : Type u)) := by
        simpa [G] using hGraded p
      exact Module.Free.of_equiv
        ((G.mapIso e).toLinearEquiv)

/-- Helper for Lemma 15.64.2: the rank-one single complex on `R` is termwise free. -/
lemma ring_single_termwise_free (n : ℤ) :
    ((CochainComplex.singleFunctor (ModuleCat R) n).obj
      ((ModuleCat.of R R) : ModuleCat R)).IsTermwiseFree := by
  intro i
  by_cases h : i = n
  · -- In the supported degree, the term is canonically `R` itself.
    subst i
    let e :
        (((CochainComplex.singleFunctor (ModuleCat R) n).obj
            ((ModuleCat.of R R) : ModuleCat R)).X n : ModuleCat R) ≅
          ((ModuleCat.of R R) : ModuleCat R) :=
      HomologicalComplex.singleObjXSelf
        (ComplexShape.up ℤ) n ((ModuleCat.of R R) : ModuleCat R)
    exact Module.Free.of_equiv e.toLinearEquiv.symm
  · -- Away from the supported degree, the term is zero and hence free.
    have hzero :
        Limits.IsZero
          ((((CochainComplex.singleFunctor (ModuleCat R) n).obj
              ((ModuleCat.of R R) : ModuleCat R)).X i : ModuleCat R)) :=
      HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) n ((ModuleCat.of R R) : ModuleCat R) i
        (by simpa [eq_comm] using h)
    let _ :
        Subsingleton
          (((((CochainComplex.singleFunctor (ModuleCat R) n).obj
              ((ModuleCat.of R R) : ModuleCat R)).X i : ModuleCat R) : Type u)) :=
      (ModuleCat.isZero_iff_subsingleton).1 hzero
    exact
      Module.Free.of_subsingleton
        (R := R)
        (N := ((((CochainComplex.singleFunctor (ModuleCat R) n).obj
            ((ModuleCat.of R R) : ModuleCat R)).X i : ModuleCat R) : Type u))

/-- Helper for Lemma 15.64.2: the rank-one single complex on `R` is termwise flat. -/
lemma ring_single_termwise_flat (n : ℤ) :
    ((CochainComplex.singleFunctor (ModuleCat R) n).obj
      ((ModuleCat.of R R) : ModuleCat R)).IsTermwiseFlat := by
  -- Termwise freeness of the single complex upgrades immediately to termwise flatness.
  let hfree := ring_single_termwise_free (R := R) n
  intro i
  let _ :
      Module.Free R
        (((((CochainComplex.singleFunctor (ModuleCat R) n).obj
            ((ModuleCat.of R R) : ModuleCat R)).X i : ModuleCat R) : Type u)) :=
    hfree i
  exact Module.Flat.of_free

/-- Helper for Lemma 15.64.2: a binary biproduct of free `R`-modules is free. -/
lemma moduleCat_free_biprod {A B : ModuleCat R}
    (hA : Module.Free R (A : Type u))
    (hB : Module.Free R (B : Type u)) :
    Module.Free R ((A ⊞ B : ModuleCat R) : Type u) := by
  -- Proof comment: identify the biproduct with the product module and use the standard free basis
  -- on a binary product of free modules.
  let _ : Module.Free R (A : Type u) := hA
  let _ : Module.Free R (B : Type u) := hB
  let _ : Module.Free R (ModuleCat.of R (A × B)) := inferInstance
  exact Module.Free.of_equiv (ModuleCat.biprodIsoProd A B).symm.toLinearEquiv

/-- Helper for Lemma 15.64.2: a binary biproduct of split monomorphisms in `ModuleCat R` is again
split monic. -/
lemma moduleCat_isSplitMono_biprod_map
    {A B C D : ModuleCat R} (f : A ⟶ B) (g : C ⟶ D)
    [IsSplitMono f] [IsSplitMono g] :
    IsSplitMono (biprod.map f g) := by
  let rf : B ⟶ A := @retraction _ _ _ _ f ‹IsSplitMono f›
  let rg : D ⟶ C := @retraction _ _ _ _ g ‹IsSplitMono g›
  refine IsSplitMono.mk' ⟨biprod.map rf rg, ?_⟩
  -- Proof comment: the product of the chosen retractions is a retraction of the biproduct map.
  apply biprod.hom_ext
  · simp [rf]
  · simp [rg]

/-- Helper for Lemma 15.64.2: forgetting the filtration is additive on filtered `R`-modules. -/
local instance filteredObject_forget_additive :
    (FilteredObject.forget : FilteredObject (ModuleCat R) ⥤ ModuleCat R).Additive where
  map_add := by
    intro A B f g
    rfl

/-- Helper for Lemma 15.64.2: taking a fixed filtration stage is additive on filtered
`R`-modules. -/
local instance filteredObject_stageFunctor_additive (p : ℤ) :
    ((FilteredObject.stageFunctor (C := ModuleCat R) p) :
      FilteredObject (ModuleCat R) ⥤ ModuleCat R).Additive where
  map_add := by
    intro A B f g
    -- Proof comment: compare both stage maps after postcomposing with the mono stage inclusion.
    apply (cancel_mono (B.filtration.obj p).arrow).1
    calc
      (FilteredObject.Hom.stageMap (f + g) p) ≫ (B.filtration.obj p).arrow
          = (A.filtration.obj p).arrow ≫ (f + g).hom := by
              rw [FilteredObject.Hom.stageMap_comm]
      _ = (A.filtration.obj p).arrow ≫ f.hom + (A.filtration.obj p).arrow ≫ g.hom := by
            simp
      _ = (FilteredObject.Hom.stageMap f p + FilteredObject.Hom.stageMap g p) ≫
            (B.filtration.obj p).arrow := by
            rw [Preadditive.add_comp, FilteredObject.Hom.stageMap_comm,
              FilteredObject.Hom.stageMap_comm]

/-- Helper for Lemma 15.64.2: an additive functor sends a chosen binary biproduct to the
canonical binary biproduct of the images. -/
def additive_functor_biprod_hom
    {C : Type u} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type u} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (A B : C) :
    F.obj (A ⊞ B) ⟶ F.obj A ⊞ F.obj B :=
  biprod.lift (F.map (biprod.fst : A ⊞ B ⟶ A)) (F.map (biprod.snd : A ⊞ B ⟶ B))

/-- Helper for Lemma 15.64.2: the inverse comparison from the binary biproduct of the images to
the image of the chosen binary biproduct is the additive image of the biproduct inclusions. -/
def additive_functor_biprod_inv
    {C : Type u} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type u} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (A B : C) :
    F.obj A ⊞ F.obj B ⟶ F.obj (A ⊞ B) :=
  biprod.desc (F.map (biprod.inl : A ⟶ A ⊞ B)) (F.map (biprod.inr : B ⟶ A ⊞ B))

/-- Helper for Lemma 15.64.2: the additive biproduct comparison and its inverse compose to the
identity on the image of the chosen binary biproduct. -/
lemma additive_functor_biprod_hom_inv_id
    {C : Type u} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type u} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (A B : C) :
    additive_functor_biprod_hom F A B ≫ additive_functor_biprod_inv F A B =
      𝟙 (F.obj (A ⊞ B)) := by
  -- Proof comment: expand the comparison morphisms and use the standard biproduct total relation
  -- after mapping it through the additive functor.
  calc
    additive_functor_biprod_hom F A B ≫ additive_functor_biprod_inv F A B
        = F.map (biprod.fst : A ⊞ B ⟶ A) ≫ F.map (biprod.inl : A ⟶ A ⊞ B) +
            F.map (biprod.snd : A ⊞ B ⟶ B) ≫ F.map (biprod.inr : B ⟶ A ⊞ B) := by
              simp [additive_functor_biprod_hom, additive_functor_biprod_inv]
    _ = F.map ((biprod.fst : A ⊞ B ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ B)) +
          F.map ((biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inr : B ⟶ A ⊞ B)) := by
          rw [← F.map_comp, ← F.map_comp]
    _ = F.map ((biprod.fst : A ⊞ B ⟶ A) ≫ (biprod.inl : A ⟶ A ⊞ B) +
          (biprod.snd : A ⊞ B ⟶ B) ≫ (biprod.inr : B ⟶ A ⊞ B)) := by
          rw [← F.map_add]
    _ = F.map (𝟙 (A ⊞ B)) := by simp
    _ = 𝟙 (F.obj (A ⊞ B)) := by simp

/-- Helper for Lemma 15.64.2: the inverse additive biproduct comparison followed by the forward
comparison is the identity on the canonical binary biproduct of the images. -/
lemma additive_functor_biprod_inv_hom_id
    {C : Type u} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type u} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (A B : C) :
    additive_functor_biprod_inv F A B ≫ additive_functor_biprod_hom F A B =
      𝟙 (F.obj A ⊞ F.obj B) := by
  -- Proof comment: compare both composites on the two biproduct generators and reduce each
  -- branch to functoriality of the four biproduct identities.
  apply biprod.hom_ext'
  · apply biprod.hom_ext
    · simpa [Category.assoc, additive_functor_biprod_hom, additive_functor_biprod_inv] using
        calc
          ((biprod.inl : F.obj A ⟶ F.obj A ⊞ F.obj B) ≫
              additive_functor_biprod_inv F A B ≫
              additive_functor_biprod_hom F A B) ≫ biprod.fst
              = F.map ((biprod.inl : A ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A)) := by
                  simp [Category.assoc, additive_functor_biprod_hom,
                    additive_functor_biprod_inv, ← F.map_comp]
          _ = 𝟙 (F.obj A) := by simp
    · simpa [Category.assoc, additive_functor_biprod_hom, additive_functor_biprod_inv] using
        calc
          ((biprod.inl : F.obj A ⟶ F.obj A ⊞ F.obj B) ≫
              additive_functor_biprod_inv F A B ≫
              additive_functor_biprod_hom F A B) ≫ biprod.snd
              = F.map ((biprod.inl : A ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)) := by
                  simp [Category.assoc, additive_functor_biprod_hom,
                    additive_functor_biprod_inv, ← F.map_comp]
          _ = 0 := by simp
  · apply biprod.hom_ext
    · simpa [Category.assoc, additive_functor_biprod_hom, additive_functor_biprod_inv] using
        calc
          ((biprod.inr : F.obj B ⟶ F.obj A ⊞ F.obj B) ≫
              additive_functor_biprod_inv F A B ≫
              additive_functor_biprod_hom F A B) ≫ biprod.fst
              = F.map ((biprod.inr : B ⟶ A ⊞ B) ≫ (biprod.fst : A ⊞ B ⟶ A)) := by
                  simp [Category.assoc, additive_functor_biprod_hom,
                    additive_functor_biprod_inv, ← F.map_comp]
          _ = 0 := by simp
    · simpa [Category.assoc, additive_functor_biprod_hom, additive_functor_biprod_inv] using
        calc
          ((biprod.inr : F.obj B ⟶ F.obj A ⊞ F.obj B) ≫
              additive_functor_biprod_inv F A B ≫
              additive_functor_biprod_hom F A B) ≫ biprod.snd
              = F.map ((biprod.inr : B ⟶ A ⊞ B) ≫ (biprod.snd : A ⊞ B ⟶ B)) := by
                  simp [Category.assoc, additive_functor_biprod_hom,
                    additive_functor_biprod_inv, ← F.map_comp]
          _ = 𝟙 (F.obj B) := by simp

/-- Helper for Lemma 15.64.2: the additive comparison morphisms assemble into an isomorphism
from the image of a chosen binary biproduct to the canonical binary biproduct of the images. -/
def additive_functor_biprod_iso
    {C : Type u} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    {D : Type u} [Category D] [Preadditive D] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.Additive] (A B : C) :
    F.obj (A ⊞ B) ≅ F.obj A ⊞ F.obj B :=
  ⟨additive_functor_biprod_hom F A B, additive_functor_biprod_inv F A B,
    additive_functor_biprod_hom_inv_id F A B, additive_functor_biprod_inv_hom_id F A B⟩

/-- Helper for Lemma 15.64.2: the split-free filtered-object property is stable under binary
biproducts. -/
lemma split_free_filtered_object_binary_biproduct
    {A B : FilteredObject (ModuleCat R)}
    (hA : split_free_filtered_object (R := R) A)
    (hB : split_free_filtered_object (R := R) B) :
    split_free_filtered_object (R := R) (A ⊞ B : FilteredObject (ModuleCat R)) := by
  rcases hA with ⟨hASplit, hAUnderlying, hAStage, hAGraded⟩
  rcases hB with ⟨hBSplit, hBUnderlying, hBStage, hBGraded⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Proof comment: identify the successor-stage map on the biproduct with the biproduct of the
    -- two successor-stage maps and transport the chosen retraction across the comparison
    -- isomorphisms.
    intro p
    let Fp : FilteredObject (ModuleCat R) ⥤ ModuleCat R :=
      FilteredObject.stageFunctor (C := ModuleCat R) p
    let Fq : FilteredObject (ModuleCat R) ⥤ ModuleCat R :=
      FilteredObject.stageFunctor (C := ModuleCat R) (p + 1)
    let sA :
        FilteredObject.stage (C := ModuleCat R) A (p + 1) ⟶
          FilteredObject.stage (C := ModuleCat R) A p :=
      ((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app A)
    let sB :
        FilteredObject.stage (C := ModuleCat R) B (p + 1) ⟶
          FilteredObject.stage (C := ModuleCat R) B p :=
      ((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app B)
    let sAB :
        FilteredObject.stage (C := ModuleCat R) (A ⊞ B : FilteredObject (ModuleCat R)) (p + 1) ⟶
          FilteredObject.stage (C := ModuleCat R) (A ⊞ B : FilteredObject (ModuleCat R)) p :=
      ((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).app
        (A ⊞ B : FilteredObject (ModuleCat R)))
    let eStage :
        FilteredObject.stage (C := ModuleCat R) (A ⊞ B : FilteredObject (ModuleCat R)) p ≅
          FilteredObject.stage (C := ModuleCat R) A p ⊞
            FilteredObject.stage (C := ModuleCat R) B p :=
      additive_functor_biprod_iso Fp A B
    let eSucc :
        FilteredObject.stage (C := ModuleCat R) (A ⊞ B : FilteredObject (ModuleCat R)) (p + 1) ≅
          FilteredObject.stage (C := ModuleCat R) A (p + 1) ⊞
            FilteredObject.stage (C := ModuleCat R) B (p + 1) :=
      additive_functor_biprod_iso Fq A B
    let _ : IsSplitMono sA := hASplit p
    let _ : IsSplitMono sB := hBSplit p
    let hMap : IsSplitMono (biprod.map sA sB) :=
      moduleCat_isSplitMono_biprod_map sA sB
    let rMap :
        FilteredObject.stage (C := ModuleCat R) A p ⊞
            FilteredObject.stage (C := ModuleCat R) B p ⟶
          FilteredObject.stage (C := ModuleCat R) A (p + 1) ⊞
            FilteredObject.stage (C := ModuleCat R) B (p + 1) :=
      @retraction (ModuleCat R) _ _ _ (biprod.map sA sB) hMap
    have hLeftFst :
        sAB ≫ eStage.hom ≫ biprod.fst = sAB ≫ Fp.map (biprod.fst : A ⊞ B ⟶ A) := by
      change
        sAB ≫
            (biprod.lift (Fp.map (biprod.fst : A ⊞ B ⟶ A))
              (Fp.map (biprod.snd : A ⊞ B ⟶ B)) ≫ biprod.fst) =
          sAB ≫ Fp.map (biprod.fst : A ⊞ B ⟶ A)
      rw [biprod.lift_fst]
    have hNatFst :
        sAB ≫ Fp.map (biprod.fst : A ⊞ B ⟶ A) =
          Fq.map (biprod.fst : A ⊞ B ⟶ A) ≫ sA := by
      exact
        ((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).naturality
          (biprod.fst : A ⊞ B ⟶ A)).symm
    have hRightFst :
        Fq.map (biprod.fst : A ⊞ B ⟶ A) ≫ sA =
          eSucc.hom ≫ biprod.map sA sB ≫ biprod.fst := by
      symm
      change
        (biprod.lift (Fq.map (biprod.fst : A ⊞ B ⟶ A))
            (Fq.map (biprod.snd : A ⊞ B ⟶ B)) ≫ biprod.map sA sB) ≫ biprod.fst =
          Fq.map (biprod.fst : A ⊞ B ⟶ A) ≫ sA
      rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst]
    have hLeftSnd :
        sAB ≫ eStage.hom ≫ biprod.snd = sAB ≫ Fp.map (biprod.snd : A ⊞ B ⟶ B) := by
      change
        sAB ≫
            (biprod.lift (Fp.map (biprod.fst : A ⊞ B ⟶ A))
              (Fp.map (biprod.snd : A ⊞ B ⟶ B)) ≫ biprod.snd) =
          sAB ≫ Fp.map (biprod.snd : A ⊞ B ⟶ B)
      rw [biprod.lift_snd]
    have hNatSnd :
        sAB ≫ Fp.map (biprod.snd : A ⊞ B ⟶ B) =
          Fq.map (biprod.snd : A ⊞ B ⟶ B) ≫ sB := by
      exact
        ((FilteredObject.stageFunctorMapOfLE (C := ModuleCat R) (int_le_add_one p)).naturality
          (biprod.snd : A ⊞ B ⟶ B)).symm
    have hRightSnd :
        Fq.map (biprod.snd : A ⊞ B ⟶ B) ≫ sB =
          eSucc.hom ≫ biprod.map sA sB ≫ biprod.snd := by
      symm
      change
        (biprod.lift (Fq.map (biprod.fst : A ⊞ B ⟶ A))
            (Fq.map (biprod.snd : A ⊞ B ⟶ B)) ≫ biprod.map sA sB) ≫ biprod.snd =
          Fq.map (biprod.snd : A ⊞ B ⟶ B) ≫ sB
      rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd]
    have hCompare : sAB ≫ eStage.hom = eSucc.hom ≫ biprod.map sA sB := by
      apply biprod.hom_ext
      · exact hLeftFst.trans (hNatFst.trans hRightFst)
      · exact hLeftSnd.trans (hNatSnd.trans hRightSnd)
    refine IsSplitMono.mk' ⟨eStage.hom ≫ rMap ≫ eSucc.inv, ?_⟩
    calc
      sAB ≫ (eStage.hom ≫ rMap ≫ eSucc.inv)
          = (sAB ≫ eStage.hom) ≫ rMap ≫ eSucc.inv := by simp [Category.assoc]
      _ = (eSucc.hom ≫ biprod.map sA sB) ≫ rMap ≫ eSucc.inv := by rw [hCompare]
      _ = eSucc.hom ≫ ((biprod.map sA sB) ≫ rMap) ≫ eSucc.inv := by simp [Category.assoc]
      _ = eSucc.hom ≫ eSucc.inv := by simp [rMap]
      _ = 𝟙 _ := by simpa using eSucc.hom_inv_id
  · -- Proof comment: the underlying module of a filtered biproduct is canonically the biproduct
    -- of the underlying modules, so freeness is stable by the module-level biproduct lemma.
    let U : FilteredObject (ModuleCat R) ⥤ ModuleCat R := FilteredObject.forget
    let e :
        ((A ⊞ B : FilteredObject (ModuleCat R)).obj : ModuleCat R) ≅
          (A.obj : ModuleCat R) ⊞ (B.obj : ModuleCat R) :=
      additive_functor_biprod_iso U A B
    let _ :
        Module.Free R ((((A.obj : ModuleCat R) ⊞ (B.obj : ModuleCat R)) : ModuleCat R) : Type u) :=
      moduleCat_free_biprod (R := R) hAUnderlying hBUnderlying
    exact Module.Free.of_equiv e.symm.toLinearEquiv
  · -- Proof comment: the same additive biproduct comparison identifies every stage of the
    -- filtered biproduct with the biproduct of the two stages.
    intro p
    let Fp : FilteredObject (ModuleCat R) ⥤ ModuleCat R :=
      FilteredObject.stageFunctor (C := ModuleCat R) p
    let e :
        FilteredObject.stage (C := ModuleCat R) (A ⊞ B : FilteredObject (ModuleCat R)) p ≅
          FilteredObject.stage (C := ModuleCat R) A p ⊞
            FilteredObject.stage (C := ModuleCat R) B p :=
      additive_functor_biprod_iso Fp A B
    let _ :
        Module.Free R
          (((FilteredObject.stage (C := ModuleCat R) A p ⊞
              FilteredObject.stage (C := ModuleCat R) B p : ModuleCat R)) : Type u) :=
      moduleCat_free_biprod (R := R) (hAStage p) (hBStage p)
    exact Module.Free.of_equiv e.symm.toLinearEquiv
  · -- Proof comment: apply the same comparison to the associated graded functor followed by
    -- evaluation at degree `p`.
    intro p
    let G : FilteredObject (ModuleCat R) ⥤ ModuleCat R :=
      (FilteredObject.associatedGradedFunctor (C := ModuleCat R)) ⋙ GradedObject.eval p
    let e :
        FilteredObject.gradedPiece (C := ModuleCat R) (A ⊞ B : FilteredObject (ModuleCat R)) p ≅
          FilteredObject.gradedPiece (C := ModuleCat R) A p ⊞
            FilteredObject.gradedPiece (C := ModuleCat R) B p :=
      additive_functor_biprod_iso G A B
    let _ :
        Module.Free R
          (((FilteredObject.gradedPiece (C := ModuleCat R) A p ⊞
              FilteredObject.gradedPiece (C := ModuleCat R) B p : ModuleCat R)) : Type u) :=
      moduleCat_free_biprod (R := R) (hAGraded p) (hBGraded p)
    exact Module.Free.of_equiv e.symm.toLinearEquiv

/-- Helper for Lemma 15.64.2: the split-free filtered-object property is closed under binary
coproducts. -/
local instance split_free_filtered_object_isClosedUnderBinaryCoproducts :
    CategoryTheory.ObjectProperty.IsClosedUnderBinaryCoproducts
      (split_free_filtered_object (R := R)) := by
  refine CategoryTheory.ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro Z ⟨F, hF⟩
  let A := F.obj ⟨WalkingPair.left⟩
  let B := F.obj ⟨WalkingPair.right⟩
  have hA : split_free_filtered_object (R := R) A := by
    simpa [A] using hF ⟨WalkingPair.left⟩
  have hB : split_free_filtered_object (R := R) B := by
    simpa [B] using hF ⟨WalkingPair.right⟩
  have hBiprod :
      split_free_filtered_object (R := R) (A ⊞ B : FilteredObject (ModuleCat R)) :=
    split_free_filtered_object_binary_biproduct (R := R) hA hB
  have hCoprod :
      split_free_filtered_object (R := R) (A ⨿ B : FilteredObject (ModuleCat R)) := by
    exact
      CategoryTheory.ObjectProperty.prop_of_iso
        (P := split_free_filtered_object (R := R))
        (biprod.isoCoprod A B) hBiprod
  -- Proof comment: every walking-pair colimit is canonically the binary coproduct of the two
  -- diagram objects.
  exact
    CategoryTheory.ObjectProperty.prop_of_iso
      (P := split_free_filtered_object (R := R))
      (HasColimit.isoOfNatIso (diagramIsoPair F)).symm hCoprod

/-- Helper for Lemma 15.64.2: it suffices to construct a filtered free model of `K` whose
underlying complex, every stage, and every graded piece are already termwise free and K-flat,
while the comparison map is already a quasi-isomorphism on the underlying complex, on every stage,
and on every graded piece. -/
lemma exists_split_filtered_free_model
    (K : FilteredCochainComplex (ModuleCat R)) :
    ∃ (P : FilteredCochainComplex (ModuleCat R)) (φ : P ⟶ K),
      P.underlying.IsKFlat ∧
      (∀ p, (F^{p} P).IsKFlat) ∧
      (∀ p, (gr^{p} P).IsKFlat) ∧
      P.underlying.IsTermwiseFree ∧
      (∀ p, (F^{p} P).IsTermwiseFree) ∧
      (∀ p, (gr^{p} P).IsTermwiseFree) ∧
      QuasiIso (underlyingMap φ) ∧
      (∀ p, QuasiIso (stageMap φ p)) ∧
      (∀ p, QuasiIso (gradedPieceMap φ p)) := by
  -- Route correction: the abstract upper-truncation tower route cannot be used here.
  -- `FilteredObject (ModuleCat R)` is not abelian in this development, so
  -- `UpperTruncationResolutionTower` is not even well-typed on filtered objects. The remaining
  -- source-faithful route is the explicit induction `P₀ ⊆ P₁ ⊆ ⋯` from the textbook proof.
  -- TODO: implement the basic filtered-object constructor, then prove the three source steps:
  -- the initial cohomology-surjective basic model, the successor kernel-killing extension, and the
  -- colimit stabilization lemma for underlying and stage cohomology.
  sorry

/-- Helper for Lemma 15.64.2: once the split filtered model construction has already produced the
owner-level freeness and K-flatness witnesses, this lemma repackages them into the conjunction
used by the main theorem. -/
lemma freeness_and_kflat_of_split_filtered_model
    (P : FilteredCochainComplex (ModuleCat R))
    (hUnderlyingKFlat : P.underlying.IsKFlat)
    (hStageKFlat : ∀ p, (F^{p} P).IsKFlat)
    (hGradedKFlat : ∀ p, (gr^{p} P).IsKFlat)
    (hUnderlyingFree : P.underlying.IsTermwiseFree)
    (hStageFree : ∀ p, (F^{p} P).IsTermwiseFree)
    (hGradedFree : ∀ p, (gr^{p} P).IsTermwiseFree) :
    P.underlying.IsKFlat ∧
      (∀ p, (F^{p} P).IsKFlat) ∧
      (∀ p, (gr^{p} P).IsKFlat) ∧
      P.underlying.IsTermwiseFree ∧
      (∀ p, (F^{p} P).IsTermwiseFree) ∧
      (∀ p, (gr^{p} P).IsTermwiseFree) := by
  -- Proof comment: the retained witness already contains the six owner-level conclusions, so the
  -- helper only repackages them in the conjunction shape consumed downstream.
  exact
    ⟨hUnderlyingKFlat, hStageKFlat, hGradedKFlat,
      hUnderlyingFree, hStageFree, hGradedFree⟩

-- Proof sketch: construct `P^•` by the stepwise free filtered resolution described in the text,
-- starting from a basic filtered complex surjective on the cohomology of `K^•` and all
-- `F^p K^•`, then iteratively kill the remaining cohomology kernels. The resulting filtered
-- complex is termwise free on the underlying complex, on every stage, and on every graded piece;
-- these source-level freeness
-- properties supply the K-flatness content of the underlying complex, every stage, and every
-- graded piece, and the construction makes the underlying, stagewise, and graded-piece
-- comparison maps quasi-isomorphisms.
/-- Lemma `15.64.2` / Stacks `15.64.2`: every filtered complex of `R`-modules admits a morphism
from a filtered complex whose underlying complex, every filtration stage, and every graded piece
are K-flat, which is termwise free on the underlying complex, every filtration stage, and every
graded piece `gr^p(P^•)`,
and which is a quasi-isomorphism on the underlying complex as well as on every filtration stage
and graded piece. -/
lemma exists_filteredFreeResolution
    (K : FilteredCochainComplex (ModuleCat R)) :
    ∃ (P : FilteredCochainComplex (ModuleCat R)) (φ : P ⟶ K),
      P.underlying.IsKFlat ∧
      (∀ p, (F^{p} P).IsKFlat) ∧
      (∀ p, (gr^{p} P).IsKFlat) ∧
      P.underlying.IsTermwiseFree ∧
      (∀ p, (F^{p} P).IsTermwiseFree) ∧
      (∀ p, (gr^{p} P).IsTermwiseFree) ∧
      QuasiIso (underlyingMap φ) ∧
      (∀ p, QuasiIso (stageMap φ p)) ∧
      (∀ p, QuasiIso (gradedPieceMap φ p)) := by
  -- First isolate the source-faithful filtered free model together with the owner-level
  -- freeness/K-flatness data.
  obtain ⟨P, φ, hUnderlyingKFlat, hStageKFlat, hGradedKFlat,
      hUnderlyingFree, hStageFree, hGradedFree, hunderlying, hstage, hgradedMap⟩ :=
    exists_split_filtered_free_model K
  exact
    ⟨P, φ, hUnderlyingKFlat, hStageKFlat, hGradedKFlat,
      hUnderlyingFree, hStageFree, hGradedFree,
      hunderlying, hstage, hgradedMap⟩

end

end FilteredCochainComplex
end CategoryTheory
