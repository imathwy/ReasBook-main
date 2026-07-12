import Mathlib
import StacksProject_2024.Chap12.Definition_12_14_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open HomologicalComplex

universe v u

noncomputable section

namespace ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/- Domain-style sampling: the primary domain is homological algebra for shifts of chain homology.
Relevant owner declarations in the surrounding ecosystem are:
- `ChainComplex.cochainComplexEquivalence`,
- `CategoryTheory.PullbackShift` together with `pullbackShiftIso`,
- `Functor.CommShift.commShiftIso`,
- `CochainComplex.ShiftSequence.shiftIso`,
- `CategoryTheory.Functor.ShiftSequence.shiftIso`.

Source/core/bridge triage:
- `core/canonical`: the Chapter 12 shift owner on `ChainComplex`, built in
  `Definition_12_14_1` from `PullbackShift`, together with the cochain owner
  `CochainComplex.ShiftSequence.shiftIso`;
- `bridge/view`: this file transports that owner to chain homology.

Primitive data:
- the chain/cochain equivalence viewed in the pullback-shift owner category;
- the comparison isomorphisms from pullbacked cochain homology to chain homology.

Derived API:
- the owner shift-sequence instance on `(homologyFunctor C (down ℤ) 0)`;
- the public comparison morphism `(homologyFunctor C (down ℤ) 0).shiftIso`.
-/
private abbrev cochainShiftPullback :=
  PullbackShift (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ)

private abbrev pullbackHomologyFunctor (i : ℤ) : cochainShiftPullback C ⥤ C :=
  homologyFunctor C (up ℤ) (-i)

/-- Helper for Chap12 Definition 12 14 2: the degree-zero pullbacked cochain homology functor,
packaged separately so the induced shift-sequence transport uses the pullback-shift owner rather
than the ambient cochain one. -/
private def pullbackHomologyFunctorZero : cochainShiftPullback C ⥤ C :=
  pullbackHomologyFunctor C 0

attribute [irreducible] pullbackHomologyFunctorZero

/-- Helper for Chap12 Definition 12 14 2: the chain/cochain equivalence, typed with the
pullback-shift owner on the cochain side. -/
private def chainCochainPullbackEquivalence : ChainComplex C ℤ ≌ cochainShiftPullback C :=
  ChainComplex.cochainComplexEquivalence C

/-- Helper for Chap12 Definition 12 14 2: the inverse chain/cochain equivalence viewed with
source exactly the pullback-shift owner category. -/
private def cochainToChainPullback : cochainShiftPullback C ⥤ ChainComplex C ℤ :=
  (chainCochainPullbackEquivalence C).inverse

attribute [irreducible] cochainToChainPullback

omit [CategoryWithHomology C] in
/-- Helper for Chap12 Definition 12 14 2: rewrite the pullback-side additive transport in the
primed normal form expected by the pullback-shift API. -/
private theorem pullbackShiftFunctorAdd_hom_app
    (K : cochainShiftPullback C) (l k : ℤ) :
    (shiftFunctorAdd (cochainShiftPullback C) l k).hom.app K =
      (pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) (l + k) (-(l + k))
          (by simp)).hom.app K ≫
        (shiftFunctorAdd' (CochainComplex C ℤ) (-l) (-k) (-(l + k)) (by omega)).hom.app K ≫
        (pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) k (-k)
            (by simp)).inv.app ((shiftFunctor (cochainShiftPullback C) l).obj K) ≫
        (shiftFunctor (cochainShiftPullback C) k).map
          ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
              (by simp)).inv.app K) := by
  -- Convert the unprimed additive transport to the primed spelling once so the owner lemma
  -- can expose the two pullback comparison maps explicitly.
  simpa [shiftFunctorAdd'_eq_shiftFunctorAdd] using
    (pullbackShiftFunctorAdd'_hom_app
      (C := CochainComplex C ℤ) (φ := (negAddMonoidHom : ℤ →+ ℤ)) (X := K)
      (a₁ := l) (a₂ := k) (a₃ := l + k) (h := rfl)
      (b₁ := -l) (b₂ := -k) (b₃ := -(l + k))
      (h₁ := by simp) (h₂ := by simp) (h₃ := by simp))

/-- Helper for Chap12 Definition 12 14 2: the cochain-side comparison map followed by the
`-l` shift is the canonical `shiftMap` attached to the pullback comparison isomorphism. -/
@[reassoc]
private theorem pullbackShiftIsoShiftMapBridge
    (K : cochainShiftPullback C) (l i' i'' : ℤ) (hi'' : l + i' = i'') :
    homologyMap
        ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
            (by simp)).hom.app K)
        (-i') ≫
      (CochainComplex.ShiftSequence.shiftIso C (-l) (-i') (-i'') (by omega)).hom.app K =
    (homologyFunctor C (up ℤ) 0).shiftMap
      ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
          (by simp)).hom.app K)
      (-i') (-i'') (by omega) := by
  -- Expand `shiftMap` once so the later additive normalization can consume it canonically.
  rfl

/-- Helper for Chap12 Definition 12 14 2: any left prefix can be pushed through the pullback
shift comparison before the cochain-side shift identification, so `shiftIso_add` can rewrite the
exact associated tail it produces. -/
private theorem compPullbackShiftIsoShiftMapBridge
    (K : cochainShiftPullback C) (l i' i'' : ℤ) (hi'' : l + i' = i'') {X : C}
    (g : X ⟶ homology ((shiftFunctor (cochainShiftPullback C) l).obj K) (-i')) :
    g ≫ homologyMap
        ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
            (by simp)).hom.app K)
        (-i') ≫
      (CochainComplex.ShiftSequence.shiftIso C (-l) (-i') (-i'') (by omega)).hom.app K =
    g ≫ (homologyFunctor C (up ℤ) 0).shiftMap
        ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
            (by simp)).hom.app K)
        (-i') (-i'') (by omega) := by
  -- Reassociate once and apply the canonical bridge at the exact tail produced by `shiftIso_add`.
  simpa [Category.assoc] using
    congrArg (fun t ↦ g ≫ t) (pullbackShiftIsoShiftMapBridge (C := C) K l i' i'' hi'')

/-- Helper for Chap12 Definition 12 14 2: any left prefix can be pushed through the canonical
`shiftIso_hom_app_comp_shiftMap` comparison, so `shiftIso_add` can use the owner formula at the
exact associated tail it produces. -/
private theorem compShiftIsoHomAppCompShiftMap
    (K : cochainShiftPullback C) (k l i i' i'' : ℤ) (hi' : k + i = i') (hi'' : l + i' = i'')
    {X : C}
    (g : X ⟶ homology ((shiftFunctor (cochainShiftPullback C) k).obj
      ((shiftFunctor (cochainShiftPullback C) l).obj K)) (-i)) :
    g ≫ (CochainComplex.ShiftSequence.shiftIso C (-k) (-i) (-i') (by omega)).hom.app
          ((shiftFunctor (cochainShiftPullback C) l).obj K) ≫
        (homologyFunctor C (up ℤ) 0).shiftMap
          ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
              (by simp)).hom.app K)
          (-i') (-i'') (by omega) =
      g ≫ ((homologyFunctor C (up ℤ) 0).shift (-i)).map
            ((shiftFunctor (HomologicalComplex C (up ℤ)) (-k)).map
              ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
                  (by simp)).hom.app K)) ≫
          ((homologyFunctor C (up ℤ) 0).shift (-i)).map
            ((shiftFunctorAdd' (HomologicalComplex C (up ℤ)) (-l) (-k) (-(l + k))
                (by omega)).inv.app K) ≫
        ((homologyFunctor C (up ℤ) 0).shiftIso (-(l + k)) (-i) (-i'') (by omega)).hom.app K := by
  -- Reassociate once and apply the owner `shiftIso_hom_app_comp_shiftMap` formula at the exact
  -- tail produced by `shiftIso_add`.
  simpa [Category.assoc] using
    congrArg (fun t ↦ g ≫ t)
      (Functor.shiftIso_hom_app_comp_shiftMap
        (F := homologyFunctor C (up ℤ) 0)
        ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) l (-l)
            (by simp)).hom.app K)
        (-k) (-(l + k)) (by omega) (-i) (-i') (-i'') (by omega) (by omega))

private noncomputable instance : (pullbackHomologyFunctorZero C).ShiftSequence ℤ where
  sequence i := pullbackHomologyFunctor C i
  isoZero := by
    -- Unfold the packaged zero functor once so the zero-shift comparison is definitional.
    unfold pullbackHomologyFunctorZero
    exact Iso.refl _
  shiftIso k i i' hi' :=
    Functor.isoWhiskerRight
      (pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) k (-k) (by simp))
      (homologyFunctor C (up ℤ) (-i)) ≪≫
    (show shiftFunctor (CochainComplex C ℤ) (-k : ℤ) ⋙ homologyFunctor C (up ℤ) (-i) ≅
        pullbackHomologyFunctor C i' from
      CochainComplex.ShiftSequence.shiftIso C (-k) (-i) (-i') (by omega))
  shiftIso_zero i := by
    -- Evaluate the transported zero-shift at an object and rewrite it to the cochain formula.
    ext K
    dsimp
    have hpullback :
        homologyMap ((shiftFunctorZero (cochainShiftPullback C) ℤ).hom.app K) (-i) =
          homologyMap
            (((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
                (by simp)).hom.app K) ≫
              (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K)
            (-i) := by
      exact congrArg (fun t ↦ homologyMap t (-i))
        (pullbackShiftFunctorZero_hom_app
          (C := CochainComplex C ℤ) (φ := (negAddMonoidHom : ℤ →+ ℤ)) (X := K))
    have hpullback' :
        homologyMap ((shiftFunctorZero (cochainShiftPullback C) ℤ).hom.app K) (-i) ≫
            𝟙 (homology K (-i)) =
          homologyMap
              (((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
                  (by simp)).hom.app K) ≫
                (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K)
              (-i) ≫
            𝟙 (homology K (-i)) := by
      simpa using congrArg (fun t ↦ t ≫ 𝟙 (homology K (-i))) hpullback
    have hcochain :
        (CochainComplex.ShiftSequence.shiftIso C 0 (-i) (-i) (by omega)).hom.app K =
          homologyMap ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) (-i) := by
      change ((homologyFunctor C (up ℤ) 0).shiftIso 0 (-i) (-i) (zero_add (-i))).hom.app K =
        homologyMap ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) (-i)
      exact Functor.shiftIso_zero_hom_app (F := homologyFunctor C (up ℤ) 0) (-i) K
    calc
      homologyMap ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
              (by simp)).hom.app K) (-i) ≫
            (CochainComplex.ShiftSequence.shiftIso C 0 (-i) (-i) (by omega)).hom.app K =
          homologyMap
              (((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
                  (by simp)).hom.app K) ≫
                (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K)
              (-i) ≫
            𝟙 (homology K (-i)) := by
              rw [hcochain]
              calc
                homologyMap
                    ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
                        (by simp)).hom.app K)
                    (-i) ≫
                    homologyMap ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K) (-i) =
                  homologyMap
                    (((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
                        (by simp)).hom.app K) ≫
                      (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K)
                    (-i) := by
                      simpa using
                        (Functor.map_comp (homologyFunctor C (up ℤ) (-i))
                          ((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
                              (by simp)).hom.app K)
                          ((shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K)).symm
                _ = homologyMap
                      (((pullbackShiftIso (CochainComplex C ℤ) (negAddMonoidHom : ℤ →+ ℤ) 0 0
                          (by simp)).hom.app K) ≫
                        (shiftFunctorZero (CochainComplex C ℤ) ℤ).hom.app K)
                      (-i) ≫
                    𝟙 (homology K (-i)) := by
                      exact (Category.comp_id _).symm
      _ = homologyMap ((shiftFunctorZero (cochainShiftPullback C) ℤ).hom.app K) (-i) ≫
            𝟙 (homology K (-i)) := by
              simpa using hpullback'.symm
  shiftIso_add k l i i' i'' hi' hi'' := by
    -- TODO: the remaining blocker is an association-sensitive transport normalization.
    -- The intended route is the prefixed `shiftIso_hom_app_comp_shiftMap` comparison followed by
    -- the prefixed `pullbackShiftIsoShiftMapBridge` collapse.
    sorry

private def homologyFunctorFactorsApp (A : ChainComplex C ℤ) (i : ℤ) :
    (pullbackHomologyFunctor C i).obj ((ChainComplex.cochainComplexEquivalence C).functor.obj A) ≅
      (homologyFunctor C (down ℤ) i).obj A :=
  ((((ChainComplex.cochainComplexEquivalence C).functor.obj A).restrictionHomologyIso
      embeddingDownIntUpInt (i + 1) i (i - 1) (by simp) (by simp)
      (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
        change -(i + 1) = -i - 1
        omega)
      (show embeddingDownIntUpInt.f i = -i by simp)
      (show embeddingDownIntUpInt.f (i - 1) = -i + 1 by
        change -(i - 1) = -i + 1
        omega)
      (show (up ℤ).prev (-i) = -i - 1 by simp)
      (show (up ℤ).next (-i) = -i + 1 by simp)).symm) ≪≫
    (homologyFunctor C (down ℤ) i).mapIso
      (((ChainComplex.cochainComplexEquivalence C).unitIso.app A).symm)

/-- Helper for Chap12 Definition 12 14 2: the comparison isomorphism is the composition of the
restriction-homology inverse with the unit-inverse map on homology. -/
private theorem homologyFunctorFactorsApp_hom_explicit
    (A : ChainComplex C ℤ) (i : ℤ) :
    (homologyFunctorFactorsApp C A i).hom =
      ((((ChainComplex.cochainComplexEquivalence C).functor.obj A).restrictionHomologyIso
          embeddingDownIntUpInt (i + 1) i (i - 1) (by simp) (by simp)
          (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
            change -(i + 1) = -i - 1
            omega)
          (show embeddingDownIntUpInt.f i = -i by simp)
          (show embeddingDownIntUpInt.f (i - 1) = -i + 1 by
            change -(i - 1) = -i + 1
            omega)
          (show (up ℤ).prev (-i) = -i - 1 by simp)
          (show (up ℤ).next (-i) = -i + 1 by simp)).inv) ≫
        homologyMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i := by
  rfl

/-- Helper for Chap12 Definition 12 14 2: after restricting the pulled-back cochain complex back
to a chain complex, the opcycles map of the equivalence unit inverse is detected directly on the
ambient `pOpcycles` projection. -/
private theorem restrictionPOpcycles_comp_unitIsoInv_opcyclesMap
    (A : ChainComplex C ℤ) (i : ℤ) :
    (restriction ((chainToCochain C).obj A) embeddingDownIntUpInt).pOpcycles i ≫
        opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i =
      ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A).f i ≫ A.pOpcycles i := by
  -- Rewrite the restriction object as the source of the unit inverse and apply opcycles naturality.
  change HomologicalComplex.pOpcycles (((ChainComplex.cochainComplexEquivalence C).functor ⋙
      (ChainComplex.cochainComplexEquivalence C).inverse).obj A) i ≫
        opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i =
      ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A).f i ≫ A.pOpcycles i
  simpa using
    (HomologicalComplex.p_opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i)

/-- Helper for Chap12 Definition 12 14 2: reassociate the canonical `pOpcycles` bridge so it can
be postcomposed without redoing the transport normalization. -/
private theorem restrictionPOpcycles_comp_unitIsoInv_opcyclesMap_assoc
    (A : ChainComplex C ℤ) (i : ℤ) {Z : C}
    (g : A.opcycles i ⟶ Z) :
    (restriction ((chainToCochain C).obj A) embeddingDownIntUpInt).pOpcycles i ≫
        opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i ≫ g =
      ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A).f i ≫ A.pOpcycles i ≫ g := by
  -- Postcompose the basic `pOpcycles` bridge once so later proofs can `simp only [assoc]`.
  calc
    (restriction ((chainToCochain C).obj A) embeddingDownIntUpInt).pOpcycles i ≫
        opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i ≫ g =
      ((restriction ((chainToCochain C).obj A) embeddingDownIntUpInt).pOpcycles i ≫
          opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i) ≫ g := by
            rw [Category.assoc]
    _ = (((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A).f i ≫
          A.pOpcycles i) ≫ g := by
            rw [restrictionPOpcycles_comp_unitIsoInv_opcyclesMap (C := C) A i]
            rfl
    _ = ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A).f i ≫
          A.pOpcycles i ≫ g := by
            rw [Category.assoc]

/-- Helper for Chap12 Definition 12 14 2: postcomposing the chain/cochain equivalence unit
inverse with `homologyι` is exactly the standard `homologyι` naturality square. -/
@[reassoc]
private theorem unitIsoInv_homologyMap_comp_homologyι
    (A : ChainComplex C ℤ) (i : ℤ) :
    homologyMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i ≫
        A.homologyι i =
      (restriction ((chainToCochain C).obj A) embeddingDownIntUpInt).homologyι i ≫
        opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i := by
  -- This is the canonical `homologyι` naturality identity for the unit inverse.
  change homologyMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i ≫
        A.homologyι i =
      (((ChainComplex.cochainComplexEquivalence C).inverse.obj
          ((ChainComplex.cochainComplexEquivalence C).functor.obj A))).homologyι i ≫
        opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i
  simpa using
    (HomologicalComplex.homologyι_naturality
      ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i)

omit [CategoryWithHomology C] in
/-- Helper for Chap12 Definition 12 14 2: the degree-`i` component of the unit-inverse
naturality square identifies the cochain-side transported component with the chain-side one. -/
private theorem chainToCochainMapComponent_comp_unitIsoInv
    {A B : ChainComplex C ℤ} (f : A ⟶ B) (i : ℤ) :
    ((chainToCochain C).map f).f (-i) ≫
        ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app B).f i =
      ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A).f i ≫ f.f i := by
  -- Take the degree-`i` component of the unit-inverse naturality square and normalize it once.
  have h := congrArg (fun φ ↦ φ.f i)
    ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.naturality f)
  simpa only [Functor.comp_map, Functor.id_map, HomologicalComplex.comp_f, chainToCochain,
    HomologicalComplex.restrictionMap_f'
      (K := (chainToCochain C).obj A)
      (L := (chainToCochain C).obj B)
      (φ := (chainToCochain C).map f)
      (e := embeddingDownIntUpInt)
      (i := i) (i' := -i) (by simp)] using h

/-- Helper for Chap12 Definition 12 14 2: any prefix can be pushed through the unit-inverse
`homologyι` identity, so later naturality proofs do not need to fight association by hand. -/
@[reassoc]
private theorem comp_unitIsoInv_homologyMap_comp_homologyι
    (A : ChainComplex C ℤ) (i : ℤ) {X : C}
    (g : X ⟶ homology (((ChainComplex.cochainComplexEquivalence C).inverse.obj
      ((ChainComplex.cochainComplexEquivalence C).functor.obj A))) i) :
    g ≫ homologyMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i ≫
        A.homologyι i =
      g ≫
        ((restriction ((chainToCochain C).obj A) embeddingDownIntUpInt).homologyι i ≫
          opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app A) i) := by
  -- Postcompose the unit-inverse `homologyι` identity by an arbitrary prefix once and for all.
  simpa [Category.assoc] using
    congrArg (fun t ↦ g ≫ t)
      (unitIsoInv_homologyMap_comp_homologyι (C := C) A i)

/-- Helper for Chap12 Definition 12 14 2: any prefix can be pushed through the restriction
homology comparison before hitting `homologyι`, giving a stable opcycles-side normal form. -/
@[reassoc]
private theorem comp_restrictionHomologyIso_inv_homologyι
    (K : CochainComplex C ℤ) (i : ℤ) {X : C}
    (g : X ⟶ K.homology (-i)) :
    g ≫
        (K.restrictionHomologyIso embeddingDownIntUpInt (i + 1) i (i - 1) (by simp) (by simp)
          (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
            change -(i + 1) = -i - 1
            omega)
          (show embeddingDownIntUpInt.f i = -i by simp)
          (show embeddingDownIntUpInt.f (i - 1) = -i + 1 by
            change -(i - 1) = -i + 1
            omega)
          (show (up ℤ).prev (-i) = -i - 1 by simp)
          (show (up ℤ).next (-i) = -i + 1 by simp)).inv ≫
        (restriction K embeddingDownIntUpInt).homologyι i =
      g ≫
        (K.homologyι (-i) ≫
          (K.restrictionOpcyclesIso embeddingDownIntUpInt (i + 1) i (by simp)
            (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
              change -(i + 1) = -i - 1
              omega)
            (show embeddingDownIntUpInt.f i = -i by simp)
            (show (up ℤ).prev (-i) = -i - 1 by simp)).inv) := by
  -- Postcompose the restriction-homology `homologyι` identity by an arbitrary prefix so the
  -- remaining proof can stay in a fixed cochain-side normal form.
  simpa [Category.assoc] using
    congrArg (fun t ↦ g ≫ t)
      (restrictionHomologyIso_inv_homologyι
        (K := K) (e := embeddingDownIntUpInt) (i := i + 1) (j := i) (k := i - 1)
        (hi := by simp) (hk := by simp)
        (hi' := by
          change -(i + 1) = -i - 1
          omega)
        (hj' := by simp)
        (hk' := by
          change -(i - 1) = -i + 1
          omega)
        (hi'' := by simp) (hk'' := by simp))

/-- Helper for Chap12 Definition 12 14 2: postcomposing the standard `homologyι` naturality
square by any morphism keeps the comparison in a rewrite-friendly normal form. -/
private theorem comp_homologyι_naturality_postcompose
    {A B : ChainComplex C ℤ} (f : A ⟶ B) (i : ℤ) {Z : C}
    (g : B.opcycles i ⟶ Z) :
    homologyMap f i ≫ (B.homologyι i ≫ g) =
      A.homologyι i ≫ opcyclesMap f i ≫ g := by
  -- Postcompose the canonical `homologyι` naturality square once so later proofs can stay flat.
  simpa [Category.assoc] using
    congrArg (fun t ↦ t ≫ g) (HomologicalComplex.homologyι_naturality f i)

/-- Helper for Chap12 Definition 12 14 2: the comparison isomorphism from pullbacked cochain
homology to chain homology is natural in the chain complex. -/
private theorem homologyFunctorFactorsApp_hom_comp_homologyι_left_normal_form
    {A B : ChainComplex C ℤ} (i : ℤ) (f : A ⟶ B) :
    (pullbackHomologyFunctor C i).map ((chainToCochain C).map f) ≫
        (homologyFunctorFactorsApp C B i).hom ≫ B.homologyι i =
      ((chainToCochain C).obj A).homologyι (-i) ≫
        opcyclesMap ((chainToCochain C).map f) (-i) ≫
            (((ChainComplex.cochainComplexEquivalence C).functor.obj B).restrictionOpcyclesIso
              embeddingDownIntUpInt (i + 1) i (by simp)
              (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
                change -(i + 1) = -i - 1
                omega)
              (show embeddingDownIntUpInt.f i = -i by simp)
              (show (up ℤ).prev (-i) = -i - 1 by simp)).inv ≫
            opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app B) i := by
  -- TODO: the remaining blocker is a reassociation mismatch between the prefixed owner bridges
  -- `comp_unitIsoInv_homologyMap_comp_homologyι_assoc`,
  -- `comp_restrictionHomologyIso_inv_homologyι_assoc`, and the final
  -- `comp_homologyι_naturality_postcompose` normal form.
  sorry

/-- Helper for Chap12 Definition 12 14 2: the chain-side comparison can be rewritten to the same
cochain-side `homologyι (-i)` normal form used on the pullback side. -/
private theorem homologyFunctorFactorsApp_hom_comp_homologyι_right_normal_form
    {A B : ChainComplex C ℤ} (i : ℤ) (f : A ⟶ B) :
    (homologyFunctorFactorsApp C A i).hom ≫
        (homologyFunctor C (down ℤ) i).map f ≫ B.homologyι i =
      ((chainToCochain C).obj A).homologyι (-i) ≫
        opcyclesMap ((chainToCochain C).map f) (-i) ≫
            (((ChainComplex.cochainComplexEquivalence C).functor.obj B).restrictionOpcyclesIso
              embeddingDownIntUpInt (i + 1) i (by simp)
              (show embeddingDownIntUpInt.f (i + 1) = -i - 1 by
                change -(i + 1) = -i - 1
                omega)
              (show embeddingDownIntUpInt.f i = -i by simp)
              (show (up ℤ).prev (-i) = -i - 1 by simp)).inv ≫
            opcyclesMap ((ChainComplex.cochainComplexEquivalence C).unitIso.inv.app B) i := by
  -- TODO: the remaining blocker is the final reassociation from the chain-side normal form to the
  -- shared cochain-side `homologyι (-i)` normal form; the route goes through the same prefixed
  -- owner bridges as the left-normal-form theorem, followed by the `pOpcycles` comparison.
  sorry

/-- Helper for Chap12 Definition 12 14 2: the comparison isomorphism from pullbacked cochain
homology to chain homology is natural in the chain complex. -/
private theorem homologyFunctorFactorsApp_hom_comp_homologyι
    {A B : ChainComplex C ℤ} (i : ℤ) (f : A ⟶ B) :
    (pullbackHomologyFunctor C i).map ((chainToCochain C).map f) ≫
        (homologyFunctorFactorsApp C B i).hom ≫ B.homologyι i =
      (homologyFunctorFactorsApp C A i).hom ≫
        (homologyFunctor C (down ℤ) i).map f ≫ B.homologyι i := by
  -- Rewrite both sides to the same cochain-side normal form and close by reflexivity.
  rw [homologyFunctorFactorsApp_hom_comp_homologyι_left_normal_form]
  rw [homologyFunctorFactorsApp_hom_comp_homologyι_right_normal_form]

/-- Helper for Chap12 Definition 12 14 2: the comparison isomorphism from pullbacked cochain
homology to chain homology is natural in the chain complex. -/
private theorem homologyFunctorFactorsApp_hom_naturality
    {A B : ChainComplex C ℤ} (i : ℤ) (f : A ⟶ B) :
    (pullbackHomologyFunctor C i).map ((chainToCochain C).map f) ≫
        (homologyFunctorFactorsApp C B i).hom =
      (homologyFunctorFactorsApp C A i).hom ≫
        (homologyFunctor C (down ℤ) i).map f := by
  -- Compare both sides after postcomposing with the chain-side `homologyι`, which is monic.
  apply (cancel_mono (B.homologyι i)).1
  simpa [Category.assoc] using homologyFunctorFactorsApp_hom_comp_homologyι (C := C) i f

private def homologyFunctorFactors (i : ℤ) :
    chainToCochain C ⋙ pullbackHomologyFunctor C i ≅
      homologyFunctor C (down ℤ) i :=
  NatIso.ofComponents
    (fun A ↦ homologyFunctorFactorsApp C A i)
    (by
      intro A B f
      -- Use the dedicated naturality lemma so the comparison remains a canonical bridge.
      simpa using homologyFunctorFactorsApp_hom_naturality (C := C) i f)

/-- Helper for Chap12 Definition 12 14 2: reorient the comparison family along the inverse
chain/cochain equivalence so `Functor.ShiftSequence.induced` sees the pullback-side sequence in
the correct direction. -/
private def cochainToChainHomologyFunctorFactors (i : ℤ) :
    cochainToChainPullback C ⋙ homologyFunctor C (down ℤ) i ≅
      pullbackHomologyFunctor C i := by
  -- Normalize the pinned inverse wrapper back to the underlying equivalence inverse once.
  simpa [cochainToChainPullback, chainCochainPullbackEquivalence] using
    (Functor.isoWhiskerLeft (ChainComplex.cochainComplexEquivalence C).inverse
        (homologyFunctorFactors C i).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (ChainComplex.cochainComplexEquivalence C).counitIso _ ≪≫
      Functor.leftUnitor _)

/-- Helper for Chap12 Definition 12 14 2: the inverse-oriented comparison family lands in the
shifted sequence attached to `pullbackHomologyFunctor C 0`. -/
private def cochainToChainHomologyFunctorFactorsShift (i : ℤ) :
    cochainToChainPullback C ⋙ homologyFunctor C (down ℤ) i ≅
      (pullbackHomologyFunctorZero C).shift i := by
  -- The private pullback-side shift sequence uses `pullbackHomologyFunctor C i` as its `i`th term.
  simpa [Functor.shift, pullbackHomologyFunctorZero] using
    cochainToChainHomologyFunctorFactors (C := C) i

/-- Helper for Chap12 Definition 12 14 2: the base comparison for the induced chain-homology
shift sequence lands in the packaged zero pullback functor. -/
private def cochainToChainHomologyFunctorFactorsZero :
    cochainToChainPullback C ⋙ homologyFunctor C (down ℤ) 0 ≅ pullbackHomologyFunctorZero C := by
  -- Normalize the packaged zero functor once so the induced construction sees the intended owner.
  unfold pullbackHomologyFunctorZero
  exact cochainToChainHomologyFunctorFactors (C := C) 0

/-- Helper for Chap12 Definition 12 14 2: the chain-homology shift sequence is induced from the
pullbacked cochain-homology shift sequence along `chainToCochain`. -/
noncomputable instance :
    (homologyFunctor C (down ℤ) 0).ShiftSequence ℤ := by
  -- Proof comment: bridge the `CommShift` structure through the pinned equivalence wrappers once.
  letI : ((chainCochainPullbackEquivalence C).functor).CommShift ℤ := by
    simpa [chainCochainPullbackEquivalence] using
      (inferInstance : (chainToCochain C).CommShift ℤ)
  letI : (cochainToChainPullback C).CommShift ℤ := by
    letI : ((chainCochainPullbackEquivalence C).inverse).CommShift ℤ :=
      (chainCochainPullbackEquivalence C).commShiftInverse ℤ
    simpa [cochainToChainPullback]
  let e : (ChainComplex C ℤ ⥤ C) ≌ (cochainShiftPullback C ⥤ C) :=
    CategoryTheory.Equivalence.congrLeft (chainCochainPullbackEquivalence C)
  letI : ((Functor.whiskeringLeft (cochainShiftPullback C) (ChainComplex C ℤ) C).obj
      (cochainToChainPullback C)).Full := by
    simpa [e, cochainToChainPullback, chainCochainPullbackEquivalence] using
      (inferInstance : e.functor.Full)
  letI : ((Functor.whiskeringLeft (cochainShiftPullback C) (ChainComplex C ℤ) C).obj
      (cochainToChainPullback C)).Faithful := by
    simpa [e, cochainToChainPullback, chainCochainPullbackEquivalence] using
      (inferInstance : e.functor.Faithful)
  -- Proof comment: the chain-homology sequence is the generic induced shift sequence coming
  -- from the pullback-side comparison family.
  exact Functor.ShiftSequence.induced
    (cochainToChainHomologyFunctorFactorsZero (C := C)) ℤ
    (fun i ↦ homologyFunctor C (down ℤ) i)
    (cochainToChainHomologyFunctorFactorsShift (C := C))

end ChainComplex

variable (C : Type u) [Category.{v} C] [Preadditive C] [CategoryWithHomology C]

/- Definition 12.14.2: after transporting the cochain owner
`CochainComplex.ShiftSequence.shiftIso` through the Chapter 12 pullback-shift owner on
`ChainComplex`, the canonical functorial identification `H_{i + k}(A) ≅ H_i(A[k])` is expressed
by the generic owner morphism `(homologyFunctor C (down ℤ) 0).shiftIso`. Its source is the
degreewise equality `A_{i + k} = A[k]_i` from Definition `12.14.1`. -/
#check (homologyFunctor C (down ℤ) 0).shiftIso

variable (A : ChainComplex C ℤ) (k : ℤ)

/- Companion recall: the underlying shifted chain complex is the canonical shift object `A⟦k⟧`. -/
#check A⟦k⟧
