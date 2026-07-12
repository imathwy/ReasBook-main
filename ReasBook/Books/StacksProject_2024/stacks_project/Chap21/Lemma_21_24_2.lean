import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
import StacksProject_2024.Chap07.HasEnoughObjectsWithProperty
import StacksProject_2024.Chap15.Lemma_15_87_3
import StacksProject_2024.Chap21.RingedSiteCohomologyTowers

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open Opposite
open RingedSite.Hom

noncomputable section

universe u v

/- Domain-style sampling for Lemma 21.24.2:
- primary domain: sequential inverse systems of cochain complexes of `𝒪_X`-modules on a
  ringed site, evaluated objectwise and then passed to cohomology sheaves;
- sampled owner declarations:
  `CategoryTheory.GrothendieckTopology.HasEnoughObjectsWithProperty`,
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.SequentialInverseSystem.firstDerivedLimit`,
  `RingedSite.Hom.moduleSectionsAsAbelianFunctor`,
  `RingedSite.Hom.underlyingAbelianSheafFunctor`,
  `limit.post`;
- best owner abstraction: the tower itself is a `SequentialInverseSystem`, while the canonical
  `R¹ lim←` hypotheses are owned by `.firstDerivedLimit`, the objectwise sections
  functor is already owned by `moduleSectionsAsAbelianFunctor X U`, and the cohomology-sheaf
  comparison `H^m(lim←_n 𝓕_n^•) ⟶ lim←_n H^m(𝓕_n^•)`
  is the standard `limit.post` morphism for the composite with
  `underlyingAbelianSheafFunctor X`.

Source/core/bridge triage:
- `source-facing`: the final basiswise hypothesis theorem about the two cohomology-sheaf maps;
- `core/canonical`: `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)`,
  `SequentialInverseSystem`, `.transitionMap`, `.firstDerivedLimit`,
  `moduleSectionsAsAbelianFunctor`, `underlyingAbelianSheafFunctor`, and `limit.post`;
- `bridge/view`: the objectwise degree/cohomology towers obtained from the canonical sections
  owner over `U`.

Primitive data are just the ringed site `X`, the tower `F`, the object `U`, and the degree `m`.
The transition maps, `R¹ lim←` terms, objectwise sections functor, and limit
comparison morphism are derived API from the owner abstractions above, and the basis-cover
hypothesis is already canonically owned by `HasEnoughObjectsWithProperty`, so this file should
reuse those owners directly rather than keep parallel local copies or restate the cover condition
by hand.
-/

section

variable (X : RingedSite.{u, v})
local notation "CpxX" => CochainComplex (ModuleCat X) ℤ
local notation "CpxAb" => CochainComplex AddCommGrpCat ℤ

variable (F : SequentialInverseSystem CpxX)
variable (m : ℤ)
variable [CategoryWithHomology (ModuleCat X)]

/-- Helper for Lemma 21.24.2: a morphism of abelian sheaves on `X.siteTopology` is an
isomorphism once it is an isomorphism on all objects of a covering family supplied by
`HasEnoughObjectsWithProperty`. -/
private theorem sheaf_map_isIso_of_app_bijective
    (B : Set X)
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    {P Q : Sheaf X.siteTopology AddCommGrpCat.{max u v}}
    (φ : P ⟶ Q)
    (hφ : ∀ ⦃U : X⦄, U ∈ B → Function.Bijective (φ.1.app (op U))) :
    IsIso φ := by
  have hlocinj : Sheaf.IsLocallyInjective φ := by
    -- Injectivity is checked on a cover by basis objects and then pulled back along the cover
    -- arrows, exactly as in the standard locally bijective sheaf criterion.
    change Presheaf.IsLocallyInjective X.siteTopology φ.hom
    constructor
    intro U x y hxy
    rcases hcover U.unop with ⟨S, hS⟩
    refine X.siteTopology.superset_covering ?_ S.2
    intro Y g hg
    rw [Presheaf.equalizerSieve_apply]
    let I : S.Arrow := ⟨Y, g, hg⟩
    have hbij : Function.Bijective (φ.hom.app (op I.Y)) := hφ (hS I)
    have hxg :
        φ.hom.app (op I.Y) ((P.obj.map g.op) x) =
          (Q.obj.map g.op) (φ.hom.app U x) := by
      exact ConcreteCategory.congr_hom (φ.hom.naturality g.op) x
    have hyg :
        φ.hom.app (op I.Y) ((P.obj.map g.op) y) =
          (Q.obj.map g.op) (φ.hom.app U y) := by
      exact ConcreteCategory.congr_hom (φ.hom.naturality g.op) y
    have hmid :
        (Q.obj.map g.op) (φ.hom.app U x) =
          (Q.obj.map g.op) (φ.hom.app U y) := by
      simpa using congrArg (Q.obj.map g.op) hxy
    exact hbij.injective (hxg.trans (hmid.trans hyg.symm))
  have hlocsurj : Sheaf.IsLocallySurjective φ := by
    -- Surjectivity is checked on the same cover by lifting a section basiswise and then viewing
    -- the lift inside the image sieve.
    change Presheaf.IsLocallySurjective X.siteTopology φ.hom
    constructor
    intro U s
    rcases hcover U with ⟨S, hS⟩
    refine X.siteTopology.superset_covering ?_ S.2
    intro Y g hg
    rw [Presheaf.imageSieve_apply]
    let I : S.Arrow := ⟨Y, g, hg⟩
    have hbij : Function.Bijective (φ.hom.app (op I.Y)) := hφ (hS I)
    obtain ⟨t, ht⟩ := hbij.surjective ((Q.obj.map g.op) s)
    exact ⟨t, ht⟩
  exact (Sheaf.isLocallyBijective_iff_isIso φ).1 ⟨hlocinj, hlocsurj⟩

/-- Helper for Lemma 21.24.2: the degree arithmetic needed to shift the `m - 2` hypothesis to
degree `-2`. -/
private theorem negTwoAddEqSubTwo (m : ℤ) : -2 + m = m - 2 := by
  omega

/-- Helper for Lemma 21.24.2: the degree arithmetic needed to shift the `m - 1` hypothesis to
degree `-1`. -/
private theorem negOneAddEqSubOne (m : ℤ) : -1 + m = m - 1 := by
  omega

/-- Helper for Lemma 21.24.2: the homology shift comparison is indexed by the identity
`m + 0 = m`. -/
private theorem addZeroEqSelf (m : ℤ) : m + 0 = m := by
  omega

/-- Helper for Lemma 21.24.2: vanishing of `R¹ lim←` is preserved when postcomposition is changed
by a natural isomorphism. -/
private theorem isZeroFirstDerivedLimitOfPostcompIso
    {C : Type*} [Category C]
    (A : SequentialInverseSystem C)
    {F G : C ⥤ AddCommGrpCat}
    (e : F ≅ G)
    (h : IsZero (firstDerivedLimit (A ⋙ F))) :
    IsZero (firstDerivedLimit (A ⋙ G)) := by
  -- Transport the first-derived-limit obstruction across the induced isomorphism of towers.
  let eA : A ⋙ F ≅ A ⋙ G := Functor.isoWhiskerLeft A e
  exact h.of_iso (SequentialInverseSystem.firstDerivedLimitIsoOfNatIso eA).symm

/-- Helper for Lemma 21.24.2: shifting a cochain complex by `m` moves evaluation in degree `i`
to evaluation in degree `i + m`. -/
private noncomputable abbrev cochainShiftEvalIso
    (m i : ℤ) :
    shiftFunctor CpxAb m ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) i ≅
      HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (i + m) :=
  NatIso.ofComponents
    (fun K ↦ K.shiftFunctorObjXIso m i (i + m) rfl)
    (by
      intro K L φ
      apply (cancel_mono (L.shiftFunctorObjXIso m i (i + m) rfl).hom).1
      simpa [Category.assoc, CochainComplex.shiftFunctorObjXIso] using
        (CochainComplex.shiftFunctor_map_f' φ m i))

/-- Helper for Lemma 21.24.2: shifting by `m` transports the degree-`m - 2` vanishing hypothesis
to the degree-`-2` tower of the shifted inverse system. -/
private theorem isZeroFirstDerivedLimitShiftEvalSubTwo
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ)
    (h :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (m - 2)))) :
    IsZero (firstDerivedLimit
      ((A ⋙ shiftFunctor CpxAb m) ⋙
        HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (-2))) := by
  let ev := HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ)
  let e :
      ev (m - 2) ≅ shiftFunctor CpxAb m ⋙ ev (-2) :=
    (eqToIso (by
      congr
      omega)) ≪≫ (cochainShiftEvalIso m (-2)).symm
  -- Isolate the arithmetic once, then transport the vanishing statement through the shift.
  simpa using isZeroFirstDerivedLimitOfPostcompIso A e h

/-- Helper for Lemma 21.24.2: shifting by `m` transports the degree-`m - 1` vanishing hypothesis
to the degree-`-1` tower of the shifted inverse system. -/
private theorem isZeroFirstDerivedLimitShiftEvalSubOne
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ)
    (h :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (m - 1)))) :
    IsZero (firstDerivedLimit
      ((A ⋙ shiftFunctor CpxAb m) ⋙
        HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (-1))) := by
  let ev := HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ)
  let e :
      ev (m - 1) ≅ shiftFunctor CpxAb m ⋙ ev (-1) :=
    (eqToIso (by
      congr
      omega)) ≪≫ (cochainShiftEvalIso m (-1)).symm
  -- The same shift-evaluation transport upgrades the degree `m - 1` hypothesis.
  simpa using isZeroFirstDerivedLimitOfPostcompIso A e h

/-- Helper for Lemma 21.24.2: shifting by `m` transports the `H^(m - 1)` vanishing hypothesis to
the `H^(-1)` tower of the shifted inverse system. -/
private theorem isZeroFirstDerivedLimitShiftHomologySubOne
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ)
    (h :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (m - 1)))) :
    IsZero (firstDerivedLimit
      ((A ⋙ shiftFunctor CpxAb m) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (-1))) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ)
  let e :
      H (m - 1) ≅ shiftFunctor CpxAb m ⋙ H (-1) :=
    ((H 0).shiftIso m (-1) (m - 1) (by omega)).symm
  -- The homology shift isomorphism transports the last `R¹ lim←` hypothesis in the same way.
  simpa using isZeroFirstDerivedLimitOfPostcompIso A e h

/-- Helper for Lemma 21.24.2: package the three shifted vanishing hypotheses into the degree-`0`
Milnor input for the shifted tower. -/
private theorem shiftedTowerHasDegreeZeroMilnorHypotheses
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ)
    (hA_m_sub_two :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (m - 2))))
    (hA_m_sub_one :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (m - 1))))
    (hH_m_sub_one :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (m - 1)))) :
    IsZero (firstDerivedLimit
      ((A ⋙ shiftFunctor CpxAb m) ⋙
        HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (-2))) ∧
      IsZero (firstDerivedLimit
        ((A ⋙ shiftFunctor CpxAb m) ⋙
          HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (-1))) ∧
      IsZero (firstDerivedLimit
        ((A ⋙ shiftFunctor CpxAb m) ⋙
          HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (-1))) := by
  -- Package the three transport lemmas once so the arbitrary-degree comparison can start from
  -- the degree-`0` Milnor interface directly.
  refine ⟨?_, ?_, ?_⟩
  · simpa using isZeroFirstDerivedLimitShiftEvalSubTwo A m hA_m_sub_two
  · simpa using isZeroFirstDerivedLimitShiftEvalSubOne A m hA_m_sub_one
  · simpa using isZeroFirstDerivedLimitShiftHomologySubOne A m hH_m_sub_one

/-- Helper for Lemma 21.24.2: after shifting the source tower, the source of the degree-`0`
comparison identifies with the degree-`m` source for the original tower. -/
private noncomputable abbrev homologyShiftLimitSourceIso
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ) :
    (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 0).obj
        (limit (A ⋙ shiftFunctor CpxAb m)) ≅
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) m).obj
        (limit A) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 0).mapIso
      (preservesLimitIso (shiftFunctor CpxAb m) A).symm ≪≫
    ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 0).shiftIso
      m 0 m (addZeroEqSelf m)).app (limit A)

/-- Helper for Lemma 21.24.2: after shifting the source tower, the target limit of the
degree-`0` comparison identifies with the degree-`m` target for the original tower. -/
private noncomputable abbrev homologyShiftLimitTargetIso
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ) :
    limit (((A ⋙ shiftFunctor CpxAb m) ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 0)) ≅
      limit (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) m) :=
  HasLimit.isoOfNatIso
    ((Functor.associator A (shiftFunctor CpxAb m)
        (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 0)) ≪≫
      Functor.isoWhiskerLeft A
        ((HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 0).shiftIso
          m 0 m (addZeroEqSelf m)))

/-- Helper for Lemma 21.24.2: the degree-`0` comparison on the shifted tower is conjugate to the
degree-`m` comparison on the original tower. -/
private theorem limitPostHomologyShiftBridge
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ) :
    (homologyShiftLimitSourceIso A m).inv ≫
        limit.post (A ⋙ shiftFunctor CpxAb m)
          (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) 0) ≫
        (homologyShiftLimitTargetIso A m).hom =
      limit.post A
        (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) m) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ)
  let S := shiftFunctor CpxAb m
  let eLimit := ((H 0).shiftIso m 0 m (addZeroEqSelf m)).app (limit A)
  -- Route correction: compare both sides after projecting to each stage, so the only remaining
  -- transport is the single shift-naturality square on homology.
  apply limit.hom_ext
  intro j
  let ej := ((H 0).shiftIso m 0 m (addZeroEqSelf m)).app (A.obj j)
  have hπ :
      (preservesLimitIso S A).hom ≫ limit.π (A ⋙ S) j = S.map (limit.π A j) := by
    simpa [S] using preservesLimitIso_hom_π S A j
  have hnat :
      (H 0).map (S.map (limit.π A j)) ≫ ej.hom =
        eLimit.hom ≫ ((H 0).shift m).map (limit.π A j) := by
    change
      HomologicalComplex.homologyMap (S.map (limit.π A j)) 0 ≫ ej.hom =
        eLimit.hom ≫ ((H 0).shift m).map (limit.π A j)
    exact ((H 0).shiftIso m 0 m (addZeroEqSelf m)).hom.naturality (limit.π A j)
  have hshift :
      (homologyShiftLimitSourceIso A m).inv ≫
          (H 0).map (limit.π (A ⋙ S) j) ≫
          ej.hom =
        ((H 0).shift m).map (limit.π A j) := by
    -- Unfold the source comparison once, rewrite the shifted limit projection,
    -- and cancel the resulting shift isomorphism.
    dsimp [homologyShiftLimitSourceIso, eLimit, H, S]
    calc
      (((H 0).shiftIso m 0 m (addZeroEqSelf m)).app (limit A)).inv ≫
          (H 0).map (preservesLimitIso S A).hom ≫
          (H 0).map (limit.π (A ⋙ S) j) ≫
          ej.hom =
        eLimit.inv ≫
          (H 0).map ((preservesLimitIso S A).hom ≫ limit.π (A ⋙ S) j) ≫
          ej.hom := by
            calc
              (((H 0).shiftIso m 0 m (addZeroEqSelf m)).app (limit A)).inv ≫
                  (H 0).map (preservesLimitIso S A).hom ≫
                  (H 0).map (limit.π (A ⋙ S) j) ≫
                  ej.hom =
                (((H 0).shiftIso m 0 m (addZeroEqSelf m)).app (limit A)).inv ≫
                  ((H 0).map (preservesLimitIso S A).hom ≫
                    (H 0).map (limit.π (A ⋙ S) j)) ≫
                  ej.hom := by
                    rw [Category.assoc]
              _ =
                (((H 0).shiftIso m 0 m (addZeroEqSelf m)).app (limit A)).inv ≫
                  (H 0).map ((preservesLimitIso S A).hom ≫ limit.π (A ⋙ S) j) ≫
                  ej.hom := by
                    rw [Functor.map_comp]
                    rfl
              _ = eLimit.inv ≫
                  (H 0).map ((preservesLimitIso S A).hom ≫ limit.π (A ⋙ S) j) ≫
                  ej.hom := by
                    rfl
      _ =
        eLimit.inv ≫ (H 0).map (S.map (limit.π A j)) ≫ ej.hom := by
          rw [hπ]
          rfl
      _ = eLimit.inv ≫ (eLimit.hom ≫ ((H 0).shift m).map (limit.π A j)) := by
          simpa [Category.assoc] using congrArg (fun k ↦ eLimit.inv ≫ k) hnat
      _ = ((H 0).shift m).map (limit.π A j) := by
          simp
  have h₅ :
      (homologyShiftLimitSourceIso A m).inv ≫
          limit.post (A ⋙ S) (H 0) ≫
          (homologyShiftLimitTargetIso A m).hom ≫
          limit.π (A ⋙ H m) j =
        (homologyShiftLimitSourceIso A m).inv ≫
          limit.post (A ⋙ S) (H 0) ≫
          limit.π ((A ⋙ S) ⋙ H 0) j ≫
          ej.hom := by
    let eFamily :=
      (Functor.associator A S (H 0)) ≪≫
        Functor.isoWhiskerLeft A ((H 0).shiftIso m 0 m (addZeroEqSelf m))
    simpa [homologyShiftLimitTargetIso, eFamily, H, S, Category.assoc, ej] using
      congrArg
        (fun k ↦ (homologyShiftLimitSourceIso A m).inv ≫ limit.post (A ⋙ S) (H 0) ≫ k)
        (limMap_π (α := eFamily.hom) (j := j))
  have h₆ :
      (homologyShiftLimitSourceIso A m).inv ≫
          limit.post (A ⋙ S) (H 0) ≫
          limit.π ((A ⋙ S) ⋙ H 0) j ≫
          ej.hom =
        (homologyShiftLimitSourceIso A m).inv ≫
          (H 0).map (limit.π (A ⋙ S) j) ≫
          ej.hom := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ (homologyShiftLimitSourceIso A m).inv ≫ k ≫ ej.hom)
        (limit.post_π (F := A ⋙ S) (G := H 0) j)
  have h₇ :
      ((H 0).shift m).map (limit.π A j) =
        limit.post A (H m) ≫ limit.π (A ⋙ H m) j := by
    simpa [H] using (limit.post_π (F := A) (G := H m) j).symm
  exact h₅.trans (h₆.trans (hshift.trans h₇))

/-- Helper for Lemma 21.24.2: the arbitrary-degree Milnor comparison for sequential towers of
cochain complexes of abelian groups follows by shifting to degree `0` and applying
Lemma `15.87.3`. -/
private theorem inverseLimitCohomologyComparison_isIso_ofVanishingR1lim
    (A : SequentialInverseSystem CpxAb)
    (m : ℤ)
    (hA_m_sub_two :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (m - 2))))
    (hA_m_sub_one :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) (m - 1))))
    (hH_m_sub_one :
      IsZero (firstDerivedLimit
        (A ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) (m - 1)))) :
    IsIso (limit.post A
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ) m)) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.up ℤ)
  let S : CpxAb ⥤ CpxAb := shiftFunctor CpxAb m
  rcases shiftedTowerHasDegreeZeroMilnorHypotheses
      A m hA_m_sub_two hA_m_sub_one hH_m_sub_one with
    ⟨hShift_negTwo, hShift_negOne, hShift_homology⟩
  haveI : IsIso (limit.post (A ⋙ S) (H 0)) := by
    -- Apply Lemma `15.87.3` exactly once to the shifted degree-`0` tower.
    exact inverse_limit_zero_cohomology_comparison_isIso_of_vanishing_r1lim
      (A ⋙ S) hShift_negTwo hShift_negOne hShift_homology
  -- Route correction: instead of simplifying the degree-`m` comparison directly, conjugate the
  -- degree-`0` comparison on the shifted tower through the named source and target isomorphisms.
  rw [← limitPostHomologyShiftBridge A m]
  infer_instance

/-- Objectwise bridge for Lemma 21.24.2, first map: on a basis object `U ∈ B`, the Milnor
comparison on sections is bijective under the three `R¹ lim←` vanishing hypotheses. -/
theorem cohomologySheafLimitComparison_app_bijective_of_basiswise_vanishing_r1lim
    (B : Set X)
    [HasLimit F]
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X F m)]
    (hdegree_m_sub_two :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionDegreeInverseSystem X F U (m - 2)).firstDerivedLimit))
    (hdegree_m_sub_one :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionDegreeInverseSystem X F U (m - 1)).firstDerivedLimit))
    (hcohom_m_sub_one :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionCohomologyInverseSystem X F U (m - 1)).firstDerivedLimit))
    (U : X) (hU : U ∈ B) :
    Function.Bijective (((limit.post F (underlyingAbelianCohomologySheafFunctor X m)).1.app
      (op U))) := by
  let A : SequentialInverseSystem (CochainComplex AddCommGrpCat.{max u v} ℤ) :=
    F ⋙ (moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ)
  haveI : IsIso
      (limit.post A
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℤ) m)) :=
    inverseLimitCohomologyComparison_isIso_ofVanishingR1lim
      (A := A) (m := m)
      (by
        -- The degree `m - 2` source hypothesis is exactly the objectwise tower needed by the
        -- generic comparison theorem.
        simpa [A, complexSectionDegreeInverseSystem, complexSectionDegreeFunctor] using
          hdegree_m_sub_two U hU)
      (by
        -- The degree `m - 1` hypothesis is the same tower, shifted by one degree.
        simpa [A, complexSectionDegreeInverseSystem, complexSectionDegreeFunctor] using
          hdegree_m_sub_one U hU)
      (by
        -- The `H^(m - 1)` hypothesis matches the objectwise cohomology tower verbatim.
        simpa [A, complexSectionCohomologyInverseSystem, complexSectionCohomologyFunctor] using
          hcohom_m_sub_one U hU)
  let η :=
    (sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v}).map
      (limit.post F (underlyingAbelianCohomologySheafFunctor X m))
  change IsIso (η.app (op U))
  -- Passing to the `U`-component identifies the sheaf comparison with the sectionwise comparison.
  have hη :
      η.app (op U) =
        limit.post A
          (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℤ) m) := by
    simp [η, A, complexSectionCohomologyFunctor, underlyingAbelianCohomologySheafFunctor]
  rw [hη]
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (show IsIso
      (limit.post A
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℤ) m)) from
      inferInstance)

/-- Lemma 21.24.2, first map: under the basiswise `R¹ lim←` vanishing hypotheses, the Milnor
comparison from the cohomology sheaf of the inverse-limit complex to the inverse limit of
cohomology sheaves is an isomorphism of underlying abelian sheaves. -/
@[stacks 08CT]
theorem cohomologySheafLimitComparison_isIso_of_basiswise_vanishing_r1lim
    (B : Set X)
    [HasLimit F]
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hdegree_m_sub_two :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionDegreeInverseSystem X F U (m - 2)).firstDerivedLimit))
    (hdegree_m_sub_one :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionDegreeInverseSystem X F U (m - 1)).firstDerivedLimit))
    (hcohom_m_sub_one :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionCohomologyInverseSystem X F U (m - 1)).firstDerivedLimit)) :
    IsIso (limit.post F (underlyingAbelianCohomologySheafFunctor X m)) :=
  sheaf_map_isIso_of_app_bijective X B
    hcover _
    (fun U hU ↦
      cohomologySheafLimitComparison_app_bijective_of_basiswise_vanishing_r1lim
        B hdegree_m_sub_two hdegree_m_sub_one hcohom_m_sub_one U hU)

/-- Source-to-canonical bridge for Lemma 21.24.2: if all transition maps
`H^m(𝓕_n^•(U)) ⟶ H^m(𝓕_{n₀}^•(U))` are isomorphisms for `n ≥ n₀`, then the corresponding
objectwise cohomology tower is eventually constant in the canonical cofiltered sense. -/
theorem complexSectionCohomologyInverseSystem_isEventuallyConstantTo_of_transitionMap_isIso
    (f : SequentialInverseSystem CpxX) (i : ℤ)
    (U : X) (n₀ : ℕ)
    (heventually_constant : ∀ n : ℕ, ∀ h : n₀ ≤ n,
      IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h)) :
    (complexSectionCohomologyInverseSystem X f U i).IsEventuallyConstantTo (op n₀) := by
  intro j k
  let hj : n₀ ≤ j.unop := leOfHom k.unop
  simpa [SequentialInverseSystem.transitionMap] using heventually_constant j.unop hj

/-- Canonical-to-source bridge for Lemma 21.24.2: eventual constancy in the cofiltered sense
forces all transition maps to the stage `n₀` to be isomorphisms. -/
theorem complexSectionCohomologyInverseSystem_transitionMap_isIso_of_isEventuallyConstantTo
    (f : SequentialInverseSystem CpxX) (i : ℤ)
    (U : X) (n₀ n : ℕ) (h : n₀ ≤ n)
    (heventually_constant :
      (complexSectionCohomologyInverseSystem X f U i).IsEventuallyConstantTo (op n₀)) :
    IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h) := by
  simpa [SequentialInverseSystem.transitionMap] using
    Functor.IsEventuallyConstantTo.isIso_map heventually_constant ((homOfLE h).op) (𝟙 (op n₀))

/-- Objectwise bridge for Lemma 21.24.2, second map: on a basis object `U ∈ B`, eventual
constancy of the degree-`m` cohomology tower identifies its inverse limit with stage `n₀`. -/
theorem cohomologySheafLimitProjection_app_bijective_of_basiswise_eventually_constant
    (f : SequentialInverseSystem CpxX) (i : ℤ)
    (B : Set X) (n₀ : ℕ)
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X f i)]
    (heventually_constant :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
        IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h))
    (U : X) (hU : U ∈ B) :
    Function.Bijective (((limit.π (underlyingAbelianCohomologySheafInverseSystem X f i)
      (op n₀)).1.app (op U))) := by
  let A := complexSectionCohomologyInverseSystem X f U i
  let hA : A.IsEventuallyConstantTo (op n₀) :=
    complexSectionCohomologyInverseSystem_isEventuallyConstantTo_of_transitionMap_isIso
      X f i U n₀ (heventually_constant U hU)
  haveI : HasLimit A := hA.hasLimit
  haveI : IsIso (limit.π A (op n₀)) := by
    simpa using hA.isIso_π_of_isLimit (limit.isLimit A)
  let η :=
    (sheafToPresheaf X.siteTopology AddCommGrpCat.{max u v}).map
      (limit.π (underlyingAbelianCohomologySheafInverseSystem X f i) (op n₀))
  -- The sheaf projection becomes the ordinary projection of the cohomology tower on sections.
  have hη : η.app (op U) = limit.π A (op n₀) := by
    simp [η, A, complexSectionCohomologyInverseSystem, complexSectionCohomologyFunctor,
      underlyingAbelianCohomologySheafInverseSystem, underlyingAbelianCohomologySheafFunctor]
  rw [hη]
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (show IsIso (limit.π A (op n₀)) from inferInstance)

/-- Lemma 21.24.2, second map: if the basiswise degree-`m` cohomology-section towers are
eventually constant from stage `n₀`, then the projection from the inverse limit of cohomology
sheaves to stage `n₀` is an isomorphism of underlying abelian sheaves. -/
@[stacks 08CT]
theorem cohomologySheafLimitProjection_isIso_of_basiswise_eventually_constant
    (f : SequentialInverseSystem CpxX) (i : ℤ)
    (B : Set X) (n₀ : ℕ)
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X f i)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (heventually_constant :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
        IsIso ((complexSectionCohomologyInverseSystem X f U i).transitionMap h)) :
    IsIso (limit.π (underlyingAbelianCohomologySheafInverseSystem X f i) (op n₀)) :=
  sheaf_map_isIso_of_app_bijective X B
    hcover _
    (fun U hU ↦
      cohomologySheafLimitProjection_app_bijective_of_basiswise_eventually_constant
        X f i B n₀ heventually_constant U hU)

/-- Canonical eventual-constancy companion for Lemma 21.24.2, second map: the basiswise
stabilization is expressed by `Functor.IsEventuallyConstantTo` for the objectwise cohomology
towers. -/
theorem cohomologySheafLimitProjection_isIso_of_basiswise_eventuallyConstantTo
    (f : SequentialInverseSystem CpxX) (i : ℤ)
    (B : Set X) (n₀ : ℕ)
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X f i)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (heventually_constant :
      ∀ U : X, U ∈ B →
        (complexSectionCohomologyInverseSystem X f U i).IsEventuallyConstantTo (op n₀)) :
    IsIso (limit.π (underlyingAbelianCohomologySheafInverseSystem X f i) (op n₀)) :=
  cohomologySheafLimitProjection_isIso_of_basiswise_eventually_constant
    X f i B n₀ hcover
    (fun U hU n h ↦
      complexSectionCohomologyInverseSystem_transitionMap_isIso_of_isEventuallyConstantTo
        X f i U n₀ n h (heventually_constant U hU))

-- Proof sketch: for each basis object `U ∈ B`, apply Lemma `15.87.3` to the tower of complexes
-- `Γ(U, 𝓕_n^•)` in degrees shifted by `m`; the hypotheses force the comparison
-- `H^m(Γ(U, lim←_n 𝓕_n^•)) ⟶ lim←_n H^m(Γ(U, 𝓕_n^•))` to be an isomorphism, and eventual
-- constancy identifies the latter with `H^m(Γ(U, 𝓕_{n₀}^•))`. The canonical cover owner
-- `X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B)` supplies a cover of every object by basis
-- members, so the two resulting morphisms of underlying abelian sheaves are isomorphisms.
/-- Lemma 21.24.2: let `(𝒞, 𝒪)` be a ringed site, let `(𝓕_n^•)_n` be an inverse system of
complexes of `𝒪`-modules, and let `m ∈ ℤ`. If a subset `B` of objects covers the site, if for
every `U ∈ B` the towers `n ↦ 𝓕_n^(m - 2)(U)`, `n ↦ 𝓕_n^(m - 1)(U)`, and
`n ↦ H^(m - 1)(𝓕_n^•(U))` have vanishing `R¹ lim←`, and if the tower
`n ↦ H^m(𝓕_n^•(U))` is constant from stage `n₀` on for every `U ∈ B`, then the canonical maps
`H^m(lim←_n 𝓕_n^•) ⟶ lim←_n H^m(𝓕_n^•) ⟶ H^m(𝓕_{n₀}^•)` are isomorphisms of underlying abelian
sheaves. -/
@[stacks 08CT]
theorem cohomologySheafLimitComparison_and_projection_isIso_of_basiswise_vanishing_r1lim
    (B : Set X) (n₀ : ℕ)
    [HasLimit F]
    [HasLimit (underlyingAbelianCohomologySheafInverseSystem X F m)]
    (hcover : X.siteTopology.HasEnoughObjectsWithProperty (· ∈ B))
    (hdegree_m_sub_two :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionDegreeInverseSystem X F U (m - 2)).firstDerivedLimit))
    (hdegree_m_sub_one :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionDegreeInverseSystem X F U (m - 1)).firstDerivedLimit))
    (hcohom_m_sub_one :
      ∀ U : X, U ∈ B →
        IsZero ((complexSectionCohomologyInverseSystem X F U (m - 1)).firstDerivedLimit))
    (heventually_constant :
      ∀ U : X, U ∈ B → ∀ n : ℕ, ∀ h : n₀ ≤ n,
        IsIso ((complexSectionCohomologyInverseSystem X F U m).transitionMap h)) :
    IsIso (limit.post F (underlyingAbelianCohomologySheafFunctor X m)) ∧
      IsIso (limit.π (underlyingAbelianCohomologySheafInverseSystem X F m) (op n₀)) :=
  ⟨ cohomologySheafLimitComparison_isIso_of_basiswise_vanishing_r1lim
      B hcover hdegree_m_sub_two hdegree_m_sub_one hcohom_m_sub_one,
    cohomologySheafLimitProjection_isIso_of_basiswise_eventually_constant
      X F m B n₀ hcover heventually_constant ⟩

end
