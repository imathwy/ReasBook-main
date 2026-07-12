import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap13.Definition_13_36_3
import StacksProject_2024.Chap13.Lemma_13_36_2
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_75_4
import StacksProject_2024.Chap15.RingSingle
import Mathlib.Tactic.StacksAttribute

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "PerfectObj" => (DerivedCategory.IsPerfect : ObjectProperty DMod)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- The perfect derived category `D_{perf}(R)` as a full subcategory of `D(R)`. -/
abbrev DPerf (R : Type u) [Ring R] : Type (u + 1) :=
  ObjectProperty.FullSubcategory
    (DerivedCategory.IsPerfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))

/-
Domain-style sampling for Lemma 15.79.1:
- primary domain: generators and generated thick object properties in triangulated categories,
  specialized to perfect objects in `D(R)`;
- sampled owner declarations:
  `IsClassicalGenerator`,
  `CategoryTheory.ObjectProperty.objectGeneratedProperty`,
  `CategoryTheory.ObjectProperty.objectGeneratedProperty_le_iff`,
  `DerivedCategory.IsPerfect`,
  `DerivedCategory.singleFunctor`,
  `FiniteProjectiveModuleCat`;
- best owner abstractions:
  the perfectness owner is `DerivedCategory.IsPerfect`, the canonical degree-zero embedding is the
  degree-zero single functor, and the reusable Chapter 15 bridge/view is the full subcategory
  `DPerf R` together with the specific object `ringSingle : D(R)`;
- primitive vs. derived:
  primitive data in this file are the degree-zero object attached to a finite projective module,
  while the specific ring object `ringSingle` is reused from the tensor-unit owner file
  `15_74_0_2`; the generated-property and classical-generator statements are derived through the
  existing Chapter 13 owner API;
- source/core/bridge triage:
  `source-facing`: the equality `D_perf(R) = ⟨R[0]⟩` and the resulting classical-generator
    statement in the perfect derived category;
  `core/canonical`: `DerivedCategory.IsPerfect`, `IsClassicalGenerator`, and
    `CategoryTheory.ObjectProperty.objectGeneratedProperty`;
  `bridge/view`: the finite-projective degree-zero perfectness theorem and its specialization to
    `ringSingle`.
-/

variable (R) in
/-- Helper for Lemma 15.79.1: the cochain single complex on a finite projective module is a bounded
finite-projective representative. -/
private theorem finiteProjectiveModule_single_isBoundedFiniteProjective
    (M : FiniteProjectiveModuleCat R) :
    CochainComplex.IsBoundedFiniteProjective
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj) := by
  -- Proof comment: the single complex is supported in degree `0`; outside degree `0` the terms
  -- are zero, hence still finite and projective.
  refine ⟨⟨0, 0, ?_, ?_⟩, ?_, ?_⟩
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj).IsStrictlyGE (0 : ℤ))
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj).IsStrictlyLE (0 : ℤ))
  · intro i
    by_cases hi : i = 0
    · subst hi
      simpa using
        (Module.Finite.equiv
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M.obj).toLinearEquiv.symm)
          M.property.1)
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj).X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M.obj i hi
      simpa using
        (Module.Finite.equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Finite R (0 : ModuleCat R)))
  · intro i
    by_cases hi : i = 0
    · subst hi
      simpa using
        (Module.Projective.of_equiv
          ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M.obj).toLinearEquiv.symm)
          M.property.2)
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj).X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) (0 : ℤ) M.obj i hi
      simpa using
        (Module.Projective.of_equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Projective R (0 : ModuleCat R)))

variable (R) in
/-- The degree-zero complex of a finite projective `R`-module is a perfect object of `D(R)`. -/
theorem finiteProjectiveModule_single_isPerfect (M : FiniteProjectiveModuleCat R) :
    ((single₀).obj M.obj).IsPerfect := by
  -- Proof comment: witness perfectness by the literal degree-zero single complex on `M`.
  refine ⟨(CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj, ?_, ?_⟩
  · -- Proof comment: the unbounded derived single functor is computed by the cochain single
    -- complex in degree `0`.
    simpa using (Iso.refl ((single₀).obj M.obj))
  · simpa using finiteProjectiveModule_single_isBoundedFiniteProjective (R := R) M

private abbrev ringFiniteProjectiveModule : FiniteProjectiveModuleCat R :=
  ⟨ModuleCat.of R R, ⟨inferInstance, inferInstance⟩⟩

/-- The degree-zero complex `R[0]` of the free rank-one `R`-module is a perfect object. -/
theorem ring_single_isPerfect :
    DerivedCategory.IsPerfect (ringSingle : DMod) := by
  simpa [ringSingle, ringFiniteProjectiveModule] using
    finiteProjectiveModule_single_isPerfect R ringFiniteProjectiveModule

/-- The canonical object `R[0]` viewed inside the perfect derived category `D_{perf}(R)`. -/
abbrev ringSingleInPerfectDerived (R : Type u) [Ring R] : DPerf R :=
  ⟨ringSingle, ring_single_isPerfect⟩

local instance perfectObjectPropertyContainsZero :
    CategoryTheory.ObjectProperty.ContainsZero PerfectObj :=
  inferInstance

/-- Helper for Lemma 15.79.1: functions on `Fin (n + 1)` split into the first coordinate and the
remaining `Fin n` coordinates. -/
private noncomputable def finSuccArrowLinearEquiv (n : ℕ) :
    (Fin (n + 1) → R) ≃ₗ[R] (R × (Fin n → R)) where
  toEquiv := (Fin.consEquiv fun _ : Fin (n + 1) => R).symm
  map_add' f g := by
    rfl
  map_smul' r f := by
    rfl

/-- Helper for Lemma 15.79.1: if `P ≤ Q` and `Q` is shift-stable, then every bounded shift
interval of `P` also lies in `Q`. -/
private theorem shiftInterval_le_of_le
    {P Q : ObjectProperty DMod}
    [Q.IsClosedUnderIsomorphisms] [Q.IsStableUnderShift ℤ]
    (hPQ : P ≤ Q) (a b : ℤ) :
    P[a, b] ≤ Q := by
  intro X hX
  -- Proof comment: unwrap the interval witness, convert the underlying shifted `P`-membership to
  -- `Q`, then shift back using the stability of `Q`.
  rw [prop_shiftInterval_iff] at hX
  rcases hX with ⟨n, _, Y, hY, ⟨e⟩⟩
  rw [prop_shift_iff] at hY
  have hQshift : Q (Y⟦n⟧) := hPQ _ hY
  have hQYshiftNeg : Q ((Y⟦n⟧)⟦(-n : ℤ)⟧) := Q.le_shift (-n : ℤ) _ hQshift
  have hQY : Q Y := Q.prop_of_iso (shiftShiftNeg Y n) hQYshiftNeg
  exact Q.prop_of_iso e.symm hQY

/-- Helper for Lemma 15.79.1: if `P ≤ Q` and `Q` is saturated triangulated, then every additive
extension stage built from `P` also lies in `Q`. -/
private theorem additiveExtensionStage_le_of_le
    {P Q : ObjectProperty DMod}
    [Q.IsStableUnderRetracts] [Q.IsTriangulated]
    (hPQ : P ≤ Q) (n : ℕ+) :
    additiveExtensionStage P n ≤ Q := by
  -- Proof comment: this is the same closure argument used in the owner proof of
  -- `objectGeneratedProperty_le_iff`, now applied directly to the chosen base property `P`.
  rw [additiveExtensionStage, retractClosure_le_iff]
  exact P.additiveClosure.extensionProductIter_le_of_isTriangulatedClosed₂
    (by
      refine colimitsClosure_le ?_
      exact hPQ)
    n.natPred

/-- Helper for Lemma 15.79.1: the degree-zero single on the finite free module `R^n` is generated
by `R[0]`. -/
private theorem finite_free_single_mem_objectGeneratedProperty_ring_single
    (n : ℕ) :
    (⟨ringSingle⟩ : ObjectProperty DMod) ((single₀).obj (ModuleCat.of R (Fin n → R))) := by
  induction n with
  | zero =>
      -- Proof comment: the rank-zero free module is zero, and generated properties contain zero.
      have hzero :
          ModuleCat.of R (Fin 0 → R) ≅ ModuleCat.of R PUnit := by
        exact (LinearEquiv.ofSubsingleton _ _).toModuleIso
      have hsingleZeroObj :
          IsZero ((single₀).obj (ModuleCat.of R PUnit)) := by
        let hzeroModule : IsZero (ModuleCat.of R PUnit) :=
          ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit)
        exact (single₀).map_isZero hzeroModule
      have hsingleZero :
          ((single₀).obj (ModuleCat.of R (Fin 0 → R))) ≅
            ((single₀).obj (ModuleCat.of R PUnit)) :=
        (single₀).mapIso hzero
      have hgenZero :
          (⟨ringSingle⟩ : ObjectProperty DMod) ((single₀).obj (ModuleCat.of R PUnit)) := by
        exact ObjectProperty.prop_of_isZero
          (P := (⟨ringSingle⟩ : ObjectProperty DMod)) hsingleZeroObj
      exact (⟨ringSingle⟩).prop_of_iso hsingleZero.symm hgenZero
  | succ n ih =>
      letI :
          PreservesBinaryBiproducts (single₀) :=
        CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts (single₀)
      let eModule :
          ModuleCat.of R (Fin (n + 1) → R) ≅
            (ModuleCat.of R R) ⊞ (ModuleCat.of R (Fin n → R)) :=
        (finSuccArrowLinearEquiv (R := R) n).toModuleIso ≪≫
          (ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R (Fin n → R))).symm
      let eSingle :
          (single₀).obj (ModuleCat.of R (Fin (n + 1) → R)) ≅
            (((single₀).obj (ModuleCat.of R R)) ⊞
              ((single₀).obj (ModuleCat.of R (Fin n → R)))) :=
        ((single₀).mapIso eModule) ≪≫
          (single₀).mapBiprod (ModuleCat.of R R) (ModuleCat.of R (Fin n → R))
      have hring : (⟨ringSingle⟩ : ObjectProperty DMod) ((single₀).obj (ModuleCat.of R R)) := by
        simpa [ringSingle] using objectGeneratedProperty_contains (ringSingle : DMod)
      have hbiprod :
          (⟨ringSingle⟩ : ObjectProperty DMod)
            (((single₀).obj (ModuleCat.of R R)) ⊞
              ((single₀).obj (ModuleCat.of R (Fin n → R)))) := by
        exact (⟨ringSingle⟩).prop_biprod hring ih
      -- Proof comment: rewrite the free rank-`n + 1` module as the biproduct of one copy of `R`
      -- and a free rank-`n` module, then use binary-coproduct closure.
      exact (⟨ringSingle⟩).prop_of_iso eSingle.symm hbiprod

/-- Helper for Lemma 15.79.1: the degree-zero single on any finite projective module is generated
by `R[0]`. -/
private theorem finiteProjective_single_mem_objectGeneratedProperty_ring_single
    (M : FiniteProjectiveModuleCat R) :
    (⟨ringSingle⟩ : ObjectProperty DMod) ((single₀).obj M.obj) := by
  let _ : Module.Finite R M.obj := M.property.1
  let _ : Module.Projective R M.obj := M.property.2
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M.obj
  let πCat : ModuleCat.of R (Fin n → R) ⟶ M.obj := ModuleCat.ofHom π
  letI : Epi πCat := (ModuleCat.epi_iff_surjective _).2 hπ
  letI : Projective M.obj := by infer_instance
  let σCat : M.obj ⟶ ModuleCat.of R (Fin n → R) :=
    Projective.factorThru (𝟙 M.obj) πCat
  have hsplit : σCat ≫ πCat = 𝟙 M.obj := by
    -- Proof comment: projectivity lifts the identity of `M` across the chosen finite free cover.
    exact Projective.factorThru_comp (𝟙 M.obj) πCat
  let r : Retract M.obj (ModuleCat.of R (Fin n → R)) := ⟨σCat, πCat, hsplit⟩
  have hfree :
      (⟨ringSingle⟩ : ObjectProperty DMod) ((single₀).obj (ModuleCat.of R (Fin n → R))) :=
    finite_free_single_mem_objectGeneratedProperty_ring_single (R := R) n
  -- Proof comment: applying `single₀` transports the split finite free cover to a retract in
  -- `D(R)`, and generated properties are stable under retracts.
  exact (⟨ringSingle⟩).prop_of_retract (r.map single₀) hfree

/-- Helper for Lemma 15.79.1: every bounded shift interval built from degree-zero singles of
finite projective modules already lies in `⟨R[0]⟩`. -/
private theorem finiteProjective_shiftInterval_le_objectGeneratedProperty_ring_single
    (a b : ℤ) :
    ((((finiteProjectiveModuleProperty R).map single₀)[a, b] : ObjectProperty DMod) ≤
      ⟨ringSingle⟩) := by
  have hbase :
      (((finiteProjectiveModuleProperty R).map single₀ : ObjectProperty DMod) ≤
        ⟨ringSingle⟩) := by
    intro X hX
    -- Proof comment: unpack the image-property witness and reduce to the finite-projective single
    -- case already handled above.
    rcases hX with ⟨M, hM, ⟨e⟩⟩
    let M' : FiniteProjectiveModuleCat R := ⟨M, hM⟩
    exact (⟨ringSingle⟩).prop_of_iso e <|
      finiteProjective_single_mem_objectGeneratedProperty_ring_single (R := R) M'
  -- Proof comment: once the base property is inside `⟨R[0]⟩`, shift stability enlarges this to
  -- the whole bounded shift interval.
  exact shiftInterval_le_of_le hbase a b

/-- Helper for Lemma 15.79.1: every additive-extension stage built from bounded shift intervals of
finite projective singles already lies in `⟨R[0]⟩`. -/
private theorem finiteProjective_intervalStage_le_objectGeneratedProperty_ring_single
    (a b : ℤ) (n : ℕ+) :
    additiveExtensionStage (((finiteProjectiveModuleProperty R).map single₀)[a, b]) n ≤
      ⟨ringSingle⟩ := by
  -- Proof comment: apply the generic closure lemma to the specialized interval containment above.
  exact additiveExtensionStage_le_of_le
    (finiteProjective_shiftInterval_le_objectGeneratedProperty_ring_single (R := R) a b) n

-- Proof sketch: for `⟨R[0]⟩ ≤ D_perf(R)`, apply `objectGeneratedProperty_le_iff` to the
-- triangulated retract-stable object property of perfect objects, using `ring_single_isPerfect`.
-- For the reverse inclusion, represent a perfect object by a bounded finite-projective complex and
-- feed that representative to the Chapter 13 interval-stage theorem; the interval base property is
-- already contained in `⟨R[0]⟩` because each finite projective module is a retract of a finite free
-- module, hence generated by `R[0]`.
/-- Helper for Lemma 15.79.1: every perfect object of `D(R)` is generated by `R[0]`. -/
private theorem perfect_mem_objectGeneratedProperty_ring_single
    {K : DMod} (hK : PerfectObj K) :
    (⟨ringSingle⟩ : ObjectProperty DMod) K := by
  -- Route correction: unpack `PerfectObj` directly into a bounded finite-projective
  -- representative and feed that representative to the Chapter 13 interval-stage theorem.
  rcases hK with ⟨L, e, hL⟩
  letI : CochainComplex.IsBoundedFiniteProjective L := hL
  rcases hL.bounded with ⟨a, b, hGE, hLE⟩
  have hstage :
      additiveExtensionStage (((finiteProjectiveModuleProperty R).map single₀)[a, b])
        (Nat.succPNat (Int.toNat (b - a))) K := by
    -- Proof comment: the bounded representative `L` has finite projective terms on the whole
    -- support interval `[a, b]`, so Lemma 13.35.7 places `K` in the corresponding extension stage.
    refine mem_additiveExtensionStage_of_exists_representative_mem
      (E := finiteProjectiveModuleProperty R) (K := K) (a := a) (b := b) ?_
    refine ⟨L, e.symm, hGE, hLE, ?_⟩
    intro i
    exact ⟨hL.finite i.1, hL.projective i.1⟩
  -- Proof comment: specialize the interval-stage containment proved above to conclude that this
  -- stage is already contained in the thick subcategory generated by `R[0]`.
  exact
    (finiteProjective_intervalStage_le_objectGeneratedProperty_ring_single
      (R := R) a b (Nat.succPNat (Int.toNat (b - a)))) K hstage

/-- Lemma 15.79.1: the perfect objects of `D(R)` are exactly the objects in the smallest strictly
full saturated triangulated subcategory generated by `R = R[0]`, i.e. `D_{perf}(R) = ⟨R⟩`. -/
@[stacks 0ATI]
theorem perfectObjectProperty_eq_objectGeneratedProperty_ring_single :
    PerfectObj = ⟨ringSingle⟩ := by
  apply le_antisymm
  · -- Proof comment: the source-faithful direction is the bounded finite-projective induction
    -- route executed above through the Chapter 13 interval-stage theorem.
    intro K hK
    exact perfect_mem_objectGeneratedProperty_ring_single (R := R) hK
  · -- Proof comment: `R[0]` is itself perfect, so the thick subcategory it generates is contained
    -- in the perfect objects by the universal property of `⟨R[0]⟩`.
    exact objectGeneratedProperty_le_of_mem ringSingle PerfectObj ring_single_isPerfect

/-- The object `R[0]` is a classical generator of the perfect derived subcategory `D_{perf}(R)`. -/
-- Proof sketch: after transporting `D_{perf}(R)` to `⟨R[0]⟩` using
-- `perfectObjectProperty_eq_objectGeneratedProperty_ring_single`, any saturated triangulated
-- subcategory of `D_{perf}(R)` containing `R[0]` must be all of `D_{perf}(R)` by the universal
-- property of `objectGeneratedProperty`.
theorem ring_single_isClassicalGenerator_in_perfectDerivedCategory :
    IsClassicalGenerator (ringSingleInPerfectDerived R) := by
  rw [isClassicalGenerator_iff_singleton_le]
  intro P _ _
  intro hP
  let iPerf : DPerf R ⥤ DMod := ObjectProperty.ι PerfectObj
  let Q : ObjectProperty DMod := P.map iPerf
  letI : Q.IsTriangulated := inferInstance
  letI : Q.IsStableUnderRetracts :=
    { of_retract := by
        intro X' Y' r hY
        let Pc : ObjectProperty DMod := PerfectObj
        rcases hY with ⟨Yc, hYc, ⟨e⟩⟩
        have r₀ : Retract X' Yc.obj := r.trans (Retract.ofIso e.symm)
        have hXperfect : PerfectObj X' := Pc.prop_of_retract r₀ Yc.property
        let Xc : DPerf R := ⟨X', hXperfect⟩
        let i' : Xc ⟶ Yc := { hom := r₀.i }
        let r' : Yc ⟶ Xc := { hom := r₀.r }
        have hr' : i' ≫ r' = 𝟙 Xc := by
          ext
          simpa [i', r'] using r₀.retract
        exact ⟨Xc, P.prop_of_retract ⟨i', r', hr'⟩ hYc, ⟨Iso.refl _⟩⟩ }
  have hsource : P (ringSingleInPerfectDerived R) := by
    simpa [singleton_le_iff] using hP
  have hQring : Q ringSingle := by
    -- Proof comment: the ambient image of `P` contains the generator `R[0]`.
    simpa [Q, iPerf, ringSingleInPerfectDerived] using P.prop_map_obj iPerf hsource
  have hle : ⟨ringSingle⟩ ≤ Q := objectGeneratedProperty_le_of_mem ringSingle Q hQring
  refine top_unique ?_
  intro X _
  have hambient : (⟨ringSingle⟩ : ObjectProperty DMod) X.obj := by
    -- Proof comment: rewrite the ambient perfectness witness using the main equality proved above.
    simpa [perfectObjectProperty_eq_objectGeneratedProperty_ring_single (R := R)] using X.property
  have hQX : Q X.obj := hle X.obj hambient
  rcases hQX with ⟨Y, hY, ⟨e⟩⟩
  -- Proof comment: lift the ambient isomorphism back to the full subcategory `D_{perf}(R)` and
  -- transport membership in `P` along it.
  exact P.prop_of_iso (ObjectProperty.isoMk (P := PerfectObj) e) hY

end

end CategoryTheory
