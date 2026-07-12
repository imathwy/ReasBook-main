import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.Shift
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.Chap13.Lemma_13_28_2
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap10.Lemma_10_55_6
import StacksProject_2024.Chap15.Definition_15_75_1
import StacksProject_2024.Chap15.Lemma_15_120_1
import StacksProject_2024.Chap15.Lemma_15_79_1

noncomputable section

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u v

set_option checkBinderAnnotations false

attribute [local instance] HasDerivedCategory.standard

section

variable (R : Type u) [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "K₀" => projectiveGrothendieckGroup R
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

private abbrev perfectObjectProperty :
    ObjectProperty (DerivedCategory (ModuleCat R)) :=
  (DerivedCategory.IsPerfect : ObjectProperty (DerivedCategory (ModuleCat R)))

/- Domain-style sampling for Lemma 15.120.2:
- primary domain: the zeroth `K`-group of the perfect derived category and its comparison with the
  Grothendieck group of finite projective modules;
- sampled owner declarations:
  `CategoryTheory.TriangulatedK0`,
  `CategoryTheory.TriangulatedK0.lift`,
  `CategoryTheory.boundedDerivedCategoryK0Equiv`,
  `projectiveGrothendieckGroup`;
- best owner abstraction:
  the source-facing map is the Euler-characteristic homomorphism
  `K₀(D_{perf}(R)) → K₀(R)`, while the canonical owner for the identification itself is the
  additive equivalence between these two `K₀`-groups;
- primitive vs. derived:
  primitive data in this file are the two additive maps and the relation-killing lemmas needed to
  construct them;
  derived API is bijectivity and the resulting equivalence, so those should be built from the
  inverse laws rather than through a parallel proof path;
- source/core/bridge triage:
  `source-facing`: the bijectivity of the comparison map from `K₀(D_{perf}(R))` to `K₀(R)`;
  `core/canonical`: the additive equivalence between `TriangulatedK0 (DPerf R)` and
    `projectiveGrothendieckGroup R`;
  `bridge/view`: the degree-zero embedding of finite projective modules into `D_{perf}(R)` and
    the Euler-characteristic map in the opposite direction.

This file should therefore keep the source-facing bijectivity theorem, but organize the API around
the additive equivalence owner exactly as in the chapter's earlier `K₀` comparison files.
-/

-- Proof sketch: a distinguished triangle in `D_{perf}(R)` is distinguished after forgetting to
-- `D(R)`, and `DPerf.eulerCharacteristic_add_of_distinguishedTriangle` shows that the associated
-- triangulated relation maps to zero in `K₀(R)`.
/-- Distinguished-triangle relations in `K₀(D_{perf}(R))` are killed by the Euler-characteristic
generator map. -/
private theorem triangulatedK0Relations_le_ker_perfectDerivedCategoryK0 :
    TriangulatedK0.relations (DPerf R) ≤
      (FreeAbelianGroup.lift fun K : DPerf R ↦ K.eulerCharacteristic).ker := by
  -- Proof comment: reduce to a single distinguished triangle generator and apply additivity of
  -- Euler characteristic across distinguished triangles in `D_{perf}(R)`.
  rw [TriangulatedK0.relations, AddSubgroup.closure_le]
  rintro _ ⟨T, rfl⟩
  rcases T with ⟨T, hT⟩
  change
    (FreeAbelianGroup.lift fun K : DPerf R ↦ K.eulerCharacteristic)
      (FreeAbelianGroup.of T.obj₂ - FreeAbelianGroup.of T.obj₁ - FreeAbelianGroup.of T.obj₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    sub_eq_zero.mpr (DPerf.eulerCharacteristic_add_of_distinguishedTriangle (R := R) hT)

/-- The comparison homomorphism `c : K₀(D_{perf}(R)) → K₀(R)` sending a perfect complex to the
Euler characteristic of any bounded finite-projective representative. -/
noncomputable def perfectDerivedCategoryK0ToProjectiveGrothendieckGroup :
    TriangulatedK0 (DPerf R) →+ K₀ :=
  TriangulatedK0.lift
    DPerf.eulerCharacteristic
    (triangulatedK0Relations_le_ker_perfectDerivedCategoryK0 R)

/-- The Euler-characteristic map sends the class of a perfect complex to its canonical
Euler-characteristic class in `K₀(R)`. -/
@[simp] theorem perfectDerivedCategoryK0ToProjectiveGrothendieckGroup_apply_of
    (K : DPerf R) :
    perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R (TriangulatedK0.of K) =
      K.eulerCharacteristic := by
  simpa [perfectDerivedCategoryK0ToProjectiveGrothendieckGroup] using
    TriangulatedK0.lift_of
      (fun K : DPerf R ↦ K.eulerCharacteristic)
      (triangulatedK0Relations_le_ker_perfectDerivedCategoryK0 R)
      K

/-- The degree-zero perfect complex attached to a finite projective `R`-module, viewed as an
object of `D_{perf}(R)`. -/
abbrev finiteProjectiveModule_singleInPerfectDerived (M : FiniteProjectiveModuleCat R) :
    DPerf R :=
  ⟨(single₀).obj M.obj, finiteProjectiveModule_single_isPerfect R M⟩

/-- Helper for Lemma 15.120.2: the degree-zero embedding of finite projective modules into the
perfect derived category. -/
private abbrev finiteProjectiveModuleToPerfectDerived :
    FiniteProjectiveModuleCat R ⥤ DPerf R :=
  ObjectProperty.lift
    (perfectObjectProperty (R := R))
    ((finiteProjectiveModuleProperty R).ι ⋙ single₀)
    (fun M ↦ finiteProjectiveModule_single_isPerfect R M)

/-- Helper for Lemma 15.120.2: a short exact sequence of finite projective modules yields the
canonical triangle of degree-zero perfect complexes. -/
private def finiteProjectiveModuleToPerfectDerivedTriangle
    {S : ShortComplex (FiniteProjectiveModuleCat R)}
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    Triangle (DPerf R) :=
  Triangle.mk
    ((finiteProjectiveModuleToPerfectDerived R).map S.f)
    ((finiteProjectiveModuleToPerfectDerived R).map S.g)
    ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage
      (hS.singleδ ≫
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).inv.app
    ((finiteProjectiveModuleToPerfectDerived R).obj S.X₁)))

/-- Helper for Lemma 15.120.2: the degree-`c` single complex on a finite projective module is
the `(-c)`-shift of the degree-zero perfect object on the same module. -/
private noncomputable def singleFunctor_obj_iso_shifted_single0_in_DPerf
    (M : FiniteProjectiveModuleCat R) (c : ℤ) :
    (DerivedCategory.singleFunctor (ModuleCat R) c).obj M.obj ≅
      (finiteProjectiveModule_singleInPerfectDerived R M).obj⟦-c⟧ := by
  let eShifted :
      (((DerivedCategory.singleFunctor (ModuleCat R) c).obj M.obj)⟦c⟧) ≅
        (finiteProjectiveModule_singleInPerfectDerived R M).obj := by
    -- Proof comment: this is exactly the canonical `singleFunctors.shiftIso`, rewritten so the
    -- target is the degree-zero perfect object already used elsewhere in this file.
    simpa [finiteProjectiveModule_singleInPerfectDerived] using
      ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso c 0 c (by simp)).app M.obj
  -- Proof comment: shift the canonical comparison back by `-c` and collapse the double shift on
  -- the source with `shiftFunctorCompIsoId`.
  exact
    ((shiftFunctorCompIsoId (DerivedCategory (ModuleCat R)) c (-c) (by simp)).app
      ((DerivedCategory.singleFunctor (ModuleCat R) c).obj M.obj)).symm ≪≫
      (shiftFunctor (DerivedCategory (ModuleCat R)) (-c)).mapIso eShifted

/-- Helper for Lemma 15.120.2: the degree-zero triangle attached to a short exact sequence of
finite projective modules is distinguished in `D_{perf}(R)`. -/
private theorem finiteProjectiveModuleToPerfectDerivedTriangle_distinguished
    {S : ShortComplex (FiniteProjectiveModuleCat R)}
    (hS : (S.map (finiteProjectiveModuleProperty R).ι).ShortExact) :
    finiteProjectiveModuleToPerfectDerivedTriangle R hS ∈ distTriang (DPerf R) := by
  -- Proof comment: forget the triangle to `D(R)`, identify it with the standard single-complex
  -- triangle attached to the short exact sequence, and transport distinguishedness back.
  rw [← (ObjectProperty.ι (perfectObjectProperty (R := R))).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).map
          ((finiteProjectiveModuleToPerfectDerived R).map S.f))
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).map
          ((finiteProjectiveModuleToPerfectDerived R).map S.g))
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).map
            ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage
              (hS.singleδ ≫
                ((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).inv.app
                  ((finiteProjectiveModuleToPerfectDerived R).obj S.X₁))) ≫
          ((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).hom.app
            ((finiteProjectiveModuleToPerfectDerived R).obj S.X₁)) ∈
      distTriang (DerivedCategory (ModuleCat R))
  rw [(ObjectProperty.ι (perfectObjectProperty (R := R))).map_preimage]
  refine isomorphic_distinguished _ hS.singleTriangle_distinguished _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp [finiteProjectiveModuleToPerfectDerived]
  · simp [finiteProjectiveModuleToPerfectDerived]
  · simpa [Category.assoc] using
      congrArg
        (fun k ↦ hS.singleδ ≫ k)
        (((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).inv_hom_id_app
          ((finiteProjectiveModuleToPerfectDerived R).obj S.X₁))

/-- Helper for Lemma 15.120.2: the degree-zero complex of a finite projective module is a bounded
finite-projective representative. -/
private theorem finiteProjectiveModule_single_isBoundedFiniteProjective_at
    (M : FiniteProjectiveModuleCat R) (c : ℤ) :
    CochainComplex.IsBoundedFiniteProjective
      ((CochainComplex.singleFunctor (ModuleCat R) c).obj M.obj) := by
  -- Proof comment: the single complex is supported in degree `c`; outside that degree every term
  -- is zero, hence still finite and projective.
  refine ⟨⟨c, c, ?_, ?_⟩, ?_, ?_⟩
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) c).obj M.obj).IsStrictlyGE c)
  · simpa using
      (inferInstance :
        ((CochainComplex.singleFunctor (ModuleCat R) c).obj M.obj).IsStrictlyLE c)
  · intro i
    by_cases hi : i = c
    · subst hi
      simpa using
        (Module.Finite.equiv
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) c M.obj).toLinearEquiv.symm
          M.property.1)
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((CochainComplex.singleFunctor (ModuleCat R) c).obj M.obj).X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) c M.obj i hi
      simpa using
        (Module.Finite.equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Finite R (0 : ModuleCat R)))
  · intro i
    by_cases hi : i = c
    · subst hi
      simpa using
        (Module.Projective.of_equiv
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) c M.obj).toLinearEquiv.symm
          M.property.2)
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((CochainComplex.singleFunctor (ModuleCat R) c).obj M.obj).X i) :=
        HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) c M.obj i hi
      simpa using
        (Module.Projective.of_equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Projective R (0 : ModuleCat R)))

/-- Helper for Lemma 15.120.2: the degree-zero complex of a finite projective module is a bounded
finite-projective representative. -/
private theorem finiteProjectiveModule_single_isBoundedFiniteProjective
    (M : FiniteProjectiveModuleCat R) :
    CochainComplex.IsBoundedFiniteProjective
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj) := by
  simpa using finiteProjectiveModule_single_isBoundedFiniteProjective_at (R := R) M (0 : ℤ)

/-- Helper for Lemma 15.120.2: the Euler characteristic of a degree-zero finite-projective
complex is the Grothendieck class of its unique nonzero term. -/
private theorem finiteProjectiveModule_single_complex_eulerCharacteristic
    (M : FiniteProjectiveModuleCat R)
    [CochainComplex.IsBoundedFiniteProjective
      ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj)] :
    CochainComplex.eulerCharacteristic (R := R)
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj) =
      projectiveGrothendieckGroupOf R M := by
  -- Proof comment: the support interval is `[0, 0]`, so only the degree-`0` term survives in
  -- the Euler sum, and `singleObjXSelf` identifies that term with `M`.
  let L := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj
  letI : CochainComplex.IsBoundedFiniteProjective L :=
    finiteProjectiveModule_single_isBoundedFiniteProjective (R := R) M
  let S : FiniteProjectiveModuleCat R := ⟨L.X 0, ⟨inferInstance, inferInstance⟩⟩
  have hS :
      projectiveGrothendieckGroupOf R S = projectiveGrothendieckGroupOf R M := by
    -- The only surviving term is literally the degree-`0` value of the single complex.
    exact projectiveGrothendieckGroupOf_eq_of_iso (R := R)
      ((finiteProjectiveModuleProperty R).isoMk
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) M.obj))
  rw [CochainComplex.eulerCharacteristic_eq_sum_Icc (R := R) (L := L)
    (show L.IsStrictlyGE 0 by infer_instance) (show L.IsStrictlyLE 0 by infer_instance)]
  simp only [Finset.Icc_self, Finset.sum_singleton, Int.negOnePow_zero, one_smul]
  simpa [L, S] using hS

/-- Helper for Lemma 15.120.2: the perfect-derived Euler characteristic of `M[0]` is `[M]`. -/
private theorem finiteProjectiveModule_singleInPerfectDerived_eulerCharacteristic
    (M : FiniteProjectiveModuleCat R) :
    (finiteProjectiveModule_singleInPerfectDerived R M).eulerCharacteristic =
      projectiveGrothendieckGroupOf R M := by
  -- Proof comment: represent the perfect object by the literal degree-zero single complex and
  -- identify its canonical Euler characteristic with the complex-level Euler sum.
  let L := (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M.obj
  have hValue :
      (finiteProjectiveModule_singleInPerfectDerived R M).IsEulerCharacteristicValue
        (projectiveGrothendieckGroupOf R M) := by
    refine ⟨L, Iso.refl _, finiteProjectiveModule_single_isBoundedFiniteProjective (R := R) M, ?_⟩
    letI : CochainComplex.IsBoundedFiniteProjective L :=
      finiteProjectiveModule_single_isBoundedFiniteProjective (R := R) M
    simpa [L] using (finiteProjectiveModule_single_complex_eulerCharacteristic (R := R) M).symm
  exact (DPerf.eq_eulerCharacteristic hValue).symm

-- Proof sketch: a short exact sequence of finite projective modules yields a distinguished
-- triangle of the associated degree-zero complexes in `D(R)`, so the defining Grothendieck
-- relation maps to zero in `K₀(D_{perf}(R))`.
/-- The Grothendieck relations of finite projective modules are killed after passing to degree-zero
perfect complexes. -/
private theorem projectiveGrothendieckGroup_relations_le_ker_toPerfectDerivedCategoryK0 :
    modulePropertyK0Relations R (finiteProjectiveModuleProperty R) ≤
      (FreeAbelianGroup.lift fun M : FiniteProjectiveModuleCat R ↦
        TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M)).ker := by
  -- Proof comment: a generator relation is exactly the distinguished-triangle relation coming
  -- from the degree-zero triangle attached to the underlying short exact sequence.
  rw [modulePropertyK0Relations, AddSubgroup.closure_le]
  rintro _ ⟨S, rfl⟩
  rcases S with ⟨S, hS⟩
  change
    (FreeAbelianGroup.lift fun M : FiniteProjectiveModuleCat R ↦
      TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M))
      (FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) = 0
  simp only [FreeAbelianGroup.lift_apply_of, map_sub]
  simpa [finiteProjectiveModuleToPerfectDerivedTriangle, finiteProjectiveModuleToPerfectDerived,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    sub_eq_zero.mpr
      (TriangulatedK0.of_distinguished
        (finiteProjectiveModuleToPerfectDerivedTriangle R hS)
        (finiteProjectiveModuleToPerfectDerivedTriangle_distinguished (R := R) hS))

/-- The map `K₀(R) → K₀(D_{perf}(R))` sending `[M]` to the class of the degree-zero perfect
complex `M[0]`. -/
noncomputable def projectiveGrothendieckGroupToPerfectDerivedCategoryK0 :
    K₀ →+ TriangulatedK0 (DPerf R) :=
  ModulePropertyK0.lift R
    (fun M : FiniteProjectiveModuleCat R ↦
      TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M))
    (projectiveGrothendieckGroup_relations_le_ker_toPerfectDerivedCategoryK0 R)

/-- The degree-zero map sends the class of a finite projective module to the class of its
degree-zero perfect complex. -/
@[simp] theorem projectiveGrothendieckGroupToPerfectDerivedCategoryK0_apply_of
    (M : FiniteProjectiveModuleCat R) :
    projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R
        (projectiveGrothendieckGroupOf R M) =
      TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M) := by
  simpa [projectiveGrothendieckGroupToPerfectDerivedCategoryK0] using
    ModulePropertyK0.lift_of R
      (fun M : FiniteProjectiveModuleCat R ↦
        TriangulatedK0.of (finiteProjectiveModule_singleInPerfectDerived R M))
      (projectiveGrothendieckGroup_relations_le_ker_toPerfectDerivedCategoryK0 R)
      M

-- Proof sketch: on a generator `[M]` of `K₀(R)`, the composite sends `M` to `M[0]` and then
-- applies the Euler-characteristic map, which returns `[M]` because the complex has exactly one
-- nonzero term in degree `0`. The quotient presentation then gives the identity everywhere.
/-- The degree-zero map on `K₀` is a right inverse to the Euler-characteristic map. -/
theorem projectiveGrothendieckGroupToPerfectDerivedCategoryK0_rightInverse :
    Function.RightInverse
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R)
      (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R) := by
  -- Proof comment: descend to the free abelian group on generators and check the composite on a
  -- single class `[M]`; additivity then handles sums and negatives automatically.
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      simp
  | of M =>
      rw [projectiveGrothendieckGroupToPerfectDerivedCategoryK0_apply_of,
        perfectDerivedCategoryK0ToProjectiveGrothendieckGroup_apply_of,
        finiteProjectiveModule_singleInPerfectDerived_eulerCharacteristic]
      simp
  | neg z hz =>
      simpa using congrArg Neg.neg hz
  | add z₁ z₂ hz₁ hz₂ =>
      simp [map_add, hz₁, hz₂]

/-- Helper for Lemma 15.120.2: the derived object of a bounded finite-projective complex is a
perfect object. -/
private theorem q_obj_isPerfect_of_isBoundedFiniteProjective
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L] :
    DerivedCategory.IsPerfect (DerivedCategory.Q.obj L) := by
  -- Proof comment: the defining representative of `Q.obj L` is the complex `L` itself.
  exact ⟨L, Iso.refl _, hL⟩

/-- Helper for Lemma 15.120.2: the lower brutal truncation keeps a bounded finite-projective
representative inside the same source-faithful class of complexes. -/
private theorem isBoundedFiniteProjective_stupidTruncGE
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L] (p : ℤ) :
    CochainComplex.IsBoundedFiniteProjective
      ((L.stupidTrunc (ComplexShape.embeddingUpIntGE p) : Cpx)) := by
  rcases hL.bounded with ⟨a, b, hge, hle⟩
  refine ⟨⟨p, b, ?_, ?_⟩, ?_, ?_⟩
  · -- Proof comment: every degree below the cutoff vanishes by construction of the lower brutal
    -- truncation.
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact L.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE p) i
      (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hi)
  · -- Proof comment: above the inherited upper bound, retained terms agree with `L`, while the
    -- discarded terms are zero by construction.
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    by_cases hpi : p ≤ i
    · let hLi : CategoryTheory.Limits.IsZero (L.X i) := L.isZero_of_isStrictlyLE b i hi
      exact hLi.of_iso (L.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) hpi)
    · exact L.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE p) i
        (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using lt_of_not_ge hpi)
  · -- Proof comment: each retained term is canonically isomorphic to the corresponding term of
    -- `L`, and each discarded term is zero.
    intro i
    by_cases hpi : p ≤ i
    · exact
        Module.Finite.equiv
          ((L.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) hpi).toLinearEquiv.symm)
          (hL.finite i)
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((L.stupidTrunc (ComplexShape.embeddingUpIntGE p) : Cpx)).X i) :=
        L.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE p) i
          (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
            lt_of_not_ge hpi)
      exact
        Module.Finite.equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Finite R (0 : ModuleCat R))
  · -- Proof comment: the same retained-vs-zero dichotomy transports projectivity termwise.
    intro i
    by_cases hpi : p ≤ i
    · exact
        Module.Projective.of_equiv
          ((L.stupidTruncXIso (ComplexShape.embeddingUpIntGE p) hpi).toLinearEquiv.symm)
          (hL.projective i)
    · let hzero :
        CategoryTheory.Limits.IsZero
          (((L.stupidTrunc (ComplexShape.embeddingUpIntGE p) : Cpx)).X i) :=
        L.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE p) i
          (by simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using
            lt_of_not_ge hpi)
      exact
        Module.Projective.of_equiv hzero.isoZero.toLinearEquiv.symm
          (by infer_instance : Module.Projective R (0 : ModuleCat R))

/-- Helper for Lemma 15.120.2: after shifting a bounded finite-projective representative so that
its top degree is `0`, the shortened brutal left stage shifted back is again bounded
finite-projective. -/
private theorem shifted_brutal_stage_shift_back_isBoundedFiniteProjective
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L]
    {a b : ℤ} {n : ℕ}
    (hn : Int.toNat (b - a) = n + 1) :
    CochainComplex.IsBoundedFiniteProjective
      (((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx)) := by
  -- Proof comment: first truncate the shifted representative at the public brutal stage from
  -- Chapter 13, then shift the shortened complex back to the original indexing.
  letI : CochainComplex.IsBoundedFiniteProjective (L⟦b⟧) :=
    CochainComplex.isBoundedFiniteProjective_shift (R := R) L b
  letI :
      CochainComplex.IsBoundedFiniteProjective
        (shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n) :=
    isBoundedFiniteProjective_stupidTruncGE (R := R) (L := L⟦b⟧) (-((n : ℕ) : ℤ))
  simpa [shifted_brutal_left_stage] using
    (CochainComplex.isBoundedFiniteProjective_shift
      (R := R)
      (L := shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)
      (-b))

/-- Helper for Lemma 15.120.2: on the shortened interval `[a + 1, b]`, the shifted-back brutal
left stage has exactly the same terms as the original representative. -/
private noncomputable def shifted_brutal_stage_shift_back_x_iso
    {L : Cpx} {a b : ℤ} {n : ℕ}
    (hn : Int.toNat (b - a) = n + 1)
    {i : ℤ} (hi : a + 1 ≤ i) (hib : i ≤ b) :
    ((((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx)).X i) ≅ L.X i := by
  have hab : a ≤ b := by
    by_contra hab
    have hnonpos : b - a ≤ 0 := by
      omega
    rw [Int.toNat_of_nonpos hnonpos] at hn
    omega
  have hwidth : b - a = ((n + 1 : ℕ) : ℤ) := by
    rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
    exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
  have ha1 : a + 1 = b - (n : ℤ) := by
    omega
  have hi_stage : -((n : ℕ) : ℤ) ≤ i - b := by
    simpa [ha1] using hi
  have hi_nonneg : 0 ≤ i - b + (n : ℤ) := by
    omega
  let eShift :
      (((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx).X i) ≅
        (shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n).X (i - b) :=
    (shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n).shiftFunctorObjXIso
      (-b) i (i - b) (by omega)
  let eStage :
      (shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n).X (i - b) ≅
        (L⟦b⟧).X (i - b) :=
    (L⟦b⟧).stupidTruncXIso (ComplexShape.embeddingUpIntGE (-((n : ℕ) : ℤ))) (by
      refine Eq.symm ?_
      dsimp [ComplexShape.embeddingUpIntGE]
      rw [Int.toNat_of_nonneg hi_nonneg]
      omega)
  let eTerm :
      (L⟦b⟧).X (i - b) ≅ L.X i :=
    L.shiftFunctorObjXIso b (i - b) i (by omega)
  -- Proof comment: compare first with the shifted stage term, then with the corresponding term
  -- of the shifted original representative, and finally shift back to degree `i` of `L`.
  exact eShift ≪≫ eStage ≪≫ eTerm

/-- Helper for Lemma 15.120.2: after peeling off the leftmost term, the shifted-back brutal
stage is supported on the shortened interval `[a + 1, b]`. -/
private theorem shifted_brutal_stage_shift_back_strict_bounds
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L]
    {a b : ℤ} {n : ℕ}
    (hge : L.IsStrictlyGE a) (hle : L.IsStrictlyLE b)
    (hn : Int.toNat (b - a) = n + 1) :
    ((((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx)).IsStrictlyGE (a + 1)) ∧
      ((((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx)).IsStrictlyLE b) := by
  -- Proof comment: this is exactly the Chapter 13 support bookkeeping after shifting the
  -- representative to the interval `[-(n + 1), 0]` and then shifting the shorter stage back.
  have hKGE : (L⟦b⟧).IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := by
    simpa using
      shifted_representative_isStrictlyGE_left_endpoint
        (A := ModuleCat R) (L := L) (a := a) (b := b) (n := n) hn hge
  have hKLE : (L⟦b⟧).IsStrictlyLE 0 := by
    simpa using
      shifted_representative_isStrictlyLE_zero (A := ModuleCat R) (L := L) (b := b) hle
  have ha1 : a + 1 = b - (n : ℤ) := by
    have hab : a ≤ b := by
      by_contra hab
      have hnonpos : b - a ≤ 0 := by
        omega
      rw [Int.toNat_of_nonpos hnonpos] at hn
      omega
    have hwidth : b - a = ((n + 1 : ℕ) : ℤ) := by
      rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hab)]
      exact congrArg (fun m : ℕ ↦ (m : ℤ)) hn
    omega
  constructor
  · letI : (L⟦b⟧).IsStrictlyGE (-((n + 1 : ℕ) : ℤ)) := hKGE
    letI :
        (shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n).IsStrictlyGE
          (-((n : ℕ) : ℤ)) :=
      inferInstance
    simpa [ha1] using
      (CochainComplex.isStrictlyGE_shift
        (K := shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)
        (-((n : ℕ) : ℤ)) (-b) (a + 1) (by omega))
  · letI : (L⟦b⟧).IsStrictlyLE 0 := hKLE
    letI :
        (shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n).IsStrictlyLE 0 :=
      inferInstance
    simpa using
      (CochainComplex.isStrictlyLE_shift
        (K := shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)
        0 (-b) b (by omega))

/-- Helper for Lemma 15.120.2: a short exact sequence of bounded finite-projective complexes
induces the canonical distinguished triangle in `D_{perf}(R)`. -/
private theorem perfectDerivedTriangle_of_shortExact_distinguished
    {S : ShortComplex Cpx}
    [CochainComplex.IsBoundedFiniteProjective S.X₁]
    [CochainComplex.IsBoundedFiniteProjective S.X₂]
    [CochainComplex.IsBoundedFiniteProjective S.X₃]
    (hS : S.ShortExact) :
    Triangle.mk
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage (DerivedCategory.Q.map S.f))
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage (DerivedCategory.Q.map S.g))
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage
          (DerivedCategory.triangleOfSESδ hS ≫
            ((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).inv.app
              ⟨DerivedCategory.Q.obj S.X₁,
                q_obj_isPerfect_of_isBoundedFiniteProjective (R := R) S.X₁⟩)) ∈
      distTriang (DPerf R) := by
  -- Proof comment: forget the triangle to the ambient derived category, where it is exactly the
  -- canonical `triangleOfSES`; then transport distinguishedness back to `DPerf`.
  rw [← (ObjectProperty.ι (perfectObjectProperty (R := R))).map_distinguished_iff]
  change
    Triangle.mk
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).map
          ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage
            (DerivedCategory.Q.map S.f)))
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).map
          ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage
            (DerivedCategory.Q.map S.g)))
        ((ObjectProperty.ι (perfectObjectProperty (R := R))).map
            ((ObjectProperty.ι (perfectObjectProperty (R := R))).preimage
              (DerivedCategory.triangleOfSESδ hS ≫
                ((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).inv.app
                  ⟨DerivedCategory.Q.obj S.X₁,
                    q_obj_isPerfect_of_isBoundedFiniteProjective (R := R) S.X₁⟩)) ≫
          ((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).hom.app
            ⟨DerivedCategory.Q.obj S.X₁,
              q_obj_isPerfect_of_isBoundedFiniteProjective (R := R) S.X₁⟩) ∈
      distTriang (DerivedCategory (ModuleCat R))
  rw [(ObjectProperty.ι (perfectObjectProperty (R := R))).map_preimage]
  refine isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · simp
  · simp
  · simpa [Category.assoc] using
      congrArg
        (fun k ↦ DerivedCategory.triangleOfSESδ hS ≫ k)
        (((ObjectProperty.ι (perfectObjectProperty (R := R))).commShiftIso (1 : ℤ)).inv_hom_id_app
          ⟨DerivedCategory.Q.obj S.X₁,
            q_obj_isPerfect_of_isBoundedFiniteProjective (R := R) S.X₁⟩)

/-- Helper for Lemma 15.120.2: the zero object has trivial class in
`K₀(D_{perf}(R))`. -/
private theorem triangulatedK0_of_zero_eq :
    TriangulatedK0.of (0 : DPerf R) = 0 := by
  -- Proof comment: the contractible triangle on the zero object yields the relation
  -- `[0] = [0] + [0]`, and canceling one copy forces `[0] = 0`.
  have hK0 :
      TriangulatedK0.of (0 : DPerf R) =
        TriangulatedK0.of (0 : DPerf R) + TriangulatedK0.of (0 : DPerf R) := by
    simpa using
      (TriangulatedK0.of_distinguished
        (Triangle.mk (0 : (0 : DPerf R) ⟶ 0) (𝟙 (0 : DPerf R)) 0)
        (by simpa using contractible_distinguished₁ (0 : DPerf R)))
  have hZero :
      (0 : TriangulatedK0 (DPerf R)) = TriangulatedK0.of (0 : DPerf R) := by
    have hSub := congrArg
      (fun z : TriangulatedK0 (DPerf R) ↦ z - TriangulatedK0.of (0 : DPerf R))
      hK0
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hSub
  simpa using hZero.symm

/-- Helper for Lemma 15.120.2: isomorphic perfect objects determine the same `K₀`-class. -/
private theorem triangulatedK0_of_eq_of_iso
    {X Y : DPerf R} (e : X ≅ Y) :
    TriangulatedK0.of X = TriangulatedK0.of Y := by
  -- Proof comment: the zero-cone triangle on an isomorphism is distinguished, so its `K₀`
  -- relation reduces to `[Y] = [X] + [0]`, and the zero term vanishes.
  have hT :
      Triangle.mk e.hom (0 : Y ⟶ 0) 0 ∈ distTriang (DPerf R) := by
    exact
      (isIso_iff_zero_cone_triangle_distinguished (D := DPerf R) e.hom).1
        (by infer_instance)
  have hK0 :
      TriangulatedK0.of Y = TriangulatedK0.of X + TriangulatedK0.of (0 : DPerf R) := by
    simpa using TriangulatedK0.of_distinguished (Triangle.mk e.hom (0 : Y ⟶ 0) 0) hT
  simpa [triangulatedK0_of_zero_eq (R := R)] using hK0

/-- Helper for Lemma 15.120.2: shifting by one negates the `K₀`-class of a perfect object. -/
private theorem triangulatedK0_of_shift_one_eq_neg
    (X : DPerf R) :
    TriangulatedK0.of (X⟦(1 : ℤ)⟧) = -TriangulatedK0.of X := by
  -- TODO: use the contractible triangle `X ⟶ 0 ⟶ X[1]`.
  sorry

/-- Helper for Lemma 15.120.2: shifting by `-1` also negates the `K₀`-class of a perfect
object. -/
private theorem triangulatedK0_of_shift_neg_one_eq_neg
    (X : DPerf R) :
    TriangulatedK0.of (X⟦(-1 : ℤ)⟧) = -TriangulatedK0.of X := by
  -- TODO: deduce the `-1` statement from the `+1` statement via `shiftNegShift`.
  sorry

/-- Helper for Lemma 15.120.2: shifting a perfect object multiplies its `K₀`-class by the
canonical sign `(-1)^n`. -/
private theorem triangulatedK0_of_shift_eq_negOnePow_smul
    (X : DPerf R) (n : ℤ) :
    TriangulatedK0.of (X⟦n⟧) = n.negOnePow • TriangulatedK0.of X := by
  -- TODO: iterate the `±1` shift formulas by induction on `n`.
  sorry

/-- Helper for Lemma 15.120.2: a bounded finite-projective representative concentrated in degree
`a` already has the expected class in `K₀(D_{perf}(R))`. -/
private theorem single_degree_representative_class
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L]
    (a : ℤ) (hge : L.IsStrictlyGE a) (hle : L.IsStrictlyLE a) :
    projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R (L.eulerCharacteristic) =
      TriangulatedK0.of
        ⟨DerivedCategory.Q.obj L,
          q_obj_isPerfect_of_isBoundedFiniteProjective (R := R) L⟩ := by
  -- TODO: compare `L` with the shifted degree-zero single complex on `L.X a`, prove both
  -- represent the same Euler characteristic, and rewrite the resulting shift on `TriangulatedK0`.
  sorry

/-- Helper for Lemma 15.120.2: one brutal-stage step gives the required `K₀(D_{perf}(R))`
class relation between the full representative, the shortened stage, and the peeled singleton
term. -/
private theorem shifted_brutal_stage_step_class_relation
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L]
    {a b : ℤ} {n : ℕ}
    (hge : L.IsStrictlyGE a)
    (hn : Int.toNat (b - a) = n + 1) :
    TriangulatedK0.of
        ⟨DerivedCategory.Q.obj L,
          q_obj_isPerfect_of_isBoundedFiniteProjective (R := R) L⟩ =
      TriangulatedK0.of
          ⟨DerivedCategory.Q.obj
              (((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx)),
            q_obj_isPerfect_of_isBoundedFiniteProjective (R := R)
              (((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx))⟩ +
        a.negOnePow •
          TriangulatedK0.of
            (finiteProjectiveModule_singleInPerfectDerived R
              ⟨L.X a, ⟨hL.finite a, hL.projective a⟩⟩) := by
  -- TODO: build the shifted brutal-stage short exact sequence into a distinguished triangle in
  -- `DPerf R`, identify its middle term with `L` and its quotient with the shifted singleton
  -- `L.X a[a]`, then apply `TriangulatedK0.of_distinguished`.
  sorry

/-- Helper for Lemma 15.120.2: the same brutal-stage step gives the matching Euler-characteristic
relation in `K₀(R)`. -/
private theorem shifted_brutal_stage_step_euler_relation
    (L : Cpx) [hL : CochainComplex.IsBoundedFiniteProjective L]
    {a b : ℤ} {n : ℕ}
    (hge : L.IsStrictlyGE a)
    (hn : Int.toNat (b - a) = n + 1) :
    L.eulerCharacteristic =
      (((shifted_brutal_left_stage (A := ModuleCat R) (L⟦b⟧) n)⟦-b⟧ : Cpx)).eulerCharacteristic +
        a.negOnePow •
          projectiveGrothendieckGroupOf R
            ⟨L.X a, ⟨hL.finite a, hL.projective a⟩⟩ := by
  -- TODO: use the same brutal-stage distinguished triangle as in the class relation and apply
  -- `DPerf.eulerCharacteristic_add_of_distinguishedTriangle`, then rewrite the quotient term by
  -- `singleFunctor_obj_iso_shifted_single0_in_DPerf` and the shift formula.
  sorry

/-- Helper for Lemma 15.120.2: the `K₀(R) → K₀(D_{perf}(R))` map sends the Euler characteristic
of a bounded finite-projective representative to the class of the represented perfect object. -/
private theorem projectiveGrothendieckGroupToPerfectDerivedCategoryK0_of_perfectRepresentative
    (K : DPerf R) (L : Cpx) (e : K.obj ≅ DerivedCategory.Q.obj L)
    [hL : CochainComplex.IsBoundedFiniteProjective L] :
    projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R (L.eulerCharacteristic) =
      TriangulatedK0.of K := by
  -- TODO: run the width induction on the support interval of `L`. The width-zero case is
  -- `single_degree_representative_class`; the successor step should combine
  -- `shifted_brutal_stage_step_euler_relation` with `shifted_brutal_stage_step_class_relation`.
  sorry

-- Proof sketch: represent a perfect object by a bounded finite-projective complex. The stupid
-- truncation triangles express its `K₀(D_{perf}(R))`-class as the alternating sum of the degree-
-- zero classes of its terms, exactly matching the chosen Euler-characteristic class in `K₀(R)`.
/-- The degree-zero map `K₀(R) → K₀(D_{perf}(R))` is a left inverse to the Euler-characteristic
comparison map. -/
theorem projectiveGrothendieckGroupToPerfectDerivedCategoryK0_leftInverse :
    Function.LeftInverse
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R)
      (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R) := by
  -- Route correction: the earlier blocked route tried to finish directly from `eulerCharacteristic_spec`.
  -- The correct source-faithful reduction is to a bounded finite-projective representative and its
  -- stupid-truncation decomposition, isolated in the helper below.
  intro x
  refine Quotient.inductionOn x ?_
  intro z
  induction z using FreeAbelianGroup.induction_on with
  | zero =>
      simp
  | of K =>
      rcases DPerf.eulerCharacteristic_spec K with ⟨L, e, hL, rfl⟩
      letI : CochainComplex.IsBoundedFiniteProjective L := hL
      simpa [TriangulatedK0.of] using
        projectiveGrothendieckGroupToPerfectDerivedCategoryK0_of_perfectRepresentative
          (R := R) K L e
  | neg z hz =>
      simpa using congrArg Neg.neg hz
  | add z₁ z₂ hz₁ hz₂ =>
      simp [map_add, hz₁, hz₂]

-- Proof sketch: the previous two theorems exhibit explicit two-sided inverses between the
-- comparison map `K₀(D_{perf}(R)) → K₀(R)` and the degree-zero map `K₀(R) → K₀(D_{perf}(R))`,
-- so the comparison map is bijective.
/-- Lemma 15.120.2: the comparison map `c : K₀(D_{perf}(R)) → K₀(R)` from the perfect derived
category is bijective, hence identifies `K₀(D_{perf}(R))` with `K₀(R)`. -/
theorem perfectDerivedCategoryK0ToProjectiveGrothendieckGroup_bijective :
    Function.Bijective (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R) := by
  refine ⟨?_, ?_⟩
  · exact Function.LeftInverse.injective
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0_leftInverse R)
  · exact Function.RightInverse.surjective
      (projectiveGrothendieckGroupToPerfectDerivedCategoryK0_rightInverse R)

/-- The canonical additive equivalence between `K₀(D_{perf}(R))` and `K₀(R)` induced by the
comparison map. -/
noncomputable def perfectDerivedCategoryK0Equiv :
    TriangulatedK0 (DPerf R) ≃+ K₀ :=
  { toFun := perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R
    invFun := projectiveGrothendieckGroupToPerfectDerivedCategoryK0 R
    left_inv := projectiveGrothendieckGroupToPerfectDerivedCategoryK0_leftInverse R
    right_inv := projectiveGrothendieckGroupToPerfectDerivedCategoryK0_rightInverse R
    map_add' := (perfectDerivedCategoryK0ToProjectiveGrothendieckGroup R).map_add }

end
