import Mathlib
import StacksProject_2024.Chap12.Remark_12_29_2
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_59_14
import StacksProject_2024.Chap15.Lemma_15_67_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open scoped DerivedTensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R' R : Type u} [CommRing R'] [CommRing R] [Algebra R' R]

local notation "DModRPrime" => DerivedCategory (ModuleCat R')
local notation "I" => RingHom.ker (algebraMap R' R)
local notation "HRPrime" => DerivedCategory.homologyFunctor (ModuleCat R')

/-- Helper for Lemma 15.67.20: restricting a degree-zero module object along a ring map commutes
with the degree-zero embedding into the derived category. -/
noncomputable def restrictScalars_single0_iso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (M : ModuleCat B) :
    ((ModuleCat.restrictScalars f).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor (ModuleCat B) (0 : ℤ)).obj M)) ≅
      (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        ((ModuleCat.restrictScalars f).obj M) :=
  -- Proof comment: compute derived restriction on a strict single complex and then normalize it
  -- back to the canonical degree-zero derived object.
  ((ModuleCat.restrictScalars f).mapDerivedCategory).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat B) (0 : ℤ)).app M) ≪≫
    (ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor (ModuleCat B) (0 : ℤ)).obj M) ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapCochainComplexSingleFunctor
          (ModuleCat.restrictScalars f)
          (0 : ℤ)).app M) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat A) (0 : ℤ)).app
      ((ModuleCat.restrictScalars f).obj M)).symm

/-- Helper for Lemma 15.67.20: restriction of scalars is exact, hence preserves finite limits on
module categories. -/
local instance restrictScalars_preservesFiniteLimits
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Limits.PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) :=
  ((exactFunctor_iff (ModuleCat.restrictScalars.{u} f)).1 (restrictScalars_exact f)).1

/-- Helper for Lemma 15.67.20: if a module becomes zero after restricting scalars, then it was
already zero. -/
lemma isZero_of_restrictScalars_obj
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (M : ModuleCat B)
    (hM : Limits.IsZero ((ModuleCat.restrictScalars f).obj M)) :
    Limits.IsZero M := by
  -- Proof comment: restriction of scalars keeps the underlying additive group unchanged, so zero
  -- objects reflect along the identity-on-carriers forgetful step.
  letI : Subsingleton ↑((ModuleCat.restrictScalars f).obj M) :=
    ModuleCat.subsingleton_of_isZero hM
  have hsub : Subsingleton ↑M := by
    simpa using
      (inferInstance : Subsingleton ↑((ModuleCat.restrictScalars f).obj M))
  letI : Subsingleton ↑M := hsub
  exact ModuleCat.isZero_of_subsingleton M

/-- Helper for Lemma 15.67.20: homology commutes with restriction of scalars on derived module
categories. -/
noncomputable def homology_restrictScalars_iso
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (L : DerivedCategory (ModuleCat B)) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat A) i).obj
        (((ModuleCat.restrictScalars f).mapDerivedCategory).obj L) ≅
      (ModuleCat.restrictScalars f).obj
        ((DerivedCategory.homologyFunctor (ModuleCat B) i).obj L) := by
  let K := DerivedCategory.Q.objPreimage L
  let FK := ((ModuleCat.restrictScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let eB :
      (DerivedCategory.homologyFunctor (ModuleCat B) i).obj L ≅ K.homology i :=
    ((DerivedCategory.homologyFunctor (ModuleCat B) i).mapIso
      (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat B) i).app K
  -- Proof comment: choose a strict complex model for `L`, compare homology before and after
  -- restriction of scalars on that model, and then transport back to the derived category.
  exact
    (DerivedCategory.homologyFunctor (ModuleCat A) i).mapIso
        ((((ModuleCat.restrictScalars f).mapDerivedCategory).mapIso
            (DerivedCategory.Q.objObjPreimageIso L)).symm ≪≫
          ((ModuleCat.restrictScalars f).mapDerivedCategoryFactors.app K)) ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat A) i).app FK ≪≫
      (K.sc i).mapHomologyIso (ModuleCat.restrictScalars f) ≪≫
      (ModuleCat.restrictScalars f).mapIso eB.symm

/- Domain-style sampling for Lemma 15.67.20:
- primary domain: tor-amplitude in derived categories under derived scalar extension across a
  nilpotent thickening;
- sampled owner declarations:
  `HasTorAmplitudeIn`,
  `derivedTensorWithAlgebra`,
  `DerivedTensorWithAlgebra` notation `⊗[R']^L[R]`,
  `hasTorAmplitudeIn_derivedTensorWithAlgebra`;
- best owner abstraction: the source-facing statement is an equivalence on the chapter owner
  predicate `HasTorAmplitudeIn` before and after applying the canonical base-change owner
  `derivedTensorWithAlgebra (algebraMap R' R)`;
- primitive vs. derived:
  primitive data are the nilpotent thickening hypotheses on `R' → R`, the derived object
  `K' : D(R')`, and the interval bounds `a, b`;
  the base-changed object `K' ⊗[R']^L[R]` is derived API through the existing scalar-extension
  owner, so this file should depend directly on the owner file `15_60_1_1` rather than on the
  later change-of-rings bridge in `Lemma_15_60_1`;
- source/core/bridge triage:
  `source-facing`: tor-amplitude is equivalent before and after base change along a surjective map
    with nilpotent kernel;
  `core/canonical`: `HasTorAmplitudeIn` and `derivedTensorWithAlgebra`;
  `bridge/view`: the notation `K' ⊗[R']^L[R]` for applying the owner functor to `K'`. -/

-- Proof sketch: the forward implication is Lemma `15.67.13`, since tor-amplitude is preserved by
-- derived base change. For the converse, induct on the nilpotence exponent of
-- `RingHom.ker (algebraMap R' R)` and use the distinguished triangle attached to
-- `0 → I M' → M' → M' / I M' → 0` for an arbitrary `R'`-module `M'`, reducing first to the case
-- where the kernel acts trivially so that `M'` descends to an `R`-module.
/-- Helper for Lemma 15.67.20: if the kernel ideal acts trivially on a module, then that module
is canonically a module over the quotient ring `R' ⧸ ker(R' → R)`. -/
lemma ker_isTorsionBySet_of_smul_top_eq_bot
    (M' : ModuleCat R')
    (hkill : I • (⊤ : Submodule R' M') = ⊥) :
    Module.IsTorsionBySet R' M' I := by
  have hiff :
      I • (⊤ : Submodule R' M') = ⊥ ↔ Module.IsTorsionBySet R' M' I := by
    rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top,
      Module.isTorsionBySet_iff_subset_annihilator]
    rfl
  -- Proof comment: the source hypothesis `I • M' = 0` is exactly the annihilator-based quotient
  -- module criterion from the torsion-by-set API.
  exact hiff.mp hkill

/-- Helper for Lemma 15.67.20: if `ker(R' → R)` kills `M'`, then `M'` descends to a concrete
`R`-module on the same carrier. -/
noncomputable abbrev descended_module_of_ker_smul_eq_zero
    (hsurj : Function.Surjective (algebraMap R' R))
    (M' : ModuleCat R')
    (hkill : I • (⊤ : Submodule R' M') = ⊥) :
    ModuleCat R :=
  let htors : Module.IsTorsionBySet R' M' I :=
    ker_isTorsionBySet_of_smul_top_eq_bot (R' := R') (R := R) M' hkill
  let e : R' ⧸ I ≃+* R :=
    RingHom.quotientKerEquivOfSurjective hsurj
  let _ : Module (R' ⧸ I) M' := htors.module
  let _ : Module R M' := Module.compHom M' e.symm.toRingHom
  ModuleCat.of R M'

/-- Helper for Lemma 15.67.20: the quotient-kernel equivalence for a surjective ring map sends
the quotient class of `r` to the image of `r`. -/
lemma quotientKerEquivOfSurjective_algebraMap_eq_mk
    (hsurj : Function.Surjective (algebraMap R' R))
    (r : R') :
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R' R) hsurj)
      (Ideal.Quotient.mk I r) =
      (algebraMap R' R) r := by
  -- Proof comment: this is the defining computation rule of
  -- `RingHom.quotientKerEquivOfSurjective` on quotient representatives.
  simp [RingHom.quotientKerEquivOfSurjective]

/-- Helper for Lemma 15.67.20: the inverse quotient-kernel equivalence recovers the canonical
quotient class of a base element. -/
lemma quotientKerEquivOfSurjective_symm_algebraMap_eq_mk
    (hsurj : Function.Surjective (algebraMap R' R))
    (r : R') :
    (RingHom.quotientKerEquivOfSurjective (f := algebraMap R' R) hsurj).symm
      ((algebraMap R' R) r) =
      Ideal.Quotient.mk I r := by
  -- Proof comment: rewrite the target through the forward computation rule and then cancel the
  -- quotient-kernel equivalence with its inverse.
  rw [← quotientKerEquivOfSurjective_algebraMap_eq_mk (R' := R') (R := R) hsurj r]
  exact (RingHom.quotientKerEquivOfSurjective (f := algebraMap R' R) hsurj).symm_apply_apply _

/-- Helper for Lemma 15.67.20: after descending a module killed by the kernel ideal to `R`,
restricting scalars recovers the original `R'`-module by the identity map on the carrier. -/
noncomputable def restrictScalars_descended_module_of_ker_smul_eq_zero_iso
    (hsurj : Function.Surjective (algebraMap R' R))
    (M' : ModuleCat R')
    (hkill : I • (⊤ : Submodule R' M') = ⊥) :
    ((ModuleCat.restrictScalars (algebraMap R' R)).obj
      (descended_module_of_ker_smul_eq_zero (R' := R') (R := R) hsurj M' hkill)) ≅ M' := by
  let htors : Module.IsTorsionBySet R' M' I :=
    ker_isTorsionBySet_of_smul_top_eq_bot (R' := R') (R := R) M' hkill
  let e : R' ⧸ I ≃+* R :=
    RingHom.quotientKerEquivOfSurjective (f := algebraMap R' R) hsurj
  let _ : Module (R' ⧸ I) M' := htors.module
  let eLin :
      ↑(((ModuleCat.restrictScalars (algebraMap R' R)).obj
        (descended_module_of_ker_smul_eq_zero (R' := R') (R := R) hsurj M' hkill))) ≃ₗ[R'] ↑M' :=
    { __ := AddEquiv.refl _
      map_smul' := by
        intro r m
        let m' : M' := show M' from m
        -- Proof comment: unfold the descended scalar action through the inverse quotient-kernel
        -- equivalence, then replace that quotient class by `Ideal.Quotient.mk I r`.
        change ((e.symm ((algebraMap R' R) r) : R' ⧸ I) • m') = r • m'
        rw [quotientKerEquivOfSurjective_symm_algebraMap_eq_mk (R' := R') (R := R) hsurj r]
        exact Module.IsTorsionBySet.mk_smul htors r m' }
  -- Proof comment: the underlying carrier is unchanged, so the identity linear equivalence gives
  -- the required module isomorphism after the scalar-action check above.
  exact eLin.toModuleIso

/-- Helper for Lemma 15.67.20: on a genuine `R`-module, the descended scalar action coming from
the quotient presentation agrees with the original `R`-action elementwise. -/
lemma descended_module_of_restrictScalars_smul_eq
    (hsurj : Function.Surjective (algebraMap R' R))
    (M : ModuleCat R)
    (hkill :
      I • (⊤ : Submodule R' ((ModuleCat.restrictScalars (algebraMap R' R)).obj M)) = ⊥)
    (r : R)
    (m :
      descended_module_of_ker_smul_eq_zero
        (R' := R') (R := R) hsurj
        ((ModuleCat.restrictScalars (algebraMap R' R)).obj M)
        hkill) :
    (show M from r • m) = r • (show M from m) := by
  let M' : ModuleCat R' := (ModuleCat.restrictScalars (algebraMap R' R)).obj M
  let htors : Module.IsTorsionBySet R' M' I :=
    ker_isTorsionBySet_of_smul_top_eq_bot (R' := R') (R := R) M' hkill
  let e : R' ⧸ I ≃+* R :=
    RingHom.quotientKerEquivOfSurjective (f := algebraMap R' R) hsurj
  let _ : Module (R' ⧸ I) M' := htors.module
  classical
  rcases hsurj r with ⟨r', rfl⟩
  let m' : M' := show M' from m
  -- Proof comment: choose a lift `r'` of the target scalar, rewrite the descended action through
  -- the quotient-kernel equivalence, and then collapse it to the restricted `R'`-action.
  change ((e.symm ((algebraMap R' R) r') : R' ⧸ I) • m') = r' • m'
  rw [quotientKerEquivOfSurjective_symm_algebraMap_eq_mk
    (R' := R') (R := R) hsurj r']
  exact Module.IsTorsionBySet.mk_smul htors r' m'

/-- Helper for Lemma 15.67.20: descending a restricted `R`-module along the quotient presentation
recovers the original `R`-module by the identity map on the carrier. -/
noncomputable def descended_module_of_restrictScalars_iso
    (hsurj : Function.Surjective (algebraMap R' R))
    (M : ModuleCat R)
    (hkill :
      I • (⊤ : Submodule R' ((ModuleCat.restrictScalars (algebraMap R' R)).obj M)) = ⊥) :
    descended_module_of_ker_smul_eq_zero
        (R' := R') (R := R) hsurj
        ((ModuleCat.restrictScalars (algebraMap R' R)).obj M)
        hkill ≅
      M := by
  let eLin :
      ↑(descended_module_of_ker_smul_eq_zero
        (R' := R') (R := R) hsurj
        ((ModuleCat.restrictScalars (algebraMap R' R)).obj M)
        hkill) ≃ₗ[R] ↑M :=
    { __ := AddEquiv.refl _
      map_smul' :=
        descended_module_of_restrictScalars_smul_eq
          (R' := R') (R := R) hsurj M hkill }
  -- Proof comment: once the scalar actions are identified, the identity map on the carrier is an
  -- honest `R`-linear equivalence and hence a module isomorphism.
  exact eLin.toModuleIso

/-- Helper for Lemma 15.67.20: in the kernel-trivial case, the source-test homology identifies
with the restricted homology of the descended `R`-linear test object. -/
noncomputable def base_case_test_homology_iso_of_ker_smul_eq_zero
    (hsurj : Function.Surjective (algebraMap R' R))
    (K' : DModRPrime) (M' : ModuleCat R')
    (hkill : I • (⊤ : Submodule R' M') = ⊥)
    (i : ℤ) :
    ((HRPrime i).obj
      (K' ⊗[R']^L
        ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M'))) ≅
      (ModuleCat.restrictScalars (algebraMap R' R)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          (((K' ⊗[R']^L[R]) ⊗[R]^L
            ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj
              (descended_module_of_ker_smul_eq_zero
                (R' := R') (R := R) hsurj M' hkill))))) := by
  -- Route correction: export only the homology-level comparison needed by the proof and keep the
  -- heavier derived-object transport internal to this helper.
  -- TODO(Lemma 15.67.20): rebuild the kernel-trivial comparison by combining the restriction
  -- tensor-product comparison, the descended-module identification for `M'`, the regular
  -- `R[0]` tensor-unit comparison, and the iterated-vs-direct scalar-extension comparison before
  -- applying `homology_restrictScalars_iso`.
  sorry

/-- Helper for Lemma 15.67.20: the kernel-trivial base case of the source induction. -/
lemma isZero_homology_of_test_object_of_ker_smul_eq_zero
    (hsurj : Function.Surjective (algebraMap R' R))
    (K' : DModRPrime) {a b i : ℤ}
    (hK : HasTorAmplitudeIn (K' ⊗[R']^L[R]) a b)
    (M' : ModuleCat R')
    (hi : i ∉ Set.Icc a b)
    (hkill : I • (⊤ : Submodule R' M') = ⊥) :
    IsZero ((HRPrime i).obj
      (K' ⊗[R']^L
        ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M'))) := by
  let M : ModuleCat R :=
    descended_module_of_ker_smul_eq_zero (R' := R') (R := R) hsurj M' hkill
  have hbase :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          ((K' ⊗[R']^L[R]) ⊗[R]^L
            ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))) :=
    hK M i hi
  have hbase_restrict :
      IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat R') i).obj
          ((ModuleCat.restrictScalars (algebraMap R' R)).mapDerivedCategory.obj
            (((K' ⊗[R']^L[R]) ⊗[R]^L
              ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))))) := by
    -- Proof comment: first commute homology with restriction of scalars, then preserve the zero
    -- homology object along the exact restriction functor.
    have hrestricted_homology :
        IsZero
          ((ModuleCat.restrictScalars (algebraMap R' R)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
              ((K' ⊗[R']^L[R]) ⊗[R]^L
                ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)))) :=
      (ModuleCat.restrictScalars (algebraMap R' R)).map_isZero hbase
    exact
      (homology_restrictScalars_iso
        (f := algebraMap R' R)
        (((K' ⊗[R']^L[R]) ⊗[R]^L
          ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))) i).isZero_iff.2
        hrestricted_homology
  -- Proof comment: transport the restricted zero homology along the specialized descended-module
  -- comparison to the original source test object.
  have hbase_restrict_homology :
      IsZero
        ((ModuleCat.restrictScalars (algebraMap R' R)).obj
          ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
            ((K' ⊗[R']^L[R]) ⊗[R]^L
              ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)))) :=
    (homology_restrictScalars_iso
      (f := algebraMap R' R)
      (((K' ⊗[R']^L[R]) ⊗[R]^L
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M))) i).isZero_iff.1
      hbase_restrict
  exact
    (base_case_test_homology_iso_of_ker_smul_eq_zero
      (R' := R') (R := R) hsurj K' M' hkill i).isZero_iff.2
      hbase_restrict_homology

/-- Helper for Lemma 15.67.20: if `I^(t + 1)` kills `M'`, then `I^t` kills the submodule `I M'`
appearing in the induction short exact sequence. -/
lemma pow_smul_top_eq_bot_on_smul_submodule
    (M' : ModuleCat R') (t : ℕ)
    (hpow : I ^ (t + 1) • (⊤ : Submodule R' M') = ⊥) :
    I ^ t • (I • (⊤ : Submodule R' M')) = ⊥ := by
  -- Proof comment: reassociate the ideal action once and then rewrite the product of ideals as the
  -- successor power.
  rw [pow_succ] at hpow
  simpa [Submodule.mul_smul] using hpow

/-- Helper for Lemma 15.67.20: the quotient `M' / I M'` is killed by `I`, exactly as in the
source induction. -/
lemma ker_smul_top_eq_bot_on_quotient
    (M' : ModuleCat R') :
    I • (⊤ : Submodule R' (M' ⧸ I • (⊤ : Submodule R' M'))) = ⊥ := by
  -- Proof comment: the quotient is literally the module killed by `I`, so this is the standard
  -- annihilator-to-smul-top reformulation.
  have hann : I ≤ Module.annihilator R' (M' ⧸ I • (⊤ : Submodule R' M')) := by
    exact (Module.isTorsionBySet_iff_subset_annihilator R' (M' ⧸ I • (⊤ : Submodule R' M'))).mp <| by
      rw [Module.isTorsionBySet_quotient_iff]
      intro y r hr
      change r • y ∈ I • (⊤ : Submodule R' M')
      exact Submodule.smul_mem_smul hr (show y ∈ (⊤ : Submodule R' M') by simp)
  refine (Submodule.le_annihilator_iff).mp ?_
  simpa [Submodule.annihilator_top] using hann

/-- Helper for Lemma 15.67.20: if a fixed power of the kernel kills `M'`, then the source
induction shows the test object has no homology outside `[a, b]`. -/
lemma isZero_homology_of_test_object_of_pow_smul_eq_bot
    (hsurj : Function.Surjective (algebraMap R' R))
    (K' : DModRPrime) {a b i : ℤ}
    (hK : HasTorAmplitudeIn (K' ⊗[R']^L[R]) a b)
    (M' : ModuleCat R') (t : ℕ)
    (hpow : I ^ (t + 1) • (⊤ : Submodule R' M') = ⊥)
    (hi : i ∉ Set.Icc a b) :
    IsZero ((HRPrime i).obj
      (K' ⊗[R']^L
        ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M'))) := by
  -- Route correction: the source induction structure is now isolated here. The remaining work is
  -- purely the `triangleOfSES` packaging over `0 → I M' → M' → M' / I M' → 0`, using the two
  -- already-proved side lemmas above and the kernel-trivial base case.
  sorry

/-- Helper for Lemma 15.67.20: a nilpotent ideal kills every module after some power. -/
lemma exists_pow_smul_top_eq_bot_of_isNilpotent
    (hker : IsNilpotent I) (M' : ModuleCat R') :
    ∃ n : ℕ, I ^ n • (⊤ : Submodule R' M') = ⊥ := by
  rcases hker with ⟨n, hn⟩
  -- Proof comment: once the ideal power itself is zero, its action on any module is zero.
  refine ⟨n, ?_⟩
  rw [hn]
  simp

/-- Helper for Lemma 15.67.20: in a distinguished triangle, if the outer degree-`i` homology
objects vanish, then the middle degree-`i` homology object also vanishes. -/
lemma isZero_homology_obj₂_of_distinguished_triangle_of_outer_zeros
    (T : Triangle DModRPrime) (hT : T ∈ distTriang DModRPrime) (i : ℤ)
    (h₁ : Limits.IsZero ((HRPrime i).obj T.obj₁))
    (h₃ : Limits.IsZero ((HRPrime i).obj T.obj₃)) :
    Limits.IsZero ((HRPrime i).obj T.obj₂) := by
  have hmor₂_zero : (HRPrime i).map T.mor₂ = 0 := by
    exact h₃.eq_of_tgt _ _
  have hmor₁_epi : Epi ((HRPrime i).map T.mor₁) := by
    -- Proof comment: exactness makes the first homology map epi once the next homology object is
    -- already zero.
    exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).2 hmor₂_zero
  -- Proof comment: an epimorphism out of a zero homology object forces the middle homology
  -- object to vanish as well.
  exact CategoryTheory.Limits.IsZero.of_epi ((HRPrime i).map T.mor₁) h₁

/-- Lemma 15.67.20: for a surjective ring map `R' → R` with nilpotent kernel, an object
`K'` of `D(R')` has tor-amplitude in `[a, b]` if and only if its derived base change
`K' \otimes_{R'}^{\mathbf L} R` has tor-amplitude in `[a, b]` in `D(R)`. -/
@[stacks 0H75]
theorem hasTorAmplitudeIn_derivedTensorWithAlgebra_iff_of_surjective_of_nilpotent_ker
    (hsurj : Function.Surjective (algebraMap R' R))
    (hker : IsNilpotent (RingHom.ker (algebraMap R' R)))
    (K' : DModRPrime) (a b : ℤ) :
    HasTorAmplitudeIn (K' ⊗[R']^L[R]) a b ↔
      HasTorAmplitudeIn K' a b := by
  constructor
  · intro hK
    intro M' i hi
    rcases exists_pow_smul_top_eq_bot_of_isNilpotent
        (R' := R') (R := R) hker M' with ⟨n, hn⟩
    cases n with
    | zero =>
        -- Proof comment: a nilpotent exponent `0` means the whole module is zero, so the test
        -- object vanishes for the trivial reason.
        have htop : (⊤ : Submodule R' M') = ⊥ := by
          simpa using hn
        have hsub : Subsingleton ↑M' := by
          refine ⟨fun x y ↦ ?_⟩
          have hx : x = 0 := by
            have hxmem : x ∈ (⊥ : Submodule R' M') := by
              rw [← htop]
              simp
            simpa using hxmem
          have hy : y = 0 := by
            have hymem : y ∈ (⊥ : Submodule R' M') := by
              rw [← htop]
              simp
            simpa using hymem
          simp [hx, hy]
        letI : Subsingleton ↑M' := hsub
        have hMzero : IsZero M' := ModuleCat.isZero_of_subsingleton M'
        have hsingle :
            IsZero
              ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M') :=
          Functor.map_isZero (DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)) hMzero
        letI : (derivedTensorProduct K').CommShift ℤ :=
          derivedTensorProduct_commShift K'
        letI : (derivedTensorProduct K').IsTriangulated :=
          derivedTensorProduct_isTriangulated K'
        letI : (derivedTensorProduct K').Additive := inferInstance
        letI : (derivedTensorProduct K').PreservesZeroMorphisms :=
          Functor.preservesZeroMorphisms_of_additive _
        have htest_comm :
            IsZero
              (((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M') ⊗[R']^L K') :=
          (derivedTensorProduct K').map_isZero hsingle
        have htest :
            IsZero
              (K' ⊗[R']^L
                ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M')) :=
          htest_comm.of_iso
            (derivedTensorProduct_comm
              K'
              ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M'))
        exact (HRPrime i).map_isZero htest
    | succ t =>
        -- Proof comment: choose the nilpotence exponent promised by `hker` and run the source
        -- induction on `t`.
        exact
          isZero_homology_of_test_object_of_pow_smul_eq_bot
            (R' := R') (R := R) hsurj K' hK M' t hn hi
  · intro hK
    intro M i hi
    let M' : ModuleCat R' := (ModuleCat.restrictScalars (algebraMap R' R)).obj M
    have hkill :
        I • (⊤ : Submodule R' M') = ⊥ := by
      have hann : I ≤ Module.annihilator R' M' := by
        intro r hr
        rw [Module.mem_annihilator]
        intro x
        change ((algebraMap R' R) r) • x = 0
        have hr0 : (algebraMap R' R) r = 0 := hr
        simpa [hr0]
      refine (Submodule.le_annihilator_iff).mp ?_
      simpa [Submodule.annihilator_top] using hann
    let Mdesc : ModuleCat R :=
      descended_module_of_ker_smul_eq_zero (R' := R') (R := R) hsurj M' hkill
    have eM : Mdesc ≅ M :=
      descended_module_of_restrictScalars_iso (R' := R') (R := R) hsurj M hkill
    have hsource :
        IsZero
          ((HRPrime i).obj
            (K' ⊗[R']^L
              ((DerivedCategory.singleFunctor (ModuleCat R') (0 : ℤ)).obj M'))) :=
      hK M' i hi
    have hrestricted_desc :
        IsZero
          ((ModuleCat.restrictScalars (algebraMap R' R)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
              (((K' ⊗[R']^L[R]) ⊗[R]^L
                ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj Mdesc))))) :=
      (base_case_test_homology_iso_of_ker_smul_eq_zero
        (R' := R') (R := R) hsurj K' M' hkill i).isZero_iff.1 hsource
    let Kbase : DerivedCategory (ModuleCat R) := K' ⊗[R']^L[R]
    let eTest :
        (Kbase ⊗[R]^L ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)) ≅
          (Kbase ⊗[R]^L ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj Mdesc)) :=
      (derivedCategory_tensorObj_iso_derivedTensorProduct
        Kbase
        ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)).symm ≪≫
        asIso (Kbase ◁
          ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).mapIso eM.symm).hom) ≪≫
        (derivedCategory_tensorObj_iso_derivedTensorProduct
          Kbase
          ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj Mdesc))
    have hrestricted :
        IsZero
          ((ModuleCat.restrictScalars (algebraMap R' R)).obj
            ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
              (Kbase ⊗[R]^L
                ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)))) := by
      -- Proof comment: replace the descended test module by the original `R`-module through the
      -- identity-on-carriers descent isomorphism.
      exact
        hrestricted_desc.of_iso
          ((ModuleCat.restrictScalars (algebraMap R' R)).mapIso
            ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso eTest))
    -- Proof comment: restriction of scalars reflects zero objects on modules, so the vanishing on
    -- the restricted homology module implies vanishing of the `R`-linear homology itself.
    exact
      isZero_of_restrictScalars_obj
        (algebraMap R' R)
        ((DerivedCategory.homologyFunctor (ModuleCat R) i).obj
          (Kbase ⊗[R]^L
            ((DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)))
        hrestricted

end

end CategoryTheory
