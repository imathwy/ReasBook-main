import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import StacksProject_2024.stacks_project.Chap15.«15_6_3_1»
import StacksProject_2024.stacks_project.Chap15.Lemma_15_5_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_6_4
import StacksProject_2024.stacks_project.Chap15.«15_91_16_1»
import StacksProject_2024.stacks_project.Chap15.«15_91_16_2»
import StacksProject_2024.stacks_project.Chap15.«15_91_16_3»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped IdealPowerTorsion
open scoped TensorProduct

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable (f : R)

/-- Helper for Theorem 15.91.16: the localization map from `R_f` to the overlap ring `R'_f`
appearing in the single-element Beauville-Laszlo square. -/
private abbrev awayMapToOverlap :
    Localization.Away f →+* Localization.Away (algebraMap R R' f) :=
  Localization.awayMap (algebraMap R R') f

local notation "BLPullback" =>
  CategoricalPullback
    (ModuleCat.extendScalars (algebraMap R' (Localization.Away (algebraMap R R' f))))
    (ModuleCat.extendScalars (awayMapToOverlap (R := R) (R' := R') f))

variable (R') in
/-- The full subcategory of `ModuleCat R` consisting of modules glueable for the
Beauville-Laszlo pair `(R → R', f)`. -/
abbrev beauvilleLaszloGlueableProperty (f : R) : ObjectProperty (ModuleCat R) :=
  fun M ↦ (beauvilleLaszloModuleCechSequence R' M f).ShortExact

local notation "BLGlueableModuleCat" =>
  (beauvilleLaszloGlueableProperty R' f).FullSubcategory

/-- Helper for Theorem 15.91.16: the single-element Beauville-Laszlo base-change functor, viewed
through the generic pullback owner from the earlier categorical API. -/
private noncomputable abbrev beauvilleLaszloBaseChangeFunctor :
    ModuleCat R ⥤ BLPullback (R := R) (R' := R') f :=
  moduleCatBaseChangeToCategoricalPullback
    (algebraMap R' (Localization.Away (algebraMap R R' f)))
    (awayMapToOverlap (R := R) (R' := R') f)
    (algebraMap R R')
    (algebraMap R (Localization.Away f))
    (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)

/-- Helper for Theorem 15.91.16: the generic pullback right adjoint specialized to the
single-element Beauville-Laszlo square. -/
private noncomputable abbrev beauvilleLaszloRightAdjointFunctor :
    BLPullback (R := R) (R' := R') f ⥤ ModuleCat R :=
  module_tensor_pullback_right_adjoint
    (algebraMap R R')
    (algebraMap R (Localization.Away f))
    (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)

/-- Helper for Theorem 15.91.16: the generic pullback right adjoint object is the kernel module
`H⁰(X)` from `15.91.16.1`. -/
private theorem beauvilleLaszloGlueingH0_eq_rightAdjoint_obj
    (X : BLPullback (R := R) (R' := R') f) :
    ModuleCat.of R ↑(beauvilleLaszloGlueingH0 f X) =
      (beauvilleLaszloRightAdjointFunctor (R := R) (R' := R') f).obj X := by
  -- Proof comment: both sides are the kernel module of the same specialized difference map.
  rfl

/-- Helper for Theorem 15.91.16: the Beauville-Laszlo kernel module `H⁰(X)` is the specialized
generic pullback right adjoint object. -/
private noncomputable abbrev beauvilleLaszloGlueingH0_iso_pullback_right_adjoint_obj
    (X : BLPullback (R := R) (R' := R') f) :
    ModuleCat.of R ↑(beauvilleLaszloGlueingH0 f X) ≅
      (beauvilleLaszloRightAdjointFunctor (R := R) (R' := R') f).obj X :=
  eqToIso (beauvilleLaszloGlueingH0_eq_rightAdjoint_obj (R := R) (R' := R') (f := f) X)

section LocalModuleCechHelpers

variable {M : Type u} [AddCommGroup M] [Module R M]

/-- Helper for Theorem 15.91.16: an element is `f`-power torsion exactly when it dies in the
localization away from `f`. -/
private theorem mem_fPowerTorsion_iff_localizedAway_eq_zero
    (x : M) :
    x ∈ (M[f^∞] : Submodule R M) ↔
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x = 0 := by
  -- Proof comment: rewrite `f^∞`-torsion as the kernel of the localization map.
  rw [Submodule.mem_torsion'_iff (Submonoid.powers f) x]
  constructor
  · rintro ⟨s, hsx⟩
    change x ∈ (LocalizedModule.mkLinearMap (Submonoid.powers f) M).ker
    exact (LocalizedModule.mem_ker_mkLinearMap_iff
      (S := Submonoid.powers f) (m := x)).2 ⟨s, s.2, hsx⟩
  · intro hx
    change x ∈ (LocalizedModule.mkLinearMap (Submonoid.powers f) M).ker at hx
    rcases (LocalizedModule.mem_ker_mkLinearMap_iff
      (S := Submonoid.powers f) (m := x)).1 hx with ⟨s, hs, hsx⟩
    exact ⟨⟨s, hs⟩, hsx⟩

/-- Helper for Theorem 15.91.16: under the canonical localization/tensor comparison, the pure
tensor `x ⊗ 1` becomes the localized generator of `x`. -/
private theorem tensor_localizationAway_eq_mkLinearMap
    (x : M) :
    let e : M ⊗[R] Localization.Away f ≃ₗ[R] LocalizedModule.Away f M :=
      (TensorProduct.comm R M (Localization.Away f)).trans
        ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars R)
    e (x ⊗ₜ[R] (1 : Localization.Away f)) =
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x := by
  -- Proof comment: this is the standard tensor/localization compatibility on a generator.
  change (LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm
      (Localization.mk (1 : R) (1 : Submonoid.powers f) ⊗ₜ[R] x) =
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x
  simpa [LocalizedModule.mkLinearMap_apply] using
    (LocalizedModule.equivTensorProduct_symm_apply_tmul
      (S := Submonoid.powers f)
      (M := M)
      (x := x)
      (r := (1 : R))
      (s := (1 : Submonoid.powers f)))

/-- Helper for Theorem 15.91.16: an element is `f`-power torsion exactly when its canonical
localization tensor `x ⊗ 1` vanishes. -/
private theorem mem_fPowerTorsion_iff_tensor_localization_eq_zero
    (x : M) :
    x ∈ (M[f^∞] : Submodule R M) ↔
      x ⊗ₜ[R] (1 : Localization.Away f) = 0 := by
  let e : M ⊗[R] Localization.Away f ≃ₗ[R] LocalizedModule.Away f M :=
    (TensorProduct.comm R M (Localization.Away f)).trans
      ((LocalizedModule.equivTensorProduct (Submonoid.powers f) M).symm.restrictScalars R)
  constructor
  · intro hx
    -- Proof comment: move the torsion statement to localization, then transport back through `e`.
    apply e.injective
    rw [tensor_localizationAway_eq_mkLinearMap (R := R) (f := f) (x := x)]
    exact (mem_fPowerTorsion_iff_localizedAway_eq_zero (R := R) (f := f) (x := x)).1 hx
  · intro hx
    -- Proof comment: vanishing of the tensor implies vanishing in localization, hence torsion.
    have hloc :
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) x = 0 := by
      rw [← tensor_localizationAway_eq_mkLinearMap (R := R) (f := f) (x := x)]
      exact congrArg e hx
    exact (mem_fPowerTorsion_iff_localizedAway_eq_zero (R := R) (f := f) (x := x)).2 hloc

/-- Helper for Theorem 15.91.16: the first component of the displayed left Beauville-Laszlo map
is the canonical pure tensor in `M ⊗[R] R'`. -/
private theorem moduleCechAlpha_fst_eq_tensor_baseChange_unit
    (x : M) :
    Prod.fst (beauvilleLaszloModuleCechAlpha R' (ModuleCat.of R M) f x) = x ⊗ₜ[R] (1 : R') := by
  -- Proof comment: normalize the displayed left map to the tensor-image model and read off the
  -- base-change coordinate.
  simp [beauvilleLaszloModuleCechAlpha, beauvilleLaszloModuleCechTensorImage,
    beauvilleLaszloModuleCechLeftIso, beauvilleLaszloModuleCechMiddleIso,
    beauvilleLaszloModuleCechCanonicalMiddleIso, beauvilleLaszloModuleCechMiddleTensorIso,
    beauvilleLaszloModuleCechMiddleTensor_eq, beauvilleLaszloCechLeftMap,
    tensorLeft_obj_tensorProductIso]

/-- Helper for Theorem 15.91.16: the second component of the displayed left Beauville-Laszlo map
is the canonical localization tensor `x ⊗ 1`. -/
private theorem moduleCechAlpha_snd_eq_tensor_localization_unit
    (x : M) :
    Prod.snd (beauvilleLaszloModuleCechAlpha R' (ModuleCat.of R M) f x) =
      x ⊗ₜ[R] (1 : Localization.Away f) := by
  -- Proof comment: the localization coordinate is the second tensor-image factor.
  simp [beauvilleLaszloModuleCechAlpha, beauvilleLaszloModuleCechTensorImage,
    beauvilleLaszloModuleCechLeftIso, beauvilleLaszloModuleCechMiddleIso,
    beauvilleLaszloModuleCechCanonicalMiddleIso, beauvilleLaszloModuleCechMiddleTensorIso,
    beauvilleLaszloModuleCechMiddleTensor_eq, beauvilleLaszloCechLeftMap,
    tensorLeft_obj_tensorProductIso]

/-- Helper for Theorem 15.91.16: the displayed right Beauville-Laszlo map is the difference
between the two canonical overlap maps on the `R'`- and `R_f`-coordinates. -/
private theorem moduleCechBeta_apply_explicit
    (y : M ⊗[R] R') (z : M ⊗[R] Localization.Away f) :
    beauvilleLaszloModuleCechBeta R' (ModuleCat.of R M) f (y, z) =
      (TensorProduct.map
          (LinearMap.id : M →ₗ[R] M)
          ((Algebra.linearMap R' (Localization.Away (algebraMap R R' f))).restrictScalars R)) y -
        (TensorProduct.map
          (LinearMap.id : M →ₗ[R] M)
          ((Localization.awayMapₐ (Algebra.ofId R R') f).toLinearMap)) z := by
  -- Proof comment: unfold the tensor-image right map once, then read off the two coordinates.
  simp [beauvilleLaszloModuleCechBeta, beauvilleLaszloModuleCechTensorImage,
    beauvilleLaszloModuleCechMiddleIso, beauvilleLaszloModuleCechCanonicalMiddleIso,
    beauvilleLaszloModuleCechMiddleTensorIso, beauvilleLaszloModuleCechMiddleTensor_eq,
    beauvilleLaszloCechRightMap, tensorLeft_obj_tensorProductIso]

/-- Helper for Theorem 15.91.16: the canonical tensor base-change unit restricted to the
principal-primary component. -/
private abbrev tensorBaseChangeUnitPrimaryComponentLocal :
    (M[(principalIdeal f)^∞] : Submodule R M) →ₗ[R]
      (R' ⊗[R] ↥((M[(principalIdeal f)^∞] : Submodule R M))) :=
  TensorProduct.mk R R' (↥((M[(principalIdeal f)^∞] : Submodule R M))) 1

/-- Helper for Theorem 15.91.16: after tensor symmetry, the restricted primary-component
base-change map is the first Beauville-Laszlo Cech coordinate. -/
private theorem tensorBaseChangeUnitPrimaryComponent_commutes_to_moduleCech_first_component
    (x : (M[(principalIdeal f)^∞] : Submodule R M)) :
    (TensorProduct.comm R R' ↥((M[(principalIdeal f)^∞] : Submodule R M)))
        (tensorBaseChangeUnitPrimaryComponentLocal
          (R := R) (R' := R') (f := f) x) =
      Prod.fst (beauvilleLaszloModuleCechAlpha R'
        (ModuleCat.of R ↥((M[(principalIdeal f)^∞] : Submodule R M))) f x) := by
  -- Proof comment: both maps are the same pure tensor after reordering the tensor factors.
  rw [moduleCechAlpha_fst_eq_tensor_baseChange_unit]
  rfl

/-- Helper for Theorem 15.91.16: after including the torsion subtype into `M`, the local
tensor base-change unit becomes the ambient first Beauville-Laszlo Cech coordinate. -/
private theorem tensorBaseChangeUnitPrimaryComponentLocal_to_ambient_first_coordinate
    (x : (M[(principalIdeal f)^∞] : Submodule R M)) :
    (TensorProduct.comm R R' M)
        (TensorProduct.map
          (LinearMap.id : R' →ₗ[R] R')
          (Submodule.subtype ((M[(principalIdeal f)^∞] : Submodule R M)))
          (tensorBaseChangeUnitPrimaryComponentLocal
            (R := R) (R' := R') (f := f) (M := M) x)) =
      Prod.fst (beauvilleLaszloModuleCechAlpha R' (ModuleCat.of R M) f x) := by
  -- Proof comment: the local tensor map is still the pure tensor `1 ⊗ x`; including the subtype
  -- and commuting the tensor factors recovers the ambient first coordinate.
  rw [moduleCechAlpha_fst_eq_tensor_baseChange_unit]
  rfl

/-- Helper for Theorem 15.91.16: the left Beauville-Laszlo map is injective exactly when the
restricted principal-primary tensor base-change map is injective. -/
private theorem beauvilleLaszloModuleCechLeftMap_injective_iff_primaryComponent_injective :
    Function.Injective ((beauvilleLaszloModuleCechSequence R' (ModuleCat.of R M) f).f.hom) ↔
      Function.Injective (tensorBaseChangeUnitPrimaryComponentLocal
        (R := R) (R' := R') (f := f) (M := M)) := by
  -- Proof comment: this is the local left-exactness bridge from the first and second Cech
  -- coordinates to the restricted torsion base-change map.
  -- TODO: the new ambient bridge above proves that the local tensor unit maps to the ambient
  -- first Cech coordinate. To finish, replay the `15.91.10` two-coordinate argument and add the
  -- missing reflection step showing that the tensorized subtype inclusion kills no element of the
  -- image of `tensorBaseChangeUnitPrimaryComponentLocal`.
  sorry

/-- Helper for Theorem 15.91.16: the principal-power quotient comparison rewrites to the generic
`Ideal.quotientMap` form required by the ideal-power-torsion base-change theorem. -/
private theorem principal_power_quotientMap_bijective
    (n : ℕ+)
    (hquot : ∀ m : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f m)) :
    Function.Bijective
      (Ideal.quotientMap
        (((principalIdeal f) ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map) := by
  -- Proof comment: transport the quotient comparison from the principal-power presentation to the
  -- generic `Ideal.quotientMap` statement used by Lemma `15.89.9`.
  let I : Ideal R := principalIdeal f
  let σ : R →+* R' := algebraMap R R'
  have hmap :
      Ideal.map σ (I ^ (n : ℕ)) = principalPowerIdeal (σ f) n := by
    simp [I, σ, principalPowerIdeal, principalIdeal, Ideal.map_pow, Ideal.map_span,
      Set.image_singleton]
  have htransport :
      principalPowerIdealImageQuotientMap σ f n =
        (Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map) := by
    -- Proof comment: both quotient maps agree on generators, so the principal-power model is the
    -- generic quotient map conjugated by the canonical quotient equivalence.
    apply Ideal.Quotient.ringHom_ext
    ext r
    dsimp [principalPowerIdealImageQuotientMap, principalPowerIdealQuotientMap]
    simpa [I, σ] using
      (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) (h := hmap) (x := σ r))
  have hcomp :
      Function.Bijective
        ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map)) := by
    -- Proof comment: rewrite the given Beauville-Laszlo quotient comparison through the quotient
    -- equivalence.
    have hcomp0 : Function.Bijective (principalPowerIdealImageQuotientMap σ f n) := by
      simpa [σ] using hquot n
    rw [htransport] at hcomp0
    exact hcomp0
  constructor
  · intro x y hxy
    have hxy0 :
        (Ideal.quotientMap
          (Ideal.map σ (I ^ (n : ℕ)))
          σ
          Ideal.le_comap_map) x =
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map) y := by
      simpa [I, σ] using hxy
    have hxy' :
        ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
          (Ideal.quotientMap
            (Ideal.map σ (I ^ (n : ℕ)))
            σ
            Ideal.le_comap_map)) x =
          ((Ideal.quotientEquivAlgOfEq R hmap).toRingHom.comp
            (Ideal.quotientMap
              (Ideal.map σ (I ^ (n : ℕ)))
              σ
              Ideal.le_comap_map)) y := by
      exact congrArg (Ideal.quotientEquivAlgOfEq R hmap) hxy0
    exact hcomp.1 hxy'
  · intro z
    obtain ⟨x, hx⟩ :=
      hcomp.2 ((Ideal.quotientEquivAlgOfEq R hmap) z)
    refine ⟨x, ?_⟩
    have hx' := hx
    have hx0 :
        (Ideal.quotientMap
          (Ideal.map σ (I ^ (n : ℕ)))
          σ
          Ideal.le_comap_map) x = z :=
      (Ideal.quotientEquivAlgOfEq R hmap).injective hx'
    simpa [I, σ] using hx0

/-- Helper for Theorem 15.91.16: the principal-primary component of a module is itself
`(f)`-power torsion. -/
private theorem primaryComponent_isIdealPowerTorsion :
    Module.IsIdealPowerTorsion (principalIdeal f) ↥((M[(principalIdeal f)^∞] : Submodule R M)) := by
  -- Proof comment: every element of the primary component carries its own annihilating power.
  rw [Module.isIdealPowerTorsion_iff]
  intro x
  obtain ⟨n, hn⟩ :=
    (Ideal.primaryComponent_mem M (principalIdeal f) x.1).1 x.2
  refine ⟨n, fun a ↦ ?_⟩
  apply Subtype.ext
  simpa using hn a

/-- Helper for Theorem 15.91.16: the restricted principal-primary tensor base-change map is
injective for a Beauville-Laszlo glueing pair. -/
private theorem tensorBaseChangeUnitPrimaryComponentLocal_injective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Injective (tensorBaseChangeUnitPrimaryComponentLocal
      (R := R) (R' := R') (f := f) (M := M)) := by
  -- Proof comment: the source proof reduces left exactness to injectivity on `(f)^∞`-torsion,
  -- and Lemma `15.89.9` supplies that injectivity once the local quotient transport above is in
  -- place.
  exact
    (tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
      (I := principalIdeal f)
      (R' := R')
      (M := ↥((M[(principalIdeal f)^∞] : Submodule R M)))
      (primaryComponent_isIdealPowerTorsion (R := R) (f := f) (M := M))
      (fun n ↦
        principal_power_quotientMap_bijective
          (R := R) (R' := R') (f := f) n hpair.quotientMapBijective)).1

/-- Helper for Theorem 15.91.16: under the quotient-isomorphism hypothesis, the right
Beauville-Laszlo module-Cech map is surjective. -/
private theorem beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
    (hquot : ∀ n : ℕ+, Function.Bijective
      (principalPowerIdealImageQuotientMap (algebraMap R R') f n)) :
    Function.Surjective ((beauvilleLaszloModuleCechSequence R' (ModuleCat.of R M) f).g.hom) := by
  -- Proof comment: tensor the ring-side surjectivity statement with `M` and transport it across
  -- the displayed middle isomorphism.
  have hring :
      Function.Surjective ((beauvilleLaszloCechSequence (algebraMap R R') f).g.hom) := by
    simpa [beauvilleLaszloCechSequence] using
      (beauvilleLaszloCechRightMap_surjective_of_principalPowerQuotientMapBijective
        (φ := algebraMap R R') (f := f) hquot)
  have htensor :
      Function.Surjective ((beauvilleLaszloModuleCechTensorImage R' (ModuleCat.of R M) f).g.hom) := by
    simpa [beauvilleLaszloModuleCechTensorImage] using
      (LinearMap.rTensor_surjective (ModuleCat.of R M)
        (g := (beauvilleLaszloCechSequence (algebraMap R R') f).g.hom)
        hring)
  change Function.Surjective (beauvilleLaszloModuleCechBeta R' (ModuleCat.of R M) f)
  intro z
  rcases htensor z with ⟨y, rfl⟩
  refine ⟨(beauvilleLaszloModuleCechMiddleIso R' (ModuleCat.of R M) f).hom y, ?_⟩
  simp [beauvilleLaszloModuleCechBeta]

end LocalModuleCechHelpers

/-- Helper for Theorem 15.91.16: the specialized pullback right adjoint lands in the full
subcategory of glueable modules. -/
private theorem beauvilleLaszloRightAdjoint_obj_mem_glueable
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (X : BLPullback (R := R) (R' := R') f) :
    beauvilleLaszloGlueableProperty R' f
      ((beauvilleLaszloRightAdjointFunctor (R := R) (R' := R') f).obj X) := by
  let M0 : ModuleCat R := ModuleCat.of R ↑(beauvilleLaszloGlueingH0 f X)
  have hleft :
      Function.Injective ((beauvilleLaszloModuleCechSequence R' M0 f).f.hom) := by
    -- Route correction: use the local torsion criterion in place of the broken imported owner
    -- file, then prove injectivity of the restricted primary-component tensor map via
    -- `tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective`.
    have hprimary :
        Function.Injective (tensorBaseChangeUnitPrimaryComponentLocal
          (R := R) (R' := R') (f := f) (M := ↑(beauvilleLaszloGlueingH0 f X))) :=
      tensorBaseChangeUnitPrimaryComponentLocal_injective
        (R := R) (R' := R') (f := f) (M := ↑(beauvilleLaszloGlueingH0 f X)) hpair
    exact
      (beauvilleLaszloModuleCechLeftMap_injective_iff_primaryComponent_injective
        (R := R) (R' := R') (f := f) (M := ↑(beauvilleLaszloGlueingH0 f X))).2 hprimary
  have hexact :
      Function.Exact
        ((beauvilleLaszloModuleCechSequence R' M0 f).f.hom)
        ((beauvilleLaszloModuleCechSequence R' M0 f).g.hom) :=
    beauvilleLaszloModuleCech_exact_of_glueing_pair
      (R := R) (R' := R') (f := f) hpair M0
  have hsurj :
      Function.Surjective ((beauvilleLaszloModuleCechSequence R' M0 f).g.hom) :=
    beauvilleLaszloModuleCechRightMap_surjective_of_principalPowerQuotientMapBijective
      (R := R) (R' := R') (f := f) (M := ↑(beauvilleLaszloGlueingH0 f X))
      hpair.quotientMapBijective
  have hshort : beauvilleLaszloGlueableProperty R' f M0 := by
    -- Proof comment: assemble short exactness of the module-Cech sequence from left injectivity,
    -- middle exactness, and right surjectivity.
    refine ModuleCat.shortComplex_shortExact (beauvilleLaszloModuleCechSequence R' M0 f) ?_ ?_ ?_
    · exact hexact
    · exact hleft
    · exact hsurj
  simpa [M0, beauvilleLaszloGlueingH0_eq_rightAdjoint_obj
    (R := R) (R' := R') (f := f) X] using hshort

/-- Helper for Theorem 15.91.16: the specialized `H⁰` construction as a functor into the
glueable full subcategory. -/
private noncomputable abbrev beauvilleLaszloGlueableCanRightAdjoint
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    BLPullback (R := R) (R' := R') f ⥤ BLGlueableModuleCat (R := R) (R' := R') f :=
  (beauvilleLaszloGlueableProperty R' f).lift
    (beauvilleLaszloRightAdjointFunctor (R := R) (R' := R') f)
    (fun X ↦ beauvilleLaszloRightAdjoint_obj_mem_glueable
      (R := R) (R' := R') (f := f) hpair X)

/-- Helper for Theorem 15.91.16: objectwise image isomorphisms for the restricted canonical
functor assemble to essential surjectivity. -/
private theorem beauvilleLaszloGlueableCan_essSurj_of_objectwise_iso
    (f : R)
    (hobj :
      ∀ X : BLPullback (R := R) (R' := R') f,
        ∃ M : (beauvilleLaszloGlueableProperty R' f).FullSubcategory,
          Nonempty
            ((((beauvilleLaszloGlueableProperty R' f).ι ⋙
                formalGlueingSingleFunctor R' f).obj M) ≅ X)) :
    (((beauvilleLaszloGlueableProperty R' f).ι ⋙
        formalGlueingSingleFunctor R' f)).EssSurj := by
  intro X
  -- Proof comment: essential surjectivity is exactly the objectwise existence of a preimage
  -- together with an isomorphism from that image to the target object.
  rcases hobj X with ⟨M, hM⟩
  exact ⟨M, hM⟩

/-- Helper for Theorem 15.91.16: on the canonical Beauville-Laszlo datum `Can(M)`, the public
`H⁰` owner is the kernel of the displayed Beauville-Laszlo module Cech right map. -/
private theorem beauvilleLaszloGlueingH0_eq_moduleCech_kernel
    (M : ModuleCat R) :
    beauvilleLaszloGlueingH0 f
        ((beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f).obj M) =
      LinearMap.ker (beauvilleLaszloModuleCechBeta R' M f) := by
  -- Proof comment: both sides are the kernel of the same difference map on
  -- `(M ⊗[R] R') × (M ⊗[R] R_f)`.
  ext x
  rcases x with ⟨y, z⟩
  constructor
  · intro hx
    -- On the canonical datum `Can(M)`, the `H⁰` kernel equation is exactly the displayed
    -- Beauville-Laszlo module-Cech kernel relation.
    simpa [beauvilleLaszloGlueingH0, LinearMap.mem_ker, beauvilleLaszloGlueingDifferential,
      LinearMap.coprod_apply, sub_eq_add_neg,
      moduleCechBeta_apply_explicit (R := R) (R' := R') (M := M) (f := f) y z] using hx
  · intro hx
    -- The converse implication is the same pointwise equality read in the opposite direction.
    simpa [beauvilleLaszloGlueingH0, LinearMap.mem_ker, beauvilleLaszloGlueingDifferential,
      LinearMap.coprod_apply, sub_eq_add_neg,
      moduleCechBeta_apply_explicit (R := R) (R' := R') (M := M) (f := f) y z] using hx

/-- Helper for Theorem 15.91.16: after passing through `moduleCatCyclesIso.hom`, the categorical
boundary map to cycles becomes the concrete kernel-level map `moduleCatToCycles`. -/
private theorem moduleCatCyclesIso_hom_toCycles
    (S : ShortComplex (ModuleCat R)) (x : S.X₁) :
    S.moduleCatCyclesIso.hom (S.toCycles.hom x) = S.moduleCatToCycles x := by
  -- Proof comment: compare both cycle representatives through their common ambient value in
  -- `S.X₂`, then use `ShortComplex.toCycles_i`.
  apply Subtype.ext
  change S.iCycles.hom (S.toCycles.hom x) = (S.moduleCatToCycles x).1
  have hto :
      S.iCycles.hom (S.toCycles.hom x) = S.f.hom x := by
    have hto' :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_i S)) x
    change ((S.toCycles ≫ S.iCycles).hom x) = S.f.hom x at hto'
    exact hto'
  simpa [ShortComplex.moduleCatToCycles] using hto

/-- Helper for Theorem 15.91.16: a Beauville-Laszlo glueing pair gives middle exactness of the
canonical module Cech sequence. -/
private theorem beauvilleLaszloModuleCech_exact_of_glueing_pair
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (M : ModuleCat R) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := by
  -- Proof comment: tensor the ring-level Beauville-Laszlo exact sequence with `M`, and then
  -- transport exactness through the canonical left and middle isomorphisms of the displayed Cech
  -- sequence.
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  have hringExact :
      Function.Exact
        (beauvilleLaszloCechLeftMap (algebraMap R R') f)
        (beauvilleLaszloCechRightMap (algebraMap R R') f) := by
    -- The glueing-pair hypothesis already packages exactness of the ring-level Cech complex.
    simpa [beauvilleLaszloCechSequence] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (beauvilleLaszloCechSequence (algebraMap R R') f)).1 hpair.shortExact.exact
  have hringSurj :
      Function.Surjective (beauvilleLaszloCechRightMap (algebraMap R R') f) := by
    -- The same short exactness statement records surjectivity of the right ring-level map.
    simpa [beauvilleLaszloCechSequence] using hpair.shortExact.moduleCat_surjective_g
  have htensorExact :
      Function.Exact
        ((beauvilleLaszloModuleCechTensorImage R' M f).f.hom)
        ((beauvilleLaszloModuleCechTensorImage R' M f).g.hom) := by
    -- Right exactness of tensor product lifts the ring-level exactness to the tensor-image model.
    simpa [beauvilleLaszloModuleCechTensorImage, ModuleCat.hom_whiskerLeft] using
      (lTensor_exact M hringExact hringSurj)
  change Function.Exact
    (beauvilleLaszloModuleCechAlpha R' M f)
    (beauvilleLaszloModuleCechBeta R' M f)
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · -- The displayed Cech maps form a complex by construction.
    simpa [beauvilleLaszloModuleCechSequence] using
      (beauvilleLaszloModuleCech_comp_eq_zero R' M f)
  · intro x hx
    let middleIso := beauvilleLaszloModuleCechMiddleIso R' M f
    let leftIso := beauvilleLaszloModuleCechLeftIso R' M f
    have hxTensor :
        (beauvilleLaszloModuleCechTensorImage R' M f).g.hom (middleIso.inv.hom x) = 0 := by
      -- Move the kernel condition for the displayed right map back to the tensor-image model.
      simpa [beauvilleLaszloModuleCechBeta, middleIso] using hx
    have hxRange :
        middleIso.inv.hom x ∈
          LinearMap.range ((beauvilleLaszloModuleCechTensorImage R' M f).f.hom) := by
      have hxKer :
          middleIso.inv.hom x ∈
            LinearMap.ker ((beauvilleLaszloModuleCechTensorImage R' M f).g.hom) := by
        simpa [LinearMap.mem_ker] using hxTensor
      rw [(LinearMap.exact_iff.1 htensorExact)] at hxKer
      exact hxKer
    rcases hxRange with ⟨y, hy⟩
    refine ⟨leftIso.hom y, ?_⟩
    have hmiddle_injective : Function.Injective middleIso.inv.hom := by
      intro a b hab
      calc
        a = middleIso.hom.hom (middleIso.inv.hom a) := by
          simpa using (middleIso.inv_hom_id_apply a).symm
        _ = middleIso.hom.hom (middleIso.inv.hom b) := by
          simpa using congrArg middleIso.hom.hom hab
        _ = b := by
          simpa using middleIso.inv_hom_id_apply b
    -- Transport the tensor-image preimage back to the displayed Beauville-Laszlo complex.
    apply hmiddle_injective
    calc
      middleIso.inv.hom (beauvilleLaszloModuleCechAlpha R' M f (leftIso.hom y)) =
          (beauvilleLaszloModuleCechTensorImage R' M f).f.hom
            (leftIso.inv.hom (leftIso.hom y)) := by
              simpa [beauvilleLaszloModuleCechAlpha, leftIso, middleIso] using
                (middleIso.hom_inv_id_apply
                  ((beauvilleLaszloModuleCechTensorImage R' M f).f.hom
                    (leftIso.inv.hom (leftIso.hom y))))
      _ = (beauvilleLaszloModuleCechTensorImage R' M f).f.hom y := by
            simpa using
              congrArg ((beauvilleLaszloModuleCechTensorImage R' M f).f.hom)
                (leftIso.hom_inv_id_apply y)
      _ = middleIso.inv.hom x := hy

/-- Helper for Theorem 15.91.16: for a glueable module, the canonical map into cycles of the
Beauville-Laszlo module Cech sequence is an isomorphism. -/
private theorem beauvilleLaszloModuleCech_moduleCatToCycles_isIso
    (M : BLGlueableModuleCat (R := R) (R' := R') f) :
    IsIso ((beauvilleLaszloModuleCechSequence R' M.obj f).moduleCatToCycles) := by
  let S := beauvilleLaszloModuleCechSequence R' M.obj f
  have hsurj : Function.Surjective S.moduleCatToCycles := by
    have hExact : S.Exact := M.property.exact
    -- Exactness of the short complex identifies surjectivity of the concrete cycles map.
    exact (ShortComplex.exact_iff_surjective_moduleCatToCycles (S := S)).1 hExact
  have hinj : Function.Injective S.moduleCatToCycles := by
    intro x y hxy
    have hxy_f : S.f.hom x = S.f.hom y := by
      -- Forgetting a cycle to the ambient middle term recovers the first Cech map.
      simpa [ShortComplex.moduleCatToCycles] using congrArg Subtype.val hxy
    exact ((ModuleCat.mono_iff_injective S.f).1 M.property.mono_f) hxy_f
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective S.moduleCatToCycles).2
    ⟨hinj, hsurj⟩

/-- Helper for Theorem 15.91.16: on `Can(M)`, the right-adjoint target of the ambient adjunction
identifies with the displayed kernel object of the Beauville-Laszlo module Cech sequence. -/
private noncomputable abbrev beauvilleLaszloGlueableCan_unitTargetIso
    (M : BLGlueableModuleCat (R := R) (R' := R') f) :
    (beauvilleLaszloRightAdjointFunctor (R := R) (R' := R') f).obj
        ((beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f).obj M.obj) ≅
      ModuleCat.of R (LinearMap.ker (beauvilleLaszloModuleCechBeta R' M.obj f)) :=
  (beauvilleLaszloGlueingH0_iso_pullback_right_adjoint_obj
      (R := R) (R' := R') (f := f)
      ((beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f).obj M.obj)).symm ≪≫
    eqToIso (congrArg (ModuleCat.of R)
      (beauvilleLaszloGlueingH0_eq_moduleCech_kernel
        (R := R) (R' := R') (f := f) M.obj))

/-- Helper for Theorem 15.91.16: after transporting the ambient adjunction unit to the displayed
kernel model for `Can(M)`, it is exactly the concrete map `moduleCatToCycles`. -/
private theorem beauvilleLaszloGlueableCan_unit_app_comp_targetIso_eq_moduleCatToCycles
    (M : BLGlueableModuleCat (R := R) (R' := R') f) :
    ((module_tensor_pullback_adjunction
        (algebraMap R R')
        (algebraMap R (Localization.Away f))
        (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).unit.app M.obj) ≫
      (beauvilleLaszloGlueableCan_unitTargetIso
        (R := R) (R' := R') (f := f) M).hom =
        (beauvilleLaszloModuleCechSequence R' M.obj f).moduleCatToCycles := by
  let adj :=
    module_tensor_pullback_adjunction
      (algebraMap R R')
      (algebraMap R (Localization.Away f))
      (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)
  let canObj := (beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f).obj M.obj
  let targetIso :=
    beauvilleLaszloGlueableCan_unitTargetIso (R := R) (R' := R') (f := f) M
  let kernelSubtype :
      ModuleCat.of R (LinearMap.ker (beauvilleLaszloModuleCechBeta R' M.obj f)) ⟶
        ModuleCat.of R ((M.obj ⊗[R] R') × (M.obj ⊗[R] Localization.Away f)) :=
    ModuleCat.ofHom (LinearMap.ker (beauvilleLaszloModuleCechBeta R' M.obj f)).subtype
  have hunit :
      (adj.homEquiv M.obj canObj) (𝟙 canObj) = adj.unit.app M.obj := by
    -- Proof comment: the adjunction unit is the Hom-equivalence image of the identity map.
    simpa using (adj.homEquiv_unit (X := M.obj) (Y := canObj) (f := 𝟙 canObj))
  apply (cancel_mono kernelSubtype).1
  -- Proof comment: compare the two maps in the ambient middle term and then read off the two
  -- coordinates using the explicit Beauville-Laszlo Cech formulas.
  ext x
  apply Prod.ext
  · have hfst :=
      congrArg
        (fun k ↦ Prod.fst ((k ≫ targetIso.hom ≫ kernelSubtype) x))
        hunit
    simpa [adj, canObj, targetIso, kernelSubtype, beauvilleLaszloBaseChangeFunctor,
      beauvilleLaszloRightAdjointFunctor, moduleCechAlpha_fst_eq_tensor_baseChange_unit] using
      hfst
  · have hsnd :=
      congrArg
        (fun k ↦ Prod.snd ((k ≫ targetIso.hom ≫ kernelSubtype) x))
        hunit
    simpa [adj, canObj, targetIso, kernelSubtype, beauvilleLaszloBaseChangeFunctor,
      beauvilleLaszloRightAdjointFunctor, moduleCechAlpha_snd_eq_tensor_localization_unit] using
      hsnd

/-- Helper for Theorem 15.91.16: the ambient pullback adjunction unit is an isomorphism on the
full subcategory of glueable modules. -/
private theorem beauvilleLaszloGlueableCan_unit_app_isIso
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (M : BLGlueableModuleCat (R := R) (R' := R') f) :
    IsIso
      ((module_tensor_pullback_adjunction
        (algebraMap R R')
        (algebraMap R (Localization.Away f))
        (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).unit.app M.obj) := by
  -- Proof comment: transport the unit target to the displayed kernel model and reuse the already
  -- proved isomorphism for the concrete `moduleCatToCycles` map.
  have hcyclesIso :
      IsIso ((beauvilleLaszloModuleCechSequence R' M.obj f).moduleCatToCycles) :=
    beauvilleLaszloModuleCech_moduleCatToCycles_isIso
      (R := R) (R' := R') (f := f) M
  let targetIso :=
    beauvilleLaszloGlueableCan_unitTargetIso (R := R) (R' := R') (f := f) M
  have hunit_eq :
      ((module_tensor_pullback_adjunction
          (algebraMap R R')
          (algebraMap R (Localization.Away f))
          (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).unit.app M.obj) ≫
        targetIso.hom =
          (beauvilleLaszloModuleCechSequence R' M.obj f).moduleCatToCycles :=
    beauvilleLaszloGlueableCan_unit_app_comp_targetIso_eq_moduleCatToCycles
      (R := R) (R' := R') (f := f) M
  have hunit_eq' :
      ((module_tensor_pullback_adjunction
          (algebraMap R R')
          (algebraMap R (Localization.Away f))
          (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).unit.app M.obj) =
        (beauvilleLaszloModuleCechSequence R' M.obj f).moduleCatToCycles ≫ targetIso.inv := by
    apply (cancel_mono targetIso.hom).1
    simpa [Category.assoc] using hunit_eq
  -- The transported unit is a composite of two isomorphisms, hence the original unit is too.
  rw [hunit_eq']
  infer_instance

/-- Helper for Theorem 15.91.16: the restricted adjunction unit component on the glueable full
subcategory. -/
private noncomputable abbrev beauvilleLaszloGlueableCan_unitIsoApp
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (M : BLGlueableModuleCat (R := R) (R' := R') f) :
    M ≅
      (((beauvilleLaszloGlueableProperty R' f).ι ⋙
          beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f) ⋙
        beauvilleLaszloGlueableCanRightAdjoint (R := R) (R' := R') (f := f) hpair).obj M :=
  letI := beauvilleLaszloGlueableCan_unit_app_isIso (R := R) (R' := R') (f := f) hpair M
  (beauvilleLaszloGlueableProperty R' f).isoMk
    (asIso ((module_tensor_pullback_adjunction
      (algebraMap R R')
      (algebraMap R (Localization.Away f))
      (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).unit.app M.obj))

/-- Helper for Theorem 15.91.16: the restricted adjunction unit is natural on glueable modules.
-/
private theorem beauvilleLaszloGlueableCan_unitIso_naturality
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    {M N : BLGlueableModuleCat (R := R) (R' := R') f}
    (g : M ⟶ N) :
    g ≫ (beauvilleLaszloGlueableCan_unitIsoApp (R := R) (R' := R') (f := f) hpair N).hom =
      (beauvilleLaszloGlueableCan_unitIsoApp (R := R) (R' := R') (f := f) hpair M).hom ≫
        ((((beauvilleLaszloGlueableProperty R' f).ι ⋙
            beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f) ⋙
          beauvilleLaszloGlueableCanRightAdjoint
            (R := R) (R' := R') (f := f) hpair).map g) := by
  -- Proof comment: forget to the ambient module category and use naturality of the adjunction
  -- unit.
  ext
  simpa [beauvilleLaszloGlueableCan_unitIsoApp] using
    NatTrans.naturality
      ((module_tensor_pullback_adjunction
        (algebraMap R R')
        (algebraMap R (Localization.Away f))
        (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).unit) g

/-- Helper for Theorem 15.91.16: the restricted adjunction unit natural isomorphism on the
glueable full subcategory. -/
private noncomputable abbrev beauvilleLaszloGlueableCan_unitIso
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    𝟭 (BLGlueableModuleCat (R := R) (R' := R') f) ≅
      ((beauvilleLaszloGlueableProperty R' f).ι ⋙
          beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f) ⋙
        beauvilleLaszloGlueableCanRightAdjoint (R := R) (R' := R') (f := f) hpair :=
  NatIso.ofComponents
    (fun M ↦ beauvilleLaszloGlueableCan_unitIsoApp (R := R) (R' := R') (f := f) hpair M)
    (fun _ _ g ↦ beauvilleLaszloGlueableCan_unitIso_naturality
      (R := R) (R' := R') (f := f) hpair g)

/-- Helper for Theorem 15.91.16: the ambient pullback adjunction counit is already an
isomorphism on every Beauville-Laszlo pullback datum. -/
private theorem beauvilleLaszloGlueableCan_counit_app_isIso
    (X : BLPullback (R := R) (R' := R') f) :
    IsIso
      ((module_tensor_pullback_adjunction
        (algebraMap R R')
        (algebraMap R (Localization.Away f))
        (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).counit.app X) := by
  -- Proof comment: this is exactly the owner-level counit isomorphism from the generic pullback
  -- adjunction.
  letI : IsIso
      ((module_tensor_pullback_adjunction
        (algebraMap R R')
        (algebraMap R (Localization.Away f))
        (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).counit) :=
    module_tensor_pullback_adjunction_counit_isIso
      (algebraMap R R')
      (algebraMap R (Localization.Away f))
      (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)
  infer_instance

/-- Helper for Theorem 15.91.16: the restricted adjunction counit component on Beauville-Laszlo
pullback data. -/
private noncomputable abbrev beauvilleLaszloGlueableCan_counitIsoApp
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    (X : BLPullback (R := R) (R' := R') f) :
    ((beauvilleLaszloGlueableCanRightAdjoint (R := R) (R' := R') (f := f) hpair) ⋙
        (beauvilleLaszloGlueableProperty R' f).ι ⋙
        beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f).obj X ≅
      X :=
  letI := beauvilleLaszloGlueableCan_counit_app_isIso (R := R) (R' := R') (f := f) X
  asIso ((module_tensor_pullback_adjunction
    (algebraMap R R')
    (algebraMap R (Localization.Away f))
    (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).counit.app X)

/-- Helper for Theorem 15.91.16: the restricted adjunction counit is natural on Beauville-Laszlo
pullback data. -/
private theorem beauvilleLaszloGlueableCan_counitIso_naturality
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f)
    {X Y : BLPullback (R := R) (R' := R') f}
    (g : X ⟶ Y) :
    (((beauvilleLaszloGlueableCanRightAdjoint (R := R) (R' := R') (f := f) hpair) ⋙
        (beauvilleLaszloGlueableProperty R' f).ι ⋙
        beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f).map g) ≫
        (beauvilleLaszloGlueableCan_counitIsoApp
          (R := R) (R' := R') (f := f) hpair Y).hom =
      (beauvilleLaszloGlueableCan_counitIsoApp
        (R := R) (R' := R') (f := f) hpair X).hom ≫ g := by
  -- Proof comment: this is ambient counit naturality after forgetting the lifted source object.
  simpa [beauvilleLaszloGlueableCan_counitIsoApp] using
    NatTrans.naturality
      ((module_tensor_pullback_adjunction
        (algebraMap R R')
        (algebraMap R (Localization.Away f))
        (formalGlueingSingleAwaySquare_commutes (R := R) (S := R') f)).counit) g

/-- Helper for Theorem 15.91.16: the restricted adjunction counit natural isomorphism on
Beauville-Laszlo pullback data. -/
private noncomputable abbrev beauvilleLaszloGlueableCan_counitIso
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloGlueableCanRightAdjoint (R := R) (R' := R') (f := f) hpair) ⋙
        (beauvilleLaszloGlueableProperty R' f).ι ⋙
        beauvilleLaszloBaseChangeFunctor (R := R) (R' := R') f ≅
      𝟭 (BLPullback (R := R) (R' := R') f) :=
  NatIso.ofComponents
    (fun X ↦ beauvilleLaszloGlueableCan_counitIsoApp
      (R := R) (R' := R') (f := f) hpair X)
    (fun _ _ g ↦ beauvilleLaszloGlueableCan_counitIso_naturality
      (R := R) (R' := R') (f := f) hpair g)

-- Proof sketch: for a glueing datum `(M', M₁, α₁)`, define `H^0` as the kernel of the
-- Beauville-Laszlo differential from `15.91.16.1`. The surjectivity and exactness statements in
-- `15.91.16.1`-`15.91.16.3`, together with Lemmas `15.91.15`, `15.89.9`, and `15.90.11`, show
-- that this kernel is glueable, that `Can(H^0(-))` reconstructs the original glueing datum, and
-- that `H^0(Can(M)) = M` for every glueable module `M`.
/-- Theorem 15.91.16: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the canonical
functor `Can : Mod_R → Glue(R → R', f)` induces an equivalence from the category of glueable
`R`-modules for `(R → R', f)` to the category of Beauville-Laszlo glueing data. In this
library-facing formalization, the source is the full subcategory
`(beauvilleLaszloGlueableProperty R' f).FullSubcategory` of `ModuleCat R`, and the target is the
categorical pullback `Mod_{R'} ×_{Mod_{R'_f}} Mod_{R_f}`. -/
theorem beauvilleLaszloGlueableCan_isEquivalence
    (f : R) (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Functor.IsEquivalence
      ((beauvilleLaszloGlueableProperty R' f).ι ⋙ formalGlueingSingleFunctor R' f) := by
  -- Route correction: package the source proof through the generic pullback adjunction, with the
  -- specialized right adjoint interpreted as the kernel module `H⁰`.
  -- Proof comment: once the right adjoint lands in the glueable full subcategory, the only
  -- nonformal Beauville-Laszlo work is the source-side unit-isomorphism statement; the target-side
  -- counit is already an owner-level isomorphism.
  simpa [formalGlueingSingleFunctor, beauvilleLaszloBaseChangeFunctor] using
    (Functor.IsEquivalence.mk'
      (beauvilleLaszloGlueableCanRightAdjoint
        (R := R) (R' := R') (f := f) hpair)
      (beauvilleLaszloGlueableCan_unitIso
        (R := R) (R' := R') (f := f) hpair)
      (beauvilleLaszloGlueableCan_counitIso
        (R := R) (R' := R') (f := f) hpair))

end
