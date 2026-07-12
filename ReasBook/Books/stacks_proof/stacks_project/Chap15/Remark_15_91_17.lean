import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import StacksProject_2024.Chap15.«15_91_16_2»
import StacksProject_2024.Chap15.«15_91_16_3»
import StacksProject_2024.Chap15.«15_91_9_1»
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

/- Domain-style sampling:
- primary domain: Beauville-Laszlo glueability for a single localization, expressed through the
  canonical module Cech short complex and its cycles object;
- sampled owner declarations:
  `beauvilleLaszloModuleCechSequence`,
  `ShortComplex.moduleCatToCycles`,
  `ShortComplex.exact_iff_surjective_moduleCatToCycles`,
  `(beauvilleLaszloModuleCechSequence R' M f).ShortExact`;
- best owner abstraction: the source-facing replacement module `\tilde M = H^0(Can(M))` should be
  exposed as the cycles object of the canonical owner
  `beauvilleLaszloModuleCechSequence R' M f`, and the canonical map `M → \tilde M` should reuse
  `ShortComplex.moduleCatToCycles` directly;
- primitive data vs derived API: the primitive data are the module Cech short complex and its
  canonical map to cycles; the replacement module, its glueability, the induced base-change and
  localization bijectivity, and the surjectivity conclusion are derived API.

Source/core/bridge triage:
- `source-facing`: the replacement module `\tilde M = H^0(Can(M))` and the canonical map
  `M → \tilde M` from Remark `15.91.17`;
- `core/canonical`: `beauvilleLaszloModuleCechSequence`, `ShortComplex.moduleCatToCycles`, and
  `ShortComplex.exact_iff_surjective_moduleCatToCycles`;
- `bridge/view`: the induced maps after tensoring with `R'` and localizing away from `f`.
-/

section

variable {R : Type u} [CommRing R]
variable {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type u} [AddCommGroup M] [Module R M]
variable {f : R}

/-- Helper for Remark 15.91.17: the canonical single-glueing datum `Can(M)` attached to `M`. -/
private abbrev beauvilleLaszloModuleCechSingleDatum :=
  (formalGlueingSingleFunctor R' f).obj (ModuleCat.of R M)

/-- Helper for Remark 15.91.17: the first branch of `Can(M)` is the usual tensor base change
`R' ⊗[R] M`. -/
private noncomputable abbrev beauvilleLaszlo_module_cech_single_datum_fst_iso :
    (beauvilleLaszloModuleCechSingleDatum (R := R) (R' := R') (M := M) (f := f)).fst ≅
      ModuleCat.of R' (R' ⊗[R] M) := by
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) ≃ₗ[R'] R' :=
    { __ := AddEquiv.refl R'
      map_smul' := fun _ _ ↦ rfl }
  letI :
      IsScalarTower R R'
        ↑((ModuleCat.restrictScalars (algebraMap R R')).obj (ModuleCat.of R' R')) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  -- Unfold the first branch of `Can(M)` to the scalar-extension owner and rewrite it in the
  -- tensor-product model used by the displayed Cech sequence.
  simpa [beauvilleLaszloModuleCechSingleDatum, formalGlueingSingleFunctor,
    ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl R M)).toModuleIso

/-- Helper for Remark 15.91.17: the second branch of `Can(M)` is the usual away localization
`R_f ⊗[R] M`. -/
private noncomputable abbrev beauvilleLaszlo_module_cech_single_datum_snd_iso :
    (beauvilleLaszloModuleCechSingleDatum (R := R) (R' := R') (M := M) (f := f)).snd ≅
      ModuleCat.of (Localization.Away f) (Localization.Away f ⊗[R] M) := by
  let restrictScalarsSelfEquiv :
      ↑((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).obj
        (ModuleCat.of (Localization.Away f) (Localization.Away f))) ≃ₗ[Localization.Away f]
        Localization.Away f :=
    { __ := AddEquiv.refl (Localization.Away f)
      map_smul' := fun _ _ ↦ rfl }
  letI :
      IsScalarTower R (Localization.Away f)
        ↑((ModuleCat.restrictScalars (algebraMap R (Localization.Away f))).obj
          (ModuleCat.of (Localization.Away f) (Localization.Away f))) :=
    IsScalarTower.of_algebraMap_smul fun r s ↦ by
      rfl
  -- The second branch is the scalar extension of `M` to the away localization, so the same
  -- tensor-product normalization applies.
  simpa [beauvilleLaszloModuleCechSingleDatum, formalGlueingSingleFunctor,
    ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
    (TensorProduct.AlgebraTensorModule.congr
      restrictScalarsSelfEquiv
      (LinearEquiv.refl R M)).toModuleIso

/-- Helper for Remark 15.91.17: after passing through `moduleCatCyclesIso.hom`, the categorical
boundary map `toCycles` becomes the concrete kernel-level map `moduleCatToCycles`. -/
private theorem moduleCatCyclesIso_hom_toCycles
    (S : ShortComplex (ModuleCat R)) (b : S.X₁) :
    S.moduleCatCyclesIso.hom (S.toCycles.hom b) = S.moduleCatToCycles b := by
  -- Compare both cycle representatives through their ambient values in `S.X₂`.
  apply Subtype.ext
  change S.iCycles.hom (S.toCycles.hom b) = (S.moduleCatToCycles b).1
  have hto :
      S.iCycles.hom (S.toCycles.hom b) = S.f.hom b := by
    -- The defining relation `toCycles ≫ iCycles = f` identifies the ambient values.
    have hto' :=
      LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_i S)) b
    change ((S.toCycles ≫ S.iCycles).hom b) = S.f.hom b at hto'
    exact hto'
  simpa [ShortComplex.moduleCatToCycles] using hto

/-- Helper for Remark 15.91.17: after applying `moduleCatCyclesIso.hom`, the image of a lifted
boundary under a short-complex morphism is the target `moduleCatToCycles` boundary. -/
private theorem cyclesMap_toCycles_moduleCatToCycles
    {S₁ S₂ : ShortComplex (ModuleCat R)} (φ : S₁ ⟶ S₂) (b : S₁.X₁) :
    S₂.moduleCatCyclesIso.hom (((ShortComplex.cyclesMap φ).hom) (S₁.toCycles.hom b)) =
      S₂.moduleCatToCycles (φ.τ₁.hom b) := by
  -- Naturality of `toCycles` transports the lifted boundary across `φ`, and the target-side
  -- `moduleCatCyclesIso.hom` then identifies the result with `moduleCatToCycles`.
  have hnat := congrArg ModuleCat.Hom.hom (ShortComplex.toCycles_naturality φ)
  have hnat' := LinearMap.congr_fun hnat b
  calc
    S₂.moduleCatCyclesIso.hom (((ShortComplex.cyclesMap φ).hom) (S₁.toCycles.hom b)) =
        S₂.moduleCatCyclesIso.hom (S₂.toCycles.hom (φ.τ₁.hom b)) := by
          exact congrArg S₂.moduleCatCyclesIso.hom hnat'
    _ = S₂.moduleCatToCycles (φ.τ₁.hom b) :=
      moduleCatCyclesIso_hom_toCycles S₂ (φ.τ₁.hom b)

/-- Helper for Remark 15.91.17: after inverting `f`, the `f`-torsion submodule of any module
vanishes. -/
lemma localized_torsionBy_eq_bot_away
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] (g : A) :
    (Submodule.torsionBy A N g).localized (p := Submonoid.powers g) = ⊥ := by
  -- A localized torsion class is still killed by the image of `g`, but that image is a unit.
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_localized'] at hx
  rcases hx with ⟨m, hm, s, rfl⟩
  rw [Submodule.mem_torsionBy_iff] at hm
  have hsmul :
      (algebraMap A (Localization.Away g) g) •
          IsLocalizedModule.mk'
            (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s = 0 := by
    -- Rewrite the torsion relation inside the away localization.
    simpa [IsLocalizedModule.mk'_smul] using congrArg
      (fun y : N ↦
        IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap (Submonoid.powers g) N) y s)
      hm
  have hunit : IsUnit (algebraMap A (Localization.Away g) g) := by
    -- The distinguished element `g` is invertible in the away localization.
    exact IsLocalization.map_units (Localization.Away g)
      ⟨g, show g ∈ Submonoid.powers g by exact ⟨1, by simp⟩⟩
  rcases hunit with ⟨u, hu⟩
  calc
    IsLocalizedModule.mk'
        (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s =
        (↑u⁻¹ : Localization.Away g) •
          ((algebraMap A (Localization.Away g) g) •
            IsLocalizedModule.mk'
              (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s) := by
          calc
            IsLocalizedModule.mk'
                (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s =
                (1 : Localization.Away g) •
                  IsLocalizedModule.mk'
                    (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s := by
                      simp
            _ = (((↑u⁻¹ : Localization.Away g) * ↑u) :
                  Localization.Away g) •
                  IsLocalizedModule.mk'
                    (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s := by
                      rw [Units.inv_mul]
            _ = (↑u⁻¹ : Localization.Away g) •
                  (↑u •
                    IsLocalizedModule.mk'
                      (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s) := by
                      simp [Units.smul_def, smul_smul]
            _ = (↑u⁻¹ : Localization.Away g) •
                  ((algebraMap A (Localization.Away g) g) •
                    IsLocalizedModule.mk'
                      (LocalizedModule.mkLinearMap (Submonoid.powers g) N) m s) := by
                      simp [Units.smul_def, hu]
    _ = 0 := by
          simp [hsmul]

/-- Helper for Remark 15.91.17: quotienting by the `f`-torsion submodule does not change the away
localization. -/
noncomputable def away_localized_quotient_torsionBy_linearEquiv_local
    {A : Type*} [CommRing A]
    {N : Type*} [AddCommGroup N] [Module A N] (g : A) :
    LocalizedModule.Away g (N ⧸ Submodule.torsionBy A N g) ≃ₗ[Localization.Away g]
      LocalizedModule.Away g N :=
  (localizedQuotientEquiv (Submonoid.powers g) (Submodule.torsionBy A N g)).symm ≪≫ₗ
    (Submodule.localized (p := Submonoid.powers g) (Submodule.torsionBy A N g)).quotEquivOfEqBot
      (localized_torsionBy_eq_bot_away (A := A) (N := N) g)

/-- Helper for Remark 15.91.17: tensoring a bijective linear map along a scalar extension keeps
the base-changed map bijective. -/
private theorem baseChange_bijective_of_bijective_local
    {A : Type*} [CommRing A] [Algebra R A]
    {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] [Module R N] [Module R P]
    (φ : N →ₗ[R] P) (hφ : Function.Bijective φ) :
    Function.Bijective (LinearMap.baseChange A φ) := by
  let e : N ≃ₗ[R] P := LinearEquiv.ofBijective φ hφ
  let ψ : P →ₗ[R] N := e.symm.toLinearMap
  have hleft : ψ ∘ₗ φ = LinearMap.id := by
    -- The inverse from the linear equivalence is a left inverse to `φ`.
    ext x
    change e.symm (e x) = x
    exact e.symm_apply_apply x
  have hright : φ ∘ₗ ψ = LinearMap.id := by
    -- The same inverse is also a right inverse to `φ`.
    ext x
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  have hbaseLeft :
      (LinearMap.baseChange A ψ) ∘ₗ (LinearMap.baseChange A φ) = LinearMap.id := by
    -- Base change preserves the left-inverse identity.
    calc
      (LinearMap.baseChange A ψ) ∘ₗ (LinearMap.baseChange A φ) =
          LinearMap.baseChange A (ψ ∘ₗ φ) := by
            rw [← LinearMap.baseChange_comp]
      _ = LinearMap.baseChange A (LinearMap.id : N →ₗ[R] N) := by
            simpa [hleft]
      _ = LinearMap.id := by
            simpa using (LinearMap.baseChange_id (R := R) (A := A) (M := N))
  have hbaseRight :
      (LinearMap.baseChange A φ) ∘ₗ (LinearMap.baseChange A ψ) = LinearMap.id := by
    -- Base change preserves the right-inverse identity.
    calc
      (LinearMap.baseChange A φ) ∘ₗ (LinearMap.baseChange A ψ) =
          LinearMap.baseChange A (φ ∘ₗ ψ) := by
            rw [← LinearMap.baseChange_comp]
      _ = LinearMap.baseChange A (LinearMap.id : P →ₗ[R] P) := by
            simpa [hright]
      _ = LinearMap.id := by
            simpa using (LinearMap.baseChange_id (R := R) (A := A) (M := P))
  constructor
  · -- A left inverse after base change makes the tensorized map injective.
    exact Function.LeftInverse.injective (f := LinearMap.baseChange A φ) <| by
      intro x
      exact LinearMap.congr_fun hbaseLeft x
  · -- A right inverse after base change makes the tensorized map surjective.
    exact Function.RightInverse.surjective (f := LinearMap.baseChange A φ) <| by
      intro x
      exact LinearMap.congr_fun hbaseRight x

/-- Helper for Remark 15.91.17: localizing a bijective linear map away from an element keeps the
localized map bijective. -/
private theorem localizedAway_bijective_of_bijective_local
    {A : Type*} [CommRing A]
    {N P : Type*} [AddCommMonoid N] [AddCommMonoid P] [Module A N] [Module A P]
    (g : A) (φ : N →ₗ[A] P) (hφ : Function.Bijective φ) :
    Function.Bijective (LocalizedModule.map (Submonoid.powers g) φ) := by
  constructor
  · -- Localization preserves injectivity of linear maps.
    exact LocalizedModule.map_injective (Submonoid.powers g) φ hφ.1
  · -- Localization also preserves surjectivity.
    exact LocalizedModule.map_surjective (Submonoid.powers g) φ hφ.2

/-- Helper for Remark 15.91.17: base change preserves surjectivity of linear maps. -/
private theorem baseChange_surjective_of_surjective_local
    {A : Type u} [CommRing A] [Algebra R A]
    {N P : Type u} [AddCommMonoid N] [AddCommMonoid P] [Module R N] [Module R P]
    (φ : N →ₗ[R] P) (hφ : Function.Surjective φ) :
    Function.Surjective (φ.baseChange A) := by
  intro z
  -- Reduce surjectivity to pure tensors and lift each tensor factor through `φ`.
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro a p
    rcases hφ p with ⟨n, rfl⟩
    exact ⟨a ⊗ₜ[R] n, by simp [LinearMap.baseChange_tmul]⟩
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨w₁, rfl⟩
    rcases hz₂ with ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, by simp⟩

/-- Helper for Remark 15.91.17: in a short exact sequence, the canonical map to cycles is already
bijective before any base change or localization. -/
private theorem moduleCatToCycles_bijective_of_shortExact_local
    (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) :
    Function.Bijective S.moduleCatToCycles := by
  constructor
  · intro x y hxy
    -- Compare the two cycle representatives through their ambient values in `S.X₂`.
    apply hS.moduleCat_injective_f
    simpa [ShortComplex.moduleCatToCycles] using congrArg Subtype.val hxy
  · -- Exactness identifies `moduleCatToCycles` as a surjective map onto the cycles object.
    exact (ShortComplex.exact_iff_surjective_moduleCatToCycles (S := S)).1 hS.exact

/-- Helper for Remark 15.91.17: after any scalar extension, the canonical map to cycles of a short
exact complex stays bijective. -/
private theorem moduleCatToCycles_baseChange_bijective_of_shortExact_local
    {A : Type u} [CommRing A] [Algebra R A]
    (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) :
    Function.Bijective (S.moduleCatToCycles.baseChange A) := by
  -- First identify `moduleCatToCycles` with a linear equivalence, then tensor that equivalence.
  exact
    baseChange_bijective_of_bijective_local
      (R := R)
      (A := A)
      S.moduleCatToCycles
      (moduleCatToCycles_bijective_of_shortExact_local S hS)

/-- Helper for Remark 15.91.17: after localizing away from any element, the canonical map to
cycles of a short exact complex stays bijective. -/
private theorem moduleCatToCycles_localizedAway_bijective_of_shortExact_local
    (g : R) (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact) :
    Function.Bijective
      (LocalizedModule.map (Submonoid.powers g) S.moduleCatToCycles) := by
  -- Localization preserves the linear equivalence already supplied by short exactness.
  exact
    localizedAway_bijective_of_bijective_local
      g
      S.moduleCatToCycles
      (moduleCatToCycles_bijective_of_shortExact_local S hS)

-- Proof sketch: for a glueing pair, the module Cech sequence for `M` is exact in the middle; the
-- canonical map to cycles is therefore surjective by
-- `ShortComplex.exact_iff_surjective_moduleCatToCycles`.
/-- Helper for Remark 15.91.17: a Beauville-Laszlo glueing pair gives middle exactness of the
module Cech sequence for `M`. -/
lemma beauville_laszlo_module_cech_exact_of_glueing_pair
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Exact
      ((beauvilleLaszloModuleCechSequence R' M f).f.hom)
      ((beauvilleLaszloModuleCechSequence R' M f).g.hom) := by
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  have hringExact :
      Function.Exact
        (beauvilleLaszloCechLeftMap (algebraMap R R') f)
        (beauvilleLaszloCechRightMap (algebraMap R R') f) := by
    -- Extract function-level exactness from the ring-side short exact sequence in the
    -- glueing-pair hypothesis.
    simpa [beauvilleLaszloCechSequence] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (beauvilleLaszloCechSequence (algebraMap R R') f)).1 hpair.shortExact.exact
  have hringSurj :
      Function.Surjective (beauvilleLaszloCechRightMap (algebraMap R R') f) := by
    -- The same ring-side short exactness gives surjectivity of the right Cech map.
    simpa [beauvilleLaszloCechSequence] using hpair.shortExact.moduleCat_surjective_g
  have htensorExact :
      Function.Exact
        ((beauvilleLaszloModuleCechTensorImage R' M f).f.hom)
        ((beauvilleLaszloModuleCechTensorImage R' M f).g.hom) := by
    -- Tensoring with `M` preserves middle exactness because the ring sequence is right exact.
    simpa [beauvilleLaszloModuleCechTensorImage, ModuleCat.hom_whiskerLeft] using
      (lTensor_exact M hringExact hringSurj)
  change Function.Exact
    (beauvilleLaszloModuleCechAlpha R' M f)
    (beauvilleLaszloModuleCechBeta R' M f)
  -- Route correction: prove exactness on the tensor-image model first, then transport it through
  -- the canonical left and middle isomorphisms of the displayed Cech sequence.
  refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
  · simpa [beauvilleLaszloModuleCechSequence] using
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
    -- Transport the tensor-image preimage back to the displayed module Cech complex.
    have hmiddle_injective : Function.Injective middleIso.inv.hom := by
      intro a b hab
      calc
        a = middleIso.hom.hom (middleIso.inv.hom a) := by
          simpa using (middleIso.inv_hom_id_apply a).symm
        _ = middleIso.hom.hom (middleIso.inv.hom b) := by
          simpa using congrArg middleIso.hom.hom hab
        _ = b := by
          simpa using middleIso.inv_hom_id_apply b
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

-- Proof sketch: Theorem `15.91.16` identifies the single-localization glueing datum `Can(M)` with
-- the Beauville-Laszlo datum of `\tilde M = H^0(Can(M))`, so `\tilde M` is glueable for the
-- pair `(R → R', f)`.
/-- Remark 15.91.17: if `(R → R', f)` is a Beauville-Laszlo glueing pair, then the replacement
module `\tilde M = H^0(Can(M))`, i.e. the cycles object
`(beauvilleLaszloModuleCechSequence R' M f).cycles`, is glueable. -/
@[stacks 0BP9]
theorem beauvilleLaszloModuleCechH0_shortExact
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    (beauvilleLaszloModuleCechSequence R'
      (beauvilleLaszloModuleCechSequence R' M f).cycles
      f).ShortExact := by
  have hExact :
      (beauvilleLaszloModuleCechSequence R'
        (beauvilleLaszloModuleCechSequence R' M f).cycles
        f).Exact := by
    -- The replacement module already satisfies the middle-exactness part of the glueing criterion.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact
      beauville_laszlo_module_cech_exact_of_glueing_pair
        (R := R)
        (R' := R')
        (M := (beauvilleLaszloModuleCechSequence R' M f).cycles)
        (f := f)
        hpair
  -- Route correction: the remaining proof should transport `15.91.16.1` along the owner-level
  -- cycles/H⁰ bridge and the two comparison isomorphisms for the first and second projections.
  -- The middle exactness component is already available; only the branch isomorphism transport
  -- needed to prove `mono_f` and `epi_g` remains.
  -- TODO: compare the cycles object of `Can(M)` with the public `H⁰` owner for the single
  -- Beauville-Laszlo glueing datum and transport `15.91.16.1` back to the displayed Cech model.
  let _ := hExact
  sorry

-- Proof sketch: Theorem `15.91.16` says the canonical map `M → H^0(Can(M))` reconstructs the
-- same Beauville-Laszlo glueing datum after tensoring with `R'`.
/-- The canonical map `M → \tilde M = H^0(Can(M))`, namely
`(beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles`, becomes bijective after base
change to `R'`. -/
theorem beauvilleLaszloModuleCechH0Map_baseChange_bijective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      (((beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles).baseChange R') := by
  let S := beauvilleLaszloModuleCechSequence R' M f
  have hExact : S.Exact := by
    -- Middle exactness of the Cech complex already forces surjectivity onto the cycles object.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact beauville_laszlo_module_cech_exact_of_glueing_pair (R := R) (R' := R') (M := M)
      (f := f) hpair
  have hsurj : Function.Surjective S.moduleCatToCycles := by
    exact (ShortComplex.exact_iff_surjective_moduleCatToCycles (S := S)).1 hExact
  have hbaseSurj : Function.Surjective (S.moduleCatToCycles.baseChange R') := by
    -- Base change preserves the surjective half of the replacement map.
    exact
      baseChange_surjective_of_surjective_local
        (R := R)
        (A := R')
        S.moduleCatToCycles
        hsurj
  -- Route correction: the intended proof is still the source-faithful transport from the public
  -- first-branch comparison map. The surjective half is now verified, and only the injective
  -- transport from the public base-change comparison remains.
  -- TODO: identify the tensorized map on `moduleCatToCycles` with the left comparison map from
  -- `15.91.16.3` after transporting from the single glueing datum `Can(M)` to the displayed
  -- cycles model.
  let _ := hbaseSurj
  sorry

-- Proof sketch: The same Beauville-Laszlo equivalence identifies the localized components of
-- `Can(M)` and `Can(\tilde M)`, so localizing the canonical map away from `f` gives a bijection.
/-- The canonical map `M → \tilde M` from Remark 15.91.17 becomes bijective after localizing away
from `f`. -/
theorem beauvilleLaszloModuleCechH0Map_localizedAway_bijective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Bijective
      (LocalizedModule.map
        (Submonoid.powers f)
        (beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles) := by
  let S := beauvilleLaszloModuleCechSequence R' M f
  have hExact : S.Exact := by
    -- The source map to cycles is already surjective before localization.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact beauville_laszlo_module_cech_exact_of_glueing_pair (R := R) (R' := R') (M := M)
      (f := f) hpair
  have hsurj : Function.Surjective S.moduleCatToCycles := by
    exact (ShortComplex.exact_iff_surjective_moduleCatToCycles (S := S)).1 hExact
  have hlocalizedSurj :
      Function.Surjective
        (LocalizedModule.map (Submonoid.powers f) S.moduleCatToCycles) := by
    -- Localizing away from `f` preserves the surjective half of the replacement map.
    exact
      LocalizedModule.map_surjective
        (Submonoid.powers f)
        S.moduleCatToCycles
        hsurj
  -- Route correction: the localized comparison will factor through the quotient-by-torsion owner
  -- from `15.91.16.2`, together with the local away-localization equivalence added above.
  -- The surjective half is done; only injectivity across the localized quotient comparison
  -- remains.
  -- TODO: transport the left map in `15.91.16.2` to the second projection
  -- `H⁰(Can(M)) → M_f`, then localize away from `f` so the `f^∞`-torsion quotient disappears.
  let _ := hlocalizedSurj
  sorry

/-- Remark 15.91.17: for a Beauville-Laszlo glueing pair, the canonical map `M → \tilde M` is
surjective. -/
@[stacks 0BP9]
theorem beauvilleLaszloModuleCechH0Map_surjective
    (hpair : IsBeauvilleLaszloGlueingPairAlong (algebraMap R R') f) :
    Function.Surjective (beauvilleLaszloModuleCechSequence R' M f).moduleCatToCycles := by
  -- The canonical map to cycles is surjective exactly when the module Cech complex is exact in
  -- the middle, so we reuse the exactness theorem from Lemma `15.91.10`.
  have hExact : (beauvilleLaszloModuleCechSequence R' M f).Exact := by
    -- Convert the function-level middle exactness into the `ShortComplex.Exact` owner used by
    -- the cycles API.
    rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact]
    exact
      beauville_laszlo_module_cech_exact_of_glueing_pair
        (R := R) (R' := R') (M := M) (f := f) hpair
  exact
    (ShortComplex.exact_iff_surjective_moduleCatToCycles
      (S := beauvilleLaszloModuleCechSequence R' M f)).1 hExact

end
