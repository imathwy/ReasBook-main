import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_24_1

open CategoryTheory LinearMap LocalizedModule IsLocalizedModule

universe u v

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

local notation "Away" => LocalizedModule.Away

/-- Localizing an `R`-linear map away from `a`. -/
noncomputable abbrev awayLocalizeLinearMap
    {M : Type v} {N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : R) (g : M →ₗ[R] N) :
    Away a M →ₗ[R] Away a N :=
  (LocalizedModule.map (Submonoid.powers a) g).restrictScalars R

/-- Localizing a linear equivalence away from `a`. -/
noncomputable abbrev awayLocalizeLinearEquiv
    {M : Type v} {N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) :
    Away a M ≃ₗ[R] Away a N :=
  LinearEquiv.ofLinear (awayLocalizeLinearMap a e.toLinearMap)
    (awayLocalizeLinearMap a e.symm.toLinearMap)
    (by
      ext x
      induction x using LocalizedModule.induction_on with
      | _ y s =>
          simp [awayLocalizeLinearMap])
    (by
      ext x
      induction x using LocalizedModule.induction_on with
      | _ y s =>
          simp [awayLocalizeLinearMap])

instance moduleCat_away_module
    (a : R) (M : ModuleCat.{max u v} (Localization.Away a)) : Module R ↥M :=
  Module.restrictScalars R (Localization.Away a) M

instance moduleCat_away_isScalarTower
    (a : R) (M : ModuleCat.{max u v} (Localization.Away a)) :
    IsScalarTower R (Localization.Away a) ↥M :=
  IsScalarTower.restrictScalars R (Localization.Away a) M

/-- The cocycle condition for pairwise overlap isomorphisms in an affine localization gluing datum
for modules. In this source-facing skeleton the triple-overlap compatibility is recorded as a proof
field, while the primitive public data remain the actual `R_(fᵢ)`-modules and `R_(fᵢfⱼ)`-linear
overlap isomorphisms. -/
noncomputable abbrev awayModuleGlueingTripleOverlapHom12
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j)))
    (i j k : Fin n) :
    Away (f i * f j * f k) (localModule i) ≃ₗ[R] Away (f i * f j * f k) (localModule j) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    ((awayMulLinearEquiv (f i * f j) (f k) (localModule i)).symm.trans
      ((awayLocalizeLinearEquiv (f k) ((overlapIso i j).toLinearEquiv.restrictScalars R)).trans
        (awayMulLinearEquiv (f i * f j) (f k) (localModule j))))

noncomputable abbrev awayModuleGlueingTripleOverlapHom23
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j)))
    (i j k : Fin n) :
    Away (f i * f j * f k) (localModule j) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
  let left :
      Away (f i * f j * f k) (localModule j) ≃ₗ[R] Away (f j * f k * f i) (localModule j) :=
    awayEqLinearEquiv (localModule j) (by ring)
  let center :
      Away (f j * f k * f i) (localModule j) ≃ₗ[R] Away (f j * f k * f i) (localModule k) :=
    (awayMulLinearEquiv (f j * f k) (f i) (localModule j)).symm.trans
      ((awayLocalizeLinearEquiv (f i) ((overlapIso j k).toLinearEquiv.restrictScalars R)).trans
        (awayMulLinearEquiv (f j * f k) (f i) (localModule k)))
  let right :
      Away (f j * f k * f i) (localModule k) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
    awayEqLinearEquiv (localModule k) (by ring)
  left.trans (center.trans right)

noncomputable abbrev awayModuleGlueingTripleOverlapHom13
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j)))
    (i j k : Fin n) :
    Away (f i * f j * f k) (localModule i) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
  let left :
      Away (f i * f j * f k) (localModule i) ≃ₗ[R] Away (f i * f k * f j) (localModule i) :=
    awayEqLinearEquiv (localModule i) (by ring)
  let center :
      Away (f i * f k * f j) (localModule i) ≃ₗ[R] Away (f i * f k * f j) (localModule k) :=
    (awayMulLinearEquiv (f i * f k) (f j) (localModule i)).symm.trans
      ((awayLocalizeLinearEquiv (f j) ((overlapIso i k).toLinearEquiv.restrictScalars R)).trans
        (awayMulLinearEquiv (f i * f k) (f j) (localModule k)))
  let right :
      Away (f i * f k * f j) (localModule k) ≃ₗ[R] Away (f i * f j * f k) (localModule k) :=
    awayEqLinearEquiv (localModule k) (by ring)
  left.trans (center.trans right)

def AwayModuleGlueingCocycleCondition
    (f : Fin n → R) (localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i)))
    (overlapIso : ∀ i j,
      ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule i)) ≅
        ModuleCat.of (Localization.Away (f i * f j))
          (Away (f i * f j) (localModule j))) :
    Prop :=
  ∀ i j k : Fin n,
    (awayModuleGlueingTripleOverlapHom12 f localModule overlapIso i j k).trans
      (awayModuleGlueingTripleOverlapHom23 f localModule overlapIso i j k) =
    awayModuleGlueingTripleOverlapHom13 f localModule overlapIso i j k

/-- A finite module gluing on the standard cover defined by `f`. The primitive local pieces are
actual `R_(fᵢ)`-modules, and the overlap data are actual `R_(fᵢfⱼ)`-linear isomorphisms. -/
structure AwayModuleGlueing (f : Fin n → R) where
  localModule : ∀ i, ModuleCat.{max u v} (Localization.Away (f i))
  overlapIso : ∀ i j,
    ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (localModule i)) ≅
      ModuleCat.of (Localization.Away (f i * f j))
        (Away (f i * f j) (localModule j))
  cocycle : AwayModuleGlueingCocycleCondition f localModule overlapIso

namespace AwayModuleGlueing

variable {f : Fin n → R} (glue : AwayModuleGlueing f)

/-- Each local piece is already localized away from its defining element. -/
instance localizedInstance (glue : AwayModuleGlueing f) (i : Fin n) :
    IsLocalizedModule.Away (f i) (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i) := by
  simpa using
    (isLocalizedModule_id (Submonoid.powers (f i)) (glue.localModule i) (Localization.Away (f i)))

/-- The compatibility map whose kernel is the glued module. Its `(i,j)`-component is
`m_i/1 - ψ_{ij}^{-1}(m_j/1)`. -/
noncomputable def compatibilityMap (glue : AwayModuleGlueing f) :
    (∀ i : Fin n, glue.localModule i) →ₗ[R]
      ∀ i : Fin n, ∀ j : Fin n, Away (f i * f j) (glue.localModule i) :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) (glue.localModule i)).comp
        (LinearMap.proj i) -
      (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm.toLinearMap).comp
        ((LocalizedModule.mkLinearMap (Submonoid.powers (f i * f j)) (glue.localModule j)).comp
          (LinearMap.proj j))

/-- The glued module attached to an affine localization gluing datum. -/
def gluedModule (glue : AwayModuleGlueing f) : Submodule R (∀ i : Fin n, glue.localModule i) :=
  LinearMap.ker glue.compatibilityMap

/-- The natural projection from the glued module to the `i`-th local module, viewed over `R`. -/
def projection (glue : AwayModuleGlueing f) (i : Fin n) : glue.gluedModule →ₗ[R] glue.localModule i :=
  (LinearMap.proj i).comp glue.gluedModule.subtype

/-- The localized projection map in the source-facing category of `R_(fᵢ)`-modules. -/
noncomputable def localizedProjection (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) glue.gluedModule →ₗ[Localization.Away (f i)] glue.localModule i :=
  (IsLocalizedModule.map (Submonoid.powers (f i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (f i)) glue.gluedModule)
      (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i)
      (glue.projection i)).extendScalarsOfIsLocalization
    (Submonoid.powers (f i)) (Localization.Away (f i))

/-- Helper for Lemma 10.24.5: every power of `f i` already acts invertibly on the `i`-th local
piece. -/
theorem localModule_powers_isUnit (glue : AwayModuleGlueing f) (i : Fin n) :
    ∀ x : Submonoid.powers (f i),
      IsUnit (algebraMap R (Module.End R (glue.localModule i)) x) := by
  -- The `i`-th local piece is itself an `f i`-localization, so every power of `f i` acts by a
  -- unit endomorphism.
  intro x
  exact
    IsLocalizedModule.map_units
      (f := (LinearMap.id : glue.localModule i →ₗ[R] glue.localModule i)) x

/-- Helper for Lemma 10.24.5: collapsing the trivial localization on the `i`-th local piece. -/
noncomputable abbrev localModuleAwayEquiv (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (glue.localModule i) ≃ₗ[R] glue.localModule i :=
  awayLocalizedByUnitEquiv (f i) (glue.localModule i) (glue.localModule_powers_isUnit i)

/-- Helper for Lemma 10.24.5: the unit-case kernel is determined by its distinguished coordinate. -/
theorem standard_kernel_eq_family_of_coordinate
    (glue : AwayModuleGlueing f) (i : Fin n)
    (x : LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f)) :
    awayLocalizationFamilyMap (glue.localModule i) f
      (glue.localModuleAwayEquiv i (x.1 i)) = x.1 := by
  let e₀ := glue.localModuleAwayEquiv i
  have hExact :=
    away_localization_glueing_exact_of_isUnit
      (M := glue.localModule i) f i (glue.localModule_powers_isUnit i)
  -- Exactness identifies the standard kernel with the range of the family map.
  have hxrange :
      x.1 ∈ LinearMap.range (awayLocalizationFamilyMap (glue.localModule i) f) := by
    rw [← Function.Exact.linearMap_ker_eq hExact.2]
    exact x.2
  rw [LinearMap.mem_range] at hxrange
  rcases hxrange with ⟨m, hm⟩
  -- The distinguished coordinate recovers the preimage because `f i` is already invertible.
  have hm_coord :
      e₀ ((awayLocalizationFamilyMap (glue.localModule i) f m) i) = e₀ (x.1 i) := by
    exact congrArg (fun z ↦ e₀ (z i)) hm
  have hm_self : e₀ ((awayLocalizationFamilyMap (glue.localModule i) f m) i) = m := by
    simp [AwayModuleGlueing.localModuleAwayEquiv, awayLocalizationFamilyMap, e₀]
  have hm_eq : m = e₀ (x.1 i) := hm_self.symm.trans hm_coord
  simpa [hm_eq] using hm

/-- Helper for Lemma 10.24.5: the distinguished coordinate map is bijective on the standard
unit-case kernel attached to `glue.localModule i`. -/
noncomputable abbrev standardKernelCoordinate
    (glue : AwayModuleGlueing f) (i : Fin n) :
    LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) →ₗ[R]
      glue.localModule i :=
  (glue.localModuleAwayEquiv i).toLinearMap.comp
    ((LinearMap.proj i).comp
      (LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f)).subtype)

/-- Helper for Lemma 10.24.5: the standard unit-case kernel coordinate map is bijective. -/
theorem standard_kernel_coordinate_bijective
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Function.Bijective (glue.standardKernelCoordinate i) := by
  let e₀ := glue.localModuleAwayEquiv i
  constructor
  · intro x y hxy
    -- Two kernel elements agree once their distinguished coordinates agree.
    apply Subtype.ext
    have hcoord : e₀ (x.1 i) = e₀ (y.1 i) := by
      simpa [AwayModuleGlueing.standardKernelCoordinate, e₀] using hxy
    calc
      x.1 = awayLocalizationFamilyMap (glue.localModule i) f (e₀ (x.1 i)) := by
        symm
        exact glue.standard_kernel_eq_family_of_coordinate i x
      _ = awayLocalizationFamilyMap (glue.localModule i) f (e₀ (y.1 i)) := by rw [hcoord]
      _ = y.1 := glue.standard_kernel_eq_family_of_coordinate i y
  · intro m
    let y := awayLocalizationFamilyMap (glue.localModule i) f m
    have hExact :=
      away_localization_glueing_exact_of_isUnit
        (M := glue.localModule i) f i (glue.localModule_powers_isUnit i)
    have hyker : y ∈ LinearMap.ker (awayLocalizationCompatibilityMap (M := glue.localModule i) f) := by
      rw [Function.Exact.linearMap_ker_eq hExact.2]
      exact LinearMap.mem_range_self _ m
    refine ⟨⟨y, hyker⟩, ?_⟩
    -- Evaluating the distinguished coordinate collapses the trivial localization back to `m`.
    simp [AwayModuleGlueing.standardKernelCoordinate, AwayModuleGlueing.localModuleAwayEquiv,
      awayLocalizationFamilyMap, y]

/-- Helper for Lemma 10.24.5: after localizing the `j`-th local piece once more away from `f i`,
the overlap isomorphism identifies it with the `j`-th standard localization of the `i`-th piece. -/
noncomputable abbrev local_piece_overlap_equiv
    (glue : AwayModuleGlueing f) (i j : Fin n) :
    Away (f i) (glue.localModule j) ≃ₗ[R] Away (f j) (glue.localModule i) :=
  -- First reinsert the trivial `f j`-localization on the `j`-piece, then swap the localization
  -- order, transport across the overlap isomorphism, and finally collapse the trivial
  -- `f i`-localization on the `i`-piece.
  (awayLocalizeLinearEquiv (f i) (glue.localModuleAwayEquiv j).symm).trans
    ((awayMulLinearEquiv (f j) (f i) (glue.localModule j)).trans
      ((awayEqLinearEquiv (glue.localModule j) (by rw [mul_comm])).trans
        ((((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm).trans
          (((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm).trans
            (awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i))))))

/-- Helper for Lemma 10.24.5: localizing the middle product away from `f i` acts coordinatewise on
the family of local pieces before the overlap identifications are applied. -/
noncomputable abbrev localized_middle_pi_map
    (glue : AwayModuleGlueing f) (i : Fin n) :
    (∀ j : Fin n, glue.localModule j) →ₗ[R] ∀ j : Fin n, Away (f i) (glue.localModule j) :=
  LinearMap.pi fun j ↦
    (LocalizedModule.mkLinearMap (.powers (f i)) (glue.localModule j)).comp (LinearMap.proj j)

/-- Helper for Lemma 10.24.5: after localizing the middle product away from `f i`, the pairwise
overlap transports identify it with the standard middle term for `glue.localModule i`. -/
noncomputable abbrev localized_middle_comparison
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (∀ j : Fin n, glue.localModule j) ≃ₗ[R]
      ∀ j : Fin n, Away (f j) (glue.localModule i) :=
  -- First compare the localized family with the coordinatewise localizations, then transport each
  -- coordinate through the corresponding overlap equivalence.
  (IsLocalizedModule.linearEquiv (.powers (f i))
      (LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
      (glue.localized_middle_pi_map i)).trans
    (LinearEquiv.piCongrRight fun j ↦ glue.local_piece_overlap_equiv i j)

/-- Helper for Lemma 10.24.5: the raw middle comparison sends a canonical localized family to the
family of its coordinatewise canonical localizations. -/
theorem localized_middle_pi_comparison_apply_mk_one
    (glue : AwayModuleGlueing f) (i j : Fin n) (x : ∀ j : Fin n, glue.localModule j) :
    ((IsLocalizedModule.linearEquiv (.powers (f i))
        (LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
        (glue.localized_middle_pi_map i))
      (LocalizedModule.mk x 1)) j =
      LocalizedModule.mk (x j) 1 := by
  -- Evaluate the universal-property comparison on the canonical localized family element.
  simpa [AwayModuleGlueing.localized_middle_pi_map, LinearMap.comp_apply] using
    congrFun
      (IsLocalizedModule.linearEquiv_apply
        (S := .powers (f i))
        (f := LocalizedModule.mkLinearMap (.powers (f i)) (∀ j : Fin n, glue.localModule j))
        (g := glue.localized_middle_pi_map i)
        x)
      j

/-- Helper for Lemma 10.24.5: the middle comparison sends a canonical localized family to the
family obtained by applying the pairwise overlap identifications coordinatewise. -/
theorem localized_middle_comparison_apply_mk_one
    (glue : AwayModuleGlueing f) (i j : Fin n) (x : ∀ j : Fin n, glue.localModule j) :
    (glue.localized_middle_comparison i (LocalizedModule.mk x 1)) j =
      glue.local_piece_overlap_equiv i j (LocalizedModule.mk (x j) 1) := by
  -- The packaged comparison is the raw coordinatewise localization map followed by the overlap
  -- equivalence on the `j`-th coordinate.
  simp only [AwayModuleGlueing.localized_middle_comparison, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply]
  rw [glue.localized_middle_pi_comparison_apply_mk_one]

/-- Helper for Lemma 10.24.5: the target-side component comparison first rewrites the iterated
localization on the `j`-piece into the common triple overlap. -/
theorem localized_target_component_domain_eq
    (i j k : Fin n) :
    (f j * f k) * f i = f i * f j * f k := by
  -- Reorder the three localization factors into the source-proof triple-overlap order.
  calc
    (f j * f k) * f i = f j * (f k * f i) := by rw [mul_assoc]
    _ = f j * (f i * f k) := by rw [mul_comm (f k) (f i)]
    _ = (f j * f i) * f k := by rw [← mul_assoc]
    _ = (f i * f j) * f k := by rw [mul_comm (f j) (f i)]
    _ = f i * f j * f k := by rfl

/-- Helper for Lemma 10.24.5: the target-side component comparison ends by viewing the common
triple overlap as a localization of the `i`-piece away from `f_j f_k`. -/
theorem localized_target_component_codomain_eq
    (i j k : Fin n) :
    f i * f j * f k = f i * (f j * f k) := by
  -- This is just the associativity rebracketing needed for `awayMulLinearEquiv`.
  rw [mul_assoc]

/-- Helper for Lemma 10.24.5: after localizing the `(j,k)` target component once more away from
`f i`, the cocycle datum transports it to the standard `(j,k)` target component on the fixed
`i`-piece. -/
noncomputable abbrev localized_target_component_equiv
    (glue : AwayModuleGlueing f) (i j k : Fin n) :
    Away (f i) (Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
      Away (f j * f k) (glue.localModule i) :=
  -- Move to the triple overlap on the `j`-piece, transport across the cocycle comparison to the
  -- `i`-piece, and then collapse the trivial `f i`-localization on the fixed local piece.
  (awayMulLinearEquiv (f j * f k) (f i) (glue.localModule j)).trans
    ((awayEqLinearEquiv (glue.localModule j)
        (AwayModuleGlueing.localized_target_component_domain_eq (f := f) i j k)).trans
      (((awayModuleGlueingTripleOverlapHom12 f glue.localModule glue.overlapIso i j k).symm).trans
        ((awayEqLinearEquiv (glue.localModule i)
            (AwayModuleGlueing.localized_target_component_codomain_eq (f := f) i j k)).trans
          (((awayMulLinearEquiv (f i) (f j * f k) (glue.localModule i)).symm).trans
            (awayLocalizeLinearEquiv (f j * f k) (glue.localModuleAwayEquiv i))))))

/-- Helper for Lemma 10.24.5: localizing a linear equivalence away from `a` sends a canonical
generator to the canonical generator of its image. -/
theorem awayLocalizeLinearEquiv_apply_mk_one
    {M : Type v} {N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) (x : M) :
    awayLocalizeLinearEquiv a e (LocalizedModule.mk x 1) = LocalizedModule.mk (e x) 1 := by
  -- The localized equivalence is defined by applying `e` under the localization functor.
  simpa only [awayLocalizeLinearEquiv, awayLocalizeLinearMap] using
    (LocalizedModule.map_mk (.powers a) e.toLinearMap x (1 : Submonoid.powers a))

/-- Helper for Lemma 10.24.5: the inverse localized equivalence sends a canonical generator to the
canonical generator of its inverse image. -/
theorem awayLocalizeLinearEquiv_symm_apply_mk_one
    {M : Type v} {N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (a : R) (e : M ≃ₗ[R] N) (x : N) :
    (awayLocalizeLinearEquiv a e).symm (LocalizedModule.mk x 1) =
      LocalizedModule.mk (e.symm x) 1 := by
  -- Apply the forward localized equivalence to reduce the inverse formula to the canonical
  -- generator computation for `e.symm`.
  apply (awayLocalizeLinearEquiv a e).injective
  rw [awayLocalizeLinearEquiv_apply_mk_one]
  simp

/-- Helper for Lemma 10.24.5: localizing an invertible endomorphism remains invertible. -/
theorem localizedModuleEnd_isUnit
    (S : Submonoid R) {N : Type v} [AddCommGroup N] [Module R N] {r : R}
    (h : IsUnit (algebraMap R (Module.End R N) r)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule S N)) r) := by
  -- The localized endomorphism is just scalar multiplication by the same ring element on the
  -- localized module, so a unit endomorphism stays invertible after localization.
  let localizedEnd :
      Module.End R (LocalizedModule S N) :=
    IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N) (LocalizedModule.mkLinearMap S N)
      (algebraMap R (Module.End R N) r)
  have hbij : Function.Bijective localizedEnd := by
    have hbij₀ : Function.Bijective (algebraMap R (Module.End R N) r) :=
      (Module.End.isUnit_iff _).mp h
    constructor
    · exact
        IsLocalizedModule.map_injective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap R (Module.End R N) r) hbij₀.1
    · exact
        IsLocalizedModule.map_surjective (S := S) (f := LocalizedModule.mkLinearMap S N)
          (g := LocalizedModule.mkLinearMap S N)
          (h := algebraMap R (Module.End R N) r) hbij₀.2
  have hEq :
      localizedEnd = algebraMap R (Module.End R (LocalizedModule S N)) r := by
    ext x
    induction x using LocalizedModule.induction_on with
    | _ m s =>
        simp [localizedEnd, IsLocalizedModule.map_LocalizedModules, LocalizedModule.smul'_mk]
  rw [← hEq]
  exact (Module.End.isUnit_iff _).2 hbij

/-- Helper for Lemma 10.24.5: if `r` divides the away-localizing element `x`, then multiplication
by `r` is invertible on `Away x M`. -/
theorem away_module_end_isUnit_of_dvd
    (M : Type v) [AddCommGroup M] [Module R M] (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (Away x M)) r) := by
  -- Away localizations invert every divisor of the distinguished element, and the induced action
  -- on the localized module is obtained by scalar multiplication.
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (Away x M) :=
    Algebra.lsmul R R (Away x M)
  simpa [Algebra.smul_def] using h'.map lsmulAway

/-- Helper for Lemma 10.24.5: reindexing an away localization along an equality fixes canonical
generators. -/
theorem awayEqLinearEquiv_apply_mk_one
    (M : Type v) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) (m : M) :
    awayEqLinearEquiv M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  -- Equality transport is definitionally trivial on canonical localization elements.
  subst h
  rfl

/-- Helper for Lemma 10.24.5: the inverse equality transport also fixes canonical generators. -/
theorem awayEqLinearEquiv_symm_apply_mk_one
    (M : Type v) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) (m : M) :
    (awayEqLinearEquiv M h).symm (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  -- Equality transport is definitional, so its inverse is also trivial on canonical generators.
  subst h
  rfl

/-- Helper for Lemma 10.24.5: equality transports with the same endpoints agree. -/
theorem awayEqLinearEquiv_congr
    (M : Type v) [AddCommGroup M] [Module R M] {a b : R} (h₁ h₂ : a = b) :
    awayEqLinearEquiv M h₁ = awayEqLinearEquiv M h₂ := by
  -- Both transports are obtained by rewriting along the same equality, so proof irrelevance
  -- identifies them.
  cases h₁
  cases h₂
  rfl

/-- Helper for Lemma 10.24.5: the inverse equality transport is transport along the reversed
equality. -/
theorem awayEqLinearEquiv_symm_eq
    (M : Type v) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) :
    (awayEqLinearEquiv M h).symm = awayEqLinearEquiv M h.symm := by
  -- After rewriting the equality to reflexivity, both sides become the identity equivalence.
  subst h
  rfl

/-- Helper for Lemma 10.24.5: the iterated-localization comparison sends a double canonical
generator to the corresponding direct-localization generator. -/
theorem awayMulLinearEquiv_apply_mk_mk
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    (awayMulLinearEquiv a b M) (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk m 1 := by
  -- The universal-property comparison from iterated localization to direct localization is
  -- normalized on `m/1/1`.
  simpa [awayMulLinearEquiv, iteratedLocalizedModuleMkLinearMap, LinearMap.comp_apply] using
    (IsLocalizedModule.linearEquiv_apply
      (S := .powers b ⊔ .powers a)
      (f := iteratedLocalizedModuleMkLinearMap (.powers b) (.powers a) M)
      (g := LocalizedModule.mkLinearMap (.powers (a * b)) M)
      m)

/-- Helper for Lemma 10.24.5: the inverse iterated-localization comparison sends a canonical
generator to the corresponding double canonical generator. -/
theorem awayMulLinearEquiv_symm_apply_mk_one
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    (awayMulLinearEquiv a b M).symm (LocalizedModule.mk m 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
  -- Apply the forward comparison to reduce the inverse-normalization claim to the canonical
  -- generator formula already established above.
  apply (awayMulLinearEquiv a b M).injective
  simpa using (awayMulLinearEquiv_apply_mk_mk a b M m).symm

/-- Helper for Lemma 10.24.5: the canonical direct localization map from `Away a M` to
`Away (ab) M`. -/
theorem away_direct_localize_powers_isUnit
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] :
    ∀ x : Submonoid.powers a,
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) x) := by
  -- Powers of `a` divide `ab`, hence they already act by units on `Away (ab) M`.
  intro x
  rcases (Submonoid.mem_powers_iff x.1 a).mp x.2 with ⟨n, hn⟩
  have ha :
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) a) :=
    away_module_end_isUnit_of_dvd M (a * b) a (dvd_mul_right _ _)
  simpa [map_pow, ← hn] using ha.pow n

/-- Helper for Lemma 10.24.5: the canonical direct localization map from `Away a M` to
`Away (ab) M`. -/
noncomputable abbrev awayDirectLocalizeLinearMap
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] :
    Away a M →ₗ[R] Away (a * b) M :=
  LocalizedModule.lift (.powers a)
    (LocalizedModule.mkLinearMap (.powers (a * b)) M)
    (away_direct_localize_powers_isUnit a b M)

/-- Helper for Lemma 10.24.5: the direct localization map sends a canonical numerator to the
same canonical numerator in `Away (ab) M`. -/
theorem awayDirectLocalizeLinearMap_apply_mk_one
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] (m : M) :
    awayDirectLocalizeLinearMap a b M (LocalizedModule.mk m 1) =
      (LocalizedModule.mk m 1 : Away (a * b) M) := by
  -- This is the universal-property map out of the `a`-localization applied to the numerator `m`.
  simpa only [awayDirectLocalizeLinearMap] using
    (LocalizedModule.lift_mk_one
      (S := .powers a)
      (g := LocalizedModule.mkLinearMap (.powers (a * b)) M)
      (h := away_direct_localize_powers_isUnit a b M)
      m)

/-- Helper for Lemma 10.24.5: the iterated-localization comparison on a numerator already lying
in `Away a M` is the canonical direct localization map. -/
theorem awayMulLinearEquiv_apply_mk_one_of_away
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] (x : Away a M) :
    (awayMulLinearEquiv a b M) (LocalizedModule.mk x 1) =
      awayDirectLocalizeLinearMap a b M x := by
  -- Compare the two maps from `Away a M` to `Away (ab) M` after precomposing with the canonical
  -- localization map on `M`; the comparison reduces to the already-known `m/1/1` formula.
  have hmap :
      (awayMulLinearEquiv a b M).toLinearMap.comp
          (LocalizedModule.mkLinearMap (.powers b) (Away a M)) =
        awayDirectLocalizeLinearMap a b M := by
    apply IsLocalizedModule.ext
      (S := .powers a)
      (f := LocalizedModule.mkLinearMap (.powers a) M)
      (map_unit := away_direct_localize_powers_isUnit a b M)
    ext m
    simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
    calc
      (awayMulLinearEquiv a b M) (LocalizedModule.mk (LocalizedModule.mk m 1) 1)
          = (LocalizedModule.mk m 1 : Away (a * b) M) := by
              simpa using awayMulLinearEquiv_apply_mk_mk a b M m
      _ = awayDirectLocalizeLinearMap a b M (LocalizedModule.mk m 1) := by
            symm
            exact awayDirectLocalizeLinearMap_apply_mk_one a b M m
  exact LinearMap.congr_fun hmap x

/-- Helper for Lemma 10.24.5: the inverse iterated-localization comparison sends the canonical
direct-localization image of `x : Away a M` back to `x/1`. -/
theorem awayMulLinearEquiv_symm_apply_mk_one_of_away
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] (x : Away a M) :
    (awayMulLinearEquiv a b M).symm (awayDirectLocalizeLinearMap a b M x) =
      (LocalizedModule.mk x 1 : Away b (Away a M)) := by
  -- Apply the forward comparison to the candidate inverse image and use the forward normal form.
  exact (awayMulLinearEquiv a b M).injective <| by
    rw [LinearEquiv.apply_symm_apply]
    exact (awayMulLinearEquiv_apply_mk_one_of_away a b M x).symm

/-- Helper for Lemma 10.24.5: direct localizing away from `a`, then away from `c`, is the same
as direct localizing once away from `a(bc)` after the standard reassociation transport. -/
theorem awayDirectLocalizeLinearMap_left_assoc
    (a b c : R) (M : Type v) [AddCommGroup M] [Module R M] :
    ((awayEqLinearEquiv M (show a * b * c = a * (b * c) by rw [mul_assoc])).toLinearMap).comp
        ((awayDirectLocalizeLinearMap (a * b) c M).comp
          (awayDirectLocalizeLinearMap a b M)) =
      awayDirectLocalizeLinearMap a (b * c) M := by
  -- Compare both localization routes after precomposing with `M → Away a M`; on `m/1`, every
  -- map becomes the canonical numerator `m/1` in the target localization.
  apply IsLocalizedModule.ext
    (S := .powers a)
    (f := LocalizedModule.mkLinearMap (.powers a) M)
    (map_unit := away_direct_localize_powers_isUnit a (b * c) M)
  ext m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  calc
    (awayEqLinearEquiv M (show a * b * c = a * (b * c) by rw [mul_assoc]))
        (awayDirectLocalizeLinearMap (a * b) c M
          (awayDirectLocalizeLinearMap a b M (LocalizedModule.mk m 1)))
        = (awayEqLinearEquiv M (show a * b * c = a * (b * c) by rw [mul_assoc]))
            (LocalizedModule.mk m 1 : Away ((a * b) * c) M) := by
              rw [awayDirectLocalizeLinearMap_apply_mk_one, awayDirectLocalizeLinearMap_apply_mk_one]
    _ = (LocalizedModule.mk m 1 : Away (a * (b * c)) M) := by
          exact awayEqLinearEquiv_apply_mk_one M (by rw [mul_assoc]) m
    _ = awayDirectLocalizeLinearMap a (b * c) M (LocalizedModule.mk m 1) := by
          symm
          exact awayDirectLocalizeLinearMap_apply_mk_one a (b * c) M m

/-- Helper for Lemma 10.24.5: the right-branch localization order also collapses to the same
direct localization after the explicit permutation and reassociation transports. -/
theorem awayDirectLocalizeLinearMap_right_assoc
    (a b c : R) (M : Type v) [AddCommGroup M] [Module R M] :
    ((awayEqLinearEquiv M (show a * b * c = a * (b * c) by rw [mul_assoc])).toLinearMap).comp
        (((awayEqLinearEquiv M (by ring : a * b * c = a * c * b)).symm.toLinearMap).comp
          ((awayDirectLocalizeLinearMap (a * c) b M).comp
            (awayDirectLocalizeLinearMap a c M))) =
      awayDirectLocalizeLinearMap a (b * c) M := by
  -- As on the left branch, both routes agree after precomposing with `M → Away a M`; the two
  -- explicit equality transports are trivial on the canonical numerator `m/1`.
  apply IsLocalizedModule.ext
    (S := .powers a)
    (f := LocalizedModule.mkLinearMap (.powers a) M)
    (map_unit := away_direct_localize_powers_isUnit a (b * c) M)
  ext m
  simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
  calc
    (awayEqLinearEquiv M (show a * b * c = a * (b * c) by rw [mul_assoc]))
        ((awayEqLinearEquiv M (by ring : a * b * c = a * c * b)).symm
          (awayDirectLocalizeLinearMap (a * c) b M
            (awayDirectLocalizeLinearMap a c M (LocalizedModule.mk m 1))))
        = (awayEqLinearEquiv M (show a * b * c = a * (b * c) by rw [mul_assoc]))
            ((awayEqLinearEquiv M (by ring : a * b * c = a * c * b)).symm
              (LocalizedModule.mk m 1 : Away (a * c * b) M)) := by
                rw [awayDirectLocalizeLinearMap_apply_mk_one, awayDirectLocalizeLinearMap_apply_mk_one]
    _ = (awayEqLinearEquiv M (show a * b * c = a * (b * c) by rw [mul_assoc]))
          (LocalizedModule.mk m 1 : Away (a * b * c) M) := by
            rw [awayEqLinearEquiv_symm_apply_mk_one]
    _ = (LocalizedModule.mk m 1 : Away (a * (b * c)) M) := by
          exact awayEqLinearEquiv_apply_mk_one M (by rw [mul_assoc]) m
    _ = awayDirectLocalizeLinearMap a (b * c) M (LocalizedModule.mk m 1) := by
          symm
          exact awayDirectLocalizeLinearMap_apply_mk_one a (b * c) M m

/-- Helper for Lemma 10.24.5: collapsing the trivial localization on the `i`-th local piece sends
`m/1` back to `m`. -/
theorem localModuleAwayEquiv_apply_mk_one
    (glue : AwayModuleGlueing f) (i : Fin n) (x : glue.localModule i) :
    glue.localModuleAwayEquiv i (LocalizedModule.mk x 1) = x := by
  -- The forward map of `localModuleAwayEquiv` is the localization collapse map.
  simp [AwayModuleGlueing.localModuleAwayEquiv]

/-- Helper for Lemma 10.24.5: the inverse of the trivial-localization collapse sends `x` to its
canonical generator `x/1`. -/
theorem localModuleAwayEquiv_symm_apply
    (glue : AwayModuleGlueing f) (i : Fin n) (x : glue.localModule i) :
    (glue.localModuleAwayEquiv i).symm x =
      (LocalizedModule.mk x 1 : Away (f i) (glue.localModule i)) := by
  -- Apply the collapse equivalence to identify the inverse image of `x`.
  apply (glue.localModuleAwayEquiv i).injective
  rw [(glue.localModuleAwayEquiv i).apply_symm_apply]
  rw [localModuleAwayEquiv_apply_mk_one]

/-- Helper for Lemma 10.24.5: localizing the trivial-localization collapse once more away from `a`
and then inverting it sends a canonical generator back to the same canonical generator in the
double-away module. -/
theorem collapse_trivial_localization_in_double_away
    (glue : AwayModuleGlueing f) (i : Fin n) (a : R)
    (x : Away (f i) (glue.localModule i)) :
    (awayLocalizeLinearEquiv a (glue.localModuleAwayEquiv i)).symm
      (LocalizedModule.mk (glue.localModuleAwayEquiv i x) 1) =
      (LocalizedModule.mk x 1 : Away a (Away (f i) (glue.localModule i))) := by
  -- The inverse localized collapse sends a canonical numerator back to the canonical numerator of
  -- its preimage under the collapse equivalence.
  rw [awayLocalizeLinearEquiv_symm_apply_mk_one]
  simpa using
    congrArg
      (fun y ↦ (LocalizedModule.mk y 1 : Away a (Away (f i) (glue.localModule i))))
      ((glue.localModuleAwayEquiv i).symm_apply_apply x)

/-- Helper for Lemma 10.24.5: the inverse cocycle relation identifies the two ways of transporting
from the `k`-piece back to the fixed `i`-piece on triple overlaps. -/
theorem triple_overlap_inverse_cocycle
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : Away (f i * f j * f k) (glue.localModule k)) :
    ((awayModuleGlueingTripleOverlapHom12 f glue.localModule glue.overlapIso i j k).symm)
        (((awayModuleGlueingTripleOverlapHom23 f glue.localModule glue.overlapIso i j k).symm) x) =
      ((awayModuleGlueingTripleOverlapHom13 f glue.localModule glue.overlapIso i j k).symm) x := by
  -- Apply the inverse of the cocycle equality to the chosen triple-overlap element.
  simpa [LinearEquiv.trans_apply] using
    congrArg (fun e ↦ e.symm x) (glue.cocycle i j k)

/-- Helper for Lemma 10.24.5: on a canonical generator from the `j`-piece, the overlap comparison
to the fixed `i`-piece is obtained by transporting across `ψ⁻¹ᵢⱼ` and collapsing the trivial
`f i`-localization. -/
theorem local_piece_overlap_equiv_apply_mk_one
    (glue : AwayModuleGlueing f) (i j : Fin n) (x : glue.localModule j) :
    glue.local_piece_overlap_equiv i j (LocalizedModule.mk x 1) =
      awayLocalizeLinearEquiv (f j) (glue.localModuleAwayEquiv i)
        ((awayMulLinearEquiv (f i) (f j) (glue.localModule i)).symm
          (((glue.overlapIso i j).toLinearEquiv.restrictScalars R).symm
            (LocalizedModule.mk x 1))) := by
  -- Unfold the overlap comparison and normalize each canonical generator step explicitly.
  simp only [AwayModuleGlueing.local_piece_overlap_equiv, LinearEquiv.trans_apply]
  rw [awayLocalizeLinearEquiv_apply_mk_one, glue.localModuleAwayEquiv_symm_apply,
    awayMulLinearEquiv_apply_mk_mk, awayEqLinearEquiv_apply_mk_one]

/-- Helper for Lemma 10.24.5: localizing the target product away from `f i` acts coordinatewise on
its `(j,k)`-components before the cocycle transport is applied. -/
noncomputable abbrev localized_target_pi_map
    (glue : AwayModuleGlueing f) (i : Fin n) :
    (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) →ₗ[R]
      ∀ j : Fin n, ∀ k : Fin n, Away (f i) (Away (f j * f k) (glue.localModule j)) :=
  LinearMap.pi fun j ↦ LinearMap.pi fun k ↦
    let rowProjection :
        (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) →ₗ[R]
          ∀ k : Fin n, Away (f j * f k) (glue.localModule j) :=
      LinearMap.proj j
    let coordinateProjection :
        (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) →ₗ[R]
          Away (f j * f k) (glue.localModule j) :=
      (LinearMap.proj k).comp rowProjection
    (LocalizedModule.mkLinearMap (.powers (f i)) (Away (f j * f k) (glue.localModule j))).comp
      coordinateProjection

/-- Helper for Lemma 10.24.5: localizing the outer target family away from `f i` acts rowwise in
the `j`-index before the inner target localization is analyzed. -/
noncomputable abbrev localized_target_outer_pi_map
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
      ∀ j : Fin n, Away (f i) (∀ k : Fin n, Away (f j * f k) (glue.localModule j)) :=
  IsLocalizedModule.linearEquiv (.powers (f i))
    (LocalizedModule.mkLinearMap (.powers (f i))
      (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
    (LinearMap.pi fun j ↦
      (LocalizedModule.mkLinearMap (.powers (f i))
        (∀ k : Fin n, Away (f j * f k) (glue.localModule j))).comp
        (LinearMap.proj j))

/-- Helper for Lemma 10.24.5: after fixing the `j`-th target row, localizing away from `f i` acts
coordinatewise in the `k`-index. -/
noncomputable abbrev localized_target_row_pi_comparison
    (glue : AwayModuleGlueing f) (i j : Fin n) :
    Away (f i) (∀ k : Fin n, Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
      ∀ k : Fin n, Away (f i) (Away (f j * f k) (glue.localModule j)) :=
  IsLocalizedModule.linearEquiv (.powers (f i))
    (LocalizedModule.mkLinearMap (.powers (f i))
      (∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
    (LinearMap.pi fun k ↦
      (LocalizedModule.mkLinearMap (.powers (f i)) (Away (f j * f k) (glue.localModule j))).comp
        (LinearMap.proj k))

/-- Helper for Lemma 10.24.5: the raw target product comparison identifies the localized target
family with the family of coordinatewise target localizations before the cocycle transport. -/
noncomputable abbrev localized_target_pi_comparison
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
      ∀ j : Fin n, ∀ k : Fin n, Away (f i) (Away (f j * f k) (glue.localModule j)) :=
  -- First localize the outer `j`-family, then localize each fixed `j`-row in the `k`-index.
  (glue.localized_target_outer_pi_map i).trans
    (LinearEquiv.piCongrRight fun j ↦ glue.localized_target_row_pi_comparison i j)

/-- Helper for Lemma 10.24.5: after localizing the target product away from `f i`, the cocycle
transport identifies it with the standard target product for the fixed `i`-th local piece. -/
noncomputable abbrev localized_target_comparison
    (glue : AwayModuleGlueing f) (i : Fin n) :
    Away (f i) (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) ≃ₗ[R]
      ∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule i) :=
  -- First compare the localized target family with the coordinatewise localized target
  -- components, then transport each `(j,k)` coordinate through the triple-overlap equivalence.
  let componentComparison :
      (∀ j : Fin n, ∀ k : Fin n, Away (f i) (Away (f j * f k) (glue.localModule j))) ≃ₗ[R]
        ∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule i) :=
    LinearEquiv.piCongrRight fun j ↦
      LinearEquiv.piCongrRight fun k ↦ glue.localized_target_component_equiv i j k
  (glue.localized_target_pi_comparison i).trans componentComparison

/-- Helper for Lemma 10.24.5: the raw target comparison sends a canonical localized target family
to the family of coordinatewise canonical localizations before the cocycle transport is applied. -/
theorem localized_target_pi_comparison_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : ∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) :
    (((glue.localized_target_pi_comparison i) (LocalizedModule.mk x 1)) j) k =
      LocalizedModule.mk (x j k) 1 := by
  have houter :
      (glue.localized_target_outer_pi_map i (LocalizedModule.mk x 1)) j =
        LocalizedModule.mk (x j) 1 := by
    -- Evaluate the outer family comparison on the canonical localized target family element.
    simpa [AwayModuleGlueing.localized_target_outer_pi_map, LinearMap.comp_apply] using
      congrFun
        (IsLocalizedModule.linearEquiv_apply
          (S := .powers (f i))
          (f := LocalizedModule.mkLinearMap (.powers (f i))
            (∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
          (g := LinearMap.pi fun j ↦
            (LocalizedModule.mkLinearMap (.powers (f i))
              (∀ k : Fin n, Away (f j * f k) (glue.localModule j))).comp
              (LinearMap.proj j))
          x)
        j
  have hrow :
      (glue.localized_target_row_pi_comparison i j (LocalizedModule.mk (x j) 1)) k =
        LocalizedModule.mk (x j k) 1 := by
    -- Evaluate the inner row comparison on the canonical `j`-th target row.
    simpa [AwayModuleGlueing.localized_target_row_pi_comparison, LinearMap.comp_apply] using
      congrFun
        (IsLocalizedModule.linearEquiv_apply
          (S := .powers (f i))
          (f := LocalizedModule.mkLinearMap (.powers (f i))
            (∀ k : Fin n, Away (f j * f k) (glue.localModule j)))
          (g := LinearMap.pi fun k ↦
            (LocalizedModule.mkLinearMap (.powers (f i))
              (Away (f j * f k) (glue.localModule j))).comp
              (LinearMap.proj k))
          (x j))
        k
  -- Compose the outer and rowwise canonical-value computations.
  simp only [AwayModuleGlueing.localized_target_pi_comparison, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply]
  rw [houter, hrow]

/-- Helper for Lemma 10.24.5: the packaged target comparison sends a canonical localized target
family to the family obtained by applying the target-side cocycle transports coordinatewise. -/
theorem localized_target_comparison_apply_mk_one
    (glue : AwayModuleGlueing f) (i j k : Fin n)
    (x : ∀ j : Fin n, ∀ k : Fin n, Away (f j * f k) (glue.localModule j)) :
    ((glue.localized_target_comparison i (LocalizedModule.mk x 1)) j) k =
      glue.localized_target_component_equiv i j k (LocalizedModule.mk (x j k) 1) := by
  have hraw :
      (((glue.localized_target_pi_comparison i) (LocalizedModule.mk x 1)) j) k =
        LocalizedModule.mk (x j k) 1 :=
    glue.localized_target_pi_comparison_apply_mk_one i j k x
  -- Apply the target-side component transport to the raw coordinatewise localization formula.
  have hcomponent :
      glue.localized_target_component_equiv i j k
          ((((glue.localized_target_pi_comparison i) (LocalizedModule.mk x 1)) j) k) =
        glue.localized_target_component_equiv i j k (LocalizedModule.mk (x j k) 1) :=
    congrArg (glue.localized_target_component_equiv i j k) hraw
  -- The packaged comparison is the raw coordinatewise localization map followed by the
  -- triple-overlap transport on the `(j,k)` target coordinate.
  simpa [AwayModuleGlueing.localized_target_comparison, AwayModuleGlueing.localized_target_pi_comparison,
    LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply] using hcomponent

end AwayModuleGlueing

end
