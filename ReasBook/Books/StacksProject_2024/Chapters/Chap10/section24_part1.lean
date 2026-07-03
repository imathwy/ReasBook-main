import Mathlib
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_24_1 (from Chap10) -/
open LinearMap LocalizedModule

universe u v w

noncomputable section

section

variable {R : Type u} [CommSemiring R]
variable {ι : Type w}

/- Domain-style sampling:
- primary domain: commutative algebra of localization exactness on a standard principal-open cover;
- sampled owner declarations:
  `LocalizedModule.mkLinearMap`,
  `LocalizedModule.lift`,
  `injective_of_localized_span`,
  `exact_of_localized_span`;
- best owner abstraction: the localization-exactness owner theorems on a span-cover, with the
  family map and overlap-difference map as the source-facing bridge data for this particular
  two-step Cech complex;
- source/core/bridge triage:
  `source-facing`: the two explicit maps `α` and `β` in the localization glueing sequence;
  `core/canonical`: `injective_of_localized_span` and `exact_of_localized_span`;
  `bridge/view`: the canonical comparison maps built from `mkLinearMap` and `lift`;
- primitive data: the family `f : ι → R` and the canonical maps obtained from localization away
  from the elements `f i`;
- derived API: the injectivity and exactness statement `away_localization_glueing_exact`.
-/

local notation "Away" => LocalizedModule.Away

/-- The canonical map from `M` to the finite family of away localizations `M_(f_i)`. -/
abbrev awayLocalizationFamilyMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) :
    M →ₗ[R] ∀ i : ι, Away (f i) M :=
  LinearMap.pi fun i ↦ mkLinearMap (.powers (f i)) M

private theorem awayModuleEnd_isUnit_of_dvd
    (M : Type v) [AddCommGroup M] [Module R M] (x r : R) (h : r ∣ x) :
    IsUnit (algebraMap R (Module.End R (Away x M)) r) := by
  have h' : IsUnit (algebraMap R (Localization.Away x) r) :=
    IsLocalization.Away.isUnit_of_dvd x h
  let lsmulAway : Localization.Away x →ₐ[R] Module.End R (Away x M) :=
    Algebra.lsmul R R (Away x M)
  simpa [Algebra.smul_def] using
    h'.map lsmulAway

/-- The pairwise compatibility map for a finite family of away localizations. -/
def awayLocalizationCompatibilityMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) :
    (∀ i : ι, Away (f i) M) →ₗ[R] ∀ i : ι, ∀ j : ι, Away (f i * f j) M :=
  LinearMap.pi fun i ↦ LinearMap.pi fun j ↦
    (LocalizedModule.lift (.powers (f i))
      (mkLinearMap (.powers (f i * f j)) M)
      (fun x ↦ by
        rcases (Submonoid.mem_powers_iff x.1 (f i)).mp x.2 with ⟨n, hn⟩
        have hfi :
            IsUnit (algebraMap R (Module.End R (Away (f i * f j) M)) (f i)) :=
          awayModuleEnd_isUnit_of_dvd M (f i * f j) (f i) (dvd_mul_right _ _)
        simpa [← hn] using hfi.pow n)).comp (LinearMap.proj i) -
    (LocalizedModule.lift (.powers (f j))
      (mkLinearMap (.powers (f i * f j)) M)
      (fun x ↦ by
        rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
        have hfj :
            IsUnit (algebraMap R (Module.End R (Away (f i * f j) M)) (f j)) :=
          awayModuleEnd_isUnit_of_dvd M (f i * f j) (f j) (dvd_mul_left _ _)
        simpa [← hn] using hfj.pow n)).comp (LinearMap.proj j)

/-- Helper for Lemma 10.24.1: the canonical two-step localization map `M → S⁻¹(S'⁻¹M)`. -/
noncomputable abbrev iteratedLocalizedModuleMkLinearMap
    (S S' : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    M →ₗ[R] LocalizedModule S (LocalizedModule S' M) :=
  (LocalizedModule.mkLinearMap S (LocalizedModule S' M)).comp
    (LocalizedModule.mkLinearMap S' M)

/-- Helper for Lemma 10.24.1: localizing an invertible endomorphism remains invertible. -/
private theorem localizedModuleEnd_isUnit
    (S : Submonoid R) {N : Type v} [AddCommGroup N] [Module R N] {r : R}
    (h : IsUnit (algebraMap R (Module.End R N) r)) :
    IsUnit (algebraMap R (Module.End R (LocalizedModule S N)) r) := by
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

/-- Helper for Lemma 10.24.1: iterated localization localizes at the supremum of the two
submonoids. -/
instance iteratedLocalizedModule_isLocalizedModule_sup
    (S S' : Submonoid R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsLocalizedModule (S ⊔ S') (iteratedLocalizedModuleMkLinearMap S S' M) where
  map_units x := by
    rcases Submonoid.mem_sup.mp x.2 with ⟨s, hs, s', hs', hss'⟩
    have hx : (x : R) = s * s' := by
      simpa using hss'.symm
    -- Elements coming from `S` are inverted by the outer localization, while elements from `S'`
    -- stay invertible after localizing again.
    have hsUnit :
        IsUnit
          (algebraMap R (Module.End R (LocalizedModule S (LocalizedModule S' M))) s) :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S (LocalizedModule S' M))
        ⟨s, hs⟩
    have hs'Unit₀ :
        IsUnit (algebraMap R (Module.End R (LocalizedModule S' M)) s') :=
      IsLocalizedModule.map_units (f := LocalizedModule.mkLinearMap S' M) ⟨s', hs'⟩
    have hs'Unit :
        IsUnit
          (algebraMap R (Module.End R (LocalizedModule S (LocalizedModule S' M))) s') :=
      localizedModuleEnd_isUnit (S := S) hs'Unit₀
    rw [hx]
    simpa [map_mul] using hsUnit.mul hs'Unit
  surj m := by
    -- Clear the outer denominator first, then the inner one, and multiply the denominators.
    obtain ⟨⟨p, s⟩, hs⟩ :=
      IsLocalizedModule.surj S (LocalizedModule.mkLinearMap S (LocalizedModule S' M)) m
    obtain ⟨⟨x, s'⟩, hs'⟩ :=
      IsLocalizedModule.surj S' (LocalizedModule.mkLinearMap S' M) p
    refine ⟨⟨x, ⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩⟩, ?_⟩
    change (s.1 * s'.1 : R) • m =
      (LocalizedModule.mkLinearMap S (LocalizedModule S' M))
        ((LocalizedModule.mkLinearMap S' M) x)
    calc
      (s.1 * s'.1 : R) • m = (s'.1 * s.1 : R) • m := by rw [mul_comm]
      _ = s'.1 • (s • m) := by
        change (s'.1 * s.1 : R) • m = (s'.1 : R) • ((s : R) • m)
        rw [smul_smul]
      _ = s'.1 • (LocalizedModule.mkLinearMap S (LocalizedModule S' M) p) := by rw [hs]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' M)) (s'.1 • p) := by
        rw [LinearMap.map_smul_of_tower]
      _ = (LocalizedModule.mkLinearMap S (LocalizedModule S' M))
            ((LocalizedModule.mkLinearMap S' M) x) := by
        simpa using congrArg (LocalizedModule.mkLinearMap S (LocalizedModule S' M)) hs'
  exists_of_eq {x₁ x₂} h := by
    -- Equality upstairs clears first in the outer localization and then in the inner one.
    obtain ⟨s, hs⟩ :=
      IsLocalizedModule.exists_of_eq (S := S)
        (f := LocalizedModule.mkLinearMap S (LocalizedModule S' M)) h
    have hs'₀ :
        (LocalizedModule.mkLinearMap S' M) (s • x₁) =
          (LocalizedModule.mkLinearMap S' M) (s • x₂) := by
      simpa [LinearMap.map_smul_of_tower] using hs
    obtain ⟨s', hs'⟩ :=
      IsLocalizedModule.exists_of_eq (S := S')
        (f := LocalizedModule.mkLinearMap S' M) hs'₀
    refine ⟨⟨s.1 * s'.1, Submonoid.mul_mem_sup s.2 s'.2⟩, ?_⟩
    change (s.1 * s'.1 : R) • x₁ = (s.1 * s'.1 : R) • x₂
    calc
      (s.1 * s'.1 : R) • x₁ = (s'.1 * s.1 : R) • x₁ := by rw [mul_comm]
      _ = s'.1 • (s • x₁) := by
        change (s'.1 * s.1 : R) • x₁ = (s'.1 : R) • ((s : R) • x₁)
        rw [smul_smul]
      _ = s'.1 • (s • x₂) := by simpa using hs'
      _ = (s'.1 * s.1 : R) • x₂ := by
        change (s'.1 : R) • ((s : R) • x₂) = (s'.1 * s.1 : R) • x₂
        rw [smul_smul]
      _ = (s.1 * s'.1 : R) • x₂ := by rw [mul_comm]

/-- Helper for Lemma 10.24.1: localizing directly away from `ab` is also a localization at the
supremum of the submonoids generated by `a` and `b`. -/
private instance mkLinearMap_isLocalizedModule_sup_away_mul
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) := by
  refine
    IsLocalizedModule.of_exists_mul_mem (S := Submonoid.powers (a * b))
      (T := Submonoid.powers a ⊔ Submonoid.powers b) ?_ ?_
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)
  · intro x hx
    rcases (Submonoid.mem_powers_iff x (a * b)).mp hx with ⟨n, rfl⟩
    simpa [mul_pow] using
      (Submonoid.mul_mem_sup
        (show a ^ n ∈ Submonoid.powers a from ⟨n, rfl⟩)
        (show b ^ n ∈ Submonoid.powers b from ⟨n, rfl⟩))
  · intro x
    rcases Submonoid.mem_sup.mp x.2 with ⟨y, hy, z, hz, hyz⟩
    have hx : (x : R) = y * z := by
      simpa using hyz.symm
    rcases (Submonoid.mem_powers_iff y a).mp hy with ⟨m, rfl⟩
    rcases (Submonoid.mem_powers_iff z b).mp hz with ⟨n, rfl⟩
    refine ⟨a ^ n * b ^ m, ?_⟩
    rw [hx]
    refine ⟨m + n, ?_⟩
    simp [pow_add, mul_pow, mul_assoc, mul_left_comm]

/-- Helper for Lemma 10.24.1: the symmetric supremum description of localization away from
`ab`. -/
private instance mkLinearMap_isLocalizedModule_sup_away_mul'
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] :
    IsLocalizedModule (Submonoid.powers b ⊔ Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M) := by
  simpa [sup_comm, mul_comm] using
    (mkLinearMap_isLocalizedModule_sup_away_mul a b M :
      IsLocalizedModule (Submonoid.powers a ⊔ Submonoid.powers b)
        (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M))

/-- Helper for Lemma 10.24.1: reindexing away localizations along an equality of the inverted
element. -/
noncomputable abbrev awayEqLinearEquiv
    (M : Type v) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) :
    Away a M ≃ₗ[R] Away b M :=
  h.rec (LinearEquiv.refl R (Away a M))

/-- Helper for Lemma 10.24.1: the equality-based reindexing map fixes canonical elements. -/
private theorem awayEqLinearEquiv_apply_mk_one
    (M : Type v) [AddCommGroup M] [Module R M] {a b : R} (h : a = b) (m : M) :
    awayEqLinearEquiv M h (LocalizedModule.mk m 1) = LocalizedModule.mk m 1 := by
  -- The equality transport is definitionally trivial once the two away localizations are identified.
  subst h
  rfl

/-- Helper for Lemma 10.24.1: localizing a module away from an element that already acts
invertibly does not change the module. -/
private theorem awayLocalizedByUnit_left_inv
    (r : R) (M : Type v) [AddCommGroup M] [Module R M]
    (h : ∀ x : Submonoid.powers r, IsUnit (algebraMap R (Module.End R M) x)) :
    (LocalizedModule.lift (Submonoid.powers r) (.id : M →ₗ[R] M) h).comp
      (LocalizedModule.mkLinearMap (Submonoid.powers r) M) = .id := by
  simpa using
    (LocalizedModule.lift_comp (Submonoid.powers r) (.id : M →ₗ[R] M) h)

/-- Helper for Lemma 10.24.1: the canonical map into a localization is inverse to the collapse map
when the inverted element already acts invertibly. -/
private theorem awayLocalizedByUnit_right_inv
    (r : R) (M : Type v) [AddCommGroup M] [Module R M]
    (h : ∀ x : Submonoid.powers r, IsUnit (algebraMap R (Module.End R M) x)) :
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M).comp
      (LocalizedModule.lift (Submonoid.powers r) (.id : M →ₗ[R] M) h) = .id := by
  ext x
  induction x using LocalizedModule.induction_on with
  | _ m s =>
      rw [LinearMap.comp_apply, LocalizedModule.lift_mk, LocalizedModule.mkLinearMap_apply,
        LinearMap.id_apply]
      change LocalizedModule.mk ((h s).unit⁻¹.val m) 1 = LocalizedModule.mk m s
      rw [LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      have hs :
          m = (s : R) • ((h s).unit⁻¹.val m) :=
        (Module.End.algebraMap_isUnit_inv_apply_eq_iff (S := R) (h s) m
          ((h s).unit⁻¹.val m)).mp rfl
      simpa [Submonoid.smul_def] using hs.symm

/-- Helper for Lemma 10.24.1: if every power of `r` acts invertibly on `M`, then `Away r M`
is canonically isomorphic to `M`. -/
noncomputable abbrev awayLocalizedByUnitEquiv
    (r : R) (M : Type v) [AddCommGroup M] [Module R M]
    (h : ∀ x : Submonoid.powers r, IsUnit (algebraMap R (Module.End R M) x)) :
    Away r M ≃ₗ[R] M :=
  LinearEquiv.ofLinear
    (LocalizedModule.lift (Submonoid.powers r) (.id : M →ₗ[R] M) h)
    (LocalizedModule.mkLinearMap (Submonoid.powers r) M)
    (awayLocalizedByUnit_left_inv r M h)
    (awayLocalizedByUnit_right_inv r M h)

/-- Helper for Lemma 10.24.1: localizing first away from `a` and then away from `b` agrees with
direct localization away from `ab`. -/
noncomputable abbrev awayMulLinearEquiv
    (a b : R) (M : Type v) [AddCommGroup M] [Module R M] :
    Away b (Away a M) ≃ₗ[R] Away (a * b) M :=
  IsLocalizedModule.linearEquiv (Submonoid.powers b ⊔ Submonoid.powers a)
    (iteratedLocalizedModuleMkLinearMap (Submonoid.powers b) (Submonoid.powers a) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (a * b)) M)

end

section

variable {R : Type u} [CommSemiring R]
variable {ι : Type w} [Finite ι]

local notation "Away" => LocalizedModule.Away

omit [Finite ι] in
/-- Helper for Lemma 10.24.1: if one distinguished generator already acts invertibly on `M`, then
the finite Cech sequence for the away localizations of `M` is exact. -/
theorem away_localization_glueing_exact_of_isUnit
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ : ι)
    (hunit : ∀ x : Submonoid.powers (f i₀), IsUnit (algebraMap R (Module.End R M) x)) :
    Function.Injective (awayLocalizationFamilyMap M f) ∧
      Function.Exact (awayLocalizationFamilyMap M f) (awayLocalizationCompatibilityMap M f) := by
  let e₀ := awayLocalizedByUnitEquiv (f i₀) M hunit
  have he₀_mk :
      e₀.toLinearMap.comp (LocalizedModule.mkLinearMap (.powers (f i₀)) M) = .id := by
    simpa [e₀, awayLocalizedByUnitEquiv] using
      (awayLocalizedByUnit_left_inv (f i₀) M hunit)
  have hOverlapUnits (j : ι) :
      ∀ x : Submonoid.powers (f i₀ * f j),
        IsUnit (algebraMap R (Module.End R (Away (f j) M)) x) := by
    rintro ⟨x, hx⟩
    rcases (Submonoid.mem_powers_iff x (f i₀ * f j)).mp hx with ⟨n, rfl⟩
    have hiBase :
        IsUnit (algebraMap R (Module.End R M) ((f i₀) ^ n)) :=
      hunit ⟨(f i₀) ^ n, ⟨n, rfl⟩⟩
    have hi :
        IsUnit (algebraMap R (Module.End R (Away (f j) M)) ((f i₀) ^ n)) :=
      localizedModuleEnd_isUnit (S := .powers (f j)) (N := M) (r := (f i₀) ^ n) hiBase
    have hjBase :
        IsUnit (algebraMap R (Module.End R (Away (f j) M)) (f j)) := by
      simpa using awayModuleEnd_isUnit_of_dvd M (f j) (f j) dvd_rfl
    have hj :
        IsUnit (algebraMap R (Module.End R (Away (f j) M)) ((f j) ^ n)) := by
      simpa [map_pow] using hjBase.pow n
    change IsUnit (algebraMap R (Module.End R (Away (f j) M)) ((f i₀ * f j) ^ n))
    rw [mul_pow]
    simpa [map_mul, map_pow] using hi.mul hj
  have hCenterUnits (j : ι) :
      ∀ x : Submonoid.powers (f i₀),
        IsUnit (algebraMap R (Module.End R (Away (f j) M)) x) := by
    intro x
    exact localizedModuleEnd_isUnit (S := .powers (f j)) (N := M) (r := x.1) (hunit x)
  let toOverlapFromI0 : ∀ j : ι, Away (f i₀) M →ₗ[R] Away (f i₀ * f j) M :=
    fun j ↦
      LocalizedModule.lift (.powers (f i₀))
        (LocalizedModule.mkLinearMap (.powers (f i₀ * f j)) M)
        (fun x ↦ by
          rcases (Submonoid.mem_powers_iff x.1 (f i₀)).mp x.2 with ⟨n, hn⟩
          have hfi :
              IsUnit (algebraMap R (Module.End R (Away (f i₀ * f j) M)) (f i₀)) :=
            awayModuleEnd_isUnit_of_dvd M (f i₀ * f j) (f i₀) (dvd_mul_right _ _)
          simpa [map_pow, ← hn] using hfi.pow n)
  let toOverlapFromJ : ∀ j : ι, Away (f j) M →ₗ[R] Away (f i₀ * f j) M :=
    fun j ↦
      LocalizedModule.lift (.powers (f j))
        (LocalizedModule.mkLinearMap (.powers (f i₀ * f j)) M)
        (fun x ↦ by
          rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
          have hfj :
              IsUnit (algebraMap R (Module.End R (Away (f i₀ * f j) M)) (f j)) :=
            awayModuleEnd_isUnit_of_dvd M (f i₀ * f j) (f j) (dvd_mul_left _ _)
          simpa [map_pow, ← hn] using hfj.pow n)
  let overlapCollapse : ∀ j : ι, Away (f i₀ * f j) M →ₗ[R] Away (f j) M :=
    fun j ↦
      LocalizedModule.lift (.powers (f i₀ * f j))
        (LocalizedModule.mkLinearMap (.powers (f j)) M)
        (hOverlapUnits j)
  have hoverlap_fromJ (j : ι) :
      (overlapCollapse j).comp (toOverlapFromJ j) = LinearMap.id := by
    -- The overlap map from the `j`-th localization has an explicit left inverse once `f i₀`
    -- already acts invertibly on `Away (f j) M`.
    apply IsLocalizedModule.linearMap_ext (S := .powers (f j))
      (f := LocalizedModule.mkLinearMap (.powers (f j)) M)
      (f' := LocalizedModule.mkLinearMap (.powers (f j)) M)
    rw [LinearMap.comp_assoc, LocalizedModule.lift_comp, LocalizedModule.lift_comp, LinearMap.id_comp]
  have hoverlap_fromI0 (j : ι) :
      (overlapCollapse j).comp (toOverlapFromI0 j) =
        (LocalizedModule.mkLinearMap (.powers (f j)) M).comp e₀.toLinearMap := by
    -- Both sides are maps out of `Away (f i₀) M`; compare them on the original module `M`.
    letI : IsLocalizedModule (.powers (f i₀))
        (.id : Away (f j) M →ₗ[R] Away (f j) M) :=
      { map_units := fun x ↦ hCenterUnits j x
        surj := fun y ↦ ⟨⟨y, 1⟩, by simp⟩
        exists_of_eq := fun {x₁ x₂} h ↦ ⟨1, by simpa using h⟩ }
    apply IsLocalizedModule.linearMap_ext (S := .powers (f i₀))
      (f := LocalizedModule.mkLinearMap (.powers (f i₀)) M)
      (f' := (.id : Away (f j) M →ₗ[R] Away (f j) M))
    rw [LinearMap.comp_assoc, LocalizedModule.lift_comp, LocalizedModule.lift_comp,
      LinearMap.comp_assoc, he₀_mk, LinearMap.comp_id]
  constructor
  · -- The distinguished coordinate becomes the identity after collapsing the trivial localization.
    intro x y hxy
    have hi : e₀ ((awayLocalizationFamilyMap M f x) i₀) = e₀ ((awayLocalizationFamilyMap M f y) i₀) :=
      congrArg (fun z ↦ e₀ (z i₀)) hxy
    have hx : e₀ ((awayLocalizationFamilyMap M f x) i₀) = x := by
      simpa [awayLocalizationFamilyMap] using LinearMap.congr_fun he₀_mk x
    have hy' : e₀ ((awayLocalizationFamilyMap M f y) i₀) = y := by
      simpa [awayLocalizationFamilyMap] using LinearMap.congr_fun he₀_mk y
    exact hx.symm.trans (hi.trans hy')
  · -- Exactness follows by reconstructing a kernel element from its distinguished coordinate.
    refine LinearMap.exact_of_comp_eq_zero_of_ker_le_range ?_ ?_
    · ext m i j
      simp [awayLocalizationFamilyMap, awayLocalizationCompatibilityMap,
        LinearMap.comp_apply, LocalizedModule.lift_mk_one]
    · intro y hy
      let m : M := e₀ (y i₀)
      refine ⟨m, ?_⟩
      ext j
      have hij_zero :
          (toOverlapFromI0 j) (y i₀) - (toOverlapFromJ j) (y j) = 0 := by
        simpa [toOverlapFromI0, toOverlapFromJ, awayLocalizationCompatibilityMap] using
          congrFun (congrFun hy i₀) j
      have hij :
          (toOverlapFromI0 j) (y i₀) = (toOverlapFromJ j) (y j) :=
        sub_eq_zero.mp hij_zero
      have hI0 :
          (overlapCollapse j) ((toOverlapFromI0 j) (y i₀)) =
            LocalizedModule.mkLinearMap (.powers (f j)) M m := by
        simpa [m] using LinearMap.congr_fun (hoverlap_fromI0 j) (y i₀)
      have hJ :
          (overlapCollapse j) ((toOverlapFromJ j) (y j)) = y j := by
        simpa using LinearMap.congr_fun (hoverlap_fromJ j) (y j)
      calc
        (awayLocalizationFamilyMap M f m) j = LocalizedModule.mkLinearMap (.powers (f j)) M m := by
          simp [awayLocalizationFamilyMap]
        _ = (overlapCollapse j) ((toOverlapFromI0 j) (y i₀)) := by simpa using hI0.symm
        _ = (overlapCollapse j) ((toOverlapFromJ j) (y j)) := by rw [hij]
        _ = y j := hJ

/-- Helper for Lemma 10.24.1: localizing the middle product away from `f i₀` coordinatewise gives
the product of the iterated away localizations `Away (f i₀) (Away (f j) M)`. -/
private noncomputable abbrev awayLocalizationMiddlePiMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ : ι) :
    (∀ j : ι, Away (f j) M) →ₗ[R] ∀ j : ι, Away (f i₀) (Away (f j) M) :=
  LinearMap.pi fun j ↦
    (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j) M)).comp (LinearMap.proj j)

/-- Helper for Lemma 10.24.1: swapping the order of localization at `f i₀` and `f j`. -/
private noncomputable abbrev awayLocalizationMiddleSwap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j : ι) :
    Away (f i₀) (Away (f j) M) ≃ₗ[R] Away (f j) (Away (f i₀) M) :=
  (awayMulLinearEquiv (f j) (f i₀) M).trans
    ((awayEqLinearEquiv M (by rw [mul_comm])).trans
      (awayMulLinearEquiv (f i₀) (f j) M).symm)

/-- Helper for Lemma 10.24.1: the localized middle product is identified with the middle term of
the unit-case sequence on `Away (f i₀) M`. -/
private noncomputable abbrev awayLocalizationMiddleComparison
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ : ι) :
    LocalizedModule (.powers (f i₀)) (∀ j : ι, Away (f j) M) ≃ₗ[R]
      ∀ j : ι, Away (f j) (Away (f i₀) M) :=
  (IsLocalizedModule.linearEquiv (.powers (f i₀))
      (LocalizedModule.mkLinearMap (.powers (f i₀)) (∀ j : ι, Away (f j) M))
      (awayLocalizationMiddlePiMap M f i₀)).trans
    (LinearEquiv.piCongrRight fun j ↦ awayLocalizationMiddleSwap M f i₀ j)

/-- Helper for Lemma 10.24.1: the product-localization comparison sends the tuple `(m/1)_j` to
the tuple of double canonical images `((m/1)/1)_j`. -/
private theorem awayLocalizationMiddlePiComparison_apply_family
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j : ι) (m : M) :
    ((IsLocalizedModule.linearEquiv (.powers (f i₀))
        (LocalizedModule.mkLinearMap (.powers (f i₀)) (∀ j : ι, Away (f j) M))
        (awayLocalizationMiddlePiMap M f i₀))
      (LocalizedModule.mk ((awayLocalizationFamilyMap M f) m) 1)) j =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
  -- Evaluate the universal-property comparison on the canonical family element `(m/1)_j`.
  simpa [awayLocalizationMiddlePiMap, awayLocalizationFamilyMap, LinearMap.comp_apply] using
    congrFun
      (IsLocalizedModule.linearEquiv_apply
        (S := .powers (f i₀))
        (f := LocalizedModule.mkLinearMap (.powers (f i₀)) (∀ j : ι, Away (f j) M))
        (g := awayLocalizationMiddlePiMap M f i₀)
        ((awayLocalizationFamilyMap M f) m))
      j

/-- Helper for Lemma 10.24.1: the order-swap equivalence fixes the canonical image of `m`. -/
private theorem awayLocalizationMiddleSwap_apply_mk_mk
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j : ι) (m : M) :
    awayLocalizationMiddleSwap M f i₀ j (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
  have hleft :
      (awayMulLinearEquiv (f j) (f i₀) M) (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        LocalizedModule.mk m 1 := by
    -- The iterated-localization comparison sends the double canonical element to the direct one.
    simpa [awayMulLinearEquiv, iteratedLocalizedModuleMkLinearMap, LinearMap.comp_apply] using
      (IsLocalizedModule.linearEquiv_apply
        (S := .powers (f i₀) ⊔ .powers (f j))
        (f := iteratedLocalizedModuleMkLinearMap (.powers (f i₀)) (.powers (f j)) M)
        (g := LocalizedModule.mkLinearMap (.powers (f j * f i₀)) M)
        m)
  have hright :
      (awayMulLinearEquiv (f i₀) (f j) M) (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        LocalizedModule.mk m 1 := by
    -- The same canonical-value computation holds for the target localization order.
    simpa [awayMulLinearEquiv, iteratedLocalizedModuleMkLinearMap, LinearMap.comp_apply] using
      (IsLocalizedModule.linearEquiv_apply
        (S := .powers (f j) ⊔ .powers (f i₀))
        (f := iteratedLocalizedModuleMkLinearMap (.powers (f j)) (.powers (f i₀)) M)
        (g := LocalizedModule.mkLinearMap (.powers (f i₀ * f j)) M)
        m)
  -- Compare both sides after transporting to the direct localization away from `f i₀ * f j`.
  apply (awayMulLinearEquiv (f i₀) (f j) M).injective
  -- The two transport routes both send the double canonical element to `m/1`.
  simp only [awayLocalizationMiddleSwap, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hleft, hright]
  -- After identifying both direct-localization values, only the commutativity reindexing remains.
  exact awayEqLinearEquiv_apply_mk_one M (by rw [mul_comm]) m

/-- Helper for Lemma 10.24.1: after localizing away from `f i₀`, the family map becomes the
unit-case family map on `Away (f i₀) M` through the middle comparison equivalence. -/
private theorem awayLocalizationFamilyMap_localized_ladder
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ : ι) :
    awayLocalizationFamilyMap (Away (f i₀) M) f =
      (awayLocalizationMiddleComparison M f i₀).toLinearMap ∘ₗ
        LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f) := by
  -- Compare the two maps after precomposing with the canonical localization map on `M`.
  apply IsLocalizedModule.linearMap_ext (S := .powers (f i₀))
    (f := LocalizedModule.mkLinearMap (.powers (f i₀)) M)
    (f' := (awayLocalizationMiddleComparison M f i₀).toLinearMap ∘ₗ
      LocalizedModule.mkLinearMap (.powers (f i₀)) (∀ j : ι, Away (f j) M))
  ext m j
  have hmap :
      ((LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f)).restrictScalars R)
          ((LocalizedModule.mkLinearMap (.powers (f i₀)) M) m) =
        LocalizedModule.mk ((awayLocalizationFamilyMap M f) m) 1 := by
    -- Re-express the localized family value as the canonical fraction of the tuple `(m/1)_j`.
    simpa using
      (LocalizedModule.map_mk (.powers (f i₀)) (awayLocalizationFamilyMap M f) m 1)
  have hmapj :
      (↑(awayLocalizationMiddleComparison M f i₀) :
          LocalizedModule (.powers (f i₀)) (∀ j : ι, Away (f j) M) →ₗ[R]
            ∀ j : ι, Away (f j) (Away (f i₀) M))
          (((LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f)).restrictScalars R)
            ((LocalizedModule.mkLinearMap (.powers (f i₀)) M) m)) j =
        (↑(awayLocalizationMiddleComparison M f i₀) :
          LocalizedModule (.powers (f i₀)) (∀ j : ι, Away (f j) M) →ₗ[R]
            ∀ j : ι, Away (f j) (Away (f i₀) M))
          (LocalizedModule.mk ((awayLocalizationFamilyMap M f) m) 1) j := by
    -- Push the canonical-value rewrite through the middle comparison at the `j`-th coordinate.
    exact congrArg
      (fun x ↦
        (↑(awayLocalizationMiddleComparison M f i₀) :
          LocalizedModule (.powers (f i₀)) (∀ j : ι, Away (f j) M) →ₗ[R]
            ∀ j : ι, Away (f j) (Away (f i₀) M)) x j)
      hmap
  -- The middle comparison first localizes the family element coordinatewise, then swaps the
  -- order of localization; the two normalization lemmas identify both steps on `(m/1)_j`.
  simp only [LinearMap.comp_apply]
  calc
    (awayLocalizationFamilyMap (Away (f i₀) M) f) ((LocalizedModule.mkLinearMap (.powers (f i₀)) M) m) j
      =
        (↑(awayLocalizationMiddleComparison M f i₀) :
          LocalizedModule (.powers (f i₀)) (∀ j : ι, Away (f j) M) →ₗ[R]
            ∀ j : ι, Away (f j) (Away (f i₀) M))
          (LocalizedModule.mk ((awayLocalizationFamilyMap M f) m) 1) j := by
            -- On a canonical localized input, the middle comparison is exactly the two-step
            -- normalization already certified above.
            simp only [LocalizedModule.mkLinearMap_apply, pi_apply, LinearEquiv.coe_coe,
              LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply]
            rw [awayLocalizationMiddlePiComparison_apply_family]
            simpa [awayLocalizationMiddleSwap] using
              (awayLocalizationMiddleSwap_apply_mk_mk M f i₀ j m).symm
    _ =
        (↑(awayLocalizationMiddleComparison M f i₀) :
          LocalizedModule (.powers (f i₀)) (∀ j : ι, Away (f j) M) →ₗ[R]
            ∀ j : ι, Away (f j) (Away (f i₀) M))
          (((LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f)).restrictScalars R)
            ((LocalizedModule.mkLinearMap (.powers (f i₀)) M) m)) j := by
            exact hmapj.symm

-- Proof sketch: apply `injective_of_localized_span` and `exact_of_localized_span` to the canonical
-- maps `α` and `β` from the statement using the covering hypothesis
-- `Ideal.span (Set.range f) = ⊤`. After localizing at each `f i`, the statement reduces via the
-- canonical comparison maps for iterated localizations to the trivial case where one generator is
-- a unit, exactly as in the Stacks proof after passing to a localization where some `f i` becomes
-- `1`.
/-- Helper for Lemma 10.24.1: after localizing away from a fixed generator `f i₀`, the original
Cech sequence becomes the unit-case sequence for `Away (f i₀) M`. -/
private theorem away_localization_glueing_exact_at_generator
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ : ι) :
    Function.Injective
        (LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f)) ∧
      Function.Exact
        (LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f))
        (LocalizedModule.map (.powers (f i₀)) (awayLocalizationCompatibilityMap M f)) := by
  -- Route correction: keep the base ring fixed and compare only the localized module `Away (f i₀) M`
  -- with the unit-case sequence. The middle ladder is now established canonically; only the target
  -- compatibility ladder still remains to finish the exactness transfer.
  let midComparison := awayLocalizationMiddleComparison M f i₀
  have hmid :
      awayLocalizationFamilyMap (Away (f i₀) M) f =
        midComparison.toLinearMap ∘ₗ
          LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f) :=
    awayLocalizationFamilyMap_localized_ladder M f i₀
  have hunit_local :
      ∀ x : Submonoid.powers (f i₀),
        IsUnit (algebraMap R (Module.End R (Away (f i₀) M)) x) := by
    intro x
    simpa using
      IsLocalizedModule.map_units
        (f := LocalizedModule.mkLinearMap (.powers (f i₀)) M) x
  have hunit :=
    away_localization_glueing_exact_of_isUnit (M := Away (f i₀) M) f i₀ hunit_local
  constructor
  · -- Injectivity transfers across the established middle comparison ladder.
    intro x y hxy
    apply hunit.1
    simpa [hmid, midComparison, LinearMap.comp_apply] using congrArg midComparison hxy
  · -- The remaining ladder is the target product analogue of the established middle comparison.
    let targetPiMap :
        (∀ j : ι, ∀ k : ι, Away (f j * f k) M) →ₗ[R]
          ∀ j : ι, ∀ k : ι, Away (f i₀) (Away (f j * f k) M) :=
      { toFun := fun x j k ↦ LocalizedModule.mk (x j k) 1
        map_add' := by
          intro x y
          ext j k
          simp
        map_smul' := by
          intro r x
          ext j k
          simpa using
            (LocalizedModule.smul'_mk r (1 : Submonoid.powers (f i₀)) (x j k)).symm }
    let targetSwap :
        ∀ j : ι, ∀ k : ι,
          Away (f i₀) (Away (f j * f k) M) ≃ₗ[R] Away (f j * f k) (Away (f i₀) M) :=
      fun j k ↦
        (awayMulLinearEquiv (f j * f k) (f i₀) M).trans
          ((awayEqLinearEquiv M (by ac_rfl)).trans
            (awayMulLinearEquiv (f i₀) (f j * f k) M).symm)
    let tarComparison :
        LocalizedModule (.powers (f i₀)) (∀ j : ι, ∀ k : ι, Away (f j * f k) M) ≃ₗ[R]
          ∀ j : ι, ∀ k : ι, Away (f j * f k) (Away (f i₀) M) :=
      by
        -- TODO: identify the localized target product with the iterated away localizations
        -- coordinatewise, then swap the localization order at each `(j, k)`.
        sorry
    let origLeftComponent :
        ∀ j : ι, ∀ k : ι, Away (f j) M →ₗ[R] Away (f j * f k) M :=
      fun j k ↦
        LocalizedModule.lift (.powers (f j))
          (LocalizedModule.mkLinearMap (.powers (f j * f k)) M)
          (fun x ↦ by
            rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
            have hfj :
                IsUnit (algebraMap R (Module.End R (Away (f j * f k) M)) (f j)) :=
              awayModuleEnd_isUnit_of_dvd M (f j * f k) (f j) (dvd_mul_right _ _)
            simpa [map_pow, ← hn] using hfj.pow n)
    let origRightComponent :
        ∀ j : ι, ∀ k : ι, Away (f k) M →ₗ[R] Away (f j * f k) M :=
      fun j k ↦
        LocalizedModule.lift (.powers (f k))
          (LocalizedModule.mkLinearMap (.powers (f j * f k)) M)
          (fun x ↦ by
            rcases (Submonoid.mem_powers_iff x.1 (f k)).mp x.2 with ⟨n, hn⟩
            have hfk :
                IsUnit (algebraMap R (Module.End R (Away (f j * f k) M)) (f k)) :=
              awayModuleEnd_isUnit_of_dvd M (f j * f k) (f k) (dvd_mul_left _ _)
            simpa [map_pow, ← hn] using hfk.pow n)
    let unitLeftComponent :
        ∀ j : ι, ∀ k : ι,
          Away (f j) (Away (f i₀) M) →ₗ[R] Away (f j * f k) (Away (f i₀) M) :=
      fun j k ↦
        LocalizedModule.lift (.powers (f j))
          (LocalizedModule.mkLinearMap (.powers (f j * f k)) (Away (f i₀) M))
          (fun x ↦ by
            rcases (Submonoid.mem_powers_iff x.1 (f j)).mp x.2 with ⟨n, hn⟩
            have hfj :
                IsUnit
                  (algebraMap R (Module.End R (Away (f j * f k) (Away (f i₀) M))) (f j)) :=
              awayModuleEnd_isUnit_of_dvd (Away (f i₀) M) (f j * f k) (f j) (dvd_mul_right _ _)
            simpa [map_pow, ← hn] using hfj.pow n)
    let unitRightComponent :
        ∀ j : ι, ∀ k : ι,
          Away (f k) (Away (f i₀) M) →ₗ[R] Away (f j * f k) (Away (f i₀) M) :=
      fun j k ↦
        LocalizedModule.lift (.powers (f k))
          (LocalizedModule.mkLinearMap (.powers (f j * f k)) (Away (f i₀) M))
          (fun x ↦ by
            rcases (Submonoid.mem_powers_iff x.1 (f k)).mp x.2 with ⟨n, hn⟩
            have hfk :
                IsUnit
                  (algebraMap R (Module.End R (Away (f j * f k) (Away (f i₀) M))) (f k)) :=
              awayModuleEnd_isUnit_of_dvd (Away (f i₀) M) (f j * f k) (f k) (dvd_mul_left _ _)
            simpa [map_pow, ← hn] using hfk.pow n)
    let origLeft : ∀ j : ι, ∀ k : ι,
        (∀ l : ι, Away (f l) M) →ₗ[R] Away (f j * f k) M :=
      fun j k ↦ (origLeftComponent j k).comp (LinearMap.proj j)
    let origRight : ∀ j : ι, ∀ k : ι,
        (∀ l : ι, Away (f l) M) →ₗ[R] Away (f j * f k) M :=
      fun j k ↦ (origRightComponent j k).comp (LinearMap.proj k)
    let unitLeft : ∀ j : ι, ∀ k : ι,
        (∀ l : ι, Away (f l) (Away (f i₀) M)) →ₗ[R] Away (f j * f k) (Away (f i₀) M) :=
      fun j k ↦ (unitLeftComponent j k).comp (LinearMap.proj j)
    let unitRight : ∀ j : ι, ∀ k : ι,
        (∀ l : ι, Away (f l) (Away (f i₀) M)) →ₗ[R] Away (f j * f k) (Away (f i₀) M) :=
      fun j k ↦ (unitRightComponent j k).comp (LinearMap.proj k)
    -- TODO: rewrite the family ladder into the exactness-transfer orientation, then prove the
    -- target ladder using `origLeft`, `origRight`, `unitLeft`, and `unitRight` one summand at a
    -- time before reassembling with `LinearMap.sub_apply`.
    sorry

/-- Lemma 10.24.1: if the finite family `f : ι → R` generates the unit ideal, then the
sequence `0 → M → ∏ i, M_(f_i) → ∏ i j, M_(f_i f_j)` with `α(m) = (m/1)_i` and
`β((m_i)_i) = (m_i|_(f_i f_j) - m_j|_(f_i f_j))_(i,j)` is exact. Because the indexing sets are
finite, this is the finite-product translation of the source's direct-sum exact sequence. -/
theorem away_localization_glueing_exact
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (awayLocalizationFamilyMap M f) ∧
      Function.Exact (awayLocalizationFamilyMap M f) (awayLocalizationCompatibilityMap M f) :=
  -- Route correction: the unit-case kernel argument is now isolated in
  -- `away_localization_glueing_exact_of_isUnit`. What remains is the source-faithful localization
  -- step: after fixing `i₀`, identify the localized product maps componentwise with the direct
  -- family and compatibility maps on `Away (f i₀) M`, then invoke the owner theorems
  -- `injective_of_localized_span` and `exact_of_localized_span`.
  by
    constructor
    · -- Detect injectivity on the standard cover by localizing away from each generator.
      apply injective_of_localized_span (s := Set.range f) (spn := hf)
      intro r
      rcases r with ⟨r, ⟨i₀, rfl⟩⟩
      exact (away_localization_glueing_exact_at_generator (M := M) f i₀).1
    · -- Exactness is detected on the same cover, with the fixed-generator local statement above.
      apply exact_of_localized_span (s := Set.range f) (spn := hf)
      intro r
      rcases r with ⟨r, ⟨i₀, rfl⟩⟩
      exact (away_localization_glueing_exact_at_generator (M := M) f i₀).2

end

/-! ### Lemma_10_24_2 (from Chap10) -/
universe u

section

variable {R : Type u} [CommRing R]
variable {n : ℕ}

/-
Lemma 10.24.2 is a `source-facing` specialization in the localization-glueing exactness domain.
The owner abstraction is `away_localization_glueing_exact`; the primitive data remain
`awayLocalizationFamilyMap` and `awayLocalizationCompatibilityMap`, and this file keeps only the
ring case `M = R` rather than introducing a parallel owner wrapper.
-/

-- Proof sketch: this is the ring case of Lemma `10.24.1`, specialized to the module `M = R`.
/-- Lemma 10.24.2: if the finite family `f : Fin n → R` generates the unit ideal, then the
sequence `0 → R → ∏ i, R_(f_i) → ∏ i j, R_(f_i f_j)` with `α(x) = (x/1)_i` and
`β((x_i)_i) = (x_i|_(f_i f_j) - x_j|_(f_i f_j))_(i,j)` is exact. This is the specialization of
Lemma `10.24.1` to the `R`-module `R`, using the canonical family and compatibility maps from that
owner theorem; as in the source, the direct-sum sequence is written here using finite products. -/
theorem ring_localization_away_glueing_exact
    (f : Fin n → R) (hf : Ideal.span (Set.range f) = ⊤) :
    Function.Injective (awayLocalizationFamilyMap R f) ∧
      Function.Exact (awayLocalizationFamilyMap R f) (awayLocalizationCompatibilityMap R f) := by
  simpa using away_localization_glueing_exact R f hf

end

/-! ### Lemma_10_24_3 (from Chap10) -/
open PrimeSpectrum

universe u

section

variable {R : Type u} [CommRing R]

/- Lemma 10.24.3 is `source-facing`: the public output should be a product decomposition of `R`
whose two factor spectra identify with the given open-and-closed pieces `U` and `V`. The owner
abstractions are the canonical classification of clopen subsets of `Spec(R)` by idempotents,
the idempotent splitting `AlgEquiv.prodQuotientOfIsIdempotentElem`, and the quotient-spectrum
homeomorphism onto a zero locus. The idempotent and quotient calculations remain internal proof
data; the public API records the textbook decomposition itself. -/
/-- Lemma 10.24.3: if `Spec(R)` is the disjoint union of two open subsets `U` and `V`, then there
exist commutative rings `R₁` and `R₂`, a ring isomorphism `R ≃ R₁ × R₂`, and homeomorphisms
`Spec(R₁) ≃ U` and `Spec(R₂) ≃ V` induced by the two factor maps. -/
theorem exists_idempotent_partition_of_isCompl_open {U V : Set (PrimeSpectrum R)}
    (hU : IsOpen U) (hV : IsOpen V) (hUV : IsCompl U V) :
    ∃ (R₁ : Type u) (_ : CommRing R₁) (R₂ : Type u) (_ : CommRing R₂)
      (φ : R ≃+* R₁ × R₂) (h₁ : PrimeSpectrum R₁ ≃ₜ U) (h₂ : PrimeSpectrum R₂ ≃ₜ V),
        (∀ p, (h₁ p).1 = comap ((RingHom.fst R₁ R₂).comp φ.toRingHom) p) ∧
          ∀ p, (h₂ p).1 = comap ((RingHom.snd R₁ R₂).comp φ.toRingHom) p := by
  have hclopenU : IsClopen U := ⟨by
    rw [hUV.eq_compl]
    exact hV.isClosed_compl, hU⟩
  obtain ⟨e, he, hUe⟩ :=
    (existsUnique_idempotent_basicOpen_eq_of_isClopen hclopenU).exists
  have hVe : V = basicOpen (1 - e) := by
    calc
      V = Uᶜ := hUV.compl_eq.symm
      _ = (basicOpen e : Set (PrimeSpectrum R))ᶜ := by rw [hUe]
      _ = basicOpen (1 - e) := by
        rw [basicOpen_eq_zeroLocus_of_isIdempotentElem e he,
          ← basicOpen_eq_zeroLocus_compl (1 - e)]
  let R₁ : Type u := R ⧸ Ideal.span ({1 - e} : Set R)
  let R₂ : Type u := R ⧸ Ideal.span ({e} : Set R)
  let φ :
      R ≃ₐ[R] (R₁ × R₂) :=
    AlgEquiv.prodQuotientOfIsIdempotentElem R he.one_sub he (by simp) (by simp [sub_mul, he.eq])
  let h₁ : PrimeSpectrum R₁ ≃ₜ U :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (Ideal.span ({1 - e} : Set R))).trans
      (Homeomorph.setCongr <| by
        calc
          zeroLocus (Ideal.span ({1 - e} : Set R) : Set R) = zeroLocus ({1 - e} : Set R) := by
            rw [zeroLocus_span]
          _ = basicOpen e := by
            simpa using (basicOpen_eq_zeroLocus_of_isIdempotentElem e he).symm
          _ = U := hUe.symm)
  let h₂ : PrimeSpectrum R₂ ≃ₜ V :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus (Ideal.span ({e} : Set R))).trans
      (Homeomorph.setCongr <| by
        calc
          zeroLocus (Ideal.span ({e} : Set R) : Set R) = zeroLocus ({e} : Set R) := by
            rw [zeroLocus_span]
          _ = basicOpen (1 - e) := by
            simpa using zeroLocus_eq_basicOpen_of_isIdempotentElem e he
          _ = V := hVe.symm)
  have hfst :
      (RingHom.fst R₁ R₂).comp φ.toRingHom =
        Ideal.Quotient.mk (Ideal.span ({1 - e} : Set R)) := by
    ext r
    simp [φ, R₁, R₂]
  have hsnd :
      (RingHom.snd R₁ R₂).comp φ.toRingHom =
        Ideal.Quotient.mk (Ideal.span ({e} : Set R)) := by
    ext r
    simp [φ, R₁, R₂]
  refine ⟨R₁, inferInstance, R₂, inferInstance, φ.toRingEquiv, h₁, h₂, ?_⟩
  refine ⟨?_, ?_⟩
  · intro p
    change ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
        (Ideal.span ({1 - e} : Set R)) p).1) =
      comap ((RingHom.fst R₁ R₂).comp φ.toRingHom) p
    rw [Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply, ← hfst, comap_comp]
  · intro p
    change ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus
        (Ideal.span ({e} : Set R)) p).1) =
      comap ((RingHom.snd R₁ R₂).comp φ.toRingHom) p
    rw [Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply, ← hsnd, comap_comp]

end

/-! ### Lemma_10_24_4 (from Chap10) -/
open LinearMap

universe u v w

noncomputable section

section

variable {R : Type u} [CommRing R]
variable {ι : Type w}
variable (M : Type v) [AddCommGroup M] [Module R M] [Finite ι] (f : ι → R)

-- Proof sketch: if the canonical map to the family of away localizations is injective and every
-- component of the product linear map `pi fun i ↦ DistribSMul.toLinearMap R M (f i)` vanishes on
-- `m`, then the image of `m` in each `M_{f_i}` is zero, so `m = 0`. Conversely, if this product
-- linear map is injective and the image of `m` in each `M_{f_i}` vanishes, then some power of
-- each `f i` kills `m`; use induction on the finite sum of these exponents to reduce to the case
-- where every exponent is `1`.
/-- Helper for Lemma 10.24.4: vanishing in every away localization is equivalent to saying that
for each index `i`, some positive power of `f i` annihilates the source element. -/
lemma away_localization_family_map_eq_zero_iff {m : M} :
    awayLocalizationFamilyMap M f m = 0 ↔
      ∀ i, ∃ e : ℕ, 0 < e ∧ (f i) ^ e • m = 0 := by
  constructor
  · intro hm i
    -- Read the family-map equation componentwise and unpack the localization kernel criterion.
    have hi :
        LocalizedModule.mkLinearMap (.powers (f i)) M m = 0 := by
      simpa [awayLocalizationFamilyMap] using congrFun hm i
    rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff] at hi
    rcases hi with ⟨r, hr, hrs⟩
    rcases (Submonoid.mem_powers_iff r (f i)).mp hr with ⟨n, rfl⟩
    cases n with
    | zero =>
        use 1
        constructor
        · simp
        · have hm_zero : m = 0 := by
            simpa using hrs
          simpa [hm_zero]
    | succ n =>
        use n + 1
        constructor
        · omega
        · simpa
  · intro hm
    -- Each positive-power annihilation witnesses that the corresponding localization component is
    -- in the kernel of the canonical map.
    ext i
    rcases hm i with ⟨e, hepos, hs⟩
    have hi :
        LocalizedModule.mkLinearMap (.powers (f i)) M m = 0 := by
      rw [← LinearMap.mem_ker, LocalizedModule.mem_ker_mkLinearMap_iff]
      exact ⟨(f i) ^ e, ⟨e, rfl⟩, hs⟩
    simpa [awayLocalizationFamilyMap] using hi

/-- Helper for Lemma 10.24.4: an element killed by each `f i` already maps to zero in every away
localization. -/
lemma away_localization_family_map_zero_of_mem_torsionBySet {m : M}
    (hm : m ∈ Submodule.torsionBySet R M (Set.range f)) :
    awayLocalizationFamilyMap M f m = 0 := by
  -- Route correction: use the new localization-zero bridge so the forward implication is a single
  -- torsion-by-set calculation.
  rw [away_localization_family_map_eq_zero_iff (M := M) (f := f)]
  intro i
  use 1
  constructor
  · simp
  · -- Membership in `torsionBySet` says every generator `f i` kills `m`.
    rw [Submodule.mem_torsionBySet_iff] at hm
    simpa using hm ⟨f i, Set.mem_range_self i⟩

/-- Helper for Lemma 10.24.4: if positive powers of all `f i` annihilate `m`, then `m = 0`
whenever the common `f i`-torsion submodule is trivial. -/
lemma eq_zero_of_forall_pos_pow_smul_eq_zero {m : M} {e : ι → ℕ}
    (hepos : ∀ i, 0 < e i)
    (hpow : ∀ i, (f i) ^ e i • m = 0)
    (hbot : Submodule.torsionBySet R M (Set.range f) = ⊥) :
    m = 0 := by
  classical
  letI := Fintype.ofFinite ι
  -- Follow the source proof: induct on the total sum of the positive exponents.
  have hP :
      ∀ n : ℕ, ∀ (m : M) (e : ι → ℕ), (∑ i, e i) = n →
        (∀ i, 0 < e i) →
        (∀ i, (f i) ^ e i • m = 0) →
        m = 0 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih m e hsum hepos hpow
    by_cases hones : ∀ i, e i = 1
    · -- Base case: all exponents are `1`, so `m` lies in the torsion-by-set submodule.
      have hm_torsion : m ∈ Submodule.torsionBySet R M (Set.range f) := by
        rw [Submodule.mem_torsionBySet_iff]
        rintro ⟨a, ha⟩
        rcases ha with ⟨i, rfl⟩
        simpa [hones i] using hpow i
      have hm_bot : m ∈ (⊥ : Submodule R M) := by
        simpa [hbot] using hm_torsion
      simpa using hm_bot
    · push Not at hones
      rcases hones with ⟨i, hi_ne⟩
      have hi_gt : 1 < e i := by
        exact lt_of_le_of_ne (Nat.succ_le_of_lt (hepos i)) (by simpa using hi_ne.symm)
      let ePred : ι → ℕ := Function.update e i (e i - 1)
      have heposPred : ∀ j, 0 < ePred j := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp [ePred, hi_gt]
        · simp [ePred, hj, hepos j]
      have hpowPred : ∀ j, (f j) ^ ePred j • (f i • m) = 0 := by
        intro j
        by_cases hj : j = i
        · subst hj
          -- Repackage the `i`-th annihilation as one lower exponent on `f i • m`.
          calc
            (f j) ^ ePred j • (f j • m)
                = (f j) ^ (e j - 1) • (f j • m) := by simp [ePred]
            _ = ((f j) ^ (e j - 1) * f j) • m := by rw [smul_smul]
            _ = (f j) ^ e j • m := by
                  rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt (hepos j))]
            _ = 0 := hpow j
        · -- Away from `i`, the same exponent still annihilates after multiplying by `f i`.
          calc
            (f j) ^ ePred j • (f i • m)
                = (f j) ^ e j • (f i • m) := by simp [ePred, hj]
            _ = ((f j) ^ e j * f i) • m := by rw [smul_smul]
            _ = (f i * (f j) ^ e j) • m := by rw [mul_comm]
            _ = f i • ((f j) ^ e j • m) := by rw [smul_smul]
            _ = 0 := by rw [hpow j, smul_zero]
      have hsumPred_lt : ∑ j, ePred j < n := by
        rw [← hsum]
        rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i) (by simp) e (e i - 1)]
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (s := Finset.univ) (i := i) (by simp) e]
        omega
      have hfi_zero : f i • m = 0 := by
        exact ih (∑ j, ePred j) hsumPred_lt (f i • m) ePred rfl heposPred hpowPred
      let eOne : ι → ℕ := Function.update e i 1
      have heposOne : ∀ j, 0 < eOne j := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp [eOne]
        · simp [eOne, hj, hepos j]
      have hpowOne : ∀ j, (f j) ^ eOne j • m = 0 := by
        intro j
        by_cases hj : j = i
        · subst hj
          simpa [eOne] using hfi_zero
        · simpa [eOne, hj] using hpow j
      have hsumOne_lt : ∑ j, eOne j < n := by
        rw [← hsum]
        rw [Finset.sum_update_of_mem (s := Finset.univ) (i := i) (by simp) e 1]
        rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (s := Finset.univ) (i := i) (by simp) e]
        omega
      exact ih (∑ j, eOne j) hsumOne_lt m eOne rfl heposOne hpowOne
  exact hP (∑ i, e i) m e rfl hepos hpow

/-- Bridge the injectivity of the canonical map to the family of away localizations with the
vanishing of the torsion submodule cut out by the generating set `Set.range f`. -/
theorem away_localization_family_map_injective_iff_torsionBySet_eq_bot :
    Function.Injective (awayLocalizationFamilyMap M f) ↔
      Submodule.torsionBySet R M (Set.range f) = ⊥ := by
  rw [← LinearMap.ker_eq_bot]
  constructor
  · intro hker
    -- The forward implication sends torsion elements to zero in every localization component.
    rw [Submodule.eq_bot_iff]
    intro m hm
    have hm_zero :
        awayLocalizationFamilyMap M f m = 0 :=
      away_localization_family_map_zero_of_mem_torsionBySet (M := M) (f := f) hm
    have hm_ker : m ∈ LinearMap.ker (awayLocalizationFamilyMap M f) := by
      rw [LinearMap.mem_ker]
      exact hm_zero
    have hm_bot : m ∈ (⊥ : Submodule R M) := by
      simpa [hker] using hm_ker
    simpa using hm_bot
  · intro hbot
    -- The reverse implication extracts positive exponents from localization vanishing and then
    -- runs the source-proof induction on their total sum.
    rw [Submodule.eq_bot_iff]
    intro m hm
    rw [LinearMap.mem_ker] at hm
    rw [away_localization_family_map_eq_zero_iff (M := M) (f := f)] at hm
    choose e hepos hpow using hm
    exact eq_zero_of_forall_pos_pow_smul_eq_zero (M := M) (f := f)
      (m := m) (e := e) hepos hpow
      hbot

/-- Lemma 10.24.4: for a finite family `f : ι → R`, the canonical map from `M` to the family of
away localizations `M_{f_i}` is injective if and only if the product linear map with components
`m ↦ f_i • m` is injective. The Stacks Project writes the targets as finite direct sums; in Lean
we use the canonically equivalent finite products `∀ i, LocalizedModule.Away (f i) M` and
`∀ i, M`. -/
theorem away_localization_family_map_injective_iff_smul_family_map_injective :
    Function.Injective (awayLocalizationFamilyMap M f) ↔
      Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) := by
  have hker :
      LinearMap.ker (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) =
        Submodule.torsionBySet R M (Set.range f) := by
    ext m
    rw [LinearMap.ker_pi, Submodule.mem_iInf, Submodule.mem_torsionBySet_iff]
    constructor
    · intro hm ⟨a, ha⟩
      rcases ha with ⟨i, rfl⟩
      simpa [LinearMap.mem_ker] using hm i
    · intro hm i
      simpa [LinearMap.mem_ker] using hm ⟨f i, Set.mem_range_self i⟩
  have hsmul :
      Function.Injective (LinearMap.pi fun i ↦ DistribSMul.toLinearMap R M (f i)) ↔
        Submodule.torsionBySet R M (Set.range f) = ⊥ := by
    rw [← LinearMap.ker_eq_bot, hker]
  exact (away_localization_family_map_injective_iff_torsionBySet_eq_bot M f).trans hsmul.symm

end
