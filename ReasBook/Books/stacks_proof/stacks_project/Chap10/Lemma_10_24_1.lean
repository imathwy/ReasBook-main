import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

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

omit [Finite ι] in
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

/-- Helper for Chap10 Lemma 10 24 1: for a fixed first index, localizing the target product
coordinatewise gives the iterated away localizations. -/
private noncomputable abbrev awayLocalizationTargetPiMapInner
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j : ι) :
    (∀ k : ι, Away (f j * f k) M) →ₗ[R]
      ∀ k : ι, Away (f i₀) (Away (f j * f k) M) :=
  LinearMap.pi fun k ↦
    (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M)).comp
      (LinearMap.proj k)

/-- Helper for Chap10 Lemma 10 24 1: localizing the target product away from `f i₀`
coordinatewise gives the product of iterated away localizations. -/
private noncomputable abbrev awayLocalizationTargetPiMap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ : ι) :
    (∀ j : ι, ∀ k : ι, Away (f j * f k) M) →ₗ[R]
      ∀ j : ι, ∀ k : ι, Away (f i₀) (Away (f j * f k) M) :=
  LinearMap.pi fun j ↦
    (awayLocalizationTargetPiMapInner M f i₀ j).comp (LinearMap.proj j)

/-- Helper for Chap10 Lemma 10 24 1: swapping the order of localization at `f i₀` and
`f j * f k` in a target component. -/
private noncomputable abbrev awayLocalizationTargetSwap
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j k : ι) :
    Away (f i₀) (Away (f j * f k) M) ≃ₗ[R]
      Away (f j * f k) (Away (f i₀) M) :=
  (awayMulLinearEquiv (f j * f k) (f i₀) M).trans
    ((awayEqLinearEquiv M (mul_comm (f j * f k) (f i₀))).trans
      (awayMulLinearEquiv (f i₀) (f j * f k) M).symm)

/-- Helper for Chap10 Lemma 10 24 1: the localized target product is identified with the target
term of the unit-case sequence on `Away (f i₀) M`. -/
private noncomputable abbrev awayLocalizationTargetComparison
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ : ι) :
    LocalizedModule (.powers (f i₀)) (∀ j : ι, ∀ k : ι, Away (f j * f k) M) ≃ₗ[R]
      ∀ j : ι, ∀ k : ι, Away (f j * f k) (Away (f i₀) M) :=
  (IsLocalizedModule.linearEquiv (.powers (f i₀))
      (LocalizedModule.mkLinearMap (.powers (f i₀))
        (∀ j : ι, ∀ k : ι, Away (f j * f k) M))
      (awayLocalizationTargetPiMap M f i₀)).trans
    (LinearEquiv.piCongrRight fun j ↦
      LinearEquiv.piCongrRight fun k ↦ awayLocalizationTargetSwap M f i₀ j k)

/-- Helper for Chap10 Lemma 10 24 1: the target product-localization comparison sends a canonical
tuple to the tuple of canonical localized target components. -/
private theorem awayLocalizationTargetPiComparison_apply
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j k : ι)
    (z : ∀ j : ι, ∀ k : ι, Away (f j * f k) M) :
    ((IsLocalizedModule.linearEquiv (.powers (f i₀))
        (LocalizedModule.mkLinearMap (.powers (f i₀))
          (∀ j : ι, ∀ k : ι, Away (f j * f k) M))
        (awayLocalizationTargetPiMap M f i₀))
      (LocalizedModule.mk z 1)) j k =
      LocalizedModule.mk (z j k) 1 := by
  -- Evaluate the universal-property comparison at the chosen target coordinate.
  simpa [awayLocalizationTargetPiMap, awayLocalizationTargetPiMapInner, LinearMap.comp_apply] using
    congrFun
      (congrFun
        (IsLocalizedModule.linearEquiv_apply
          (S := .powers (f i₀))
          (f := LocalizedModule.mkLinearMap (.powers (f i₀))
            (∀ j : ι, ∀ k : ι, Away (f j * f k) M))
          (g := awayLocalizationTargetPiMap M f i₀)
          z)
        j)
      k

/-- Helper for Chap10 Lemma 10 24 1: the target comparison evaluates on canonical localized
tuples by first localizing coordinatewise and then swapping localization order. -/
private theorem awayLocalizationTargetComparison_apply
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j k : ι)
    (z : ∀ j : ι, ∀ k : ι, Away (f j * f k) M) :
    (awayLocalizationTargetComparison M f i₀ (LocalizedModule.mk z 1)) j k =
      awayLocalizationTargetSwap M f i₀ j k (LocalizedModule.mk (z j k) 1) := by
  -- The comparison is the coordinatewise localization comparison followed by the target swap.
  simp only [awayLocalizationTargetComparison, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply]
  exact congrArg (awayLocalizationTargetSwap M f i₀ j k)
    (awayLocalizationTargetPiComparison_apply M f i₀ j k z)

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: the target order-swap equivalence fixes double canonical
images of elements of `M`. -/
private theorem awayLocalizationTargetSwap_apply_mk_mk
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j k : ι) (m : M) :
    awayLocalizationTargetSwap M f i₀ j k
        (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
      LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
  have hleft :
      (awayMulLinearEquiv (f j * f k) (f i₀) M)
          (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        LocalizedModule.mk m 1 := by
    -- The first comparison sends the iterated canonical element to the direct localization.
    simpa [awayMulLinearEquiv, iteratedLocalizedModuleMkLinearMap, LinearMap.comp_apply] using
      (IsLocalizedModule.linearEquiv_apply
        (S := .powers (f i₀) ⊔ .powers (f j * f k))
        (f := iteratedLocalizedModuleMkLinearMap (.powers (f i₀)) (.powers (f j * f k)) M)
        (g := LocalizedModule.mkLinearMap (.powers ((f j * f k) * f i₀)) M)
        m)
  have hright :
      (awayMulLinearEquiv (f i₀) (f j * f k) M)
          (LocalizedModule.mk (LocalizedModule.mk m 1) 1) =
        LocalizedModule.mk m 1 := by
    -- The opposite-order comparison has the same canonical value.
    simpa [awayMulLinearEquiv, iteratedLocalizedModuleMkLinearMap, LinearMap.comp_apply] using
      (IsLocalizedModule.linearEquiv_apply
        (S := .powers (f j * f k) ⊔ .powers (f i₀))
        (f := iteratedLocalizedModuleMkLinearMap (.powers (f j * f k)) (.powers (f i₀)) M)
        (g := LocalizedModule.mkLinearMap (.powers (f i₀ * (f j * f k))) M)
        m)
  -- Transport both sides to the direct localization, where the equality reindexing is canonical.
  apply (awayMulLinearEquiv (f i₀) (f j * f k) M).injective
  simp only [awayLocalizationTargetSwap, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hleft, hright]
  exact awayEqLinearEquiv_apply_mk_one M (mul_comm (f j * f k) (f i₀)) m

/-- Helper for Chap10 Lemma 10 24 1: the middle comparison evaluates on arbitrary canonical
localized families by coordinatewise localization followed by the middle swap. -/
private theorem awayLocalizationMiddleComparison_apply
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j : ι)
    (z : ∀ j : ι, Away (f j) M) :
    (awayLocalizationMiddleComparison M f i₀ (LocalizedModule.mk z 1)) j =
      awayLocalizationMiddleSwap M f i₀ j (LocalizedModule.mk (z j) 1) := by
  -- Unfold the middle comparison only far enough to expose the coordinatewise localization map.
  simp only [awayLocalizationMiddleComparison, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply]
  congr 1
  simpa [awayLocalizationMiddlePiMap, LinearMap.comp_apply] using
    congrFun
      (IsLocalizedModule.linearEquiv_apply
        (S := .powers (f i₀))
        (f := LocalizedModule.mkLinearMap (.powers (f i₀)) (∀ j : ι, Away (f j) M))
        (g := awayLocalizationMiddlePiMap M f i₀)
        z)
      j

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: powers of the left factor act invertibly on
`Away (a * b) M`. -/
private theorem awayOverlapLeftComponent_units
    (M : Type v) [AddCommGroup M] [Module R M] (a b : R) :
    ∀ x : Submonoid.powers a,
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) x) := by
  rintro ⟨x, hx⟩
  rcases (Submonoid.mem_powers_iff x a).mp hx with ⟨n, hn⟩
  have ha :
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) a) :=
    awayModuleEnd_isUnit_of_dvd M (a * b) a (dvd_mul_right _ _)
  simpa [map_pow, ← hn] using ha.pow n

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: powers of the right factor act invertibly on
`Away (a * b) M`. -/
private theorem awayOverlapRightComponent_units
    (M : Type v) [AddCommGroup M] [Module R M] (a b : R) :
    ∀ x : Submonoid.powers b,
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) x) := by
  rintro ⟨x, hx⟩
  rcases (Submonoid.mem_powers_iff x b).mp hx with ⟨n, hn⟩
  have hb :
      IsUnit (algebraMap R (Module.End R (Away (a * b) M)) b) :=
    awayModuleEnd_isUnit_of_dvd M (a * b) b (dvd_mul_left _ _)
  simpa [map_pow, ← hn] using hb.pow n

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: the left restriction map
`Away a M →ₗ[R] Away (a * b) M`. -/
private noncomputable abbrev awayOverlapLeftComponent
    (M : Type v) [AddCommGroup M] [Module R M] (a b : R) :
    Away a M →ₗ[R] Away (a * b) M :=
  LocalizedModule.lift (.powers a)
    (LocalizedModule.mkLinearMap (.powers (a * b)) M)
    (awayOverlapLeftComponent_units M a b)

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: the right restriction map
`Away b M →ₗ[R] Away (a * b) M`. -/
private noncomputable abbrev awayOverlapRightComponent
    (M : Type v) [AddCommGroup M] [Module R M] (a b : R) :
    Away b M →ₗ[R] Away (a * b) M :=
  LocalizedModule.lift (.powers b)
    (LocalizedModule.mkLinearMap (.powers (a * b)) M)
    (awayOverlapRightComponent_units M a b)

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: the compatibility map is the difference of the two
restriction maps in each pair of coordinates. -/
private theorem awayLocalizationCompatibilityMap_apply_components
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R)
    (x : ∀ i : ι, Away (f i) M) (j k : ι) :
    awayLocalizationCompatibilityMap M f x j k =
      awayOverlapLeftComponent M (f j) (f k) (x j) -
        awayOverlapRightComponent M (f j) (f k) (x k) := by
  -- Unfold only the source-facing map and the named overlap components.
  simp [awayLocalizationCompatibilityMap, awayOverlapLeftComponent, awayOverlapRightComponent]

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: the left overlap restriction commutes with localization
away from `f i₀` and the canonical order-swap equivalences. -/
private theorem awayOverlapLeftComponent_localized_ladder
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j k : ι) :
    ((awayOverlapLeftComponent (Away (f i₀) M) (f j) (f k)).comp
        (awayLocalizationMiddleSwap M f i₀ j).toLinearMap).comp
        (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j) M)) =
      ((awayLocalizationTargetSwap M f i₀ j k).toLinearMap.comp
        (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M))).comp
          (awayOverlapLeftComponent M (f j) (f k)) := by
  -- Compare maps out of `Away (f j) M` on canonical elements of `M`.
  apply IsLocalizedModule.ext (S := .powers (f j))
    (f := LocalizedModule.mkLinearMap (.powers (f j)) M)
    (map_unit := awayOverlapLeftComponent_units (Away (f i₀) M) (f j) (f k))
  ext m
  have hOrig :
      awayOverlapLeftComponent M (f j) (f k) (LocalizedModule.mk m 1) =
        LocalizedModule.mk m 1 := by
    -- The original left restriction fixes canonical fractions with denominator `1`.
    simp [awayOverlapLeftComponent]
  calc
    (((awayOverlapLeftComponent (Away (f i₀) M) (f j) (f k) ∘ₗ
          ↑(awayLocalizationMiddleSwap M f i₀ j)) ∘ₗ
          LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j) M)) ∘ₗ
          LocalizedModule.mkLinearMap (.powers (f j)) M) m
        =
          awayOverlapLeftComponent (Away (f i₀) M) (f j) (f k)
            (awayLocalizationMiddleSwap M f i₀ j
              (LocalizedModule.mk (LocalizedModule.mk m 1) 1)) := by
          simp [LinearMap.comp_apply]
    _ = awayOverlapLeftComponent (Away (f i₀) M) (f j) (f k)
          (LocalizedModule.mk (LocalizedModule.mk m 1) 1) := by
          rw [awayLocalizationMiddleSwap_apply_mk_mk]
    _ = LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
          simp [awayOverlapLeftComponent]
    _ = awayLocalizationTargetSwap M f i₀ j k
          (LocalizedModule.mk (LocalizedModule.mk m 1) 1) := by
          exact (awayLocalizationTargetSwap_apply_mk_mk M f i₀ j k m).symm
    _ =
        (((↑(awayLocalizationTargetSwap M f i₀ j k) ∘ₗ
            LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M)) ∘ₗ
            awayOverlapLeftComponent M (f j) (f k)) ∘ₗ
            LocalizedModule.mkLinearMap (.powers (f j)) M) m := by
          simp [LinearMap.comp_apply, hOrig]

omit [Finite ι] in
/-- Helper for Chap10 Lemma 10 24 1: the right overlap restriction commutes with localization
away from `f i₀` and the canonical order-swap equivalences. -/
private theorem awayOverlapRightComponent_localized_ladder
    (M : Type v) [AddCommGroup M] [Module R M] (f : ι → R) (i₀ j k : ι) :
    ((awayOverlapRightComponent (Away (f i₀) M) (f j) (f k)).comp
        (awayLocalizationMiddleSwap M f i₀ k).toLinearMap).comp
        (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f k) M)) =
      ((awayLocalizationTargetSwap M f i₀ j k).toLinearMap.comp
        (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M))).comp
          (awayOverlapRightComponent M (f j) (f k)) := by
  -- Compare maps out of `Away (f k) M` on canonical elements of `M`.
  apply IsLocalizedModule.ext (S := .powers (f k))
    (f := LocalizedModule.mkLinearMap (.powers (f k)) M)
    (map_unit := awayOverlapRightComponent_units (Away (f i₀) M) (f j) (f k))
  ext m
  have hOrig :
      awayOverlapRightComponent M (f j) (f k) (LocalizedModule.mk m 1) =
        LocalizedModule.mk m 1 := by
    -- The original right restriction fixes canonical fractions with denominator `1`.
    simp [awayOverlapRightComponent]
  calc
    (((awayOverlapRightComponent (Away (f i₀) M) (f j) (f k) ∘ₗ
          ↑(awayLocalizationMiddleSwap M f i₀ k)) ∘ₗ
          LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f k) M)) ∘ₗ
          LocalizedModule.mkLinearMap (.powers (f k)) M) m
        =
          awayOverlapRightComponent (Away (f i₀) M) (f j) (f k)
            (awayLocalizationMiddleSwap M f i₀ k
              (LocalizedModule.mk (LocalizedModule.mk m 1) 1)) := by
          simp [LinearMap.comp_apply]
    _ = awayOverlapRightComponent (Away (f i₀) M) (f j) (f k)
          (LocalizedModule.mk (LocalizedModule.mk m 1) 1) := by
          rw [awayLocalizationMiddleSwap_apply_mk_mk]
    _ = LocalizedModule.mk (LocalizedModule.mk m 1) 1 := by
          simp [awayOverlapRightComponent]
    _ = awayLocalizationTargetSwap M f i₀ j k
          (LocalizedModule.mk (LocalizedModule.mk m 1) 1) := by
          exact (awayLocalizationTargetSwap_apply_mk_mk M f i₀ j k m).symm
    _ =
        (((↑(awayLocalizationTargetSwap M f i₀ j k) ∘ₗ
            LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M)) ∘ₗ
            awayOverlapRightComponent M (f j) (f k)) ∘ₗ
            LocalizedModule.mkLinearMap (.powers (f k)) M) m := by
          simp [LinearMap.comp_apply, hOrig]

-- Proof sketch: apply `injective_of_localized_span` and `exact_of_localized_span` to the canonical
-- maps `α` and `β` from the statement using the covering hypothesis
-- `Ideal.span (Set.range f) = ⊤`. After localizing at each `f i`, the statement reduces via the
-- canonical comparison maps for iterated localizations to the trivial case where one generator is
-- a unit, exactly as in the Stacks proof after passing to a localization where some `f i` becomes
-- `1`.
/-- Chap10 Lemma 10 24 1: after localizing away from a fixed generator `f i₀`, the original
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
    let tarComparison :
        LocalizedModule (.powers (f i₀)) (∀ j : ι, ∀ k : ι, Away (f j * f k) M) ≃ₗ[R]
          ∀ j : ι, ∀ k : ι, Away (f j * f k) (Away (f i₀) M) :=
      awayLocalizationTargetComparison M f i₀
    have htar :
        awayLocalizationCompatibilityMap (Away (f i₀) M) f ∘ₗ midComparison.toLinearMap =
          tarComparison.toLinearMap ∘ₗ
            LocalizedModule.map (.powers (f i₀)) (awayLocalizationCompatibilityMap M f) := by
      -- Compare the target compatibility maps on canonical localized middle-family elements.
      apply IsLocalizedModule.linearMap_ext (S := .powers (f i₀))
        (f := LocalizedModule.mkLinearMap (.powers (f i₀)) (∀ j : ι, Away (f j) M))
        (f' := tarComparison.toLinearMap ∘ₗ
          LocalizedModule.mkLinearMap (.powers (f i₀))
            (∀ j : ι, ∀ k : ι, Away (f j * f k) M))
      ext z j k
      -- Normalize both target components on a canonical localized family; the overlap maps then
      -- agree because all constructions are induced by the same canonical maps out of `M`.
      simp only [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply]
      change (awayLocalizationCompatibilityMap (Away (f i₀) M) f)
          ((awayLocalizationMiddleComparison M f i₀) (LocalizedModule.mk z 1)) j k =
        (awayLocalizationTargetComparison M f i₀)
          (((LocalizedModule.map (.powers (f i₀)) (awayLocalizationCompatibilityMap M f)).restrictScalars R)
            (LocalizedModule.mk z 1)) j k
      rw [awayLocalizationCompatibilityMap_apply_components]
      rw [awayLocalizationMiddleComparison_apply M f i₀ j z]
      rw [awayLocalizationMiddleComparison_apply M f i₀ k z]
      have hmap :
          ((LocalizedModule.map (.powers (f i₀)) (awayLocalizationCompatibilityMap M f)).restrictScalars R)
              (LocalizedModule.mk z 1) =
            LocalizedModule.mk (awayLocalizationCompatibilityMap M f z) 1 := by
        -- The localized compatibility map sends a canonical family to the canonical image.
        simpa using
          (LocalizedModule.map_mk (.powers (f i₀)) (awayLocalizationCompatibilityMap M f) z 1)
      rw [hmap]
      rw [awayLocalizationTargetComparison_apply]
      rw [awayLocalizationCompatibilityMap_apply_components]
      have hleft :=
        LinearMap.congr_fun (awayOverlapLeftComponent_localized_ladder M f i₀ j k) (z j)
      have hright :=
        LinearMap.congr_fun (awayOverlapRightComponent_localized_ladder M f i₀ j k) (z k)
      have hleft' :
          awayOverlapLeftComponent (Away (f i₀) M) (f j) (f k)
              (awayLocalizationMiddleSwap M f i₀ j (LocalizedModule.mk (z j) 1)) =
            awayLocalizationTargetSwap M f i₀ j k
              (LocalizedModule.mk (awayOverlapLeftComponent M (f j) (f k) (z j)) 1) := by
        simpa [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply] using hleft
      have hright' :
          awayOverlapRightComponent (Away (f i₀) M) (f j) (f k)
              (awayLocalizationMiddleSwap M f i₀ k (LocalizedModule.mk (z k) 1)) =
            awayLocalizationTargetSwap M f i₀ j k
              (LocalizedModule.mk (awayOverlapRightComponent M (f j) (f k) (z k)) 1) := by
        simpa [LinearMap.comp_apply, LocalizedModule.mkLinearMap_apply] using hright
      rw [hleft', hright']
      -- The target swap is linear, so it carries the difference of overlap restrictions to the
      -- difference of their target images.
      change
        awayLocalizationTargetSwap M f i₀ j k
              (LocalizedModule.mk (awayOverlapLeftComponent M (f j) (f k) (z j)) 1) -
            awayLocalizationTargetSwap M f i₀ j k
              (LocalizedModule.mk (awayOverlapRightComponent M (f j) (f k) (z k)) 1) =
          awayLocalizationTargetSwap M f i₀ j k
            (LocalizedModule.mk
              (awayOverlapLeftComponent M (f j) (f k) (z j) -
                awayOverlapRightComponent M (f j) (f k) (z k)) 1)
      have hmk :
          (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M))
              (awayOverlapLeftComponent M (f j) (f k) (z j)) -
              (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M))
                (awayOverlapRightComponent M (f j) (f k) (z k)) =
            (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M))
              (awayOverlapLeftComponent M (f j) (f k) (z j) -
                awayOverlapRightComponent M (f j) (f k) (z k)) := by
        simpa using
          (map_sub
            (LocalizedModule.mkLinearMap (.powers (f i₀)) (Away (f j * f k) M) :
              Away (f j * f k) M →ₗ[R] Away (f i₀) (Away (f j * f k) M))
            (awayOverlapLeftComponent M (f j) (f k) (z j))
            (awayOverlapRightComponent M (f j) (f k) (z k))).symm
      have hmk' :
          LocalizedModule.mk (awayOverlapLeftComponent M (f j) (f k) (z j))
              (1 : Submonoid.powers (f i₀)) -
              LocalizedModule.mk (awayOverlapRightComponent M (f j) (f k) (z k))
                (1 : Submonoid.powers (f i₀)) =
            LocalizedModule.mk
              (awayOverlapLeftComponent M (f j) (f k) (z j) -
                awayOverlapRightComponent M (f j) (f k) (z k))
              (1 : Submonoid.powers (f i₀)) := by
        simpa [LocalizedModule.mkLinearMap_apply] using hmk
      rw [← hmk']
      exact
        (map_sub (awayLocalizationTargetSwap M f i₀ j k).toLinearMap
          (LocalizedModule.mk (awayOverlapLeftComponent M (f j) (f k) (z j)) 1)
          (LocalizedModule.mk (awayOverlapRightComponent M (f j) (f k) (z k)) 1)).symm
    have hfirst :
        (LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f)).restrictScalars R ∘ₗ
            (LinearEquiv.refl R (Away (f i₀) M)).toLinearMap =
          midComparison.symm.toLinearMap ∘ₗ awayLocalizationFamilyMap (Away (f i₀) M) f := by
      -- Reorient the middle comparison ladder for mathlib's exactness transport lemma.
      ext x
      apply midComparison.injective
      simpa [hmid, LinearMap.comp_apply]
    have hsecond :
        (LocalizedModule.map (.powers (f i₀)) (awayLocalizationCompatibilityMap M f)).restrictScalars R ∘ₗ
            midComparison.symm.toLinearMap =
          tarComparison.symm.toLinearMap ∘ₗ awayLocalizationCompatibilityMap (Away (f i₀) M) f := by
      -- Reorient the target square by applying `tarComparison` and using the proved ladder.
      ext x
      apply tarComparison.injective
      ext j k
      simpa [LinearMap.comp_apply] using
        (congrFun (congrFun (LinearMap.congr_fun htar (midComparison.symm x)) j) k).symm
    have hexactR :
        Function.Exact
          ((LocalizedModule.map (.powers (f i₀)) (awayLocalizationFamilyMap M f)).restrictScalars R)
          ((LocalizedModule.map (.powers (f i₀)) (awayLocalizationCompatibilityMap M f)).restrictScalars R) :=
      Function.Exact.of_ladder_linearEquiv_of_exact
        (e₁ := LinearEquiv.refl R (Away (f i₀) M))
        (e₂ := midComparison.symm)
        (e₃ := tarComparison.symm)
        hfirst
        hsecond
        hunit.2
    -- Exactness as `R`-linear maps is the same underlying function exactness as in the goal.
    simpa using hexactR

/-- Global form of Chap10 Lemma 10 24 1: if the finite family `f : ι → R` generates the unit
ideal, then the sequence `0 → M → ∏ i, M_(f_i) → ∏ i j, M_(f_i f_j)` with `α(m) = (m/1)_i` and
`β((m_i)_i) = (m_i|_(f_i f_j) - m_j|_(f_i f_j))_(i,j)` is exact. Because the indexing sets are
finite, this is the finite-product translation of the source's direct-sum exact sequence. -/
@[stacks 00EK]
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
