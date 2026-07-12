import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap15.Lemma_15_22_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Module
open scoped nonZeroDivisors

/-
Domain-style sampling:
- primary domain: module duality, reflexivity, and torsion for modules over commutative domains;
- sampled owner API:
  `Module.IsReflexive`,
  `Module.Dual.eval`,
  `Module.evalEquiv`,
  `Module.IsReflexive.to_isTorsionFree`;
- best owner abstraction: the canonical owner object is the reflexivity class `Module.IsReflexive`
  together with the canonical evaluation map `Module.Dual.eval`; torsion and torsion-freeness are
  already owned by `Module.IsTorsion` and `Module.IsTorsionFree`, both available through the
  owner import `Mathlib.LinearAlgebra.Dual.Defs`;
- source/core/bridge triage:
  `source-facing`: the torsion statements about the kernel and cokernel of the evaluation map and
  the finite-module injectivity criterion;
  `core/canonical`: `Module.IsReflexive`, `Module.Dual.eval`, `Module.IsTorsionFree`,
  `Module.IsTorsion`;
  `bridge/view`: clause `(1)` is exact-interface reuse of the canonical owner instance
  `Module.IsReflexive.to_isTorsionFree`.

Primitive data are the ambient semiring/module for clause `(1)`, and the finite module plus the
canonical map `Module.Dual.eval` for clauses `(2)` through `(4)`. No extra wrapper around the
double dual or its evaluation map is mathematically needed, and clause `(1)` should remain a direct
recall of the upstream owner instance rather than a local theorem shell.
-/

section

variable {R : Type u} [CommSemiring R]
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Lemma 15.23.2 (1): a reflexive module is torsion free. The source states this over a domain,
but the canonical owner instance already works over a commutative semiring. -/
recall IsReflexive.to_isTorsionFree

end

section Finite

open Module.Dual

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

/-- Helper for Lemma 15.23.2: a finitely generated submodule of the fraction ring admits a single
nonzero denominator clearing all of its elements. -/
private theorem fractionRing_finite_submodule_has_common_denominator
    (I : Submodule R (FractionRing R)) (hI : I.FG) :
    ∃ c : R, c ≠ 0 ∧ ∀ z ∈ I,
      c • z ∈ LinearMap.range (Algebra.linearMap R (FractionRing R)) := by
  classical
  let aMap : R →ₗ[R] FractionRing R := Algebra.linearMap R (FractionRing R)
  let num : FractionRing R → R := fun z ↦ (IsLocalization.exists_mk'_eq (R⁰) z).choose
  let den : FractionRing R → R⁰ := fun z ↦
    ((IsLocalization.exists_mk'_eq (R⁰) z).choose_spec).choose
  have hfrac : ∀ z : FractionRing R, IsLocalization.mk' (FractionRing R) (num z) (den z) = z := by
    intro z
    exact ((IsLocalization.exists_mk'_eq (R⁰) z).choose_spec).choose_spec
  obtain ⟨t, ht⟩ := hI
  let c : R := ∏ z ∈ t, (den z : R)
  have hc : c ≠ 0 := by
    -- Every chosen denominator lies in `R⁰`, so their finite product stays nonzero.
    refine Finset.prod_ne_zero_iff.mpr fun z hz ↦ ?_
    exact mem_nonZeroDivisors_iff_ne_zero.mp (den z).2
  let J : Submodule R (FractionRing R) :=
    { carrier := {z | c • z ∈ LinearMap.range aMap}
      zero_mem' := by
        refine ⟨0, ?_⟩
        simp
      add_mem' := by
        intro z w hz hw
        simpa [smul_add] using (LinearMap.range aMap).add_mem hz hw
      smul_mem' := by
        intro r z hz
        simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          (LinearMap.range aMap).smul_mem r hz }
  have hgen : ∀ z ∈ (↑t : Set (FractionRing R)), z ∈ J := by
    intro z hz
    change c • z ∈ LinearMap.range aMap
    let d : R := ∏ w ∈ t.erase z, (den w : R)
    have hden :
        (den z : R) • z = aMap (num z) := by
      -- Rewriting the chosen fraction identifies multiplication by the denominator with a numerator
      -- coming from `R`.
      have hz' :
          aMap (num z) = z * aMap (den z : R) := by
        exact
          (IsLocalization.mk'_eq_iff_eq_mul (M := R⁰) (S := FractionRing R)
            (x := num z) (y := den z) (z := z)).mp (hfrac z)
      simpa [aMap, Algebra.smul_def, mul_comm] using hz'.symm
    have hc' : d * (den z : R) = c := by
      simpa [c, d] using
        (Finset.prod_erase_mul (s := t) (f := fun w ↦ (den w : R)) (a := z) (h := hz))
    refine ⟨d * num z, ?_⟩
    calc
      aMap (d * num z) = d • aMap (num z) := by
        simp [aMap, Algebra.smul_def]
      _ = d • ((den z : R) • z) := by rw [hden]
      _ = (d * (den z : R)) • z := by rw [smul_smul]
      _ = c • z := by rw [hc']
  have hI_le : I ≤ J := by
    -- The generators lie in the denominator-cleared submodule, so the whole span does.
    rw [← ht]
    exact Submodule.span_le.mpr hgen
  refine ⟨c, hc, ?_⟩
  intro z hz
  exact hI_le hz

/-- Helper for Lemma 15.23.2: after multiplying by one nonzero scalar, a
`FractionRing R`-valued linear functional on a finite module descends to an `R`-valued one. -/
private theorem exists_smul_eq_algebraMap_comp_fractionRing
    (ℓ : M →ₗ[R] FractionRing R) :
    ∃ c : R, c ≠ 0 ∧ ∃ ℓ0 : M →ₗ[R] R,
      (Algebra.linearMap R (FractionRing R)).comp ℓ0 = c • ℓ := by
  let I : Submodule R (FractionRing R) := LinearMap.range ℓ
  have hI : I.FG := by
    -- The range of a map out of a finite module is finitely generated.
    change (LinearMap.range ℓ).FG
    rw [LinearMap.range_eq_map]
    exact Submodule.FG.map ℓ Module.Finite.fg_top
  obtain ⟨c, hc, hclear⟩ :=
    fractionRing_finite_submodule_has_common_denominator (R := R) I hI
  let aMap : R →ₗ[R] FractionRing R := Algebra.linearMap R (FractionRing R)
  have haMap_inj : Function.Injective aMap := IsFractionRing.injective R (FractionRing R)
  let e : R ≃ₗ[R] LinearMap.range aMap := LinearEquiv.ofInjective aMap haMap_inj
  have hcod : ∀ x : M, (c • ℓ) x ∈ LinearMap.range aMap := by
    intro x
    exact hclear (ℓ x) ⟨x, rfl⟩
  let ℓrange : M →ₗ[R] LinearMap.range aMap :=
    LinearMap.codRestrict (LinearMap.range aMap) (c • ℓ) hcod
  let ℓ0 : M →ₗ[R] R := e.symm.toLinearMap.comp ℓrange
  refine ⟨c, hc, ℓ0, ?_⟩
  -- The descended functional is obtained by moving from the algebra-map range back to `R`.
  ext x
  change ((e (ℓ0 x) : LinearMap.range aMap) : FractionRing R) = (ℓrange x : FractionRing R)
  exact congrArg Subtype.val (e.apply_symm_apply (ℓrange x))

/-- Helper for Lemma 15.23.2: after localizing at `R⁰`, a finite module admits a finite-free
model whose composite with the localization map is multiplication by one nonzero scalar. -/
private theorem exists_free_cover_retraction_smul_localized :
    ∃ (n : ℕ) (α : (Fin n → R) →ₗ[R] M) (β : M →ₗ[R] (Fin n → R)) (c : R),
      c ≠ 0 ∧
        (LocalizedModule.mkLinearMap R⁰ M).comp (α.comp β) =
          c • LocalizedModule.mkLinearMap R⁰ M := by
  classical
  -- Route correction: the blocked monolithic descent `LocalizedModule R⁰ M → (Fin n → FractionRing R)`
  -- should be replaced by a split construction. The new denominator-clearing helpers above handle
  -- one fraction-field-valued coordinate functional at a time; the remaining work is to package
  -- them against `localized_basis_lift_with_denominators` into maps `α, β` and the localized
  -- scalar-splitting identity.
  let n : ℕ := Module.finrank (FractionRing R) (LocalizedModule R⁰ M)
  let b : Basis (Fin n) (FractionRing R) (LocalizedModule R⁰ M) :=
    Module.finBasis (FractionRing R) (LocalizedModule R⁰ M)
  obtain ⟨w, s, hs, _hw⟩ :=
    localized_basis_lift_with_denominators (R := R) (M := M) n b
  let mkM : M →ₗ[R] LocalizedModule R⁰ M := LocalizedModule.mkLinearMap R⁰ M
  let coordMap : Fin n → M →ₗ[R] FractionRing R :=
    fun i ↦ ((b.coord i).restrictScalars R).comp mkM
  have hdesc :
      ∀ i : Fin n,
        ∃ c0 : R, c0 ≠ 0 ∧ ∃ ℓ0 : M →ₗ[R] R,
          (Algebra.linearMap R (FractionRing R)).comp ℓ0 = c0 • coordMap i := by
    intro i
    simpa [coordMap] using
      exists_smul_eq_algebraMap_comp_fractionRing (R := R) (M := M) (coordMap i)
  choose c0 hc0 ℓ0 hℓ0 using hdesc
  let t : Fin n → R := fun i ↦ (s i : R) * c0 i
  let d : Fin n → R := fun i ↦ (Finset.univ.erase i).prod t
  let c : R := Finset.univ.prod t
  have hc : c ≠ 0 := by
    -- Every basis denominator and every cleared coordinate scalar is nonzero, so the common
    -- product is still nonzero.
    refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
    exact mul_ne_zero (mem_nonZeroDivisors_iff_ne_zero.mp (s i).2) (hc0 i)
  let α : (Fin n → R) →ₗ[R] M := (Pi.basisFun R (Fin n)).constr R w
  let β : M →ₗ[R] (Fin n → R) := LinearMap.pi fun i ↦ (d i : R) • ℓ0 i
  have hprod : ∀ i : Fin n, d i * t i = c := by
    intro i
    simpa [c, d, t, mul_comm, mul_left_comm, mul_assoc] using
      (Finset.prod_erase_mul (s := Finset.univ) (f := t) (a := i) (by simp : i ∈ Finset.univ))
  refine ⟨n, α, β, c, hc, ?_⟩
  ext x
  -- Compare the two localized maps by evaluating every basis coordinate on the generic fiber.
  apply b.ext_elem
  intro i
  have hs' :
      mkM (w i) = algebraMap R (FractionRing R) (s i : R) • b i := by
    -- The chosen lifts of the basis vectors become scalar multiples of the basis after
    -- localization.
    have hsi :
        mkM (w i) = (s i : R⁰) • b i :=
      (IsLocalizedModule.mk'_eq_iff (S := R⁰) (f := mkM)).mp (hs i)
    simpa [Submonoid.smul_def] using hsi
  have hαcoord :
      ((b.coord i).restrictScalars R).comp (mkM.comp α) =
        (Algebra.linearMap R (FractionRing R)).comp ((s i : R) • LinearMap.proj i) := by
    -- On the standard basis of `R^n`, the map `α` lands on the lifted basis vector `w i`,
    -- whose `i`-th localized coordinate is exactly the chosen denominator `s i`.
    refine (Pi.basisFun R (Fin n)).ext fun j ↦ ?_
    have hsj :
        mkM (w j) = algebraMap R (FractionRing R) (s j : R) • b j := by
      have hsj' :
          mkM (w j) = (s j : R⁰) • b j :=
        (IsLocalizedModule.mk'_eq_iff (S := R⁰) (f := mkM)).mp (hs j)
      simpa [Submonoid.smul_def] using hsj'
    by_cases hij : i = j
    · subst hij
      simp [α, hsj, LinearMap.comp_apply, Algebra.smul_def]
    · simp [α, hsj, LinearMap.comp_apply, hij]
  have hβi : (β x) i = d i * ℓ0 i x := by
    simp [β, d]
  have hℓ0x :
      algebraMap R (FractionRing R) (ℓ0 i x) = c0 i • b.coord i (mkM x) := by
    -- The coordinate functional on the generic fiber is exactly the localization of `ℓ0 i`,
    -- up to the cleared denominator `c0 i`.
    have := congrArg (fun f : M →ₗ[R] FractionRing R => f x) (hℓ0 i)
    simpa [coordMap, LinearMap.comp_apply] using this
  calc
    b.coord i (mkM ((α.comp β) x)) =
        (((b.coord i).restrictScalars R).comp (mkM.comp α)) (β x) := by
          simp [LinearMap.comp_apply]
    _ = ((Algebra.linearMap R (FractionRing R)).comp ((s i : R) • LinearMap.proj i)) (β x) := by
          rw [hαcoord]
    _ = algebraMap R (FractionRing R) ((s i : R) * (β x i)) := by
          simp [LinearMap.comp_apply]
    _ = algebraMap R (FractionRing R) ((s i : R) * (d i * ℓ0 i x)) := by rw [hβi]
    _ = algebraMap R (FractionRing R) (d i * ((s i : R) * ℓ0 i x)) := by
          simp [mul_comm, mul_assoc]
    _ = algebraMap R (FractionRing R) (d i * (s i : R)) *
          algebraMap R (FractionRing R) (ℓ0 i x) := by
          simp [map_mul, mul_assoc]
    _ = algebraMap R (FractionRing R) (d i * (s i : R)) * (c0 i • b.coord i (mkM x)) := by
          rw [hℓ0x]
    _ = algebraMap R (FractionRing R) (d i * ((s i : R) * c0 i)) * b.coord i (mkM x) := by
          simp [Algebra.smul_def, map_mul, mul_comm, mul_left_comm, mul_assoc]
    _ = algebraMap R (FractionRing R) c * b.coord i (mkM x) := by
          rw [hprod i]
    _ = b.coord i (c • mkM x) := by
          simp [Algebra.smul_def]
    _ = b.coord i ((c • mkM) x) := by
          simp

-- Proof sketch: choose generators of `M`, pass to the fraction field, extract a basis of
-- `M ⊗[R] K`, and clear denominators to produce maps `R^r → M → R^r` whose two composites are
-- multiplication by a single nonzero scalar `c`. Comparing the induced diagram with the double
-- dual evaluation map `eval R M` shows that `c` annihilates the kernel.
/-- Lemma 15.23.2 (2): if `M` is finite, then the kernel of the canonical map from `M` to its
double dual is a torsion module. -/
@[stacks 0AV0]
theorem eval_ker_isTorsion :
    IsTorsion R (eval R M).ker := by
  obtain ⟨n, α, β, c, hc, hloc⟩ := exists_free_cover_retraction_smul_localized (R := R) (M := M)
  let mkM : M →ₗ[R] LocalizedModule R⁰ M := LocalizedModule.mkLinearMap R⁰ M
  let basisFree : Basis (Fin n) R (Fin n → R) := Pi.basisFun R (Fin n)
  intro x
  -- Naturality moves `x` into the finite free model, where evaluation is injective.
  have hβx : β x = 0 := by
    have hnat := Module.Dual.eval_naturality (R := R) (M₁ := M) (M₂ := Fin n → R) β
    have hx0 : eval R M x = 0 := x.2
    have hEval :
        eval R (Fin n → R) (β x) = 0 := by
      have := congrArg (fun f : M →ₗ[R] Dual R (Dual R (Fin n → R)) => f x) hnat
      simpa [LinearMap.comp_apply, hx0] using this.symm
    exact basisFree.eval_injective (by simpa using hEval)
  have hlocZero : mkM (c • x) = 0 := by
    -- The localized scalar-splitting relation kills `x` once `β x = 0`.
    have := congrArg (fun f : M →ₗ[R] LocalizedModule R⁰ M => f x) hloc
    simpa [LinearMap.comp_apply, hβx, smul_assoc] using this.symm
  rcases (IsLocalizedModule.eq_zero_iff (S := R⁰) (f := mkM)).mp hlocZero with ⟨s, hs⟩
  refine ⟨⟨(s : R) * c, by simpa [mul_comm] using mul_ne_zero (nonZeroDivisors.ne_zero s.2) hc⟩, ?_⟩
  apply Subtype.ext
  change ((s : R) * c) • (x : M) = 0
  have hs' : (s : R) • (c • (x : M)) = 0 := hs
  calc
    ((s : R) * c) • (x : M) = (((s : R) • c : R) • (x : M)) := by
      simp [smul_eq_mul]
    _ = (s : R) • (c • (x : M)) := by
      exact smul_assoc (s : R) c (x : M)
    _ = 0 := hs'

-- Proof sketch: use the same denominator-clearing maps `R^r → M → R^r` as in the kernel case.
-- The induced commutative diagram with `eval R M` shows that the same
-- nonzero scalar `c` annihilates the quotient of the double dual by the image of `M`.
/-- Helper for Lemma 15.23.2: after localizing the cokernel quotient map of `eval R M`,
surjectivity is preserved. This fixes the quotient-side part of the source proof route before the
remaining dual-localization comparison is inserted. -/
private theorem localized_eval_cokernel_quotient_surjective :
    let Q : Submodule R (Dual R (Dual R M)) := (eval R M).range
    Function.Surjective
      (IsLocalizedModule.map R⁰
        (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R M)))
        (Submodule.toLocalizedQuotient (p := R⁰) Q)
        (Submodule.mkQ Q)) := by
  let Q : Submodule R (Dual R (Dual R M)) := (eval R M).range
  -- Localizing a surjective linear map stays surjective, and `mkQ` is surjective by construction.
  simpa [Q] using
    (IsLocalizedModule.map_surjective (S := R⁰)
      (f := LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R M)))
      (g := Submodule.toLocalizedQuotient (p := R⁰) Q)
      (h := Submodule.mkQ Q)
      (Submodule.mkQ_surjective Q))

/-- Helper for Lemma 15.23.2: localizing an `R`-linear form on `M` gives an `R`-linear
fraction-field-valued functional on the generic fiber. -/
private noncomputable def localized_dual_raw_map :
    Dual R M →ₗ[R] (LocalizedModule R⁰ M →ₗ[R] FractionRing R) :=
  IsLocalizedModule.map R⁰ (LocalizedModule.mkLinearMap R⁰ M)
    (Algebra.linearMap R (FractionRing R))

/-- Helper for Lemma 15.23.2: on numerator generators, the raw localized dual map is just scalar
extension of the original functional. -/
private theorem localized_dual_raw_map_comp (φ : Dual R M) :
    (localized_dual_raw_map (R := R) (M := M) φ).comp (LocalizedModule.mkLinearMap R⁰ M) =
      (Algebra.linearMap R (FractionRing R)).comp φ := by
  -- This is exactly the defining commutative square for `IsLocalizedModule.map`.
  simpa [localized_dual_raw_map] using
    (IsLocalizedModule.map_comp (S := R⁰)
      (f := LocalizedModule.mkLinearMap R⁰ M)
      (g := Algebra.linearMap R (FractionRing R))
      (h := φ))

/-- Helper for Lemma 15.23.2: the raw map from `Dual R M` to fraction-field-valued linear forms
on the generic fiber satisfies the localization universal property. -/
private theorem localized_dual_raw_map_isLocalizedModule :
    IsLocalizedModule R⁰ (localized_dual_raw_map (R := R) (M := M)) := by
  classical
  letI : Module (FractionRing R) (LocalizedModule R⁰ M →ₗ[R] FractionRing R) := inferInstance
  letI : IsScalarTower R (FractionRing R) (LocalizedModule R⁰ M →ₗ[R] FractionRing R) :=
    inferInstance
  refine
    { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    letI :
        IsLocalizedModule R⁰
          (.id (R := R) (M := LocalizedModule R⁰ M →ₗ[R] FractionRing R)) :=
      isLocalizedModule_id
        (S := R⁰) (M := LocalizedModule R⁰ M →ₗ[R] FractionRing R) (R' := FractionRing R)
    -- Scalar multiplication by a nonzero denominator is invertible on a fraction-field vector
    -- space, so the same is true on this function space.
    simpa using
      (IsLocalizedModule.map_units
        (S := R⁰)
        (f := (.id (R := R) (M := LocalizedModule R⁰ M →ₗ[R] FractionRing R))) s)
  · intro ψ
    obtain ⟨c, hc, ℓ₀, hℓ₀⟩ :=
      exists_smul_eq_algebraMap_comp_fractionRing (R := R) (M := M)
        (ψ.comp (LocalizedModule.mkLinearMap R⁰ M))
    refine ⟨⟨ℓ₀, ⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc⟩⟩, ?_⟩
    -- Route correction: first compare the two candidate functionals after precomposing with the
    -- localization map `M → M[R⁰⁻¹]`, then invoke localization extensionality.
    apply IsLocalizedModule.linearMap_ext (S := R⁰)
      (LocalizedModule.mkLinearMap R⁰ M)
      (Algebra.linearMap R (FractionRing R))
    ext m
    calc
      ((((⟨c, mem_nonZeroDivisors_iff_ne_zero.mpr hc⟩ : R⁰) • ψ).comp
          (LocalizedModule.mkLinearMap R⁰ M)) m)
          = (((c : R) • (ψ.comp (LocalizedModule.mkLinearMap R⁰ M))) m) := by
              simp [LinearMap.comp_apply]
      _ = (((Algebra.linearMap R (FractionRing R)).comp ℓ₀) m) := by
            simpa [LinearMap.comp_apply] using
              (congrArg (fun f : M →ₗ[R] FractionRing R => f m) hℓ₀).symm
      _ = (((localized_dual_raw_map (R := R) (M := M) ℓ₀).comp
            (LocalizedModule.mkLinearMap R⁰ M)) m) := by
            rw [localized_dual_raw_map_comp]
  · intro φ₁ φ₂ h
    have hcomp :
        (localized_dual_raw_map (R := R) (M := M) φ₁).comp (LocalizedModule.mkLinearMap R⁰ M) =
          (localized_dual_raw_map (R := R) (M := M) φ₂).comp
            (LocalizedModule.mkLinearMap R⁰ M) := by
      simpa using congrArg
        (fun ψ : LocalizedModule R⁰ M →ₗ[R] FractionRing R =>
          ψ.comp (LocalizedModule.mkLinearMap R⁰ M)) h
    have hφ : φ₁ = φ₂ := by
      ext m
      have hm :
          algebraMap R (FractionRing R) (φ₁ m) = algebraMap R (FractionRing R) (φ₂ m) := by
        simpa [localized_dual_raw_map_comp, LinearMap.comp_apply] using
          congrArg (fun f : M →ₗ[R] FractionRing R => f m) hcomp
      exact (IsFractionRing.injective R (FractionRing R)) hm
    exact ⟨1, by simpa [hφ]⟩

/-- Helper for Lemma 15.23.2: after upgrading the codomain to genuine
`FractionRing R`-linear functionals, the dual localization comparison is still a localization map.
-/
private noncomputable def dual_localization_map :
    Dual R M →ₗ[R] Dual (FractionRing R) (LocalizedModule R⁰ M) :=
  (((LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := LocalizedModule R⁰ M) (N := FractionRing R)).restrictScalars R).toLinearMap) ∘ₗ
    localized_dual_raw_map (R := R) (M := M)

/-- Helper for Lemma 15.23.2: the genuine dual localization comparison is obtained from the raw
one by a codomain linear equivalence, so it also satisfies the localization universal property. -/
private theorem dual_localization_map_isLocalizedModule :
    IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) := by
  let e : (LocalizedModule R⁰ M →ₗ[R] FractionRing R) ≃ₗ[R]
      Dual (FractionRing R) (LocalizedModule R⁰ M) :=
    (LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := LocalizedModule R⁰ M) (N := FractionRing R)).restrictScalars R
  letI : IsLocalizedModule R⁰ (localized_dual_raw_map (R := R) (M := M)) :=
    localized_dual_raw_map_isLocalizedModule (R := R) (M := M)
  -- Transport the localization property across the linear equivalence from `R`-linear to
  -- `FractionRing R`-linear functionals on the generic fiber.
  simpa [dual_localization_map, e] using
    (show IsLocalizedModule R⁰ (e.toLinearMap ∘ₗ localized_dual_raw_map (R := R) (M := M))
      from inferInstance)

/-- Helper for Lemma 15.23.2: localizing a bidual element along the canonical dual localization map
gives an `R`-linear fraction-field-valued functional on the generic dual. -/
private noncomputable def localized_bidual_raw_map :
    Dual R (Dual R M) →ₗ[R] (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) :=
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) :=
    dual_localization_map_isLocalizedModule (R := R) (M := M)
  IsLocalizedModule.map R⁰ (dual_localization_map (R := R) (M := M))
    (Algebra.linearMap R (FractionRing R))

/-- Helper for Lemma 15.23.2: on denominator-`1` generators in the dual, the raw bidual
localization map is still the defining localization square. -/
private theorem localized_bidual_raw_map_comp (Φ : Dual R (Dual R M)) :
    (localized_bidual_raw_map (R := R) (M := M) Φ).comp
        (dual_localization_map (R := R) (M := M)) =
      (Algebra.linearMap R (FractionRing R)).comp Φ := by
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) :=
    dual_localization_map_isLocalizedModule (R := R) (M := M)
  -- This is the bidual analogue of `localized_dual_raw_map_comp`.
  simpa [localized_bidual_raw_map] using
    (IsLocalizedModule.map_comp (S := R⁰)
      (f := dual_localization_map (R := R) (M := M))
      (g := Algebra.linearMap R (FractionRing R))
      (h := Φ))

/-- Helper for Lemma 15.23.2: after upgrading the raw bidual codomain to genuine
`FractionRing R`-linear functionals, the image of `eval R M m` is ordinary evaluation at the
localized generator `LocalizedModule.mk m 1`. -/
private theorem localized_bidual_raw_map_eval (m : M) :
    let e :
      (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) ≃ₗ[R]
        Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
      (LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
        (M := Dual (FractionRing R) (LocalizedModule R⁰ M)) (N := FractionRing R)).restrictScalars
        R
    e (localized_bidual_raw_map (R := R) (M := M) (eval R M m)) =
      Dual.eval (FractionRing R) (LocalizedModule R⁰ M) (LocalizedModule.mk m 1) := by
  let e :
      (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) ≃ₗ[R]
        Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
    (LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := Dual (FractionRing R) (LocalizedModule R⁰ M)) (N := FractionRing R)).restrictScalars R
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) :=
    dual_localization_map_isLocalizedModule (R := R) (M := M)
  apply LinearMap.restrictScalars_injective R
  -- Compare the two candidate bidual functionals after precomposing with the dual localization map.
  apply IsLocalizedModule.linearMap_ext (S := R⁰)
    (dual_localization_map (R := R) (M := M))
    (Algebra.linearMap R (FractionRing R))
  ext φ
  have hleft := congrArg
      (fun f : Dual R M →ₗ[R] FractionRing R => f φ)
      (localized_bidual_raw_map_comp (R := R) (M := M) (Φ := eval R M m))
  have hright := congrArg
      (fun f : M →ₗ[R] FractionRing R => f m)
      (localized_dual_raw_map_comp (R := R) (M := M) (φ := φ))
  -- Both composites reduce to the scalar `φ m` viewed in the fraction field.
  simpa [e, dual_localization_map, LinearMap.comp_apply,
    LinearEquiv.restrictScalars_apply, Module.Dual.eval_apply] using hleft.trans hright.symm

/-- Helper for Lemma 15.23.2: every raw `R`-linear functional on the localized dual becomes, after
one denominator, the image of an evaluation functional coming from `M`. -/
private theorem localized_bidual_raw_map_surj
    (ψ : Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) :
    ∃ m : M, ∃ s : R⁰,
      s • ψ = localized_bidual_raw_map (R := R) (M := M) (eval R M m) := by
  let e :
      (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) ≃ₗ[R]
        Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
    (LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := Dual (FractionRing R) (LocalizedModule R⁰ M)) (N := FractionRing R)).restrictScalars R
  obtain ⟨x, hx⟩ :=
    (Module.bijective_dual_eval (FractionRing R) (LocalizedModule R⁰ M)).2 (e ψ)
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj R⁰ (LocalizedModule.mkLinearMap R⁰ M) x
  refine ⟨m, s, e.injective ?_⟩
  -- Route correction: represent the upgraded functional by evaluation on the generic fiber first,
  -- then clear one denominator on that localized vector.
  calc
    e (s • ψ) = (s : R) • e ψ := by
      simpa [Submonoid.smul_def] using e.map_smul (s : R) ψ
    _ = (s : R) • Dual.eval (FractionRing R) (LocalizedModule R⁰ M) x := by rw [hx]
    _ = Dual.eval (FractionRing R) (LocalizedModule R⁰ M) ((s : R) • x) := by
          ext φ
          simp [Module.Dual.eval_apply]
    _ = Dual.eval (FractionRing R) (LocalizedModule R⁰ M) (LocalizedModule.mk m 1) := by
          simpa [LocalizedModule.mkLinearMap_apply] using congrArg
            (fun y : LocalizedModule R⁰ M =>
              Dual.eval (FractionRing R) (LocalizedModule R⁰ M) y) hs
    _ = e (localized_bidual_raw_map (R := R) (M := M) (eval R M m)) := by
          simpa [e] using (localized_bidual_raw_map_eval (R := R) (M := M) m).symm

/-- Helper for Lemma 15.23.2: equality in the raw localized bidual already forces equality in the
source bidual after multiplying by a denominator, and here denominator `1` suffices. -/
private theorem localized_bidual_raw_map_exists_of_eq
    {Φ₁ Φ₂ : Dual R (Dual R M)}
    (hΦ :
      localized_bidual_raw_map (R := R) (M := M) Φ₁ =
        localized_bidual_raw_map (R := R) (M := M) Φ₂) :
    ∃ s : R⁰, s • Φ₁ = s • Φ₂ := by
  have hcomp :
      (localized_bidual_raw_map (R := R) (M := M) Φ₁).comp
          (dual_localization_map (R := R) (M := M)) =
        (localized_bidual_raw_map (R := R) (M := M) Φ₂).comp
          (dual_localization_map (R := R) (M := M)) := by
    simpa using congrArg
      (fun ψ : Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R =>
        ψ.comp (dual_localization_map (R := R) (M := M))) hΦ
  have hEq : Φ₁ = Φ₂ := by
    -- Precomposing with `dual_localization_map` reduces equality to equality after applying the
    -- fraction-field algebra map pointwise on the original dual.
    ext φ
    have hφ :
        algebraMap R (FractionRing R) (Φ₁ φ) = algebraMap R (FractionRing R) (Φ₂ φ) := by
      simpa [localized_bidual_raw_map_comp, LinearMap.comp_apply] using
        congrArg (fun f : Dual R M →ₗ[R] FractionRing R => f φ) hcomp
    exact (IsFractionRing.injective R (FractionRing R)) hφ
  exact ⟨1, by simpa [hEq]⟩

private theorem localized_bidual_raw_map_isLocalizedModule :
    IsLocalizedModule R⁰ (localized_bidual_raw_map (R := R) (M := M)) := by
  classical
  letI :
      Module (FractionRing R)
        (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) := inferInstance
  letI :
      IsScalarTower R (FractionRing R)
        (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) := inferInstance
  refine
    { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro s
    -- The raw bidual codomain is still a vector space over the fraction field, so multiplying by a
    -- denominator acts invertibly.
    rw [← (Algebra.lsmul R
      (A := FractionRing R) R
      (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R)).commutes]
    exact (IsLocalization.map_units (FractionRing R) s).map _
  · intro ψ
    obtain ⟨m, s, hs⟩ := localized_bidual_raw_map_surj (R := R) (M := M) ψ
    exact ⟨⟨eval R M m, s⟩, hs⟩
  · intro Φ₁ Φ₂ hΦ
    exact localized_bidual_raw_map_exists_of_eq (R := R) (M := M) hΦ

/-- Helper for Lemma 15.23.2: after upgrading the codomain to genuine
`FractionRing R`-linear bidual functionals, the bidual localization comparison is still a
localization map. -/
private noncomputable def bidual_localization_map :
    Dual R (Dual R M) →ₗ[R]
      Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
  (((LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := Dual (FractionRing R) (LocalizedModule R⁰ M)) (N := FractionRing R)).restrictScalars
      R).toLinearMap) ∘ₗ
    localized_bidual_raw_map (R := R) (M := M)

/-- Helper for Lemma 15.23.2: the bidual localization comparison is obtained from the raw bidual
map by the same codomain linear equivalence as in the dual case, so it inherits the localization
universal property. -/
private theorem bidual_localization_map_isLocalizedModule :
    IsLocalizedModule R⁰ (bidual_localization_map (R := R) (M := M)) := by
  let e :
      (Dual (FractionRing R) (LocalizedModule R⁰ M) →ₗ[R] FractionRing R) ≃ₗ[R]
        Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
    (LinearMap.extendScalarsOfIsLocalizationEquiv (R⁰) (FractionRing R)
      (M := Dual (FractionRing R) (LocalizedModule R⁰ M)) (N := FractionRing R)).restrictScalars R
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) :=
    dual_localization_map_isLocalizedModule (R := R) (M := M)
  letI : IsLocalizedModule R⁰ (localized_bidual_raw_map (R := R) (M := M)) :=
    localized_bidual_raw_map_isLocalizedModule (R := R) (M := M)
  -- Route correction: the previous proof attempt left the localized double dual with an opaque
  -- codomain comparison. Making it a canonical localization map restores the source generic-fiber
  -- route before the final denominator-`1` evaluation comparison.
  simpa [bidual_localization_map, e] using
    (show IsLocalizedModule R⁰ (e.toLinearMap ∘ₗ localized_bidual_raw_map (R := R) (M := M))
      from inferInstance)

/-- Helper for Lemma 15.23.2: the canonical identification between the localized dual and the dual
of the generic fiber. -/
private noncomputable abbrev dual_localization_linearEquiv :
    LocalizedModule R⁰ (Dual R M) ≃ₗ[R] Dual (FractionRing R) (LocalizedModule R⁰ M) :=
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) :=
    dual_localization_map_isLocalizedModule (R := R) (M := M)
  IsLocalizedModule.linearEquiv R⁰
    (LocalizedModule.mkLinearMap R⁰ (Dual R M))
    (dual_localization_map (R := R) (M := M))

/-- Helper for Lemma 15.23.2: the canonical identification between the localized bidual and the
bidual of the generic fiber. -/
private noncomputable abbrev bidual_localization_linearEquiv :
    LocalizedModule R⁰ (Dual R (Dual R M)) ≃ₗ[R]
      Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
  letI : IsLocalizedModule R⁰ (bidual_localization_map (R := R) (M := M)) :=
    bidual_localization_map_isLocalizedModule (R := R) (M := M)
  IsLocalizedModule.linearEquiv R⁰
    (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R M)))
    (bidual_localization_map (R := R) (M := M))

/-- Helper for Lemma 15.23.2: after transporting the localized evaluation map through the bidual
localization equivalence, its restriction to denominator-`1` generators agrees with the fraction
field evaluation map when both are tested on denominator-`1` dual generators. -/
private theorem localized_eval_compare_on_generators (x : M) :
    (((bidual_localization_linearEquiv (R := R) (M := M)
        ((LocalizedModule.map R⁰ (eval R M)) (LocalizedModule.mk x 1))).restrictScalars R).comp
        (dual_localization_map (R := R) (M := M))) =
      (((Dual.eval (FractionRing R) (LocalizedModule R⁰ M) (LocalizedModule.mk x 1)).restrictScalars R).comp
        (dual_localization_map (R := R) (M := M))) := by
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) :=
    dual_localization_map_isLocalizedModule (R := R) (M := M)
  letI : IsLocalizedModule R⁰ (bidual_localization_map (R := R) (M := M)) :=
    bidual_localization_map_isLocalizedModule (R := R) (M := M)
  -- First rewrite the transported localized evaluation map on the numerator generator `x`.
  have hBidual :
      bidual_localization_linearEquiv (R := R) (M := M)
          ((LocalizedModule.map R⁰ (eval R M)) (LocalizedModule.mk x 1)) =
        bidual_localization_map (R := R) (M := M) (eval R M x) := by
    rw [LocalizedModule.map_mk]
    simpa [bidual_localization_linearEquiv] using
      (IsLocalizedModule.linearEquiv_apply (S := R⁰)
        (LocalizedModule.mkLinearMap R⁰ (Dual R (Dual R M)))
        (bidual_localization_map (R := R) (M := M))
        (eval R M x))
  rw [hBidual]
  ext φ
  -- Compare both transported functionals after precomposing with `dual_localization_map`.
  have hleft := congrArg
      (fun f : Dual R M →ₗ[R] FractionRing R => f φ)
      (localized_bidual_raw_map_comp (R := R) (M := M) (Φ := eval R M x))
  have hright := congrArg
      (fun f : M →ₗ[R] FractionRing R => f x)
      (localized_dual_raw_map_comp (R := R) (M := M) φ)
  -- Both sides reduce to the scalar `φ x` viewed in the fraction field.
  simpa [bidual_localization_map, dual_localization_map, bidual_localization_linearEquiv,
    dual_localization_linearEquiv, LinearMap.comp_apply,
    LinearEquiv.restrictScalars_apply, Module.Dual.eval_apply] using hleft.trans hright.symm

/-- Helper for Lemma 15.23.2: after transporting the localized evaluation map through the bidual
localization equivalence, one recovers the usual evaluation map on the generic fiber. -/
private theorem localized_eval_transport_eq_fraction_eval :
    (bidual_localization_linearEquiv (R := R) (M := M)).toLinearMap.comp
        (LinearMap.restrictScalars R (LocalizedModule.map R⁰ (eval R M))) =
      LinearMap.restrictScalars R
        (Dual.eval (FractionRing R) (LocalizedModule R⁰ M)) := by
  letI : IsLocalizedModule R⁰ (dual_localization_map (R := R) (M := M)) :=
    dual_localization_map_isLocalizedModule (R := R) (M := M)
  letI : IsLocalizedModule R⁰ (bidual_localization_map (R := R) (M := M)) :=
    bidual_localization_map_isLocalizedModule (R := R) (M := M)
  -- Route correction: compare the two maps out of the localized source by first restricting both
  -- codomain functionals along `dual_localization_map`.
  apply IsLocalizedModule.linearMap_ext (S := R⁰)
    (LocalizedModule.mkLinearMap R⁰ M)
    (bidual_localization_map (R := R) (M := M))
  apply LinearMap.ext
  intro x
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext (S := R⁰)
    (dual_localization_map (R := R) (M := M))
    (Algebra.linearMap R (FractionRing R))
  simpa [LinearMap.comp_apply] using
    localized_eval_compare_on_generators (R := R) (M := M) x

/-- Helper for Lemma 15.23.2: the localized canonical evaluation map is bijective on the generic
fiber. -/
private theorem localized_eval_bijective :
    Function.Bijective (LocalizedModule.map R⁰ (eval R M)) := by
  letI : IsLocalizedModule R⁰ (bidual_localization_map (R := R) (M := M)) :=
    bidual_localization_map_isLocalizedModule (R := R) (M := M)
  let eBidual :
      LocalizedModule R⁰ (Dual R (Dual R M)) ≃ₗ[R]
        Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
    bidual_localization_linearEquiv (R := R) (M := M)
  let transported :
      LocalizedModule R⁰ M →ₗ[R]
        Dual (FractionRing R) (Dual (FractionRing R) (LocalizedModule R⁰ M)) :=
    eBidual.toLinearMap.comp
      (LinearMap.restrictScalars R (LocalizedModule.map R⁰ (eval R M)))
  have htransport :
      Function.Bijective transported := by
    rw [show transported =
        LinearMap.restrictScalars R
          (Dual.eval (FractionRing R) (LocalizedModule R⁰ M)) by
          simpa [transported] using
            localized_eval_transport_eq_fraction_eval (R := R) (M := M)]
    simpa using
      (Module.bijective_dual_eval (FractionRing R) (LocalizedModule R⁰ M))
  constructor
  · intro x y hxy
    apply htransport.injective
    simpa [transported, hxy]
  · intro z
    obtain ⟨x, hx⟩ := htransport.surjective (eBidual z)
    refine ⟨x, ?_⟩
    apply eBidual.injective
    simpa [transported] using hx

/-- Helper for Lemma 15.23.2: the torsion conclusion follows immediately once the localized
evaluation map on the generic fiber is known to be bijective. -/
private theorem localized_quotient_subsingleton_of_localized_eq_top
    {N : Type*} [AddCommGroup N] [Module R N]
    (P : Submodule R N) (hP : Submodule.localized (p := R⁰) P = ⊤) :
    Subsingleton (LocalizedModule R⁰ (N ⧸ P)) := by
  let e :
      (LocalizedModule R⁰ N ⧸ Submodule.localized (p := R⁰) P) ≃ₗ[FractionRing R]
        LocalizedModule R⁰ (N ⧸ P) :=
    localizedQuotientEquiv R⁰ P
  have hquot :
      Subsingleton (LocalizedModule R⁰ N ⧸ Submodule.localized (p := R⁰) P) := by
    rw [hP]
    infer_instance
  -- Once the localized submodule is all of the generic fiber, the localized quotient is the
  -- quotient by `⊤`, hence trivial.
  letI : Subsingleton (LocalizedModule R⁰ N ⧸ Submodule.localized (p := R⁰) P) := hquot
  exact e.symm.toEquiv.subsingleton

/-- Helper for Lemma 15.23.2: the torsion conclusion follows immediately once the localized
evaluation map on the generic fiber is known to be bijective. -/
private theorem localized_cokernel_subsingleton_of_bijective_eval
    (hbij : Function.Bijective (LocalizedModule.map R⁰ (eval R M))) :
    Subsingleton (LocalizedModule R⁰ (Dual R (Dual R M) ⧸ (eval R M).range)) := by
  let D : Type max u v := Dual R (Dual R M)
  let Q : Submodule R D := (eval R M).range
  let locEvalR : LocalizedModule R⁰ M →ₗ[R] LocalizedModule R⁰ D :=
    IsLocalizedModule.map R⁰
      (LocalizedModule.mkLinearMap R⁰ M)
      (LocalizedModule.mkLinearMap R⁰ D)
      (eval R M)
  have hsurjR : Function.Surjective locEvalR := by
    simpa [locEvalR, LocalizedModule.map] using hbij.surjective
  have hlocalized_range_top :
      Submodule.localized₀ R⁰ (LocalizedModule.mkLinearMap R⁰ D) Q = ⊤ := by
    -- Surjectivity of the localized evaluation map says its range is the whole generic fiber, and
    -- the owner theorem identifies that range with the localization of the original image.
    calc
      Submodule.localized₀ R⁰ (LocalizedModule.mkLinearMap R⁰ D) Q
          = locEvalR.range := by
              symm
              simpa [Q, D, locEvalR] using
                (LinearMap.range_localizedMap_eq_localized₀_range
                  (p := R⁰)
                  (f := LocalizedModule.mkLinearMap R⁰ M)
                  (f' := LocalizedModule.mkLinearMap R⁰ D)
                  (g := eval R M))
      _ = ⊤ := LinearMap.range_eq_top.2 hsurjR
  have hlocalized_top : Submodule.localized (p := R⁰) Q = ⊤ := by
    -- `Submodule.localized` is the same carrier as `localized₀`, now viewed over the fraction
    -- field rather than only after restricting scalars.
    ext x
    change x ∈ Submodule.localized₀ R⁰ (LocalizedModule.mkLinearMap R⁰ D) Q ↔
      x ∈ (⊤ : Submodule R (LocalizedModule R⁰ D))
    rw [hlocalized_range_top]
  -- Once the localized image is all of the generic fiber, the localized quotient vanishes.
  exact
    localized_quotient_subsingleton_of_localized_eq_top
      (R := R) (P := Q) hlocalized_top

/-- Helper for Lemma 15.23.2: the torsion conclusion follows immediately once the localized
evaluation map on the generic fiber is known to be bijective. -/
private theorem eval_cokernel_isTorsion_of_localized_eval_bijective
    (hbij : Function.Bijective (LocalizedModule.map R⁰ (eval R M))) :
    IsTorsion R (Dual R (Dual R M) ⧸ (eval R M).range) := by
  let D : Type max u v := Dual R (Dual R M)
  let Q : Submodule R D := (eval R M).range
  have hsub :
      Subsingleton (LocalizedModule R⁰ (D ⧸ Q)) :=
    localized_cokernel_subsingleton_of_bijective_eval (R := R) (M := M) hbij
  rw [LocalizedModule.subsingleton_iff (S := R⁰) (M := D ⧸ Q)] at hsub
  intro x
  -- The localized quotient is zero, so every quotient class is killed by a nonzero denominator.
  rcases hsub x with ⟨r, hr, hzero⟩
  exact ⟨⟨r, hr⟩, hzero⟩

/-- Lemma 15.23.2 (3): if `M` is finite, then the cokernel of the canonical map from `M` to its
double dual is a torsion module. -/
@[stacks 0AV0]
theorem eval_cokernel_isTorsion :
    IsTorsion R (Dual R (Dual R M) ⧸ (eval R M).range) := by
  -- Route correction: the quotient-side exactness argument is now isolated in
  -- `eval_cokernel_isTorsion_of_localized_eval_bijective`, so the only remaining job is the
  -- source-faithful generic-fiber comparison showing that the localized evaluation map becomes the
  -- usual bidual evaluation over `FractionRing R`.
  refine eval_cokernel_isTorsion_of_localized_eval_bijective (R := R) (M := M) ?_
  -- The transported localized evaluation map is exactly the bidual evaluation over the fraction
  -- field, so it inherits bijectivity from the vector-space owner theorem.
  exact localized_eval_bijective (R := R) (M := M)

-- Proof sketch: if `M` is torsion free, the denominator-clearing map to a finite free module
-- constructed above is injective, forcing the evaluation map to be injective. Conversely, if the
-- evaluation map is injective, then `M` embeds into its torsion-free double dual.
/-- Lemma 15.23.2 (4): for a finite module over a domain, the canonical map to the double dual is
injective exactly when the module is torsion free. -/
@[stacks 0AV0]
theorem eval_injective_iff_isTorsionFree :
    Function.Injective (eval R M) ↔ IsTorsionFree R M := by
  constructor
  · intro hinj
    -- The double dual is torsion free, and an injective evaluation map transfers that structure
    -- back to `M`.
    letI : IsTorsionFree R (Dual R (Dual R M)) := inferInstance
    exact hinj.moduleIsTorsionFree _ fun r x => by simp
  · intro htf
    -- Route correction: instead of rebuilding a torsion-free structure on the kernel, use the
    -- torsion witness from `eval_ker_isTorsion` and cancel it in the ambient torsion-free module.
    intro x y hxy
    have hker : x - y ∈ (eval R M).ker := by
      simp [LinearMap.mem_ker, map_sub, hxy]
    obtain ⟨a, ha⟩ := eval_ker_isTorsion (R := R) (M := M) (x := ⟨x - y, hker⟩)
    have ha' : (a : R) • (x - y) = 0 := by
      exact congrArg Subtype.val ha
    have hsub : x - y = 0 := (smul_eq_zero.mp ha').resolve_left (by simpa using a.2)
    exact sub_eq_zero.mp hsub

end Finite
