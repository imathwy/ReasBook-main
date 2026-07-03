import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.Data.List.TFAE
import Mathlib.Data.PNat.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Ideal.Quotient.Operations

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_89_1 (from Chap15) -/
universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The finite-stage `I^n`-torsion submodule of `M`, i.e. the source-facing finite ideal-power
torsion owner underlying the chapter notation `M[I^n]`. -/
abbrev powerTorsion (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] (n : ℕ) :
    Submodule R M :=
  Submodule.torsionBySet R M ↑(I ^ n)

end Ideal

namespace IdealPowerTorsion

open Lean Elab Term Meta

variable {R : Type u} [CommRing R]

/- Source-facing notation for finite and infinite power torsion submodules. The index can be an
ideal `I`, giving `M[I^n]` and `M[I^∞]`, or an element `f`, giving the principal specializations
`M[f^n]` and `M[f^∞]`. The notation is a thin bridge to the canonical owners
`Submodule.torsionBySet`, `Ideal.primaryComponent`, `Submodule.torsionBy`, and
`Submodule.torsion'`; the implementation support stays confined to the
`IdealPowerTorsion` namespace. -/
syntax:lead term:max noWs "[" term:max "^" term:max "]" : term
syntax:lead term:max noWs "[" term:max "^∞]" : term

private def elabFinitePowerTorsion
    (M a n : TSyntax `term) : TermElabM Expr := do
  let aExpr ← elabTerm a none
  let aType ← inferType aExpr
  if aType.isAppOf ``Ideal then
    elabTerm (← `((Ideal.powerTorsion $a $M $n))) none
  else
    elabTerm (← `((Submodule.torsionBy _ $M ($a ^ $n)))) none

private def elabInfinitePowerTorsion
    (M a : TSyntax `term) : TermElabM Expr := do
  let aExpr ← elabTerm a none
  let aType ← inferType aExpr
  if aType.isAppOf ``Ideal then
    elabTerm (← `((($a).primaryComponent $M))) none
  else
    elabTerm (← `((Submodule.torsion' _ $M (Submonoid.powers $a)))) none

@[term_elab IdealPowerTorsion.«term__[_^_]»] private def elabTermFinitePowerTorsion : TermElab
  | stx, _ => elabFinitePowerTorsion ⟨stx[0]⟩ ⟨stx[2]⟩ ⟨stx[4]⟩

@[term_elab IdealPowerTorsion.«term__[_^∞]»] private def elabTermInfinitePowerTorsion : TermElab
  | stx, _ => elabInfinitePowerTorsion ⟨stx[0]⟩ ⟨stx[2]⟩

end IdealPowerTorsion

namespace Module

open scoped DirectSum
open scoped IdealPowerTorsion

variable {R : Type u} [CommRing R]

section

/- 
Domain-style sampling pass for Definition 15.89.1.

Primary domain: commutative algebra of ideal-power torsion modules.

Sampled owner declarations:
* `Submodule.torsionBySet` from mathlib's torsion-submodule API;
* `Ideal.primaryComponent` and `Ideal.primaryComponent_mem` from mathlib's primary-component API;
* `Module.IsTorsion'` and `Submodule.isTorsion'_iff_torsion'_eq_top` from mathlib's
  powers-torsion API.

Best owner abstraction: the source-facing module predicate should be the chapter owner
`Module.IsIdealPowerTorsion I M`, with its core owner given directly by `Ideal.primaryComponent`
and its source-facing theorem surface written using the chapter notation `M[I^n]`, `M[I^∞]`,
`M[f^n]`, and `M[f^∞]`.
-/

/-- Definition 15.89.1 (1): an `R`-module is `I`-power torsion if every element is annihilated by
some positive power of the ideal `I`, equivalently if `M[I^∞] = ⊤`. -/
abbrev IsIdealPowerTorsion (I : Ideal R) (M : Type v) [AddCommMonoid M] [Module R M] : Prop :=
  (M[I^∞] : Submodule R M) = ⊤

variable {M : Type v} [AddCommMonoid M] [Module R M]

/-- The predicate `IsIdealPowerTorsion I` means that each module element is killed by some
positive power of `I`. -/
theorem isIdealPowerTorsion_iff (I : Ideal R) :
    IsIdealPowerTorsion I M ↔
      ∀ x : M, ∃ n : ℕ+, ∀ a : ↥(I ^ (n : ℕ)), (a : R) • x = 0 := by
  constructor
  · intro hM x
    have hx : x ∈ (M[I^∞] : Submodule R M) := by
      rw [hM]
      exact Submodule.mem_top
    rw [Ideal.primaryComponent_mem] at hx
    obtain ⟨n, hn⟩ := hx
    rw [Submodule.mem_torsionBySet_iff] at hn
    refine ⟨⟨n + 1, Nat.succ_pos n⟩, fun a ↦ ?_⟩
    exact hn ⟨a, Ideal.pow_le_pow_right (Nat.le_succ n) a.2⟩
  · intro hM
    refine Submodule.eq_top_iff'.2 fun x ↦ ?_
    rw [Ideal.primaryComponent_mem]
    obtain ⟨n, hn⟩ := hM x
    exact ⟨(n : ℕ), by simpa [Submodule.mem_torsionBySet_iff] using hn⟩

/-- The quotient `R ⧸ I^n` is `I`-power torsion. -/
theorem isIdealPowerTorsion_quotient_pow (I : Ideal R) (n : ℕ) :
    IsIdealPowerTorsion I (R ⧸ (I ^ n)) := sorry

/-- Linear-equivalent modules have the same `I`-power torsion property. -/
theorem isIdealPowerTorsion_iff_of_linearEquiv
    (I : Ideal R) {N : Type*} [AddCommMonoid N] [Module R N] (e : M ≃ₗ[R] N) :
    IsIdealPowerTorsion I M ↔ IsIdealPowerTorsion I N := sorry

/-- A direct sum of `I`-power torsion modules is `I`-power torsion. -/
theorem isIdealPowerTorsion_directSum
    (I : Ideal R) {ι : Type*} {A : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    (hA : ∀ i, IsIdealPowerTorsion I (A i)) :
    IsIdealPowerTorsion I (⨁ i, A i) := sorry

/-- Definition 15.89.1 (2): specializing to the principal ideal `(f)` identifies the chapter
notation `M[(f)^∞]` with the canonical `f`-power torsion submodule. -/
theorem primaryComponent_principalIdeal_eq_fPowerTorsion (f : R) :
    (M[(principalIdeal f)^∞] : Submodule R M) = M[f^∞] := by
  ext x
  constructor
  · intro hx
    have hx₀ :
        ∃ n, x ∈ Submodule.torsionBySet R M ↑(principalIdeal f ^ n) := by
      simpa using (Ideal.primaryComponent_mem M (principalIdeal f) x).1 hx
    rcases hx₀ with ⟨n, hx⟩
    have hx' : x ∈ Submodule.torsionBy R M (f ^ n) := by
      simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx
    rw [Submodule.mem_torsionBy_iff] at hx'
    exact ⟨⟨f ^ n, ⟨n, rfl⟩⟩, hx'⟩
  · rintro ⟨⟨a, ha⟩, hx⟩
    rcases (Submonoid.mem_powers_iff a f).mp ha with ⟨n, hn⟩
    have hx' : x ∈ Submodule.torsionBy R M (f ^ n) := by
      rw [Submodule.mem_torsionBy_iff]
      exact hn.symm ▸ hx
    refine (Ideal.primaryComponent_mem M (principalIdeal f) x).2 ?_
    exact ⟨n, by
      simpa [Ideal.span_singleton_pow, Submodule.torsionBySet_ideal_span_singleton_eq] using hx'⟩

/-- Definition 15.89.1 (2): specializing to the principal ideal `(f)` recovers mathlib's
canonical `f`-power torsion predicate `Module.IsTorsion' M (Submonoid.powers f)`. -/
theorem isIdealPowerTorsion_principalIdeal_iff (f : R) :
    IsIdealPowerTorsion (principalIdeal f) M ↔ IsTorsion' M (Submonoid.powers f) := by
  rw [IsIdealPowerTorsion, primaryComponent_principalIdeal_eq_fPowerTorsion]
  simpa using (Submodule.isTorsion'_iff_torsion'_eq_top (Submonoid.powers f)).symm

end

end Module

/-! ### Lemma_15_89_2 (from Chap15) -/
open CategoryTheory ChainComplex
open scoped DirectSum

universe u

/-
Domain-style sampling for ideal-power torsion resolutions:
- primary domain: chain-complex resolutions of modules whose terms are direct sums of ideal-power
  quotients;
- same-domain declarations inspected:
  `QuasiIso`,
  `Module.IsIdealPowerTorsion`,
  `ChainComplex.IsFreeResolution`,
  `ChainComplex.IsFiniteFreeResolution`;
- best owner abstraction: the augmented chain complex data
  `π : F ⟶ moduleSingle[R] M` together with the canonical owner
  `QuasiIso π`; the source-specific extra datum is only the termwise direct-sum-of-quotients
  predicate on `F`;
- primitive data: the augmented chain complex and the degreewise direct-sum-of-quotients property;
- derived API: exactness and surjectivity of the resolution are carried by the canonical
  chain-complex owner `QuasiIso π`, while closure of `Module.IsIdealPowerTorsion` under linear
  equivalence and direct sums belongs to the module owner API rather than to a parallel
  chain-complex-specific wrapper.

Layer triage:
- `source-facing`: the existence of an infinite resolution by direct sums of quotients `R ⧸ I^n`;
- `core/canonical`: the augmented chain-complex owner with `QuasiIso π`;
- `bridge/view`: the termwise predicate recording that each degree is a direct sum of ideal-power
  quotients.

The previous local wrapper duplicated the chain-complex owner `QuasiIso π`. This file should
express the same mathematics directly over the canonical augmentation together with the
source-specific termwise quotient condition, reusing the owner-level `Module.IsIdealPowerTorsion`
API from `Definition_15_89_1` rather than re-declaring it locally.
-/

namespace ChainComplex

/-- A chain complex of `R`-modules is termwise a direct sum of quotients `R ⧸ I^n`, with the
exponent allowed to vary from summand to summand and from degree to degree. The summand index may
live in the module universe of the complex. -/
def IsTermwiseDirectSumOfIdealPowerQuotients
    {R : Type u} [CommRing R] (I : Ideal R) (F : ChainComplex (ModuleCat R) ℕ) : Prop :=
  ∀ n : ℕ, ∃ (ι : Type u) (exponent : ι → ℕ),
    Nonempty (F.X n ≃ₗ[R] (⨁ j : ι, R ⧸ (I ^ exponent j)))

section

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {F : ChainComplex (ModuleCat R) ℕ}

namespace IsTermwiseDirectSumOfIdealPowerQuotients

/-- Every term of a chain complex that is a direct sum of quotients `R ⧸ I^n` is `I`-power
torsion. This is derived API from the direct-sum presentation, not additional primitive data. -/
theorem isIdealPowerTorsion
    (hF : F.IsTermwiseDirectSumOfIdealPowerQuotients I) (n : ℕ) :
    Module.IsIdealPowerTorsion I (F.X n) := by
  rcases hF n with ⟨ι, exponent, ⟨e⟩⟩
  have hsum : Module.IsIdealPowerTorsion I (⨁ j : ι, R ⧸ (I ^ exponent j)) :=
    Module.isIdealPowerTorsion_directSum I fun j ↦
      Module.isIdealPowerTorsion_quotient_pow I (exponent j)
  exact (Module.isIdealPowerTorsion_iff_of_linearEquiv I e).2 hsum

end IsTermwiseDirectSumOfIdealPowerQuotients

end

end ChainComplex

section

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : ModuleCat R)

local notation "moduleSingle[" R "]" M =>
  CategoryTheory.Functor.obj (single₀ (ModuleCat R)) M

-- Proof sketch: for each `m : M`, choose a power `I^(n_m)` annihilating `m` and obtain a
-- canonical surjection from the direct sum of the cyclic quotients `R ⧸ I^(n_m)` onto `M`. Its
-- kernel is again `I`-power torsion, so iterating the same construction yields an exact infinite
-- resolution by such direct sums.
/-- Lemma 15.89.2: an `I`-power torsion `R`-module admits an infinite resolution whose terms are
direct sums of quotients `R ⧸ I^n` with the exponent `n` allowed to vary from summand to summand. -/
theorem exists_infinite_ideal_power_quotient_resolution
    (hM : Module.IsIdealPowerTorsion I M) :
    ∃ (F : ChainComplex (ModuleCat R) ℕ)
      (π : F ⟶ moduleSingle[R] M),
        QuasiIso π ∧ F.IsTermwiseDirectSumOfIdealPowerQuotients I := sorry

end

/-! ### Lemma_15_89_3 (from Chap15) -/
universe u v w

section

open scoped IdealPowerTorsion

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R}
variable {ι : Type w} [Finite ι]

/- Domain-style sampling:
- primary domain: commutative algebra of ideal-power torsion and away localizations;
- sampled owner declarations:
  `Ideal.powerTorsion`,
  `Module.IsIdealPowerTorsion`,
  `Submodule.torsionBySet`,
  `awayLocalizationFamilyMap`,
  `Submodule.torsionBySet_eq_torsionBySet_span`,
  `away_localization_family_map_injective_iff_torsionBySet_eq_bot`;
- best owner abstraction: the source-facing Chapter `15` finite-stage owner is
  `Ideal.powerTorsion`, whose core owner is `Submodule.torsionBySet`; the Chapter `10` owner
  `awayLocalizationFamilyMap` and the bridge
  `away_localization_family_map_injective_iff_torsionBySet_eq_bot`;
- primitive data: the ideal `I` together with a finite generating family `f` satisfying
  `Ideal.span (Set.range f) = I`;
- derived API: the vanishing conditions `M[I^1] = ⊥` and
  `∀ n : ℕ+, M[I^(n : ℕ)] = ⊥`, together with injectivity of
  `awayLocalizationFamilyMap M f`, packaged as a local `List.TFAE`.

Layer triage:
- `source-facing`: the three equivalent conditions in Stacks Lemma `15.89.3`;
- `core/canonical`: `Submodule.torsionBySet`;
- `bridge/view`: the Chapter `10` away-localization injectivity criteria.
-/

-- Proof sketch: when `I = Ideal.span (Set.range f)`, the chapter bridge
-- `away_localization_family_map_injective_iff_torsionBySet_eq_bot` together with
-- `Submodule.torsionBySet_eq_torsionBySet_span` identifies the base case
-- `I.powerTorsion M 1 = ⊥` with injectivity of the canonical map
-- `awayLocalizationFamilyMap M f`. For higher powers, if
-- `I^(n + 2)` kills `x`, then `I^(n + 1)` kills each `f i • x`; induction on `n` and injectivity
-- of the smul family map show `x = 0`.

/-- Bridge lemma: if `f` spans `I` and the canonical map to the away localizations `M_{f_i}` is
injective, then every positive-power torsion submodule `M[I^n]` vanishes. -/
theorem powerTorsionSubmodule_eq_bot_of_injective_awayLocalizationFamilyMap (f : ι → R)
    (hI : Ideal.span (Set.range f) = I)
    (hloc : Function.Injective (awayLocalizationFamilyMap M f)) (n : ℕ+) :
    M[I^(n : ℕ)] = ⊥ := by
  have hf_mem : ∀ i, f i ∈ I := fun i ↦ by
    simpa [hI] using (Ideal.subset_span (Set.mem_range_self i) : f i ∈ Ideal.span (Set.range f))
  let smulFamilyMap : M →ₗ[R] ∀ i, M := LinearMap.pi fun i ↦
    DistribSMul.toLinearMap R M (f i)
  have hsmul : Function.Injective smulFamilyMap := by
    simpa [smulFamilyMap] using
      (away_localization_family_map_injective_iff_smul_family_map_injective M f).mp hloc
  have hpow : ∀ m : ℕ, Submodule.torsionBySet R M ↑(I ^ (m + 1)) = ⊥ := by
    intro m
    induction m with
    | zero =>
        change Submodule.torsionBySet R M ↑(I ^ 1) = ⊥
        simpa [Submodule.torsionBySet_eq_torsionBySet_span, hI] using
          (away_localization_family_map_injective_iff_torsionBySet_eq_bot M f).mp hloc
    | succ m hm =>
        exact (Submodule.eq_bot_iff _).2 fun x hx ↦ by
          apply hsmul
          ext i
          have hfx : f i • x ∈ Submodule.torsionBySet R M ↑(I ^ (m + 1)) := by
            change x ∈ Submodule.torsionBySet R M ↑(I ^ (m + 2)) at hx
            change f i • x ∈ Submodule.torsionBySet R M ↑(I ^ (m + 1))
            rw [Submodule.mem_torsionBySet_iff] at hx ⊢
            intro a
            have hmul : f i * (a : R) ∈ I ^ (m + 2) := by
              simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
                (Ideal.mul_mem_mul a.2 (hf_mem i) : (a : R) * f i ∈ I ^ (m + 1) * I)
            simpa [smul_smul, mul_comm] using hx ⟨f i * a, hmul⟩
          simpa [hm] using hfx
  have hn : ((n : ℕ) - 1) + 1 = (n : ℕ) := Nat.sub_add_cancel (Nat.succ_le_of_lt n.2)
  simpa [hn] using hpow ((n : ℕ) - 1)

/-- Lemma 15.89.3: for a finitely generated ideal written as `I = Ideal.span (Set.range f)`, the
vanishing of `M[I^1]`, the vanishing of all higher power-torsion submodules `M[I^n]` for
`n ≥ 1`, and injectivity of the canonical localization-family map `awayLocalizationFamilyMap M f`
from `M` to the family of away localizations `M_{f_i}` are equivalent. -/
theorem ideal_power_torsion_bot_tfae_of_span_eq (f : ι → R)
    (hI : Ideal.span (Set.range f) = I) :
    List.TFAE [
      M[I^1] = ⊥,
      ∀ n : ℕ+, M[I^(n : ℕ)] = ⊥,
      Function.Injective (awayLocalizationFamilyMap M f)
    ] := by
  tfae_have 1 ↔ 3 := by
    simpa [Submodule.torsionBySet_eq_torsionBySet_span, hI] using
      (away_localization_family_map_injective_iff_torsionBySet_eq_bot M f).symm
  tfae_have 3 → 2 := by
    intro hloc n
    exact powerTorsionSubmodule_eq_bot_of_injective_awayLocalizationFamilyMap f hI hloc n
  tfae_have 2 → 1 := by
    intro h
    simpa using h 1
  tfae_finish

end

/-! ### Lemma_15_89_4 (from Chap15) -/
universe u v

section

open scoped IdealPowerTorsion

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I : Ideal R}

/-
Domain-style sampling pass for Lemma 15.89.4.

Primary domain: commutative algebra of ideal-power torsion modules and their extension closure.

Sampled same-domain owners:
* `Module.IsIdealPowerTorsion` and `Module.isIdealPowerTorsion_iff` from
  `Definition_15_89_1.lean`;
* the source-facing finite-stage owner notation `M[I^n]`, implemented by `Ideal.powerTorsion`;
* `Ideal.primaryComponent` as the canonical owner of `M[I^∞]`;
* the Chapter `15` finite-stage vanishing API from `Lemma_15_89_3.lean`.

Best owner abstraction:
* `source-facing`: the quotient by `M[I^∞]` has no residual `I`-torsion, and ideal-power torsion
  is closed under extensions;
* `core/canonical`: `Module.IsIdealPowerTorsion`, `Ideal.primaryComponent`, and `Ideal.powerTorsion`;
* `bridge/view`: the first clause is the finite-stage vanishing statement for the quotient module,
  written through the chapter owner notation `Q[I^1] = ⊥` rather than the raw
  `Submodule.torsionBySet` expansion.

Primitive data are only the ideal `I`, the module `M`, and in part `(2)` the chosen submodule
`N`. The quotient `M ⧸ M[I^∞]` and its stage-one power-torsion submodule are derived API.
-/

-- Proof sketch: choose finitely many generators of `I`. If the class of `m` in the quotient is
-- `I`-torsion, then each generator sends `m` into the `I`-primary component, hence into some
-- `I^n`-torsion submodule. A sufficiently large power of `I` therefore kills `m`, so its class in
-- the quotient is already zero.
/-- Lemma 15.89.4 (1): if `I` is finitely generated, then the quotient of `M` by its canonical
`I^∞`-torsion submodule `M[I^∞]` has no `I`-torsion. -/
theorem powerTorsion_quotient_primaryComponent_eq_bot
    (hI : I.FG) :
    (((M ⧸ (M[I^∞] : Submodule R M))[I^1]) :
      Submodule R (M ⧸ (M[I^∞] : Submodule R M))) = ⊥ := sorry

-- Proof sketch: let `m : M`. Since `M ⧸ N` is `I`-power torsion, some power of `I` kills the
-- image of `m` in the quotient, so a corresponding power sends `m` into `N`. Since `N` is
-- `I`-power torsion, a further power kills that element of `N`, and therefore a larger power of
-- `I` kills `m`.
/-- Lemma 15.89.4 (2): a module is `I`-power torsion whenever a submodule and the corresponding
quotient are both `I`-power torsion. -/
theorem isIdealPowerTorsion_of_submodule_and_quotient (N : Submodule R M)
    (hN : Module.IsIdealPowerTorsion I N)
    (hQ : Module.IsIdealPowerTorsion I (M ⧸ N)) :
    Module.IsIdealPowerTorsion I M := sorry

end

/-! ### Lemma_15_89_5 (from Chap15) -/
open CategoryTheory
open LinearMap

universe u

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

/- 
Domain-style sampling for Lemma 15.89.5:
- primary domain: object properties on the abelian category `ModuleCat R`, with LinearRepresentations_Serre_1977-class
  structure expressed by the owner interface `ObjectProperty.IsSerreClass`;
- inspected same-domain declarations:
  `Module.IsIdealPowerTorsion`,
  `ObjectProperty`,
  `ObjectProperty.IsSerreClass`,
  `isNoetherianObject_isSerreClass`;
- best owner abstraction: the object property on `ModuleCat R` induced directly from the
  source-facing predicate `Module.IsIdealPowerTorsion`;
- primitive data: only the module-level torsion predicate `Module.IsIdealPowerTorsion I M`;
- derived API: the direct `ObjectProperty` view of that predicate on `ModuleCat R` and its
  LinearRepresentations_Serre_1977-class instance.

Source/core/bridge triage:
- `source-facing`: the textbook class of `I`-power torsion modules;
- `core/canonical`: the predicate `Module.IsIdealPowerTorsion`;
- `bridge/view`: the direct `ObjectProperty` view on `ModuleCat R`.

The owner-level object property should therefore be only a thin bridge over
`Module.IsIdealPowerTorsion`, not a second predicate encoded through `I.primaryComponent M = ⊤`.
-/
-- Proof sketch: submodules and quotients of an `I`-power torsion module are again `I`-power
-- torsion by checking the annihilation condition elementwise, and extensions are handled by the
-- corresponding module-theoretic lemma. These are exactly the data
-- needed for the LinearRepresentations_Serre_1977-class constructor on `ModuleCat R`.
/-- Lemma 15.89.5: the `I`-power torsion modules form a LinearRepresentations_Serre_1977 subcategory of the abelian
category `Mod_R`. -/
instance
    (I : Ideal R) :
    ObjectProperty.IsSerreClass (fun M : ModuleCat R ↦ Module.IsIdealPowerTorsion I M) where
  exists_zero := by
    refine ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, ?_⟩
    rw [Module.isIdealPowerTorsion_iff]
    intro x
    refine ⟨1, fun a ↦ ?_⟩
    simpa using (zero_smul R x)
  prop_of_mono f _ hY := by
    have hf : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 inferInstance
    rw [Module.isIdealPowerTorsion_iff] at hY ⊢
    intro x
    obtain ⟨n, hn⟩ := hY (f.hom x)
    refine ⟨n, fun a ↦ hf ?_⟩
    simpa using hn a
  prop_of_epi f _ hX := by
    have hf : Function.Surjective f.hom := (ModuleCat.epi_iff_surjective f).1 inferInstance
    rw [Module.isIdealPowerTorsion_iff] at hX ⊢
    intro y
    rcases hf y with ⟨x, rfl⟩
    obtain ⟨n, hn⟩ := hX x
    refine ⟨n, fun a ↦ ?_⟩
    simpa using congrArg f.hom (hn a)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have hf : Function.Injective S.f.hom := (ModuleCat.mono_iff_injective S.f).1 hS.mono_f
    have hg : Function.Surjective S.g.hom := (ModuleCat.epi_iff_surjective S.g).1 hS.epi_g
    have hRange : Module.IsIdealPowerTorsion I (range S.f.hom) :=
      (Module.isIdealPowerTorsion_iff_of_linearEquiv I (LinearEquiv.ofInjective S.f.hom hf)).1 h₁
    let g := S.g.hom
    have hQuotKer : Module.IsIdealPowerTorsion I (S.X₂ ⧸ ker g) :=
      (Module.isIdealPowerTorsion_iff_of_linearEquiv I
        (quotKerEquivOfSurjective g hg)).2 h₃
    have hQuot : Module.IsIdealPowerTorsion I (S.X₂ ⧸ range S.f.hom) := by
      exact (ShortComplex.Exact.moduleCat_range_eq_ker hS.exact).symm ▸ hQuotKer
    exact isIdealPowerTorsion_of_submodule_and_quotient
      (range S.f.hom) hRange hQuot

end

end CategoryTheory

/-! ### Lemma_15_89_6 (from Chap15) -/
universe u v

namespace Module

section

open PrimeSpectrum

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-
Domain-style sampling pass for Lemma 15.89.6.

Primary domain: commutative algebra of ideal-power torsion modules and support in `Spec R`.

Sampled owner declarations:
* `Module.IsIdealPowerTorsion` and `Module.isIdealPowerTorsion_iff` from
  `Definition_15_89_1.lean`;
* `Module.support` and `Module.support_subset_of_injective`;
* `Module.exists_pow_le_annihilator_iff_support_subset_zeroLocus` from
  `Lemma_10_62_4.lean`.

Best owner abstraction: the source-facing predicate `Module.IsIdealPowerTorsion I M` together with
the canonical support owner `Module.support R M`. The cyclic-submodule annihilator criterion is
derived API used only as the bridge from support containment to elementwise torsion.

Source/core/bridge triage:
* `source-facing`: the Stacks equivalence between `I`-power torsion and support contained in
  `V(I)`;
* `core/canonical`: `Module.IsIdealPowerTorsion` and `Module.support`;
* `bridge/view`: the finite cyclic-module support criterion
  `exists_pow_le_annihilator_iff_support_subset_zeroLocus`.
-/

-- Proof sketch: use `Module.isIdealPowerTorsion_iff` to unpack `I`-power torsion elementwise.
-- If `p ∈ support R M`, the owner theorem `Module.mem_support_iff_exists_annihilator` produces an
-- element whose cyclic submodule has annihilator contained in `p`; any `f ∈ I \ p` would then
-- give a contradiction, because some power of `f` kills that element. Conversely, if the support
-- is contained in `V(I)`, then each cyclic submodule `R ∙ x` has support in `V(I)`; applying the
-- finite-module support criterion from Lemma `10.62.4` to `R ∙ x` produces a power of `I`
-- contained in the annihilator of `R ∙ x`, hence killing `x`.
/-- Lemma 15.89.6: for a finitely generated ideal `I`, an `R`-module `M` is `I`-power torsion,
equivalently `M[I^∞] = ⊤`, if and only if its support is contained in `V(I)`. -/
theorem isIdealPowerTorsion_iff_support_subset_zeroLocus
    (I : Ideal R) (hI : I.FG) :
    IsIdealPowerTorsion I M ↔ support R M ⊆ zeroLocus I := by
  rw [isIdealPowerTorsion_iff]
  constructor
  · intro hM p hp
    rw [mem_zeroLocus]
    by_contra hpI
    obtain ⟨f, hfI, hfp⟩ := Set.not_subset.mp hpI
    obtain ⟨m, hm⟩ := mem_support_iff_exists_annihilator.mp hp
    obtain ⟨n, hn⟩ := hM m
    have hpow : (f ^ (n : ℕ)) • m = 0 :=
      hn ⟨f ^ (n : ℕ), Ideal.pow_mem_pow hfI _⟩
    have hfpow : f ^ (n : ℕ) ∈ p.asIdeal := hm <|
      (Submodule.mem_annihilator_span_singleton _ _).mpr hpow
    exact hfp (p.isPrime.mem_of_pow_mem _ hfpow)
  · intro hM x
    set N : Submodule R M := R ∙ x
    haveI : Module.Finite R N := by
      simpa [N] using
        (Module.Finite.of_fg (Submodule.fg_span_singleton x) : Module.Finite R (R ∙ x : Submodule R M))
    have hNSupport : support R N ⊆ zeroLocus I :=
      (support_subset_of_injective N.subtype N.subtype_injective).trans hM
    obtain ⟨n, hn⟩ :=
      (exists_pow_le_annihilator_iff_support_subset_zeroLocus I hI).mpr hNSupport
    refine ⟨⟨n + 1, Nat.succ_pos n⟩, fun a ↦ ?_⟩
    have ha : (a : R) ∈ annihilator R N :=
      hn <| Ideal.pow_le_pow_right (Nat.le_succ n) a.2
    simpa [N] using (Submodule.mem_annihilator_span_singleton x (a : R)).mp ha

end

end Module

/-! ### Lemma_15_89_7 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)
local notation "RmodI" =>
  ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I))

/- Domain-style sampling for derived tensor bounds with ideal-power torsion coefficients:
- primary domain: canonical t-structure bounds `DerivedCategory.IsLE 0` on derived tensor
  products in `D(R)`;
- same-domain declarations inspected:
  `DerivedCategory.IsLE`,
  `boundedDerivedHomologyFunctor`,
  `ModuleCat.single0Functor`,
  `DerivedCategory.isLE_iff`,
  `Module.IsIdealPowerTorsion`;
- best owner abstraction: the bound `(K ⊗[R]^L M).IsLE 0` in the canonical derived-category
  t-structure;
- primitive data: the bounded object `M`, the source-facing nonpositive bound `M.obj.IsLE 0`,
  and the torsion hypotheses on the genuinely possibly nonzero cohomology objects `H^i(M)` for
  `i ≤ 0`;
- derived API: vanishing of the positive cohomology objects of `M` is already supplied by
  `DerivedCategory.isLE_iff` / `DerivedCategory.isZero_of_isLE`, so torsion in positive degrees
  is redundant and should not remain primitive input.

Layer triage:
- `source-facing`: the tensor-vanishing statement for bounded complexes with ideal-power torsion
  cohomology;
- `core/canonical`: the owner predicate `DerivedCategory.IsLE 0` on the derived tensor product;
- `bridge/view`: `ModuleCat.single0Functor` for modules concentrated in degree `0` and
  `boundedDerivedHomologyFunctor` for the cohomology objects of `M`.

Within this file, the quotient clause `(1)` is derived API: after identifying `R ⧸ I^n` as an
`I`-power torsion module through `Module.isIdealPowerTorsion_quotient_pow`, it is a specialization
of the module clause `(2)` rather than a second primitive owner.
-/

-- Proof sketch: write an `I`-power torsion module `N` as the filtered colimit of its submodules
-- annihilated by powers of `I`, reduce to the case where some `I^n` kills `N`, and then apply
-- the quotient case `R ⧸ I^n` after passing to the square-zero extension `R ⧸ I^n ⊕ N` as in the
-- textbook proof.
/-- Lemma 15.89.7 (2): if `K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has no positive cohomology, then
`K ⊗_R^{\mathbf L} N[0]` has no positive cohomology for every `I`-power torsion `R`-module
`N`. -/
theorem derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj N).IsLE 0 := sorry

-- Proof sketch: this is the module case `(2)` specialized to the `I`-power torsion module
-- `R ⧸ I^n`, using `Module.isIdealPowerTorsion_quotient_pow`.
/-- Lemma 15.89.7 (1): if `K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has no positive cohomology, then
`K ⊗_R^{\mathbf L} (R ⧸ I^n)[0]` has no positive cohomology for every positive `n`. -/
theorem derivedTensorProduct_idealPowQuotient_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (n : ℕ+) :
    (K ⊗[R]^L ModuleCat.single0Functor.obj (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))).IsLE 0 := by
  simpa using
    derivedTensorProduct_idealPowerTorsionModule_isLE_zero_of_modIdeal
      I K hKI (ModuleCat.of R (R ⧸ I ^ (n : ℕ)))
      (Module.isIdealPowerTorsion_quotient_pow I (n : ℕ))

-- Proof sketch: use part `(2)` for each possibly nonzero cohomology object `H^i(M)` with `i ≤ 0`,
-- since `hMle` already forces `H^i(M) = 0` for `i > 0`; then induct on the number of nonzero
-- cohomology objects of the bounded complex `M` via the truncation distinguished triangles from
-- Remark `13.12.4`.
/-- Lemma 15.89.7 (3): if `M` is a bounded derived `R`-complex whose nonpositive cohomology
modules are `I`-power torsion and which has no positive cohomology, then
`K ⊗_R^{\mathbf L} M` has no positive cohomology whenever
`K ⊗_R^{\mathbf L} (R ⧸ I)[0]` has none. -/
theorem derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal
    (K : DMod)
    (hKI : (K ⊗[R]^L RmodI).IsLE 0)
    (M : DbMod)
    (hMtors : ∀ i ≤ 0, Module.IsIdealPowerTorsion I ((Hb i).obj M))
    (hMle : M.obj.IsLE 0) :
    (K ⊗[R]^L M.obj).IsLE 0 := sorry

end

end CategoryTheory

/-! ### Lemma_15_89_8 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R] (I : Ideal R)

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "DbMod" => boundedDerivedCategory (ModuleCat R)
local notation "Hb" => boundedDerivedHomologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)
local notation "RmodI" =>
  Functor.obj (ModuleCat.single0Functor : ModuleCat R ⥤ DMod) (ModuleCat.of R (R ⧸ I))

/- Domain-style sampling for Lemma 15.89.8:
- primary domain: derived tensor product in `D(R)` together with the canonical t-structure on the
  bounded derived category;
- sampled owner declarations:
  `Module.IsIdealPowerTorsion`,
  `CategoryTheory.derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal`,
  `DerivedCategory.IsLE`,
  `boundedDerivedHomologyFunctor`,
  `ModuleCat.single0Functor`,
  `CategoryTheory.Triangulated.TStructure.isZero`;
- best owner abstraction: the core vanishing input is the canonical t-structure bound
  `(K ⊗[R]^L M).IsLE 0`, obtained from Lemma `15.89.7` after shifting `K`;
- primitive data: the source-facing hypothesis that every cohomology module `H^i(M)` is
  `I`-power torsion and the zero-object hypothesis modulo `I`;
- derived API: the zero-object consequences for bounded complexes, single modules, and the
  quotients `R ⧸ I^n`, all routed through the chapter owner `ModuleCat.single0Functor`.

Source/core/bridge triage:
- `source-facing`: the three `IsZero` consequences in this file;
- `core/canonical`: `DerivedCategory.IsLE` / `IsGE` and the t-structure zero-object criterion;
- `bridge/view`: `ModuleCat.single0Functor`, shifting `K`, and the
  `Module.IsIdealPowerTorsion` hypotheses on the bounded-derived cohomology objects `((Hb i).obj M)`.

Accordingly, this file keeps the source-facing zero-object statements and depends directly on the
chapter owner theorem `derivedTensorProduct_boundedIdealPowerTorsion_isLE_zero_of_modIdeal`,
rather than reimporting only its lower-level ingredients. -/

variable (K : DMod) (hKI : IsZero (K ⊗[R]^L RmodI))

-- Proof sketch: apply Lemma `15.89.7 (3)` to every shift `K[i]`; since the hypothesis says
-- `K ⊗_R^L (R ⧸ I)[0]` is the zero object, the same holds for all shifts, so every cohomology
-- object of `K ⊗_R^L M` vanishes. Then use the standard criterion that an object of `D(R)` with
-- zero cohomology in every degree is itself zero.
/-- Lemma 15.89.8: if `K \otimes_R^{\mathbf L} (R ⧸ I)[0]` is zero in `D(R)`, then
`K \otimes_R^{\mathbf L} M` is zero for every bounded derived `R`-complex whose cohomology
modules are `I`-power torsion. -/
theorem derivedTensorProduct_isZero_of_boundedIdealPowerTorsion_of_modIdeal_isZero
    (M : DbMod)
    (hMtors : ∀ i : ℤ, Module.IsIdealPowerTorsion I ((Hb i).obj M)) :
    IsZero (K ⊗[R]^L M.obj) := sorry

-- Proof sketch: regard the `I`-power torsion module `N` as an object of `D^b(R)` concentrated in
-- degree `0`, observe that its only nonzero cohomology object is `N` itself, and apply the main
-- bounded-derived vanishing theorem.
/-- If `K \otimes_R^{\mathbf L} (R ⧸ I)[0]` is zero, then `K \otimes_R^{\mathbf L} N[0]` is zero
for every `I`-power torsion `R`-module `N`. -/
theorem derivedTensorProduct_isZero_of_idealPowerTorsionModule_of_modIdeal_isZero
    (N : ModuleCat R) (hN : Module.IsIdealPowerTorsion I N) :
    IsZero (K ⊗[R]^L (single₀).obj N) := sorry

-- Proof sketch: the quotient `R ⧸ I^n` is `I`-power torsion for every `n` by Lemma `15.89.2`,
-- so this is the previous module case specialized to `N = R ⧸ I^n`.
/-- If `K \otimes_R^{\mathbf L} (R ⧸ I)[0]` is zero, then
`K \otimes_R^{\mathbf L} (R ⧸ I^n)[0]` is zero for every `n`. -/
theorem derivedTensorProduct_isZero_of_modIdealPow_of_modIdeal_isZero
    (n : ℕ) :
    IsZero (K ⊗[R]^L (single₀).obj (ModuleCat.of R (R ⧸ I ^ n))) := sorry

end

end CategoryTheory

/-! ### Lemma_15_89_9 (from Chap15) -/
universe u v w

section

variable {R : Type u} [CommRing R]
variable {R' : Type w} [CommRing R'] [Algebra R R']
variable (I : Ideal R)

/- Domain-style sampling for the tensor base-change statement:
- primary domain: commutative algebra of ideal-power torsion modules under scalar extension and
  tensor products;
- sampled owners: `Module.IsIdealPowerTorsion`, `Ideal.quotientMap`, `TensorProduct.mk`;
- best owner abstraction: the canonical tensor-base-change unit `TensorProduct.mk R R' M 1 :
  M →ₗ[R] R' ⊗[R] M`; the symmetric map `M → M ⊗[R] R'` is only its tensor-symmetry view;
- primitive data: the ideal `I`, the algebra map `R → R'`, the module `M`, the torsion
  hypothesis, and the quotient-map bijectivity family;
- derived API: bijectivity of the base-change unit on `I`-power torsion modules.

Layer triage:
- `source-facing`: the tensor-base-change bijectivity statement below;
- `core/canonical`: `Ideal.quotientMap` and `TensorProduct.mk`;
- `bridge/view`: the tensor-symmetry reinterpretation `M → M ⊗[R] R'`.
-/

variable {M : Type v} [AddCommMonoid M] [Module R M]

-- Proof sketch: if `I ^ n` annihilates `M`, then `M` is naturally an `R ⧸ I ^ n`-module, so
-- base change along `R → R'` factors through `R ⧸ I ^ n → R' ⧸ I ^ n R'`, which is bijective by
-- hypothesis. For a general `I`-power torsion module, write `M` as the directed union of its
-- `I ^ n`-annihilated submodules and use that tensor products commute with direct limits.
/-- Lemma 15.89.9: if the canonical maps `R ⧸ I^n → R' ⧸ I^n R'` are isomorphisms for all positive
`n`, then for every `I`-power torsion `R`-module `M` the canonical base-change unit
`M → R' ⊗[R] M` is bijective. -/
theorem tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective
    (hM : Module.IsIdealPowerTorsion I M)
    (hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R R'))
        (algebraMap R R')
        Ideal.le_comap_map)) :
    Function.Bijective (TensorProduct.mk R R' M 1) := sorry

end

section

variable {R : Type u} [CommRing R]
variable (I : Ideal R)
variable {M : Type v} [AddCommMonoid M] [Module R M]

/- Domain-style sampling for the adic-completion quotient statement:
- primary domain: `I`-adic completion and quotient comparison for commutative rings;
- sampled owners: `Ideal.quotientMap`, `AdicCompletion.evalₐ`,
  `completionIdeal_pow_eq_ker_evalₐ`;
- best owner abstraction: the canonical completion-side map is
  `AdicCompletion.evalₐ I n : AdicCompletion I R →ₐ[R] R ⧸ I ^ n`; the quotient comparison below is
  its source-facing `Ideal.quotientMap` presentation, with the Chapter 10 bridge
  `completionIdeal_pow_eq_ker_evalₐ` identifying the kernel with the extended ideal
  `((I ^ n).map (algebraMap R (AdicCompletion I R)))`;
- primitive data: the ideal `I`, the ring `R`, the finite-generation hypothesis on `I`, and the
  exponent `n`, together with an `I`-power torsion `R`-module when specializing the tensor
  base-change theorem to completion;
- derived API: bijectivity of the induced quotient map to the completion quotient, and the
  completion-specialized tensor base-change statement for `I`-power torsion modules.

Layer triage:
- `source-facing`: the completion-specialized tensor base-change statement below;
- `core/canonical`: `AdicCompletion.evalₐ` and `completionIdeal_pow_eq_ker_evalₐ`;
- `bridge/view`: the quotient-comparison statement below, and its principal-ideal specialization
  `principalAdicCompletion_quotientMap_bijective` in Lemma `15.91.1`.
-/

-- Proof sketch: `AdicCompletion.evalₐ I n` is surjective, and
-- `completionIdeal_pow_eq_ker_evalₐ` identifies its kernel with the extended ideal
-- `(I^n) (AdicCompletion I R)`. The displayed `Ideal.quotientMap` is therefore the quotient-side
-- presentation of `evalₐ`.
/-- If `I` is finitely generated, then for every `n : ℕ` the canonical quotient map
`R ⧸ I^n → AdicCompletion I R ⧸ I^n AdicCompletion I R` is bijective. -/
theorem adicCompletion_quotientMap_bijective
    (hI : I.FG) (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        ((I ^ n).map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R))
        Ideal.le_comap_map) := sorry

-- Proof sketch: specialize the general tensor base-change bijectivity theorem to the algebra
-- map `R → AdicCompletion I R`, and supply its quotient-map hypothesis via
-- `adicCompletion_quotientMap_bijective`.
/-- Lemma 15.89.9: if `I` is finitely generated, then for every `I`-power torsion `R`-module `M`
the canonical base-change unit `M → AdicCompletion I R ⊗[R] M` is bijective. This is the direct
completion specialization of the main base-change statement. -/
theorem tensorAdicCompletion_bijective_of_isIdealPowerTorsion
    (hI : I.FG) (hM : Module.IsIdealPowerTorsion I M) :
    Function.Bijective (TensorProduct.mk R (AdicCompletion I R) M 1) := by
  let hquot : ∀ n : ℕ+, Function.Bijective
      (Ideal.quotientMap
        ((I ^ (n : ℕ)).map (algebraMap R (AdicCompletion I R)))
        (algebraMap R (AdicCompletion I R))
        Ideal.le_comap_map) :=
    fun n ↦ adicCompletion_quotientMap_bijective I hI n
  exact tensorBaseChange_bijective_of_isIdealPowerTorsion_of_quotientMapBijective I hM hquot

end
