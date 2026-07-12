import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import StacksProject_2024.Chap15.PrincipalIdeal
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped DirectSum

universe u v w

section

variable {R : Type u} [CommRing R]

namespace LinearMap

variable {M : Type*} {N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- A linear map is principal-pure if multiplication by every principal ideal meets its range
exactly as in the Stacks Project hypothesis `fA = A ∩ fB`. -/
def IsPrincipalPure (f : M →ₗ[R] N) : Prop :=
  ∀ r : R,
    principalIdeal r • f.range = f.range ⊓ principalIdeal r • ⊤

end LinearMap

open LinearMap

/- Domain-style sampling:
- primary domain: short exact sequences of `R`-modules tested against cyclic quotient modules
  `R ⧸ (f)` and the resulting split-summand criterion;
- sampled owner declarations:
  `principalIdeal`,
  `CategoryTheory.ShortComplex.ShortExact`,
  `LinearMap.IsPrincipalPure`,
  `LinearMap.compRight`,
  `Module.Projective.iff_split`;
- best owner abstraction: this file is `source-facing`; the exact-sequence side should reuse the
  canonical short-complex owner `ShortComplex.ShortExact`. No upstream chapter/mathlib owner was
  found for the principal-purity condition `fA = A ∩ fB`, so the source-facing owner in this file
  should be the left map itself via `LinearMap.IsPrincipalPure`, with its range expression kept
  internal to that definition;
  the cyclic quotient side should use the chapter owner `principalIdeal`, and the surjectivity
  statement should remain on the canonical postcomposition map `LinearMap.compRight`; although
  `IsSplitMono` is the categorical owner of a split inclusion, this theorem quantifies modules in
  different universes, so the stable source-facing direct-summand witness remains the explicit
  split data `s.comp i = LinearMap.id`;
- primitive data vs. derived API:
  primitive data are the short complex `S`, the principal-purity property of the image submodule
  carried by the left map `S.f.hom`, and a split inclusion of `P` into a direct sum of principal
  quotients;
  derived API is the lifting-surjectivity criterion phrased through `LinearMap.compRight`.

Source/core/bridge triage:
- `source-facing`: the equivalence theorem below;
- `core/canonical`: `principalIdeal`, `ShortComplex.ShortExact`,
  `LinearMap.IsPrincipalPure`, `LinearMap.compRight`, `Module.Projective.iff_split`, and the
  range submodule `S.f.hom.range` appearing only inside the owner definition;
- `bridge/view`: the theorem below, which combines the exact short-complex owner with the
  map-level principal-purity owner in the source lifting criterion.
-/

-- Proof sketch: for the forward implication, reduce to a summand `R ⧸ (f)` and lift a map
-- `R ⧸ (f) → C` by choosing a preimage of `1` in `B` and correcting it using the hypothesis
-- `fA = A ∩ fB`. For the reverse implication, take the direct sum over all maps `R ⧸ (f) → P`,
-- map it onto `P`, and apply the assumed lifting property to the resulting short exact sequence;
-- the principal-purity condition on its kernel gives a splitting.
variable {P : Type v} [AddCommGroup P] [Module R P]

/-- Helper for Lemma 15.125.1: if `r • m = 0`, then the principal ideal `(r)` lies in the kernel
of the map sending `1` to `m`. -/
lemma principalIdeal_le_ker_toSpanSingleton
    {M : Type*} [AddCommGroup M] [Module R M] {r : R} {m : M} (hm : r • m = 0) :
    principalIdeal r ≤ LinearMap.ker (LinearMap.toSpanSingleton R M m) := by
  intro a ha
  rcases Ideal.mem_span_singleton'.mp (by simpa [principalIdeal] using ha) with ⟨c, rfl⟩
  change (c * r) • m = 0
  rw [mul_smul, hm, smul_zero]

/-- Helper for Lemma 15.125.1: the quotient `R ⧸ (r)` maps to any module element annihilated by
`r` by sending the class of `1` to that element. -/
abbrev principalQuotientLift
    {M : Type*} [AddCommGroup M] [Module R M] (r : R) (m : M) (hm : r • m = 0) :
    (R ⧸ principalIdeal r) →ₗ[R] M :=
  Submodule.liftQ (principalIdeal r) (LinearMap.toSpanSingleton R M m)
    (principalIdeal_le_ker_toSpanSingleton (R := R) hm)

/-- Helper for Lemma 15.125.1: the universal quotient lift evaluates the class of `a` as `a • m`.
-/
lemma principalQuotientLift_mk
    {M : Type*} [AddCommGroup M] [Module R M] {r : R} {m : M} (hm : r • m = 0) (a : R) :
    principalQuotientLift (R := R) r m hm (Ideal.Quotient.mk (principalIdeal r) a) = a • m := by
  -- Normalize the ideal quotient constructor to the submodule quotient constructor.
  rw [← Ideal.Quotient.mk_eq_mk (I := principalIdeal r) a]
  -- Now `Submodule.liftQ_apply` computes the lift on representatives.
  simpa [principalQuotientLift, LinearMap.toSpanSingleton_apply] using
    (Submodule.liftQ_apply (p := principalIdeal r) (f := LinearMap.toSpanSingleton R M m)
      (h := principalIdeal_le_ker_toSpanSingleton (R := R) hm) a)

/-- Helper for Lemma 15.125.1: every class in `R ⧸ (r)` is a scalar multiple of the class of
`1`. -/
lemma principalQuotient_mk_eq_smul_one (r a : R) :
    (Ideal.Quotient.mk (principalIdeal r) a : R ⧸ principalIdeal r) =
      a • Ideal.Quotient.mk (principalIdeal r) (1 : R) := by
  change Ideal.Quotient.mk (principalIdeal r) a =
    Ideal.Quotient.mk (principalIdeal r) (a * 1)
  simp

/-- Helper for Lemma 15.125.1: the class of `1` in `R ⧸ (r)` is annihilated by `r`. -/
lemma principalQuotient_smul_mk_one_eq_zero (r : R) :
    r • (Ideal.Quotient.mk (principalIdeal r) (1 : R) : R ⧸ principalIdeal r) = 0 := by
  change Ideal.Quotient.mk (principalIdeal r) (r * 1) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  simpa [principalIdeal] using Ideal.mem_span_singleton_self r

/-- Helper for Lemma 15.125.1: principal-purity lets us correct a preimage of an `r`-torsion
element to an `r`-torsion preimage. -/
lemma exists_preimage_smul_eq_zero_of_principalPure
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (hi : IsPrincipalPure S.f.hom) (r : R) {c : S.X₃} (hc : r • c = 0) :
    ∃ b : S.X₂, S.g.hom b = c ∧ r • b = 0 := by
  obtain ⟨b₀, hb₀⟩ := hS.moduleCat_surjective_g c
  -- Exactness places `r • b₀` in the image of the left map.
  have hrb₀_range : r • b₀ ∈ LinearMap.range S.f.hom := by
    have hrb₀_ker : r • b₀ ∈ LinearMap.ker S.g.hom := by
      change S.g.hom (r • b₀) = 0
      calc
        S.g.hom (r • b₀) = r • S.g.hom b₀ := by rw [LinearMap.map_smul]
        _ = r • c := by rw [hb₀]
        _ = 0 := hc
    simpa [hS.exact.moduleCat_range_eq_ker] using hrb₀_ker
  have hrb₀_inf :
      r • b₀ ∈ LinearMap.range S.f.hom ⊓ principalIdeal r • (⊤ : Submodule R S.X₂) := by
    rw [Submodule.mem_inf]
    constructor
    · exact hrb₀_range
    · rw [Submodule.ideal_span_singleton_smul]
      exact (Submodule.mem_smul_pointwise_iff_exists (r • b₀) r
        (⊤ : Submodule R S.X₂)).2 ⟨b₀, trivial, rfl⟩
  have hrb₀_smul_range : r • b₀ ∈ principalIdeal r • LinearMap.range S.f.hom := by
    rw [hi r]
    exact hrb₀_inf
  rw [Submodule.ideal_span_singleton_smul] at hrb₀_smul_range
  rcases (Submodule.mem_smul_pointwise_iff_exists (r • b₀) r
      (LinearMap.range S.f.hom)).1 hrb₀_smul_range with ⟨a, ha, hmul⟩
  rcases ha with ⟨x, rfl⟩
  refine ⟨b₀ - S.f.hom x, ?_, ?_⟩
  · -- The correction term lies in the kernel of `g`, so the lifted element still maps to `c`.
    calc
      S.g.hom (b₀ - S.f.hom x) = S.g.hom b₀ - S.g.hom (S.f.hom x) := by
        rw [LinearMap.map_sub]
      _ = c - 0 := by simp [hb₀, S.moduleCat_zero_apply]
      _ = c := sub_zero c
  · -- The correction was chosen so that its `r`-multiple matches `r • b₀`.
    calc
      r • (b₀ - S.f.hom x) = r • b₀ - r • S.f.hom x := by rw [smul_sub]
      _ = 0 := by simpa [hmul]

/-- Helper for Lemma 15.125.1: maps from a cyclic principal quotient lift across any
principal-pure short exact sequence. -/
lemma surjective_compRight_cyclic_quotient_of_principalPure_shortExact
    {S : ShortComplex (ModuleCat R)} (hS : S.ShortExact)
    (hi : IsPrincipalPure S.f.hom) (r : R) :
    Function.Surjective
      (LinearMap.compRight R S.g.hom :
        ((R ⧸ principalIdeal r) →ₗ[R] S.X₂) →ₗ[R] ((R ⧸ principalIdeal r) →ₗ[R] S.X₃)) := by
  intro φ
  let q₁ : R ⧸ principalIdeal r := Ideal.Quotient.mk (principalIdeal r) (1 : R)
  -- The image of the quotient generator is annihilated by `r`.
  have hq₁ : r • φ q₁ = 0 := by
    calc
      r • φ q₁ = φ (r • q₁) := by rw [← LinearMap.map_smul]
      _ = φ 0 := by rw [principalQuotient_smul_mk_one_eq_zero]
      _ = 0 := by rw [LinearMap.map_zero]
  obtain ⟨b, hb, hrb⟩ := exists_preimage_smul_eq_zero_of_principalPure hS hi r hq₁
  refine ⟨principalQuotientLift (R := R) r b hrb, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  -- Every quotient class is a scalar multiple of the class of `1`, so the lift is determined on
  -- the generator.
  calc
    ((LinearMap.compRight R S.g.hom) (principalQuotientLift (R := R) r b hrb))
        (Ideal.Quotient.mk (principalIdeal r) a)
        = S.g.hom (a • b) := by
            rw [LinearMap.compRight_apply, LinearMap.comp_apply, principalQuotientLift_mk]
    _ = a • S.g.hom b := by rw [LinearMap.map_smul]
    _ = a • φ q₁ := by rw [hb]
    _ = φ (a • q₁) := by rw [LinearMap.map_smul]
    _ = φ (Ideal.Quotient.mk (principalIdeal r) a) := by
          rw [principalQuotient_mk_eq_smul_one]

/-- Helper for Lemma 15.125.1: surjective postcomposition for cyclic principal quotients extends
componentwise to direct sums of such quotients. -/
lemma surjective_compRight_directSum_of_principal_quotients
    {ι : Type*} (r : ι → R) {S : ShortComplex (ModuleCat R)}
    (hS : S.ShortExact) (hi : IsPrincipalPure S.f.hom) :
    Function.Surjective
      (LinearMap.compRight R S.g.hom :
        ((⨁ j : ι, R ⧸ principalIdeal (r j)) →ₗ[R] S.X₂) →ₗ[R]
          ((⨁ j : ι, R ⧸ principalIdeal (r j)) →ₗ[R] S.X₃)) := by
  classical
  intro φ
  choose ψ hψ using fun j : ι ↦
    surjective_compRight_cyclic_quotient_of_principalPure_shortExact
      (R := R) hS hi (r j) (φ.comp (DirectSum.lof R ι (fun j ↦ R ⧸ principalIdeal (r j)) j))
  refine ⟨DirectSum.toModule R ι S.X₂ ψ, ?_⟩
  -- Equality of maps out of a direct sum reduces to equality on each summand.
  apply DirectSum.linearMap_ext R
  intro j
  apply LinearMap.ext
  intro x
  have hψj : S.g.hom.comp (ψ j) =
      φ.comp (DirectSum.lof R ι (fun j ↦ R ⧸ principalIdeal (r j)) j) := by
    simpa [LinearMap.compRight_apply] using hψ j
  change
    S.g.hom ((DirectSum.toModule R ι S.X₂ ψ)
      ((DirectSum.lof R ι (fun j ↦ R ⧸ principalIdeal (r j)) j) x)) =
      φ ((DirectSum.lof R ι (fun j ↦ R ⧸ principalIdeal (r j)) j) x)
  rw [DirectSum.toModule_lof]
  simpa using congrArg
    (fun f : (R ⧸ principalIdeal (r j)) →ₗ[R] S.X₃ => f x) hψj

/-- Helper for Lemma 15.125.1: the indexing type for the universal direct sum of principal
quotients attached to `P`. -/
abbrev universalPrincipalQuotientIndex :=
  Σ r : R, {p : P // r • p = 0}

/-- Helper for Lemma 15.125.1: classical decidable equality on the universal index type. -/
noncomputable instance universalPrincipalQuotientIndexDecidableEq :
    DecidableEq (universalPrincipalQuotientIndex (R := R) (P := P)) :=
  Classical.decEq _

/-- Helper for Lemma 15.125.1: the summand indexed by `(r, p)` evaluates the class of `1` to `p`.
-/
abbrev universalPrincipalQuotientComponent (t : universalPrincipalQuotientIndex (R := R) (P := P)) :
    (R ⧸ principalIdeal t.1) →ₗ[R] P :=
  principalQuotientLift (R := R) t.1 t.2.1 t.2.2

/-- Helper for Lemma 15.125.1: the universal evaluation map from the direct sum of principal
quotients indexed by annihilated elements onto `P`. -/
noncomputable abbrev universalPrincipalQuotientEvaluation :
    (⨁ t : universalPrincipalQuotientIndex (R := R) (P := P), R ⧸ principalIdeal t.1) →ₗ[R] P :=
  DirectSum.toModule R (universalPrincipalQuotientIndex (R := R) (P := P)) P
    (fun t ↦ universalPrincipalQuotientComponent (R := R) (P := P) t)

/-- Helper for Lemma 15.125.1: the universal evaluation map is surjective, using the summands
indexed by `(0, p)`. -/
lemma universal_principal_quotient_evaluation_surjective :
    Function.Surjective (universalPrincipalQuotientEvaluation (R := R) (P := P)) := by
  intro p
  let t : universalPrincipalQuotientIndex (R := R) (P := P) := ⟨0, ⟨p, by simp⟩⟩
  refine ⟨DirectSum.of (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦
      R ⧸ principalIdeal t.1) t (Ideal.Quotient.mk (principalIdeal t.1) (1 : R)), ?_⟩
  -- Rewrite the chosen direct-sum generator as a `lof` term and evaluate the selected summand.
  rw [← DirectSum.lof_eq_of R (universalPrincipalQuotientIndex (R := R) (P := P))
    (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦ R ⧸ principalIdeal t.1) t
    (Ideal.Quotient.mk (principalIdeal t.1) (1 : R))]
  rw [universalPrincipalQuotientEvaluation, DirectSum.toModule_lof, universalPrincipalQuotientComponent,
    principalQuotientLift_mk]
  simp [t]

/-- Helper for Lemma 15.125.1: the kernel of the universal evaluation map is principal-pure. -/
lemma ker_universal_principal_quotient_evaluation_isPrincipalPure :
    IsPrincipalPure
      (LinearMap.ker (universalPrincipalQuotientEvaluation (R := R) (P := P))).subtype := by
  let D :=
    (⨁ t : universalPrincipalQuotientIndex (R := R) (P := P), R ⧸ principalIdeal t.1)
  let π := universalPrincipalQuotientEvaluation (R := R) (P := P)
  let K : Submodule R D := LinearMap.ker π
  intro r
  -- Route correction: prove the submodule equality elementwise, with the correction vector built
  -- from the summand indexed by `(r, π y)`.
  rw [Submodule.range_subtype]
  ext x
  constructor
  · intro hx
    rw [Submodule.ideal_span_singleton_smul] at hx
    rcases (Submodule.mem_smul_pointwise_iff_exists x r K).1 hx with ⟨y, hy, rfl⟩
    rw [Submodule.mem_inf]
    constructor
    · exact K.smul_mem r hy
    · rw [Submodule.ideal_span_singleton_smul]
      exact (Submodule.mem_smul_pointwise_iff_exists (r • y) r
        (⊤ : Submodule R D)).2
        ⟨y, Submodule.mem_top, rfl⟩
  · intro hx
    rw [Submodule.mem_inf] at hx
    rw [Submodule.ideal_span_singleton_smul] at hx
    rcases (Submodule.mem_smul_pointwise_iff_exists x r (⊤ : Submodule R D)).1 hx.2 with
      ⟨y, -, hy⟩
    have hx_zero : π x = 0 := (LinearMap.mem_ker).1 hx.1
    -- The image of `y` is annihilated by `r`, so it determines the correction summand.
    have hπy_zero : r • π y = 0 := by
      calc
        r • π y = π (r • y) := by rw [← LinearMap.map_smul]
        _ = π x := by rw [hy]
        _ = 0 := hx_zero
    let t : universalPrincipalQuotientIndex (R := R) (P := P) := ⟨r, ⟨π y, hπy_zero⟩⟩
    let z :=
      y - DirectSum.of (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦
          R ⧸ principalIdeal t.1) t (Ideal.Quotient.mk (principalIdeal r) (1 : R))
    have hcorrection_eval :
        π (DirectSum.of (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦
            R ⧸ principalIdeal t.1) t (Ideal.Quotient.mk (principalIdeal r) (1 : R))) = π y := by
      -- Evaluating the correction vector recovers the chosen torsion element `π y`.
      rw [← DirectSum.lof_eq_of R (universalPrincipalQuotientIndex (R := R) (P := P))
        (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦ R ⧸ principalIdeal t.1) t
        (Ideal.Quotient.mk (principalIdeal r) (1 : R))]
      change universalPrincipalQuotientEvaluation (R := R) (P := P)
        ((DirectSum.lof R (universalPrincipalQuotientIndex (R := R) (P := P))
          (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦ R ⧸ principalIdeal t.1) t)
          (Ideal.Quotient.mk (principalIdeal r) (1 : R))) = π y
      rw [universalPrincipalQuotientEvaluation, DirectSum.toModule_lof,
        universalPrincipalQuotientComponent, principalQuotientLift_mk]
      simp [t]
    have hcorrection_torsion :
        r • DirectSum.of (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦
            R ⧸ principalIdeal t.1) t (Ideal.Quotient.mk (principalIdeal r) (1 : R)) = 0 := by
      -- The chosen summand is the class of `1` modulo `(r)`, hence killed by `r`.
      rw [← DirectSum.lof_eq_of R (universalPrincipalQuotientIndex (R := R) (P := P))
        (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦ R ⧸ principalIdeal t.1) t
        (Ideal.Quotient.mk (principalIdeal r) (1 : R))]
      rw [← LinearMap.map_smul]
      rw [principalQuotient_smul_mk_one_eq_zero, LinearMap.map_zero]
    have hz_mem : z ∈ K := by
      rw [LinearMap.mem_ker]
      -- The correction vector is chosen to have the same image as `y`, so the difference lies in
      -- the kernel.
      change π (y - DirectSum.of (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦
        R ⧸ principalIdeal t.1) t (Ideal.Quotient.mk (principalIdeal r) (1 : R))) = 0
      rw [LinearMap.map_sub, hcorrection_eval]
      simp
    rw [Submodule.ideal_span_singleton_smul]
    refine (Submodule.mem_smul_pointwise_iff_exists x r K).2 ⟨z, hz_mem, ?_⟩
    -- Multiplying the corrected element by `r` recovers `x`.
    change r • (y - DirectSum.of (fun t : universalPrincipalQuotientIndex (R := R) (P := P) ↦
      R ⧸ principalIdeal t.1) t (Ideal.Quotient.mk (principalIdeal r) (1 : R))) = x
    rw [smul_sub, hy, hcorrection_torsion, sub_zero]

/-- Lemma 15.125.1: an `R`-module `P` is a direct summand of a direct sum of modules of the form
`R ⧸ (f)` if and only if for every short exact sequence `0 → A → B → C → 0` of `R`-modules with
`fA = A ∩ fB` for all `f : R`, the induced map `Hom_R(P, B) → Hom_R(P, C)` is surjective. -/
@[stacks 0ASM]
theorem directSummand_iff_surjective_compRight_of_principalPure_shortExact :
    (∃ (ι : Type (max u v w)) (r : ι → R)
      (i : P →ₗ[R] (⨁ j : ι, R ⧸ principalIdeal (r j)))
      (s : (⨁ j : ι, R ⧸ principalIdeal (r j)) →ₗ[R] P),
      s.comp i = LinearMap.id) ↔
      ∀ ⦃S : ShortComplex (ModuleCat.{max u v} R)⦄
        (hS : S.ShortExact)
        (hi : IsPrincipalPure S.f.hom),
        Function.Surjective
          (LinearMap.compRight R S.g.hom : (P →ₗ[R] S.X₂) →ₗ[R] P →ₗ[R] S.X₃) := by
  constructor
  · rintro ⟨ι, r, i, s, hs⟩ S hS hi φ
    obtain ⟨ψ, hψ⟩ :=
      surjective_compRight_directSum_of_principal_quotients (R := R) r hS hi (φ.comp s)
    refine ⟨ψ.comp i, ?_⟩
    have hψ' : S.g.hom.comp ψ = φ.comp s := by
      simpa [LinearMap.compRight_apply] using hψ
    have hs_eval : ∀ p : P, s (i p) = p := by
      intro p
      simpa using congrArg (fun f : P →ₗ[R] P => f p) hs
    apply LinearMap.ext
    intro p
    -- Lift along the ambient direct sum and then descend through the retraction identity.
    calc
      ((LinearMap.compRight R S.g.hom) (ψ.comp i)) p = S.g.hom (ψ (i p)) := by
        simp [LinearMap.compRight_apply]
      _ = (φ.comp s) (i p) := by
        simpa using congrArg
          (fun f : (⨁ j : ι, R ⧸ principalIdeal (r j)) →ₗ[R] S.X₃ => f (i p)) hψ'
      _ = φ (s (i p)) := rfl
      _ = φ p := by rw [hs_eval p]
  · intro h
    classical
    let D :=
      (⨁ t : universalPrincipalQuotientIndex (R := R) (P := P), R ⧸ principalIdeal t.1)
    let P' := ULift.{max u v, v} P
    let up : P →ₗ[R] P' := (ULift.moduleEquiv : P' ≃ₗ[R] P).symm.toLinearMap
    let down : P' →ₗ[R] P := (ULift.moduleEquiv : P' ≃ₗ[R] P).toLinearMap
    let π : D →ₗ[R] P := universalPrincipalQuotientEvaluation (R := R) (P := P)
    let π' : D →ₗ[R] P' := up.comp π
    let K : Submodule R D := LinearMap.ker π
    let T : ShortComplex.{max u v, max u ((max u v) + 1)} (ModuleCat.{max u v} R) :=
      CategoryTheory.ShortComplex.moduleCatMk K.subtype π' <| by
        apply LinearMap.ext
        intro x
        change up (π x) = 0
        rw [x.property]
        rfl
    have hExact : Function.Exact K.subtype π' := by
      intro y
      constructor
      · intro hy
        have hy' : π y = 0 := by
          change up (π y) = 0 at hy
          simpa [up] using congrArg ULift.down hy
        exact ⟨⟨y, hy'⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        change up (π x) = 0
        rw [x.property]
        rfl
    have hInj : Function.Injective K.subtype := by
      intro x y hxy
      exact Subtype.ext hxy
    have hSurj : Function.Surjective π' := by
      intro p
      obtain ⟨d, hd⟩ := universal_principal_quotient_evaluation_surjective
        (R := R) (P := P) (down p)
      refine ⟨d, ?_⟩
      change up (π d) = p
      rw [hd]
      simp [up, down]
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T hExact hInj hSurj
    have hK : IsPrincipalPure T.f.hom := by
      have hK₀ : IsPrincipalPure K.subtype := by
        simpa [K] using
          ker_universal_principal_quotient_evaluation_isPrincipalPure (R := R) (P := P)
      simpa [T] using hK₀
    obtain ⟨i, hi⟩ := h (S := T) hT hK up
    have hi' : π'.comp i = up := by
      simpa [LinearMap.compRight_apply] using hi
    have hsection : π.comp i = LinearMap.id := by
      have hdown := congrArg (fun f : P →ₗ[R] P' => down.comp f) hi'
      simpa [π', up, down, LinearMap.comp_assoc] using hdown
    let κ := ULift.{max u v w, max u v} (universalPrincipalQuotientIndex (R := R) (P := P))
    let e :
        D ≃ₗ[R] (⨁ t : κ, R ⧸ principalIdeal t.down.1) :=
      DirectSum.lequivCongrLeft R
        ((Equiv.ulift : κ ≃ universalPrincipalQuotientIndex (R := R) (P := P)).symm)
    refine ⟨κ, fun t ↦ t.down.1, e.toLinearMap.comp i, π.comp e.symm.toLinearMap, ?_⟩
    -- Reindexing the direct sum does not change the retract identity.
    have heid : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact e.symm_apply_apply x
    calc
      (π.comp e.symm.toLinearMap).comp (e.toLinearMap.comp i)
          = π.comp ((e.symm.toLinearMap.comp e.toLinearMap).comp i) := by
              rw [LinearMap.comp_assoc, LinearMap.comp_assoc]
      _ = π.comp i := by
            rw [heid, LinearMap.id_comp]
      _ = LinearMap.id := hsection

end
