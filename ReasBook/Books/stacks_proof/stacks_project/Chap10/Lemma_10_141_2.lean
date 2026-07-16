import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_141_1
import stacks_proof.stacks_project.Chap10.Lemma_10_74_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w x y

namespace Algebra

open scoped TensorProduct

/-
Domain-style sampling:
- primary domain: local infinitesimal lifting criteria for smoothness at a prime;
- sampled owner declarations:
  `IsSmoothAt`,
  `smoothAtPrime_iff_isSmoothAt`,
  `Algebra.FormallySmooth.iff_comp_surjective`,
  `RingHom.IsSmallExtension`;
- best owner abstraction: the public mathematical owner is `IsSmoothAt R q.asIdeal`, while the
  TFAE clauses below are source-facing bridge conditions formulated in terms of local liftings.

Source/core/bridge triage:
- `source-facing`: the TFAE theorem matching Lemma `10.141.2`;
- `core/canonical`: `IsSmoothAt R q.asIdeal`, together with the canonical infinitesimal lifting
  owner `Algebra.FormallySmooth.iff_comp_surjective` after localization;
- `bridge/view`: the local lifting clauses for square-zero extensions and small extensions at the
  prime `q`.

Primitive data vs. derived API:
- primitive data: the local extension `B' → B`, its square-zero or small-extension hypothesis, and
  the local `R`-algebra map `f : S →ₐ[R] B` with closed point `q`;
- derived API: existence of a lift to `B'`, and in the third clause the induced residue-field map.
-/

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

open IsLocalRing

/-- The common derived payload in the local lifting clauses: a lift of `f` through `B' → B`. -/
private abbrev isSmoothAtLift
    (B' : Type w) [CommRing B'] {B : Type x} [CommRing B]
    [Algebra R B'] [Algebra R B] [Algebra B' B] [IsScalarTower R B' B]
    (f : S →ₐ[R] B) : Prop :=
  ∃ f' : S →ₐ[R] B', (IsScalarTower.toAlgHom R B' B).comp f' = f

/-- The closed-point compatibility condition in the local lifting clauses. -/
private abbrev isSmoothAtClosedPoint
    (q : PrimeSpectrum S) {B : Type x} [CommRing B] [Algebra R B] [IsLocalRing B]
    (f : S →ₐ[R] B) : Prop :=
  q.asIdeal = Ideal.comap f.toRingHom (IsLocalRing.maximalIdeal B)

/-- The residue-field hypothesis appearing in the final lifting clause. -/
private abbrev isSmoothAtResidueFieldMapBijective
    (q : PrimeSpectrum S) {B : Type x} [CommRing B] [Algebra R B] [IsLocalRing B]
    (f : S →ₐ[R] B)
    (hq : q.asIdeal = Ideal.comap f.toRingHom (IsLocalRing.maximalIdeal B)) : Prop :=
  Function.Bijective (Ideal.ResidueField.mapₐ q.asIdeal (IsLocalRing.maximalIdeal B) f hq)

private abbrev isSmoothAtClosedPointOfSmallExtension
    (q : PrimeSpectrum S) (B' : Type w) [CommRing B'] [Algebra R B']
    {B : Type x} [CommRing B] [Algebra R B] [Algebra B' B] [IsScalarTower R B' B]
    [RingHom.IsSmallExtension (algebraMap B' B)] (f : S →ₐ[R] B) : Prop :=
  letI : IsLocalRing B := RingHom.IsSmallExtension.isLocalRingTarget (φ := algebraMap B' B)
  isSmoothAtClosedPoint q f

private abbrev isSmoothAtResidueFieldMapBijectiveOfSmallExtension
    (q : PrimeSpectrum S) (B' : Type w) [CommRing B'] [Algebra R B']
    {B : Type x} [CommRing B] [Algebra R B] [Algebra B' B] [IsScalarTower R B' B]
    [RingHom.IsSmallExtension (algebraMap B' B)] (f : S →ₐ[R] B)
    (hq : isSmoothAtClosedPointOfSmallExtension q B' f) : Prop :=
  letI : IsLocalRing B := RingHom.IsSmallExtension.isLocalRingTarget (φ := algebraMap B' B)
  let hq' : isSmoothAtClosedPoint q f := by
    simpa [isSmoothAtClosedPointOfSmallExtension] using hq
  isSmoothAtResidueFieldMapBijective q f hq'

/-- The square-zero infinitesimal lifting condition for formal smoothness at the prime `q`. -/
abbrev isSmoothAt_squareZeroLiftingCondition (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∀ {B' : Type w} [CommRing B'] [Algebra R B'] [IsLocalRing B'] [IsLocalHom (algebraMap R B')]
    {B : Type x} [CommRing B] [Algebra R B] [IsLocalRing B] [Algebra B' B] [IsScalarTower R B' B]
    (_ : Function.Surjective (algebraMap B' B))
    (_ : RingHom.ker (algebraMap B' B) ^ 2 = ⊥) (f : S →ₐ[R] B)
    (_ : isSmoothAtClosedPoint q f),
      isSmoothAtLift B' f

/-- The small-extension lifting condition for formal smoothness at the prime `q`. -/
abbrev isSmoothAt_smallExtensionLiftingCondition (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (q : PrimeSpectrum S) : Prop :=
  ∀ {B' : Type w} [CommRing B'] [Algebra R B']
    {B : Type x} [CommRing B] [Algebra R B] [Algebra B' B] [IsScalarTower R B' B]
    [RingHom.IsSmallExtension (algebraMap B' B)] [IsLocalHom (algebraMap R B')]
    (f : S →ₐ[R] B)
    (_ : isSmoothAtClosedPointOfSmallExtension q B' f),
      isSmoothAtLift B' f

/-- The small-extension lifting condition at `q` with residue-field isomorphism on the target. -/
abbrev isSmoothAt_smallExtensionResidueFieldLiftingCondition
    (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  ∀ {B' : Type w} [CommRing B'] [Algebra R B']
    {B : Type x} [CommRing B] [Algebra R B] [Algebra B' B] [IsScalarTower R B' B]
    [RingHom.IsSmallExtension (algebraMap B' B)] [IsLocalHom (algebraMap R B')]
    (f : S →ₐ[R] B)
    (hq : isSmoothAtClosedPointOfSmallExtension q B' f)
    (_ : isSmoothAtResidueFieldMapBijectiveOfSmallExtension
      q B' f hq),
      isSmoothAtLift B' f

/-- Helper for Chap10 Lemma 10 141 2: a small extension has square-zero kernel. -/
private theorem smallExtension_ker_square_zero
    {B' : Type w} {B : Type x} [CommRing B'] [CommRing B]
    (π : B' →+* B) [hπ : RingHom.IsSmallExtension π] :
    RingHom.ker π ^ 2 = ⊥ := by
  -- Proof comment: the kernel has module length `1`, hence is simple; in a local ring the
  -- maximal ideal equals its annihilator, so the maximal ideal kills the kernel and the square
  -- of the kernel vanishes.
  have hsimple : IsSimpleModule B' (RingHom.ker π) := by
    exact (Module.length_eq_one_iff.mp hπ.ker_length)
  have hannEq : Module.annihilator B' (RingHom.ker π) = maximalIdeal B' := by
    let _ : IsSimpleModule B' (RingHom.ker π) := hsimple
    exact IsLocalRing.eq_maximalIdeal IsSimpleModule.annihilator_isMaximal
  have hker_le : RingHom.ker π ≤ maximalIdeal B' := by
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
  have hsqle : RingHom.ker π ^ 2 ≤ ⊥ := by
    rw [pow_two]
    calc
      RingHom.ker π * RingHom.ker π ≤ maximalIdeal B' * RingHom.ker π := by
        simpa [Ideal.mul_comm] using (mul_le_mul_left hker_le (RingHom.ker π))
      _ = Module.annihilator B' (RingHom.ker π) * RingHom.ker π := by
        rw [hannEq]
      _ = ⊥ := by
        simpa using (Submodule.annihilator_mul (RingHom.ker π))
  exact le_bot_iff.mp hsqle

/-- Helper for Chap10 Lemma 10 141 2: at a closed point over `q`, every element outside `q`
maps to a unit in the local target. -/
private theorem closedPoint_primeCompl_isUnit
    (q : PrimeSpectrum S) {B : Type x} [CommRing B] [Algebra R B] [IsLocalRing B]
    (f : S →ₐ[R] B) (hq : isSmoothAtClosedPoint q f) :
    ∀ y : q.asIdeal.primeCompl, IsUnit (f y.1) := by
  intro y
  -- Proof comment: a nonunit in a local ring lies in the maximal ideal, contradicting that
  -- `y` is in the prime complement after transporting the closed-point equality.
  by_contra hy
  exact y.2 <| by
    have hy' : y.1 ∈ Ideal.comap f.toRingHom (maximalIdeal B) := by
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hy
    simpa [hq] using hy'

/-- Helper for Chap10 Lemma 10 141 2: smoothness at `q` gives the square-zero local lifting
criterion by factoring the target map through the local ring `S_q`. -/
private theorem squareZeroLiftingCondition_of_isSmoothAt
    (q : PrimeSpectrum S)
    [IsSmoothAt R q.asIdeal] :
    isSmoothAt_squareZeroLiftingCondition.{u, v, w, x} R S q := by
  intro B' _ _ _ _ B _ _ _ _ _ hsurj hsq f hq
  -- Proof comment: the closed-point condition says every denominator away from `q` maps to a
  -- unit in the local target `B`, so `f` factors through `S_q`.
  have hunits : ∀ y : q.asIdeal.primeCompl, IsUnit (f y.1) :=
    closedPoint_primeCompl_isUnit (R := R) (S := S) q f hq
  let fq : Localization.AtPrime q.asIdeal →ₐ[R] B :=
    IsLocalization.liftAlgHom
      (M := q.asIdeal.primeCompl)
      (S := Localization.AtPrime q.asIdeal)
      (f := f)
      hunits
  have hfq : fq.comp (IsScalarTower.toAlgHom R S (Localization.AtPrime q.asIdeal)) = f := by
    -- Proof comment: the localization factor is characterized by agreeing with `f` on `S`.
    ext x
    simp [fq, IsLocalization.lift_eq]
  have hker_nil : IsNilpotent (RingHom.ker (algebraMap B' B)) := ⟨2, hsq⟩
  let fq' : Localization.AtPrime q.asIdeal →ₐ[R] B' :=
    Algebra.FormallySmooth.liftOfSurjective fq (IsScalarTower.toAlgHom R B' B) hsurj hker_nil
  -- Proof comment: formal smoothness of `S_q` lifts the factorization across the square-zero
  -- extension, and composing back with `S → S_q` gives the required lift of `f`.
  refine ⟨fq'.comp (IsScalarTower.toAlgHom R S (Localization.AtPrime q.asIdeal)), ?_⟩
  ext x
  change (IsScalarTower.toAlgHom R B' B)
      (fq' ((algebraMap S (Localization.AtPrime q.asIdeal)) x)) = f x
  calc
    (IsScalarTower.toAlgHom R B' B)
        (fq' ((algebraMap S (Localization.AtPrime q.asIdeal)) x))
        = fq ((algebraMap S (Localization.AtPrime q.asIdeal)) x) := by
            exact
              Algebra.FormallySmooth.liftOfSurjective_apply fq
                (IsScalarTower.toAlgHom R B' B) hsurj hker_nil
                ((algebraMap S (Localization.AtPrime q.asIdeal)) x)
    _ = f x := AlgHom.congr_fun hfq x

/-- Helper for Chap10 Lemma 10 141 2: the square-zero local lifting criterion immediately implies
the small-extension local lifting criterion because small extensions are surjective with square-zero
kernel. -/
private theorem smallExtensionLiftingCondition_of_squareZeroLiftingCondition
    (q : PrimeSpectrum S)
    (hsq : isSmoothAt_squareZeroLiftingCondition.{u, v, w, x} R S q) :
    isSmoothAt_smallExtensionLiftingCondition.{u, v, w, x} R S q := by
  intro B' _ _ B _ _ _ _ _ _ f hq
  let hsmall : RingHom.IsSmallExtension (algebraMap B' B) := inferInstance
  letI : IsLocalRing B := RingHom.IsSmallExtension.isLocalRingTarget (φ := algebraMap B' B)
  have hq' : isSmoothAtClosedPoint q f := by
    -- Proof comment: clause `(3)` packages the same closed-point condition as clause `(2)`.
    simpa [isSmoothAtClosedPointOfSmallExtension] using hq
  -- Proof comment: a small extension is a surjective square-zero extension, so clause `(2)`
  -- applies verbatim after forgetting the extra owner data.
  specialize hsq (B' := B') (B := B) hsmall.surjective
    (smallExtension_ker_square_zero (π := algebraMap B' B)) f hq'
  exact hsq

/-- Helper for Chap10 Lemma 10 141 2: clause `(4)` is just clause `(3)` with an extra
residue-field hypothesis, so the implication is immediate after forgetting that datum. -/
private theorem smallExtensionResidueFieldLiftingCondition_of_smallExtensionLiftingCondition
    (q : PrimeSpectrum S)
    (hsmall : isSmoothAt_smallExtensionLiftingCondition.{u, v, w, x} R S q) :
    isSmoothAt_smallExtensionResidueFieldLiftingCondition.{u, v, w, x} R S q := by
  intro B' _ _ B _ _ _ _ _ _ f hq _
  -- Proof comment: clause `(4)` only adds residue-field bijectivity to clause `(3)`, so we
  -- forget that extra datum and reuse the smaller lifting hypothesis directly.
  specialize hsmall (B' := B') (B := B) f hq
  exact hsmall

/-- Helper for Chap10 Lemma 10 141 2: a surjective polynomial presentation sends the complement
of the prime over `q` onto the complement of `q`, so the localized presentation is defined over
matching denominator submonoids. -/
private theorem localizedPresentation_primeCompl_map_eq
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π)
    (q : PrimeSpectrum S) :
    Submonoid.map π.toRingHom (PrimeSpectrum.comap π.toRingHom q).asIdeal.primeCompl =
      q.asIdeal.primeCompl := by
  -- Proof comment: one inclusion is contraction along `π`, and the converse uses surjectivity to
  -- lift a denominator of `S` back to the polynomial source.
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    rcases hπ y with ⟨x, rfl⟩
    exact ⟨x, hy, rfl⟩

/-- Helper for Chap10 Lemma 10 141 2: localizing a surjective polynomial presentation at `q`
identifies the kernel of the localized map with the localized kernel ideal of the original
presentation. -/
private theorem localizedPresentation_ker_localRingHom_eq
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π)
    (q : PrimeSpectrum S) :
    RingHom.ker
        (Localization.localRingHom
          (PrimeSpectrum.comap π.toRingHom q).asIdeal q.asIdeal π.toRingHom rfl) =
      Ideal.map
        (algebraMap (MvPolynomial (Fin n) R)
          (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal))
        (RingHom.ker π.toRingHom) := by
  -- Proof comment: after matching the prime-complement submonoids, `IsLocalization.ker_map`
  -- computes the localized kernel directly.
  simpa [Localization.localRingHom] using
    (IsLocalization.ker_map
      (S := Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
      (Q := Localization.AtPrime q.asIdeal)
      (g := π.toRingHom)
      (localizedPresentation_primeCompl_map_eq (π := π) hπ q))

/-- Helper for Chap10 Lemma 10 141 2: the localized polynomial presentation at `q` stays
surjective. -/
private theorem localizedPresentation_localRingHom_surjective
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π)
    (q : PrimeSpectrum S) :
    Function.Surjective
      (Localization.localRingHom
        (PrimeSpectrum.comap π.toRingHom q).asIdeal q.asIdeal π.toRingHom rfl) := by
  -- Proof comment: every fraction in `S_q` has a numerator and denominator lifted from the
  -- polynomial presentation, so it comes from the corresponding localized source fraction.
  intro y
  rcases IsLocalization.exists_mk'_eq q.asIdeal.primeCompl y with ⟨a, s, rfl⟩
  rcases hπ a with ⟨x, rfl⟩
  rcases hπ s with ⟨t, ht⟩
  let t' : (PrimeSpectrum.comap π.toRingHom q).asIdeal.primeCompl := ⟨t, by
    intro htmem
    exact s.2 (by
      change π.toRingHom t ∈ q.asIdeal at htmem
      simpa [ht] using htmem)⟩
  refine
    ⟨IsLocalization.mk'
      (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal) x t', ?_⟩
  rw [Localization.localRingHom_mk']
  have hs_eq :
      (⟨π.toRingHom t, by
        exact Localization.le_comap_primeCompl_iff.mpr
          (ge_of_eq
            (rfl :
              (PrimeSpectrum.comap π.toRingHom q).asIdeal = q.asIdeal.comap π.toRingHom))
            t'.2⟩ :
        q.asIdeal.primeCompl) = s := by
    exact Subtype.ext ht
  rw [hs_eq]
  rfl

/-- Helper for Chap10 Lemma 10 141 2: the kernel of the localized polynomial presentation at `q`
is still finitely generated. -/
private theorem localizedPresentation_localRingHom_kernel_fg
    [Algebra.FinitePresentation R S]
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π)
    (q : PrimeSpectrum S) :
    (RingHom.ker
        (Localization.localRingHom
          (PrimeSpectrum.comap π.toRingHom q).asIdeal q.asIdeal π.toRingHom rfl)).FG := by
  -- Proof comment: finite presentation gives finite generation of `ker π`, and localization maps
  -- finitely generated ideals to finitely generated ideals.
  have hker_fg : (RingHom.ker π.toRingHom).FG := by
    simpa using Algebra.FinitePresentation.ker_fG_of_surjective (f := π) hπ
  rw [localizedPresentation_ker_localRingHom_eq (π := π) hπ q]
  exact Ideal.FG.map hker_fg _

/-- Helper for Chap10 Lemma 10 141 2: the localized presentation map carries the expected
`R → P → A` scalar tower. -/
private theorem localizedPresentation_isScalarTower
    {n : ℕ} (π : MvPolynomial (Fin n) R →ₐ[R] S) (q : PrimeSpectrum S)
    [Algebra
      (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
      (Localization.AtPrime q.asIdeal)]
    (hAlg :
      ∀ x : Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal,
        algebraMap
          (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
          (Localization.AtPrime q.asIdeal) x =
        Localization.localRingHom
          (PrimeSpectrum.comap π.toRingHom q).asIdeal q.asIdeal π.toRingHom rfl x) :
    IsScalarTower R
      (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
      (Localization.AtPrime q.asIdeal) := by
  -- Proof comment: the localized map agrees with the original presentation on polynomial
  -- generators, so the two induced `R → A` algebra maps are pointwise equal.
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  calc
    (algebraMap R (Localization.AtPrime q.asIdeal)) r =
        algebraMap S (Localization.AtPrime q.asIdeal) (algebraMap R S r) := by
      rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal)]
    _ = algebraMap S (Localization.AtPrime q.asIdeal)
        (π ((algebraMap R (MvPolynomial (Fin n) R)) r)) := by
      exact congrArg (algebraMap S (Localization.AtPrime q.asIdeal)) (π.commutes r).symm
    _ =
        Localization.localRingHom (PrimeSpectrum.comap π.toRingHom q).asIdeal
          q.asIdeal π.toRingHom rfl
          (algebraMap (MvPolynomial (Fin n) R)
            (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
            ((algebraMap R (MvPolynomial (Fin n) R)) r)) := by
      exact
        (Localization.localRingHom_to_map (PrimeSpectrum.comap π.toRingHom q).asIdeal
          q.asIdeal π.toRingHom rfl ((algebraMap R (MvPolynomial (Fin n) R)) r)).symm
    _ =
        algebraMap
          (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
          (Localization.AtPrime q.asIdeal)
          (algebraMap (MvPolynomial (Fin n) R)
            (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
            ((algebraMap R (MvPolynomial (Fin n) R)) r)) := by
      rw [hAlg]
    _ =
        algebraMap
          (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)
          (Localization.AtPrime q.asIdeal)
          ((algebraMap R
            (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)) r) := by
      rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R)
        (Localization.AtPrime (PrimeSpectrum.comap π.toRingHom q).asIdeal)]

/-- Helper for Chap10 Lemma 10 141 2: a finitely generated presentation kernel has a finite
conormal module. -/
private theorem conormalCotangent_finite_of_fg_kernel
    {P : Type y} {A : Type v} [CommRing P] [CommRing A] [Algebra P A]
    (hφfg : (RingHom.ker (algebraMap P A)).FG) :
    Module.Finite P (RingHom.ker (algebraMap P A)).Cotangent := by
  -- Proof comment: the conormal module is a quotient of the finitely generated kernel ideal.
  have hKerFinite : Module.Finite P (RingHom.ker (algebraMap P A)) :=
    Module.Finite.of_fg hφfg
  exact
    Module.Finite.of_surjective
      (RingHom.ker (algebraMap P A)).toCotangent
      (Ideal.toCotangent_surjective _)

/-- Helper for Chap10 Lemma 10 141 2: a surjective presentation makes the tensor differential
term finite once the source differentials are finite. -/
private theorem tensorKaehlerDifferential_finite_of_surjective
    {P : Type y} {A : Type v} [CommRing P] [CommRing A] [Algebra R P] [Algebra P A]
    (hφsurj : Function.Surjective (algebraMap P A))
    [Module.Finite P Ω[P⁄R]] :
    Module.Finite P (TensorProduct P A Ω[P⁄R]) := by
  -- Proof comment: the quotient algebra is finite over `P`, and tensor products of finite
  -- `P`-modules are finite.
  have hAFinite : Module.Finite P A :=
    Module.Finite.of_surjective (Algebra.linearMap P A) hφsurj
  let _ : Module.Finite P A := hAFinite
  infer_instance

/-- Helper for Chap10 Lemma 10 141 2: in a local ring, the maximal ideal lies in the Jacobson
radical of the zero ideal, i.e. in `Ring.jacobson`. -/
private theorem maximalIdeal_le_ringJacobson_of_local
    {P : Type y} [CommRing P] [IsLocalRing P] :
    IsLocalRing.maximalIdeal P ≤ Ring.jacobson P := by
  -- Proof comment: this is the local-ring Jacobson API rewritten from ideal-relative notation
  -- to the ring-level Jacobson radical used by the split-retraction theorem.
  simpa [Ideal.jacobson_bot] using
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal P))

/-- Helper for Chap10 Lemma 10 141 2: the conormal map has split reductions modulo arbitrarily
large powers of the maximal ideal. -/
private abbrev splitModuloMaximalPowersFrequently
    {P : Type y} {A : Type v} [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    [IsLocalRing P]
    (f : (RingHom.ker (algebraMap P A)).Cotangent →ₗ[P] TensorProduct P A Ω[P⁄R]) : Prop :=
  ∀ n₀ : ℕ, ∃ n ≥ n₀,
    ∃ s : (TensorProduct P A Ω[P⁄R]) ⧸
          ((IsLocalRing.maximalIdeal P) ^ n •
            (⊤ : Submodule P (TensorProduct P A Ω[P⁄R]))) →ₗ[P]
        (RingHom.ker (algebraMap P A)).Cotangent ⧸
          ((IsLocalRing.maximalIdeal P) ^ n •
            (⊤ : Submodule P (RingHom.ker (algebraMap P A)).Cotangent)),
      s.comp (f.quotientMapByIdeal ((IsLocalRing.maximalIdeal P) ^ n)) = LinearMap.id

/-- Helper for Chap10 Lemma 10 141 2: cofinal split reductions modulo powers of the maximal ideal
give an actual retraction of the conormal map. -/
private theorem conormalMap_split_of_splitModuloMaximalPowersFrequently
    {P : Type y} {A : Type v} [CommRing P] [CommRing A]
    [Algebra R P] [Algebra R A] [Algebra P A] [IsScalarTower R P A]
    [IsLocalRing P] [IsNoetherianRing P]
    (hφsurj : Function.Surjective (algebraMap P A))
    (hφfg : (RingHom.ker (algebraMap P A)).FG)
    [Module.Finite P Ω[P⁄R]]
    (hsplit :
      splitModuloMaximalPowersFrequently
        (KaehlerDifferential.kerCotangentToTensor R P A)) :
    ∃ l : (TensorProduct P A Ω[P⁄R]) →ₗ[P]
        (RingHom.ker (algebraMap P A)).Cotangent,
      l ∘ₗ KaehlerDifferential.kerCotangentToTensor R P A = LinearMap.id := by
  -- Proof comment: package the finite-domain, finite-codomain, and Jacobson side conditions, then
  -- apply Lemma 10.74.1 to upgrade the cofinal reduced splittings to an honest retraction.
  have hNFinite : Module.Finite P (RingHom.ker (algebraMap P A)).Cotangent :=
    conormalCotangent_finite_of_fg_kernel hφfg
  have hMFinite : Module.Finite P (TensorProduct P A Ω[P⁄R]) :=
    tensorKaehlerDifferential_finite_of_surjective (R := R) hφsurj
  let _ : Module.Finite P (RingHom.ker (algebraMap P A)).Cotangent := hNFinite
  let _ : Module.Finite P (TensorProduct P A Ω[P⁄R]) := hMFinite
  exact
    exists_retraction_of_split_injective_mod_ideal_pow_frequently
      (I := IsLocalRing.maximalIdeal P)
      (hI := maximalIdeal_le_ringJacobson_of_local)
      (f := KaehlerDifferential.kerCotangentToTensor R P A)
      hsplit

/-- Helper for Chap10 Lemma 10 141 2: the converse `4 → 1` is the remaining source-faithful
Noetherian devissage step over Artinian quotient powers of the localized presentation. -/
private theorem isSmoothAt_of_smallExtensionResidueFieldLifting
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (h :
      isSmoothAt_smallExtensionResidueFieldLiftingCondition.{u, v, w, x} R S q) :
    IsSmoothAt R q.asIdeal := by
  -- Route correction: the source-faithful hard direction is still the quotient-power devissage
  -- through the localized polynomial presentation at `q`.
  let A := Localization.AtPrime q.asIdeal
  letI : Algebra.FinitePresentation R S :=
    (Algebra.FinitePresentation.of_finiteType (R := R) (A := S)).mp inferInstance
  obtain ⟨n, π, hπsurj, hπfg⟩ := Algebra.FinitePresentation.out (R := R) (A := S)
  let q' : PrimeSpectrum (MvPolynomial (Fin n) R) := PrimeSpectrum.comap π.toRingHom q
  let P := Localization.AtPrime q'.asIdeal
  let φq : P →+* A := Localization.localRingHom q'.asIdeal q.asIdeal π.toRingHom rfl
  letI : Algebra P A := φq.toAlgebra
  letI : IsScalarTower R P A := by
    -- Proof comment: the scalar-tower transport is isolated in the localized-presentation bridge.
    simpa [q', P, A, φq] using
      localizedPresentation_isScalarTower (R := R) (S := S) (π := π) q (hAlg := fun _ ↦ rfl)
  have hφqsurj : Function.Surjective φq := by
    -- Proof comment: the localized polynomial presentation is still surjective at the chosen
    -- prime, so it remains a valid owner presentation for the local ring `S_q`.
    simpa [q', P, A, φq] using
      localizedPresentation_localRingHom_surjective (π := π) hπsurj q
  have hφqfg : (RingHom.ker φq).FG := by
    -- Proof comment: finite presentation of `S` localizes to finite generation of the localized
    -- kernel ideal, which is the conormal-domain owner for the remaining devissage.
    simpa [q', P, A, φq] using
      localizedPresentation_localRingHom_kernel_fg (R := R) (S := S) (π := π) hπsurj q
  have hPFormallySmooth : Algebra.FormallySmooth R P := by
    -- Proof comment: the localized polynomial ring is formally smooth over `R`.
    infer_instance
  have hPOmegaFree : Module.Free P Ω[P⁄R] := by
    -- Proof comment: over the local ring `P`, finite projective differentials are free.
    letI : Algebra.FormallySmooth R P := hPFormallySmooth
    have hFinite : Module.Finite P Ω[P⁄R] := KaehlerDifferential.finite R P
    letI : Module.Finite P Ω[P⁄R] := hFinite
    letI : Module.Projective P Ω[P⁄R] :=
      Algebra.FormallySmooth.projective_kaehlerDifferential (R := R) (A := P)
    letI : Module.Flat P Ω[P⁄R] := Module.Flat.of_projective
    exact Module.free_of_flat_of_isLocalRing
  have hPOmegaFinite : Module.Finite P Ω[P⁄R] := by
    -- Proof comment: the same differential module is finitely generated, so the local Jacobian
    -- criterion applies to this presentation.
    infer_instance
  have hConormalSplit :
      ∃ l : (TensorProduct P A Ω[P⁄R]) →ₗ[P]
          (RingHom.ker (algebraMap P A)).Cotangent,
        l ∘ₗ KaehlerDifferential.kerCotangentToTensor R P A = LinearMap.id := by
    -- Proof comment: the remaining source frontier is to turn the Artinian quotient-power
    -- liftings supplied by clause `(4)` into cofinal split reductions of this conormal map.
    have hsplitModuloMaximalPowers :
        splitModuloMaximalPowersFrequently
          (KaehlerDifferential.kerCotangentToTensor R P A) := by
      -- TODO: prove this by the source devissage: construct sections of the finite local
      -- first-order thickenings from `h`, convert each section via the split conormal sequence,
      -- and use Artin-Rees to identify these with reductions of the localized conormal map.
      sorry
    -- Proof comment: Lemma 10.74.1 upgrades those cofinal reduced splittings to the actual
    -- retraction required by the formal-smoothness split-injection criterion.
    let _ : Module.Finite P Ω[P⁄R] := hPOmegaFinite
    exact
      conormalMap_split_of_splitModuloMaximalPowersFrequently
        (R := R) (P := P) (A := A) hφqsurj hφqfg hsplitModuloMaximalPowers
  have hAFormallySmooth : Algebra.FormallySmooth R A := by
    -- Proof comment: a retraction of the conormal map is exactly the split-injection criterion
    -- for formal smoothness of the quotient presentation `P → A`.
    letI : Algebra.FormallySmooth R P := hPFormallySmooth
    exact (Algebra.FormallySmooth.iff_split_injection (R := R) (P := P) hφqsurj).2
      hConormalSplit
  -- Proof comment: `IsSmoothAt R q.asIdeal` is exactly formal smoothness of the localization `A`.
  let _ := hπfg
  let _ := hφqsurj
  let _ := hφqfg
  let _ := hPOmegaFree
  let _ := hPOmegaFinite
  exact hAFormallySmooth

-- Proof sketch: use `smoothAtPrime_iff_isSmoothAt` to rewrite Stacks-style smoothness at `q` as
-- mathlib's local formal smoothness condition at `q`. Then combine Proposition `10.138.13` with
-- the infinitesimal lifting criterion for formally smooth localizations to obtain the square-zero
-- lifting clause, observe that it immediately implies the two Artinian small-extension clauses, and
-- prove the converse by reducing split-injectivity of the localized conormal map to liftings
-- against Artinian length-one kernel extensions exactly as in the Stacks argument.
/-- Lemma 10.141.2: for a Noetherian ring map `R → S` of finite type and a prime `q` of `S`, the
following are equivalent: the localization `S_q` is formally smooth over `R`, i.e.
`IsSmoothAt R q.asIdeal`; every square-zero surjection of local `R`-algebras `B' → B` admits a
lift of every local `R`-algebra map `S → B` with closed point corresponding to `q`; the same
lifting statement holds for local Artinian surjections `B' → B` whose kernel has module length
`1`; and it still holds for such length-one extensions when `S → B` induces an isomorphism on
residue fields at `q` and the maximal ideal of `B`. -/
@[stacks 02HT]
theorem isSmoothAt_tfae_squareZeroLifting_smallExtension_residueFieldIso
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    List.TFAE
      [ IsSmoothAt R q.asIdeal,
        isSmoothAt_squareZeroLiftingCondition.{u, v, w, x} R S q,
        isSmoothAt_smallExtensionLiftingCondition.{u, v, w, x} R S q,
        isSmoothAt_smallExtensionResidueFieldLiftingCondition.{u, v, w, x} R S q ] := by
  tfae_have 1 → 2 := by
    intro hsmooth
    letI : IsSmoothAt R q.asIdeal := hsmooth
    -- Proof comment: this is exactly the localization-based lifting lemma proved above.
    exact
      (squareZeroLiftingCondition_of_isSmoothAt (R := R) (S := S) (q := q) :
        isSmoothAt_squareZeroLiftingCondition.{u, v, w, x} R S q)
  tfae_have 2 → 3 := by
    intro hsq
    exact
      smallExtensionLiftingCondition_of_squareZeroLiftingCondition
        (R := R) (S := S) (q := q) hsq
  tfae_have 3 → 4 := by
    intro hsmall
    exact
      smallExtensionResidueFieldLiftingCondition_of_smallExtensionLiftingCondition
        (R := R) (S := S) (q := q) hsmall
  tfae_have 4 → 1 := by
    intro h
    exact isSmoothAt_of_smallExtensionResidueFieldLifting (R := R) (S := S) q h
  tfae_finish

end

end Algebra
