import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_141_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w x

namespace Algebra

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
theorem isSmoothAt_tfae_squareZeroLifting_smallExtension_residueFieldIso
    [IsNoetherianRing R] [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    List.TFAE
      [ IsSmoothAt R q.asIdeal,
        isSmoothAt_squareZeroLiftingCondition R S q,
        isSmoothAt_smallExtensionLiftingCondition R S q,
        isSmoothAt_smallExtensionResidueFieldLiftingCondition R S q ] := sorry

end

end Algebra
