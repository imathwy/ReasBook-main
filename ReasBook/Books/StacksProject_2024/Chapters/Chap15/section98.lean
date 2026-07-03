import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_98_1 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open Opposite
open DerivedModuleTower

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {F : ℕᵒᵖ ⥤ CommRingCat.{u}}

section

local notation "DModA" => DerivedCategory (ModuleCat (inverseLimitRing F))

namespace DerivedModuleTower

/-- A stagewise property on a derived module tower either holds at every stage, or it holds at one
stage after which all transition kernels are nilpotent. -/
def StagewiseOrEventuallyNilpotent
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (P : ℕ → Prop) : Prop :=
  (∀ n : ℕ, P n) ∨
    ∃ n₀ : ℕ, P n₀ ∧
      ∀ n : ℕ, n₀ ≤ n → IsNilpotent (RingHom.ker (stageTransitionRingHom F n))

/-- Monotonicity of the stagewise/eventually-nilpotent hypothesis with respect to the stagewise
property. -/
theorem stagewiseOrEventuallyNilpotent_mono
    (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (P Q : ℕ → Prop) (hPQ : ∀ n : ℕ, P n → Q n)
    (hP : StagewiseOrEventuallyNilpotent F P) :
    StagewiseOrEventuallyNilpotent F Q := by
  rcases hP with hP | ⟨n₀, hPn₀, hnil⟩
  · exact Or.inl (fun n ↦ hPQ n (hP n))
  · exact Or.inr ⟨n₀, hPQ n₀ hPn₀, hnil⟩

/-- The canonical stagewise derived base-change comparison induced by the tower map
`T.stepMap n : K_{n + 1} ⟶ K_n` viewed over `A_{n + 1}`. -/
abbrev stageDerivedBaseChangeComparison
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F)) (n : ℕ) :
    stageDerivedBaseChange F T n ⟶ T.obj n :=
  ((derivedTensorWithAlgebraAdjunction).homEquiv (T.obj (n + 1)) (T.obj n)).symm (T.stepMap n)

/-- The derived-limit base-change comparison attached to a chosen stage comparison
`c : K ⟶ K_n|_A`. -/
abbrev inverseLimitBaseChangeComparison
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F))
    (K : DModA) (n : ℕ) (c : K ⟶ (stageRestrictionToLimitTower F T).obj (op n)) :
    inverseLimitBaseChange F K n ⟶ T.obj n :=
  ((derivedTensorWithAlgebraAdjunction).homEquiv K (T.obj n)).symm c

end DerivedModuleTower

/- Domain-style sampling for Lemma 15.98.1:
- primary domain: derived inverse limits for towers of derived module objects over a sequential
  inverse system of commutative rings, together with pseudo-coherence and derived base change;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `CategoryTheory.IsDerivedLimit`,
  `DerivedModuleTower.stageRestrictionToLimitTower`,
  `DerivedModuleTower.stageDerivedBaseChangeComparison`,
  `CategoryTheory.HasMilnorTriangle.WithMap`;
- best owner abstraction: the chapter bridge owner
  `DerivedModuleTower (stageRing F) (stageTransitionRingHom F)` together with its canonical
  fixed-base inverse system `DerivedModuleTower.stageRestrictionToLimitTower T`, the canonical
  stagewise adjoint comparison
  `DerivedModuleTower.stageDerivedBaseChangeComparison F T n`, and the canonical
  derived-category owners `K.IsPseudoCoherent`, `CategoryTheory.IsDerivedLimit`, and the
  chosen-Milnor-map bridge `CategoryTheory.HasMilnorTriangle.WithMap`;
- primitive vs. derived:
  primitive data are the tower `T`, the chosen derived limit `K` of the canonical fixed-base
  tower `stageRestrictionToLimitTower T`, and the stagewise pseudo-coherence / nilpotence
  hypotheses;
  derived API is the pseudo-coherence conclusion for `K` and the inverse-limit base-change
  comparison induced by a derived-limit stage map.

Source/core/bridge triage:
- `source-facing`: the pseudo-coherence and base-change conclusion for the chosen derived limit;
- `core/canonical`: `K.IsPseudoCoherent` and `CategoryTheory.IsDerivedLimit`;
- `bridge/view`: `stageRestrictionToLimitTower`, `stageDerivedBaseChangeComparison`, and
  `inverseLimitBaseChangeComparison`, together with `HasMilnorTriangle.WithMap`. -/

-- Proof sketch: represent the tower by bounded-above finite-free complexes compatible under
-- reduction along the surjective transition maps, form the termwise inverse limit complex over
-- `A = lim A_n`, and use the Milnor description of `R lim` together with stagewise derived
-- tensor compatibility to identify pseudo-coherence of the limit object.
/-
Lemma 15.98.1: let `A = \varprojlim_n A_n` be a sequential inverse limit of commutative
rings, let `T` encode the compatible system `K_n ∈ D(A_n)`, and let `K` be a chosen derived
limit of the canonical fixed-base tower `stageRestrictionToLimitTower T` in `D(A)`. Assume the
transition maps `A_{n + 1} → A_n` are surjective with locally nilpotent kernels, that either every
`K_n` is pseudo-coherent or some stage `K_{n₀}` is pseudo-coherent and all later kernels are
nilpotent, and that the canonical stagewise derived base-change comparisons
`K_{n + 1} \otimes_{A_{n + 1}}^{\mathbf L} A_n → K_n` induced by `T.stepMap` are isomorphisms.
Then `K` is pseudo-coherent over `A`.
-/
variable
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F))
    (K : DModA)
    (h_surj : ∀ n : ℕ, Function.Surjective (stageTransitionRingHom F n))
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (stageTransitionRingHom F n) ≤ nilradical (stageRing F (n + 1)))
    (hpc : StagewiseOrEventuallyNilpotent F (fun n ↦ (T.obj n).IsPseudoCoherent))
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))

theorem derivedLimit_isPseudoCoherent_of_stagewisePseudoCoherent_or_eventuallyNilpotent
    (hKlim : IsDerivedLimit (stageRestrictionToLimitTower F T) K) :
    K.IsPseudoCoherent := sorry

-- Proof sketch: apply Lemma `15.98.1` to the canonical fixed-base tower
-- `stageRestrictionToLimitTower T`; any chosen Milnor map
-- `ι : K ⟶ ∏ stageRestrictionToLimitTower(T)_n` then yields the stage comparison
-- `ι ≫ π_n : K ⟶ K_n|_A`, which transposes under the derived extension/restriction adjunction to
-- the canonical base-change morphism `K ⊗_A^{\mathbf L} A_n ⟶ K_n`.
/-- Under the hypotheses of Lemma 15.98.1, the `n`th component of any chosen Milnor product map
from the derived limit `K` to the fixed-base tower `stageRestrictionToLimitTower T` induces an
isomorphism on derived base change `K ⊗_A^{\mathbf L} A_n → K_n`. -/
theorem inverseLimitBaseChangeComparison_isIso_of_stagewisePseudoCoherent_or_eventuallyNilpotent
    [HasProduct (inverseSystemFamily (stageRestrictionToLimitTower F T))]
    {ι : K ⟶ ∏ᶜ inverseSystemFamily (stageRestrictionToLimitTower F T)} {n : ℕ}
    (hι : HasMilnorTriangle.WithMap (stageRestrictionToLimitTower F T) ι) :
    IsIso
      (inverseLimitBaseChangeComparison T K n
        (ι ≫ Pi.π (inverseSystemFamily (stageRestrictionToLimitTower F T)) n)) := sorry

end

end

/-! ### Lemma_15_98_2 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "F" => idealPowerQuotientRingSystem I

/- Domain-style sampling for Lemma 15.98.2:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, together with
  pseudo-coherence, derived base change, and derived completeness;
- sampled owner declarations:
  `IdealPowerQuotientDerivedTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChangeComparison`,
  `CategoryTheory.IsDerivedLimit`,
  `IsAdicComplete`,
  `derivedLimit_of_idealPowerQuotientTower_isDerivedComplete`,
  `DerivedCategory.IsPseudoCoherent`,
  `DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing specialized tower owner
  `IdealPowerQuotientDerivedTower I` from `Lemma_15_98_4`, together with its canonical fixed-base
  tower `stageRestrictionToBaseTower F A T` and stagewise base-change comparison
  `stageDerivedBaseChangeComparison T n`;
- primitive vs. derived:
  primitive data are the specialized tower `T : IdealPowerQuotientDerivedTower I`, the chosen
  derived-limit object `K : D(A)`, the source-essential adic-completeness hypothesis
  `IsAdicComplete I A`, and the textbook pseudo-coherence/base-change hypotheses on the stages;
  derived API is the pseudo-coherence and derived-completeness conclusion for `K`, together with
  the induced quotient-stage base-change identification.

Source/core/bridge triage:
- `source-facing`: the two theorem statements in this file;
- `core/canonical`: `K.IsPseudoCoherent`, `K.IsDerivedCompleteWithRespectTo I`, and
  `CategoryTheory.IsDerivedLimit`;
- `bridge/view`: `stageRestrictionToBaseTower F A`,
  `stageDerivedBaseChangeComparison`, and the quotient-stage base-change object
  `K ⊗[A]^L[A ⧸ I ^ (n + 1)]`, all reused directly from `Lemma_15_98_4` and
  `Lemma_15_98_5`. -/

-- Proof sketch: specialize Lemma `15.98.1` to the ideal-power quotient tower to obtain
-- pseudo-coherence of the chosen derived limit `K`, then combine it with the specialized
-- derived-completeness result from Lemma `15.98.5` for the same tower.
/-- Lemma 15.98.2: let `A` be a ring, let `I ⊆ A` be an ideal, and let `K` be a chosen derived
limit of the canonical fixed-base tower attached to a compatible tower
`T : IdealPowerQuotientDerivedTower I` of objects `K_n ∈ D(A / I^(n+1))` viewed over `A`.
Assume `A` is `I`-adically complete, the first stage `K_1` is pseudo-coherent, and the stagewise
derived reductions
`K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1) → K_n` induced by `T.stepMap` are
isomorphisms. Then `K` is pseudo-coherent and derived complete with respect to `I`. Here stage
`0` corresponds to the textbook object `K_1`. -/
theorem derivedLimit_of_idealPowerQuotientTower_isPseudoCoherent_and_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n)) :
    K.IsPseudoCoherent ∧ K.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: this is the base-change part of Lemma `15.98.1` specialized to the ideal-power
-- quotient tower `A / I^(n+1)`, whose transition maps are the canonical quotient morphisms.
/-- For the quotient tower of Lemma 15.98.2, if `A` is `I`-adically complete, then the derived
base change of the chosen limit object `K` to each quotient stage `A / I^(n+1)` recovers the
corresponding stage object `K_n`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_pseudoCoherent_derivedLimit
    (T : IdealPowerQuotientDerivedTower I) (K : DMod) (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPseudoCoherent)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))
    (n : ℕ) : IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := sorry

end

/-! ### Lemma_15_98_3 (from Chap15) -/
open CategoryTheory
open CommRingCat
open Opposite
open DerivedModuleTower

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u})

section

local notation "DModA" => DerivedCategory (ModuleCat (inverseLimitRing F))

/- Domain-style sampling for Lemma 15.98.3:
- primary domain: perfect derived objects over an inverse-limit ring, controlled by a compatible
  derived module tower over the stages `A_n`;
- sampled owner declarations:
  `DerivedCategory.IsPerfect`,
  `CategoryTheory.isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`,
  `DerivedModuleTower.StagewiseOrEventuallyNilpotent F`,
  `derivedLimit_isPseudoCoherent_of_stagewisePseudoCoherent_or_eventuallyNilpotent`;
- best owner abstraction: the tower-side stage hypothesis should be expressed through the
  owner-level predicate `DerivedModuleTower.StagewiseOrEventuallyNilpotent F`, specialized to the
  stage property `fun n ↦ (T.obj n).IsPerfect`, while the fixed-base tower, the stage
  base-change morphisms, and the pseudo-coherent derived-limit theorem are reused directly from
  `Lemma_15_98_1`;
- primitive vs. derived:
  primitive data are the derived tower `T`, the chosen derived limit `K`, the surjective
  locally-nilpotent transition maps, the stagewise perfectness hypothesis in the owner form above,
  and the stagewise base-change isomorphisms;
  derived API is the perfectness of `K`; the needed stagewise pseudo-coherence hypothesis is
  derived from perfectness via `Lemma_15_75_2`, while the inverse-limit base-change comparison
  remains owned upstream by `Lemma_15_98_1`.

Source/core/bridge triage:
- `source-facing`: the perfectness conclusion for the chosen derived limit;
- `core/canonical`: `DerivedCategory.IsPerfect`, `CategoryTheory.IsDerivedLimit`, and the tower
  owner `DerivedModuleTower.StagewiseOrEventuallyNilpotent F`;
- `bridge/view`: the passage from stagewise perfectness to stagewise pseudo-coherence via
  `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension`; the corresponding inverse-limit
  base-change isomorphism stays a direct reuse of the owner theorem from `Lemma_15_98_1`. -/

-- Proof sketch: Lemma `15.98.1` gives pseudo-coherence of the chosen derived limit `K` together
-- with the stagewise base-change comparison isomorphisms over `A_n`. To prove perfectness, apply
-- Lemma
-- `15.78.3` after reducing to residue fields of the inverse-limit ring `A`: the locally
-- nilpotent-kernel hypothesis places `ker(A → A₀)` in the Jacobson radical, so every residue
-- field of `A` factors through `A₀`; then the residue-field fibers of `K` identify with those of
-- `K₀`, and finite tor dimension for the relevant stage follows from Lemma `15.75.2`.
/- Lemma 15.98.3: let `A = \varprojlim_n A_n` be a sequential inverse limit of commutative
rings, let `T` model the compatible system `K_n ∈ D(A_n)`, and let `K` be a chosen derived limit
of the canonical fixed-base tower `stageRestrictionToLimitTower T` in `D(A)`. If the transition
maps `A_{n + 1} → A_n` are surjective with locally nilpotent kernels, if either every `K_n` is
perfect or some `K_{n₀}` is perfect and the kernels are nilpotent for all `n ≥ n₀`, and if the
canonical stagewise derived base-change comparisons
`K_{n + 1} \otimes_{A_{n + 1}}^{\mathbf L} A_n → K_n` induced by `T.stepMap` are isomorphisms,
then the derived limit `K` is perfect. -/
-- Proof sketch: combine pseudo-coherence and residue-field control from Lemma `15.98.1` with the
-- perfectness criterion of Lemma `15.78.3`, using the locally nilpotent transition kernels to
-- compare residue-field fibers of `K` with those of a perfect stage.
variable
    (T : DerivedModuleTower (stageRing F) (stageTransitionRingHom F))
    (K : DModA)

theorem derivedLimit_isPerfect_of_stagewisePerfect_or_eventuallyNilpotent
    (hKlim : CategoryTheory.IsDerivedLimit (stageRestrictionToLimitTower F T) K)
    (h_surj : ∀ n : ℕ, Function.Surjective (stageTransitionRingHom F n))
    (h_locnil :
      ∀ n : ℕ, RingHom.ker (stageTransitionRingHom F n) ≤ nilradical (stageRing F (n + 1)))
    (hperfect : StagewiseOrEventuallyNilpotent F (fun n ↦ (T.obj n).IsPerfect))
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n)) :
    K.IsPerfect := sorry

theorem stagewisePseudoCoherentOrEventuallyNilpotent_of_stagewisePerfect_or_eventuallyNilpotent
    (hperfect' : StagewiseOrEventuallyNilpotent F (fun n ↦ (T.obj n).IsPerfect)) :
    StagewiseOrEventuallyNilpotent F (fun n ↦ (T.obj n).IsPseudoCoherent) :=
  stagewiseOrEventuallyNilpotent_mono
    F
    (fun n ↦ (T.obj n).IsPerfect)
    (fun n ↦ (T.obj n).IsPseudoCoherent)
    (fun n h ↦
      (isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension (T.obj n)).1 h |>.1)
    hperfect'

end

end

/-! ### Lemma_15_98_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open DerivedModuleTower
open Opposite
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.98.4:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, with stagewise
  derived base change along the quotient transition maps;
- sampled owner declarations:
  `sequentialRingSystem`,
  `DerivedModuleTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChange`,
  `stageDerivedBaseChangeComparison`;
- best owner abstraction: the source-facing ideal-power quotient tower should be a specialization
  of the chapter bridge owner `DerivedModuleTower`, with the fixed-base restriction now owned by
  the generic bridge `stageRestrictionToBaseTower` specialized to the quotient maps
  `A → A / I^(n+1)`;
- primitive data: the quotient stages `A / I^(n+1)`, their transition maps, the quotient
  algebra maps `A → A / I^(n+1)`, realized through `Ideal.Quotient.factorPow`, and the
  specialized derived tower itself;
- derived API: the specialized tower owner `IdealPowerQuotientDerivedTower`, the canonical
  fixed-base tower `stageRestrictionToBaseTower F A`, and the theorem surface specialized from the
  upstream base-change owners `stageDerivedBaseChange` and
  `stageDerivedBaseChangeComparison`.

Source/core/bridge triage:
- `source-facing`: the specialized ideal-power quotient tower and the two theorem statements;
- `core/canonical`: `DerivedModuleTower` and the upstream stagewise base-change owners;
- `bridge/view`: the fixed-base restriction tower over `A`, owned by
  `stageRestrictionToBaseTower` and specialized to the quotient algebra maps
  `A → A / I^(n+1)`. -/

/-- The sequential inverse system of quotient rings `A / I^(n+1)`. -/
abbrev idealPowerQuotientRingSystem : ℕᵒᵖ ⥤ CommRingCat.{u} :=
  sequentialRingSystem (fun n ↦ A ⧸ I ^ (n + 1))
    (fun n ↦ Ideal.Quotient.factorPowSucc I (n + 1))

local notation "F" => idealPowerQuotientRingSystem I

/-- Each stage ring in the quotient system is naturally an `A`-algebra. -/
instance idealPowerQuotientStageRingAlgebra (n : ℕ) :
    Algebra A (stageRing F n) := by
  change Algebra A (A ⧸ I ^ (n + 1))
  exact RingHom.toAlgebra (Ideal.Quotient.mk (I ^ (n + 1)))

private theorem idealPowerQuotient_algebraMap_comp (n : ℕ) :
    algebraMap A (stageRing F n) =
      (stageTransitionRingHom F n).comp (algebraMap A (stageRing F (n + 1))) := by
  ext x
  change (algebraMap A (A ⧸ I ^ (n + 1))) x =
      ((stageTransitionRingHom F n).comp (algebraMap A (A ⧸ I ^ (n + 2)))) x
  have htransition : stageTransitionRingHom F n = Ideal.Quotient.factorPowSucc I (n + 1) := by
    simp [idealPowerQuotientRingSystem, sequentialRingSystem, stageTransitionRingHom]
  rw [htransition]
  rfl

/-- The stage transition in the quotient system is compatible with the ambient `A`-algebra
structure. -/
instance idealPowerQuotientStageRingIsScalarTower (n : ℕ) :
    IsScalarTower A (stageRing F (n + 1)) (stageRing F n) := by
  exact IsScalarTower.of_algebraMap_eq' (idealPowerQuotient_algebraMap_comp I n)

/-- A compatible tower of derived quotient stages `K_n ∈ D(A / I^(n+1))`, expressed through the
chapter owner `DerivedModuleTower` specialized to the ideal-power quotient system. -/
abbrev IdealPowerQuotientDerivedTower :=
  DerivedModuleTower (stageRing F) (stageTransitionRingHom F)

-- Proof sketch: specialize Lemma `15.98.3` to the tower `A / I^(n+1)`, whose transition maps are
-- the canonical quotient morphisms with nilpotent kernels. The perfectness of stage `0`
-- corresponds to the textbook hypothesis that `K_1` is perfect, and the stagewise derived
-- base-change hypothesis identifies the tower with its reductions. Once perfection is known,
-- Lemma `15.92.8` applied to the `I`-adically complete ring `A` yields derived completeness.
/-- Lemma 15.98.4: if `A` is `I`-adically complete, `K_1` is perfect, and a compatible tower of
objects `K_n ∈ D(A / I^(n+1))` has derived reductions
`K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1) ≅ K_n`, then any derived-limit object
`K ∈ D(A)` of the tower viewed over `A` is perfect and derived complete with respect to `I`.
Here stage `0` corresponds to the textbook object `K_1`. -/
theorem derivedLimit_of_idealPowerQuotientTower_isPerfect_and_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I)
    (K : DMod)
    (hA : IsAdicComplete I A)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPerfect)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n)) :
    K.IsPerfect ∧ K.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: this is the base-change part of Lemma `15.98.3` specialized to the tower of
-- quotients `A / I^(n+1)`, using the canonical quotient transition maps between the stages.
/-- For the quotient tower of Lemma `15.98.4`, the derived base change of the chosen limit object
`K` to each stage `A / I^(n+1)` recovers the stage object `K_n`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_derivedLimit
    (T : IdealPowerQuotientDerivedTower I)
    (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁ : (T.obj 0).IsPerfect)
    (hstageBaseChange : ∀ n : ℕ, IsIso (stageDerivedBaseChangeComparison T n))
    (n : ℕ) : IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := sorry

end

/-! ### Lemma_15_98_5 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open DerivedModuleTower
open scoped DerivedTensorWithAlgebra

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "F" => idealPowerQuotientRingSystem I

/- Domain-style sampling:
- primary domain: derived inverse limits of ideal-power quotient towers in `D(A)`, together with
  the chapter bridge owner for stagewise restriction/base change and the derived-completeness owner;
- sampled owner declarations:
  `IdealPowerQuotientDerivedTower`,
  `stageRestrictionToBaseTower`,
  `stageDerivedBaseChange`,
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing ideal-power quotient tower owner
  `IdealPowerQuotientDerivedTower I` from `Lemma_15_98_4`, with derived completeness coming from
  `Definition_15_92_4`;
- primitive data: the tower `T : IdealPowerQuotientDerivedTower I` and the chosen derived limit
  `K` of the canonical fixed-base inverse system `stageRestrictionToBaseTower F A T`;
- derived API: the canonical fixed-base tower owner
  `stageRestrictionToBaseTower` and the upstream stagewise base-change owner
  `stageDerivedBaseChange (idealPowerQuotientRingSystem I) T n`, and the predicate
  `K.IsDerivedCompleteWithRespectTo I`.

Source/core/bridge triage:
- `source-facing`: the two statements of Lemma `15.98.5`;
- `core/canonical`: `CategoryTheory.IsDerivedLimit` and
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- `bridge/view`: `stageRestrictionToBaseTower F A`,
  `stageDerivedBaseChange (idealPowerQuotientRingSystem I) T n`, and the quotient-stage
  base-change object `K ⊗[A]^L[A ⧸ I ^ (n + 1)]`, reused directly from
  `Lemma_15_98_4`. -/

-- Proof sketch: restrict the tower `K_n` from `D(A / I^(n+1))` to `D(A)`. On stage `n`, the
-- ideal power `I^(n+1)` acts trivially, so for every `f ∈ I` a sufficiently large power of `f`
-- kills the `n`th stage. Apply Lemma `15.92.14` to the resulting inverse system in `D(A)`.
/-- Lemma 15.98.5 (1): let `A` be a ring, let `I ⊆ A` be an ideal, and let `K` be a
chosen derived limit of a compatible tower `K_n ∈ D(A / I^(n+1))` viewed over `A`. Then `K` is
derived complete with respect to `I`. Here stage `0` corresponds to the textbook object `K_1`. -/
theorem derivedLimit_of_idealPowerQuotientTower_isDerivedComplete
    (T : IdealPowerQuotientDerivedTower I) (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    : K.IsDerivedCompleteWithRespectTo I := sorry

section

variable [IsNoetherianRing A]

-- Proof sketch: choose bounded-above flat representatives for the stages using the bounded-above
-- hypothesis on `K_1` and the nilpotent lifting statement of Lemma `15.76.3`, then represent the
-- derived limit by the termwise inverse limit complex. Tensoring this bounded-above flat complex
-- with `A / I^(n+1)` commutes with the inverse limit and stabilizes at stage `n`, giving the
-- desired identification with `K_n`.
/-- Lemma 15.98.5 (2): let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, and let `K` be a
chosen derived limit of a compatible tower `K_n ∈ D(A / I^(n+1))` whose stagewise derived
reductions `K_{n+1} \otimes_{A / I^(n+2)}^{\mathbf L} A / I^(n+1)` identify with `K_n`. If the
first stage `K_1` is bounded above, then the derived base change of `K` to each quotient
`A / I^(n+1)` recovers `K_n`. Here stage `0` corresponds to the textbook object `K_1`. -/
theorem idealPowerQuotientBaseChange_isomorphic_of_boundedAbove_derivedLimit
    (T : IdealPowerQuotientDerivedTower I) (K : DMod)
    (hKlim : IsDerivedLimit (stageRestrictionToBaseTower F A T) K)
    (hK₁_bounded : ∃ b : ℤ, (T.obj 0).IsLE b)
    (hstageBaseChange :
      ∀ n : ℕ,
        IsIsomorphic
          (T.obj (n + 1) ⊗[A ⧸ I ^ (n + 2)]^L[A ⧸ I ^ (n + 1)])
          (T.obj n)) :
    ∀ n : ℕ, IsIsomorphic (K ⊗[A]^L[(A ⧸ I ^ (n + 1))]) (T.obj n) := sorry

end

end

/-! ### Lemma_15_98_6_Koll_r_Kov_cs (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem

universe u v

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/- Domain-style sampling for Lemma 15.98.6:
- primary domain: Milnor short exact sequences for derived inverse limits, specialized to the
  ideal-power quotient-tensor tower computing derived completion;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `DerivedCategory.homologyCompletionComparison`,
  `DerivedCategory.homologyCompletionComparison_isIso`,
  `IsDerivedCompletionIdealPowerQuotientTensorComparison`;
- best owner abstraction: this numbered item is `source-facing`, but its primitive comparison data
  are still owned by the canonical Milnor short exact sequence and the derived-completion
  comparison morphism. Any chosen `ι` and `π` from the Milnor sequence are only `bridge/view`
  witnesses and should not remain in the public theorem surface;
- primitive vs. derived:
  primitive data are the ideal `I`, the derived object `K`, the degree `i`, the finite cohomology
  hypothesis, and the Mittag-Leffler hypothesis on the previous-degree tower;
  derived API is the resulting canonical object-level isomorphism between
  `(H^i(K))^∧` and `lim H^i(K_n)`, while the chosen Milnor comparison
  `H^i(K^∧) ⟶ lim H^i(K_n)` remains internal bridge data. -/

/-- The quotient module `M / I^(n + 1) M`. -/
abbrev idealPowerModuleQuotient (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]
    (n : ℕ) : Type v :=
  M ⧸ (I ^ (n + 1) • (⊤ : Submodule A M))

/-- The `n`th quotient stage `M / I^(n + 1) M` in the ideal-power inverse system of an
`A`-module. -/
abbrev idealPowerQuotientStage (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    ModuleCat A :=
  ModuleCat.of A (idealPowerModuleQuotient I M n)

/-- The transition morphism `M / I^(n + 2) M ⟶ M / I^(n + 1) M` in the ideal-power quotient
inverse system. -/
abbrev idealPowerQuotientStep (I : Ideal A) (M : ModuleCat A) (n : ℕ) :
    idealPowerQuotientStage I M (n + 1) ⟶
      idealPowerQuotientStage I M n :=
  ModuleCat.ofHom (AdicCompletion.transitionMap I M (Nat.le_succ (n + 1)))

/-- The sequential inverse system `(M / I^(n + 1) M)_n` attached to an `A`-module `M`. -/
abbrev idealPowerQuotientInverseSystem (I : Ideal A) (M : ModuleCat A) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  Functor.ofOpSequence (idealPowerQuotientStep I M)

/-- The inverse system
`(H^i((A / I^(n+1))[0] ⊗_A^{\mathbf L} K))_n`, which is canonically identified with the textbook
tower `(H^i(K ⊗_A^{\mathbf L} A / I^(n+1)))_n` over a commutative base ring. -/
abbrev idealPowerQuotientTensorHomologyInverseSystem
    (I : Ideal A) (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  (idealPowerQuotientTensorDerivedInverseSystem I K) ⋙ H i

private theorem toDerivedCompletion_isDerivedCompletionIdealPowerQuotientTensorComparison
    (I : Ideal A) (K : DMod) :
    IsDerivedCompletionIdealPowerQuotientTensorComparison I
      K
      (K^∧[I, I.fg_of_isNoetherianRing])
      (DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K) := by
  sorry

private theorem exists_homologyDerivedCompletionToLimit
    (I : Ideal A) (K : DMod) (i : ℤ) :
    ∃ (π :
        (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]) ⟶
          limit (idealPowerQuotientTensorHomologyInverseSystem I K i))
      (ι :
        firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)) ⟶
          (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  let c :
      K ⟶ K^∧[I, I.fg_of_isNoetherianRing] :=
    DerivedCategory.toDerivedCompletion I I.fg_of_isNoetherianRing K
  have hc :
      IsDerivedCompletionIdealPowerQuotientTensorComparison I
        K (K^∧[I, I.fg_of_isNoetherianRing]) c :=
    toDerivedCompletion_isDerivedCompletionIdealPowerQuotientTensorComparison I K
  rcases CategoryTheory.derivedLimit_cohomology_shortExact
      (idealPowerQuotientTensorDerivedInverseSystem I K)
      (K^∧[I, I.fg_of_isNoetherianRing]) hc.isDerivedLimit i with
    ⟨ι, π, h, hshort⟩
  refine ⟨π, ι, h, ?_⟩
  simpa [c, idealPowerQuotientTensorHomologyInverseSystem, sub_eq_add_neg] using hshort

/-- If `π : H^i(K^∧) ⟶ \varprojlim_n H^i(K_n)` appears in the Milnor short exact sequence for the
quotient-tensor tower and the previous-degree tower is Mittag-Leffler, then composing `π` with the
canonical comparison `(H^i(K))^∧ → H^i(K^∧)` from Lemma `15.95.4` yields an isomorphism. -/
private theorem homologyCompletionComparison_comp_isIso_of_shortExact
    (I : Ideal A) (K : DMod) (i : ℤ)
    (hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K))
    (ι :
      firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)) ⟶
        (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]))
    (π :
      (H i).obj (K^∧[I, I.fg_of_isNoetherianRing]) ⟶
        limit (idealPowerQuotientTensorHomologyInverseSystem I K i))
    (h : ι ≫ π = 0)
    (hshort : (ShortComplex.mk ι π h).ShortExact)
    (hML_prev : (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)).IsMittagLeffler) :
    IsIso (DerivedCategory.homologyCompletionComparison I K i hKfinite ≫ π) := by
  have hzero :
      IsZero (firstDerivedLimit (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1))) := by
    sorry
  haveI : IsIso π := (ShortComplex.ShortExact.isIso_g_iff hshort).2 hzero
  haveI : IsIso (DerivedCategory.homologyCompletionComparison I K i hKfinite) :=
    DerivedCategory.homologyCompletionComparison_isIso I K i hKfinite
  infer_instance

-- Proof sketch: Proposition `15.95.2` identifies derived completion with the derived inverse
-- limit of the ideal-power tensor tower. Lemma `15.95.4` identifies `H^i` of that derived
-- completion with the `I`-adic completion of `H^i(K)`, i.e. the inverse limit of the quotients
-- `H^i(K) / I^(n+1) H^i(K)`. Lemma `15.88.4` gives the Milnor short exact sequence for the right
-- derived inverse limit, whose left term is `R^1 lim H^{i-1}(K_n)`, and the Mittag-Leffler
-- hypothesis in degree `i - 1` kills that obstruction via Lemma `15.88.1`.
/-- Lemma 15.98.6 (Kollár-Kovács): let `I` be an ideal of the Noetherian ring `A`, let `K ∈ D(A)`,
and set `K_n = K ⊗_A^{\mathbf L} A / I^(n+1)`. If every `H^j(K)` is a finite `A`-module and the
inverse system `(H^{i - 1}(K_n))_n` satisfies the Mittag-Leffler condition, then there exists a
Milnor comparison from `(H^i(K))^∧` to `\varprojlim_n H^i(K_n)`, obtained by composing the
canonical map `(H^i(K))^∧ → H^i(K^∧)` with a Milnor comparison
`H^i(K^∧) → \varprojlim_n H^i(K_n)`. Since that Milnor comparison is chosen only through the
owner theorem `derivedLimit_cohomology_shortExact`, the public surface is the resulting canonical
object-level isomorphism between the completion of `H^i(K)` and the limit of the tower
`(H^i(K_n))_n`. The Lean indexing starts at `n = 0`, corresponding to the textbook power `I^1`. -/
theorem homology_idealPowerQuotient_limit_iso_tensorQuotient_homology_limit
    (I : Ideal A) (K : DMod) (i : ℤ)
    (hKfinite : ∀ j : ℤ, Module.Finite A ((H j).obj K))
    (hML_prev : (idealPowerQuotientTensorHomologyInverseSystem I K (i - 1)).IsMittagLeffler) :
    IsIsomorphic
      (ModuleCat.of A (AdicCompletion I ((H i).obj K)))
      (limit (idealPowerQuotientTensorHomologyInverseSystem I K i)) := by
  rcases exists_homologyDerivedCompletionToLimit I K i with ⟨π, ι, h, hshort⟩
  let φ :
      ModuleCat.of A (AdicCompletion I ((H i).obj K)) ⟶
        limit (idealPowerQuotientTensorHomologyInverseSystem I K i) :=
    DerivedCategory.homologyCompletionComparison I K i hKfinite ≫ π
  have hφ : IsIso φ := by
    simpa [φ] using
      homologyCompletionComparison_comp_isIso_of_shortExact
        I K i hKfinite ι π h hshort hML_prev
  let _ := hφ
  exact ⟨asIso φ⟩

end
