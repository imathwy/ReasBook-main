import Mathlib
import StacksProject_2024.stacks_project.Chap15.Lemma_15_98_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_75_2

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
