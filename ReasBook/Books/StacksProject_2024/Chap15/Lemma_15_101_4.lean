import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import StacksProject_2024.Chap15.Lemma_15_101_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w x y

/- Domain-style sampling for Lemma 15.101.4:
- primary domain: `I`-power quotient towers, adic completion, and Mittag-Leffler inverse systems
  attached to `Hom_A(M, N / I^(n + 1) N)` and quotient-level isomorphisms;
- sampled owner declarations:
  `idealPowerModuleQuotient` from `Lemma_15_101_1`,
  `CategoryTheory.SequentialInverseSystem`,
  `CategoryTheory.Functor.IsMittagLeffler`,
  `AdicCompletion.transitionMap`;
- best owner abstraction: the quotient data live in sequential inverse systems, while the
  `Type`-valued Mittag-Leffler condition is already owned canonically by
  `CategoryTheory.Functor.IsMittagLeffler`, so a local `Type`-specific redefinition would be a
  duplicate wheel;
- primitive data: the modules `M`, `N`, the ideal `I`, and the canonical reduction/transition maps
  induced by `AdicCompletion.transitionMap`;
- derived API: the Hom tower, the quotient-isomorphism tower, the comparison maps on quotients, and
  the resulting Mittag-Leffler / inverse-limit statements.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma statements about the Hom tower, the isomorphism tower, and the
  completion comparisons;
- `core/canonical`: `idealPowerModuleQuotient`, `SequentialInverseSystem`, and
  `Functor.IsMittagLeffler`;
- `bridge/view`: the explicit quotient comparison maps and the stagewise reduction maps on
  isomorphisms. -/

section

variable {A : Type u} [CommRing A]
variable (I : Ideal A)

/-- The kernel of the transition `X / I^(n + 2) X → X / I^(n + 1) X`. -/
abbrev idealPowerModuleTransitionKer (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    Submodule A (idealPowerModuleQuotient I X (n + 1)) :=
  LinearMap.ker (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1)))

/-- The stage `Hom_A(M, N / I^(n + 1) N)`, which canonically models `Hom_A(M_n, N_n)`. -/
abbrev homIdealPowerStage
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) : Type (max v w) :=
  M →ₗ[A] idealPowerModuleQuotient I N n

/-- The transition map on the Hom tower induced by reduction modulo one lower power of `I`. -/
abbrev homIdealPowerStep
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    homIdealPowerStage I M N (n + 1) →ₗ[A] homIdealPowerStage I M N n :=
  LinearMap.compRight A (AdicCompletion.transitionMap I N (Nat.le_succ (n + 1)))

/-- The inverse system `(Hom_A(M_n, N_n))_n`, modeled as `(Hom_A(M, N / I^(n + 1) N))_n`. -/
abbrev homIdealPowerTower
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (ModuleCat A) :=
  @Functor.ofOpSequence (ModuleCat A) _
    (fun n ↦ ModuleCat.of A (homIdealPowerStage I M N n))
    (fun n ↦ ModuleCat.ofHom (homIdealPowerStep I M N n))

/-- The canonical map `Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)`. -/
abbrev homReductionLinearMap
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    (M →ₗ[A] N) →ₗ[A] homIdealPowerStage I M N n :=
  LinearMap.compRight A (Submodule.mkQ (I ^ (n + 1) • (⊤ : Submodule A N)))

-- Proof sketch: if `f` lies in `I^(n + 1) Hom_A(M, N)`, then every value of `f` lands in
-- `I^(n + 1) N`, so the composite `M → N → N / I^(n + 1) N` is zero.
/-- The canonical reduction `Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)` kills `I^(n + 1)`. -/
theorem idealPowerHomComparison_condition
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N)) ≤
      LinearMap.ker (homReductionLinearMap I M N n) := sorry

/-- The canonical comparison
`Hom_A(M, N) / I^(n + 1) Hom_A(M, N) → Hom_A(M, N / I^(n + 1) N)`. -/
abbrev homReductionComparison
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    idealPowerModuleQuotient I (M →ₗ[A] N) n →ₗ[A] homIdealPowerStage I M N n :=
  Submodule.liftQ
    (I ^ (n + 1) • (⊤ : Submodule A (M →ₗ[A] N)))
    (homReductionLinearMap I M N n)
    (idealPowerHomComparison_condition I M N n)

/-- The stage of `A`-linear isomorphisms `M_n ≃ N_n`. -/
abbrev moduleIsomorphismStage
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) : Type (max v w) :=
  idealPowerModuleQuotient I M n ≃ₗ[A] idealPowerModuleQuotient I N n

-- Proof sketch: every quotient map `X / I^(n + 2) X → X / I^(n + 1) X` is induced by the
-- universal quotient map, hence is surjective.
/-- The transition map on ideal-power quotients is surjective. -/
theorem idealPowerModuleTransition_surjective
    (X : Type x) [AddCommGroup X] [Module A X] (n : ℕ) :
    Function.Surjective (AdicCompletion.transitionMap I X (Nat.le_succ (n + 1))) := sorry

-- Proof sketch: an isomorphism `e : M_(n+1) ≃ N_(n+1)` carries the kernel of the reduction map on
-- `M_(n+1)` onto the corresponding kernel on `N_(n+1)` because the reduction maps commute with `e`
-- and `e.symm`.
/-- An isomorphism of the higher quotient stages identifies the kernels of the next transition
maps. -/
theorem idealPowerModuleTransitionKer_map_eq
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N]
    (n : ℕ) (e : moduleIsomorphismStage I M N (n + 1)) :
    (idealPowerModuleTransitionKer I M n).map (e : _ →ₗ[A] _) =
      idealPowerModuleTransitionKer I N n := sorry

/-- Reduction modulo one lower power of `I` sends an isomorphism `M_(n+1) ≃ N_(n+1)` to an
isomorphism `M_n ≃ N_n`. -/
abbrev moduleIsomorphismReduction
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] (n : ℕ) :
    moduleIsomorphismStage I M N (n + 1) → moduleIsomorphismStage I M N n :=
  fun e ↦
    ((AdicCompletion.transitionMap I M (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
        (idealPowerModuleTransition_surjective I M n)).symm.trans
      ((Submodule.Quotient.equiv
          (idealPowerModuleTransitionKer I M n)
          (idealPowerModuleTransitionKer I N n)
          e
          (idealPowerModuleTransitionKer_map_eq I M N n e)).trans
        ((AdicCompletion.transitionMap I N (Nat.le_succ (n + 1))).quotKerEquivOfSurjective
          (idealPowerModuleTransition_surjective I N n)))

/-- The inverse system `(Isom_A(M_n, N_n))_n` of `A`-linear isomorphisms between the quotient
modules. -/
abbrev moduleIsomorphismTower
    (M : Type v) [AddCommGroup M] [Module A M]
    (N : Type w) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (Type (max v w)) :=
  @Functor.ofOpSequence (Type (max v w)) _
    (fun n ↦ moduleIsomorphismStage I M N n)
    (fun n ↦ moduleIsomorphismReduction I M N n)

end

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (I : Ideal A)
variable {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
variable {N : Type w} [AddCommGroup N] [Module A N] [Module.Finite A N]

local notation "HomTower" => homIdealPowerTower I M N
local notation "IsoTower" => moduleIsomorphismTower I M N
local notation "HomComparison" => fun n ↦ homReductionComparison I M N n

-- Proof sketch: choose a finite presentation of `M`, rewrite `Hom_A(M_n, N_n)` as the middle
-- homology of the induced two-term quotient complex, and apply Lemma `15.101.1 (3)` to that
-- complex.
/-- Lemma 15.101.4 (1): for finite `A`-modules `M` and `N` over a Noetherian ring, the inverse
system `(\mathrm{Hom}_A(M_n, N_n))_n`, identified with
`(\mathrm{Hom}_A(M, N / I^(n + 1) N))_n`, is Mittag-Leffler. -/
theorem homIdealPowerTower_isMittagLeffler :
    SequentialInverseSystem.IsMittagLeffler HomTower := sorry

-- Proof sketch: apply the homomorphism case to both directions `M → N` and `N → M`, then use the
-- Nakayama argument from the Stacks proof to show that an inverse pair modulo a sufficiently low
-- stage lifts to a genuine inverse pair at every higher stage.
/-- Lemma 15.101.4 (2): the inverse system of `A`-linear isomorphisms
`(\operatorname{Isom}_A(M_n, N_n))_n` is Mittag-Leffler. -/
theorem moduleIsomorphismTower_isMittagLeffler :
    Functor.IsMittagLeffler IsoTower := sorry

-- Proof sketch: use the same finite presentation of `M` and the Artin-Rees comparison from Lemma
-- `15.101.1 (5)` for the resulting two-term complex to obtain one constant `c` that annihilates
-- the kernel and cokernel at every stage.
/-- Lemma 15.101.4 (3): there is a single constant `c > 0` such that for every `n`, the kernel
and cokernel of the canonical comparison map
`Hom_A(M, N) / I^(n + 1) Hom_A(M, N) → Hom_A(M_n, N_n)` are killed by `I^c`. -/
theorem exists_homReductionComparison_annihilated_kernel_cokernel :
    ∃ c : ℕ, 0 < c ∧
      (∀ n : ℕ,
        I ^ c • (⊤ : Submodule A (LinearMap.ker (HomComparison n))) = ⊥) ∧
      ∀ n : ℕ,
        I ^ c •
            (⊤ :
              Submodule A
                (homIdealPowerStage I M N n ⧸ LinearMap.range (HomComparison n))) =
          ⊥ := sorry

-- Proof sketch: the same Artin-Rees comparison identifies the Hom tower with the quotient tower
-- of `Hom_A(M, N)` as a pro-object, so Lemma `15.101.1 (2)` yields the inverse-limit comparison
-- with the `I`-adic completion of `Hom_A(M, N)`.
/-- Lemma 15.101.4 (4): the inverse limit of the system `(\mathrm{Hom}_A(M_n, N_n))_n`,
identified with `(\mathrm{Hom}_A(M, N / I^(n + 1) N))_n`, is canonically isomorphic to the
`I`-adic completion of `Hom_A(M, N)`. -/
theorem limit_homIdealPowerTower_iso_completedHom :
    IsIsomorphic
      (limit HomTower)
      (ModuleCat.of A (AdicCompletion I (M →ₗ[A] N))) := sorry

-- Proof sketch: combine the inverse-limit description of completions with the fact that finite
-- modules satisfy `M^ = \varprojlim M_n` and `N^ = \varprojlim N_n`, then identify compatible
-- systems of maps with `A^`-linear maps between the completed modules as in Lemma `10.97.4`.
/-- Lemma 15.101.4 (5): the `I`-adic completion of `Hom_A(M, N)` is canonically isomorphic, as an
`A^`-module, to `Hom_{A^}(M^, N^)`, where completion is taken with respect to `I`. -/
theorem completedHom_iso_completedLinearMap :
    IsIsomorphic
      (ModuleCat.of (AdicCompletion I A) (AdicCompletion I (M →ₗ[A] N)))
      (ModuleCat.of (AdicCompletion I A)
        ((AdicCompletion I M) →ₗ[AdicCompletion I A] (AdicCompletion I N))) := sorry

-- Proof sketch: an element of the inverse limit of the isomorphism tower is a compatible family
-- of stagewise inverses. Apply the previous Hom-limit comparison in both directions and use the
-- Nakayama argument from the Stacks proof to show that the two limiting maps are inverse.
/-- Lemma 15.101.4 (6): the inverse limit of the system `(\operatorname{Isom}_A(M_n, N_n))_n`
is canonically identified with the type of `A^`-linear isomorphisms `M^ ≃ N^`. -/
theorem limit_moduleIsomorphismTower_iso_completedLinearEquiv :
    IsIsomorphic
      (limit IsoTower)
      (AdicCompletion I M ≃ₗ[AdicCompletion I A] AdicCompletion I N) := sorry

end
