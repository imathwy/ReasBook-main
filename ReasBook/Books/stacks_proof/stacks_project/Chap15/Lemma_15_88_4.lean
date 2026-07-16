import Mathlib
import stacks_proof.stacks_project.Chap15.Lemma_15_87_10
import stacks_proof.stacks_project.Chap15.Lemma_15_88_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open SequentialInverseSystem

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

local notation "SeqMod" => SequentialInverseSystem (ModuleCat A)
local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "DSeq" => DerivedCategory SeqMod
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/-- Helper for Lemma 15.88.4: the fixed-base derived inverse-limit functor with explicit
universe parameters. -/
private abbrev fixedBaseDerivedInverseLimitFunctor : DSeq ⥤ DMod :=
  additiveFunctorTotalRightDerived.{u + 1, u + 1, u + 1, u, u}
    (lim : SeqMod ⥤ ModuleCat A)

/-
Domain-style sampling for Lemma 15.88.4:
- primary domain: Milnor short exact sequences for derived inverse limits in
  `DerivedCategory (ModuleCat A)`;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `CategoryTheory.IsDerivedLimit`,
  `stagewiseModuleDerivedLimitTower`,
  `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation`;
- best owner abstraction: the Milnor short exact sequence itself is already owned by the canonical
  Chapter 15 theorem `CategoryTheory.derivedLimit_cohomology_shortExact`; this file only supplies
  the fixed-base stagewise bridge from Lemma `15.88.3`;
- primitive data: only `K : D(\mathbf N^\mathrm{op} \to \mathrm{Mod}_A)` and the stagewise tower
  `stagewiseModuleDerivedLimitTower K`;
- derived API: the chosen derived-limit witness
  `moduleDerivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation A K` and the resulting short
  exact sequence on cohomology, whose left term is
  `SequentialInverseSystem.firstDerivedLimit
    ((stagewiseModuleDerivedLimitTower K) ⋙ H (p - 1))`.

Source/core/bridge triage:
- `source-facing`: the fixed-base module specialization of the Milnor short exact sequence;
- `core/canonical`: `CategoryTheory.derivedLimit_cohomology_shortExact`;
- `bridge/view`: `stagewiseModuleDerivedLimitTower K` together with the derived-limit witness from
  Lemma `15.88.3`.
-/

-- Proof sketch: apply the canonical Milnor short exact sequence owner
-- `CategoryTheory.derivedLimit_cohomology_shortExact` to the stagewise tower from Lemma `15.88.3`.
/-- Lemma 15.88.4: with notation as in Lemma `15.88.3`, the long exact cohomology sequence of the
distinguished triangle for `R \!\varprojlim(K)` breaks into a short exact sequence
`0 \to R^1 \!\varprojlim_n H^{p-1}(K_n^\bullet) \to H^p(R \!\varprojlim(K)) \to
\varprojlim_n H^p(K_n^\bullet) \to 0` of `A`-modules. Here the left term is modeled by the
canonical owner
`SequentialInverseSystem.firstDerivedLimit
  ((stagewiseModuleDerivedLimitTower K) ⋙ H (p - 1))`. -/
@[stacks 0CQE]
theorem moduleDerivedInverseLimit_cohomology_shortExact
    (K : DSeq) (p : ℤ) :
    ∃ (ι :
        SequentialInverseSystem.firstDerivedLimit
          ((stagewiseModuleDerivedLimitTower K) ⋙ H (p - 1)) ⟶
          R^p lim(K))
      (π :
        R^p lim(K) ⟶
          limit ((stagewiseModuleDerivedLimitTower K) ⋙ H p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := by
  have hKlim :
      IsDerivedLimit
        (stagewiseModuleDerivedLimitTower K)
        ((fixedBaseDerivedInverseLimitFunctor (A := A)).obj K) := by
    simpa [stagewiseModuleDerivedLimitTower, fixedBaseDerivedInverseLimitFunctor] using
      (CategoryTheory.derivedInverseLimit_isDerivedLimit_of_stagewiseEvaluation
        (A := ModuleCat A) K)
  -- The target is the canonical Milnor short exact sequence after unfolding the fixed-base
  -- textbook `R lim` notation.
  simpa [fixedBaseDerivedInverseLimitFunctor] using
    (CategoryTheory.derivedLimit_cohomology_shortExact
      (C := ModuleCat A)
      (stagewiseModuleDerivedLimitTower K)
      ((fixedBaseDerivedInverseLimitFunctor (A := A)).obj K)
      hKlim
      p)
