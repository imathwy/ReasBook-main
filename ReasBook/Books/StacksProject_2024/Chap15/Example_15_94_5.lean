import Mathlib
import stacks_project.Chap15.Lemma_15_94_6
import stacks_project.Chap15.PrincipalIdeal
import stacks_project.Chap15.Remark_15_94_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SequentialInverseSystem
open scoped PrincipalIdeal PrincipalTateModule

universe u

attribute [local instance] HasDerivedCategory.standard

/- Domain-style sampling for Example `15.94.5`.
- primary domain: principal derived completion of modules and derived objects, together with the
  degree-`-1`/`0` module case and the general cohomology short exact sequence;
- sampled owner declarations:
  `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `principalTateModule`,
  `DerivedCategory.derivedCompletionOf`;
- sampled bridge companion declarations:
  `principalDerivedCompletion_cohomology_has_comparison_diagram`;
- best owner abstraction: the source-facing owner is the canonical derived completion object
  `((single0).obj M)^∧[(f), principalIdeal_fg f]`, together with the chapter owners
  `principalTateModule` and `principalPowerQuotientTower`/`principalPowerTorsionTower`; the later
  comparison theorem from `Lemma_15_94_6` is bridge/view data, while the degree-zero short exact
  sequence itself is owned canonically by the Milnor theorem
  `CategoryTheory.derivedLimit_cohomology_shortExact` specialized to the principal completion
  tower;
- primitive vs. derived:
  primitive data are the ring element `f`, the module `M`, and the canonical principal towers
  `principalPowerQuotientTower f M` and `principalPowerTorsionTower f M`, together with the
  derived object `K` and degree `p` for the general cohomology sequence;
  derived API is the `H^{-1}` Tate-module comparison, the module-level `H^0` short exact sequence
  against the ordinary completion tower, the general short exact sequence
  `0 → H^0(H^p(K)^∧) → H^p(K^∧) → T_f(H^{p+1}(K)) → 0`, and the amplitude bound below.

Source/core/bridge triage:
- `source-facing`: the `H^{-1}`/`H^0` module statements for
  `((single0).obj M)^∧[(f), principalIdeal_fg f]`, the general short exact sequence for
  `H^p(K^∧[(f), principalIdeal_fg f])`, and the amplitude bound;
- `core/canonical`: `CategoryTheory.derivedLimit_cohomology_shortExact`,
  `principalTateModule`, `principalPowerQuotientTower`, `principalPowerTorsionTower`, and
  `DerivedCategory.derivedCompletionOf`;
- `bridge/view`: the later comparison theorem from `Lemma_15_94_6`, specialized to `K = M[0]` and
  `p = -1, 0` in the module case and used below to recover the general cohomology sequence. -/

section

variable {A : Type u} [CommRing A]

local notation "ModA" => ModuleCat A
local notation "DMod" => DerivedCategory ModA
local notation "H" => DerivedCategory.homologyFunctor ModA
local notation "single0" => DerivedCategory.singleFunctor ModA (0 : ℤ)

/- Example 15.94.5: the source-facing Tate module in this chapter is the owner
`principalTateModule`, written `T[f] M`. -/
recall principalTateModule

/- Companion bridge: Lemma `15.94.6` records the comparison rows and columns used to recover the
source-facing module statements below. -/

section

variable (f : A)

local notation "I" => ((f) : Ideal A)
local notation "hI" => principalIdeal_fg f

/-- Example 15.94.5: the degree-zero cohomology of principal derived completion of a module fits
into the short exact sequence
`0 → R^1 lim_n M[f^(n + 1)] → H^0(M^∧) → lim_n M / f^(n + 1) M → 0`. -/
theorem principalDerivedCompletionModule_hzero_shortExact
    (M : ModA) :
    ∃ (ι :
        firstDerivedLimit (principalPowerTorsionTower f M) ⟶
          (H 0).obj (((single0).obj M)^∧[I, hI]))
      (π :
        (H 0).obj (((single0).obj M)^∧[I, hI]) ⟶
          limit (principalPowerQuotientTower f M))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-- Example 15.94.5: the degree-`-1` cohomology of principal derived completion of a module is
canonically isomorphic to the principal Tate module `T[f] M`. -/
theorem principalDerivedCompletionModule_hnegOne_isomorphic_tateModule
    (M : ModA) :
    IsIsomorphic ((H (-1)).obj (((single0).obj M)^∧[I, hI])) (T[f] M) := sorry

/-- Example 15.94.5: for every `K ∈ D(A)` and `p : ℤ`, the cohomology of principal derived
completion fits into the short exact sequence
`0 → H^0(H^p(K)^∧) → H^p(K^∧) → T_f(H^{p+1}(K)) → 0`. -/
theorem principalDerivedCompletion_cohomology_shortExact
    (K : DMod) (p : ℤ) :
    ∃ (ι :
        (H 0).obj (((single0).obj ((H p).obj K))^∧[I, hI]) ⟶
          (H p).obj (K^∧[I, hI]))
      (π :
        (H p).obj (K^∧[I, hI]) ⟶
          T[f] ((H (p + 1)).obj K))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

-- Proof sketch: the derived inverse limit of a tower of modules has no cohomology above degree
-- `1`, and for the principal completion tower all degrees below `-1` are trivially zero because
-- each stage is a two-term complex.
/-- The derived `(f)`-adic completion of a module has cohomology only in degrees `-1` and `0`. -/
theorem principalDerivedCompletionModule_homology_isZero_of_ne_zero_or_negOne
    (M : ModA) (p : ℤ)
    (hp0 : p ≠ 0) (hpneg1 : p ≠ -1) :
    IsZero ((H p).obj (((single0).obj M)^∧[I, hI])) := sorry

end

end
