import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap15.Definition_15_65_1
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap15.Definition_15_69_1
import StacksProject_2024.Chap15.Definition_15_75_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => (ModuleCat.single0Functor : ModuleCat R ⥤ DMod)

/-
Domain sampling pass:
* primary domain: projective amplitude and perfectness criteria for pseudo-coherent objects in the
  derived category `D(R)`, tested by derived `Ext` against degree-zero modules;
* sampled owner declarations:
  - `HasProjectiveAmplitudeIn` from `Definition_15_69_1`, the chapter owner for projective
    amplitude;
  - `projectiveAmplitudeIn_ext_vanishing_tfae` from `Lemma_15_69_2`, the source-facing TFAE using
    unrestricted `Ext`-vanishing;
  - `derivedExtFilteredColimitComparison_isIso_of_isMPseudoCoherent` and
    `derivedExtFilteredColimitComparison_mono_at_neg_of_isMPseudoCoherent` from `Lemma_15_66_1`,
    whose statements are phrased on the canonical comparison map `colimit.post`, giving the
    chapter bridge from all modules to finitely presented test modules under
    pseudo-coherence;
  - `isPerfect_iff_isPseudoCoherent_and_hasFiniteTorDimension` from `Lemma_15_75_2`, the
    perfectness owner criterion.

Source/core/bridge triage:
* `source-facing`: the finitely-presented `Ext`-vanishing clauses appearing in Stacks
  `Lemma 15.78.4`;
* `core/canonical`: `HasProjectiveAmplitudeIn`, `HasTorAmplitudeIn`, and
  `DerivedCategory.IsPerfect`, together with the unrestricted `Ext`-vanishing package from
  `Lemma_15_69_2`;
* `bridge/view`: Lemma `15.66.1`, which justifies replacing unrestricted module tests by
  finitely presented ones for pseudo-coherent objects.

Primitive data here are only the finitely-presented `Ext`-vanishing predicates themselves. The
perfectness, tor-amplitude, projective-amplitude, and cohomology-vanishing owners are already
canonical upstream, so this file should keep only the source-facing specialization and reuse those
owners directly in the main `TFAE`.
-/

-- Proof sketch: `(2) → (1)` is the final implication of Lemma `15.75.2`. For `(1) → (2)`, a
-- projective representative concentrated in `[a, b]` is automatically a flat representative in
-- the same range, so Lemma `15.75.2` upgrades it to perfection with tor-amplitude in `[a, b]`.
-- Under pseudo-coherence, Lemma `15.66.1` together with Lemma `10.11.3` lets one test the relevant
-- `Ext`-vanishing only on finitely presented modules, and then Lemma `15.69.2` gives the
-- equivalence with the projective-amplitude criteria.
/-- Lemma 15.78.4: let `R` be a ring, let `K` be a pseudo-coherent object of `D(R)`, and let
`a, b ∈ ℤ`. Then the following are equivalent: `K` has projective-amplitude in `[a, b]`; `K` is
perfect and has tor-amplitude in `[a, b]`; `Ext^i_R(K, N) = 0` for every finitely presented
`R`-module `N` and every `i ∉ [-b, -a]`; `H^n(K) = 0` for `n > b` and
`Ext^i_R(K, N) = 0` for every finitely presented `R`-module `N` and every `i > -a`; and
`H^n(K) = 0` for `n ∉ [a - 1, b]` and `Ext^{-a + 1}_R(K, N) = 0` for every finitely presented
`R`-module `N`. -/
theorem projectiveAmplitudeIn_perfect_finitelyPresented_ext_tfae_of_isPseudoCoherent
    (K : DMod) (a b : ℤ) (hK : K.IsPseudoCoherent) :
    List.TFAE [
      HasProjectiveAmplitudeIn K a b,
      K.IsPerfect ∧ HasTorAmplitudeIn K a b,
      ∀ (N : ModuleCat R) [Module.FinitePresentation R N] (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          ∀ e : Ext^i(K, (single₀).obj N), e = 0,
      (∀ n : ℤ, b < n → IsZero ((H n).obj K)) ∧
        ∀ (N : ModuleCat R) [Module.FinitePresentation R N] (i : ℤ), -a < i →
          ∀ e : Ext^i(K, (single₀).obj N), e = 0,
      (∀ n : ℤ, n ∉ Set.Icc (a - 1) b → IsZero ((H n).obj K)) ∧
        ∀ (N : ModuleCat R) [Module.FinitePresentation R N],
          ∀ e : Ext^(-a + 1)(K, (single₀).obj N), e = 0
    ] := sorry

end

end CategoryTheory
