import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap15.Definition_15_69_1
import StacksProject_2024.Chap15.Lemma_15_66_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-
Domain-style sampling:
- primary domain: projective-amplitude criteria in `D(R)` detected by derived `Ext` against
  degree-zero modules;
- sampled owner declarations:
  `HasProjectiveAmplitudeIn` from `Definition_15_69_1`,
  `derivedExtToModuleFunctor` from `Lemma_15_66_1`,
  `ShiftedHom`,
  `Ext^i(X, Y)` from `Definition_13_27_1`,
  `existsUnique_truncation_gap_biprod_and_projectiveAmplitude_of_ext_vanishing` from
    `Lemma_15_77_6`;
- best owner abstraction:
  `source-facing`: the interval and half-line vanishing clauses in the TFAE, written as
    vanishing of the derived extension groups `Ext^i(K, N[0])`;
  `core/canonical`: the chapter owner `derivedExtToModuleFunctor K i` for the unrestricted
    degree-`i` vanishing test on modules;
  `bridge/view`: its value at `N`, namely `ShiftedHom K ((singleFunctor _ 0).obj N) i`, written in
    the chapter notation as `Ext^i(K, N[0])`.

Primitive data here are only the degree-wise vanishing statements with their module argument
visible. The “outside an interval”, “for all degrees above a bound”, and mixed cohomology-plus-Ext
clauses are derived API over the existing Ext owner, so the public theorem surface should keep the
source-facing pointwise `Ext^i(K, N[0])` clauses rather than hide `N` inside
`IsZero (derivedExtToModuleFunctor K i)`.
-/

/-
Proof sketch: follow the Stacks proof. `(1) → (2)` computes `Ext` from a bounded projective
representative. `(2) → (3)` and `(3) → (4)` test cohomology against injective modules. For
`(4) → (1)`, first deduce cohomology vanishing below `a`, choose a bounded-above projective
representative, truncate in degree `a`, and use the degree `1 - a` `Ext`-vanishing plus
Lemma `10.77.2` to show the leftmost cokernel is projective.
-/
/-- Lemma 15.69.2: for an object `K` of `D(R)` and integers `a, b`, the following are
equivalent: `K` has projective-amplitude in `[a, b]`; the derived `Ext` groups
`Ext^i_R(K, N)` vanish for every `R`-module `N` and every
`i ∉ [-b, -a]`; `H^n(K)` vanishes for `n > b` and these groups vanish for all `i > -a`; and
`H^n(K)` vanishes for `n ∉ [a - 1, b]` and `Ext^{-a + 1}_R(K, N)` vanishes for every
`R`-module `N`. -/
theorem projectiveAmplitudeIn_ext_vanishing_tfae
    (K : DMod) (a b : ℤ) :
    List.TFAE
      [ HasProjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc (-b) (-a) →
          ∀ e : Ext^i(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, b < n → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R) (i : ℤ), -a < i → ∀ e : Ext^i(K, (single₀).obj N), e = 0
      , (∀ n : ℤ, n ∉ Set.Icc (a - 1) b → IsZero ((H n).obj K)) ∧
          ∀ (N : ModuleCat R), ∀ e : Ext^(-a + 1)(K, (single₀).obj N), e = 0
      ] := sorry

end

end CategoryTheory
