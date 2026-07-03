import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap13.Definition_13_27_1
import StacksProject_2024.Chap15.Definition_15_70_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedExt

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/- Domain-style sampling:
- primary domain: injective-amplitude criteria in `DerivedCategory (ModuleCat R)`, expressed by
  vanishing of derived `Ext` groups;
- inspected owner declarations:
  `CategoryTheory.HasInjectiveAmplitudeIn`,
  `CategoryTheory.Ext^i(_, _)`,
  `CategoryTheory.projectiveAmplitudeIn_ext_vanishing_tfae`,
  `CategoryTheory.injective_iff_ext_one_eq_zero`,
  `CategoryTheory.injective_tfae_extOneFromIdealQuotient_eq_zero_baer`;
- best owner abstraction: the source-facing owner is `HasInjectiveAmplitudeIn K a b`; the
  shifted-Hom vanishing clauses are derived API describing that owner, not a separate local owner;
- layer: `source-facing`, since this lemma gives the textbook criterion for the existing owner
  `HasInjectiveAmplitudeIn`;
- primitive data: `K : DMod` and the bounds `a b : ℤ`;
- derived API: testing `Ext^i((single₀).obj N, K)` and its ideal-quotient specialization by
  direct vanishing `∀ e, e = 0`, in the same chapter style as the projective-amplitude and
  Baer-criterion files;
- bridge/view: the core owner remains `ShiftedHom`, but `Ext^i(_, _)` is the canonical
  source-facing notation already introduced in Chapter `13`, so the public theorem surface should
  use that notation rather than restating the raw owner. -/

-- Proof sketch: prove `(1) → (2)` by computing morphisms from degree-zero modules against an
-- injective representative supported in `[a, b]`; `(2) → (3)` is immediate by specializing to
-- quotient modules `R/I`; for `(3) → (1)`, first recover cohomological boundedness of `K` from
-- the case `I = ⊥`, then truncate an injective resolution and apply Lemma `15.55.4` to the final
-- kernel using the vanishing for all quotients `R/I`.
/-- Lemma 15.70.2: for an object `K` of `D(R)` and integers `a, b`, the following are
equivalent: `K` is represented by a cochain complex of injective `R`-modules supported in
degrees `[a, b]`; for every `R`-module `N`, the groups `Ext^i_R(N, K)` vanish for
`i ∉ [a, b]`; and it is enough to test this vanishing on quotient modules `R/I` for ideals
`I ⊆ R`. -/
theorem injectiveAmplitudeIn_ext_vanishing_tfae
    (K : DMod) (a b : ℤ) :
    List.TFAE
      [ HasInjectiveAmplitudeIn K a b
      , ∀ (N : ModuleCat R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj N, K), e = 0
      , ∀ (I : Ideal R) (i : ℤ), i ∉ Set.Icc a b →
          ∀ e : Ext^i((single₀).obj (ModuleCat.of R (R ⧸ I)), K), e = 0
      ] := sorry

end

end CategoryTheory
