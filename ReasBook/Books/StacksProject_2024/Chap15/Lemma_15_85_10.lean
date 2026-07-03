import Mathlib
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap15.Definition_15_71_4
import StacksProject_2024.Chap15.Definition_15_89_1
import StacksProject_2024.Chap15.Lemma_15_85_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Limits
open PrimeSpectrum
open scoped PrimeSpectrum

universe u

attribute [local instance] HasDerivedCategory.standard

variable {R : Type u} [CommRing R]

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation:max "H^" i:max => DerivedCategory.homologyFunctor (ModuleCat R) i

/- Domain-style sampling for Lemma 15.85.10:
- primary domain: two-term derived `R`-complexes, `I`-projective cohomology, and finite
  basic-open localization criteria for projectivity on the open complement `Spec R \ V(I)`;
- sampled owner declarations in this domain:
  `Module.IsIdealProjective`,
  `Module.IsIdealPowerTorsion`,
  `Module.LocallyFree`,
  `twoTermExtOneAnnihilatedByIdeal`,
  `twoTermExtOneAnnihilatedByIdealOnFiniteModules`;
- best owner abstraction: the primitive source data is the pair of cohomology modules
  `H^(-1)(K)` and `H^0(K)` together with the chapter owners `Module.IsIdealProjective` and
  `Module.IsIdealPowerTorsion`; the localization-cover clauses are source-facing finite-set
  projectivity criteria for `H⁰(K)` on finite basic-open neighborhoods of `Spec R \ V(I)`, so
  they stay inline in the theorem statement rather than being promoted to separate public owners;
- primitive data vs. derived API: annihilator containment, ideal-projectivity, and localized
  projectivity of `H⁰(K)` are primitive clause data, while the `Ext¹` reformulations are derived
  API supplied upstream by Lemma `15.85.5`.

Source/core/bridge triage:
- `source-facing`: the TFAE statements below and their finite-localization clauses;
- `core/canonical`: `Module.IsIdealProjective`, `Module.IsIdealPowerTorsion`,
  `twoTermExtOneAnnihilatedByIdeal`, and `twoTermExtOneAnnihilatedByIdealOnFiniteModules`;
- `bridge/view`: the comparison between the cohomology-side conditions and the `Ext¹` conditions.
-/

-- Proof sketch: use the distinguished triangle
-- `H^{-1}(K)[1] ⟶ K ⟶ H^0(K)[0] ⟶ H^{-1}(K)[2]` to compare annihilation of `Ext^1_R(K, N)` by
-- powers of `I` with annihilation of `H^{-1}(K)` and `I^c`-projectivity of `H^0(K)`. In the
-- Noetherian finite case, combine Lemma `15.85.5` with the local criterion for `I`-projective
-- modules and the standard algebraic equivalences between `V(f_1, ..., f_s)` and powers of `I`.
/-- Lemma 15.85.10: for a derived `R`-complex `K` with cohomology concentrated in degrees `-1`
and `0`, the existence of a power `I^c` satisfying the equivalent conditions `(1)`, `(2)`, `(3)`
of Lemma `15.85.5` is equivalent to the existence of a power `I^c` that annihilates `H^{-1}(K)`
and makes `H^0(K)` `I^c`-projective. -/
theorem two_term_ideal_power_projectivity_tfae
    (K : DMod) (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K)
    ] := sorry

/-- Lemma 15.85.10, Noetherian finite case: if `R` is Noetherian and `H^{-1}(K)` and `H^0(K)` are
finite, then the two equivalent conditions of `two_term_ideal_power_projectivity_tfae` are also
equivalent to the finite-module version of Lemma `15.85.5` and to the local projectivity criteria
obtained from finite families cutting out `V(I)`, viewed as finite basic-open covers of
`Spec R \ V(I)`. -/
theorem two_term_ideal_power_projectivity_tfae_of_isNoetherianRing
    [IsNoetherianRing R]
    (K : DMod) (I : Ideal R)
    (hKGE : K.IsGE (-1))
    (hKLE : K.IsLE 0)
    (hHneg1 : Module.Finite R ((H^(-1)).obj K))
    (hH0 : Module.Finite R ((H^0).obj K)) :
    List.TFAE [
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdeal K (I ^ c),
      ∃ c : ℕ,
        I ^ c ≤ Module.annihilator R ((H^(-1)).obj K) ∧
          Module.IsIdealProjective (I ^ c) ((H^0).obj K),
      ∃ c : ℕ, twoTermExtOneAnnihilatedByIdealOnFiniteModules K (I ^ c),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          V((↑s : Set R)) ⊆ V((I : Set R)) ∧
            ∀ f ∈ s, Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∃ s : Finset R,
          (↑s : Set R) ⊆ I ∧
            V((↑s : Set R)) = V((I : Set R)) ∧
              ∀ f ∈ s,
                Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K)),
      Module.IsIdealPowerTorsion I ((H^(-1)).obj K) ∧
        ∀ s : Finset R,
          (↑s : Set R) ⊆ I →
            V((↑s : Set R)) = V((I : Set R)) →
              ∀ f ∈ s,
                Module.Projective (Localization.Away f) (LocalizedModule.Away f ((H^0).obj K))
    ] := sorry

end

end CategoryTheory
