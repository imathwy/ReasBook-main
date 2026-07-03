import Mathlib
import StacksProject_2024.Chap15.Definition_15_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

section

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat R)}

/- Domain-style sampling:
* primary domain: short exact sequences of `R`-modules, projective splittings, and stable
  freeness;
* sampled owner declarations:
  `ShortComplex.ShortExact.splittingOfProjective`,
  `ModuleCat.free_shortExact`,
  `Module.Projective.of_free`,
  `Module.StablyFree`;
* best owner abstraction: the ambient owner is the short exact complex `S : ShortComplex
  (ModuleCat R)` with `hS : S.ShortExact`;
* primitive vs. derived:
  the primitive end-term data are the canonical owners `Module.Finite` and `Module.StablyFree`,
  while "finite stably free" is only their conjunction and should remain derived API rather than a
  separate wrapper; projectivity of a stably free end term is supporting bridge data rather than
  primitive public input for the closure lemmas that only use stable freeness.

Source/core/bridge triage:
* `source-facing`: the three closure statements from Stacks Lemma 15.3.2;
* `core/canonical`: `hS.splittingOfProjective` and the owner properties `Module.Finite` /
  `Module.StablyFree`;
* `bridge/view`: the identification of the middle term with a split product coming from the
  canonical splitting. -/

-- Proof sketch: use the canonical splitting `hS.splittingOfProjective`, so `S.X₂` identifies with
-- `S.X₁ × S.X₃`. Stabilize the two end terms by finite free summands, use that products preserve
-- finite/free modules, and apply `ModuleCat.free_shortExact` to obtain a finite free stabilization
-- of `S.X₂`.
/-- Lemma 15.3.2 (1): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P'` and `P''` are finite stably free, then `P` is finite stably free. -/
theorem finiteStablyFree_X₂_of_shortExact (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₂ ∧ Module.StablyFree R S.X₂ := sorry

-- Proof sketch: via `hS.splittingOfProjective`, the canonical decomposition
-- `S.X₂ ≃ₗ[R] S.X₁ × S.X₃` exhibits `S.X₃` as a direct summand of `S.X₂`; transport finite stable
-- freeness across that split-product description.
/-- Lemma 15.3.2 (2): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P'` and `P` are finite stably free, then `P''` is finite stably free. -/
theorem finiteStablyFree_X₃_of_shortExact (hS : S.ShortExact)
    [Module.Projective R S.X₃]
    [Module.Finite R S.X₁] [Module.StablyFree R S.X₁]
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂] :
    Module.Finite R S.X₃ ∧ Module.StablyFree R S.X₃ := sorry

-- Proof sketch: use the same canonical splitting of `hS`; under
-- `S.X₂ ≃ₗ[R] S.X₁ × S.X₃`, the module `S.X₁` is the complementary direct summand to `S.X₃`, so
-- finite stable freeness descends from the split-product description.
/-- Lemma 15.3.2 (3): in a short exact sequence `0 ⟶ P' ⟶ P ⟶ P'' ⟶ 0` of finite projective
`R`-modules, if `P` and `P''` are finite stably free, then `P'` is finite stably free. -/
theorem finiteStablyFree_X₁_of_shortExact (hS : S.ShortExact)
    [Module.Finite R S.X₂] [Module.StablyFree R S.X₂]
    [Module.Finite R S.X₃] [Module.StablyFree R S.X₃] :
    Module.Finite R S.X₁ ∧ Module.StablyFree R S.X₁ := sorry

end CategoryTheory.ShortComplex

end
