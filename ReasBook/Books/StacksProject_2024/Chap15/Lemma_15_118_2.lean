import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap10.Definition_10_78_1
import StacksProject_2024.Chap15.Definition_15_118_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory MonoidalCategory

universe u

namespace ModuleCat

section

variable {R : Type u} [CommRing R]
variable (M : ModuleCat R)

/- Domain-style sampling for Lemma 15.118.2:
- primary domain: invertible modules and rank-one finite local freeness in `ModuleCat R`;
- sampled owner declarations:
  `Module.FiniteLocallyFreeOfRank R M 1`,
  `(tensorLeft M).IsEquivalence`,
  `tensorLeft_isEquivalence_iff_moduleInvertible`,
  `Module.Invertible.left`,
  `tensorLeft_isEquivalence_iff_exists_tensor_inverse`;
- best owner abstraction: the chapter-wide tensor-left equivalence owner `(tensorLeft M).IsEquivalence`;
- primitive vs. derived:
  the source-facing primitive clauses are rank-one finite local freeness and the one-sided
  tensor-unit witness `∃ N, M ⊗ N ≅ 𝟙`, while the chapter owner `(tensorLeft M).IsEquivalence`
  is the canonical core abstraction tying them together; the specialized predicate
  `Module.Invertible R M` and the two-sided tensor-inverse criterion are derived bridge/view API.

Source/core/bridge triage:
- `source-facing`: the rank-one finite-locally-free / invertible / tensor-inverse TFAE;
- `core/canonical`: `(tensorLeft M).IsEquivalence`;
- `bridge/view`: the module-specific predicate `Module.Invertible R M`, the passage from the
  one-sided tensor-unit witness to invertibility via `Module.Invertible.left`, and the Chapter
  `4` two-sided tensor-inverse comparison
  `tensorLeft_isEquivalence_iff_exists_tensor_inverse`.

Definition `15.118.1` already identifies the specialized mathlib predicate `Module.Invertible R M`
with the chapter owner `(tensorLeft M).IsEquivalence`, so the present source-facing TFAE keeps the
chapter owner itself and the genuinely source-facing one-sided tensor-unit condition. -/

-- Proof sketch: if `M` is finite locally free of rank `1`, take the dual module
-- `Module.Dual R M`; the evaluation pairing becomes an isomorphism after localizing on any open
-- where `M` is free of rank `1`, and Lemma `10.23.2` descends that isomorphism globally. If
-- `M ⊗ N ≅ R`, first promote that one-sided tensor-unit witness to `Module.Invertible R M` via
-- `Module.Invertible.left`, then use Definition `15.118.1` to reach the chapter owner
-- `(tensorLeft M).IsEquivalence`. Conversely, if `tensorLeft M` is an equivalence, apply the
-- Chapter `4` owner theorem `tensorLeft_isEquivalence_iff_exists_tensor_inverse` to obtain a
-- two-sided tensor inverse and then forget the second isomorphism; the resulting local tensor
-- trivializations recover finite local freeness of rank `1` by the finite-projective local
-- criterion.
/-- Lemma 15.118.2: for an `R`-module `M`, the following are equivalent: `M` is finite locally
free of rank `1`; tensoring on the left by `M` is an equivalence of `ModuleCat R`; and there
exists an `R`-module `N` such that `M ⊗ N` is isomorphic to the tensor unit in `ModuleCat R`.
The specialized predicate `Module.Invertible R M` remains only a bridge from
Definition `15.118.1`, while the public statement keeps the chapter owner
`(tensorLeft M).IsEquivalence` and the source-facing one-sided tensor-unit witness. -/
theorem invertible_tfae_finiteLocallyFreeOfRank_one_and_tensor_unit :
    List.TFAE
      [ Module.FiniteLocallyFreeOfRank R M 1
      , (tensorLeft M).IsEquivalence
      , ∃ N : ModuleCat R, Nonempty (M ⊗ N ≅ 𝟙_ _)
      ] := sorry

end

end ModuleCat
