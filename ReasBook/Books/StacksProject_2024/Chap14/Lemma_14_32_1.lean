import Mathlib
import StacksProject_2024.Chap14.Definition_14_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Simplicial
open SSet.modelCategoryQuillen

universe u

variable {V U : SSet.{u}} (f : V ⟶ U)

/- Domain-style sampling for Lemma 14.32.1:
- primary domain: simplicial-set lifting properties and coskeletality.
- inspected owner declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.isCoskeletal_iff_isIso`,
  `SimplicialObject.isoCoskOfIsCoskeletal`.
- best owner abstractions:
  `I.rlp` for the textbook phrase “trivial Kan fibration”, and `IsCoskeletal n` for the
  coskeletality hypotheses.
- primitive-vs-derived split:
  primitive data: the morphism `f`, degreewise bijectivity below `n`, surjectivity in degree `n`,
  and the owner-level coskeletality assumptions on source and target;
  derived API: the source-facing phrase “trivial Kan fibration” for `I.rlp`, together with the
  canonical bridge from `IsCoskeletal n` to the unit isomorphism `X ≅ (cosk n).obj X`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that these degreewise hypotheses force a trivial Kan
  fibration;
- `core/canonical`: `I.rlp f` and the owner predicate `IsCoskeletal n`;
- `bridge/view`: `SimplicialObject.isCoskeletal_iff_isIso` and
  `SimplicialObject.isoCoskOfIsCoskeletal`.

There is no better upstream owner theorem to recall directly here; the correct refinement is to
keep the source-facing implication but express both the conclusion and the coskeletality input
through the canonical owners already used elsewhere in the chapter. -/

-- Proof sketch: to prove the boundary lifting property, consider a lifting problem against
-- `∂Δ[k].ι` and split into the cases `k ≤ n` and `k > n`. For `k ≤ n`, use surjectivity in
-- degree `n` together with degreewise bijectivity below `n` to construct a filler compatible with
-- the prescribed boundary. For `k > n`, use the `n`-coskeletality of `V` and `U` to identify
-- `k`-simplices with compatible `n`-skeletal boundary data, so the boundary datum determines a
-- unique filler.
/-- Lemma 14.32.1: a morphism of simplicial sets that is degreewise bijective in simplicial
degrees `< n`, surjective in degree `n`, and whose source and target are `n`-coskeletal is a
trivial Kan fibration, canonically expressed by the owner predicate `I.rlp`. -/
theorem trivialKanFibration_of_bijective_below_of_surjective_of_coskeletal
    (n : ℕ)
    (hbelow : ∀ i < n, Function.Bijective (f.app (op ⦋i⦌)))
    (hsurj : Function.Surjective (f.app (op ⦋n⦌)))
    (hV : V.IsCoskeletal n)
    (hU : U.IsCoskeletal n) :
    I.rlp f := sorry
