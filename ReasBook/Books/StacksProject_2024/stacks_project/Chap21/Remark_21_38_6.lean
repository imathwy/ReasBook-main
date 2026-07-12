import StacksProject_2024.Chap04.«4_34_2_1»
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap21.Remark_21_37_3
import StacksProject_2024.Chap21.Lemma_21_38_5

namespace CategoryTheory
namespace FibredCategoryOver

/-
Domain-style sampling for Remark 21.38.6:
- primary domain: projection lower-shriek / forgetful comparison for the canonical morphism from
  a fibred category over a ringed site to the base fibred category;
- sampled owner declarations:
  `toBase`,
  `lowerShriek_forget_functor_isomorphic`,
  `derivedLowerShriek_forget_comparison`,
  `FibredCategoryMor.inheritedRingedSiteHom`;
- best owner abstraction: the canonical owner data is the morphism `toBase P`, while the
  underived and derived comparison morphisms are already owned upstream by
  `lowerShriek_forget_functor_isomorphic` and
  `derivedLowerShriek_forget_comparison`;
- primitive data: a ringed site `X`, a fibred category `P` over `X`, and the canonical base
  morphism `toBase P`;
- derived API: none locally; this file remains a projection-specialization recall surface, and
  downstream users specialize the upstream owners at `toBase P` instead of going through a local
  wrapper theorem.

Source/core/bridge triage:
- `source-facing`: Remark `21.38.6`, specialized to the projection from `P`;
- `core/canonical`: `toBase`, `lowerShriek_forget_functor_isomorphic`, and
  `derivedLowerShriek_forget_comparison`;
- `bridge/view`: this file, which only recalls those existing owners in the projection case.
-/

/- The canonical projection morphism is already owned upstream by `toBase`. -/
recall toBase

/- Remark 21.38.6 (1): the underived projection comparison is obtained by specializing
`lowerShriek_forget_functor_isomorphic` at the canonical morphism
`toBase P : P ⟶ ofFunctor (𝟭 X)`. No separate projection-specific wrapper is introduced here. -/
recall lowerShriek_forget_functor_isomorphic

/- Remark 21.38.6 (2): the derived projection comparison is obtained by specializing
`derivedLowerShriek_forget_comparison` at the same canonical base morphism `toBase P`. -/
recall derivedLowerShriek_forget_comparison

end FibredCategoryOver
end CategoryTheory
