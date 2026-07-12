import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Domain triage:
- primary domain: linear disjointness for intermediate fields inside a common overfield;
- sampled owner declarations: `IntermediateField.LinearDisjoint`,
  `IntermediateField.linearDisjoint_iff'`, `Subalgebra.linearDisjoint_iff_injective`, and
  `Subalgebra.mulMap`;
- core/canonical owner abstraction: `IntermediateField.LinearDisjoint`;
- layer: `core/canonical` for the definition itself, with a thin `bridge/view` companion recall
  below translating to the tensor-product injectivity formulation from the source;
- primitive data: only the base field `k`, the overfield `Ω`, and the two intermediate fields;
- derived API: passage to `toSubalgebra`, the multiplication map on the tensor product, and the
  injectivity criterion.
-/

/- Definition 9.27.2: for intermediate fields `K` and `L` of the extension `Ω / k`, the Stacks
notion that `K` and `L` are linearly disjoint over `k` in `Ω` is the canonical predicate
`IntermediateField.LinearDisjoint`. -/
recall IntermediateField.LinearDisjoint

namespace IntermediateField

section

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω]
variable {K L : IntermediateField k Ω}

/- Companion recall: the Stacks tensor-product formulation says that the multiplication map
`K ⊗[k] L → Ω` is injective, equivalently that the induced map to the compositum `K ⊔ L` is
injective. This is a `bridge/view` specialization of the canonical subalgebra criterion
`Subalgebra.linearDisjoint_iff_injective`, transported along
`IntermediateField.linearDisjoint_iff'`. -/
#check
  (linearDisjoint_iff'.trans Subalgebra.linearDisjoint_iff_injective :
    K.LinearDisjoint L ↔ Function.Injective (K.toSubalgebra.mulMap L.toSubalgebra))

end

end IntermediateField
