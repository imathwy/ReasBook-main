import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 14.2.1:
- primary domain: simplicial operators in `SimplexCategory`
- source-facing content: the basic coface maps `δ_j^n` and codegeneracy maps `σ_j^n`
- core/canonical owner: `SimplexCategory.δ` and `SimplexCategory.σ`
- same-kind upstream declarations:
  `SimplexCategory.δ`,
  `SimplexCategory.σ`,
  `SimplexCategory.δ_comp_δ`,
  `SimplexCategory.σ_comp_σ`
- primitive data: none in this file; the primitive owner declarations already live upstream in
  mathlib
- derived API: the simplicial identities are recalled separately in `Lemma_14_2_3`, so this file
  should recall the owner declarations directly rather than repackage them through local aliases or
  wrappers.
- layer target: `core/canonical` recall of the existing owner declarations, since Definition 14.2.1
  introduces no extra source-facing structure beyond these standard maps.
-/

/- Definition 14.2.1 (1): for `n ≥ 1` and `0 ≤ j ≤ n`, the injective order-preserving map
`δ_j^n : [n - 1] → [n]` skipping `j` is the canonical coface map `SimplexCategory.δ`. -/
recall SimplexCategory.δ

/- Definition 14.2.1 (2): for `n ≥ 0` and `0 ≤ j ≤ n`, the surjective order-preserving map
`σ_j^n : [n + 1] → [n]` with fiber over `j` equal to `{j, j + 1}` is the canonical
codegeneracy map `SimplexCategory.σ`. -/
recall SimplexCategory.σ
