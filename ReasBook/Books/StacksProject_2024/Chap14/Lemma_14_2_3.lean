import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 14.2.3:
- primary domain: simplicial identities in `SimplexCategory`
- source-facing statements: the six relations among the canonical coface maps `δ` and
  codegeneracy maps `σ`
- core/canonical owner: the mathlib declarations
  `SimplexCategory.δ_comp_δ`,
  `SimplexCategory.δ_comp_σ_of_le`,
  `SimplexCategory.δ_comp_σ_self`,
  `SimplexCategory.δ_comp_σ_succ`,
  `SimplexCategory.δ_comp_σ_of_gt`,
  `SimplexCategory.σ_comp_σ`
- same-kind upstream declarations inspected:
  `SimplexCategory.δ`,
  `SimplexCategory.σ`,
  `SimplexCategory.δ_comp_δ`,
  `SimplexCategory.σ_comp_σ`
- primitive data: the canonical face and degeneracy maps `SimplexCategory.δ` and
  `SimplexCategory.σ`
- derived API: the six simplicial identities are theorem-level consequences of that owner data, so
  this file should expose only the canonical owner theorems, not local wrappers or restated `_iff`
  surfaces
- layer target: `core/canonical` recall of the existing owner theorems, since this lemma adds no
  new source-facing structure beyond the standard simplicial identities.
-/

/- Lemma 14.2.3 (1): the coface maps satisfy the simplicial relation
`δ_j^{n + 1} ∘ δ_i^n = δ_i^{n + 1} ∘ δ_{j - 1}^n` for `0 ≤ i < j ≤ n + 1`. -/
recall SimplexCategory.δ_comp_δ

/- Lemma 14.2.3 (2): if `0 ≤ i < j ≤ n - 1`, then the coface and codegeneracy maps satisfy
`σ_j^{n - 1} ∘ δ_i^n = δ_i^{n - 1} ∘ σ_{j - 1}^{n - 2}`. -/
recall SimplexCategory.δ_comp_σ_of_le

/- Lemma 14.2.3 (3): the composite `σ_j^{n - 1} ∘ δ_j^n` is the identity on `[n - 1]`. -/
recall SimplexCategory.δ_comp_σ_self

/- Lemma 14.2.3 (4): the composite `σ_j^{n - 1} ∘ δ_{j + 1}^n` is the identity on `[n - 1]`. -/
recall SimplexCategory.δ_comp_σ_succ

/- Lemma 14.2.3 (5): if `0 < j + 1 < i ≤ n`, then the coface and codegeneracy maps satisfy
`σ_j^{n - 1} ∘ δ_i^n = δ_{i - 1}^{n - 1} ∘ σ_j^{n - 2}`. -/
recall SimplexCategory.δ_comp_σ_of_gt

/- Lemma 14.2.3 (6): the codegeneracy maps satisfy the simplicial relation
`σ_j^{n - 1} ∘ σ_i^n = σ_i^{n - 1} ∘ σ_{j + 1}^n` for `0 ≤ i ≤ j ≤ n - 1`. -/
recall SimplexCategory.σ_comp_σ
