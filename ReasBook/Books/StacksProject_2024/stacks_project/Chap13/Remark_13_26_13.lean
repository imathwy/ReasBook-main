import Mathlib
import StacksProject_2024.stacks_project.Chap19.Remark_19_9_4

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

/-
Domain-style sampling:
- primary domain: object properties and full subcategories of abelian categories with enough
  injectives;
- sampled owner-side declarations:
  `ObjectProperty.ofObj`,
  `ObjectProperty.ofObj_le_iff`,
  `ObjectProperty.Small`,
  `ObjectProperty.IsWeakSerreClass`,
  `exists_small_abelian_fullSubcategory_containing`,
  `EnoughInjectives`;
- best owner abstraction: a small weak-Serre object property `P : ObjectProperty 𝒜`;
- primitive data: a small object property `E : ObjectProperty 𝒜`, together with the target owner
  data `E ≤ P`, `ObjectProperty.Small P`, `P.IsWeakSerreClass`, and
  `EnoughInjectives P.FullSubcategory`;
- derived API: the source-facing family-membership bridge `∀ i, P (A i)`, induced from
  `ObjectProperty.ofObj_le_iff`, the abelian structure on `P.FullSubcategory`, and the additional
  conclusion `EnoughInjectives P.FullSubcategory`.

Layer triage:
- `source-facing`: the existence of a small abelian full subcategory with enough injectives
  containing the family `A`;
- `core/canonical`: `ObjectProperty.Small`, `ObjectProperty.IsWeakSerreClass`, and
  `EnoughInjectives P.FullSubcategory`;
- `bridge/view`: the equivalence between owner-side containment `ObjectProperty.ofObj A ≤ P` and
  the source-facing pointwise condition `∀ i, P (A i)` via `ObjectProperty.ofObj_le_iff`.
-/

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [EnoughInjectives 𝒜]
variable {I : Type w}

-- Proof sketch: first use `exists_small_abelian_fullSubcategory_containing` on `E` to obtain a
-- small weak-Serre object property `P` containing `E`; its full subcategory is canonically
-- abelian, and the remaining content is the extra `EnoughInjectives` conclusion on
-- `P.FullSubcategory`.
/-- Owner refinement of Remark 13.26.13: any small object property in an abelian category with
enough injectives is contained in a small weak-Serre object property whose full subcategory has
enough injectives. -/
theorem exists_small_abelian_fullSubcategory_with_enough_injectives_containing
    (E : ObjectProperty 𝒜) [ObjectProperty.Small.{w} E] :
    ∃ P : ObjectProperty 𝒜,
      E ≤ P ∧ ObjectProperty.Small.{w} P ∧
        P.IsWeakSerreClass ∧ EnoughInjectives P.FullSubcategory := sorry

-- Proof sketch: specialize the owner theorem above to the small object property
-- `ofObj A`.
/-- Remark 13.26.13: in a possibly large abelian category with enough injectives, every
set-indexed family of objects is contained in a small full subcategory that is abelian and has
enough injectives. -/
theorem exists_small_abelian_subcategory_with_enough_injectives_containing
    (A : I → 𝒜) :
    ∃ P : ObjectProperty 𝒜,
      (∀ i, P (A i)) ∧ ObjectProperty.Small.{w} P ∧
        P.IsWeakSerreClass ∧ EnoughInjectives P.FullSubcategory := by
  simpa [ObjectProperty.ofObj_le_iff] using
    exists_small_abelian_fullSubcategory_with_enough_injectives_containing
      (ObjectProperty.ofObj A)

end

end CategoryTheory
