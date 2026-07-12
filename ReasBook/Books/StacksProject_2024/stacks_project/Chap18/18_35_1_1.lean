import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {𝒜 𝒝 𝒜' 𝒝' : Sheaf J CommRingCat}
variable (α : 𝒜 ⟶ 𝒝) (ρ : 𝒜 ⟶ 𝒜') (β : 𝒜' ⟶ 𝒝') (φ : 𝒝 ⟶ 𝒝')

/- Domain-style sampling for 18.35.1.1:
- primary domain: categorical commutative squares in the category `Sheaf J CommRingCat` of sheaves
  of commutative rings on a site;
- sampled same-domain declarations:
  `CategoryTheory.CommSq`,
  `CommSq.mk`,
  `CommSq.w`,
  `stacks_project.Chap17.17_31_1_1`;
- best owner abstraction: `CategoryTheory.CommSq`;
- primitive data: the four corner sheaves and the four displayed morphisms
  `α : 𝒜 ⟶ 𝒝`, `ρ : 𝒜 ⟶ 𝒜'`, `β : 𝒜' ⟶ 𝒝'`, and `φ : 𝒝 ⟶ 𝒝'`;
- derived API: the equality `sq.w` and the standard `CommSq` constructors/composition lemmas, so
  no site-specific wrapper should be introduced here.

Source/core/bridge triage:
- `source-facing`: the displayed commutative square of sheaves of commutative rings on the site;
- `core/canonical`: `CategoryTheory.CommSq`;
- `bridge/view`: the specialization of `CommSq` to `Sheaf J CommRingCat`.
-/

/- 18.35.1.1: the displayed square of sheaves of commutative rings on the site,
`𝒜 ⟶ 𝒝`, `𝒜 ⟶ 𝒜'`, `𝒝 ⟶ 𝒝'`, `𝒜' ⟶ 𝒝'`, is formalized by the canonical
commutative-square predicate in `Sheaf J CommRingCat`. -/
#check CommSq ρ α β φ
