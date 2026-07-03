import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

/- Definition 3.19-extra-1: a category is the canonical mathlib typeclass
`Category C`, whose underlying hom-types, identity morphisms, and composition
come from `CategoryStruct`, and whose axioms are the identity laws
`Category.id_comp`, `Category.comp_id`, and associativity `Category.assoc`. -/
recall Category
