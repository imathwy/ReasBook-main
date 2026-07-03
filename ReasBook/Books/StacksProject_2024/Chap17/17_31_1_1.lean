import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat

universe u

variable {X : TopCat.{u}}
variable {𝒜 𝒜' 𝒝 𝒝' : X.Sheaf CommRingCat.{u}}
variable (α : 𝒜 ⟶ 𝒝) (ρ : 𝒜 ⟶ 𝒜') (β : 𝒜' ⟶ 𝒝') (φ : 𝒝 ⟶ 𝒝')

/- Domain-style sampling for 17.31.1.1:
- primary domain: categorical commutative squares in the category `X.Sheaf CommRingCat` of sheaves
  of commutative rings on a topological space `X`;
- sampled same-domain declarations:
  `CategoryTheory.CommSq`,
  `CommSq.mk`,
  `CommSq.w`,
  `CommSq.horiz_comp`;
- best owner abstraction: `CategoryTheory.CommSq`;
- primitive data: the algebra-over-base square maps `α : 𝒜 ⟶ 𝒝`, `ρ : 𝒜 ⟶ 𝒜'`,
  `β : 𝒜' ⟶ 𝒝'`, and `φ : 𝒝 ⟶ 𝒝'` in `X.Sheaf CommRingCat.{u}`;
- derived API: the composite equality `sq.w` and the standard `CommSq` construction/composition
  lemmas, so no sheaf-specific wrapper should be introduced here. In particular, the source roles
  of `𝒜, 𝒝, 𝒜', 𝒝'` should remain visible because they drive the later comparison
  `NL_{𝒝/𝒜} → NL_{𝒝'/𝒜'}`.

Source/core/bridge triage:
- `source-facing`: the displayed algebra-over-base commutative square of sheaves of commutative
  rings on `X`;
- `core/canonical`: `CategoryTheory.CommSq`;
- `bridge/view`: the specialization of `CommSq` to the sheaf category `X.Sheaf CommRingCat`.
-/

/- 17.31.1.1: the displayed square of sheaves of commutative rings on `X`,
`𝒜 ⟶ 𝒝`, `𝒜 ⟶ 𝒜'`, `𝒝 ⟶ 𝒝'`, `𝒜' ⟶ 𝒝'`, is formalized by the canonical
commutative-square predicate in `X.Sheaf CommRingCat`. -/
#check CommSq ρ α β φ
