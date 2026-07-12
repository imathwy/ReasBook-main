import Mathlib
import Mathlib.Tactic.Recall
import StacksProject_2024.Chap10.Lemma_10_132_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Domain-style sampling:
- primary domain: algebraic de Rham differentials on exterior powers of Kähler differentials;
- sampled same-domain declarations:
  `KaehlerDifferential.D`,
  `DeRhamFamily`,
  `IsExteriorPowerDeRhamDifferential.degree_zero`,
  `IsExteriorPowerDeRhamDifferential.degree_one`,
  `IsExteriorPowerDeRhamDifferential.higher`;
- owner abstraction: `IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D R S) δ`.

Source/core/bridge triage:
- `source-facing`: the exact-form formulas of item `17.30.1.1`;
- `core/canonical`: the owner predicate `IsExteriorPowerDeRhamDifferential`;
- `bridge/view`: evaluating the degree-zero owner equality on an element `b₀ : S`.

Primitive data is the differential family `δ`; the exact-form rules are derived API from the owner
predicate, so the numbered formulas should be direct recalls of the owner fields, with only the
degree-zero evaluation on an element kept as a thin bridge/view companion.
-/

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {δ : DeRhamFamily R S Ω[S⁄R]}

/-
17.30.1.1 in degree `0`: the de Rham differential on `0`-forms is exactly the owner field
`IsExteriorPowerDeRhamDifferential.degree_zero`.
-/
recall IsExteriorPowerDeRhamDifferential.degree_zero

-- Evaluating the recalled degree-zero owner equality on an element gives the source-facing formula
-- `d(b₀) = db₀`.
example
    (hd : IsExteriorPowerDeRhamDifferential (KaehlerDifferential.D R S) δ)
    (b₀ : S) :
    δ 0 b₀ = KaehlerDifferential.D R S b₀ :=
  LinearMap.congr_fun hd.degree_zero b₀

/-
17.30.1.1 in degree `1`: the de Rham differential of the exact `1`-form `b₀ \, db₁` is the
two-fold wedge `db₀ ∧ db₁`. This is exactly the owner field
`IsExteriorPowerDeRhamDifferential.degree_one`.
-/
recall IsExteriorPowerDeRhamDifferential.degree_one

/-
17.30.1.1 in higher degree: the de Rham differential of the exact `(p + 2)`-form
`b₀ \, db₁ ∧ \cdots ∧ db_{p + 2}` is obtained by adjoining `db₀` on the left. This is exactly
the owner field `IsExteriorPowerDeRhamDifferential.higher`.
-/
recall IsExteriorPowerDeRhamDifferential.higher

end
