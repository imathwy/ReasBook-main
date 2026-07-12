import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import StacksProject_2024.Chap20.«20_11_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-
Source/core/bridge triage for Lemma 30.4.1:
- `source-facing`: the Stacks induction principle for properties of quasi-compact opens of a qcqs
  scheme, stated using affine opens and compact intersections;
- `core/canonical`: `AlgebraicGeometry.compact_open_induction_on`;
- `bridge/view`: the theorems below are the source-facing affine-open specialization of that
  canonical induction principle.
-/

-- Semantic recall: `lean_leansearch` found the canonical compact-open owner
-- `AlgebraicGeometry.compact_open_induction_on`. The statements here keep the Stacks hypotheses
-- explicit while presenting the property on quasi-compact opens in the canonical `X.Opens` plus
-- `IsCompact` shape, and affine opens through `X.affineOpens`.

section

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- Lemma 30.4.1 (Induction Principle): let `X` be a quasi-compact and quasi-separated scheme, and
let `P` be a property of the quasi-compact opens of `X`. If `P` holds for every affine open of
`X`, and whenever `U` is quasi-compact open and `V` is affine open, the assumptions that `P`
holds for `U`, `V`, and `U ∩ V` imply that `P` holds for `U ∪ V`, then `P` holds for every
quasi-compact open of `X`. -/
@[stacks 08DR]
theorem compactOpen_induction_principle
    (P : X.Opens → Prop)
    (h_affine : ∀ U : X.affineOpens, P U)
    (h_union :
      ∀ (U : X.Opens), IsCompact (U : Set X) → ∀ V : X.affineOpens,
        P U →
          P V →
            P (U ⊓ V) →
              P (U ⊔ V)) :
    ∀ (U : X.Opens), IsCompact (U : Set X) → P U := sorry

/-- Under the induction hypotheses of `compactOpen_induction_principle`, the property also holds
for the whole scheme `X`, viewed as the top open subset. -/
theorem compactOpen_induction_principle_top
    (P : X.Opens → Prop)
    (h_affine : ∀ U : X.affineOpens, P U)
    (h_union :
      ∀ (U : X.Opens), IsCompact (U : Set X) → ∀ V : X.affineOpens,
        P U →
          P V →
            P (U ⊓ V) →
              P (U ⊔ V)) :
    P (⊤ : X.Opens) := by
  exact compactOpen_induction_principle P h_affine h_union ⊤ (isCompact_univ : IsCompact (Set.univ : Set X))

end

end AlgebraicGeometry.Scheme
