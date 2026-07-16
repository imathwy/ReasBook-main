import Mathlib.Tactic.Recall
import StacksProject_2024.stacks_project.Chap22.Situation_22_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open DifferentialGradedCategory

universe u v w

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [D : DifferentialGradedCategory.{u, v, w} R A]
variable [HasShift (Comp R A) ℤ]
variable [HasAdmissibleCones R A]

-- Semantic recall hit: the source-facing owner for Situation `22.27.2` is
-- `HasAdmissibleCones.admissibleCone`, and the situation-level companion API
-- `HasAdmissibleCones.shortComplex`, `HasAdmissibleCones.splitting`, and
-- `HasAdmissibleCones.boundary_eq` already exposes the chosen cone triangle without forcing
-- downstream code to project through a fixed `AdmissibleCone f`.

/- Source/core/bridge triage for Lemma 22.27.10:
- `source-facing`: in Situation `22.27.2`, every morphism `f : x ⟶ y` in `Comp(𝒜)` is assigned an
  associated triangle `(y, c(f), x[1], i, p, f[1])`;
- `core/canonical`: the situation-level field `HasAdmissibleCones.admissibleCone`;
- `bridge/view`: the fixed-morphism structure `AdmissibleCone f`, with the chosen triangle exposed
  through the situation-level companion API.
-/

/- Lemma 22.27.10: in Situation 22.27.2, the triangle
`(y, c(f), x[1], i, p, f[1])` attached to a morphism `f : x ⟶ y` in `Comp(𝒜)` is formalized in
the current repository by the situation-level choice
`HasAdmissibleCones.admissibleCone f : AdmissibleCone f`. -/
recall HasAdmissibleCones.admissibleCone

/- Companion recall: the chosen cone triangle yields the short complex `y ⟶ c(f) ⟶ x[1]`. -/
recall HasAdmissibleCones.shortComplex

/- Companion recall: the chosen short complex is split exact. -/
recall HasAdmissibleCones.splitting

/- Companion recall: the connecting morphism of the chosen associated triangle is `f[1]`. -/
recall HasAdmissibleCones.boundary_eq

end
