import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksProject_2024.stacks_project.Chap24.Definition_24_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Semantic recall:
`lean_leansearch` surfaced the canonical scheme-morphism owner `AlgebraicGeometry.IsProper` and
the absolute `AlgebraicGeometry.Proj` owner. Local Chapter 31 precedent currently represents
relative `Proj` through `RelativeProjPresentation`, and Chapter 29 represents locally projective
morphisms through `LocallyProjective`; however those owner files are not dependency-closed in the
current Lake target. The checks below keep this item attached to the stable graded-algebra and
properness surfaces without introducing a duplicate relative-`Proj` or locally-projective owner.
-/

/- Lemma 31.30.4 (Stacks tag `0800`): let `S` be a scheme, let `\mathcal A` be a quasi-coherent
graded `\mathcal O_S`-algebra, and let
`p : X = \underline{\mathrm{Proj}}_S(\mathcal A) ⟶ S` be the relative `Proj` morphism. The
condition that `\mathcal A_0` is a finite type `\mathcal O_S`-module and `\mathcal A` is finite
type as an `\mathcal A_0`-algebra is equivalent to the condition that `\mathcal A_0` is a finite
type `\mathcal O_S`-module and `\mathcal A` is finite type as an `\mathcal O_S`-algebra`. If
these conditions hold, then `p` is locally projective and in particular proper.

The intended source-facing declaration should be restored against the relative-`Proj` and
locally-projective owners once their dependency closure elaborates. -/
#check fun {S : Scheme.{u}} (𝒜 : GradedAlgebraSheaf.{u, u} S.sheaf) ↦ (𝒜 0).IsFiniteType

#check fun {S X : Scheme.{u}} (p : X ⟶ S) ↦ IsProper p

#check fun {S X : Scheme.{u}} (p : X ⟶ S) ↦ LocallyOfFiniteType p

end AlgebraicGeometry.Scheme.Hom
