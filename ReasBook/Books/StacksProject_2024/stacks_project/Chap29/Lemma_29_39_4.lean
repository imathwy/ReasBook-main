import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-
Semantic recall / owner check:
- `lean_leansearch` recalled the canonical finite-type morphism predicate
  `LocallyOfFiniteType`; the project-local finite-type owner is `Scheme.Hom.FiniteType`.
- The current Chapter 29 relative-ampleness/projective-space owners needed for the full theorem,
  `RelativelyAmple`, `RelativelyVeryAmple`, and `ProjectiveSpaceOver`, are not
  dependency-closed in this item environment because importing `Definition_29_37_1.lean` fails
  before this target elaborates.
- The Stacks tag evidence is consistent: item tag `01VT` and source URL
  `https://stacks.math.columbia.edu/tag/01VT`.
-/

/- Lemma 29.39.4 (Stacks tag `01VT`): let `f : X ⟶ S` be a morphism of schemes, let
`\mathcal L` be an invertible `\mathcal O_X`-module, assume `S` is affine and `f` is of finite
type. The following are equivalent: `\mathcal L` is ample on `X`; `\mathcal L` is `f`-ample;
`\mathcal L^{\otimes d}` is `f`-very ample for some `d ≥ 1`;
`\mathcal L^{\otimes d}` is `f`-very ample for all `d ≫ 1`; for some `d ≥ 1` there exist
`n ≥ 1` and an immersion `i : X ⟶ \mathbf P^n_S` such that
`\mathcal L^{\otimes d} ≅ i^*\mathcal O_{\mathbf P^n_S}(1)`; and for all `d ≫ 1` there exist
`n ≥ 1` and such an immersion presentation.

When the Chapter 28/29 ampleness owners are dependency-closed, the intended source-facing
statement is a `List.TFAE` theorem over the six clauses using `Scheme.Modules.IsAmple L`,
`RelativelyAmple f L`, `RelativelyVeryAmple f (hL d)`, and the `ProjectiveSpaceOver S n`
tautological sheaf presentation from Lemma 29.39.1.
-/
#check List.TFAE
#check fun {X S : Scheme.{u}} (f : X ⟶ S) ↦ LocallyOfFiniteType f
#check fun {S : Scheme.{u}} ↦ IsAffine S
#check fun {X S : Scheme.{u}} (i : X ⟶ S) ↦ IsImmersion i

end AlgebraicGeometry
