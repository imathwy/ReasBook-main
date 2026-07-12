import Mathlib
import StacksProject_2024.Chap29.Lemma_29_35_10

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owner `FormallyUnramified`;
- local Chapter 29 precedent already provides the source-facing owners `Unramified`,
  `GUnramified`, and `Scheme.Hom.UnramifiedAt`.
-/

/- Definition 29.35.1 (1), (3), and (4): the existing source-facing scheme predicates are
`Scheme.Hom.UnramifiedAt`, `Unramified`, and `GUnramified`. -/
recall Scheme.Hom.UnramifiedAt
recall Unramified
recall GUnramified

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Definition 29.35.1: a morphism of schemes is G-unramified at `x` if its pullback along
`Spec(𝒪_{X, x}) ⟶ X` is G-unramified. -/
@[stacks 02G4]
def Scheme.Hom.GUnramifiedAt (f : X ⟶ S) (x : X) : Prop :=
  GUnramified (X.fromSpecStalk x ≫ f)

/-- Unfolding lemma for `Scheme.Hom.GUnramifiedAt`. -/
@[simp] theorem Scheme.Hom.gUnramifiedAt_iff (f : X ⟶ S) (x : X) :
    f.GUnramifiedAt x ↔ GUnramified (X.fromSpecStalk x ≫ f) :=
  Iff.rfl

end AlgebraicGeometry
