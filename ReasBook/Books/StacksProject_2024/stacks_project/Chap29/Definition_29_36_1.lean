import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owner `AlgebraicGeometry.IsEtale`;
- it also recalled the affine-chart owners `Algebra.IsStandardEtale` and
  `StandardEtalePresentation`, matching the ring-level dependency Definition `10.144.1`.
-/

/- Definition 29.36.1 (1)-(2): the textbook local/global notion of an étale morphism of schemes is
the canonical morphism property `AlgebraicGeometry.IsEtale`. This owner is packaged by affine open
neighborhoods around each point whose induced `Scheme.Hom.appLE` ring map is standard étale, so it
captures both “étale at `x`” and “étale at every point”. -/
recall AlgebraicGeometry.IsEtale

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Definition 29.36.1 (1): a morphism of schemes is étale at `x` if its pullback along
`Spec(𝒪_{X, x}) ⟶ X` is étale. -/
@[stacks 02GI]
def Scheme.Hom.EtaleAt (f : X ⟶ S) (x : X) : Prop :=
  Etale (X.fromSpecStalk x ≫ f)

/-- Unfolding lemma for `Scheme.Hom.EtaleAt`. -/
@[stacks 02GI, simp] theorem Scheme.Hom.etaleAt_iff (f : X ⟶ S) (x : X) :
    f.EtaleAt x ↔ Etale (X.fromSpecStalk x ≫ f) :=
  Iff.rfl

namespace Scheme.Hom

/-- Definition 29.36.1 (2): a morphism of schemes is étale if and only if it is étale at every
point of its source. -/
@[stacks 02GI]
theorem etale_iff_forall_etaleAt (f : X ⟶ S) :
    Etale f ↔ ∀ x : X, f.EtaleAt x := by
  sorry

end Scheme.Hom

/- Definition 29.36.1 (3): for affine schemes `X ≅ Spec A` and `S ≅ Spec R`, the textbook notion
that `X ⟶ S` is standard étale is controlled on coordinates by `Algebra.IsStandardEtale R A`. -/
recall Algebra.IsStandardEtale

/- The bridge from the explicit presentation `Spec (R[x]_h/(g)) → Spec R` in Definition
29.36.1 (3) to the intrinsic affine-ring owner is `StandardEtalePresentation R A`. -/
recall StandardEtalePresentation

end AlgebraicGeometry
