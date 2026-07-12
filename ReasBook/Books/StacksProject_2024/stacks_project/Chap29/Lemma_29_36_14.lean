import Mathlib
import StacksProject_2024.Chap29.Lemma_29_36_5

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

namespace Scheme.Hom

/-- The affine-coordinate map induced by `f` from `U` to the fixed affine target neighborhood
`V` is standard étale. -/
def IsStandardEtaleOver (f : X ⟶ S) (V : S.affineOpens) (U : X.affineOpens) : Prop :=
  ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
    letI : Algebra Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) :=
      (f.appLE (V : S.Opens) (U : X.Opens) e).hom.toAlgebra
    Algebra.IsStandardEtale Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens))

/-- Unfolding lemma for `f.IsStandardEtaleOver V U`. -/
theorem isStandardEtaleOver_iff
    (f : X ⟶ S) (V : S.affineOpens) (U : X.affineOpens) :
    f.IsStandardEtaleOver V U ↔
      ∃ e : (U : X.Opens) ≤ f ⁻¹ᵁ (V : S.Opens),
        letI : Algebra Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) :=
          (f.appLE (V : S.Opens) (U : X.Opens) e).hom.toAlgebra
        Algebra.IsStandardEtale Γ(S, (V : S.Opens)) Γ(X, (U : X.Opens)) :=
  Iff.rfl

end Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the scheme-side owner `AlgebraicGeometry.IsEtale`;
- direct mathlib source inspection in `Morphisms/Etale` verified that `Etale` is defined via affine
  `appLE` maps whose ring homs are étale;
- `Morphisms/Smooth` provides the analogous neighborhood theorem
  `Smooth.iff_forall_exists_isStandardSmooth`, so this item is stated as the étale-at-a-point
  specialization with a fixed affine target neighborhood.
-/

/-- Lemma 29.36.14: for a fixed affine open neighborhood `V` of `f x`, the morphism `f` is étale
at `x` if and only if there exists an affine open neighborhood `U` of `x` mapping into `V` such
that the induced affine-coordinate ring map is standard étale. -/
@[stacks 02GT]
theorem etaleAt_iff_exists_affineOpen_over_isStandardEtale
    (x : X) (V : S.affineOpens) (hxV : f x ∈ (V : S.Opens)) :
    f.EtaleAt x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        f.IsStandardEtaleOver V U := sorry

end AlgebraicGeometry
