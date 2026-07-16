import StacksProject_2024.stacks_project.Chap10.Definition_10_135_5
import StacksProject_2024.stacks_project.Chap29.Definition_29_21_1
import StacksProject_2024.stacks_project.Chap29.Definition_29_30_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open IsLocalRing

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` surfaced the scheme-morphism owners `AlgebraicGeometry.Flat` and
  `AlgebraicGeometry.IsSmooth`; local Chapter 29 precedent then fixed the pointwise owner choice
  against `FinitePresentationAt` from `Definition_29_21_1` and the global affine-neighborhood
  owner `LocallyOfType RingHom.Syntomic`;
- this file therefore keeps the source-facing pointwise syntomic predicate and packages the
  stalk/fiber criterion in the same owner style used elsewhere in Chapter 29.
-/

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The point `x` lies in the complete-intersection fiber locus of `f` when the closed fiber local
ring `𝒪_{X_{f(x)}, x}` is a complete intersection over `κ(f(x))`. -/
def closedFiberCompleteIntersectionAt (f : X ⟶ S) (x : X) : Prop :=
  let A := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let _ : Algebra A B := (f.stalkMap x).hom.toAlgebra
  Algebra.IsCompleteIntersectionOver (ResidueField A) (Ideal.Fiber (maximalIdeal A) B)

/-- The local stalk-flatness and closed-fiber complete-intersection condition at `x`. -/
private def flatStalkMapAndClosedFiberCompleteIntersectionAt
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) : Prop :=
  (f.stalkMap x).hom.Flat ∧ f.closedFiberCompleteIntersectionAt x

/-- Lemma 29.30.10 (1): fixing an affine open neighborhood `V` of `s = f(x)`, syntomicity at
`x` is equivalent to the existence of an affine neighborhood `U` of `x` mapping into `V` whose
induced affine chart ring map is syntomic. This is the pointwise source-facing version of the
project's affine-neighborhood owner for syntomic morphisms. -/
theorem syntomicAt_iff_exists_affine_chart_over
    (x : X) (V : S.affineOpens) (hsV : f x ∈ (V : S.Opens)) :
    SyntomicAt f x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : U ≤ f ⁻¹ᵁ V,
          RingHom.Syntomic (f.appLE V U e).hom := sorry

/-- Lemma 29.30.10 (2): a morphism of schemes is syntomic at `x` if and only if it is of finite
presentation at `x`, the induced local ring map `𝒪_{S, f(x)} → 𝒪_{X, x}` is flat, and the closed
fiber `𝒪_{X, x} / 𝔪_{f(x)} 𝒪_{X, x}` is a complete intersection over `κ(f(x))`. -/
theorem syntomicAt_iff_finitePresentationAt_and_flat_stalkMap_and_closedFiber_completeIntersection
    (x : X) :
    SyntomicAt f x ↔
      FinitePresentationAt f x ∧
        flatStalkMapAndClosedFiberCompleteIntersectionAt f x := sorry

end Scheme.Hom

end AlgebraicGeometry
