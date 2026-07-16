import Mathlib
import stacks_proof.stacks_project.Chap14.Example_14_33_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CommRingCat
open Under
open scoped IteratedEndofunctor

universe u

noncomputable section

namespace CategoryTheory

variable (A : CommRingCat.{u})

set_option quotPrecheck false in
local notation "T" => (CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.toFunctor
set_option quotPrecheck false in
local notation "ε" => (CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.ε
set_option quotPrecheck false in
local notation "δ" => (CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.δ
set_option quotPrecheck false in
local notation "Tobj(" B ")" =>
  ((CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.toFunctor).obj B
set_option quotPrecheck false in
local notation "η(" X ")" => ((CommRingCat.adj.comp (Under.costarAdjForget A)).unit).app X
set_option quotPrecheck false in
local notation "ε_(" B ")" => ((CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.ε).app B

/- Domain-style sampling for Example 14.34.7:
- primary domain: the comonad on `Under A` induced by the free `A`-algebra adjunction on
  underlying sets, together with the canonical iterated face/degeneracy maps attached to that
  comonad;
- sampled same-kind declarations:
  `CommRingCat.adj`,
  `Under.costarAdjForget`,
  `iteratedFaceMap`,
  `iteratedDegeneracyMap`,
  `d[Y, d]⦅n, j⦆`,
  `s[Y, s]⦅n, j⦆`;
- best owner abstraction: the canonical owner is the composed adjunction
  `CommRingCat.adj.comp (Under.costarAdjForget A)` and its induced comonad on `Under A`,
  accessed directly through the chapter face/degeneracy owners;
- primitive data: the composed adjunction `CommRingCat.adj.comp (Under.costarAdjForget A)`, its
  left adjoint `CommRingCat.free ⋙ Under.costar A`, and the induced comonad data;
- derived API: the four degree-`1` formulas on the canonical bracket generators supplied by the
  adjunction unit.

Source/core/bridge triage:
- `source-facing`: the bracket-generator formulas for the degree-`1` face and degeneracy maps of
  the polynomial `A`-algebra resolution;
- `core/canonical`: `CommRingCat.free`, `CommRingCat.adj`, `Under.costar`, the composed
  adjunction `CommRingCat.adj.comp (Under.costarAdjForget A)`, its induced comonad owner surface,
  and the chapter owners `iteratedFaceMap` and `iteratedDegeneracyMap`;
- `bridge/view`: the source formulas themselves, obtained by evaluating the canonical unit and
  simplicial operators in the `Under A` realization. -/

/-- Helper for Example 14.34.7: the comultiplication of the polynomial-algebra resolution is the
functorial image of the adjunction unit. -/
lemma polynomialAlgebraResolutionComultiplication_app_eq_map_unit
    (B : Under A) :
    ((CommRingCat.adj.comp (Under.costarAdjForget A)).toComonad.δ).app B =
      (CommRingCat.free ⋙ Under.costar A).map (η(B.right)) := by
  -- Normalize the comultiplication to the canonical formula for the comonad of a composed
  -- adjunction.
  rfl

/-- Helper for Example 14.34.7: forgetting the right triangle identity for
`Under.costarAdjForget A` gives the expected equality of ring maps on the right components. -/
lemma costarAdjForget_right_triangle_right
    (B : Under A) :
    (Under.costarAdjForget A).unit.app B.right ≫
      ((Under.costarAdjForget A).counit.app B).right =
        𝟙 B.right := by
  -- This is exactly the right triangle identity after forgetting from `Under A`.
  simpa using (Under.costarAdjForget A).right_triangle_components B

/-- Helper for Example 14.34.7: the left triangle identity for `Under.costarAdjForget A`
specialized to right components. -/
lemma costarAdjForget_left_triangle_right
    (R : CommRingCat) :
    (((Under.costar A).map ((Under.costarAdjForget A).unit.app R)) ≫
        (Under.costarAdjForget A).counit.app ((Under.costar A).obj R)).right =
      𝟙 ((Under.costar A).obj R).right := by
  -- This is the left triangle identity projected to the underlying ring morphisms.
  simpa using congrArg (fun f => f.right) ((Under.costarAdjForget A).left_triangle_components R)

/-- Helper for Example 14.34.7: functoriality of the polynomial-algebra resolution sends a
bracket generator `[x]` to the bracket generator `[f(x)]`. -/
lemma polynomialAlgebraResolution_map_apply_bracket
    {X Y : Type u} (f : X → Y) (x : X) :
    (((CommRingCat.free ⋙ Under.costar A).map f).right) (η(X) x) =
      η(Y) (f x) := by
  -- The bracket generator map is the unit of the composed adjunction, so its naturality gives the
  -- desired compatibility with `f`.
  simpa using congrFun ((CommRingCat.adj.comp (Under.costarAdjForget A)).unit.naturality f).symm x

-- Proof sketch: unfold `d^⦅0, (1 : Fin 2)⦆.app B`; it is the outer counit map for the comonad
-- on `Under A`, so on the bracket generator `[x] ∈ A[A[B]]` it simply removes the outer bracket.
/-- Example 14.34.7 (1): for `x ∈ A[B]`, the face map `d₀` sends the bracket generator
`[x] ∈ A[A[B]]` to `x`. -/
@[stacks 09CB]
theorem polynomialAlgebraResolutionD0_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((d[T, ε]⦅0, (1 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      x :=
  by
  have hLast : (1 : Fin 2) = Fin.last 1 := rfl
  -- The last degree-`1` face is the comonad counit evaluated at `T(B)`.
  rw [hLast]
  rw [iteratedFaceMap, Fin.lastCases_last, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app]
  -- Now specialize the right triangle identity of the composed adjunction to the underlying
  -- element `x`.
  simpa using congrFun
    ((CommRingCat.adj.comp (Under.costarAdjForget A)).right_triangle_components (Tobj(B))) x

-- Proof sketch: unfold `d^⦅0, (0 : Fin 2)⦆.app B`; it applies the counit to the inner copy
-- before reintroducing the outer bracket via the adjunction unit.
/-- Example 14.34.7 (2): for `x ∈ A[B]`, the face map `d₁` sends `[x]` to `[ε(x)]`. -/
@[stacks 09CB]
theorem polynomialAlgebraResolutionD1_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((d[T, ε]⦅0, (0 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η(B.right)) ((ε_(B)).right x) :=
  by
  have hZero : (0 : Fin 2) = Fin.castSucc 0 := rfl
  -- The first degree-`1` face is the polynomial functor applied to the counit `ε_B`.
  rw [hZero]
  rw [iteratedFaceMap, Fin.lastCases_castSucc, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app]
  -- Naturality of the bracket-generator map identifies the image with `[ε(x)]`.
  simpa using
    polynomialAlgebraResolution_map_apply_bracket (A := A) ((ε_(B)).right) x

-- Proof sketch: unfold `s^⦅1, (1 : Fin 2)⦆.app B`; it inserts the comultiplication in the outer
-- copy, so the bracket generator `[x]` becomes the doubly bracketed element `[[x]]`.
/-- Example 14.34.7 (3): for `x ∈ A[B]`, the degeneracy map `s₀` sends `[x]` to `[[x]]`. -/
@[stacks 09CB]
theorem polynomialAlgebraResolutionS0_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((s[T, δ]⦅1, (1 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η((Tobj(Tobj(B))).right)) (η((Tobj(B)).right) x) :=
  by
  have hLast : (1 : Fin 2) = Fin.last 1 := rfl
  -- The last degree-`1` degeneracy is the comultiplication evaluated at `T(B)`.
  rw [hLast]
  rw [iteratedDegeneracyMap, Fin.lastCases_last, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app]
  rw [polynomialAlgebraResolutionComultiplication_app_eq_map_unit]
  -- The comultiplication is `map η`, so it adds one more outer bracket to `[x]`.
  simpa using
    polynomialAlgebraResolution_map_apply_bracket (A := A) (η((Tobj(B)).right)) x

-- Proof sketch: unfold `s^⦅1, (0 : Fin 2)⦆.app B`; it inserts the comultiplication in the inner
-- copy, which applies the polynomial functor to the bracket map `η.app B.right` before taking one
-- more outer bracket.
/-- Example 14.34.7 (4): for `x ∈ A[B]`, the degeneracy map `s₁` sends `[x]` to `[A[η](x)]`. -/
@[stacks 09CB]
theorem polynomialAlgebraResolutionS1_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((s[T, δ]⦅1, (0 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η((Tobj(Tobj(B))).right))
        ((((CommRingCat.free ⋙ Under.costar A).map (η(B.right))).right) x) :=
  by
  have hZero : (0 : Fin 2) = Fin.castSucc 0 := rfl
  -- The first degree-`1` degeneracy is the polynomial functor applied to `δ_B`.
  rw [hZero]
  rw [iteratedDegeneracyMap, Fin.lastCases_castSucc, Functor.whiskerRight_app]
  rw [iteratedDegeneracyMap]
  rw [polynomialAlgebraResolutionComultiplication_app_eq_map_unit]
  -- Naturality of the bracket-generator map then identifies the result with `[A[η](x)]`.
  simpa using
    polynomialAlgebraResolution_map_apply_bracket (A := A)
      ((((CommRingCat.free ⋙ Under.costar A).map (η(B.right))).right)) x

end CategoryTheory
