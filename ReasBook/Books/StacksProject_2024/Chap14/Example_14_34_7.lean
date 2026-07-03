import Mathlib
import StacksProject_2024.Chap14.Example_14_33_1

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

-- Proof sketch: unfold `d^⦅0, (1 : Fin 2)⦆.app B`; it is the outer counit map for the comonad
-- on `Under A`, so on the bracket generator `[x] ∈ A[A[B]]` it simply removes the outer bracket.
/-- Example 14.34.7 (1): for `x ∈ A[B]`, the face map `d₀` sends the bracket generator
`[x] ∈ A[A[B]]` to `x`. -/
theorem polynomialAlgebraResolutionD0_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((d[T, ε]⦅0, (1 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      x :=
  sorry

-- Proof sketch: unfold `d^⦅0, (0 : Fin 2)⦆.app B`; it applies the counit to the inner copy
-- before reintroducing the outer bracket via the adjunction unit.
/-- Example 14.34.7 (2): for `x ∈ A[B]`, the face map `d₁` sends `[x]` to `[ε(x)]`. -/
theorem polynomialAlgebraResolutionD1_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((d[T, ε]⦅0, (0 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η(B.right)) ((ε_(B)).right x) :=
  sorry

-- Proof sketch: unfold `s^⦅1, (1 : Fin 2)⦆.app B`; it inserts the comultiplication in the outer
-- copy, so the bracket generator `[x]` becomes the doubly bracketed element `[[x]]`.
/-- Example 14.34.7 (3): for `x ∈ A[B]`, the degeneracy map `s₀` sends `[x]` to `[[x]]`. -/
theorem polynomialAlgebraResolutionS0_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((s[T, δ]⦅1, (1 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η((Tobj(Tobj(B))).right)) (η((Tobj(B)).right) x) :=
  sorry

-- Proof sketch: unfold `s^⦅1, (0 : Fin 2)⦆.app B`; it inserts the comultiplication in the inner
-- copy, which applies the polynomial functor to the bracket map `η.app B.right` before taking one
-- more outer bracket.
/-- Example 14.34.7 (4): for `x ∈ A[B]`, the degeneracy map `s₁` sends `[x]` to `[A[η](x)]`. -/
theorem polynomialAlgebraResolutionS1_apply_bracket
    (B : Under A)
    (x : (Tobj(B)).right) :
    ((s[T, δ]⦅1, (0 : Fin 2)⦆).app B).right
      (η((Tobj(B)).right) x) =
      (η((Tobj(Tobj(B))).right))
        ((((CommRingCat.free ⋙ Under.costar A).map (η(B.right))).right) x) :=
  sorry

end CategoryTheory
