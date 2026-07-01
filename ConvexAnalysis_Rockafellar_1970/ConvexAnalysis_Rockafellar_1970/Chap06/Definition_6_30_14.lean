import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_12

noncomputable section

open scoped Rockafellar

universe u v u' v' w

namespace Bifunction

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg UStar]
variable [HasPairing (U × X) (UStar × XStar) L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition 6.30.14 introduces the adjoint bifunction associated to a bifunction
  `F`, with sign convention `F⋆(x⋆, u⋆) = - (uncurry F)⋆(-u⋆, x⋆)`.
- `core/canonical`: conjugation is already owned by `convexConjugate` (`(·)⋆`) at the pairing
  layer, so the primitive owner here should be this thin sign/currying bridge on the same codomain
  layer rather than a separate `WithBotTop`-specific package.
- `bridge/view`: the source writes the adjoint itself as `F⋆` and its biadjoint as `F⋆⋆`, so the
  public surface here exposes those scoped postfix notations. The raw owner remains the explicit
  map `adjoint F` because the dual parameters are not recoverable from `F` alone. Any
  swapped operational view is the canonical `Function.swap (F⋆)`, not a second bifunction owner.

Domain-style sampling used here:
- `convexConjugate` / `(·)⋆` from `Chap03.Defn_12_2`;
- product pairing owner from `Chap01.HasPairing`;
- `(·)₀` from `Chap06.Definition_6_29_12`.

Primitive data vs derived API:
- primitive data: a bifunction `F : U → X → L`;
- primitive owner: `adjoint F : XStar → UStar → L`;
- derived API: the optional scoped source-facing notations `F⋆` and `F⋆⋆` when the ambient dual
  parameters are already determined, together with the immediate pointwise and zero-slice
  simplification theorems stated on the explicit owner `adjoint F`, since the
  dual parameters are not recoverable from `F` alone.

Layer target: `source-facing` on the pairing-based codomain owner layer, avoiding an unnecessary
specialization to `WithBotTop α`, `EReal`, or inner-product self-duality.
-/

/-- Definition 6.30.14: the adjoint bifunction attached to `F`, expressed canonically as a
sign/currying bridge from the conjugate of `Function.uncurry F`. -/
def adjoint (F : U → X → L) : XStar → UStar → L :=
  fun xStar uStar ↦ - (Function.uncurry F)⋆ (-uStar, xStar)

end

end Bifunction

namespace Rockafellar

/- Rockafellar's optional adjoint-bifunction notation. In `open scoped Rockafellar`, a bifunction
term `F` may be written as `F⋆`, and when both adjoint pairings are in scope its biadjoint may be
written as `F⋆⋆`, when local type information already determines the dual ambient types. The
explicit owner remains `Bifunction.adjoint F`, and the self-dual biconjugate surface
is `(F⋆⋆ : U → X → L)` when that type ascription is needed for disambiguation. -/
scoped[Rockafellar] postfix:max "⋆" => fun F ↦ Bifunction.adjoint F
scoped[Rockafellar] postfix:max "⋆⋆" =>
  fun F ↦ Bifunction.adjoint (Bifunction.adjoint F)
scoped[Rockafellar] notation:max "adjoint " XStar " " UStar " " F =>
  (Bifunction.adjoint (XStar := XStar) (UStar := UStar) F)

end Rockafellar

namespace Bifunction

open scoped Rockafellar

section

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L]
variable [Neg UStar]
variable [HasPairing (U × X) (UStar × XStar) L]

/-- Evaluating the adjoint bifunction gives the defining conjugate formula. -/
@[simp] theorem adjoint_apply
    (F : U → X → L) (xStar : XStar) (uStar : UStar) :
    F⋆ xStar uStar = - ((Function.uncurry F)⋆ (-uStar, xStar)) :=
  rfl

section

variable [Zero XStar]

-- Proof sketch: evaluate the zero slice of `F⋆` at `u⋆`, then unfold `adjoint`.
/-- Evaluating the dual zero-slice objective `(F⋆)₀` at `u⋆` gives the source formula
`- (uncurry F)⋆ (-u⋆, 0)`. -/
@[simp] theorem objective_adjoint_apply
    (F : U → X → L) (uStar : UStar) :
    ((adjoint XStar UStar F)₀ uStar) =
      - ((Function.uncurry F)⋆ (-uStar, (0 : XStar))) := by
  rfl

end

end

end Bifunction
