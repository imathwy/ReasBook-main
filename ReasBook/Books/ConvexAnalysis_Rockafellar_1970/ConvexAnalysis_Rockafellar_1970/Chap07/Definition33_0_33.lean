import ConvexAnalysis_Rockafellar_1970.Chap01.HasPairing

universe u v w z

open scoped Rockafellar

namespace Bifunction

section

variable {U : Type u} {X : Type v} {XStar : Type w} {L : Type z}
variable [HAdd U U U] [HSub L L L] [HasPairing X XStar L]

/-!
Source/core/bridge triage:

- `source-facing`: Definition33.0.33 introduces the auxiliary bifunction `H` attached to a
  bifunction `F`, a base point `u`, and a dual vector `x⋆`.
- `core/canonical`: the owner object is still an ordinary bifunction `U → X → L`; there is no
  earlier chapter owner with this exact interface, so the source-facing translated kernel remains
  the right public declaration here. The definition only translates the first argument and
  subtracts the canonical pairing in the second argument.
- `bridge/view`: later convexity or closedness statements about `H` should be stated as separate
  theorems on this concrete bifunction, not bundled into the definition itself.

Domain-style sampling used here:
- `Bifunction.perturbationFunction` from Chapter 6 for the owner shape `U → X → L`;
- `translatedDefectFunction` from `Chap05.Proposition_23_6_1` for the source-facing
  translate-and-subtract pattern on one-variable functions;
- `convexConjugate_translate_sub_pairing` from `Chap06.Remark_31_4_3` for the canonical
  translate-minus-pairing duality bridge built on the same primitive pairing data;
- the pairing owner `HasPairing X XStar L` from `Chap01.HasPairing`, reused directly with the
  minimal subtraction owner `HSub L L L` on the same codomain layer.

Primitive data vs derived API:
- primitive data: `F`, `u`, and `xStar`;
- primitive source-defined object: the translated pairing perturbation below;
- derived API: the pointwise evaluation theorem.

Layer target: `source-facing`.
-/

/-- Definition33.0.33: the bifunction `translatedSubPairing F u xStar`, i.e. Rockafellar's `H`,
is defined by `H(v, y) = F(u + v, y) - ⟪y, xStar⟫ₚ`. -/
def translatedSubPairing (F : U → X → L) (u : U) (xStar : XStar) : U → X → L :=
  fun v y ↦ F (u + v) y - ⟪y, xStar⟫ₚ

/- Rockafellar's source-facing kernel notation for Definition 33.0.33. -/
scoped[Rockafellar] notation "H[" F " | " u ", " xStar "]" =>
  Bifunction.translatedSubPairing F u xStar

/-- The translated pairing perturbation is exactly the bifunction sending `(v, y)` to
`F (u + v) y - ⟪y, xStar⟫ₚ`, on the source-facing `H[· | ·, ·]` surface. -/
theorem translatedSubPairing_eq
    (F : U → X → L) (u : U) (xStar : XStar) :
    H[F | u, xStar] = fun v y ↦ F (u + v) y - ⟪y, xStar⟫ₚ := rfl

/-- Uncurried form of the translated pairing perturbation. -/
@[simp] theorem uncurry_translatedSubPairing
    (F : U → X → L) (u : U) (xStar : XStar) :
    Function.uncurry (H[F | u, xStar]) =
      fun p : U × X ↦ F (u + p.1) p.2 - ⟪p.2, xStar⟫ₚ := rfl

/-- Evaluating the translated pairing perturbation gives the defining formula
`F(u + v, y) - ⟪y, xStar⟫ₚ`. -/
@[simp] theorem translatedSubPairing_apply
    (F : U → X → L) (u : U) (xStar : XStar) (v : U) (y : X) :
    H[F | u, xStar] v y = F (u + v) y - ⟪y, xStar⟫ₚ := rfl

end

end Bifunction
