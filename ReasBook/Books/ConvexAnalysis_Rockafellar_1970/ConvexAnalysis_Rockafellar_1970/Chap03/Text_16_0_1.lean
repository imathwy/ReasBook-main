import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.0.1 records four standard transformation rules for Fenchel conjugates
  and support functions under translation, addition of a linear form, and addition of a constant.
- `core/canonical`: the owner declarations already present earlier in the chapter are
  `convexConjugate_affineChange`,
  `supportFunction_set_add_apply`, and `supportFunction_def`.
- `bridge/view`: each displayed source formula is a thin specialization of those owners, so this
  file keeps the four source-facing formulas explicitly while deriving them directly from the
  upstream owner API instead of introducing a second owner layer.

Domain-style sampling used here:
- `convexConjugate_affineChange`;
- `supportFunction_set_add_apply`;
- `supportFunction_def`.

Primitive data vs derived API:
- primitive owner data is already upstream: the affine-change owners for Fenchel conjugates and
  the pointwise Minkowski-sum support-function theorem;
- derived source-facing API: the direct translation formula, the pure linear-form specialization,
  the pure constant specialization, and the singleton-translation specialization.

Layer target: `bridge/view`.
-/

section Conjugate

variable {α : Type*} [AddCommGroup α]
variable {X : Type*} {Y : Type*}
variable [AddCommGroup X] [AddCommGroup Y]
variable [HasPairing X Y (WithTopBot α)]
variable [HasPairingAddLeft X Y (WithTopBot α)]
variable [HasPairingSubRight X Y (WithTopBot α)]
variable [SupSet (WithTopBot α)]

-- Proof sketch: specialize the chapter affine-change owner with both bijections equal to
-- the identity, zero linear perturbation, and zero constant term.
/-- Text 16.0.1 (1): translating the argument of `h` by `a` adds the linear form
`x⋆ ↦ ⟪a, x⋆⟫` to the conjugate. -/
theorem convexConjugate_translate
    (h : X → WithTopBot α) (a : X) :
    (fun x ↦ h (x - a))⋆ =
      fun xStar : Y ↦ h⋆ xStar + ⟪a, xStar⟫ₚ := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) a (0 : Y) (0 : WithTopBot α))

-- Proof sketch: specialize the same affine-change owner to zero translation and zero constant.
/-- Text 16.0.1 (2): adding the pairing form `x ↦ ⟪x, a⋆⟫ₚ` shifts the dual variable by `-a⋆`. -/
theorem convexConjugate_add_inner
    [HasPairingZeroLeft X Y (WithTopBot α)]
    (h : X → WithTopBot α) (aStar : Y) :
    (fun x ↦ h x + ⟪x, aStar⟫ₚ)⋆ = fun xStar ↦ h⋆ (xStar - aStar) := by
  simpa [pairing_zero_left, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) (0 : X) aStar (0 : WithTopBot α))

-- Proof sketch: specialize the same affine-change owner to zero translation and zero pairing
-- perturbation.
/-- Text 16.0.1 (3): adding the constant `α` subtracts the same constant from the conjugate. -/
theorem convexConjugate_add_const
    [HasPairingZeroLeft X Y (WithTopBot α)]
    (h : X → WithTopBot α) (β : WithTopBot α) :
    (fun x ↦ h x + β : X → WithTopBot α)⋆ = fun xStar : Y ↦ h⋆ xStar - β := by
  simpa [pairing_zero_left, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (convexConjugate_affineChange h (Equiv.refl X)
      (Equiv.refl Y) (fun x xStar ↦ rfl) (0 : X) (0 : Y) β)

end Conjugate

section SupportFunction

variable {𝕜 : Type*} [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsOrderedAddMonoid 𝕜] [DenselyOrdered 𝕜]
variable {X : Type*} {Y : Type*}
variable [Add Y] [HasPairing X Y 𝕜] [HasPairingAddRight X Y 𝕜]

-- Proof sketch: apply the owner Minkowski-sum theorem `supportFunction_set_add` with the
-- singleton `{a}` and rewrite the resulting singleton support value by
-- `supportFunction_singleton`.
/-- Text 16.0.1 (4), owner form: translating a set by `a` adds the linear form
`x⋆ ↦ ⟪x⋆, a⟫ₚ` to its support function. -/
theorem supportFunction_translate_set
    (C : Set Y) (a : Y) :
    (δᵛ(· | C + ({a} : Set Y)) : X → WithTopBot 𝕜) =
      fun xStar ↦ δᵛ(xStar | C) + (⟪xStar, a⟫ₚ : WithTopBot 𝕜) := by
  funext xStar
  simpa [supportFunction_singleton] using
    (supportFunction_set_add_apply C ({a} : Set Y) xStar)

/-- Text 16.0.1 (4), pointwise form: evaluating the translated support function at `x⋆` adds the
linear term `⟪x⋆, a⟫ₚ`. -/
theorem supportFunction_translate_set_apply
    (C : Set Y) (a : Y) (xStar : X) :
    (δᵛ(xStar | C + ({a} : Set Y)) : WithTopBot 𝕜) =
      δᵛ(xStar | C) + (⟪xStar, a⟫ₚ : WithTopBot 𝕜) := by
  simpa using congrFun (supportFunction_translate_set C a) xStar

end SupportFunction
