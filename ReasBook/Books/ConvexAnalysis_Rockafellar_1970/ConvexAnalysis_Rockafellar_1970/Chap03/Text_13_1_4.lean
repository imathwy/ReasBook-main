import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar
attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.1.4 identifies the Fenchel conjugate of the indicator `δ(· | C)` with
  the support function of `C`.
- `core/canonical`: the owner abstractions are `indicator`, `convexConjugate`,
  `supportFunction`, and the pairing-orientation bridge owner `HasPairingSwap`.
- `bridge/view`: Rockafellar's `δ(· | C)` is represented by `indicator C`, while the
  source's pointwise value `δ*(x⋆ | C)` is the evaluation of the owner equality at `xStar`.
- Primitive data vs derived API: the main declaration is the owner-level function equality at the
  pairing-swap layer, with pointwise formulas and symmetry-argument variants kept as thin bridges.

Domain-style sampling used here:
- `indicator`;
- `supportFunction` and `supportFunction_def`;
- `convexConjugate`;
- `HasPairingSwap`.
-/

section PairingSwap

variable {E : Type*} {EStar : Type*} {α : Type*}
variable [Add α] [Neg α] [Zero α] [ConditionallyCompleteLattice α]
variable [HasPairing E EStar α] [HasPairing EStar E α] [HasPairingSwap E EStar α]

-- Proof sketch: unfold `convexConjugate` at `indicator C`.
-- For `x ∈ C`, the indicator term is `0`, so the affine defect is `⟪x, xStar⟫`.
-- For `x ∉ C`, the
-- indicator term is `⊤`, so the defect is `⊥` and does not change the supremum. The remaining
-- supremum over `C` is exactly `supportFunction C xStar`, after swapping the pairing arguments
-- by the pairing-swap owner hypothesis.
/-- Text 13.1.4 at the pairing layer: if the two pairing orientations `(E, EStar)` and
`(EStar, E)` agree by `HasPairingSwap`, then the Fenchel conjugate of the indicator `δ(· | C)`
is the support function `δᵛ(· | C)`. -/
theorem convexConjugate_indicator_eq_supportFunction
    (C : Set E) :
    ((δ(· | C))⋆ : EStar → WithTopBot α) =
      (δᵛ(· | C) : EStar → WithTopBot α) := by
  classical
  funext xStar
  rw [convexConjugate_eq_iSup_pairing_sub]
  calc
    (⨆ x : E, (⟪x, xStar⟫ₚ - δ(x | C)))
        = ⨆ x : E, if x ∈ C then (⟪x, xStar⟫ₚ : WithTopBot α) else ⊥ := by
          congr with x
          by_cases hx : x ∈ C
          · simp [hx]
          · simp [hx]
    _ = ⨆ x ∈ C, ⟪x, xStar⟫ₚ := by
          apply le_antisymm
          · refine iSup_le fun x ↦ ?_
            by_cases hx : x ∈ C
            · exact le_iSup_of_le x <| le_iSup_of_le hx <| by simp [hx]
            · simp [hx]
          · refine iSup₂_le fun x hx ↦ ?_
            exact le_iSup_of_le x <| by simp [hx]
    _ = ⨆ x : C, ⟪(x : E), xStar⟫ₚ := by
          rw [← iSup_subtype'' C fun x : E ↦ ⟪x, xStar⟫ₚ]
    _ = δᵛ(xStar | C) := by
          rw [supportFunction_def]
          congr with x
          exact congrArg ((↑) : α → WithTopBot α)
            (HasPairingSwap.pairing_swap (x := (x : E)) (y := xStar))

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction
    (C : Set E) :
    ((δ(· | C))⋆ : EStar → WithTopBot α) =
      (δᵛ(· | C) : EStar → WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction (C := C)

/- Text 13.1.4 in pointwise form at the pairing layer with the canonical pairing-swap owner. -/
theorem convexConjugate_indicator_eq_supportFunction_pointwise
    (C : Set E) (xStar : EStar) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  simpa using congrFun
    (convexConjugate_indicator_eq_supportFunction (C := C)) xStar

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction_pointwise
    (C : Set E) (xStar : EStar) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction_pointwise (C := C) (xStar := xStar)

end PairingSwap

section PairingSymmetric

variable {E : Type*} {α : Type*}
variable [Add α] [Neg α] [Zero α] [ConditionallyCompleteLattice α]
variable [HasPairing E E α]

/-- Text 13.1.4 at the pairing layer: if the self-pairing is symmetric, then the Fenchel conjugate
of the indicator `δ(· | C)` is the support function `δᵛ(· | C)`. -/
theorem convexConjugate_indicator_eq_supportFunction_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) :
    ((δ(· | C))⋆ : E → WithTopBot α) =
      (δᵛ(· | C) : E → WithTopBot α) := by
  letI : HasPairingSwap E E α := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_indicator_eq_supportFunction (C := C))

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) :
    ((δ(· | C))⋆ : E → WithTopBot α) =
      (δᵛ(· | C) : E → WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction_of_pairing_symm
    (hpair_symm := hpair_symm) (C := C)

/- Text 13.1.4 in pointwise form at the pairing layer. -/
theorem convexConjugate_indicator_eq_supportFunction_pointwise_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) (xStar : E) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  letI : HasPairingSwap E E α := ⟨hpair_symm⟩
  simpa using
    (convexConjugate_indicator_eq_supportFunction_pointwise (C := C) (xStar := xStar))

/- Long-name bridge alias for downstream files still using `indicatorFunction` in theorem names. -/
theorem convexConjugate_indicatorFunction_eq_supportFunction_pointwise_of_pairing_symm
    (hpair_symm : ∀ x y : E, (⟪x, y⟫ₚ : α) = ⟪y, x⟫ₚ)
    (C : Set E) (xStar : E) :
    (δ(· | C))⋆ xStar = (δᵛ(xStar | C) : WithTopBot α) := by
  simpa using convexConjugate_indicator_eq_supportFunction_pointwise_of_pairing_symm
    (hpair_symm := hpair_symm) (C := C) (xStar := xStar)

end PairingSymmetric

end
