import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_0_1
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Operations

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise Rockafellar

section Pairing

variable {X : Type*} [Neg X]
variable {Y : Type*}
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLattice α]
variable [IsOrderedAddMonoid α] [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 13.0.2 rewrites an infimum pairing formula as the negative of a support
  function at `-x⋆`.
- `core/canonical`: the owner abstraction is the chapter support function `supportFunction C`,
  together with the order-reversing isomorphism `WithTopBot` negation duality.
- `bridge/view`: the source infimum formula is obtained from
  `supportFunction_eq_sSup_image` by order
  duality plus the primitive neg-left rule of the pairing.
- Primitive data vs derived API: the only primitive bridge data are a set `C`, a point `xStar`,
  and the pairing neg-left identity; the displayed infimum identity is derived API.

Domain-style sampling used here:
- `supportFunction`;
- `supportFunction_eq_sSup_image`;
- `WithTopBot.negOrderIso`, the canonical `WithTopBot` negation order isomorphism;
- `OrderIso.map_sSup_eq_sSup_symm_preimage`, the lattice bridge used to transport the support
  function's supremum formula across that order duality.

Layer target: `bridge/view`, stated directly as the support-function infimum companion while
reusing the canonical support-function owner.

Ambient assumptions in theorem headers:
- `[ConditionallyCompleteLattice α]` is used only to supply `sSup`/`sInf` on `WithTopBot α`;
- `[AddCommGroup α] [IsOrderedAddMonoid α]` are exactly the assumptions required by the canonical
  order-duality bridge `WithTopBot.negOrderIso`.
- No ad-hoc local `Neg`/`InvolutiveNeg` scaffolding is introduced: this item relies on the
  canonical `WithTopBot` instances from `Chap01.EOrder.Operations`.
-/

-- Proof sketch: rewrite `supportFunction C (-xStar)` by `supportFunction_eq_sSup_image`, transport
-- the resulting supremum through `WithTopBot.negOrderIso`, and rewrite the negated image
-- set using the pairing neg-left identity.
/-- Text 13.0.2 at the pairing layer: under the canonical left-negation pairing owner,
`-δᵛ(-xStar | C)` is the infimum of the pairing values with `xStar` on `C`. -/
theorem neg_supportFunction_neg_eq_sInf_image_pairing
    [HasPairingNegLeft X Y α]
    (C : Set Y) (xStar : X) :
    (-(δᵛ(-xStar | C) : WithTopBot α)) = sInf ((fun y ↦ ⟪xStar, y⟫ₚ) '' C) := by
  rw [supportFunction_eq_sSup_image (C := C) (x := -xStar)]
  let A : Set (WithTopBot α) := ((fun y ↦ ⟪-xStar, y⟫ₚ) '' C)
  have hnegneg : ∀ t : WithTopBot α, -(-t) = t := by
    intro t
    cases t using WithBotTop.rec with
    | bot => rfl
    | top => rfl
    | coe a =>
        change (((-(-a) : α) : α) : WithTopBot α) = (a : WithTopBot α)
        rw [neg_neg]
  have hneg : -sSup A = sInf (-A) := by
    have h0 :
        -sSup A =
          ((WithTopBot.negOrderIso (α := α)) (sSup A) : OrderDual (WithTopBot α)) := by
      simpa using (WithTopBot.negOrderIso_apply (α := α) (x := sSup A)).symm
    have h1 :
        ((WithTopBot.negOrderIso (α := α)) (sSup A) : OrderDual (WithTopBot α)) =
          sSup (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
            Set (OrderDual (WithTopBot α))) :=
      OrderIso.map_sSup_eq_sSup_symm_preimage (WithTopBot.negOrderIso (α := α)) A
    have h2 :
        sSup (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
          Set (OrderDual (WithTopBot α))) =
            sInf (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
              Set (WithTopBot α)) := rfl
    have h3 :
        sInf (((WithTopBot.negOrderIso (α := α)).symm ⁻¹' A) :
          Set (WithTopBot α)) = sInf (-A) := by
      congr 1
    exact h0.trans (h1.trans (h2.trans h3))
  have hA : -A = ((fun y ↦ -⟪-xStar, y⟫ₚ) '' C : Set (WithTopBot α)) := by
    dsimp [A]
    ext z
    constructor
    · intro hz
      rcases Set.mem_neg.mp hz with ⟨y, hy, hyz⟩
      refine ⟨y, hy, ?_⟩
      calc
        -⟪-xStar, y⟫ₚ = -(-z : WithTopBot α) := by simp [hyz]
        _ = z := hnegneg z
    · rintro ⟨y, hy, hyz⟩
      refine Set.mem_neg.mpr ?_
      refine ⟨y, hy, ?_⟩
      calc
        (⟪-xStar, y⟫ₚ : WithTopBot α) = -(-⟪-xStar, y⟫ₚ : WithTopBot α) :=
          (hnegneg (⟪-xStar, y⟫ₚ : WithTopBot α)).symm
        _ = -z := by simp [hyz]
  have himage' :
      ((fun y ↦ -⟪-xStar, y⟫ₚ) '' C : Set (WithTopBot α)) =
        ((fun y ↦ ⟪xStar, y⟫ₚ) '' C : Set (WithTopBot α)) := by
    refine Set.image_congr ?_
    intro y hy
    have hα : (-(⟪-xStar, y⟫ₚ : α)) = (⟪xStar, y⟫ₚ : α) := by
      simpa using congrArg (fun t : α ↦ -t) (HasPairingNegLeft.pairing_neg_left xStar y)
    calc
      -(⟪-xStar, y⟫ₚ : WithTopBot α) =
          ((-(⟪-xStar, y⟫ₚ : α) : α) : WithTopBot α) :=
        (WithTopBot.coe_neg _).symm
      _ = (⟪xStar, y⟫ₚ : WithTopBot α) :=
        congrArg (fun t : α ↦ (t : WithTopBot α)) hα
  calc
    -sSup A = sInf (-A) := hneg
    _ = sInf (((fun y ↦ -⟪-xStar, y⟫ₚ) '' C) : Set (WithTopBot α)) := by rw [hA]
    _ = sInf (((fun y ↦ ⟪xStar, y⟫ₚ) '' C) : Set (WithTopBot α)) := by rw [himage']

/-- Pairing-level support-function infimum bridge in swapped orientation: if the pairing is
swap-compatible and the swapped orientation is right-neg compatible, then
`-δᵛ(-xStar | C)` is the infimum of the pairing values `⟪y, xStar⟫ₚ` on `C`. -/
theorem neg_supportFunction_neg_eq_sInf_image_pairing_swap
    [HasPairing Y X α] [HasPairingSwap X Y α] [HasPairingNegRight Y X α]
    (C : Set Y) (xStar : X) :
    (-(δᵛ(-xStar | C) : WithTopBot α)) = sInf ((fun y ↦ ⟪y, xStar⟫ₚ) '' C) := by
  have hpair :
      (-(δᵛ(-xStar | C) : WithTopBot α)) = sInf ((fun y ↦ ⟪xStar, y⟫ₚ) '' C) :=
    neg_supportFunction_neg_eq_sInf_image_pairing C xStar
  have himage_swap :
      ((fun y ↦ ⟪xStar, y⟫ₚ) '' C : Set (WithTopBot α)) =
        ((fun y ↦ ⟪y, xStar⟫ₚ) '' C : Set (WithTopBot α)) := by
    refine Set.image_congr ?_
    intro y hy
    change ((⟪xStar, y⟫ₚ : α) : WithTopBot α) =
      ((⟪y, xStar⟫ₚ : α) : WithTopBot α)
    exact congrArg (fun t : α ↦ (t : WithTopBot α))
      (HasPairingSwap.pairing_swap xStar y)
  simpa [himage_swap] using hpair

end Pairing

end
