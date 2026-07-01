import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v} {α : Type w}
variable [Add α] [Neg α] [ConditionallyCompleteLattice α]

section IntrinsicCodomainCore

variable [HasPairing X Y (WithBotTop α)]

-- Proof sketch: if for each `y` there is some `x` with finite pairing value, then that term in
-- the defining supremum is `⊤` because subtracting `⊥` gives `⊤`; hence the whole supremum is
-- `⊤`.
/-- Core codomain-level `⊥ ↦ ⊤` conjugacy identity: if each dual point `y` admits at least one
finite pairing value `⟪x, y⟫ₚ ≠ ⊥`, then the conjugate of the constant `-∞` function is the
constant `+∞` function. -/
theorem convexConjugate_bot_eq_top_of_exists_pairing_ne_bot
    (hfinite : ∀ y : Y, ∃ x : X, (⟪x, y⟫ₚ : WithBotTop α) ≠ ⊥) :
    ((⊥ : X → WithBotTop α)⋆) = (⊤ : Y → WithBotTop α) := by
  ext y
  rcases hfinite y with ⟨x0, hx0⟩
  change (⨆ x : X, ⟪x, y⟫ₚ - (⊥ : WithBotTop α)) = (⊤ : WithBotTop α)
  rw [eq_top_iff]
  refine le_iSup_of_le x0 ?_
  change (⊤ : WithBotTop α) ≤ (⟪x0, y⟫ₚ - (⊥ : WithBotTop α))
  simp [WithBotTop.sub_bot hx0]

-- Proof sketch: use `convexConjugate_eq_iSup_pairing_sub`; every summand is `⊥` because
-- subtracting `⊤` in `WithBotTop α` gives `⊥`, so the supremum is `⊥`.
/-- Core codomain-level `⊤ ↦ ⊥` conjugacy identity for any pairing into `WithBotTop α`. -/
theorem convexConjugate_top_eq_bot_core :
    ((⊤ : X → WithBotTop α)⋆) = (⊥ : Y → WithBotTop α) := by
  ext y
  simp [convexConjugate_eq_iSup_pairing_sub]

end IntrinsicCodomainCore

section FinitePairingLift

variable [HasPairing X Y α]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.1.3 states that the constant functions with values `-∞` and `+∞` are
  Fenchel conjugates of one another.
- `core/canonical`: the owner abstraction is the chapter Fenchel conjugate `convexConjugate`.
- `bridge/view`: the scoped postfix notation `f⋆` from `Defn_12_2` is the canonical theorem
  surface for that owner, while the complete-lattice constants `⊥` and `⊤` on
  `X → WithBotTop α` and `Y → WithBotTop α` are the canonical Lean owners for the constant `-∞`
  and `+∞` functions.

Domain-style sampling used here:
- `convexConjugate`;
- `convexConjugate_eq_iSup_pairing_sub`;
- the complete-lattice constants `⊥` and `⊤` on `X → WithBotTop α` and `Y → WithBotTop α`;
- the `WithBotTop` arithmetic simplifications `sub_bot` and `sub_top`.

Primitive data vs derived API:
- primitive codomain-level core for `⊥ ↦ ⊤`: pairing in `WithBotTop α` plus the finite-value
  witness `∀ y, ∃ x, ⟪x, y⟫ₚ ≠ ⊥`;
- source-facing finite-lift bridge for `⊥ ↦ ⊤`: `HasPairing X Y α` gives canonical finite pairing
  values in `WithBotTop α`;
- primitive codomain-level core for `⊤ ↦ ⊥`: `HasPairing X Y (WithBotTop α)`.
- primitive codomain layer: `WithBotTop α`;
- derived API: the two atomic conjugacy identities for the canonical owner
  `convexConjugate`.

Layer target: `source-facing`; the source writes this on `R^n` with `EReal`, while the canonical
owner statement only needs the intrinsic pairing layer together with an extended ordered codomain.
-/

/-- Text 12.1.3 (1): for any nonempty primal pairing domain and any chapter extended codomain
`WithBotTop α`, the Fenchel conjugate of the constant `-∞` function is the constant `+∞`
function, written on the canonical function-lattice surface as
`((⊥ : X → WithBotTop α))⋆ = (⊤ : Y → WithBotTop α)`. -/
@[simp] theorem convexConjugate_bot_eq_top [Nonempty X] :
    ((⊥ : X → WithBotTop α)⋆) = (⊤ : Y → WithBotTop α) := by
  refine convexConjugate_bot_eq_top_of_exists_pairing_ne_bot (X := X) (Y := Y) (α := α) ?_
  intro y
  rcases (inferInstance : Nonempty X) with ⟨x0⟩
  refine ⟨x0, ?_⟩
  exact WithBotTop.coe_ne_bot (⟪x0, y⟫ₚ : α)

end FinitePairingLift

section IntrinsicCodomainPairing

variable [HasPairing X Y (WithBotTop α)]

/-- Text 12.1.3 (2): for any pairing and any chapter extended codomain `WithBotTop α`, the
Fenchel conjugate of the constant `+∞` function is the constant `-∞` function, written on the
canonical function-lattice surface as `((⊤ : X → WithBotTop α))⋆ = (⊥ : Y → WithBotTop α)`. -/
@[simp] theorem convexConjugate_top_eq_bot :
    ((⊤ : X → WithBotTop α)⋆) = (⊥ : Y → WithBotTop α) := by
  exact convexConjugate_top_eq_bot_core (X := X) (Y := Y) (α := α)

end IntrinsicCodomainPairing

end
