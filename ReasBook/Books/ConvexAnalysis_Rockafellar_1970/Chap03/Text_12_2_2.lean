import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Defn_12_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

open scoped Rockafellar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 12.2.2 studies pairs `(f, g)` of extended-valued functions,
  specialized in the source to `R^n`, satisfying the generalized Fenchel inequality and ordered
  pointwise by simultaneous tightening.
- `core/canonical`: the owner construction for conjugation is `convexConjugate`, and the ambient
  order is the canonical product order on `(X → L) × (Y → L)`, specialized below to
  `WithBotTop α` where conjugacy is used.
- `bridge/view`: the textbook set `𝒲` is rendered by the owner `fenchelAdmissiblePairs`
  (notation `𝒲`), while pointwise admissibility is rendered by `isFenchelPair`. Textbook
  minimality is rendered as `Minimal 𝒲` on function pairs. The owner-side comparison data is the
  pointwise inequality `f⋆ ≤ g`, with the converse recovered only under the exact no-`⊥`
  hypotheses forced by Fenchel admissibility.

Domain-style sampling used here:
- `convexConjugate`;
- `convexConjugate_antitone`;
- `fenchelAdmissiblePairs` (notation `𝒲`);
- `Minimal` for order-theoretic minimality in a partial order.

Primitive data vs derived API:
- primitive inputs: a pair of functions `f : X → L` and `g : Y → L`;
- primitive pairing data is the codomain-level owner `HasPairing X Y L`; in the conjugacy layer,
  `L = WithBotTop α` is supplied by the canonical lift from a scalar pairing;
- primitive owner relation introduced here: `isFenchelPair f g` at weak assumptions
  `[LE L] [Add L]`;
- product owner/set view: `fenchelAdmissiblePairs` with notation `𝒲`;
- derived API: symmetry of the admissibility relation under a swap-compatible pairing identity, the
  owner inequality `isFenchelPair f g → f⋆ ≤ g`, the atomic left/right no-`⊥` consequences under
  opposite-side nonemptiness, its converse under the sharp no-`⊥` side conditions, and the
  minimality criterion.

Layer target: `source-facing`; the item remains a direct theorem about admissible pairs and
mutual Fenchel conjugacy. The source writes this on `R^n`, while the canonical chapter codomain is
`WithBotTop α`; the declarations are therefore stated directly on paired spaces
`HasPairing X Y α` (with canonical codomain lift to `WithBotTop α`) rather than on a concrete
real self-model.
-/

section FenchelPairOwner

variable {L : Type v} [LE L] [Add L]
variable {X : Type u} {Y : Type w} [HasPairing X Y L]

/-- A Fenchel-admissible pair is a pair of `L`-valued functions on paired spaces, satisfying the
generalized Fenchel inequality `⟪x, y⟫ₚ ≤ f x + g y` for all `x` and `y`. -/
def isFenchelPair (f : X → L) (g : Y → L) : Prop :=
  ∀ x : X, ∀ y : Y, ⟪x, y⟫ₚ ≤ f x + g y

/-- The textbook Fenchel-admissible set `𝒲`, viewed as a predicate on pairs of functions. -/
def fenchelAdmissiblePairs : Set ((X → L) × (Y → L)) :=
  {fg | isFenchelPair fg.1 fg.2}

scoped[Rockafellar] notation "𝒲" => fenchelAdmissiblePairs

@[simp] theorem mem_fenchelAdmissiblePairs
    (f : X → L) (g : Y → L) :
    (f, g) ∈ 𝒲 ↔ isFenchelPair f g :=
  Iff.rfl

-- Proof sketch: swap `x` and `y` and use `HasPairingSwap.pairing_swap`.
/-- The generalized Fenchel inequality is symmetric in the two functions. -/
@[simp]
theorem isFenchelPair_comm
    [HasPairing Y X L] [HasPairingSwap X Y L]
    (f : X → L) (g : Y → L) :
    isFenchelPair f g ↔ isFenchelPair g f := sorry

end FenchelPairOwner

section ConjugacyLayer

variable {α : Type v} [AddCommGroup α] [ConditionallyCompleteLinearOrder α]
  [IsOrderedAddMonoid α]
variable {X : Type u} {Y : Type w} [HasPairing X Y α]

-- Proof sketch: rewrite `⟪x, y⟫ₚ ≤ f x + g y` as `⟪x, y⟫ₚ - f x ≤ g y` and take the supremum over
-- `x` to obtain `f⋆ y ≤ g y`.
/-- A Fenchel-admissible pair gives the owner-side conjugate inequality `f⋆ ≤ g`. -/
theorem convexConjugate_le_of_isFenchelPair
    (f : X → WithBotTop α) (g : Y → WithBotTop α) (hfg : isFenchelPair f g) :
    f⋆ ≤ g := sorry

-- Proof sketch: for fixed `x`, choose `y` from the nonempty right space. If
-- `⟪x, y⟫ₚ ≤ f x + g y` and `f x = ⊥`, then the right side is `⊥`, impossible because pairing
-- values lie in `α` and therefore are not `⊥`.
/-- If the right space is nonempty, a Fenchel-admissible pair has no `-∞` values in its left
component. -/
theorem isFenchelPair_left_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hy : Nonempty Y) (hfg : isFenchelPair f g) (x : X) :
    f x ≠ ⊥ := sorry

/-- If the left space is nonempty, a Fenchel-admissible pair has no `-∞` values in its right
component. -/
theorem isFenchelPair_right_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hx : Nonempty X) (hfg : isFenchelPair f g) (y : Y) :
    g y ≠ ⊥ := sorry

-- Proof sketch: from `f⋆ y ≤ g y`, each affine defect `⟪x, y⟫ₚ - f x` is bounded
-- above by `g y`. The hypotheses `f x ≠ ⊥` and `g y ≠ ⊥` are exactly the side conditions needed
-- for `sub_le_iff_le_add`, which converts this defect bound back to
-- `⟪x, y⟫ₚ ≤ f x + g y`.
/-- The owner inequality `f⋆ ≤ g` recovers the generalized Fenchel inequality once both functions
avoid the value `-∞`; with nonempty opposite-side spaces, admissibility forces exactly these
side conditions. -/
theorem isFenchelPair_of_convexConjugate_le_of_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hf : ∀ x : X, f x ≠ ⊥) (hg : ∀ y : Y, g y ≠ ⊥)
    (hfg : f⋆ ≤ g) :
    isFenchelPair f g := sorry

-- Proof sketch: combine the forward owner inequality with the converse under the no-`⊥`
-- hypotheses.
/-- Under the sharp no-`⊥` hypotheses, Fenchel admissibility is equivalent to the owner inequality
`f⋆ ≤ g`. -/
theorem isFenchelPair_iff_convexConjugate_le_of_ne_bot
    (f : X → WithBotTop α) (g : Y → WithBotTop α)
    (hf : ∀ x : X, f x ≠ ⊥) (hg : ∀ y : Y, g y ≠ ⊥) :
    isFenchelPair f g ↔ f⋆ ≤ g := sorry

-- Proof sketch: from minimality, first read off admissibility and then, using nonemptiness on
-- both sides, read off the no-`⊥` conditions from `isFenchelPair_left_ne_bot` and
-- `isFenchelPair_right_ne_bot`. The owner inequalities
-- `f⋆ ≤ g` and `g⋆ ≤ f` follow from
-- `convexConjugate_le_of_isFenchelPair` and symmetry. If `(f', g')` is an admissible smaller pair,
-- antitonicity of conjugation forces `g ≤ f'* ≤ g'` and `f ≤ g'* ≤ f'`, so minimality makes the
-- owner equalities sharp. Conversely, if `(f, g)` is admissible and mutually conjugate, then any
-- admissible smaller pair has the same owner inequalities, and the same antitonicity argument
-- forces equality.
/-- Text 12.2.2: a pair `(f, g)` is a minimal element among the Fenchel-admissible pairs, ordered
pointwise by simultaneous tightening, if and only if `f` and `g` are mutually conjugate:
`g = f⋆` and `f = g⋆`. Over arbitrary `WithBotTop α`-valued functions the admissibility clause is
not redundant, because mutual conjugacy alone does not rule out the `⊤`/`⊥` pathologies of the
extended codomain. -/
theorem minimal_fenchel_pair_iff_mutually_conjugate
    [HasPairing Y X α] [HasPairingSwap X Y α]
    (hx : Nonempty X) (hy : Nonempty Y)
    (f : X → WithBotTop α) (g : Y → WithBotTop α) :
    Minimal 𝒲 (f, g) ↔
      (f, g) ∈ 𝒲 ∧ g = f⋆ ∧ f = g⋆ := sorry

end ConjugacyLayer
