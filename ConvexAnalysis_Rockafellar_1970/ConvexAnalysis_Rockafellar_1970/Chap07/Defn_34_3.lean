import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4

noncomputable section

universe u v w

open scoped Rockafellar

namespace SaddleFunction

section

variable {U : Type u} {X : Type v} {α : Type w}
variable [LT α]

/-!
Source/core/bridge triage:

- `source-facing`: Defn 34.3 introduces the first-coordinate domain `dom₁ K`, the
  second-coordinate domain `dom₂ K`, their product domain `dom K`, and properness as nonemptiness
  of that product.
- `core/canonical`: these owners only need primitive codomain endpoint/order data
  (`⊥`, `⊤`, `<`), so they are stated for a general bifunction `K : U → X → α`.
- `bridge/view`: later chapter files can speak directly in terms of these owners without
  repackaging them through a separate wrapper.

Domain-style sampling used here:
- a codomain with designated endpoints/order data (`⊥`, `⊤`, `<`);
- `Set` and product sets `×ˢ` from mathlib's canonical set API;
- `Set.Nonempty` as the canonical owner for nonempty effective domain.

Primitive data vs derived API:
- primitive source-facing owners: `dom₁`, `dom₂`, the product-domain owner `dom`, and
  `IsProper`;
- derived API: the membership lemmas, the slice-domain bridges
  `dom_firstSlice_eq_univ` / `dom₂_subset_dom_secondSlice`, and the nonempty-product
  characterization `isProper_iff`.

Layer target: `source-facing`.

Notation decision:
- as in Chapter 6's bifunction domain owner, the recurring Chapter 34 product domain is surfaced
  through the scoped textbook notation `dom K`;
- the raw owner is the short canonical `dom`.
-/

section

variable [Bot α]

/-- The first-coordinate effective domain of a saddle bifunction consists of those `u` for which
every value `K u v` is strictly above `⊥`. -/
def dom₁ (K : U → X → α) : Set U :=
  {u | ∀ v : X, ⊥ < K u v}

-- Proof sketch: unfold the definition of `dom₁`; membership is exactly the displayed universal
-- lower-bound condition on the first coordinate.
/-- Membership in `dom₁ K` means that all second-variable values stay strictly above `⊥`. -/
@[simp] theorem mem_dom₁ {K : U → X → α} {u : U} :
    u ∈ dom₁ K ↔ ∀ v : X, ⊥ < K u v := Iff.rfl

end

section

variable [Top α]

/-- The second-coordinate effective domain of a saddle bifunction consists of those `v` for which
every value `K u v` is strictly below `⊤`. -/
def dom₂ (K : U → X → α) : Set X :=
  {v | ∀ u : U, K u v < ⊤}

-- Proof sketch: unfold the definition of `dom₂`; membership is exactly the displayed universal
-- upper-bound condition on the second coordinate.
/-- Membership in `dom₂ K` means that all first-variable values stay strictly below `⊤`. -/
@[simp] theorem mem_dom₂ {K : U → X → α} {v : X} :
    v ∈ dom₂ K ↔ ∀ u : U, K u v < ⊤ := Iff.rfl

end

section

variable [Bot α] [Top α]

/-- The effective domain of a saddle bifunction is the product of its first- and second-coordinate
effective domains. -/
def dom (K : U → X → α) : Set (U × X) :=
  dom₁ K ×ˢ dom₂ K

/- Rockafellar's source-facing notation for the Chapter 34 product domain of a saddle-function. -/
scoped[Rockafellar] prefix:max "dom " => SaddleFunction.dom

-- Proof sketch: unfold `dom K`; membership in a product set is coordinatewise
-- membership in the two factors.
/-- A point lies in `dom K` exactly when its first coordinate lies in `dom₁ K` and its second
coordinate lies in `dom₂ K`. -/
@[simp] theorem mem_dom {K : U → X → α} {p : U × X} :
    p ∈ dom K ↔ p.1 ∈ dom₁ K ∧ p.2 ∈ dom₂ K := Iff.rfl

/-- Pair form of `mem_dom`, matching the source coordinate notation `(u, v)`. -/
@[simp] theorem mem_dom_mk {K : U → X → α} {u : U} {v : X} :
    (u, v) ∈ dom K ↔ u ∈ dom₁ K ∧ v ∈ dom₂ K :=
  Iff.rfl

/-- Defn 34.3: a saddle bifunction is proper when its product domain
`dom K = dom₁ K ×ˢ dom₂ K` is nonempty. -/
def IsProper (K : U → X → α) : Prop :=
  (dom K).Nonempty

/-- A proper saddle bifunction has nonempty Chapter 34 product domain. -/
theorem IsProper.nonempty_dom {K : U → X → α} (hK : IsProper K) :
    (dom K).Nonempty :=
  hK

end

section

variable [Top α]

/-- Rockafellar's source-facing notation for the first-variable slice of a saddle bifunction. -/
scoped[Rockafellar] notation:max K "(·, " v ")" => fun u => K u v

/-- If `v ∈ dom₂ K`, then the first-variable slice `K(·, v)` is everywhere strictly below `⊤`, so
its effective domain is all of `U`. -/
@[simp] theorem dom_firstSlice_eq_univ
    (K : U → X → α) {v : X} (hv : v ∈ dom₂ K) :
    dom(K(·, v)) = Set.univ := by
  ext u
  simp [mem_dom₂.mp hv u]

/-- The second-coordinate domain `dom₂ K` is contained in the effective domain of every
second-variable slice `K u`. -/
theorem dom₂_subset_dom_secondSlice
    (K : U → X → α) {u : U} :
    dom₂ K ⊆ dom(K u) :=
  fun _ hv ↦ hv u

end

section

variable [Bot α] [Top α]

-- Proof sketch: unfold `IsProper` and `dom K`; nonemptiness of a product set is
-- equivalent to nonemptiness of each coordinate factor.
/-- Properness is equivalent to both coordinate effective domains being nonempty. -/
theorem isProper_iff (K : U → X → α) :
    IsProper K ↔ (dom₁ K).Nonempty ∧ (dom₂ K).Nonempty := by
  change (dom K).Nonempty ↔ (dom₁ K).Nonempty ∧ (dom₂ K).Nonempty
  exact Set.prod_nonempty_iff

/-- A proper saddle bifunction has nonempty first-coordinate effective domain. -/
theorem IsProper.dom₁_nonempty {K : U → X → α} (hK : IsProper K) :
    (dom₁ K).Nonempty :=
  (isProper_iff K).1 hK |>.1

/-- A proper saddle bifunction has nonempty second-coordinate effective domain. -/
theorem IsProper.dom₂_nonempty {K : U → X → α} (hK : IsProper K) :
    (dom₂ K).Nonempty :=
  (isProper_iff K).1 hK |>.2

end

end

end SaddleFunction
