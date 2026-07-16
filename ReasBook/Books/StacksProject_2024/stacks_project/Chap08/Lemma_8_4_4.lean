import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_33_8
import StacksProject_2024.stacks_project.Chap08.Lemma_8_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃

namespace CategoryTheory

open BasedFunctor

section

variable {C : Type u₁} {S₁ : Type u₂} {S₂ : Type u₃}
variable [Category.{v₁} C] [Category.{v₂} S₁] [Category.{v₃} S₂]
variable (J : GrothendieckTopology C)

variable (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C)

/- Domain-style sampling for Lemma 8.4.4:
- primary domain: stacks over a site, transported along equivalences in the based category
  `Cat/C`.
- inspected owner-level declarations:
  `IsStackOnSite`,
  `BasedFunctor.IsEquivalenceOverBase`,
  `BasedFunctor.isFibered_iff_of_equivalence_over_base`,
  `isStackOnSite_iff_canonicalFiberPseudofunctor_toDescentData_isEquivalence`.
- best owner abstraction: the source-facing owner remains `IsStackOnSite J p`; the based functor
  `F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂` and the predicate
  `F.IsEquivalenceOverBase` are the canonical Chapter 4 transport interface.
- primitive data: only the two projection functors `p₁`, `p₂` and the over-base equivalence data
  `hF`.
- derived API: the induced transport of fibredness and of the canonical descent-data equivalences
  used to compare the stack conditions.

Source/core/bridge triage:
- `source-facing`: `isStackOnSite_iff_of_equivalence_over_base`.
- `core/canonical`: `IsStackOnSite`, `BasedFunctor.IsEquivalenceOverBase`, and
  `Pseudofunctor.IsStack (canonicalFiberPseudofunctor p) J`.
- `bridge/view`: the coverwise descent-data criterion from Lemma `8.4.2`. -/

/-
Proof sketch: use `BasedFunctor.isFibered_iff_of_equivalence_over_base` to transport the
fibredness part of `IsStackOnSite`, then apply Lemma `8.4.2` to rewrite the stack condition for
each side in terms of equivalence of the canonical descent functors for every cover. The
equivalence-over-base data also upgrades to full faithfulness of the underlying based functor by
the Chapter 4 owner API, which is the canonical input for comparing the resulting descent-data
functors coverwise.
-/
/-- An equivalence over the base between fibred categories is automatically fully faithful on the
underlying based functor. This is a proof-shape helper used in the stack transport argument. -/
private theorem fullyFaithful_of_isEquivalenceOverBase
    [p₁.IsFibered] [p₂.IsFibered]
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    Nonempty F.FullyFaithful := by
  let _ : F.IsEquivalence := isEquivalence_of_isEquivalenceOverBase F hF
  exact ⟨show F.FullyFaithful from .ofFullyFaithful F.toFunctor⟩

/-- Lemma 8.4.4: if two categories over the site `(C, J)` are equivalent over the base category
`C`, then one is a stack over `(C, J)` if and only if the other is. -/
theorem isStackOnSite_iff_of_equivalence_over_base
    (F : BasedCategory.ofFunctor p₁ ⥤ᵇ BasedCategory.ofFunctor p₂)
    (hF : F.IsEquivalenceOverBase) :
    IsStackOnSite J p₁ ↔ IsStackOnSite J p₂ := by
  constructor
  · intro h
    letI : IsStackOnSite J p₁ := h
    letI : p₂.IsFibered := by
      letI : p₁.IsFibered := inferInstance
      exact (BasedFunctor.isFibered_iff_of_equivalence_over_base F hF).mp
        (show (BasedCategory.ofFunctor p₁).p.IsFibered by
          simpa using (inferInstance : p₁.IsFibered))
    have hFF : Nonempty F.FullyFaithful :=
      fullyFaithful_of_isEquivalenceOverBase p₁ p₂ F hF
    sorry
  · intro h
    let e : EquivalenceOverBase F := Classical.choice hF.nonempty
    let G := e.inverse
    have hG : G.IsEquivalenceOverBase := e.inverse_isEquivalenceOverBase
    letI : IsStackOnSite J p₂ := h
    letI : p₁.IsFibered := by
      letI : p₂.IsFibered := inferInstance
      exact (BasedFunctor.isFibered_iff_of_equivalence_over_base G hG).mp
        (show (BasedCategory.ofFunctor p₂).p.IsFibered by
          simpa using (inferInstance : p₂.IsFibered))
    have hGG : Nonempty G.FullyFaithful :=
      fullyFaithful_of_isEquivalenceOverBase p₂ p₁ G hG
    sorry

end

end CategoryTheory
