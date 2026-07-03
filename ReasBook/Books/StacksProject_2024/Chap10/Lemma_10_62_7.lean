import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory
open CategoryTheory.ShortComplex

private theorem moduleSupport_isUpperSet
    {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :
    IsUpperSet (Module.support R M) := by
  intro p q hpq hp
  exact Module.mem_support_mono hpq hp

private theorem krullDim_union_eq_max_of_isUpperSet
    {α : Type*} [Preorder α] {s t : Set α} (hs : IsUpperSet s) (ht : IsUpperSet t) :
    Order.krullDim ↑(s ∪ t) = max (Order.krullDim ↑s) (Order.krullDim ↑t) := by
  refine le_antisymm ?_ (max_le_iff.mpr ⟨?_, ?_⟩)
  · rw [Order.krullDim, iSup_le_iff]
    intro p
    by_cases hp : (p.head : α) ∈ s
    · let q : LTSeries s :=
        LTSeries.mk p.length
          (fun i ↦ ⟨(p i : α), hs (show (p.head : α) ≤ (p i : α) from p.head_le i) hp⟩)
          (fun i j hij ↦ p.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim q).trans (le_max_left _ _)
    · have hp' : (p.head : α) ∈ t := by
        rcases p.head.2 with hp' | hp'
        · exact (hp hp').elim
        · exact hp'
      let q : LTSeries t :=
        LTSeries.mk p.length
          (fun i ↦ ⟨(p i : α), ht (show (p.head : α) ≤ (p i : α) from p.head_le i) hp'⟩)
          (fun i j hij ↦ p.strictMono hij)
      exact (Order.LTSeries.length_le_krullDim q).trans (le_max_right _ _)
  · exact Order.krullDim_le_of_strictMono
      (fun x : s ↦ (⟨(x : α), Or.inl x.2⟩ : ↑(s ∪ t)))
      (fun _ _ h ↦ h)
  · exact Order.krullDim_le_of_strictMono
      (fun x : t ↦ (⟨(x : α), Or.inr x.2⟩ : ↑(s ∪ t)))
      (fun _ _ h ↦ h)

-- Proof sketch: `Module.support_of_exact` rewrites the support of the middle term as the union of
-- the supports of the two end terms. Each module support is an upper set in the specialization
-- order on `Spec R`, so any prime chain in that union is already contained in whichever support
-- contains its head. The Krull dimension of the union is therefore the maximum of the two support
-- dimensions.
/-
Source/core/bridge triage:
* source-facing: Lemma 10.62.7 is the short-exact-sequence dimension formula from the text.
* core/canonical: the owner abstractions are `Module.support` and `Module.supportDim`.
* bridge/view: exactness identifies the middle support with a union, and support monotonicity
  upgrades the set-theoretic union formula to the owner invariant `Module.supportDim`.
-/
/-- Lemma 10.62.7: for a short exact sequence `0 → M' → M → M'' → 0` of `R`-modules, the support
dimension of the middle term is the maximum of the support dimensions of the two end terms. -/
theorem supportDim_eq_max_of_shortExact
    {R : Type u} [CommRing R]
    {S : ShortComplex (ModuleCat.{v} R)}
    (hS : S.ShortExact) :
    Module.supportDim R S.X₂ =
      max (Module.supportDim R S.X₁) (Module.supportDim R S.X₃) := by
  have hExact : Function.Exact S.f.hom S.g.hom :=
    (ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact
  have hsupp :
      Module.support R S.X₂ = Module.support R S.X₁ ∪ Module.support R S.X₃ :=
    Module.support_of_exact hExact hS.moduleCat_injective_f hS.moduleCat_surjective_g
  rw [Module.supportDim, Module.supportDim, Module.supportDim, hsupp]
  exact
    krullDim_union_eq_max_of_isUpperSet
      (moduleSupport_isUpperSet S.X₁)
      (moduleSupport_isUpperSet S.X₃)
