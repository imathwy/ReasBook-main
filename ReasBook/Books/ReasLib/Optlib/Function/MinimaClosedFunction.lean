/-
Copyright (c) 2023 Wanyi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

/-!
  the Weierstrass theorem
-/
variable {E F : Type*}

open Set Bornology Topology Filter TopologicalSpace

section preparation

variable {E F : Type*} [CompleteLinearOrder F]

private lemma l0 {f : E → F} (y : F) (h : (f ⁻¹' Set.Iic y).Nonempty) :
    sInf {f x | x ∈ f ⁻¹' Set.Iic y} = sInf {f x | x : E}:= by
  have h₀ : {f x | x : E} = {f x | x ∈ f ⁻¹' Set.Iic y} ∪ {f x | x ∈ (f ⁻¹' Set.Iic y)ᶜ} := by
    ext y'; constructor
    · rintro ⟨x, xeq⟩
      by_cases xsub : x ∈ f ⁻¹' Set.Iic y
      · exact Or.inl ⟨x, xsub, xeq⟩
      · exact Or.inr ⟨x, xsub, xeq⟩
    · intro h'
      rcases h' with ⟨x, _, xeq⟩ | ⟨x, _, xeq⟩
      · exact Exists.intro x xeq
      · exact Exists.intro x xeq
  have h₁ : sInf {f x | x ∈ f ⁻¹' Set.Iic y} ≤ sInf {f x | x ∈ (f ⁻¹' Set.Iic y)ᶜ} := by
    apply sInf_le_sInf_of_isCoinitialFor
    intro y' ynsub
    rcases h with ⟨x', xsub⟩; use f x'
    constructor
    · exact ⟨x', xsub, rfl⟩
    rcases ynsub with ⟨x, xnsub, xeq⟩
    simp only [← Set.preimage_compl, Set.compl_Iic] at xnsub
    exact xsub.trans (le_of_lt (by rwa [← xeq]))
  calc
    sInf {f x | x ∈ f ⁻¹' Set.Iic y} =
      sInf {f x | x ∈ f ⁻¹' Set.Iic y} ⊓ sInf {f x | x ∈ (f ⁻¹' Set.Iic y)ᶜ} :=
        Iff.mpr left_eq_inf h₁
    _ = sInf ({f x | x ∈ f ⁻¹' Set.Iic y} ∪ {f x | x ∈ (f ⁻¹' Set.Iic y)ᶜ}) := Eq.symm sInf_union
    _ = sInf {f x | x : E} := congrArg sInf (id (Eq.symm h₀))

end preparation

/-! ### Generalized Weierstrass theorem -/

section

variable [CompleteLinearOrder F]

variable {f : E → F}

variable [TopologicalSpace E] [TopologicalSpace F] [OrderTopology F]

variable [FirstCountableTopology E] [FirstCountableTopology F]

/- If a premiage of `f` is nonempty and compact,
  then its minimum point set `{x | IsMinOn f univ x}` is nonempty -/


theorem IsMinOn.of_isCompact_preimage (hf : LowerSemicontinuous f) {y : F}
    (h1 : (f ⁻¹' Set.Iic y).Nonempty) (h2 : IsCompact (f ⁻¹' Set.Iic y)) :
    ∃ x, IsMinOn f univ x := by
  have hs : Set.Nonempty {f x | x ∈ (f ⁻¹' Set.Iic y)} := by
    rcases h1 with ⟨x, xsub⟩
    exact Exists.intro (f x) (Exists.intro x ⟨xsub, rfl⟩)
  have hs' : BddBelow {f x | x ∈ (f ⁻¹' Set.Iic y)} :=
    OrderBot.bddBelow {x | ∃ x_1 ∈ f ⁻¹' Iic y, f x_1 = x}
  rcases exists_seq_tendsto_sInf hs hs' with ⟨fx, _, cfx, fxs⟩
  choose x xsub xeq using fxs
  rcases IsCompact.tendsto_subseq h2 xsub with ⟨x', xsub', k, mono, cxk⟩
  have cfxk : Tendsto (f ∘ x ∘ k) atTop (𝓝 (sInf {f x | x ∈ (f ⁻¹' Set.Iic y)})) := by
    have xkeq : ∀ (n : ℕ), (f ∘ x ∘ k) n = (fx ∘ k) n := fun n => xeq <| k n
    rw [tendsto_congr xkeq]
    apply Tendsto.comp cfx (StrictMono.tendsto_atTop mono)
  have inepi : (x', sInf {f x | x ∈ (f ⁻¹' Set.Iic y)}) ∈ {p : E × F | f p.1 ≤ p.2} :=
    (IsClosed.isSeqClosed (LowerSemicontinuous.isClosed_epigraph hf))
      (fun n => Eq.le (by rfl)) (Filter.Tendsto.prodMk_nhds cxk cfxk)
  use x'; intro xx _
  apply le_of_eq_of_le
  · apply le_antisymm inepi (sInf_le (Exists.intro x' ⟨xsub', rfl⟩))
  · apply le_of_eq_of_le (l0 y h1) (sInf_le (by use xx))

/- If a premiage of `f` is nonempty and compact,
  then its minimum point set `{x | IsMinOn f univ x}` is compact -/

theorem IsCompact_isMinOn_of_isCompact_preimage (hf : LowerSemicontinuous f) {y : F}
    (h1 : (f ⁻¹' Set.Iic y).Nonempty) (h2 : IsCompact (f ⁻¹' Set.Iic y)) :
    IsCompact {x | IsMinOn f univ x} := by
  obtain ⟨x', hx'⟩ := IsMinOn.of_isCompact_preimage hf h1 h2
  have seq : {x | IsMinOn f univ x} = (f ⁻¹' Set.Iic (f x')) :=
      Set.ext fun xx =>
        { mp := fun hxx => isMinOn_iff.mp hxx x' trivial,
          mpr := fun hxx x xuniv => ge_trans (hx' xuniv) hxx }
  simp only [seq]
  apply IsCompact.of_isClosed_subset h2 (LowerSemicontinuous.isClosed_preimage hf (f x'))
  apply Set.preimage_mono
  simp only [Set.Iic_subset_Iic]
  obtain ⟨x, hx⟩ := h1
  exact ge_trans hx (hx' trivial)

end

/-! ### Existence of Solutions -/

section

variable {𝕜 : Type _} {f : E → F}
variable [AddCommMonoid E] [CompleteLinearOrder F]
variable [Ring 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [Module 𝕜 E]

def strong_quasi (f : E → F) (𝕜 : Type _) [Ring 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [Module 𝕜 E] : Prop :=
  ∀ ⦃x⦄, ∀ ⦃y⦄, x ≠ y → ∀ ⦃a b : 𝕜⦄, 0 < a → 0 < b → a + b = 1
    → f ((a • x : E) + (b • y : E)) < max (f x) (f y)

/- the Minimum of strongly quasi function is unique -/
theorem isMinOn_unique {x y : E} (hf' : strong_quasi f 𝕜)
    (hx : IsMinOn f univ x) (hy : IsMinOn f univ y) : x = y := by
  by_contra neq
  have : (0 : 𝕜) < (1 : 𝕜) := one_pos
  obtain ⟨a, lta, alt⟩ := exists_between this
  have eqone : a + (1 - a) = 1 := add_sub_cancel a 1
  have lta' : 0 < 1 - a := sub_pos_of_lt alt
  have h : f (a • x + (1 - a) • y) < f y := by
    have hmax := hf' neq lta lta' eqone
    rwa [max_eq_right (hx trivial)] at hmax
  simp only [isMinOn_iff] at hy
  specialize hy (a • x + (1 - a) • y) trivial
  apply not_le_of_gt h hy

end
