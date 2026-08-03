import BauschkeLean.Chap21.Corollary_21_14
import BauschkeLean.Chap25.Definition_25_10

open scoped InnerProductSpace SetValuedOperator

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 25.11 identifies the closure of `dom (F[A])`.
- `core/canonical`: the owner data are `F[A]` and `Maximal IsMonotone A`.
- `bridge/view`: the proof routes through the Chapter 21 projection views
  `A.fstImageDomFitzpatrick` and `A.sndImageDomFitzpatrick`, together with the Chapter 25
  predicate `A.IsThreeStarMonotone`.

The reusable API surface here is the direct inclusion
`ERealFunction.dom (F[A]) ⊆ closure A.dom ×ˢ closure A.range`; the proposition then combines it
with the source-facing `3*`-monotonicity inclusion `A.dom ×ˢ A.range ⊆ ERealFunction.dom (F[A])`.
-/

/-- Every point of the Fitzpatrick effective domain of a maximally monotone operator lies in the
product of the closures of its domain and range. -/
theorem dom_fitzpatrick_subset_closure_dom_prod_closure_range_of_maximal
    {A : SetValuedOperator H H} (hA_max : Maximal IsMonotone A) :
    ERealFunction.dom (F[A]) ⊆ closure A.dom ×ˢ closure A.range := by
  intro p hp
  refine ⟨?_, ?_⟩
  · exact fst_image_dom_fitzpatrick_subset_closure_dom A hA_max ⟨p, hp, rfl⟩
  · have hp_snd : p.2 ∈ A.sndImageDomFitzpatrick := ⟨p, hp, rfl⟩
    have hsnd :
        closure A.range = closure A.sndImageDomFitzpatrick :=
      closure_range_eq_closure_snd_image_dom_fitzpatrick_of_maximal A hA_max
    simpa [hsnd] using (subset_closure hp_snd : p.2 ∈ closure A.sndImageDomFitzpatrick)

/-- Proposition 25.11: if `A` is maximally monotone and `3*` monotone, then the closure of
`dom F_A`, formalized by `ERealFunction.dom (F[A])`, is `closure A.dom ×ˢ closure A.range`. -/
theorem closure_dom_fitzpatrick_eq_closure_dom_prod_closure_range_of_maximal_threeStarMonotone
    {A : SetValuedOperator H H} (hA_max : Maximal IsMonotone A)
    (hA_threeStar : A.IsThreeStarMonotone) :
    closure (ERealFunction.dom (F[A])) = closure A.dom ×ˢ closure A.range := by
  apply le_antisymm
  · exact closure_minimal
      (dom_fitzpatrick_subset_closure_dom_prod_closure_range_of_maximal hA_max)
      (isClosed_closure.prod isClosed_closure)
  · rw [← closure_prod_eq]
    exact closure_mono hA_threeStar.subset_dom_fitzpatrickFunction

end SetValuedOperator
