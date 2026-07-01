import Mathlib
import stacks_project.Chap10.Lemma_10_69_5
import stacks_project.Chap15.Definition_15_30_1
import stacks_project.Chap15.Lemma_15_30_11
import stacks_project.Chap15.Lemma_15_30_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace RingTheory.Sequence

variable {A : Type u} [CommRing A]

/-
Domain triage:
* primary domain: `H₁`-regular and quasi-regular finite sequences in commutative algebra;
* sampled owner API:
  `Ideal.ofList`,
  `Ideal.ofList_ofFn_eq_span_range`,
  `RingTheory.Sequence.IsH1RegularSequence`,
  `RingTheory.Sequence.IsH1RegularOn.isQuasiRegular`,
  `RingTheory.Sequence.IsQuasiRegular.tail_quotient`;
* core/canonical owner abstraction: the canonical quotient-by-prefix and tail construction already
  organized by `IsQuasiRegular.tail_quotient`, with the prefix ideal canonically expressed as
  `Ideal.ofList (List.ofFn f)`;
* primitive data: the prefix `f` and the tail `g`;
  derived API: the source-facing quotient ring `A ⧸ Ideal.span (Set.range f)` and the quotient-side
  `H₁`-regularity statement for the image family of `g`;
* layer: `bridge/view`, since the public theorem keeps the source-facing quotient by
  `(f₁, \ldots, fₙ)` while the owner-level regular-sequence API is already organized around
  `Ideal.ofList (List.ofFn f)`.
-/

-- Proof sketch: first prove the quotient-side statement for the canonical prefix ideal
-- `Ideal.ofList (List.ofFn f)`, which is the owner-level quotient-by-prefix input for finite
-- sequences. Then rewrite that owner-level quotient to the source-facing ideal
-- `Ideal.span (Set.range f)`.
/-- Lemma 15.30.12: if the concatenated family `f_1, \ldots, f_n, g_1, \ldots, g_m` is
`H_1`-regular in `A`, then the images of `g_1, \ldots, g_m` in `A / (f_1, \ldots, f_n)` form an
`H_1`-regular sequence. -/
theorem isH1RegularSequence_quotient_of_append {n m : ℕ} (f : Fin n → A) (g : Fin m → A)
    (hfg : IsH1RegularSequence (Fin.append f g)) :
    IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk (Ideal.span (Set.range f)) (g i)) := by
  suffices hcanon :
      IsH1RegularSequence (fun i ↦ Ideal.Quotient.mk (Ideal.ofList (List.ofFn f)) (g i)) by
    rw [← Ideal.ofList_ofFn_eq_span_range f]
    exact hcanon
  sorry

end RingTheory.Sequence
