import ProbabilityTheory_Klenke_2020.Chap14.Definition_14_39
import ProbabilityTheory_Klenke_2020.Chap14.Definition_14_40

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

section

variable {I : Type u} {E : Type v}
variable [AddCommSemigroup I] [PartialOrder I] [ExistsAddOfLE I] [AddLeftMono I]
variable [Sub I] [OrderedSub I]
variable [MeasurableSpace E]

/-- Lemma 14.41: if a family of stochastic kernels satisfies the Chapman--Kolmogorov semigroup
law, then the time-difference family `(s, t) ↦ κ (t - s)` is a consistent kernel family in the
sense of Definition 14.39. -/
theorem time_difference_kernels_consistent_of_chapman_kolmogorov
    (κ : I → Kernel E E)
    (hChapmanKolmogorov : ∀ s t : I, (κ t) ∘ₖ (κ s) = κ (s + t)) :
    IsConsistentKernelFamily (fun {s t} _ ↦ κ (t - s)) := sorry

end

section

variable {I : Type u} {E : Type v}
variable [AddCommMonoid I] [PartialOrder I] [ExistsAddOfLE I] [AddLeftMono I]
variable [Sub I] [OrderedSub I]
variable [MeasurableSpace E]
variable {κ : I → Kernel E E}

-- Proof sketch: apply Lemma 14.41 to the owner abstraction `IsMarkovSemigroup` and use its
-- Chapman--Kolmogorov field.
/-- A Markov semigroup induces a consistent family of time-difference kernels. -/
theorem IsMarkovSemigroup.time_difference_kernels_consistent
    (hκ : IsMarkovSemigroup κ) :
    IsConsistentKernelFamily (fun {s t} _ ↦ κ (t - s)) :=
  time_difference_kernels_consistent_of_chapman_kolmogorov κ hκ.comp_eq

end
