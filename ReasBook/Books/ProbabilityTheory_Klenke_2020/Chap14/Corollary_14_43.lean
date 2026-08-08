import ProbabilityTheory_Klenke_2020.Chap14.Theorem_14_42

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Preorder Finset
open scoped ProbabilityTheory

noncomputable section

universe u v

variable {I : Type u} [Preorder I] [OrderBot I]
variable {E : Type v} [MeasurableSpace E]

-- Proof sketch: define the candidate measure as the composition `κpath ∘ₘ μ`. The finite-chain
-- marginal identity follows by integrating the point-mass identity from `hκpath.2` against `μ`;
-- the resulting measure is a probability measure because both `μ` and `κpath` are Markov. For
-- uniqueness, compare finite-dimensional marginals on every ordered finite chain and invoke the
-- usual cylinder/projective-limit uniqueness argument.
/-- Auxiliary bridge: once a path kernel with the finite-dimensional marginals from Theorem 14.42
is fixed, composing it with an initial probability measure yields the corresponding unique
probability measure on path space. -/
theorem existsUnique_probabilityMeasure_with_consistent_kernel_marginals_of_kernel
    (μ : Measure E) [IsProbabilityMeasure μ]
    (κ : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (κpath : Kernel E (I → E))
    (hκpath :
      IsMarkovKernel κpath ∧
        ∀ (x : E) {n : ℕ} (j : Π _ : Finset.Iic n, I),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
              (κpath x).map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalKernel κ j hj x) :
    ∃! P : Measure (I → E),
      IsProbabilityMeasure P ∧
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, I),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
              P.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure μ κ j hj := sorry

section

variable {E : Type v} [MeasurableSpace E] [StandardBorelSpace E]
variable {I : Set NNReal}
variable (h0I : (0 : NNReal) ∈ I)

-- Proof sketch: apply Theorem 14.42 to obtain a path kernel `κpath` with the prescribed
-- point-mass finite-dimensional marginals, then compose it with the initial law `μ` and invoke
-- `existsUnique_probabilityMeasure_with_consistent_kernel_marginals_of_kernel`.
/-- Corollary 14.43: a consistent family of Markov kernels on the standard Borel state space `E`
and an initial probability measure determine a unique probability measure on the path space whose
finite-dimensional marginals are the mixed laws induced by the kernels along every strictly
increasing chain starting at `0`. -/
theorem existsUnique_probabilityMeasure_with_consistent_kernel_marginals
    (K : ∀ ⦃s t : I⦄, s < t → Kernel E E)
    (hMarkov : ∀ {s t} (hst : s < t), IsMarkovKernel (K hst))
    (hConsistent : IsConsistentKernelFamily K)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    letI : OrderBot I := Subtype.orderBot h0I
    ∃! P : Measure (I → E),
      IsProbabilityMeasure P ∧
        ∀ {n : ℕ} (j : Π _ : Finset.Iic n, I),
          ∀ (hj : StrictMono j),
            j ⟨0, mem_Iic.2 (Nat.zero_le n)⟩ = ⊥ →
              P.map (finiteCoordinateProjection j) =
                consistentFamilyFiniteDimensionalMeasure μ K j hj := sorry

end
