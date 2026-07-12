import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_21_1
import ConvexAnalysis_Rockafellar_1970.Chap04.Text_21_0_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Rockafellar

noncomputable section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 21.2 is Rockafellar's alternative for a mixed finite system consisting
  of a strict convex block `fᵢ(x) < 0` and a weak affine block `gⱼ(x) ≤ 0` on a convex set `C`.
- `core/canonical`: the owner abstraction is the mixed feasible set
  `C ∩ mixedConvexInequalitySolutionSet f g`, built from the
  chapter owner `convexInequalitySolutionSet`.
- `bridge/view`: the source pointwise system and the split multiplier certificate are recovered by
  direct bridge theorems from that owner feasible set.

Domain-style sampling used here:
- `convexInequalitySolutionSet` and `mem_convexInequalitySolutionSet` from `Text_21_0_1`;
- `strict_convexInequalitySolutionSet_nonempty_iff` from `Theorem_21_1`;
- `xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate` from
  `Theorem_21_1`;
- `mixedSystem`.

Primitive data vs derived API:
- primitive data: the strict convex family `f`, the affine family `g`, the mixed relation
  tags, and the zero bounds;
- derived API: the owner mixed feasible set, the pointwise feasibility bridge, and the explicit
  multiplier alternative.

Abstraction audit:
- codomain: the mixed-feasible-set owners in this file are already generalized to the weakest
  primitive codomain layer `WithTopBot α` (`mixedBounds`, `mixedSystem`,
  `mixed_convexInequalitySolutionSet_nonempty_iff`, and
  `mixed_convexInequalitySolutionSet_nonempty_iff_affine`). The final XOR alternatives are stated
  on the same codomain layer `WithTopBot 𝕜`, inherited from the upstream Chapter 21 owner
  `Function.IsNonnegativeZeroBoundCertificateOn`.
- scalar: the source-facing XOR theorems follow the scalar-generic layer of the upstream
  alternative owner they reuse,
  `xor_strict_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate`, so
  this file does not introduce any stronger scalar assumption than that upstream owner.
- model owner: the ambient model is not a coordinate specialization (`EuclideanSpace`, `Fin n`);
  the owner surface is the canonical abstract layer
  `[TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E] [Module 𝕜 E]
  [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]`.
- topology language: the public hypotheses use intrinsic/relative language `ri[𝕜](C)` rather than
  ambient interior.

Layer target: `bridge/view`, with the public theorem stated on the owner mixed strict/weak
feasible set over
the sum-indexed family and the textbook split convex/affine system kept as a thin
`source-facing` companion theorem.
-/

section

variable {𝕜 E α : Type*}
variable {ι κ : Type*}

/-- Index-side owner for the mixed strict/weak relation used in Theorem 21.2. -/
abbrev mixedRelation : ι ⊕ κ → ConvexInequalityRelation :=
  Sum.elim
    (fun _ : ι ↦ ConvexInequalityRelation.lt)
    (fun _ : κ ↦ ConvexInequalityRelation.le)

/-- Index-side owner for the mixed zero bounds used in Theorem 21.2. -/
abbrev mixedBounds [Zero α] : ι ⊕ κ → WithTopBot α :=
  Sum.elim
    (fun _ : ι ↦ (0 : WithTopBot α))
    (fun _ : κ ↦ (0 : WithTopBot α))

/-- Mixed strict/weak system owner, combining a convex `WithTopBot` block and an affine finite
block canonically lifted into `WithTopBot` on the sum index `ι ⊕ κ`. -/
abbrev mixedSystem
    [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup α] [Module 𝕜 α]
    (f : ι → E → WithTopBot α) (g : κ → AffineMap 𝕜 E α) :
    ι ⊕ κ → E → WithTopBot α :=
  Sum.elim f (fun j ↦ Function.toWithTopBot (g j))

/-- Chapter 21 mixed strict/weak feasible-set owner specialized to a strict convex block `f`
and a weak affine block `g`. -/
abbrev mixedConvexInequalitySolutionSet
    [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup α] [Module 𝕜 α]
    [LE α] [LT α] [Zero α]
    (f : ι → E → WithTopBot α) (g : κ → AffineMap 𝕜 E α) : Set E :=
  convexInequalitySolutionSet mixedRelation (mixedSystem f g) mixedBounds

end

section

variable {E α : Type*}
variable {ι κ : Type*}
variable [LE α] [LT α] [Zero α]

/-- Theorem 21.2 owner-side bridge: the mixed feasible set on `C` is nonempty exactly when there
is a point `x ∈ C` satisfying the mixed strict/weak system. -/
theorem mixed_convexInequalitySolutionSet_nonempty_iff
    {C : Set E} (f : ι → E → WithTopBot α) (g : κ → E → WithTopBot α) :
    (C ∩
      convexInequalitySolutionSet
        mixedRelation (Sum.elim f g) mixedBounds).Nonempty ↔
      ∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0 := sorry

end

section

variable {𝕜 E α : Type*}
variable {ι κ : Type*}
variable [Ring 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [AddCommGroup α] [Module 𝕜 α]
variable [LE α] [LT α] [Zero α]

/-- Theorem 21.2 affine-specialized bridge: the owner mixed feasible set is nonempty exactly when
there is `x ∈ C` satisfying the strict convex block and weak affine block. -/
theorem mixed_convexInequalitySolutionSet_nonempty_iff_affine
    {C : Set E} (f : ι → E → WithTopBot α) (g : κ → AffineMap 𝕜 E α) :
    (C ∩ mixedConvexInequalitySolutionSet f g).Nonempty ↔
      ∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0 := sorry

end

section

variable {𝕜 E : Type*} [LinearOrderedField 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [TopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

-- Proof sketch: if a point of `C` satisfies the mixed strict/weak inequalities, then no
-- nonnegative multiplier certificate with some nonzero convex-side coefficient can stay
-- nonnegative on all of `C`, since evaluating at that point makes the weighted sum strictly
-- negative. Conversely, if the mixed system is infeasible, form the convex set of achievable
-- slack vectors for the first block and exact affine values for the second block, separate it from
-- the nonpositive orthant via
-- Theorem 20.2, and use Corollary 7.3.3 to extend the resulting lower bound from the common
-- effective-domain region to all of `C`.
/-- Theorem 21.2 in owner form, stated directly on the mixed strict/weak feasible-set owner
`mixedConvexInequalitySolutionSet`, on the same scalar-generic finite-dimensional topological layer
used by Theorem 21.1. -/
theorem xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate
    {C : Set E} (hC : Convex 𝕜 C)
    (f : ι → E → WithTopBot 𝕜) (g : κ → AffineMap 𝕜 E 𝕜)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, (⊥ : WithTopBot 𝕜) < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[𝕜](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      ((C ∩ mixedConvexInequalitySolutionSet f g).Nonempty)
      (∃ w : (ι ⊕ κ) → 𝕜,
        w.IsNonnegativeZeroBoundCertificateOn C (mixedSystem f g) ∧
          ∃ i : ι, w (Sum.inl i) ≠ 0) := sorry

/-- Theorem 21.2 source-facing restatement. -/
theorem xor_strict_feasible_or_nonnegative_multiplier_certificate
    {C : Set E} (hC : Convex 𝕜 C)
    (f : ι → E → WithTopBot 𝕜) (g : κ → AffineMap 𝕜 E 𝕜)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_bot : ∀ i x, (⊥ : WithTopBot 𝕜) < f i x)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[𝕜](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      (∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0)
      (∃ wf : ι → 𝕜, ∃ wg : κ → 𝕜,
        (∀ i : ι, 0 ≤ wf i) ∧
        (∀ j : κ, 0 ≤ wg j) ∧
        (∃ i : ι, wf i ≠ 0) ∧
        ∀ x : C,
          (0 : WithTopBot 𝕜) ≤
            (∑ i, (wf i : WithTopBot 𝕜) * f i x) +
              ∑ j, (wg j : WithTopBot 𝕜) * Function.toWithTopBot (g j) x) := sorry

/-- Theorem 21.2 properness-form restatement on the owner mixed feasible set. -/
theorem
    xor_mixed_convexInequalitySolutionSet_nonempty_or_nonnegative_multiplier_certificate_of_proper
    {C : Set E} (hC : Convex 𝕜 C)
    (f : ι → E → WithTopBot 𝕜) (g : κ → AffineMap 𝕜 E 𝕜)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[𝕜](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      ((C ∩ mixedConvexInequalitySolutionSet f g).Nonempty)
      (∃ w : (ι ⊕ κ) → 𝕜,
        w.IsNonnegativeZeroBoundCertificateOn C (mixedSystem f g) ∧
          ∃ i : ι, w (Sum.inl i) ≠ 0) := sorry

/-- Theorem 21.2 properness-form source-facing restatement. -/
theorem xor_strict_feasible_or_nonnegative_multiplier_certificate_of_proper
    {C : Set E} (hC : Convex 𝕜 C)
    (f : ι → E → WithTopBot 𝕜) (g : κ → AffineMap 𝕜 E 𝕜)
    (hf_convex : ∀ i, ConvexOn 𝕜 C (f i))
    (hf_proper : ∀ i, (f i).IsProper)
    (hdom : ∀ i, ri[𝕜](C) ⊆ dom(f i))
    (hfeas_affine : ∃ x, x ∈ ri[𝕜](C) ∧ ∀ j, g j x ≤ 0) :
    Xor'
      (∃ x : E, x ∈ C ∧ (∀ i : ι, f i x < 0) ∧ ∀ j : κ, g j x ≤ 0)
      (∃ wf : ι → 𝕜, ∃ wg : κ → 𝕜,
        (∀ i : ι, 0 ≤ wf i) ∧
        (∀ j : κ, 0 ≤ wg j) ∧
        (∃ i : ι, wf i ≠ 0) ∧
        ∀ x : C,
          (0 : WithTopBot 𝕜) ≤
            (∑ i, (wf i : WithTopBot 𝕜) * f i x) +
              ∑ j, (wg j : WithTopBot 𝕜) * Function.toWithTopBot (g j) x) := sorry

end
