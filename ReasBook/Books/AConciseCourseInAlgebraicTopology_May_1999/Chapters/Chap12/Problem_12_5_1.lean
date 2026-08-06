import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- Semantic recall: mathlib provides `GradedObject.eulerChar` for graded `ModuleCat` objects,
-- so the source statement is best formalized as an additivity theorem for that canonical Euler
-- characteristic under the exactness pattern of a long exact sequence.

universe u v w x

open CategoryTheory

namespace GradedObject

variable {K : Type u} [Field K]

/-- The reindexed connecting morphism `V'' (i + 1) ⟶ V' i` associated to a degreewise family
`δ i : V'' i ⟶ V' (i - 1)`. -/
abbrev reindexedBoundary
    {V' V'' : CategoryTheory.GradedObject ℤ (ModuleCat K)}
    (δ : ∀ i : ℤ, V'' i ⟶ V' (i - 1)) (i : ℤ) :
    V'' (i + 1) ⟶ V' i :=
  (δ (i + 1)) ≫ eqToHom (congrArg V' (add_sub_cancel_right i 1))

/-- The degreewise exactness pattern of a long exact sequence of `ℤ`-graded vector spaces
`V' ⟶ V ⟶ V'' ⟶ V'[-1]`, written with the displayed connecting family
`δ i : V'' i ⟶ V' (i - 1)`. -/
class LongExactSequence
    {V' V V'' : CategoryTheory.GradedObject ℤ (ModuleCat K)}
    (f : ∀ i : ℤ, V' i ⟶ V i)
    (g : ∀ i : ℤ, V i ⟶ V'' i)
    (δ : ∀ i : ℤ, V'' i ⟶ V' (i - 1)) : Prop where
  /-- Exactness at `V i`. -/
  exact_f_g : ∀ i : ℤ, Function.Exact (f i) (g i)
  /-- Exactness at `V'' i`. -/
  exact_g_δ : ∀ i : ℤ, Function.Exact (g i) (δ i)
  /-- Exactness at `V' i`, using the reindexed connecting map
  `reindexedBoundary δ i : V'' (i + 1) ⟶ V' i`. -/
  exact_reindexedBoundary_f : ∀ i : ℤ, Function.Exact (reindexedBoundary δ i) (f i)

/-- Helper for Problem 12.5.1: exactness identifies the middle finite rank with the sum of the
finite ranks of the two adjacent images. -/
lemma finrank_eq_finrankRange_add_finrankRange_of_exact
    {M : Type v} {N : Type w} {P : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] [FiniteDimensional K N]
    (f : M →ₗ[K] N) (g : N →ₗ[K] P) (hfg : Function.Exact f g) :
    Module.finrank K N = Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
  -- Rank-nullity for `g` and exactness replace `ker g` by `range f`.
  calc
    Module.finrank K N
        = Module.finrank K (LinearMap.range g) + Module.finrank K (LinearMap.ker g) := by
            simpa [add_comm] using (LinearMap.finrank_range_add_finrank_ker g).symm
    _ = Module.finrank K (LinearMap.range g) + Module.finrank K (LinearMap.range f) := by
          rw [hfg.linearMap_ker_eq]
    _ = Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
          ac_rfl

/-- Helper for Problem 12.5.1: a linear map with zero-dimensional source has zero-dimensional
range. -/
lemma finrankRange_eq_zero_of_source_finrank_eq_zero
    {M : Type v} {N : Type w} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [FiniteDimensional K M] (f : M →ₗ[K] N) (hM : Module.finrank K M = 0) :
    Module.finrank K (LinearMap.range f) = 0 := by
  -- The range cannot have larger finite rank than the source.
  exact Nat.eq_zero_of_le_zero <| hM ▸ LinearMap.finrank_range_le f

/-- Helper for Problem 12.5.1: a linear map into a zero-dimensional target has zero-dimensional
range. -/
lemma finrankRange_eq_zero_of_target_finrank_eq_zero
    {M : Type v} {N : Type w} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [FiniteDimensional K N] (f : M →ₗ[K] N) (hN : Module.finrank K N = 0) :
    Module.finrank K (LinearMap.range f) = 0 := by
  -- The range sits inside the target, so it must vanish with the target.
  exact Nat.eq_zero_of_le_zero <| hN ▸ (LinearMap.range f).finrank_le

/-- Helper for Problem 12.5.1: multiplying the exact rank identity by an Euler sign gives the
degreewise summand rewrite used in the final finite sums. -/
lemma signedFinrank_eq_signedFinrankRange_add_signedFinrankRange_of_exact
    (s : ℤ) {M : Type v} {N : Type w} {P : Type x}
    [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup P] [Module K P] [FiniteDimensional K N]
    (f : M →ₗ[K] N) (g : N →ₗ[K] P) (hfg : Function.Exact f g) :
    s * Module.finrank K N =
      s * Module.finrank K (LinearMap.range f) + s * Module.finrank K (LinearMap.range g) := by
  -- Cast the exact rank formula to `ℤ` once, then distribute the sign.
  have hfg' : (Module.finrank K N : ℤ) =
      Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.range g) := by
    exact_mod_cast finrank_eq_finrankRange_add_finrankRange_of_exact (K := K) f g hfg
  calc
    s * Module.finrank K N
        = s * ((Module.finrank K (LinearMap.range f) : ℤ) + Module.finrank K (LinearMap.range g)) := by
            rw [hfg']
    _ = s * Module.finrank K (LinearMap.range f) + s * Module.finrank K (LinearMap.range g) := by
          ring

/-- Helper for Problem 12.5.1: the `eqToHom` used to reindex the connecting morphism preserves
the finite rank of its range. -/
lemma finrankRange_reindexedBoundary_eq
    {V' V'' : CategoryTheory.GradedObject ℤ (ModuleCat K)}
    (δ : ∀ i : ℤ, V'' i ⟶ V' (i - 1)) (i : ℤ) :
    Module.finrank K
        (LinearMap.range (reindexedBoundary δ i).hom) =
      Module.finrank K
        (LinearMap.range (δ (i + 1)).hom) := by
  -- Rewrite the transport as a map along an isomorphism and preserve the range finrank.
  let e : V' ((i + 1) - 1) = V' i := congrArg V' (add_sub_cancel_right i 1)
  unfold reindexedBoundary
  rw [ModuleCat.hom_comp, LinearMap.range_comp]
  simpa [e] using
    LinearEquiv.finrank_map_eq (f := (eqToIso e).toLinearEquiv) (p := LinearMap.range (δ (i + 1)).hom)

/-- Helper for Problem 12.5.1: shifting the index by `i ↦ i + 1` turns the signed
`reindexedBoundary` sum into the negative signed `δ` sum. -/
lemma sum_signedReindexedBoundary_eq_neg_sum_signedDelta_shift
    {V' V'' : CategoryTheory.GradedObject ℤ (ModuleCat K)}
    (δ : ∀ i : ℤ, V'' i ⟶ V' (i - 1)) (s : Finset ℤ) :
    ∑ i ∈ s, (((ComplexShape.up ℤ).χ i : ℤ) *
      Module.finrank K
        (LinearMap.range (reindexedBoundary δ i).hom)) =
      -∑ i ∈ s.image (fun i : ℤ => i + 1),
        (((ComplexShape.up ℤ).χ i : ℤ) *
          Module.finrank K (LinearMap.range (δ i).hom)) := by
  -- Reindex the sum so the transported boundary term is replaced by the original `δ`.
  calc
    ∑ i ∈ s, (((ComplexShape.up ℤ).χ i : ℤ) *
      Module.finrank K
        (LinearMap.range (reindexedBoundary δ i).hom))
      = ∑ j ∈ s.image (fun i : ℤ => i + 1),
          (((ComplexShape.up ℤ).χ (j - 1) : ℤ) *
            Module.finrank K
              (LinearMap.range (reindexedBoundary δ (j - 1)).hom)) := by
            refine Finset.sum_bijective (fun i : ℤ => i + 1) (Equiv.addRight 1).bijective ?_ ?_
            · intro i
              constructor
              · intro hi
                exact Finset.mem_image.mpr ⟨i, hi, by simp⟩
              · intro hi
                rcases Finset.mem_image.mp hi with ⟨j, hj, hji⟩
                have : j = i := by simpa using add_right_cancel hji
                simpa [this] using hj
            · intro i hi
              have hindex : i + 1 - 1 = i := add_sub_cancel_right i 1
              rw [hindex]
    _ = ∑ j ∈ s.image (fun i : ℤ => i + 1),
          (-((ComplexShape.up ℤ).χ j : ℤ)) *
            Module.finrank K (LinearMap.range (δ j).hom) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            have hsignForward : (((ComplexShape.up ℤ).χ j : ℤ)) =
                -((ComplexShape.up ℤ).χ (j - 1) : ℤ) := by
              have hj' : j = (j - 1) + 1 := by omega
              rw [hj']
              simpa [ComplexShape.χ] using
                congrArg (fun z : ℤˣ => (z : ℤ)) (Int.negOnePow_succ (j - 1))
            have hsign : (((ComplexShape.up ℤ).χ (j - 1) : ℤ)) =
                -((ComplexShape.up ℤ).χ j : ℤ) := by
              simpa [eq_comm] using congrArg Neg.neg hsignForward
            rw [hsign, finrankRange_reindexedBoundary_eq (K := K) (δ := δ) (i := j - 1)]
            rw [sub_add_cancel j 1]
    _ = ∑ j ∈ s.image (fun i : ℤ => i + 1),
          -((((ComplexShape.up ℤ).χ j : ℤ) *
            Module.finrank K (LinearMap.range (δ j).hom))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
    _ = -∑ j ∈ s.image (fun i : ℤ => i + 1),
          (((ComplexShape.up ℤ).χ j : ℤ) *
            Module.finrank K (LinearMap.range (δ j).hom)) := by
            rw [Finset.sum_neg_distrib]

/-- Problem 12.5.1. For a long exact sequence of finite-dimensional `ℤ`-graded vector spaces
`V' ⟶ V ⟶ V'' ⟶ (fun i ↦ V' (i - 1))`, the Euler characteristic is additive:
`χ(V) = χ(V') + χ(V'')`.

Here the graded pieces are modeled as objects of `ModuleCat K`, the long exactness is expressed
degreewise by `LongExactSequence f g δ`, and finiteness of Euler characteristic is encoded by
requiring the `finrankSupport` of each graded object to be finite. -/
theorem eulerChar_eq_add_of_longExact
    {V' V V'' : CategoryTheory.GradedObject ℤ (ModuleCat K)}
    (f : ∀ i : ℤ, V' i ⟶ V i)
    (g : ∀ i : ℤ, V i ⟶ V'' i)
    (δ : ∀ i : ℤ, V'' i ⟶ V' (i - 1))
    (h_exact : LongExactSequence f g δ)
    [∀ i : ℤ, FiniteDimensional K (V' i)]
    [∀ i : ℤ, FiniteDimensional K (V i)]
    [∀ i : ℤ, FiniteDimensional K (V'' i)]
    (h_supportV' : Set.Finite (finrankSupport V'))
    (h_supportV : Set.Finite (finrankSupport V))
    (h_supportV'' : Set.Finite (finrankSupport V'')) :
    eulerChar (ComplexShape.up ℤ) V =
      eulerChar (ComplexShape.up ℤ) V' + eulerChar (ComplexShape.up ℤ) V'' := by
  let sV' : Finset ℤ := h_supportV'.toFinset
  let sV : Finset ℤ := h_supportV.toFinset
  let sV'' : Finset ℤ := h_supportV''.toFinset
  let sδ : Finset ℤ := sV'.image (fun i : ℤ => i + 1)
  let U : Finset ℤ := ((sV ∪ sV') ∪ sV'') ∪ sδ
  let σ : ℤ → ℤ := fun i => ((ComplexShape.up ℤ).χ i : ℤ)
  let fLin : ∀ i : ℤ, V' i →ₗ[K] V i := fun i => (f i).hom
  let gLin : ∀ i : ℤ, V i →ₗ[K] V'' i := fun i => (g i).hom
  let deltaLin : ∀ i : ℤ, V'' i →ₗ[K] V' (i - 1) := fun i => (δ i).hom
  let boundaryLin : ∀ i : ℤ, V'' (i + 1) →ₗ[K] V' i := fun i => (reindexedBoundary δ i).hom
  let fTerm : ℤ → ℤ := fun i => σ i * Module.finrank K (LinearMap.range (fLin i))
  let gTerm : ℤ → ℤ := fun i => σ i * Module.finrank K (LinearMap.range (gLin i))
  let boundaryTerm : ℤ → ℤ := fun i =>
    σ i * Module.finrank K (LinearMap.range (boundaryLin i))
  let deltaTerm : ℤ → ℤ := fun i => σ i * Module.finrank K (LinearMap.range (deltaLin i))
  let F : ℤ := ∑ i ∈ U, fTerm i
  let G : ℤ := ∑ i ∈ U, gTerm i
  let B : ℤ := ∑ i ∈ U, boundaryTerm i
  let D : ℤ := ∑ i ∈ U, deltaTerm i
  have hEulerV :
      eulerChar (ComplexShape.up ℤ) V = ∑ i ∈ sV, σ i * Module.finrank K (V i) := by
    -- Reduce the Euler `finsum` to the finite support of `V`.
    simpa [sV, σ] using
      (GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
        (c := ComplexShape.up ℤ) V sV
        (by simpa [sV] using (Set.subset_rfl : finrankSupport V ⊆ finrankSupport V)))
  have hEulerV' :
      eulerChar (ComplexShape.up ℤ) V' = ∑ i ∈ sV', σ i * Module.finrank K (V' i) := by
    -- Reduce the Euler `finsum` to the finite support of `V'`.
    simpa [sV', σ] using
      (GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
        (c := ComplexShape.up ℤ) V' sV'
        (by simpa [sV'] using (Set.subset_rfl : finrankSupport V' ⊆ finrankSupport V')))
  have hEulerV'' :
      eulerChar (ComplexShape.up ℤ) V'' = ∑ i ∈ sV'', σ i * Module.finrank K (V'' i) := by
    -- Reduce the Euler `finsum` to the finite support of `V''`.
    simpa [sV'', σ] using
      (GradedObject.eulerChar_eq_sum_finSet_of_finrankSupport_subset
        (c := ComplexShape.up ℤ) V'' sV''
        (by simpa [sV''] using (Set.subset_rfl : finrankSupport V'' ⊆ finrankSupport V'')))
  have hEulerV_ranges :
      eulerChar (ComplexShape.up ℤ) V = ∑ i ∈ sV, fTerm i + ∑ i ∈ sV, gTerm i := by
    -- Exactness at `V i` splits each summand into the `f`- and `g`-image contributions.
    rw [hEulerV]
    calc
      ∑ i ∈ sV, σ i * Module.finrank K (V i)
          = ∑ i ∈ sV, (fTerm i + gTerm i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [σ, fTerm, gTerm] using
                signedFinrank_eq_signedFinrankRange_add_signedFinrankRange_of_exact
                  (K := K) (s := σ i) (f := fLin i) (g := gLin i) (hfg := h_exact.exact_f_g i)
      _ = ∑ i ∈ sV, fTerm i + ∑ i ∈ sV, gTerm i := by
            rw [Finset.sum_add_distrib]
  have hEulerV'_ranges :
      eulerChar (ComplexShape.up ℤ) V' = ∑ i ∈ sV', boundaryTerm i + ∑ i ∈ sV', fTerm i := by
    -- Exactness at `V' i` contributes the reindexed boundary range and the image of `f i`.
    rw [hEulerV']
    calc
      ∑ i ∈ sV', σ i * Module.finrank K (V' i)
          = ∑ i ∈ sV', (boundaryTerm i + fTerm i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [σ, boundaryTerm, fTerm] using
                signedFinrank_eq_signedFinrankRange_add_signedFinrankRange_of_exact
                  (K := K) (s := σ i) (f := boundaryLin i) (g := fLin i)
                  (hfg := h_exact.exact_reindexedBoundary_f i)
      _ = ∑ i ∈ sV', boundaryTerm i + ∑ i ∈ sV', fTerm i := by
            rw [Finset.sum_add_distrib]
  have hEulerV''_ranges :
      eulerChar (ComplexShape.up ℤ) V'' = ∑ i ∈ sV'', gTerm i + ∑ i ∈ sV'', deltaTerm i := by
    -- Exactness at `V'' i` contributes the image of `g i` and the image of `δ i`.
    rw [hEulerV'']
    calc
      ∑ i ∈ sV'', σ i * Module.finrank K (V'' i)
          = ∑ i ∈ sV'', (gTerm i + deltaTerm i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [σ, gTerm, deltaTerm] using
                signedFinrank_eq_signedFinrankRange_add_signedFinrankRange_of_exact
                  (K := K) (s := σ i) (f := gLin i) (g := deltaLin i) (hfg := h_exact.exact_g_δ i)
      _ = ∑ i ∈ sV'', gTerm i + ∑ i ∈ sV'', deltaTerm i := by
            rw [Finset.sum_add_distrib]
  have hsV_U : sV ⊆ U := by
    intro i hi
    simp [U, hi]
  have hsV'_U : sV' ⊆ U := by
    intro i hi
    simp [U, hi]
  have hsV''_U : sV'' ⊆ U := by
    intro i hi
    simp [U, hi]
  have hsδ_U : sδ ⊆ U := by
    intro i hi
    simp [U, hi]
  have hf_zero_of_not_mem_sV : ∀ i ∈ U, i ∉ sV → fTerm i = 0 := by
    intro i hiU hiV
    have hiSupport : i ∉ finrankSupport V := by
      simpa [sV] using hiV
    have hVzero : Module.finrank K (V i) = 0 := by
      simpa [GradedObject.finrankSupport] using hiSupport
    have hRangeZero : Module.finrank K (LinearMap.range (fLin i)) = 0 :=
      finrankRange_eq_zero_of_target_finrank_eq_zero (K := K) (f := fLin i) hVzero
    simp [fTerm, hRangeZero]
  have hf_zero_of_not_mem_sV' : ∀ i ∈ U, i ∉ sV' → fTerm i = 0 := by
    intro i hiU hiV'
    have hiSupport : i ∉ finrankSupport V' := by
      simpa [sV'] using hiV'
    have hV'zero : Module.finrank K (V' i) = 0 := by
      simpa [GradedObject.finrankSupport] using hiSupport
    have hRangeZero : Module.finrank K (LinearMap.range (fLin i)) = 0 :=
      finrankRange_eq_zero_of_source_finrank_eq_zero (K := K) (f := fLin i) hV'zero
    simp [fTerm, hRangeZero]
  have hg_zero_of_not_mem_sV : ∀ i ∈ U, i ∉ sV → gTerm i = 0 := by
    intro i hiU hiV
    have hiSupport : i ∉ finrankSupport V := by
      simpa [sV] using hiV
    have hVzero : Module.finrank K (V i) = 0 := by
      simpa [GradedObject.finrankSupport] using hiSupport
    have hRangeZero : Module.finrank K (LinearMap.range (gLin i)) = 0 :=
      finrankRange_eq_zero_of_source_finrank_eq_zero (K := K) (f := gLin i) hVzero
    simp [gTerm, hRangeZero]
  have hg_zero_of_not_mem_sV'' : ∀ i ∈ U, i ∉ sV'' → gTerm i = 0 := by
    intro i hiU hiV''
    have hiSupport : i ∉ finrankSupport V'' := by
      simpa [sV''] using hiV''
    have hV''zero : Module.finrank K (V'' i) = 0 := by
      simpa [GradedObject.finrankSupport] using hiSupport
    have hRangeZero : Module.finrank K (LinearMap.range (gLin i)) = 0 :=
      finrankRange_eq_zero_of_target_finrank_eq_zero (K := K) (f := gLin i) hV''zero
    simp [gTerm, hRangeZero]
  have hBoundary_zero_of_not_mem_sV' : ∀ i ∈ U, i ∉ sV' → boundaryTerm i = 0 := by
    intro i hiU hiV'
    have hiSupport : i ∉ finrankSupport V' := by
      simpa [sV'] using hiV'
    have hV'zero : Module.finrank K (V' i) = 0 := by
      simpa [GradedObject.finrankSupport] using hiSupport
    have hRangeZero : Module.finrank K (LinearMap.range (boundaryLin i)) = 0 :=
      finrankRange_eq_zero_of_target_finrank_eq_zero (K := K) (f := boundaryLin i) hV'zero
    simp [boundaryTerm, hRangeZero]
  have hDelta_zero_of_not_mem_sV'' : ∀ i ∈ U, i ∉ sV'' → deltaTerm i = 0 := by
    intro i hiU hiV''
    have hiSupport : i ∉ finrankSupport V'' := by
      simpa [sV''] using hiV''
    have hV''zero : Module.finrank K (V'' i) = 0 := by
      simpa [GradedObject.finrankSupport] using hiSupport
    have hRangeZero : Module.finrank K (LinearMap.range (deltaLin i)) = 0 :=
      finrankRange_eq_zero_of_source_finrank_eq_zero (K := K) (f := deltaLin i) hV''zero
    simp [deltaTerm, hRangeZero]
  have hDelta_zero_of_not_mem_sδ : ∀ i ∈ U, i ∉ sδ → deltaTerm i = 0 := by
    intro i hiU hiδ
    have hiShift : i - 1 ∉ sV' := by
      intro hiV'
      exact hiδ <| Finset.mem_image.mpr ⟨i - 1, hiV', by omega⟩
    have hiSupport : i - 1 ∉ finrankSupport V' := by
      simpa [sV'] using hiShift
    have hV'zero : Module.finrank K (V' (i - 1)) = 0 := by
      simpa [GradedObject.finrankSupport] using hiSupport
    have hBoundaryZero :
        Module.finrank K (LinearMap.range (boundaryLin (i - 1))) = 0 :=
      finrankRange_eq_zero_of_target_finrank_eq_zero
        (K := K) (f := boundaryLin (i - 1)) hV'zero
    have hBridge :
        Module.finrank K (LinearMap.range (boundaryLin (i - 1))) =
          Module.finrank K (LinearMap.range (deltaLin i)) := by
      have hBridge₀ :
          Module.finrank K (LinearMap.range (boundaryLin (i - 1))) =
            Module.finrank K (LinearMap.range (δ (i - 1 + 1)).hom) := by
        simpa [boundaryLin] using
          (finrankRange_reindexedBoundary_eq (K := K) (δ := δ) (i := i - 1))
      have hDeltaIndex :
          Module.finrank K (LinearMap.range (δ (i - 1 + 1)).hom) =
            Module.finrank K (LinearMap.range (deltaLin i)) := by
        have hi' : i - 1 + 1 = i := sub_add_cancel i 1
        simpa [deltaLin] using
          congrArg (fun j : ℤ => Module.finrank K (LinearMap.range (δ j).hom)) hi'
      calc
        Module.finrank K (LinearMap.range (boundaryLin (i - 1)))
            = Module.finrank K (LinearMap.range (δ (i - 1 + 1)).hom) := hBridge₀
        _ = Module.finrank K (LinearMap.range (deltaLin i)) := hDeltaIndex
    have hRangeZero : Module.finrank K (LinearMap.range (deltaLin i)) = 0 := by
      rw [← hBridge]
      exact hBoundaryZero
    simp [deltaTerm, hRangeZero]
  have hF_from_sV : ∑ i ∈ sV, fTerm i = F := by
    -- The `f`-image contribution is supported inside the finite set `U`.
    simp [F]
    exact Finset.sum_subset hsV_U hf_zero_of_not_mem_sV
  have hF_from_sV' : ∑ i ∈ sV', fTerm i = F := by
    -- The same `f`-image contribution can be expanded from the `V'` support to `U`.
    simp [F]
    exact Finset.sum_subset hsV'_U hf_zero_of_not_mem_sV'
  have hG_from_sV : ∑ i ∈ sV, gTerm i = G := by
    -- The `g`-image contribution can be expanded from the `V` support to `U`.
    simp [G]
    exact Finset.sum_subset hsV_U hg_zero_of_not_mem_sV
  have hG_from_sV'' : ∑ i ∈ sV'', gTerm i = G := by
    -- The same `g`-image contribution can be expanded from the `V''` support to `U`.
    simp [G]
    exact Finset.sum_subset hsV''_U hg_zero_of_not_mem_sV''
  have hBoundary_from_sV' : ∑ i ∈ sV', boundaryTerm i = B := by
    -- The reindexed boundary term vanishes away from the support of `V'`.
    simp [B]
    exact Finset.sum_subset hsV'_U hBoundary_zero_of_not_mem_sV'
  have hDelta_from_sV'' : ∑ i ∈ sV'', deltaTerm i = D := by
    -- The connecting-map image vanishes away from the support of `V''`.
    simp [D]
    exact Finset.sum_subset hsV''_U hDelta_zero_of_not_mem_sV''
  have hDelta_from_sδ : ∑ i ∈ sδ, deltaTerm i = D := by
    -- The same connecting contribution is also supported on the shifted support of `V'`.
    simp [D]
    exact Finset.sum_subset hsδ_U hDelta_zero_of_not_mem_sδ
  have hBoundaryShift :
      ∑ i ∈ sV', boundaryTerm i = -∑ i ∈ sδ, deltaTerm i := by
    -- Reindexing by one step converts the boundary sum into the negative `δ` sum.
    simpa [sδ, σ, boundaryTerm, deltaTerm] using
      sum_signedReindexedBoundary_eq_neg_sum_signedDelta_shift (K := K) (δ := δ) sV'
  have hBoundary_eq_neg_delta : B = -D := by
    -- Compare both sides on their natural support finsets, then enlarge to `U`.
    calc
      B = ∑ i ∈ sV', boundaryTerm i := by symm; exact hBoundary_from_sV'
      _ = -∑ i ∈ sδ, deltaTerm i := hBoundaryShift
      _ = -D := by rw [hDelta_from_sδ]
  have hEulerV_U : eulerChar (ComplexShape.up ℤ) V = F + G := by
    -- Gather the `V` contribution on the common finite set `U`.
    rw [hEulerV_ranges, hF_from_sV, hG_from_sV]
  have hEulerV'_U : eulerChar (ComplexShape.up ℤ) V' = B + F := by
    -- Gather the `V'` contribution on the common finite set `U`.
    rw [hEulerV'_ranges, hBoundary_from_sV', hF_from_sV']
  have hEulerV''_U : eulerChar (ComplexShape.up ℤ) V'' = G + D := by
    -- Gather the `V''` contribution on the common finite set `U`.
    rw [hEulerV''_ranges, hG_from_sV'', hDelta_from_sV'']
  -- Route correction: the proof closes by finite-support bookkeeping and a single shifted
  -- boundary cancellation, rather than by building an auxiliary complex.
  calc
    eulerChar (ComplexShape.up ℤ) V = F + G := hEulerV_U
    _ = (B + F) + (G + D) := by
          rw [hBoundary_eq_neg_delta]
          ring
    _ = eulerChar (ComplexShape.up ℤ) V' + eulerChar (ComplexShape.up ℤ) V'' := by
          rw [hEulerV'_U, hEulerV''_U]

end GradedObject
