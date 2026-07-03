import Mathlib
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_6_5_1 (from Chap02) -/
open scoped Rockafellar

section IntrinsicInterior

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.5.1 states that if an affine set `M` meets the relative interior of
  a convex set `C`, then intersecting `C` with `M` preserves both relative interior and closure.
- `core/canonical`: the owner notions are `intrinsicInterior 𝕜`, `intrinsicClosure 𝕜`,
  `closure`, `Convex 𝕜`, and the affine-set owner object `AffineSubspace 𝕜 E`.
- `bridge/view`: Rockafellar's `ri` is formalized by notation `ri[𝕜](·)` over
  `intrinsicInterior 𝕜`; the textbook affine set `M` is represented canonically by an affine
  subspace and then coerced to a set.
- Primitive data vs derived API: the affine subspace `M` and convex set `C` are the input data,
  while the relative-interior and closure identities are derived geometric facts.
- Domain-style sampling used here: the chapter owner theorems
  `Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior`,
  `Convex.intrinsicClosure_iInter_eq_iInter_intrinsicClosure`, and the bridge
  `intrinsicClosure_eq_closure`.
- Layer target: this item stays `source-facing`, but both displayed identities are thin affine
  specializations of the owner theorems from Theorem 6.5 rather than parallel local reproofs.
-/

namespace AffineSubspace

/-- Corollary 6.5.1 (1): if an affine set `M` meets the relative interior of a convex set `C`,
then the relative interior of `M ∩ C` is exactly `M ∩ ri[𝕜](C)`. -/
-- Proof sketch: view relative interior as `ri`. Because `M` meets
-- `ri C`, the affine spans of `M ∩ C` and `M ∩ ri C` agree with
-- the affine section cut out by `M`, and the intrinsic interior inside that affine section reduces
-- to ordinary interior in the subtype corresponding to `M`.
theorem intrinsicInterior_inter_eq (M : AffineSubspace 𝕜 E) {C : Set E} [FiniteDimensional 𝕜 E]
    (hC : Convex 𝕜 C)
    (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty) :
    ri[𝕜]((M : Set E) ∩ C) = (M : Set E) ∩ ri[𝕜](C) := by
  have hMri : ri[𝕜]((M : Set E)) = (M : Set E) := M.intrinsicInterior_coe
  let D : Bool → Set E := fun b ↦ cond b (M : Set E) C
  have hDconv : ∀ b : Bool, Convex 𝕜 (D b) := by
    intro b
    cases b
    · simpa [D] using hC
    · simpa [D] using M.convex
  have hDri : (⋂ b : Bool, ri[𝕜](D b)).Nonempty := by
    rcases hri with ⟨x, hxM, hxC⟩
    refine ⟨x, Set.mem_iInter.2 fun b ↦ ?_⟩
    cases b
    · simpa [D] using hxC
    · simpa [D, hMri] using hxM
  calc
    ri[𝕜]((M : Set E) ∩ C) = ri[𝕜](⋂ b : Bool, D b) := by
      rw [Set.inter_eq_iInter]
    _ = ⋂ b : Bool, ri[𝕜](D b) := by
      simpa [D] using Convex.intrinsicInterior_iInter_eq_iInter_intrinsicInterior hDconv hDri
    _ = (M : Set E) ∩ ri[𝕜](C) := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · simpa [D, hMri] using (Set.mem_iInter.1 hx) true
        · simpa [D] using (Set.mem_iInter.1 hx) false
      · rintro ⟨hxM, hxC⟩
        refine Set.mem_iInter.2 fun b ↦ ?_
        cases b
        · simpa [D] using hxC
        · simpa [D, hMri] using hxM

end AffineSubspace

end IntrinsicInterior

section IntrinsicClosure

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

namespace AffineSubspace

/-- Intrinsic-closure companion to Corollary 6.5.1: if an affine set `M` meets `ri[𝕜](C)` for a
convex set `C`, then the intrinsic closure of `M ∩ C` is exactly
`M ∩ cl[𝕜](C)`. -/
theorem intrinsicClosure_inter_eq (M : AffineSubspace 𝕜 E) {C : Set E} (hC : Convex 𝕜 C)
    (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty) :
    cl[𝕜]((M : Set E) ∩ C) = (M : Set E) ∩ cl[𝕜](C) := by
  have hMri : ri[𝕜]((M : Set E)) = (M : Set E) := M.intrinsicInterior_coe
  have hMicl : cl[𝕜]((M : Set E)) = (M : Set E) := M.intrinsicClosure_coe
  let D : Bool → Set E := fun b ↦ cond b (M : Set E) C
  have hDconv : ∀ b : Bool, Convex 𝕜 (D b) := by
    intro b
    cases b
    · simpa [D] using hC
    · simpa [D] using M.convex
  have hDri : (⋂ b : Bool, ri[𝕜](D b)).Nonempty := by
    rcases hri with ⟨x, hxM, hxC⟩
    refine ⟨x, Set.mem_iInter.2 fun b ↦ ?_⟩
    cases b
    · simpa [D] using hxC
    · simpa [D, hMri] using hxM
  calc
    cl[𝕜]((M : Set E) ∩ C) = cl[𝕜](⋂ b : Bool, D b) := by
      rw [Set.inter_eq_iInter]
    _ = ⋂ b : Bool, cl[𝕜](D b) := by
      simpa [D] using Convex.intrinsicClosure_iInter_eq_iInter_intrinsicClosure hDconv hDri
    _ = (M : Set E) ∩ cl[𝕜](C) := by
      ext x
      constructor
      · intro hx
        refine ⟨?_, ?_⟩
        · simpa [D, hMicl] using (Set.mem_iInter.1 hx) true
        · simpa [D] using (Set.mem_iInter.1 hx) false
      · rintro ⟨hxM, hxC⟩
        refine Set.mem_iInter.2 fun b ↦ ?_
        cases b
        · simpa [D] using hxC
        · simpa [D, hMicl] using hxM

end AffineSubspace

end IntrinsicClosure

section ClosureIsClosedAffineSpan

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

namespace AffineSubspace

/-- Primitive ambient-closure form of Corollary 6.5.1 (2): if an affine set `M` meets
`ri[𝕜](C)` for a convex set `C`, and the affine hulls `aff[𝕜] C` and `aff[𝕜] (M ∩ C)` are closed,
then
`closure (M ∩ C) = M ∩ closure C`. -/
theorem closure_inter_eq_of_isClosed_affineSpan (M : AffineSubspace 𝕜 E) {C : Set E}
    (hC : Convex 𝕜 C) (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty)
    (hclosedC : IsClosed (aff[𝕜] C : Set E))
    (hclosedInter : IsClosed (aff[𝕜] ((M : Set E) ∩ C) : Set E)) :
    closure ((M : Set E) ∩ C) = (M : Set E) ∩ closure C := by
  have hclInter :
      cl[𝕜]((M : Set E) ∩ C) = closure ((M : Set E) ∩ C) :=
    Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan
      (hclosed := hclosedInter)
  have hclC : cl[𝕜](C) = closure C :=
    Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan
      (hclosed := hclosedC)
  calc
    closure ((M : Set E) ∩ C) = cl[𝕜]((M : Set E) ∩ C) := by
      exact hclInter.symm
    _ = (M : Set E) ∩ cl[𝕜](C) := M.intrinsicClosure_inter_eq hC hri
    _ = (M : Set E) ∩ closure C := by simp [hclC]

end AffineSubspace

end ClosureIsClosedAffineSpan

section Closure

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T1Space E]

namespace AffineSubspace

/-- Corollary 6.5.1 (2), ambient-closure form on the finite-direction affine-hull layer:
if an affine set `M` meets `ri[𝕜](C)` for a convex set `C`, and `aff[𝕜] C` has
finite-dimensional direction, then `closure (M ∩ C) = M ∩ closure C`. -/
theorem closure_inter_eq (M : AffineSubspace 𝕜 E) {C : Set E} (hC : Convex 𝕜 C)
    (hri : ((M : Set E) ∩ ri[𝕜](C)).Nonempty)
    [FiniteDimensional 𝕜 (aff[𝕜] C).direction] :
    closure ((M : Set E) ∩ C) = (M : Set E) ∩ closure C := by
  have hfd_inter : FiniteDimensional 𝕜 (aff[𝕜] ((M : Set E) ∩ C)).direction :=
    Submodule.finiteDimensional_of_le <|
      AffineSubspace.direction_le <|
        affineSpan_mono 𝕜 (Set.inter_subset_right : ((M : Set E) ∩ C) ⊆ C)
  exact M.closure_inter_eq_of_isClosed_affineSpan hC hri
    (Set.isClosed_affineSpan (C := C))
    (Set.isClosed_affineSpan
      (C := ((M : Set E) ∩ C)))

end AffineSubspace

end Closure

/-! ### Corollary_6_5_2 (from Chap02) -/
section

open scoped Rockafellar

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 6.5.2 says that if `C₂` lies in `closure C₁` but is not entirely
  contained in the relative boundary of a convex set `C₁`, then the relative interior of `C₂`
  is contained in the relative interior of `C₁`. The source also states `C₂` convex, but that
  hypothesis is redundant for the owner-form inclusion.
- `core/canonical`: the owner notions are `Convex 𝕜`, `closure`,
  `intrinsicInterior 𝕜`, `intrinsicClosure 𝕜`, and `intrinsicFrontier 𝕜`, together with the
  affine-owner object `AffineSubspace 𝕜 E`; the public theorem should therefore live on the
  `Convex` owner surface, with the chapter notation `ri[𝕜](C)` and `rb[𝕜](C)` and with
  `intrinsicClosure 𝕜 C`
  used on theorem surfaces.
- `bridge/view`: Rockafellar's relative interior and relative boundary are represented on the
  chapter theorem surface by `ri[𝕜](C)` and `rb[𝕜](C)`, over the canonical owners
  `intrinsicInterior 𝕜` and `intrinsicFrontier 𝕜`.
- Domain-style sampling: the relevant canonical/project declarations are `intrinsicFrontier`,
  `intrinsicClosure_diff_intrinsicFrontier`, the chapter bridge
  `mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset`, the
  affine-hull control theorems `subset_affineSpan` and `affineSpan_intrinsicClosure`, together
  with the affine-owner section formulas `AffineSubspace.intrinsicInterior_inter_eq` and
  `AffineSubspace.intrinsicClosure_inter_eq`.
- Primitive data vs derived API: the primitive input data is the convex owner `hC₁`, the
  relative-closure inclusion `C₂ ⊆ intrinsicClosure 𝕜 C₁`, and the witness-level condition
  `(C₂ ∩ ri[𝕜](C₁)).Nonempty`; the source hypothesis
  `¬ C₂ ⊆ rb[𝕜](C₁)` is then a thin bridge to this primitive layer.
- Layer target: this item is `source-facing`, stated directly in the canonical
  `intrinsicInterior`/`intrinsicFrontier` language on the chapter's ambient finite-dimensional
  ordered-complete nontrivially normed-field owner layer, and organized as a `Convex` owner
  theorem.
-/

namespace Convex

/-- Primitive intrinsic-closure owner form for Corollary 6.5.2: if `C₂` lies in
`intrinsicClosure 𝕜 C₁` and `C₂` meets `ri[𝕜](C₁)`, then `ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
-- Proof sketch: choose `x ∈ C₂ ∩ ri[𝕜](C₁)`. Let
-- `M = affineSpan 𝕜 C₂` and `S = M ∩ C₁`. Then `x ∈ M ∩ ri[𝕜](C₁)`, so
-- Corollary 6.5.1 yields
-- the owner identities `ri[𝕜](S) = M ∩ ri[𝕜](C₁)` and
-- `intrinsicClosure 𝕜 S = M ∩ intrinsicClosure 𝕜 C₁`. Hence
-- `C₂ ⊆ intrinsicClosure 𝕜 S`, while `intrinsicClosure 𝕜 S` has affine span `M`.
-- If `z ∈ ri[𝕜](C₂)`, the relative-interior neighborhood criterion gives a closed
-- ball in `M` around `z` contained in `C₂`, hence in `intrinsicClosure 𝕜 S`, so the same
-- criterion puts `z ∈ ri[𝕜](intrinsicClosure 𝕜 S) = ri[𝕜](S)`. Unwinding the
-- affine-owner identity for `ri[𝕜](S)` gives `z ∈ ri[𝕜](C₁)`.
theorem ri_subset_ri_of_subset_intrinsicClosure
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hsubset : C₂ ⊆ intrinsicClosure 𝕜 C₁)
    (hinter : (C₂ ∩ ri[𝕜](C₁)).Nonempty) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  rcases hinter with ⟨x, hx₂, hx₁⟩
  let M : AffineSubspace 𝕜 E := affineSpan 𝕜 C₂
  let S : Set E := (M : Set E) ∩ C₁
  have hxM : x ∈ (M : Set E) := by
    simpa [M] using subset_affineSpan 𝕜 C₂ hx₂
  have hMri : ((M : Set E) ∩ ri[𝕜](C₁)).Nonempty := ⟨x, hxM, hx₁⟩
  have hSconv : Convex 𝕜 S := by
    simpa [S] using M.convex.inter hC₁
  have hScl : intrinsicClosure 𝕜 S = (M : Set E) ∩ intrinsicClosure 𝕜 C₁ := by
    simpa [S] using M.intrinsicClosure_inter_eq hC₁ hMri
  have hSri : ri[𝕜](S) = (M : Set E) ∩ ri[𝕜](C₁) := by
    simpa [S] using M.intrinsicInterior_inter_eq hC₁ hMri
  have hC₂_clS : C₂ ⊆ intrinsicClosure 𝕜 S := by
    intro z hz
    have hzM : z ∈ (M : Set E) := by
      simpa [M] using subset_affineSpan 𝕜 C₂ hz
    rw [hScl]
    exact ⟨hzM, hsubset hz⟩
  have hspan_clS : affineSpan 𝕜 (intrinsicClosure 𝕜 S) = M := by
    refine le_antisymm ?_ ?_
    · rw [affineSpan_intrinsicClosure]
      exact affineSpan_le_of_subset_coe fun _ hz ↦ hz.1
    · change affineSpan 𝕜 C₂ ≤ affineSpan 𝕜 (intrinsicClosure 𝕜 S)
      exact affineSpan_le_of_subset_coe fun z hz ↦
        subset_affineSpan 𝕜 (intrinsicClosure 𝕜 S) (hC₂_clS hz)
  intro z hz
  obtain ⟨_, ε, hε, hzball⟩ :=
    (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).1 hz
  have hz_clS : z ∈ ri[𝕜](intrinsicClosure 𝕜 S) := by
    refine
      (mem_ri_iff_mem_affineSpan_and_exists_pos_closedBall_inter_subset).2
        ⟨subset_affineSpan 𝕜 (intrinsicClosure 𝕜 S)
          (hC₂_clS (intrinsicInterior_subset hz)), ε, hε, ?_⟩
    intro y hy
    exact hC₂_clS <| hzball <| by
      refine ⟨hy.1, ?_⟩
      have hyM : y ∈ (M : Set E) := hspan_clS ▸ hy.2
      simpa [M] using hyM
  have hzS : z ∈ ri[𝕜](S) := by
    rw [← hSconv.ri_intrinsicClosure_eq_ri]
    exact hz_clS
  have hzSri : z ∈ (M : Set E) ∩ ri[𝕜](C₁) := by
    simpa [hSri] using hzS
  exact hzSri.2

/-- Corollary 6.5.2, intrinsic-closure source form: if a convex set `C₁`
satisfies `C₂ ⊆ intrinsicClosure 𝕜 C₁` and `C₂` is not contained in the
relative boundary `rb[𝕜](C₁)`, then `ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
theorem ri_subset_ri_of_subset_intrinsicClosure_of_not_subset_rb
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hsubset : C₂ ⊆ intrinsicClosure 𝕜 C₁)
    (hnot_frontier : ¬ C₂ ⊆ rb[𝕜](C₁)) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  have hinter : (C₂ ∩ ri[𝕜](C₁)).Nonempty := by
    rcases Set.not_subset.mp hnot_frontier with ⟨x, hx₂, hxnot_frontier⟩
    have hxri : x ∈ intrinsicClosure 𝕜 C₁ \ rb[𝕜](C₁) := ⟨hsubset hx₂, hxnot_frontier⟩
    exact ⟨x, hx₂, by simpa [intrinsicClosure_diff_intrinsicFrontier] using hxri⟩
  exact ri_subset_ri_of_subset_intrinsicClosure hC₁ hsubset hinter

/-- Primitive ambient-closure bridge for Corollary 6.5.2: once intrinsic closure agrees with
ambient closure for `C₁`, the source-facing closure hypothesis yields
`ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
theorem ri_subset_ri_of_subset_closure_of_not_subset_rb_of_intrinsicClosure_eq_closure
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hclosure : intrinsicClosure 𝕜 C₁ = closure C₁)
    (hsubset : C₂ ⊆ closure C₁) (hnot_frontier : ¬ C₂ ⊆ rb[𝕜](C₁)) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  have hsubset' : C₂ ⊆ intrinsicClosure 𝕜 C₁ := by
    intro x hx
    rw [hclosure]
    exact hsubset hx
  exact ri_subset_ri_of_subset_intrinsicClosure_of_not_subset_rb
    hC₁ hsubset' hnot_frontier

/-- Corollary 6.5.2, ambient-closure bridge: if `C₂ ⊆ closure C₁` and `C₂` is not
contained in the relative boundary `rb[𝕜](C₁)`, then `ri[𝕜](C₂) ⊆ ri[𝕜](C₁)`. -/
theorem ri_subset_ri_of_subset_closure_of_not_subset_rb
    {C₁ C₂ : Set E} (hC₁ : Convex 𝕜 C₁) (hsubset : C₂ ⊆ closure C₁)
    (hnot_frontier : ¬ C₂ ⊆ rb[𝕜](C₁)) :
    ri[𝕜](C₂) ⊆ ri[𝕜](C₁) := by
  exact ri_subset_ri_of_subset_closure_of_not_subset_rb_of_intrinsicClosure_eq_closure
    hC₁ (intrinsicClosure_eq_closure 𝕜 C₁) hsubset hnot_frontier

end Convex

end

/-! ### Text_6_5 (from Chap02) -/
open Metric
open scoped Pointwise Rockafellar

section

variable {𝕜 : Type*} [NormedDivisionRing 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E] [NormSMulClass 𝕜 E]

/-- Canonical scalar-generic bridge: a closed ball of radius `‖c‖` is a translate of a scalar
multiple of the unit closed ball owner `B`. -/
theorem closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a : E) {c : 𝕜} (hc : c ≠ 0) :
    closedBall a ‖c‖ = a +ᵥ (c • (B : Set E)) := by
  have hsmul :
      closedBall (0 : E) ‖c‖ = c • (B : Set E) := by
    ext x
    constructor
    · intro hx
      refine ⟨c⁻¹ • x, ?_, by simp [smul_smul, hc]⟩
      rw [Metric.mem_closedBall] at hx ⊢
      have hdist : dist x (0 : E) = ‖c‖ * dist (c⁻¹ • x) (0 : E) := by
        simpa [smul_smul, hc] using (dist_smul₀ c (c⁻¹ • x) (0 : E))
      have hmul : ‖c‖ * dist (c⁻¹ • x) (0 : E) ≤ ‖c‖ * (1 : ℝ) := by
        calc
          ‖c‖ * dist (c⁻¹ • x) (0 : E) = dist x (0 : E) := hdist.symm
          _ ≤ ‖c‖ := hx
          _ = ‖c‖ * (1 : ℝ) := by simp
      have hcnorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
      have hdist_nonneg : 0 ≤ dist (c⁻¹ • x) (0 : E) := dist_nonneg
      nlinarith
    · rintro ⟨y, hy, rfl⟩
      rw [Metric.mem_closedBall] at hy ⊢
      calc
        dist (c • y) (0 : E) = ‖c‖ * dist y (0 : E) := by
          simpa using (dist_smul₀ c y (0 : E))
        _ ≤ ‖c‖ * (1 : ℝ) := by gcongr
        _ = ‖c‖ := by simp
  calc
    closedBall a ‖c‖ = a +ᵥ closedBall (0 : E) ‖c‖ := by
      exact (vadd_closedBall_zero (x := a) (δ := ‖c‖)).symm
    _ = a +ᵥ (c • (B : Set E)) := by rw [hsmul]

/-- Canonical scalar-generic bridge with intrinsic invertibility witness:
for a unit scalar `u : 𝕜ˣ`, the closed ball of radius `‖u‖` is `a + u • B`. -/
theorem closedBall_eq_add_smul_unitClosedBall_unit (a : E) (u : 𝕜ˣ) :
    closedBall a ‖(u : 𝕜)‖ = a +ᵥ ((u : 𝕜) • (B : Set E)) := by
  simpa using
    (closedBall_eq_add_smul_unitClosedBall_of_ne_zero
      (a := a) (c := (u : 𝕜)) u.ne_zero)

/-- Canonical scalar-generic owner bridge: for any scalar `c`, the closed ball of radius `‖c‖`
is the translate-dilate `a + c • B`. The endpoint `c = 0` needs separation (`T1Space`) so that
`closedBall a 0 = {a}`. -/
theorem closedBall_eq_add_smul_unitClosedBall [T1Space E] (a : E) (c : 𝕜) :
    closedBall a ‖c‖ = a +ᵥ (c • (B : Set E)) := by
  by_cases hc : c = 0
  · subst hc
    ext x
    simp [Metric.closedBall_zero', Set.mem_vadd_set, eq_comm]
  · exact closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := a) (c := c) hc

end

section

variable {E : Type*} [SeminormedAddCommGroup E] [Module ℝ E] [NormSMulClass ℝ E]

/-
Source/core/bridge triage:
- `source-facing`: Text 6.5 describes the closed ball centered at `a` with radius `ε` as both the
  translated norm-sublevel set `{a + y | ‖y‖ ≤ ε}` and the translate/dilate `a + ε B` of the unit
  ball.
- `core/canonical`: the owner abstraction is the metric closed ball `closedBall a ε`.
- `bridge/view`: the intrinsic translation presentations
  `a +ᵥ (ε • B)` and `a +ᵥ {y : E | ‖y‖ ≤ ε}` are bridge views of the same owner object.
- Primitive data vs derived API: the primitive inputs are the center `a` and radius `ε`; the
  translated-unit-ball and translated-sublevel descriptions are derived API.
- Domain-style sampling: `closedBall`, `Metric.mem_closedBall`, `mem_closedBall_zero_iff`,
  `smul_closedBall'`, `vadd_closedBall_zero`, and `Metric.closedBall_zero'`.
- Layer target: `bridge/view`, keeping `closedBall` as owner and expressing the textbook forms as
  thin companion theorems.
-/

/-- Text 6.5, owner bridge for positive radii: a closed ball is the translate and dilation of the
unit closed ball, written in pointwise-set form. -/
theorem closedBall_eq_add_smul_unitClosedBall_of_pos (a : E) {ε : ℝ} (hε : 0 < ε) :
    closedBall a ε = a +ᵥ (ε • (B : Set E)) := by
  simpa [Real.norm_of_nonneg hε.le] using
    (closedBall_eq_add_smul_unitClosedBall_of_ne_zero (a := a) (c := ε) hε.ne')

/-- Text 6.5, owner bridge: a closed ball is the translate and dilation of the unit closed ball,
written in pointwise-set form. The `ε = 0` endpoint needs separation (`T1Space`) so that
`closedBall a 0 = {a}`. -/
theorem closedBall_eq_add_smul_unitClosedBall_of_nonneg [T1Space E] (a : E) {ε : ℝ} (hε : 0 ≤ ε) :
    closedBall a ε = a +ᵥ (ε • (B : Set E)) := by
  simpa [Real.norm_of_nonneg hε] using
    (closedBall_eq_add_smul_unitClosedBall (a := a) (c := ε))

/- The metric set-builder presentation `closedBall a ε = {x | dist x a ≤ ε}` is already the
canonical owner API `Metric.mem_closedBall`, so no parallel wrapper theorem is introduced here. -/
recall Metric.mem_closedBall

end

section

variable {E : Type*} [PseudoMetricSpace E] [AddGroup E] [IsIsometricVAdd E E]

/-- A closed ball is the translate of the zero-centered closed ball by `a`. -/
theorem closedBall_eq_vadd_closedBall_zero (a : E) (ε : ℝ) :
    closedBall a ε = a +ᵥ closedBall (0 : E) ε := by
  calc
    closedBall a ε = closedBall ((IsometryEquiv.addLeft a) 0) ε := by
      simp
    _ = ((IsometryEquiv.addLeft a : E → E) '' closedBall (0 : E) ε) := by
      exact ((IsometryEquiv.addLeft a).image_closedBall (0 : E) ε).symm
    _ = a +ᵥ closedBall (0 : E) ε := by
      rfl

end

section

variable {E : Type*} [SeminormedAddGroup E]

/-- A closed ball is the translate by `a` of the norm sublevel set `{y | ‖y‖ ≤ ε}`. -/
-- Proof sketch: this is the translation-isometry owner theorem
-- `closedBall_eq_vadd_closedBall_zero`, with the zero-centered closed ball identified with
-- its canonical norm-sublevel presentation via `mem_closedBall_zero_iff`.
theorem closedBall_eq_vadd_norm_sublevel (a : E) (ε : ℝ) :
    closedBall a ε = a +ᵥ {y : E | ‖y‖ ≤ ε} := by
  rw [closedBall_eq_vadd_closedBall_zero (a := a) (ε := ε)]
  congr 1
  ext y
  simp

end

/-! ### Theorem_6_5 (from Chap02) -/
open scoped Rockafellar

section IntrinsicClosure

local notation "cl[" 𝕜 "](" C ")" => intrinsicClosure 𝕜 C

variable {ι 𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

/-
Source/core/bridge triage:
- `source-facing`: Theorem 6.5 (1) gives an intersection formula for the closure of convex subsets
  of a finite-dimensional ambient space whose relative interiors share a common point; the owner
  theorem below records the more primitive intrinsic-closure identity at the ordered topological
  `𝕜`-module layer, with the ordinary closure statement recovered later as its finite-dimensional
  corollary.
- `core/canonical`: the owner notions are `Convex 𝕜`, `intrinsicClosure 𝕜`,
  `intrinsicInterior 𝕜`, and the indexed intersection operator `iInter`; the chapter's
  owner-style derived API for convex sets is organized under `namespace Convex`.
- `bridge/view`: Rockafellar's `ri Cᵢ` is represented by mathlib's canonical
  `intrinsicInterior 𝕜 (C i)`. In finite-dimensional normed spaces, the ambient closure statement
  is the corollary obtained from the intrinsic-closure owner theorem via
  `intrinsicClosure_eq_closure`.
- Domain-style sampling used here: `intrinsicClosure`, `intrinsicClosure_eq_closure`,
  `Convex.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior`, and
  `intrinsicClosure_mono`.
- Primitive data vs derived API: the primitive data are the family `C` and the owner proofs
  `hC : ∀ i, Convex 𝕜 (C i)`; the closure identity is derived API, so it should live in the
  owner-style `Convex` namespace rather than as a parallel global wrapper.
- Layer target: this item stays `source-facing`, but Theorem 6.5 (1) is refined to the owner-style
  `Convex` API in canonical `intrinsicInterior`/`intrinsicClosure` language, with the ordinary
  closure version retained as a corollary.
-/

namespace Convex

open AffineMap

variable {C : ι → Set E}

private theorem right_mem_intrinsicClosure_openSegment (x y : E) :
    y ∈ intrinsicClosure 𝕜 (openSegment 𝕜 x y) := by
  rw [intrinsicClosure_eq_closure_inter_affineSpan]
  refine ⟨segment_subset_closure_openSegment (right_mem_segment 𝕜 x y), ?_⟩
  let u : E := lineMap x y ((1 : 𝕜) / 2)
  let v : E := lineMap u y ((1 : 𝕜) / 2)
  have hu : u ∈ openSegment 𝕜 x y := by
    dsimp [u]
    exact lineMap_mem_openSegment 𝕜 x y <| by constructor <;> norm_num
  have hv : v ∈ openSegment 𝕜 x y := by
    dsimp [v, u]
    rw [lineMap_lineMap_left]
    exact lineMap_mem_openSegment 𝕜 x y <| by constructor <;> norm_num
  have hy_line : y ∈ line[𝕜, u, v] := by
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq]
    refine ⟨(2 : 𝕜), ?_⟩
    dsimp [v]
    rw [lineMap_lineMap_right]
    norm_num
  exact
    (affineSpan_pair_le_of_mem_of_mem
      (subset_affineSpan 𝕜 (openSegment 𝕜 x y) hu)
      (subset_affineSpan 𝕜 (openSegment 𝕜 x y) hv)) hy_line

/-- Theorem 6.5 (1), intrinsic form: if a family of convex sets in an ordered topological
`𝕜`-module has relative interiors with a common point, then the intrinsic closure of their
intersection is the intersection of their intrinsic closures. -/
-- Proof sketch: choose a common point `x ∈ ⋂ i, intrinsicInterior 𝕜 (C i)`. For
-- `y ∈ ⋂ i, intrinsicClosure 𝕜 (C i)`, Theorem 6.1 puts every point of the open segment from `x`
-- to `y` into each `intrinsicInterior 𝕜 (C i)`, hence into `⋂ i, C i`; letting the segment
-- endpoint enter `intrinsicClosure 𝕜 (openSegment 𝕜 x y)`, and then monotonicity of
-- `intrinsicClosure` finishes. The reverse inclusion is the monotonicity of intrinsic closure.
theorem intrinsicClosure_iInter_eq_iInter_intrinsicClosure (hC : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, ri[𝕜](C i)).Nonempty) :
    cl[𝕜](⋂ i, C i) = ⋂ i, cl[𝕜](C i) := by
  refine subset_antisymm ?_ ?_
  · intro y hy
    refine Set.mem_iInter.2 fun i ↦ ?_
    exact intrinsicClosure_mono (show (⋂ i, C i) ⊆ C i from fun z hz ↦ Set.mem_iInter.1 hz i) hy
  · rcases hri with ⟨x, hx⟩
    have hxri : ∀ i, x ∈ ri[𝕜](C i) := fun i ↦ Set.mem_iInter.1 hx i
    intro y hy
    have hycl : ∀ i, y ∈ cl[𝕜](C i) := fun i ↦ Set.mem_iInter.1 hy i
    have hseg : openSegment 𝕜 x y ⊆ ⋂ i, C i := by
      intro z hz
      refine Set.mem_iInter.2 fun i ↦ ?_
      exact intrinsicInterior_subset <|
        openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior (hC i) (hxri i)
          (hycl i) hz
    exact intrinsicClosure_mono hseg <| right_mem_intrinsicClosure_openSegment x y

end Convex

end IntrinsicClosure

section Closure

variable {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

namespace Convex

variable {C : ι → Set E}

/-- Theorem 6.5 (1), ambient-closure form in finite-dimensional normed spaces. -/
theorem closure_iInter_eq_iInter_closure (hC : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, ri[𝕜](C i)).Nonempty) :
    closure (⋂ i, C i) = ⋂ i, closure (C i) := by
  simpa [intrinsicClosure_eq_closure 𝕜 (⋂ i, C i)] using
    intrinsicClosure_iInter_eq_iInter_intrinsicClosure (C := C) hC hri

end Convex

end Closure

section Interior

variable {ι 𝕜 E : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace 𝕜]
  [FiniteDimensional 𝕜 E]

namespace Convex

open AffineMap

variable {C : ι → Set E}

/-- Theorem 6.5 (2): if a finite family of convex sets in a finite-dimensional normed space over
`𝕜` has relative interiors with a common point, then the relative interior of their intersection
is the intersection of their relative interiors. Specializing to
`E = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement. -/
-- Proof sketch: by part (1), the sets `⋂ i, C i` and `⋂ i, intrinsicInterior 𝕜 (C i)` have the
-- same intrinsic closure. Applying the owner theorem `Convex.ri_intrinsicClosure_eq_ri`
-- to the convex intersection then gives
-- `intrinsicInterior 𝕜 (⋂ i, C i) ⊆ ⋂ i, intrinsicInterior 𝕜 (C i)`. For the reverse inclusion,
-- fix `z` in the right-hand side and use Theorem 6.4 to prolong any segment in `⋂ i, C i` past
-- `z` inside each `C i`; finiteness lets these prolongations be intersected into one common
-- prolongation in `⋂ i, C i`.
theorem intrinsicInterior_iInter_eq_iInter_intrinsicInterior (hC : ∀ i, Convex 𝕜 (C i))
    (hri : (⋂ i, ri[𝕜](C i)).Nonempty) [Finite ι] :
    ri[𝕜](⋂ i, C i) = ⋂ i, ri[𝕜](C i) := by
  have hCri : ∀ i, Convex 𝕜 (ri[𝕜](C i)) := fun i ↦ (hC i).intrinsicInterior
  have hInter : Convex 𝕜 (⋂ i, C i) := convex_iInter hC
  have hInterRi : Convex 𝕜 (⋂ i, ri[𝕜](C i)) := convex_iInter hCri
  refine subset_antisymm ?_ ?_
  · have hri_idem : ∀ i, ri[𝕜](ri[𝕜](C i)) = ri[𝕜](C i) := fun i ↦ by
      calc
        ri[𝕜](ri[𝕜](C i)) = ri[𝕜](closure (ri[𝕜](C i))) := by
          symm
          exact (hCri i).intrinsicInterior_closure_eq_intrinsicInterior
        _ = ri[𝕜](closure (C i)) := by
          rw [(hC i).closure_intrinsicInterior_eq_closure]
        _ = ri[𝕜](C i) := (hC i).intrinsicInterior_closure_eq_intrinsicInterior
    have hri' : (⋂ i, ri[𝕜](ri[𝕜](C i))).Nonempty := by
      rcases hri with ⟨x, hx⟩
      refine ⟨x, Set.mem_iInter.2 fun i ↦ ?_⟩
      simpa [hri_idem i] using (Set.mem_iInter.1 hx i)
    have hclosure_ri : ∀ i, closure (ri[𝕜](C i)) = closure (C i) := fun i ↦
      (hC i).closure_intrinsicInterior_eq_closure
    have hclosure : closure (⋂ i, ri[𝕜](C i)) = closure (⋂ i, C i) := by
      calc
        closure (⋂ i, ri[𝕜](C i)) = ⋂ i, closure (ri[𝕜](C i)) := by
          exact closure_iInter_eq_iInter_closure hCri hri'
        _ = ⋂ i, closure (C i) := by
          ext x
          simp [hclosure_ri]
        _ = closure (⋂ i, C i) := by
          symm
          exact closure_iInter_eq_iInter_closure hC hri
    intro z hz
    have hz' : z ∈ ri[𝕜](closure (⋂ i, C i)) := by
      simpa [hInter.intrinsicInterior_closure_eq_intrinsicInterior] using hz
    have hz'' : z ∈ ri[𝕜](closure (⋂ i, ri[𝕜](C i))) := by
      simpa [hclosure] using hz'
    have hz''' : z ∈ ri[𝕜](⋂ i, ri[𝕜](C i)) := by
      simpa [hInterRi.intrinsicInterior_closure_eq_intrinsicInterior] using hz''
    exact intrinsicInterior_subset hz'''
  · classical
    by_cases hι : IsEmpty ι
    · letI := hι
      have huniv : ri[𝕜]((Set.univ : Set E)) = Set.univ := by
        refine subset_antisymm intrinsicInterior_subset ?_
        simpa using
          (interior_subset_intrinsicInterior : interior (Set.univ : Set E) ⊆
            ri[𝕜]((Set.univ : Set E)))
      simp [huniv]
    · letI := Fintype.ofFinite ι
      letI : Nonempty ι := not_isEmpty_iff.mp hι
      intro z hz
      have hzri : ∀ i, z ∈ ri[𝕜](C i) := fun i ↦ Set.mem_iInter.1 hz i
      have hzInter : z ∈ ⋂ i, C i := Set.mem_iInter.2 fun i ↦ intrinsicInterior_subset (hzri i)
      have hInterNe : (⋂ i, C i).Nonempty := ⟨z, hzInter⟩
      refine (hInter.mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem).2 ⟨hInterNe, ?_⟩
      intro x hx
      have hxC : ∀ i, x ∈ C i := fun i ↦ Set.mem_iInter.1 hx i
      choose μ hμ_gt hμ_mem using fun i : ι ↦
        (((hC i).mem_intrinsicInterior_iff_forall_exists_gt_one_lineMap_mem).1 (hzri i)).2 x
          (hxC i)
      have hne : (Finset.univ : Finset ι).Nonempty := Finset.univ_nonempty
      let μmin : 𝕜 := (Finset.univ : Finset ι).inf' hne μ
      let ν : 𝕜 := (1 + μmin) / 2
      have hμmin_gt : 1 < μmin := by
        dsimp [μmin]
        rw [Finset.lt_inf'_iff hne]
        intro i hi
        exact hμ_gt i
      have hν_gt : 1 < ν := by
        dsimp [ν]
        linarith
      have hν_lt : ∀ i : ι, ν < μ i := by
        intro i
        have hle : μmin ≤ μ i := by
          dsimp [μmin]
          exact Finset.inf'_le μ (by simp)
        dsimp [ν]
        linarith
      refine ⟨ν, hν_gt, Set.mem_iInter.2 ?_⟩
      intro i
      have hseg : lineMap x z ν ∈ openSegment 𝕜 z (lineMap x z (μ i)) := by
        rw [openSegment_eq_image_lineMap]
        refine ⟨(ν - 1) / (μ i - 1), ?_, ?_⟩
        · constructor
          · have : 0 < ν - 1 := by linarith [hν_gt]
            have hden : 0 < μ i - 1 := by linarith [hμ_gt i]
            have : 0 < (ν - 1) / (μ i - 1) := div_pos this hden
            simpa
          · have hden : 0 < μ i - 1 := by linarith [hμ_gt i]
            have : (ν - 1) / (μ i - 1) < 1 := by
              rw [div_lt_one hden]
              linarith [hν_lt i]
            simpa
        · have hden : μ i - 1 ≠ 0 := by linarith [hμ_gt i]
          calc
            lineMap z (lineMap x z (μ i)) ((ν - 1) / (μ i - 1)) =
                lineMap (lineMap x z (μ i)) z (1 - (ν - 1) / (μ i - 1)) := by
                  rw [lineMap_symm]
                  simp
            _ = lineMap x z (1 - (1 - (1 - (ν - 1) / (μ i - 1))) * (1 - μ i)) := by
                  rw [lineMap_lineMap_left]
            _ = lineMap x z ν := by
                  congr 1
                  field_simp [hden]
                  ring
      exact intrinsicInterior_subset <|
        (hC i).openSegment_intrinsicInterior_closure_subset_intrinsicInterior (hzri i)
          (subset_closure (hμ_mem i)) hseg

end Convex

end Interior
