import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_7_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6
import ConvexAnalysis_Rockafellar_1970.Chap05.Example_23_0_7
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_8

noncomputable section

open scoped Pointwise Rockafellar

universe u v

section

variable {𝕜 : Type v} [AddGroup 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommGroup E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 27.4 is the constrained first-order optimality criterion: a feasible
  minimizer of a convex function on a convex set is characterized by a subgradient whose negative
  lies in the normal cone of the constraint set.
- `core/canonical`: the owner abstractions already present upstream are `IsMinOn`,
  `subdifferentialAt`, `N[𝕜](· | ·)`, `riDom[𝕜](·)`, and `ri[𝕜](·)`.
- `bridge/view`: the textbook optimality condition is best expressed directly on those owners,
  rather than by introducing a packaged constrained-minimum structure or a duplicate local
  “KKT-point” wrapper.

Domain-style sampling used here:
- `IsMinOn` from mathlib's order-extrema API;
- `N[𝕜](· | ·)` from `Chap01.Definition_2_7_10`;
- `subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `ri[𝕜](·)` from `Chap02.Text_6_8`.

Primitive data vs derived API:
- primitive inputs: the convex constraint set `C`, the convex function `h`, the base point `x`,
  the pairing codomain `N`, and the owner-side optimality witness
  `xStar ∈ ∂[N]h(x)` with `-xStar ∈ N[𝕜](x | C)`;
- derived API: feasibility of `x`, the canonical minimizer owner `IsMinOn h C x`, and under the
  relative-interior qualification the full equivalence between minimizers and normal-cone
  subgradient witnesses.

Ambient-layer lock-in:
- the current canonical owner `subdifferentialAt` is defined for
  `h : E → WithTopBot 𝕜` and supports pairing-based witness codomains `N`;
- the companion normal-cone owner used here is `N[𝕜](· | ·)`;
- the owner-level sufficiency theorem below is pairing-intrinsic at codomain `N`, and uses only
  the pairing-compatibility data needed for sign/subtraction rewrites in the normal-cone and
  subgradient inequalities, over scalar/order assumptions
  `[AddGroup 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]`.
- the later equivalence theorem keeps the stronger finite-dimensional normed-space layer required by
  the relative-interior qualification machinery.

Layer target: `source-facing`. The numbered item states a theorem about the existing owners
`IsMinOn`, `subdifferentialAt`, and `N[𝕜](· | ·)`; it does not own a new abstraction.
-/

-- Proof sketch: combine the subgradient inequality for `h` at `x` with the defining inequality of
-- `N[𝕜](x | C)` for `-xStar`. On every `z ∈ C`, the normal-cone inequality gives
-- `(⟪z - x, xStar⟫ₚ : 𝕜) ≥ 0`, so the subgradient inequality reduces to `h x ≤ h z`. The same
-- normal-cone membership, via `mem_normalCone_iff`, already forces the feasibility condition
-- `x ∈ C`.
/-- A subgradient at `x` whose negative lies in the normal cone to `C` at `x` certifies that `x`
is feasible and minimizes `h` over `C`. -/
theorem isMinOn_of_mem_subdifferentialAt_and_neg_mem_normalCone
    {N : Type (max u v)} [AddCommGroup N]
    [HasPairing E N 𝕜] [HasPairingSubLeft E N 𝕜] [HasPairingNegRight E N 𝕜]
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E} {xStar : N}
    (hxStar_sub : xStar ∈ ∂[N]h(x))
    (hxStar_normal : -xStar ∈ N[𝕜](x | C)) :
    x ∈ C ∧ IsMinOn h C x := by
  rcases (mem_normalCone_iff_sub_nonpos.mp hxStar_normal) with ⟨hxC, hxStar_normal'⟩
  refine ⟨hxC, (isMinOn_iff.mpr ?_)⟩
  intro z hzC
  have hsub : h x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ h z := by
    simpa [ge_iff_le] using (mem_subdifferentialAt_pairing.mp hxStar_sub) z
  have hnonneg_scalar : 0 ≤ (⟪z - x, xStar⟫ₚ : 𝕜) := by
    have hnonneg_neg : 0 ≤ -(⟪z - x, -xStar⟫ₚ : 𝕜) :=
      neg_nonneg.mpr (hxStar_normal' z hzC)
    simpa [HasPairingNegRight.pairing_neg_right] using hnonneg_neg
  have hnonneg : (0 : WithTopBot 𝕜) ≤ ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
    simpa using (WithTopBot.coe_le_coe.mpr hnonneg_scalar)
  have hx_le_add : h x ≤ h x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_le_add_right hnonneg (h x))
  exact le_trans hx_le_add hsub

/-- Existential-witness wrapper of
`isMinOn_of_mem_subdifferentialAt_and_neg_mem_normalCone`. -/
theorem isMinOn_of_exists_subgradient_neg_mem_normalCone
    {N : Type (max u v)} [AddCommGroup N]
    [HasPairing E N 𝕜] [HasPairingSubLeft E N 𝕜] [HasPairingNegRight E N 𝕜]
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E}
    (hopt :
      ∃ xStar : N,
        xStar ∈ ∂[N]h(x) ∧ -xStar ∈ N[𝕜](x | C)) :
    x ∈ C ∧ IsMinOn h C x := by
  rcases hopt with ⟨xStar, hxStar_sub, hxStar_normal⟩
  exact isMinOn_of_mem_subdifferentialAt_and_neg_mem_normalCone hxStar_sub hxStar_normal

end

section

variable {𝕜 : Type v} [ConditionallyCompleteLinearOrder 𝕜] [NormedField 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜]
variable [AddLeftMono 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

-- Proof sketch: view minimization of `h` on `C` as unconstrained minimization of
-- `h + indicatorFunction C`, use the Chapter 23/25 owner layer for subdifferentials of the
-- indicator-augmented objective under the relative-interior qualification, and rewrite the
-- resulting vanishing-subgradient condition as the existence of
-- `xStar ∈ (∂ h at x)` with `-xStar ∈ N[𝕜](x | C)`.
/-- Theorem 27.4: in a finite-dimensional seminormed space over `𝕜`, under the relative-interior
qualification `riDom[𝕜](h) ∩ ri[𝕜](C) ≠ ∅`, a point `x` is a feasible minimizer of a convex
function `h` on a convex set `C` exactly when some dual subgradient at `x` has negative
lying in the normal cone of `C` at `x`. The theorem is stated directly on the canonical owners
`IsMinOn`, `subdifferentialAt`, and `N[𝕜](· | ·)`. -/
theorem isMinOn_iff_exists_subgradient_neg_mem_normalCone_of_intrinsicInterior
    {h : E → WithTopBot 𝕜} {C : Set E} {x : E}
    (hneBot : ∀ y, h y ≠ ⊥) (hh_convex : h.IsConvex 𝕜) (hC_convex : Convex 𝕜 C)
    (hqual : (riDom[𝕜](h) ∩ ri[𝕜](C)).Nonempty) :
    (x ∈ C ∧ IsMinOn h C x) ↔
      ∃ xStar : StrongDual 𝕜 E,
        xStar ∈ (∂ h at x) ∧ -xStar ∈ N[𝕜](x | C) := by
  constructor
  · intro hxmin
    let f : Fin 2 → E → WithTopBot 𝕜 := Fin.cases (δ[𝕜](· | C)) (fun _ : Fin 1 => h)
    have hh_proper : h.IsProper := by
      rcases hqual with ⟨xq, hxq_ri, _⟩
      refine (Function.isProper_iff (f := h)).2 ?_
      refine ⟨⟨xq, intrinsicInterior_subset hxq_ri⟩, hneBot⟩
    have h_ind_proper : (δ[𝕜](· | C) : E → WithTopBot 𝕜).IsProper := by
      rcases hqual with ⟨xq, _, hxq_ri⟩
      refine (Function.isProper_iff (f := (δ[𝕜](· | C) : E → WithTopBot 𝕜))).2 ?_
      refine ⟨?_, ?_⟩
      · refine ⟨xq, ?_⟩
        rw [mem_effectiveDomain]
        exact
          (indicator_lt_top_iff_mem (α := 𝕜) (C := C) (x := xq)).2
            (intrinsicInterior_subset hxq_ri)
      · intro y
        by_cases hy : y ∈ C
        · simp [hy]
        · simp [hy]
    have hf_convex : ∀ i : Fin 2, (f i).IsConvex 𝕜 := by
      intro i
      fin_cases i
      · simpa [f] using
          ((indicator_isConvex_iff (𝕜 := 𝕜) (C := C)).2 hC_convex :
            (δ[𝕜](· | C) : E → WithTopBot 𝕜).IsConvex 𝕜)
      · simpa [f] using hh_convex
    have hf_proper : ∀ i : Fin 2, (f i).IsProper := by
      intro i
      fin_cases i
      · simpa [f] using h_ind_proper
      · simpa [f] using hh_proper
    have hri_f : (⋂ i : Fin 2, riDom[𝕜](f i)).Nonempty := by
      rcases hqual with ⟨xq, hxq_riDom, hxq_riC⟩
      refine ⟨xq, Set.mem_iInter.mpr ?_⟩
      intro i
      fin_cases i
      · classical
        have hdom_if :
            dom(fun y : E ↦ if y ∈ C then (0 : WithTopBot 𝕜) else ⊤) = C := by
          ext y
          rw [mem_effectiveDomain]
          by_cases hy : y ∈ C
          · simpa [hy] using (WithTopBot.coe_lt_top (0 : 𝕜))
          · simp [hy]
        simpa [f, hdom_if] using hxq_riC
      · simpa [f] using hxq_riDom
    have hsum_sub :
        subdifferentialAt (∑ i, f i) x (StrongDual 𝕜 E) =
          ∑ i, subdifferentialAt (f i) x (StrongDual 𝕜 E) :=
      subdifferentialAt_sum_eq_sum_subdifferentialAt_of_nonempty_iInter_riDom
        f hf_convex hf_proper hri_f x
    have hsum_sub' :
        subdifferentialAt (fun y ↦ δ[𝕜](y | C) + h y) x (StrongDual 𝕜 E) =
          subdifferentialAt (δ[𝕜](· | C)) x (StrongDual 𝕜 E) +
            subdifferentialAt h x (StrongDual 𝕜 E) := by
      simpa [Fin.sum_univ_two, f] using hsum_sub
    have hsum_min :
        ∀ z, (δ[𝕜](x | C) : WithTopBot 𝕜) + h x ≤ (δ[𝕜](z | C) : WithTopBot 𝕜) + h z := by
      intro z
      by_cases hzC : z ∈ C
      · have hxy : h x ≤ h z := (isMinOn_iff.mp hxmin.2) z hzC
        simpa [hxmin.1, hzC, add_comm, add_left_comm, add_assoc] using hxy
      · have hz_top : (δ[𝕜](z | C) : WithTopBot 𝕜) + h z = ⊤ := by
          calc
            (δ[𝕜](z | C) : WithTopBot 𝕜) + h z = ⊤ + h z := by simp [hzC]
            _ = ⊤ := WithTopBot.top_add_of_ne_bot (hneBot z)
        calc
          (δ[𝕜](x | C) : WithTopBot 𝕜) + h x = h x := by simp [hxmin.1]
          _ ≤ ⊤ := le_top
          _ = (δ[𝕜](z | C) : WithTopBot 𝕜) + h z := hz_top.symm
    have hzero_sub :
        (0 : StrongDual 𝕜 E) ∈
          subdifferentialAt (fun y ↦ δ[𝕜](y | C) + h y) x (StrongDual 𝕜 E) := by
      rw [mem_subdifferentialAt]
      intro z
      simpa [ge_iff_le] using hsum_min z
    rw [hsum_sub'] at hzero_sub
    rcases (Set.mem_add.mp hzero_sub) with ⟨u, hu, v, hv, huv0⟩
    refine ⟨v, hv, ?_⟩
    have hu_normal : u ∈ N[𝕜](x | C) := by
      exact
        (subdifferentialAt_indicatorFunction_eq_normalCone
          (𝕜 := 𝕜) (N := StrongDual 𝕜 E) C x) ▸ hu
    have hu_eq : u = -v := eq_neg_of_add_eq_zero_left huv0
    exact hu_eq ▸ hu_normal
  · intro hopt
    exact
      isMinOn_of_exists_subgradient_neg_mem_normalCone
        (N := StrongDual 𝕜 E) hopt

end
