import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_14
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_5_1
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜]
variable [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]
variable {I : Sort v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.5.1.2 identifies the support function of the intersection of the
  closures `closure (C i)` with the closure of the convex hull of the individual support
  functions. A stronger intrinsic-closure view is added below.
- `core/canonical`: the owner abstractions already present in the project are `supportFunction`,
  `conv`, `convexConjugate`, and `lowerSemicontinuousHull`.
- `bridge/view`: Rockafellar's `δ^*(· | C)` is represented by `δᵛ(· | C)`, while
  `cl (conv {δ^*(· | C_i)})` is represented by
  `cl(conv(⨅ i, (δᵛ(· | C i) : E → WithBotTop 𝕜)))`.

Domain-style sampling used here:
- `δ[𝕜](· | C)` / `δᵛ(· | C)`;
- `convexConjugate_supportFunction_eq_indicatorFunction_closure`;
- `convexConjugate_conv_iInf_eq_iSup`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`.
- `Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan` (for the intrinsic bridge theorem below).

Primitive data vs derived API:
- primitive input: a family of sets `C : I → Set E`;
- source-essential hypotheses: `I` is nonempty and each `C i` is convex;
- derived API: the support-function identity for the intersection of closures, then its
  intrinsic-closure restatement under the primitive affine-hull-closedness bridge assumptions.

Layer target: `source-facing`, stated directly on the finite-dimensional scalar-field pairing
owner layer already used by Theorem 16.5.1 and Text 13.1.5, with codomain `WithBotTop 𝕜`
instead of the over-concrete `EReal`/`ℝ` inner-product specialization.

Topology note: the primary conjugacy bridge imported from Text 13.1.5 is stated with ambient
`closure`; the intrinsic version uses the primitive bridge
`Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan` and is exposed below with explicit
affine-hull closedness assumptions on each set.
-/

omit [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [IsStrictOrderedRing 𝕜]
  [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜] [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
  [FiniteDimensional 𝕜 E] [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
  [HasPairingSwap E E 𝕜] in
private theorem iSup_indicator_eq_indicator_iInter
    (C : I → Set E) (hI : Nonempty I) :
    (⨆ i : I, (δ[𝕜](· | C i) : E → WithBotTop 𝕜)) = (δ[𝕜](· | ⋂ i : I, C i)) := by
  letI : Nonempty I := hI
  classical
  funext x
  by_cases hx : ∀ i : I, x ∈ C i
  · have hx_not_union : x ∉ ⋃ i : I, (C i)ᶜ := by
      intro hx_union
      rcases Set.mem_iUnion.1 hx_union with ⟨i, hi⟩
      exact hi (hx i)
    have hδ : δ[𝕜](x | ⋂ i : I, C i) = (0 : WithBotTop 𝕜) := by
      simp [hx_not_union]
    rw [iSup_apply]
    calc
      (⨆ i : I, δ[𝕜](x | C i)) = (0 : WithBotTop 𝕜) := by
        refine le_antisymm ?_ ?_
        · refine iSup_le ?_
          intro i
          simp [hx i]
        · obtain ⟨i⟩ := hI
          exact le_iSup_of_le i (by simp [hx i])
      _ = δ[𝕜](x | ⋂ i : I, C i) := hδ.symm
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hsup : (⨆ i : I, δ[𝕜](x | C i)) = ⊤ := by
      apply top_unique
      refine le_iSup_of_le i ?_
      simp [hi]
    have hx' : x ∉ ⋂ i : I, C i := by
      simpa [Set.mem_iInter] using hx
    have hx_union : x ∈ ⋃ i : I, (C i)ᶜ := by
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    have hδ : δ[𝕜](x | ⋂ i : I, C i) = (⊤ : WithBotTop 𝕜) := by
      simp [hx_union]
    calc
      (⨆ i : I, (δ[𝕜](· | C i) : E → WithBotTop 𝕜)) x = ⊤ := by
        rw [iSup_apply]
        exact hsup
      _ = δ[𝕜](x | ⋂ i : I, C i) := by
        exact hδ.symm

-- Proof sketch: apply Theorem 16.5.1 to `fun i ↦ δᵛ(· | C i)`.
-- Text 13.1.5 rewrites each conjugate as `δ[𝕜](· | closure (C i))`, and the supremum of those
-- indicators is the indicator of `⋂ i, closure (C i)` because the family is nonempty.
-- Applying biconjugacy to `conv(⨅ i, ...)` yields the right-hand closure.
/-- Corollary 16.5.1.2 at the pairing owner layer: for a nonempty family of convex sets on a
finite-dimensional scalar-field space with continuous linear self-pairing, the support function
of `⋂ i, closure (C i)` is `cl(conv {δ^*(· | C_i)})`, rendered as
`cl(conv(⨅ i, (δᵛ(· | C i) : E → WithBotTop 𝕜)))`. -/
theorem supportFunction_iInter_closure_eq_cl_conv_iInf_supportFunction_of_convex
    (C : I → Set E) (hI : Nonempty I) (hC_convex : ∀ i : I, Convex 𝕜 (C i)) :
    (δᵛ(· | ⋂ i : I, closure (C i)) : E → WithBotTop 𝕜) =
      cl(conv(⨅ i : I, (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
  letI : Nonempty I := hI
  let g : I → E → WithBotTop 𝕜 := fun i ↦ (δᵛ(· | C i) : E → WithBotTop 𝕜)
  have hg_convex : (conv(⨅ i : I, g i)).IsConvex 𝕜 :=
    (Function.isGreatest_conv_iInf_minorant g).1.1
  have hconj :
      convexConjugate (conv(⨅ i : I, g i)) = (δ[𝕜](· | ⋂ i : I, closure (C i))) := by
    calc
      convexConjugate (conv(⨅ i : I, g i))
          = ⨆ i : I, convexConjugate (g i) :=
            convexConjugate_conv_iInf_eq_iSup g
      _ = ⨆ i : I, (δ[𝕜](· | closure (C i))) := by
            funext x
            simp [iSup_apply, g,
              convexConjugate_supportFunction_eq_indicatorFunction_closure, hC_convex]
      _ = (δ[𝕜](· | ⋂ i : I, closure (C i))) :=
            iSup_indicator_eq_indicator_iInter (C := fun i ↦ closure (C i)) hI
  simpa [g] using
    (calc
      (δᵛ(· | ⋂ i : I, closure (C i)) : E → WithBotTop 𝕜)
          = convexConjugate (δ[𝕜](· | ⋂ i : I, closure (C i))) := by
              simpa using
                (convexConjugate_indicatorFunction_eq_supportFunction
                  (E := E) (EStar := E) (α := 𝕜)
                  (⋂ i : I, closure (C i))).symm
      _ = convexConjugate (convexConjugate (conv(⨅ i : I, g i))) := by
            rw [hconj.symm]
      _ = cl(conv(⨅ i : I, g i)) :=
            hg_convex.biconjugate_eq_lowerSemicontinuousHull)

end

section

open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)]
variable [IsStrictOrderedRing 𝕜] [DenselyOrdered 𝕜] [ClosedIciTopology 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]
variable {I : Sort v}

/-- Intrinsic-closure bridge of Corollary 16.5.1.2 at the same pairing owner layer: if each
`affineSpan 𝕜 (C i)` is closed, then the same support formula is read on
`⋂ i, intrinsicClosure 𝕜 (C i)` rather than `⋂ i, closure (C i)`. -/
theorem supportFunction_iInter_intrinsicClosure_eq_cl_conv_iInf_supportFunction_of_convex
    (C : I → Set E) (hI : Nonempty I) (hC_convex : ∀ i : I, Convex 𝕜 (C i))
    (hC_affineClosed : ∀ i : I, IsClosed (affineSpan 𝕜 (C i) : Set E)) :
    (δᵛ(· | ⋂ i : I, intrinsicClosure 𝕜 (C i)) : E → WithBotTop 𝕜) =
      cl(conv(⨅ i : I, (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
  have hIntrinsic :
      ∀ i : I, intrinsicClosure 𝕜 (C i) = closure (C i) := by
    intro i
    exact Set.intrinsicClosure_eq_closure_of_isClosed_affineSpan (𝕜 := 𝕜) (C := C i)
      (hC_affineClosed i)
  calc
    (δᵛ(· | ⋂ i : I, intrinsicClosure 𝕜 (C i)) : E → WithBotTop 𝕜) =
        (δᵛ(· | ⋂ i : I, closure (C i)) : E → WithBotTop 𝕜) := by
          simp [hIntrinsic]
    _ = cl(conv(⨅ i : I, (δᵛ(· | C i) : E → WithBotTop 𝕜))) := by
      simpa using
        (supportFunction_iInter_closure_eq_cl_conv_iInf_supportFunction_of_convex
          C hI hC_convex)

end
