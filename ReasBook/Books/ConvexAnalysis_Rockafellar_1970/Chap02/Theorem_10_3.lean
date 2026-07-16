import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_6_3
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_10_1_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_6_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

variable {E α : Type*}
variable [TopologicalSpace E] [AddCommGroup E]
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]

attribute [local instance] Classical.propDecidable

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 10.3 starts with a real-valued finite convex function on the relative
  interior `ri C`, assumes local simpliciality of the ambient convex set `C`, and concludes that
  the function admits a unique continuous finite convex extension to `C`.
- `core/canonical`: the owner abstractions are the Chapter 1 extension-by-`+∞` owner
  `Function.toWithBotTopOn f ri[𝕜](C)`, the Chapter 1 bridge
  `Function.toWithBotTopOn_eq_add_indicator`, the Chapter 7 closure operator `cl(·)`,
  the codomain lift `Function.toWithBotTop`, and the canonical two-branch presentation
  `Set.piecewise`,
  `Set.IsLocallySimplicial`, mathlib's relative interior `intrinsicInterior 𝕜 C`, the canonical
  setwise predicates `ConvexOn`, `ContinuousOn`, `Set.EqOn`, the Chapter 10.2 continuity owner
  theorem
  `Function.continuousOn_of_lowerSemicontinuous_of_upperSemicontinuousOn`,
  the Chapter 7.3.4 hull-identification owner theorem
  `Function.IsConvex.cl_eq_of_riDom_eq_and_eqOn`, and
  boundedness via `Bornology.IsBounded` and `BddAbove`.
- `bridge/view`: because `ConvexOn` and `ContinuousOn` are ambient-space predicates, the extension
  is represented by a real-valued ambient function `g : E → ℝ` whose convexity and continuity are
  required only on `C`; uniqueness is therefore expressed as equality on `C`, not as literal
  equality of global ambient functions.

Domain-style sampling used here:
- `Set.IsLocallySimplicial`;
- `ri[𝕜](C)`;
- `Function.toWithBotTopOn f ri[𝕜](C)`;
- `Function.toWithBotTopOn_eq_add_indicator`;
- `cl(·)`;
- `Function.continuousOn_of_lowerSemicontinuous_of_upperSemicontinuousOn`;
- `Function.IsConvex.cl_eq_of_riDom_eq_and_eqOn`;
- `ConvexOn ℝ C g`;
- `ContinuousOn g C`;
- `Set.EqOn g f S`.

Primitive data vs derived API:
- primitive inputs: the convex set `C`, its local simpliciality, the real-valued function `f`,
  convexity of `f` on `ri C`, and the hypothesis that `f` is bounded above on every bounded subset
  of `ri C`;
- owner construction: the canonical ambient `WithBotTop` extension
  `cl(Function.toWithBotTopOn f ri[𝕜](C))`, with the source-facing real branch
  `f.extensionFromIntrinsicInterior C` obtained by reading off its finite values on `C`;
- derived API: the owner-side convexity, continuity, and `EqOn` theorems for that extension,
  together with the source-facing existence-and-uniqueness corollary.

Layer target: the numbered theorem remains `source-facing`, but the refined owner-side API exposes
the canonical extension itself and keeps the existential theorem as a thin corollary.
- Ambient refinement: the owner construction itself uses only the generic chapter notions
  `intrinsicInterior 𝕜`, `indicator`, `Function.toWithBotTop`, and
  `lowerSemicontinuousHull`, so it lives at the additive topological module layer; the
  finite-dimensional normed-space hypotheses enter only in the derived
  convexity/continuity/uniqueness theorems below.
-/

namespace Function

/-- Canonical Chapter 10 owner: close the `+∞`-outside-`ri[𝕜](C)` extension at the chapter
`WithBotTop` layer. -/
def extensionFromIntrinsicInteriorWithBotTop
    (f : E → α) (𝕜 : Type*) [Ring 𝕜] [Module 𝕜 E] (C : Set E) : E → WithBotTop α :=
  cl(f.toWithBotTopOn ri[𝕜](C))

end Function

end

section

variable {E : Type*}

namespace Function

/-- Canonical finite real branch of a `WithBotTop ℝ`-valued function. -/
noncomputable abbrev realBranch (f : E → WithBotTop ℝ) : E → ℝ :=
  fun x ↦ EReal.toReal (f x)

end Function

end

section

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

attribute [local instance] Classical.propDecidable

namespace Function

/-- Source-facing real branch of the canonical owner
`Function.extensionFromIntrinsicInteriorWithBotTop`. -/
noncomputable abbrev extensionFromIntrinsicInterior (f : E → ℝ) (C : Set E) : E → ℝ :=
  (f.extensionFromIntrinsicInteriorWithBotTop ℝ C).realBranch

end Function

end

section

variable {𝕜 E : Type*}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]

attribute [local instance] Classical.propDecidable

namespace Function.extensionFromIntrinsicInteriorWithBotTop

variable {C : Set E} {f : E → 𝕜}

-- Proof sketch: extend `f` to a `WithBotTop 𝕜`-valued function by setting it equal to `⊤` off
-- `ri C`, then take its Chapter 7 closure `cl(·)`. The bounded-above-on-bounded-subsets
-- hypothesis and local simpliciality on `C` allow the Chapter 10 regularity machinery to propagate
-- convexity from `ri C` to `C`.
theorem isConvex
    (hC_conv : Convex 𝕜 C) (hC_simplicial : C.IsLocallySimplicial 𝕜)
    (hf_convex : ConvexOn 𝕜 ri[𝕜](C) f)
    (hf_bddAbove : ∀ (b : Set E), b ⊆ ri[𝕜](C) → Bornology.IsBounded b → BddAbove (f '' b)) :
    (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C).IsConvex 𝕜 := sorry

-- Proof sketch: apply Theorem 10.2 to the Chapter 7 closure of the `WithBotTop 𝕜`-valued
-- extension by `⊤` off `ri C`; lower semicontinuity comes from `cl(·)`, while upper
-- semicontinuity on `C` is obtained from the same boundedness and simplicial hypotheses.
theorem continuousOn
    (hC_conv : Convex 𝕜 C) (hC_simplicial : C.IsLocallySimplicial 𝕜)
    (hf_convex : ConvexOn 𝕜 ri[𝕜](C) f)
    (hf_bddAbove : ∀ (b : Set E), b ⊆ ri[𝕜](C) → Bornology.IsBounded b → BddAbove (f '' b)) :
    ContinuousOn (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) C := sorry

-- Proof sketch: derive convexity of `ri[𝕜](C).piecewise f.toWithBotTop ⊤` from `hf_convex`,
-- then use the Chapter 7 hull-identification theorem to show that `cl(·)` agrees with
-- `f.toWithBotTop` on `ri C`.
theorem eqOn_intrinsicInterior (hf_convex : ConvexOn 𝕜 ri[𝕜](C) f) :
    Set.EqOn (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) f.toWithBotTop
      ri[𝕜](C) :=
  sorry

/-- Primitive continuity uniqueness bridge at the canonical `WithBotTop` owner layer. -/
theorem eqOn_of_continuousOn_of_eqOn_intrinsicInterior
    (hC_conv : Convex 𝕜 C)
    (g : E → WithBotTop 𝕜) (hg_cont : ContinuousOn g C)
    (hg_eq : Set.EqOn g f.toWithBotTop ri[𝕜](C))
    (h_extension_cont : ContinuousOn (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) C)
    (h_extension_eq :
      Set.EqOn (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) f.toWithBotTop
        ri[𝕜](C)) :
    Set.EqOn g (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) C := by
  have hg_extension_eq :
      Set.EqOn g (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) ri[𝕜](C) :=
    fun x hx ↦ (hg_eq hx).trans (h_extension_eq hx).symm
  have hC_subset_closure_ri : C ⊆ closure ri[𝕜](C) := by
    intro x hx
    rw [Convex.closure_intrinsicInterior_eq_closure hC_conv]
    exact subset_closure hx
  exact
    hg_extension_eq.of_subset_closure hg_cont h_extension_cont intrinsicInterior_subset
      hC_subset_closure_ri

/-- Any continuous extension on `C` agreeing with `f` on `ri C` must equal the canonical owner
extension on `C`. -/
theorem eqOn
    (hC_conv : Convex 𝕜 C) (hC_simplicial : C.IsLocallySimplicial 𝕜)
    (hf_convex : ConvexOn 𝕜 ri[𝕜](C) f)
    (hf_bddAbove : ∀ (b : Set E), b ⊆ ri[𝕜](C) → Bornology.IsBounded b → BddAbove (f '' b))
    (g : E → WithBotTop 𝕜) (hg_cont : ContinuousOn g C)
    (hg_eq : Set.EqOn g f.toWithBotTop ri[𝕜](C)) :
    Set.EqOn g (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) C := by
  have h_extension_cont :
      ContinuousOn (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) C :=
    continuousOn hC_conv hC_simplicial hf_convex hf_bddAbove
  have h_extension_eq :
      Set.EqOn (f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C) f.toWithBotTop
        ri[𝕜](C) :=
    eqOn_intrinsicInterior hf_convex
  exact
    eqOn_of_continuousOn_of_eqOn_intrinsicInterior
      hC_conv g hg_cont hg_eq h_extension_cont h_extension_eq

end Function.extensionFromIntrinsicInteriorWithBotTop

/-- Canonical owner-side existence/uniqueness form behind Theorem 10.3:
construct the extension at the `WithBotTop` layer first, then obtain source-facing finite-valued
specializations as bridges. -/
theorem exists_unique_continuousOn_isConvex_extension_from_intrinsicInterior_withBotTop
    {C : Set E} (hC_conv : Convex 𝕜 C) (hC_simplicial : C.IsLocallySimplicial 𝕜) (f : E → 𝕜)
    (hf_convex : ConvexOn 𝕜 ri[𝕜](C) f)
    (hf_bddAbove :
      ∀ (b : Set E), b ⊆ ri[𝕜](C) → Bornology.IsBounded b → BddAbove (f '' b)) :
    ∃ g : E → WithBotTop 𝕜,
      g.IsConvex 𝕜 ∧
        ContinuousOn g C ∧
          Set.EqOn g f.toWithBotTop ri[𝕜](C) ∧
            ∀ g' : E → WithBotTop 𝕜,
                ContinuousOn g' C →
                  Set.EqOn g' f.toWithBotTop ri[𝕜](C) →
                    Set.EqOn g' g C :=
  let g := f.extensionFromIntrinsicInteriorWithBotTop 𝕜 C
  have h_extension_convex : g.IsConvex 𝕜 :=
    Function.extensionFromIntrinsicInteriorWithBotTop.isConvex
      hC_conv hC_simplicial hf_convex hf_bddAbove
  have h_extension_cont : ContinuousOn g C :=
    Function.extensionFromIntrinsicInteriorWithBotTop.continuousOn
      hC_conv hC_simplicial hf_convex hf_bddAbove
  have h_extension_eq : Set.EqOn g f.toWithBotTop ri[𝕜](C) :=
    Function.extensionFromIntrinsicInteriorWithBotTop.eqOn_intrinsicInterior hf_convex
  ⟨g,
    h_extension_convex,
    h_extension_cont,
    h_extension_eq,
    fun g' hg'_cont hg'_eq ↦
      Function.extensionFromIntrinsicInteriorWithBotTop.eqOn
        hC_conv hC_simplicial hf_convex hf_bddAbove g' hg'_cont hg'_eq⟩

end

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

attribute [local instance] Classical.propDecidable

namespace Function.extensionFromIntrinsicInterior

variable {C : Set E} {f : E → ℝ}

-- Proof sketch: extend `f` to a `WithBotTop ℝ`-valued function by setting it equal to `⊤` off
-- `ri C`, then take its Chapter 7 closure `cl(·)`. The bounded-above-on-bounded-subsets
-- hypothesis ensures that the hull is finite on `C`, and convexity descends to the real-valued
-- `toReal` representative there.
theorem convexOn
    (hC_conv : Convex ℝ C) (hC_simplicial : C.IsLocallySimplicial ℝ)
    (hf_convex : ConvexOn ℝ ri[ℝ](C) f)
    (hf_bddAbove : ∀ (b : Set E), b ⊆ ri[ℝ](C) → Bornology.IsBounded b → BddAbove (f '' b)) :
    ConvexOn ℝ C (f.extensionFromIntrinsicInterior C) := sorry

-- Proof sketch: apply Theorem 10.2 to the Chapter 7 closure of the `WithBotTop ℝ`-valued
-- extension by `⊤` off `ri C`. The bounded-above-on-bounded-subsets hypothesis guarantees
-- finiteness on `C`, and lower semicontinuity comes from `cl(·)`.
theorem continuousOn
    (hC_conv : Convex ℝ C) (hC_simplicial : C.IsLocallySimplicial ℝ)
    (hf_convex : ConvexOn ℝ ri[ℝ](C) f)
    (hf_bddAbove : ∀ (b : Set E), b ⊆ ri[ℝ](C) → Bornology.IsBounded b → BddAbove (f '' b)) :
    ContinuousOn (f.extensionFromIntrinsicInterior C) C := sorry

-- Proof sketch: derive convexity of the canonical `WithBotTop ℝ`-valued extension
-- `ri[ℝ](C).piecewise f.toWithBotTop ⊤` from `hf_convex` via the indicator-function bridge.
-- Then the Chapter 7 hull-identification theorem shows that its closure `cl(·)` agrees with the
-- original branch `f` on `ri C`, and on that set the hull is finite, so `toReal` recovers the
-- original real value.
theorem eqOn_intrinsicInterior (hf_convex : ConvexOn ℝ ri[ℝ](C) f) :
    Set.EqOn (f.extensionFromIntrinsicInterior C) f ri[ℝ](C) := sorry

/-- Primitive continuity uniqueness bridge: if a continuous function on `C` agrees with `f` on
`ri C`, and the canonical extension is also continuous on `C` and agrees with `f` on `ri C`,
then the two functions agree on `C`. -/
theorem eqOn_of_continuousOn_of_eqOn_intrinsicInterior
    (hC_conv : Convex ℝ C)
    (g : E → ℝ) (hg_cont : ContinuousOn g C) (hg_eq : Set.EqOn g f ri[ℝ](C))
    (h_extension_cont : ContinuousOn (f.extensionFromIntrinsicInterior C) C)
    (h_extension_eq : Set.EqOn (f.extensionFromIntrinsicInterior C) f ri[ℝ](C)) :
    Set.EqOn g (f.extensionFromIntrinsicInterior C) C := by
  have hg_extension_eq : Set.EqOn g (f.extensionFromIntrinsicInterior C) ri[ℝ](C) := fun x hx ↦
    (hg_eq hx).trans (h_extension_eq hx).symm
  have hC_subset_closure_ri : C ⊆ closure ri[ℝ](C) := by
    intro x hx
    rw [Convex.closure_intrinsicInterior_eq_closure hC_conv]
    exact subset_closure hx
  exact
    hg_extension_eq.of_subset_closure hg_cont h_extension_cont intrinsicInterior_subset
      hC_subset_closure_ri

/-- Any continuous extension to `C` that agrees with `f` on `ri C` must coincide on `C` with the
canonical owner-side extension from Theorem 10.3. -/
theorem eqOn
    (hC_conv : Convex ℝ C) (hC_simplicial : C.IsLocallySimplicial ℝ)
    (hf_convex : ConvexOn ℝ ri[ℝ](C) f)
    (hf_bddAbove : ∀ (b : Set E), b ⊆ ri[ℝ](C) → Bornology.IsBounded b → BddAbove (f '' b))
    (g : E → ℝ) (hg_cont : ContinuousOn g C) (hg_eq : Set.EqOn g f ri[ℝ](C)) :
    Set.EqOn g (f.extensionFromIntrinsicInterior C) C := by
  have h_extension_cont : ContinuousOn (f.extensionFromIntrinsicInterior C) C :=
    continuousOn hC_conv hC_simplicial hf_convex hf_bddAbove
  have h_extension_eq : Set.EqOn (f.extensionFromIntrinsicInterior C) f ri[ℝ](C) :=
    eqOn_intrinsicInterior hf_convex
  exact
    eqOn_of_continuousOn_of_eqOn_intrinsicInterior
      hC_conv g hg_cont hg_eq h_extension_cont h_extension_eq

end Function.extensionFromIntrinsicInterior

/-- Theorem 10.3, source-facing finite-valued bridge: if `C` is a locally simplicial convex set
and `f` is a finite convex function on `ri[ℝ](C)`, bounded above on every bounded subset of
`ri[ℝ](C)`, then `f` admits a unique continuous finite convex extension to `C`. The canonical owner
construction lives at `WithBotTop`; this theorem is its real-valued specialization. -/
theorem exists_unique_continuousOn_convexOn_extension_from_intrinsicInterior
    {C : Set E} (hC_conv : Convex ℝ C) (hC_simplicial : C.IsLocallySimplicial ℝ) (f : E → ℝ)
    (hf_convex : ConvexOn ℝ ri[ℝ](C) f)
    (hf_bddAbove :
      ∀ (b : Set E), b ⊆ ri[ℝ](C) → Bornology.IsBounded b → BddAbove (f '' b)) :
    ∃ g : E → ℝ,
      ConvexOn ℝ C g ∧
        ContinuousOn g C ∧
          Set.EqOn g f ri[ℝ](C) ∧
            ∀ g' : E → ℝ,
                ContinuousOn g' C →
                  Set.EqOn g' f ri[ℝ](C) →
                    Set.EqOn g' g C :=
  let g := f.extensionFromIntrinsicInterior C
  have h_extension_convex : ConvexOn ℝ C g :=
    Function.extensionFromIntrinsicInterior.convexOn hC_conv hC_simplicial hf_convex hf_bddAbove
  have h_extension_cont : ContinuousOn g C :=
    Function.extensionFromIntrinsicInterior.continuousOn
      hC_conv hC_simplicial hf_convex hf_bddAbove
  have h_extension_eq : Set.EqOn g f ri[ℝ](C) :=
    Function.extensionFromIntrinsicInterior.eqOn_intrinsicInterior hf_convex
  ⟨g,
    h_extension_convex,
    h_extension_cont,
    h_extension_eq,
    fun g' hg'_cont hg'_eq ↦
      Function.extensionFromIntrinsicInterior.eqOn
        hC_conv hC_simplicial hf_convex hf_bddAbove g' hg'_cont hg'_eq⟩

end
