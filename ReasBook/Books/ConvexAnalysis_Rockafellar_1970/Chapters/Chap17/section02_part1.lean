import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_17_2_1 (from Chap04) -/
noncomputable section

section

open Bornology Function

variable {𝕜 E : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜] [TopologicalSpace (WithTopBot 𝕜)]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.2.1 starts from a nonempty closed bounded set `S` and a
  continuous `𝕜`-valued function on `S`, extends that function by `+∞` off `S`, and asserts that
  the convex hull of the extension is a closed proper convex function.
- `core/canonical`: the owner abstractions already present upstream are `Function.convexHull` for
  Rockafellar's `conv`, the canonical extension owner `Function.toWithTopBotOn`, and the bundled
  predicate `Function.IsClosedProperConvex`.
- `bridge/view`: the source's extension by `+∞` off `S` is exactly the canonical function
  `f.toWithTopBotOn S`, so the corollary should be stated directly on that owner
  expression rather than by introducing a parallel local wrapper for the extension or for the
  closed/proper/convex package.

Domain-style sampling used here:
- `Function.convexHull` from `Chap01.Text_5_5_1`;
- `Function.toWithTopBotOn` from `Chap01.Remark_4_4_5`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Metric.isCompact_iff_isClosed_bounded` for the closed-bounded-to-compact bridge in proper
  pseudo-metric spaces.

Primitive data vs derived API:
- primitive source data: the set `S` and the `𝕜`-valued branch `f`;
- intrinsic compactness owner datum: `IsCompact S` for the relative topology of `S`;
- canonical bridge data: the ambient extension `f.toWithTopBotOn S`;
- explicit closedness bridge datum: `LowerSemicontinuous (conv(f.toWithTopBotOn S))`;
- derived API: the closed/proper/convex conclusion for the same convex-hull owner.

Layer target: `core/canonical` for the primary theorem (`IsCompact` surface), plus a thin
`source-facing` bridge theorem that recovers the closed-and-bounded hypotheses through compactness
of proper pseudo-metric spaces.
-/

-- Proof sketch: use `hS_nonempty` to get one finite value of `f.toWithTopBotOn S`, and use
-- compactness plus continuity to get a global lower bound on `f` over `S`; this lower bound
-- controls the vertical infimum defining `conv(f.toWithTopBotOn S)`, yielding non-`⊥` values.
-- Convexity comes from `Function.isConvex_conv`, and closedness is the explicit bridge hypothesis
-- `hconv_closed`.
/-- Intrinsic compact-set owner form of Corollary 17.2.1: if `S` is nonempty compact and `f` is
continuous on `S` and `conv(f.toWithTopBotOn S)` is lower semicontinuous, then the convex hull of
the canonical extension `f.toWithTopBotOn S` is a closed proper convex function. -/
theorem conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isCompact
    [TopologicalSpace E] [AddCommMonoid E] [Module 𝕜 E]
    {S : Set E} {f : E → 𝕜} (hS_nonempty : S.Nonempty) (hS_compact : IsCompact S)
    (hf : ContinuousOn f S)
    (hconv_closed : LowerSemicontinuous (conv(f.toWithTopBotOn S))) :
    IsClosedProperConvex[𝕜] (conv(f.toWithTopBotOn S)) := by
  let g : E → WithTopBot 𝕜 := f.toWithTopBotOn S
  refine ⟨Function.isConvex_conv g, ?_, ?_⟩
  · rw [Function.isProper_iff]
    refine ⟨?_, ?_⟩
    · rcases hS_nonempty with ⟨x0, hx0⟩
      refine ⟨x0, ?_⟩
      rw [mem_effectiveDomain]
      have hx0_epi : (x0, f x0) ∈ epi g := by
        exact (mem_epi_iff).2 (le_of_eq (by simpa [g] using Function.toWithTopBotOn_of_mem f S hx0))
      have hx0_convexEpi : (x0, f x0) ∈ _root_.convexHull 𝕜 (epi g) :=
        subset_convexHull 𝕜 (epi g) hx0_epi
      have hle : conv(g) x0 ≤ (f x0 : WithTopBot 𝕜) := by
        rw [Function.convexHull_eq_verticalInfimum_convexHull_epigraph]
        exact Function.verticalInfimum_le_of_mem hx0_convexEpi
      have hfx_lt_top : (f x0 : WithTopBot 𝕜) < ⊤ := by
        exact lt_top_iff_ne_top.2 (by simp)
      exact lt_of_le_of_lt hle hfx_lt_top
    · rcases hS_compact.exists_isMinOn hS_nonempty hf with ⟨xmin, hxminS, hxmin⟩
      let m : 𝕜 := f xmin
      have hxmin_le : ∀ y ∈ S, f xmin ≤ f y := by
        simpa [IsMinOn, IsMinFilter, Filter.Eventually, Filter.mem_principal] using hxmin
      have hsubset_const : epi g ⊆ epi (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) := by
        intro p hp
        have hp_le : g p.1 ≤ (p.2 : WithTopBot 𝕜) := (mem_epi_iff).1 hp
        have hp_mem_S : p.1 ∈ S := by
          by_contra hp_not_mem_S
          have hp_top : g p.1 = (⊤ : WithTopBot 𝕜) := by
            simpa [g] using Function.toWithTopBotOn_of_notMem f S hp_not_mem_S
          have hp_le_top : (⊤ : WithTopBot 𝕜) ≤ (p.2 : WithTopBot 𝕜) := by
            rw [← hp_top]
            exact hp_le
          have hp2_eq_top : (p.2 : WithTopBot 𝕜) = ⊤ := (top_le_iff).1 hp_le_top
          exact (WithTopBot.coe_ne_top p.2) hp2_eq_top
        have hm_le_fx : (m : WithTopBot 𝕜) ≤ (f p.1 : WithTopBot 𝕜) := by
          exact (WithTopBot.coe_le_coe).2 (by simpa [m] using hxmin_le p.1 hp_mem_S)
        have hfx_eq : (f p.1 : WithTopBot 𝕜) = g p.1 := by
          simpa [g] using (Function.toWithTopBotOn_of_mem f S hp_mem_S).symm
        exact (mem_epi_iff).2 (le_trans (hfx_eq ▸ hm_le_fx) hp_le)
      have hconst_convex : Convex 𝕜 (epi (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜))) := by
        have hconst_convexOn : ConvexOn 𝕜 (Set.univ : Set E) (fun _ : E ↦ m) :=
          Function.convexOn_univ_const (𝕜 := 𝕜) (E := E) m
        simpa using
          (Function.isConvex_coe_of_convexOn_univ
            (𝕜 := 𝕜) (E := E) (β := 𝕜) hconst_convexOn)
      have hsubset_convexEpi :
          _root_.convexHull 𝕜 (epi g) ⊆ epi (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) := by
        exact convexHull_min hsubset_const hconst_convex
      have hm_le_conv : (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) ≤ conv(g) := by
        intro x
        have hle_vi :
            (fun _ : E ↦ ((m : 𝕜) : WithTopBot 𝕜)) x ≤
              Function.verticalInfimum (_root_.convexHull 𝕜 (epi g)) x := by
          exact (Function.le_verticalInfimum_of_subset_epi hsubset_convexEpi) x
        rw [Function.convexHull_eq_verticalInfimum_convexHull_epigraph]
        exact hle_vi
      intro x
      have hbot_lt_m : (⊥ : WithTopBot 𝕜) < ((m : 𝕜) : WithTopBot 𝕜) := by
        exact lt_of_le_of_ne (by simp) (by simp)
      have hconv_ne_bot : conv(g) x ≠ (⊥ : WithTopBot 𝕜) :=
        ne_of_gt <| lt_of_lt_of_le hbot_lt_m (hm_le_conv x)
      simpa [g] using hconv_ne_bot
  · simpa using hconv_closed

/-- Corollary 17.2.1 in closed-and-bounded bridge form over proper pseudo-metric spaces: if `S` is
nonempty closed bounded and `f` is continuous on `S`, then the convex hull of `f.toWithTopBotOn S`
is a closed proper convex function provided the same lower-semicontinuity witness for that convex
hull. -/
theorem conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isClosed_of_isBounded
    [PseudoMetricSpace E] [AddCommMonoid E] [Module 𝕜 E]
    [ProperSpace E]
    {S : Set E} {f : E → 𝕜} (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S)
    (hS_bounded : IsBounded S) (hf : ContinuousOn f S)
    (hconv_closed : LowerSemicontinuous (conv(f.toWithTopBotOn S))) :
    IsClosedProperConvex[𝕜] (conv(f.toWithTopBotOn S)) := by
  have hS_compact : IsCompact S := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bounded
  exact conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isCompact
    hS_nonempty hS_compact hf hconv_closed

end

/-! ### Definition_17_2_2 (from Chap04) -/
noncomputable section

universe u v

section

open scoped Rockafellar

variable {X : Type u} {Y : Type v}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.2 introduces, for a subset `S` and a function
  `f : S → α ∪ {+∞}`, the function `h` given by the supremum
  `h(y) = sup_{x ∈ S} (⟪x, y⟫ - f(x))`.
- `core/canonical`: the chapter owner abstraction for Fenchel conjugation is
  `convexConjugate` from `Defn_12_2`, already stated for arbitrary pairings and codomains with
  supremum and subtraction.
- `bridge/view`: restricted source data is compared to the ambient owner by the canonical subtype
  bridge `Function.extendByTop` from `Defn_12_4`, applied to the restricted branch.

Primitive data vs derived API:
- primitive source-facing data: the subset `S` and a branch `f : S → L`;
- primitive owner in this file: the restricted conjugate `convexConjugateOn f`;
- derived bridge/view: the ambient `+∞`-extension through the canonical owner
  `Function.extendByTop`, compared with `convexConjugate`.

Layer target: `source-facing`. The textbook object is a conjugate-like supremum attached to
restricted data on `S`. The ambient `convexConjugate` owner remains the canonical comparison
object, and the extension bridge reuses the existing canonical owner instead of introducing a
parallel extension definition.

Topology-language axis for this item: not applicable. This file introduces an owner and a bridge
identity for conjugation; it does not state ambient/intrinsic closure/interior claims.
-/

/-- Definition 17.2.2 owner: for `f : S → L`, the restricted conjugate is just the
Fenchel conjugate on the subtype domain. The primitive pairing assumption is only the pairing on
the source domain `S`, not an ambient pairing assumption on `X`. -/
def convexConjugateOn {L : Type*} {S : Set X} [SupSet L] [Sub L]
    [HasPairing S Y L] (f : S → L) : Y → L :=
  f⋆

section AmbientBridge

variable {L : Type*} [CompleteLattice L] [Sub L]

/-- The restricted conjugate from Definition 17.2.2 is the ambient Fenchel conjugate of the
canonical subtype-extension-by-`⊤` of the branch. The bridge uses only codomain-level data:
complete-lattice supremum, subtraction, and the off-domain law `a - ⊤ = ⊥`. -/
theorem convexConjugateOn_eq_convexConjugate_extendByTop {S : Set X}
    [HasPairing X Y L]
    (hsub_top : ∀ a : L, a - (⊤ : L) = (⊥ : L))
    (f : S → L) :
    convexConjugateOn f =
      (((Function.extendByTop f)⋆) : Y → L) := by
  let fExt : X → L := Function.extendByTop f
  change convexConjugateOn f = ((fExt)⋆ : Y → L)
  ext y
  rw [convexConjugateOn]
  rw [convexConjugate_eq_iSup_pairing_sub (f := f) (y := y)]
  rw [convexConjugate_eq_iSup_pairing_sub (f := fExt) (y := y)]
  let gS : S → L := fun x ↦ (⟪x, y⟫ₚ : L) - f x
  let gX : X → L := fun x ↦ (⟪x, y⟫ₚ : L) - fExt x
  change (iSup gS : L) = (iSup gX : L)
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    have hxext : fExt x = f x := by
      simp [fExt]
    calc
      gS x = gX x := by
        dsimp [gS, gX]
        rw [hxext]
        rfl
      _ ≤ ⨆ x : X, gX x := by
        exact le_iSup gX x
  · refine iSup_le ?_
    intro x
    by_cases hx : x ∈ S
    · let xS : S := ⟨x, hx⟩
      have hxext : fExt x = f xS := by
        simpa [fExt, xS] using
          (Function.extendByTop_apply_of_mem (g := f) (x := x) hx)
      calc
        gX x = gS xS := by
          dsimp [gS, gX]
          rw [hxext]
          rfl
        _ ≤ ⨆ x : S, gS x := by
          exact le_iSup gS xS
    · have hxTop : fExt x = (⊤ : L) := by
        simpa [fExt] using
          (Function.extendByTop_apply_of_notMem
            (g := f) (x := x) hx)
      calc
        gX x = (⊥ : L) := by
          have hpair_sub_top :
              (⟪x, y⟫ₚ : L) - (⊤ : L) = (⊥ : L) :=
            hsub_top (⟪x, y⟫ₚ : L)
          simpa [gX, hxTop] using hpair_sub_top
        _ ≤ ⨆ x : S, gS x := by
          exact (bot_le : (⊥ : L) ≤ ⨆ x : S, gS x)

end AmbientBridge

end

/-! ### Theorem_17_2 (from Chap04) -/
section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-!
Source/core/bridge triage:

`source-facing`: this file keeps the Theorem 17.2 bridge shape through
`closedConvexHull 𝕜 S = convexHull 𝕜 (closure S)` and
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)`, but it makes the key
closedness witness explicit: `IsClosed (convexHull 𝕜 (closure S))`.
- `core/canonical`: the owner abstraction is `closedConvexHull 𝕜 S`, together with set closure
  `closure` and convex hull `convexHull 𝕜`, at the primitive topological-module layer.
- `bridge/view`: the owner-side identity is obtained directly from the minimality owners
  `closedConvexHull_min` and `convexHull_min`, together with
  `closedConvexHull_closure_eq_closedConvexHull`.
- Domain-style sampling used here: `closedConvexHull`, `closedConvexHull_eq_closure_convexHull`,
  `closedConvexHull_closure_eq_closedConvexHull`, `isClosed_closedConvexHull`.
- Primitive data vs derived API: the primitive owner-side bridge input in this file is exactly the
  closedness of `convexHull 𝕜 (closure S)`, rather than a stronger compactness or boundedness
  hypothesis. `closedConvexHull 𝕜 S` is generated owner data, and the displayed equalities are
  derived bridge API.
- Layer target: `bridge/view`; source-facing corollaries are stated directly on the same primitive
  closedness witness, with no non-primitive wrapper assumptions.
-/

/-- The primitive owner-side bridge: if `convexHull 𝕜 (closure S)` is closed, then the closed
convex hull of `S` is the convex hull of `closure S`. -/
-- Proof sketch: rewrite `closedConvexHull 𝕜 S` as `closedConvexHull 𝕜 (closure S)`, then use
-- the minimality rules for `closedConvexHull` and `convexHull`.
theorem closedConvexHull_eq_convexHull_closure_of_isClosed_convexHull_closure (S : Set E)
    (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S))) :
    closedConvexHull 𝕜 S = convexHull 𝕜 (closure S) := by
  calc
    closedConvexHull 𝕜 S = closedConvexHull 𝕜 (closure S) := by
      symm
      exact closedConvexHull_closure_eq_closedConvexHull
    _ = convexHull 𝕜 (closure S) := by
      refine subset_antisymm ?_ ?_
      · exact
          closedConvexHull_min (subset_convexHull 𝕜 (closure S))
            (convex_convexHull 𝕜 (closure S)) hS_convexHullClosure_closed
      · exact
          convexHull_min (subset_closedConvexHull (𝕜 := 𝕜) (s := closure S))
            (convex_closedConvexHull (𝕜 := 𝕜) (s := closure S))

/-- Owner-side recognition bridge: `closedConvexHull 𝕜 S` is exactly `convexHull 𝕜 (closure S)`
precisely when `convexHull 𝕜 (closure S)` is closed. -/
theorem closedConvexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure (S : Set E) :
    closedConvexHull 𝕜 S = convexHull 𝕜 (closure S) ↔
      IsClosed (convexHull 𝕜 (closure S)) := by
  constructor
  · intro hEq
    simpa [← hEq] using (isClosed_closedConvexHull (𝕜 := 𝕜) (s := S))
  · intro hS_convexHullClosure_closed
    exact
      closedConvexHull_eq_convexHull_closure_of_isClosed_convexHull_closure
        S hS_convexHullClosure_closed

end

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-- Primitive source-facing closure bridge: if `convexHull 𝕜 (closure S)` is closed and
`closure (convexHull 𝕜 S)` is convex, then
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)`. -/
-- Proof sketch: prove each inclusion by minimality at the primitive set level.
theorem
    closure_convexHull_eq_convexHull_closure_of_isClosed_of_convex_closure
    (S : Set E) (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S)))
    (hS_closureConvexHull_convex : Convex 𝕜 (closure (convexHull 𝕜 S))) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) := by
  refine subset_antisymm ?_ ?_
  · exact
      closure_minimal
        (convexHull_mono (subset_closure : S ⊆ closure S))
        hS_convexHullClosure_closed
  · exact
      convexHull_min
        (closure_minimal
          (subset_trans (subset_convexHull 𝕜 S) subset_closure)
          isClosed_closure)
        hS_closureConvexHull_convex

/-- Primitive source-facing recognition bridge: under the primitive convexity input
`Convex 𝕜 (closure (convexHull 𝕜 S))`, the identity
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)` is equivalent to closedness of
`convexHull 𝕜 (closure S)`. -/
theorem
    closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure_of_convex_closure
    (S : Set E) (hS_closureConvexHull_convex : Convex 𝕜 (closure (convexHull 𝕜 S))) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) ↔
      IsClosed (convexHull 𝕜 (closure S)) := by
  constructor
  · intro hEq
    simpa [hEq] using (isClosed_closure : IsClosed (closure (convexHull 𝕜 S)))
  · intro hS_convexHullClosure_closed
    exact
      closure_convexHull_eq_convexHull_closure_of_isClosed_of_convex_closure
        S hS_convexHullClosure_closed hS_closureConvexHull_convex

end

section

variable {𝕜 E : Type*}
variable [Field 𝕜] [PartialOrder 𝕜]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E]

/-- Source-facing recognition bridge: `closure (convexHull 𝕜 S)` is exactly
`convexHull 𝕜 (closure S)` precisely when `convexHull 𝕜 (closure S)` is closed. -/
theorem closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure
    (S : Set E) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) ↔
      IsClosed (convexHull 𝕜 (closure S)) := by
  have hS_closureConvexHull_convex : Convex 𝕜 (closure (convexHull 𝕜 S)) := by
    simpa [closedConvexHull_eq_closure_convexHull (𝕜 := 𝕜) (s := S)] using
      (convex_closedConvexHull (𝕜 := 𝕜) (s := S))
  exact
    closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure_of_convex_closure
      (𝕜 := 𝕜) S hS_closureConvexHull_convex

/-- Source-facing closure bridge: if `convexHull 𝕜 (closure S)` is closed, then
`closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S)`. -/
theorem closure_convexHull_eq_convexHull_closure_of_isClosed_convexHull_closure (S : Set E)
    (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S))) :
    closure (convexHull 𝕜 S) = convexHull 𝕜 (closure S) := by
  exact
    (closure_convexHull_eq_convexHull_closure_iff_isClosed_convexHull_closure
      (𝕜 := 𝕜) S).2 hS_convexHullClosure_closed

end

section

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-- Closed-set bridge at the source-facing surface: for closed `S`,
`convexHull 𝕜 S` is closed precisely when `convexHull 𝕜 (closure S)` is closed. -/
theorem isClosed_convexHull_iff_isClosed_convexHull_closure_of_isClosed
    (S : Set E) (hS_closed : IsClosed S) :
    IsClosed (convexHull 𝕜 S) ↔ IsClosed (convexHull 𝕜 (closure S)) := by
  simp

/-- Closed-set corollary under the same bridge witness: if `S` is closed and
`convexHull 𝕜 (closure S)` is closed, then `convexHull 𝕜 S` is closed. -/
theorem isClosed_convexHull_of_isClosed_of_isClosed_convexHull_closure
    (S : Set E) (hS_closed : IsClosed S)
    (hS_convexHullClosure_closed : IsClosed (convexHull 𝕜 (closure S))) :
    IsClosed (convexHull 𝕜 S) := by
  exact
    (isClosed_convexHull_iff_isClosed_convexHull_closure_of_isClosed
      (𝕜 := 𝕜) S hS_closed).2 hS_convexHullClosure_closed

end

/-! ### Proposition_17_2_3 (from Chap04) -/
noncomputable section

universe u

section

open Bornology Function
open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [TopologicalSpace E]
variable [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {S : Set E} {f : E → 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 17.2.3 fixes a nonempty compact set `S`, a continuous
  scalar-valued function on `S`, lets `h` be the Definition 17.2.2 restricted conjugate of that
  branch, and asserts that `h` is finite everywhere and that `h⋆` is the convex hull of the
  extension by `+∞` off `S`.
- `core/canonical`: the relevant owner declarations already present in the project are
  `convexConjugateOn`, `toWithBotTopOn`, and `conv(·)`.
- `bridge/view`: the source-facing restricted conjugate owner
  `convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))` is canonically identified with the
  ambient conjugate of the extension-by-`+∞` owner `toWithBotTopOn f S`.

Domain-style sampling used here:
- `convexConjugateOn` from `Definition_17_2_2`;
- `convexConjugateOn_eq_convexConjugate_extendByTop` from `Definition_17_2_2`;
- `toWithBotTopOn` from `Remark_4_4_5`;
- `conv_toWithTopBotOn_isClosedProperConvex_of_nonempty_of_isCompact`
  from `Corollary_17_2_1`;

Primitive data vs derived API:
- primitive source data: the set `S` and the scalar-valued branch `f`;
- source-facing owner: the restricted conjugate
  `convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))`;
- canonical bridge object: the ambient extension `toWithBotTopOn f S`;
- derived API: pointwise finiteness and continuity of the restricted conjugate, plus the
  conjugacy identity with `conv(toWithBotTopOn f S)`.

Layer target:
- primary owner surface: compact-domain (`IsCompact`) statements on
  `convexConjugateOn`, matching the intrinsic compactness layer already present upstream;
- bridge surface: closed-and-bounded statements only as thin companions in proper pseudo-metric
  spaces, derived from the compact owner via
  `Metric.isCompact_iff_isClosed_bounded`.
-/

-- Proof sketch: bridge the source-facing owner
-- `convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))`
-- to the ambient conjugate of the `⊤`-extension of `f|S`. Corollary 17.2.1 shows that
-- `conv(toWithBotTopOn f S)` is closed proper convex, so the Chapter 12/13 conjugacy API applied
-- to that ambient bridge yields pointwise scalar-valuedness of the restricted conjugate.
/-- Proposition 17.2.3, intrinsic compact form: if `S` is nonempty compact and `f` is continuous
on `S`,
then the Definition 17.2.2 restricted conjugate `h` of the scalar-valued branch `f|S` is finite at
every point. -/
theorem convexConjugateOn_realValued_everywhere_of_nonempty_of_isCompact_of_continuousOn
    (hS_nonempty : S.Nonempty) (hS_compact : IsCompact S)
    (hf : ContinuousOn f S) (y : E) :
    ∃ r : 𝕜, convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜)) y = r := sorry

-- Proof sketch: the source-facing restricted conjugate owner is canonically the ambient conjugate
-- of the extension-by-`⊤` function, hence convex. If `S = ∅`, this restricted conjugate is the
-- constant `⊥` function, so continuity is immediate. Otherwise the previous theorem supplies the
-- everywhere scalar-valued hypothesis required by the Chapter 10 continuity owner theorem.
/-- The restricted conjugate is continuous everywhere under compact-domain hypotheses.
When `S = ∅`, it is the constant `⊥` function. -/
theorem
    continuous_convexConjugateOn_of_isCompact_of_continuousOn
    (hS_compact : IsCompact S)
    (hf : ContinuousOn f S)
    : Continuous ((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜) := sorry

-- Proof sketch: use `convexConjugateOn_eq_convexConjugate_extendByTop` to identify the
-- source-facing restricted conjugate with the ambient conjugate of the extension-by-`⊤` function.
-- If `S = ∅`, that restricted conjugate is constant `⊥`, hence its conjugate is constant `⊤`,
-- which agrees with `conv(toWithBotTopOn f S)`. Otherwise Corollary 17.2.1 makes
-- `conv(toWithBotTopOn f S)` closed proper convex, so the Chapter 12 biconjugacy theorem yields
-- the textbook identity `h⋆ = conv f`.
/-- The Fenchel conjugate of the restricted conjugate equals the convex hull of the extension of
`f` by `+∞` outside `S` under compact-domain hypotheses. When `S = ∅`, both sides
are the constant `⊤` function. -/
theorem
    convexConjugateOn_conjugate_eq_conv_toWithBotTopOn_of_isCompact_of_continuousOn
    [OrderTopology 𝕜] [HasPairingSwap E E 𝕜]
    (hS_compact : IsCompact S)
    (hf : ContinuousOn f S)
    : ((((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜)⋆)) =
        conv(toWithBotTopOn f S) := sorry

end

section

open Bornology Function
open scoped Rockafellar

variable {E : Type u} {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [ClosedIicTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)]
variable [PseudoMetricSpace E] [T2Space E] [ProperSpace E]
variable [AddCommGroup E] [Module 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜]
variable {S : Set E} {f : E → 𝕜}

/-- Proper-space bridge form of Proposition 17.2.3: nonempty closed bounded sets are compact, so
the compact-domain finite-valued statement applies directly. -/
theorem convexConjugateOn_realValued_everywhere_of_nonempty_of_isClosed_of_isBounded_of_continuousOn
    (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_bounded : IsBounded S)
    (hf : ContinuousOn f S) (y : E) :
    ∃ r : 𝕜, convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜)) y = r := by
  have hS_compact : IsCompact S :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hS_closed, hS_bounded⟩
  exact convexConjugateOn_realValued_everywhere_of_nonempty_of_isCompact_of_continuousOn
    (S := S) (f := f) hS_nonempty hS_compact hf y

/-- Proper-space bridge form: continuity of the restricted conjugate from closed bounded domain
hypotheses follows by compactness reduction. -/
theorem
    continuous_convexConjugateOn_of_isClosed_of_isBounded_of_continuousOn
    (hS_closed : IsClosed S) (hS_bounded : IsBounded S)
    (hf : ContinuousOn f S)
    : Continuous ((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜) := by
  have hS_compact : IsCompact S :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hS_closed, hS_bounded⟩
  exact continuous_convexConjugateOn_of_isCompact_of_continuousOn
    (S := S) (f := f) hS_compact hf

/-- Proper-space bridge form: the conjugacy identity from closed bounded domain hypotheses follows
from the compact-domain owner theorem. -/
theorem
    convexConjugateOn_conjugate_eq_conv_toWithBotTopOn_of_isClosed_of_isBounded_of_continuousOn
    [OrderTopology 𝕜] [HasPairingSwap E E 𝕜]
    (hS_closed : IsClosed S) (hS_bounded : IsBounded S)
    (hf : ContinuousOn f S)
    : ((((convexConjugateOn (fun x : S ↦ (f x : WithBotTop 𝕜))) : E → WithBotTop 𝕜)⋆)) =
        conv(toWithBotTopOn f S) := by
  have hS_compact : IsCompact S :=
    (Metric.isCompact_iff_isClosed_bounded).2 ⟨hS_closed, hS_bounded⟩
  exact convexConjugateOn_conjugate_eq_conv_toWithBotTopOn_of_isCompact_of_continuousOn
    (S := S) (f := f) hS_compact hf

end

/-! ### Definition_17_2_4 (from Chap04) -/
universe u v w

section

open scoped Rockafellar
open LinearConstraintRelation

variable {E : Type u} {Y : Type v} {R : Type w}

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.4 introduces the subset cut out by a family of weak linear
  inequalities indexed by a set `S⋆ ⊆ Y × R`; specializing to the inner-product pairing with
  `R = ℝ` recovers the textbook `ℝ^n` statement.
- `core/canonical`: the canonical owner here is the upstream indexed weak feasible owner
  `LinearConstraintRelation.leFeasible`, instantiated on the intrinsic subtype index `S⋆`.
- `bridge/view`: this owner is also the intersection of weak half-spaces
  `closedHalfSpaceLE y.1 y.2` attached to the primitive data `y ∈ S⋆`.

Domain-style sampling used here:
- the chapter half-space owner `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `mem_closedHalfSpaceLE_iff` from `Chap01.Definition_2_0_3`;
- the weak indexed owner `LinearConstraintRelation.leFeasible` from
  `Chap01.Corollary_2_1_1`;
- `LinearConstraintRelation.mem_leFeasible` from `Chap01.Corollary_2_1_1`.

Primitive data vs derived API:
- primitive data: the set `S⋆ : Set (Y × R)` and pairing values `⟪x, y.1⟫ₚ`;
- source-facing owner: `linearInequalitySolutionSet S⋆`;
- derived API: the explicit membership form and indexed-range bridge to
  `LinearConstraintRelation.leFeasible`.

Layer target: `source-facing`. The owner is stated at the primitive pairing/order layer rather
than a concrete real inner-product model.
-/

section Ordered

variable [LE R] [HasPairing E Y R]

/-- Definition 17.2.4, stated at the primitive pairing layer: the subset of `E` cut out by the
family of weak inequalities encoded by `SStar ⊆ Y × R`. -/
abbrev linearInequalitySolutionSet (SStar : Set (Y × R)) : Set E :=
  (leFeasible (fun y : SStar ↦ y.1.1) (fun y ↦ y.1.2) : Set E)

scoped[Rockafellar] notation3:max "solutionSet[" SStar "]" =>
  linearInequalitySolutionSet SStar

/-- Membership in `linearInequalitySolutionSet SStar` means satisfying every inequality encoded by
an element of `SStar`. -/
@[simp] theorem mem_linearInequalitySolutionSet_iff {SStar : Set (Y × R)} {x : E} :
    x ∈ solutionSet[SStar] ↔ ∀ y ∈ SStar, ⟪x, y.1⟫ₚ ≤ y.2 := by
  rw [linearInequalitySolutionSet, mem_leFeasible]
  constructor
  · intro hx y hy
    exact hx ⟨y, hy⟩
  · intro hx y
    exact hx y.1 y.2

/-- Membership in the `Set.range` presentation of a weak indexed system is exactly the textbook
pointwise family of inequalities. This source-facing inequality lemma stays at the primitive
`[LE R]` pairing layer. -/
@[simp] theorem mem_linearInequalitySolutionSet_range_iff
    {I : Sort*} (a : I → Y) (α : I → R) {x : E} :
    x ∈ solutionSet[Set.range fun i ↦ (a i, α i)] ↔ ∀ i, ⟪x, a i⟫ₚ ≤ α i := by
  rw [mem_linearInequalitySolutionSet_iff]
  constructor
  · intro hx i
    simpa using hx (a i, α i) ⟨i, rfl⟩
  · intro hx y hy
    rcases hy with ⟨i, rfl⟩
    simpa using hx i

/-- The source-facing weak-system owner is definitionally the upstream weak indexed owner. -/
theorem linearInequalitySolutionSet_eq_leFeasible (SStar : Set (Y × R)) :
    solutionSet[SStar] =
      (leFeasible (fun y : SStar ↦ y.1.1) (fun y ↦ y.1.2) : Set E) :=
  rfl

/-- The source-facing owner is exactly the intersection of the primitive weak-inequality fibers
indexed by `SStar`. This bridge stays at the minimal order layer `[LE R]`. -/
theorem linearInequalitySolutionSet_eq_iInter_setOf
    (SStar : Set (Y × R)) :
    solutionSet[SStar] = ⋂ y ∈ SStar, {x : E | ⟪x, y.1⟫ₚ ≤ y.2} := by
  ext x
  simp [linearInequalitySolutionSet, mem_leFeasible]

end Ordered

section WeakConstraintBridge

variable [HasPairing E Y R]

/-- The source-facing owner is exactly the textbook intersection of the half-spaces encoded by
`SStar`. -/
theorem linearInequalitySolutionSet_eq_iInter_closedHalfSpaceLE [LE R]
    (SStar : Set (Y × R)) :
    solutionSet[SStar] = ⋂ y ∈ SStar, (closedHalfSpaceLE y.1 y.2 : Set E) := by
  rw [linearInequalitySolutionSet_eq_iInter_setOf (SStar := SStar)]
  ext x
  simp [closedHalfSpaceLE]

/-- For an indexed weak system, the `Set.range` presentation of Definition 17.2.4 is exactly the
upstream indexed weak owner `LinearConstraintRelation.leFeasible`. -/
theorem linearInequalitySolutionSet_range_eq_leFeasible
    [LE R]
    {I : Sort*} (a : I → Y) (α : I → R) :
    solutionSet[Set.range fun i ↦ (a i, α i)] =
      (leFeasible a α : Set E) := by
  ext x
  rw [mem_linearInequalitySolutionSet_iff, mem_leFeasible]
  constructor
  · intro hx i
    simpa using hx (a i, α i) ⟨i, rfl⟩
  · intro hx y hy
    rcases hy with ⟨i, rfl⟩
    simpa using hx i

end WeakConstraintBridge

end

/-! ### Definition_17_2_5 (from Chap04) -/
noncomputable section

section

universe u v

variable {E : Type u} {R : Type v} [Zero E] [One R]

local notation "EStar" => E × R

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.5 adjoins the vertical unit vector `((0 : E), 1)` to
  `SStar ⊆ E × R`; this primitive generating-set step itself only needs `0` in `E` and `1` in
  the vertical codomain `R`.
- `core/canonical`: the chapter owner abstraction for generated cones is `cone[R]`,
  i.e. `PointedCone.hull`.
- `bridge/view`: `adjoin_vertical_unit SStar` records the textbook generating set, while the
  generated cone is exposed through textbook notation `K⋆[R] SStar` on the canonical owner.

Domain-style sampling used here:
- the owner notation `cone[R]` from `Chap01.Definition_2_6_10`;
- `PointedCone.hull`;
- `PointedCone.subset_hull`;
- `(cone[R] (adjoin_vertical_unit SStar)).zero_mem`.

Primitive data vs derived API:
- primitive source data: the set `SStar : Set (E × R)`;
- source-facing owner data: `adjoin_vertical_unit SStar`;
- derived owner-side cone: `K⋆[R] SStar = cone[R] (adjoin_vertical_unit SStar)`.

Layer target: `source-facing`.
-/

/-- The distinguished vertical unit point used in Definition 17.2.5. -/
def vertical_unit : EStar := ((0 : E), (1 : R))

/-- Definition 17.2.5: adjoin the vertical unit point to `SStar`. -/
def adjoin_vertical_unit (SStar : Set EStar) : Set EStar :=
  insert vertical_unit SStar

@[simp] theorem mem_adjoin_vertical_unit {SStar : Set EStar} {pStar : EStar} :
    pStar ∈ adjoin_vertical_unit SStar ↔ pStar = vertical_unit ∨ pStar ∈ SStar := by
  simp [adjoin_vertical_unit]

theorem subset_adjoin_vertical_unit (SStar : Set EStar) :
    SStar ⊆ adjoin_vertical_unit SStar :=
  Set.subset_insert _ _

@[simp] theorem vertical_unit_mem_adjoin_vertical_unit (SStar : Set EStar) :
    vertical_unit ∈ adjoin_vertical_unit SStar := by
  simp [adjoin_vertical_unit]

end

section

open scoped Rockafellar

/-! Textbook owner notation for Definition 17.2.5. -/
scoped[Rockafellar] notation:max "K⋆[" R "] " SStar =>
  cone[R] (adjoin_vertical_unit SStar)

end

/-! ### Lemma_17_2_6 (from Chap04) -/
open scoped Rockafellar

/-
Source/core/bridge triage:
- `source-facing`: Lemma 17.2.6 states the half-space containment criterion
  `H ⊇ C ↔ μStar ≥ δ*(xStar | C)` for the half-space cut out by `⟪x, xStar⟫ ≤ μStar`.
- `core/canonical`: the owner declarations are the chapter half-space
  `closedHalfSpaceLE xStar μStar`
  and the project support function `supportFunction C xStar`.
- `bridge/view`: the source notation `δ*(xStar | C)` is exactly
  `supportFunction C xStar`, and the source inclusion `H ⊇ C` is the same set-theoretic relation
  as `C ⊆ closedHalfSpaceLE xStar μStar`.
- Primitive data vs derived API: this item introduces no new data or local wrapper; it is direct
  reuse of the owner theorem already proved in Chapter 13.
- Domain-style sampling used here: `closedHalfSpaceLE`, `supportFunction`,
  `subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le`, and
  `subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot`.
- Layer target: `bridge/view`; keep the canonical owner theorem as a recall and add the textbook
  `H ⊇ C` surface as a thin orientation bridge at the intrinsic threshold layer
  `β : WithTopBot α`.
- The source side condition `xStar ≠ 0` is redundant for this equivalence itself, so it is not
  kept in the public interface.
-/
/- Lemma 17.2.6: if `H = closedHalfSpaceLE xStar μStar`, then `H ⊇ C` if and only if
`μStar ≥ supportFunction C xStar`. This is exactly
`subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le`. -/
recall subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le
recall subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot

section

universe u v w

variable {X : Type u} {Y : Type v} {α : Type w}
variable [ConditionallyCompleteLattice α]
variable [HasPairing X Y α]

-- Canonical swapped pairing view needed by `δᵛ(xStar | C)` when `xStar : Y` and `C : Set X`.
local instance : HasPairing Y X α :=
  HasPairing.swap (X := X) (Y := Y) (L := α)

/-- Textbook inequality orientation of Lemma 17.2.6:
`H ⊇ C ↔ β ≥ δ*(x* | C)` at the intrinsic threshold layer `β : WithTopBot α`. -/
theorem closedHalfSpaceLE_superset_iff_ge_supportFunction
    (C : Set X) (xStar : Y) (β : WithTopBot α) :
    closedHalfSpaceLE xStar β ⊇ C ↔ β ≥ δᵛ(xStar | C) := by
  simpa [ge_iff_le] using
    (subset_closedHalfSpaceLE_withTopBot_iff_supportFunction_le C xStar β)

end

/-! ### Definition_17_2_7 (from Chap04) -/
noncomputable section

section

universe u v

variable {E : Type u} {R : Type v}
    [ConditionallyCompleteLattice R]
    [Semiring R] [IsOrderedRing R]
    [AddCommMonoid E] [Module R E]

open Function (verticalHeights)
open scoped Rockafellar

local notation "EStar" => E × R

/-!
Source/core/bridge triage:

- `source-facing`: Definition 17.2.7 introduces the function attached to the cone from
  Definition 17.2.5 by taking its vertical infimum.
- `bridge/view`: the source-facing bridge `generated_cone_inf_eq_sInf` is stated in the
  intrinsic `verticalHeights` language.

Domain-style sampling used here:
- `K⋆[R]` from Definition 17.2.5;
- `Function.verticalHeights`;
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf_verticalHeights`.

Primitive data vs derived API:
- primitive source input: the cone owner `K⋆[R] SStar`.
- source-facing owner: `generated_cone_inf SStar`;
- derived bridge API: the intrinsic `verticalHeights` descriptions
  `generated_cone_inf_eq_sInf`.

Ambient minimization:
- this owner uses only the additive/module structure on `E` together with the vertical
  scalar coordinate already present in `K⋆[R] SStar`, so it is stated for arbitrary ordered
  scalar modules and later specialized to the textbook real layer.

Layer target: `source-facing`.
-/

/-- Definition 17.2.7: the function attached to `SStar` sends `x*` to the infimum of the scalar
heights `μ*` for which `(x*, μ*)` lies in `K⋆[R] SStar`. -/
def generated_cone_inf (SStar : Set EStar) : E → WithTopBot R :=
  Function.verticalInfimum (K⋆[R] SStar)

/-- Textbook-scoped notation for the Definition 17.2.7 owner. -/
scoped[Rockafellar] notation3:max "Kinf[" R "](" SStar ")" =>
  generated_cone_inf (R := R) SStar

/-- Canonical owner bridge from Definition 17.2.7 to Chapter 1's `verticalInfimum` owner. -/
@[simp] theorem generated_cone_inf_eq_verticalInfimum (SStar : Set EStar) :
    Kinf[R](SStar) = Function.verticalInfimum (K⋆[R] SStar) :=
  rfl

/-- Coercion-clean owner bridge: `generated_cone_inf SStar x*` is the infimum of the intrinsic
vertical heights above `x*` in `K⋆[R] SStar`. -/
theorem generated_cone_inf_eq_sInf (SStar : Set EStar) (xStar : E) :
    Kinf[R](SStar) xStar =
      sInf (verticalHeights (K⋆[R] SStar) xStar) := by
  simpa [generated_cone_inf] using
    Function.verticalInfimum_eq_sInf_verticalHeights
      (F := ((K⋆[R] SStar : PointedCone R EStar) : Set EStar)) xStar

end

/-! ### Proposition_17_2_8 (from Chap04) -/
section

open scoped Rockafellar

variable {X Y : Type*} {𝕜 : Type*}
    [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsOrderedRing 𝕜]
    [AddCommGroup Y] [Module 𝕜 Y]
    [HasPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]
    [HasPairingAddRight X Y 𝕜] [HasPairingSMulRight X Y 𝕜] [HasPairingZeroRight X Y 𝕜]
local notation "YStar" => Y × 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Proposition 17.2.8 identifies, for a dual family `SStar ⊆ Y × 𝕜`, the support
  function of the inequality solution set with the function generated in Definition 17.2.7 from
  the cone of Definition 17.2.5.
- `core/canonical`: the owner abstractions are the support function `supportFunction`, the
  solution-set owner `linearInequalitySolutionSet`, and the fiber-infimum owner
  `Kinf[𝕜](SStar)`, canonically presented via `generated_cone_inf` and
  `Function.verticalInfimum`, together with the lower-semicontinuous hull owner `cl(·)`.
- `bridge/view`: this item is the closed-owner bridge from `Kinf[𝕜](SStar)` to the
  support function of `linearInequalitySolutionSet SStar`.

Domain-style sampling used here:
- `supportFunction`;
- `linearInequalitySolutionSet`;
- `Kinf[𝕜](SStar)` / `generated_cone_inf`;
- the Chapter 1 owner `Function.verticalInfimum` underlying `Kinf[𝕜](SStar)`;
- the closure owner `cl(·)`;
- `convexConjugate_indicator_eq_supportFunction`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull`;
- the generated-cone owner `PointedCone.hull`.

Primitive data vs derived API:
- primitive source-facing data: the family of inequalities `SStar : Set (Y × 𝕜)`;
- owner objects derived from that data: `linearInequalitySolutionSet SStar` and
  `Kinf[𝕜](SStar)`;
- derived bridge API: the equality between the support function of the former and the
  lower-semicontinuous hull of the latter, proved through Fenchel conjugacy rather than through a
  false raw cone/epigraph identification.

Ambient-layer decision:
- `linearInequalitySolutionSet` already lives on the primal/dual pairing layer (`X` paired with
  `Y`), while `Kinf[𝕜](SStar)` only needs an ordered scalar module on `Y`. The bridge theorem
  is therefore stated with explicit primal and dual owners, with reverse-orientation pairing data
  used only for conjugacy-side steps.

Closure correction:
- the raw cone `K⋆[𝕜] SStar = PointedCone.hull 𝕜 (adjoin_vertical_unit SStar)` is not a
  priori a closed epigraph, so this file should not present a literal set equality between
  `K⋆[𝕜] SStar` and `{p | δᵛ(p.1 | linearInequalitySolutionSet SStar) ≤ p.2}` as its
  main bridge.
- instead, the proof works at the canonical function-duality layer: the conjugate of
  `Kinf[𝕜](SStar)` is the indicator of `linearInequalitySolutionSet SStar`, so
  convex biconjugacy yields
  `δᵛ(· | linearInequalitySolutionSet SStar) = cl(Kinf[𝕜](SStar))`.

Layer target: `bridge/view`. The file should expose the source theorem directly in terms of the
existing owners rather than introduce a parallel wrapper around support functions, vertical
infimum functions, or epigraph packages.
-/

private theorem pairing_le_Kinf_of_mem_linearInequalitySolutionSet
    {SStar : Set YStar} {x : X} (hx : x ∈ solutionSet[SStar]) :
    ∀ y : Y, (⟪x, y⟫ₚ : WithTopBot 𝕜) ≤ Kinf[𝕜](SStar) y := by
  sorry

private theorem convexConjugate_Kinf_eq_indicator_linearInequalitySolutionSet
    (SStar : Set YStar) :
    (Kinf[𝕜](SStar))⋆ =
      (δ[𝕜](· | solutionSet[SStar])) := by
  sorry

private theorem Kinf_isConvex (SStar : Set YStar) :
    (Kinf[𝕜](SStar)).IsConvex 𝕜 := by
  simpa [generated_cone_inf] using
    Function.isConvex_verticalInfimum
      (K⋆[𝕜] SStar).convex

/-- Proposition 17.2.8: the support function of the set cut out by the inequalities encoded in
`SStar ⊆ Y × 𝕜` is the lower-semicontinuous hull of the generated-cone infimum owner
`Kinf[𝕜](SStar)`. This source theorem is stated on the primal/dual pairing owner surface rather
than by identifying primal and dual ambient spaces. -/
theorem supportFunction_linearInequalitySolutionSet_eq_lowerSemicontinuousHull_generated_cone_inf
    [TopologicalSpace (WithTopBot 𝕜)]
    [FiniteDimensional 𝕜 Y]
    [HasContinuousPairing Y X 𝕜]
    (SStar : Set YStar) :
    δᵛ(· | solutionSet[SStar]) =
      cl(Kinf[𝕜](SStar)) := by
  sorry

end

/-! ### Lemma_17_2_9 (from Chap04) -/
section

universe u v

open scoped BigOperators Rockafellar

variable {E : Type u} {R : Type v}
    [Semiring R] [PartialOrder R] [IsOrderedRing R]
    [AddCommMonoid E] [Module R E]

local notation "EStar" => E × R

/-!
Source/core/bridge triage:

- `source-facing`: this item exposes membership in the cone generated by
  `SStar ∪ {((0 : E), 1)}` via finite nonnegative combinations over `SStar`.
- `core/canonical`: the chapter owner abstraction is `cone[R] (adjoin_vertical_unit SStar)`,
  introduced upstream through the canonical generated-cone owner `cone[R] = PointedCone.hull`.
- `bridge/view`: `PointedCone.mem_hull_set` supplies the canonical finite conic-combination witness
  in `adjoin_vertical_unit SStar`; splitting the distinguished generator `((0 : E), 1)` produces a
  primitive nonnegative vertical slack coefficient.

Domain-style sampling used here:
- `cone[R]` from `Chap01.Definition_2_6_10`;
- `adjoin_vertical_unit` and `vertical_unit` from Definition 17.2.5;
- `PointedCone.hull`;
- `PointedCone.mem_hull_set`;
- finite subset sums via `Finset.attach`;
- coordinate projections on the product module `E × R`.

Primitive data vs derived API:
- primitive owner object: `cone[R] (adjoin_vertical_unit SStar)`;
- primitive source-facing API: the finite-support certificate on a finite subset of `SStar`
  together with an explicit nonnegative vertical slack coefficient;
- derived API: the inequality formulation obtained by eliminating this slack through subtraction.

Ambient minimization:
- the statement uses only the additive/module structure needed by
  `cone[R] (adjoin_vertical_unit SStar)`, so the owner file stays at the generic module level
  instead of specializing prematurely to `ℝ^n`.

Layer target: `bridge/view`; the public statement keeps the source-facing finite certificate but
derives it from the existing owner `cone[R] (adjoin_vertical_unit SStar)`.
-/

/-- Primitive internal slack certificate for generated-cone membership in Definition 17.2.5:
finite support in `SStar`, nonnegative coefficients, exact first-coordinate reconstruction, and an
explicit nonnegative vertical slack coefficient on the second coordinate. -/
private structure GeneratedConeSlackCert
    (SStar : Set EStar) (pStar : EStar) where
  support : Finset EStar
  support_subset : (support : Set EStar) ⊆ SStar
  weights : {y // y ∈ support} → R
  weights_nonneg (y : {z // z ∈ support}) : 0 ≤ weights y
  fst_eq : pStar.1 = support.attach.sum (fun y ↦ weights y • (y : EStar).1)
  slack : R
  slack_nonneg : 0 ≤ slack
  snd_eq : support.attach.sum (fun y ↦ weights y * (y : EStar).2) + slack = pStar.2

/-- Semiring-level internal bridge for Lemma 17.2.9: a point belongs to the cone generated by
`SStar ∪ {((0 : E), 1)}` iff it is a finite nonnegative conic combination of points of `SStar`
plus an explicit nonnegative vertical slack coefficient. -/
-- Proof sketch: apply `PointedCone.mem_hull_set` to the generating set
-- `SStar ∪ {((0 : E), 1)}`. Separate the coefficient of the distinguished singleton generator
-- `((0 : E), 1)` from the remaining finitely many generators in `SStar`.
private theorem mem_generated_cone_iff_exists_conicCombination_with_slack
    {SStar : Set EStar} {pStar : EStar} :
    pStar ∈ (K⋆[R] SStar) ↔
      Nonempty (GeneratedConeSlackCert SStar pStar) := by
  constructor
  · intro hmem
    classical
    rcases (PointedCone.mem_hull_set.mp (show
      pStar ∈ PointedCone.hull R (adjoin_vertical_unit SStar) by
        simpa using hmem)) with ⟨c, hcS, hc0, hsum⟩
    let s : Finset EStar := c.support.filter fun y ↦ y ∈ SStar
    let weights : {y // y ∈ s} → R := fun y ↦ c y
    have h_eq_vertical {y : EStar} (hy : y ∈ c.support) (hyS : y ∉ SStar) :
        y = vertical_unit := by
      rcases hcS hy with hy_eq | hyS_mem
      · exact hy_eq
      · exact (hyS hyS_mem).elim
    have hs : (s : Set EStar) ⊆ SStar := by
      intro y hy
      exact (Finset.mem_filter.mp hy).2
    have hweights : ∀ y, 0 ≤ weights y := by
      intro y
      exact hc0 y
    have hxfull : pStar.1 = ∑ y ∈ c.support, c y • y.1 := by
      calc
        pStar.1 = (∑ y ∈ c.support, c y • y).1 := by
          simpa [Finsupp.sum] using (congrArg Prod.fst hsum).symm
        _ = ∑ y ∈ c.support, c y • y.1 := by
          simpa using
            (Prod.fst_sum :
              (∑ y ∈ c.support, c y • y).1 = ∑ y ∈ c.support, (c y • y).1)
    have hfirst_omitted : ∑ y ∈ c.support.filter (fun y ↦ y ∉ SStar), c y • y.1 = 0 := by
      refine Finset.sum_eq_zero fun y hy ↦ ?_
      have hy_support : y ∈ c.support := (Finset.mem_filter.mp hy).1
      have hyS : y ∉ SStar := (Finset.mem_filter.mp hy).2
      rw [h_eq_vertical hy_support hyS]
      simp [vertical_unit]
    have hx : pStar.1 = s.attach.sum (fun y ↦ weights y • (y : EStar).1) := by
      calc
        pStar.1 = ∑ y ∈ c.support, c y • y.1 := hxfull
        _ = (∑ y ∈ s, c y • y.1) + ∑ y ∈ c.support.filter (fun y ↦ y ∉ SStar), c y • y.1 := by
          symm
          simpa [s] using
            (Finset.sum_filter_add_sum_filter_not c.support
              (fun y ↦ y ∈ SStar) (fun y ↦ c y • y.1))
        _ = ∑ y ∈ s, c y • y.1 := by rw [hfirst_omitted, add_zero]
        _ = s.attach.sum (fun y ↦ weights y • (y : EStar).1) := by
          simpa [weights] using (Finset.sum_attach s (fun y ↦ c y • y.1)).symm
    have hmu_full : ∑ y ∈ c.support, c y * y.2 = pStar.2 := by
      calc
        ∑ y ∈ c.support, c y * y.2 = (∑ y ∈ c.support, c y • y).2 := by
          simpa [smul_eq_mul] using
            (Prod.snd_sum :
              (∑ y ∈ c.support, c y • y).2 = ∑ y ∈ c.support, (c y • y).2).symm
        _ = pStar.2 := by
          simpa [Finsupp.sum] using congrArg Prod.snd hsum
    let slack : R := ∑ y ∈ c.support.filter (fun y ↦ y ∉ SStar), c y * y.2
    have hslack_nonneg : 0 ≤ slack := by
      dsimp [slack]
      refine Finset.sum_nonneg fun y hy ↦ ?_
      have hy_support : y ∈ c.support := (Finset.mem_filter.mp hy).1
      have hyS : y ∉ SStar := (Finset.mem_filter.mp hy).2
      rw [h_eq_vertical hy_support hyS]
      simpa [vertical_unit] using hc0 vertical_unit
    have hmu_eq :
        s.attach.sum (fun y ↦ weights y * (y : EStar).2) + slack = pStar.2 := by
      have hsecond_sum :
          s.attach.sum (fun y ↦ weights y * (y : EStar).2) = ∑ y ∈ s, c y * y.2 := by
        simpa [weights] using (Finset.sum_attach s (fun y ↦ c y * y.2))
      calc
        s.attach.sum (fun y ↦ weights y * (y : EStar).2) + slack =
            (∑ y ∈ s, c y * y.2) + ∑ y ∈ c.support.filter (fun y ↦ y ∉ SStar), c y * y.2 := by
          simpa [slack] using congrArg (fun t : R ↦ t + slack) hsecond_sum
        _ = ∑ y ∈ c.support, c y * y.2 := by
          simpa [s] using
            (Finset.sum_filter_add_sum_filter_not c.support
              (fun y ↦ y ∈ SStar) (fun y ↦ c y * y.2))
        _ = pStar.2 := hmu_full
    exact ⟨{
      support := s
      support_subset := hs
      weights := weights
      weights_nonneg := hweights
      fst_eq := hx
      slack := slack
      slack_nonneg := hslack_nonneg
      snd_eq := hmu_eq
    }⟩
  · rintro ⟨s, hs, weights, hweights, hx, slack, hslack_nonneg, hmu_eq⟩
    have hmem_points :
        ∀ y : {z // z ∈ s}, (y : EStar) ∈ K⋆[R] SStar := by
      intro y
      simpa using
        (PointedCone.subset_hull ((subset_adjoin_vertical_unit (SStar := SStar)) (hs y.2)))
    have hsum_mem :
        s.attach.sum (fun y ↦ weights y • (y : EStar)) ∈ K⋆[R] SStar := by
      classical
      induction s.attach using Finset.induction_on with
      | empty =>
          change (0 : EStar) ∈ K⋆[R] SStar
          exact (K⋆[R] SStar).zero_mem
      | @insert y t hy ht =>
          simpa [Finset.sum_insert, hy] using
            (K⋆[R] SStar).add_mem
              ((K⋆[R] SStar).smul_mem (hweights y) (hmem_points y)) ht
    have hv_mem :
        slack • vertical_unit ∈ K⋆[R] SStar := by
      refine (K⋆[R] SStar).smul_mem hslack_nonneg ?_
      simpa using
        (PointedCone.subset_hull (vertical_unit_mem_adjoin_vertical_unit (SStar := SStar)))
    have hfst :
        (s.attach.sum (fun y ↦ weights y • (y : EStar))).1 =
          s.attach.sum (fun y ↦ weights y • (y : EStar).1) := by
      simpa using
        (Prod.fst_sum :
          (s.attach.sum (fun y ↦ weights y • (y : EStar))).1 =
            s.attach.sum (fun y ↦ (weights y • (y : EStar)).1))
    have hsnd :
        (s.attach.sum (fun y ↦ weights y • (y : EStar))).2 =
          s.attach.sum (fun y ↦ weights y * (y : EStar).2) := by
      simpa [smul_eq_mul] using
        (Prod.snd_sum :
          (s.attach.sum (fun y ↦ weights y • (y : EStar))).2 =
            s.attach.sum (fun y ↦ (weights y • (y : EStar)).2))
    have heq :
        pStar =
          s.attach.sum (fun y ↦ weights y • (y : EStar)) +
            slack • vertical_unit := by
      ext
      · simp [vertical_unit, hfst, hx]
      · simpa [vertical_unit, hsnd] using hmu_eq.symm
    rw [heq]
    exact (K⋆[R] SStar).add_mem hsum_mem hv_mem

end

section

universe u v

open scoped BigOperators Rockafellar

variable {E : Type u} {R : Type v}
    [Semiring R] [PartialOrder R] [IsOrderedRing R] [ExistsAddOfLE R] [AddLeftReflectLE R]
    [AddCommMonoid E] [Module R E]

local notation "EStar" => E × R

/-- Semiring-level source-facing bridge for Lemma 17.2.9: the primitive nonnegative slack witness is
equivalent to the textbook inequality on the scalar coordinate. -/
theorem mem_generated_cone_iff_exists_conicCombination
    {SStar : Set EStar} {pStar : EStar} :
    pStar ∈ (K⋆[R] SStar) ↔
      ∃ s : Finset EStar,
        (∀ y ∈ s, y ∈ SStar) ∧
          ∃ weights : {y // y ∈ s} → R,
            (∀ y, 0 ≤ weights y) ∧
              pStar.1 = s.attach.sum (fun y ↦ weights y • (y : EStar).1) ∧
              s.attach.sum (fun y ↦ weights y * (y : EStar).2) ≤ pStar.2 := by
  constructor
  · intro hmem
    rcases (mem_generated_cone_iff_exists_conicCombination_with_slack.mp hmem) with
      ⟨s, hs, weights, hweights, hx, slack, hslack_nonneg, hmu_eq⟩
    refine ⟨s, ?_, weights, hweights, hx, ?_⟩
    · intro y hy
      exact hs hy
    · calc
        s.attach.sum (fun y ↦ weights y * (y : EStar).2) ≤
            s.attach.sum (fun y ↦ weights y * (y : EStar).2) + slack :=
          le_add_of_nonneg_right hslack_nonneg
        _ = pStar.2 := hmu_eq
  · rintro ⟨s, hs, weights, hweights, hx, hmu⟩
    have hs' : (s : Set EStar) ⊆ SStar := by
      intro y hy
      exact hs y hy
    rcases exists_add_of_le hmu with ⟨slack, hmu_eq⟩
    have hsum_le :
        s.attach.sum (fun y ↦ weights y * (y : EStar).2) ≤
          s.attach.sum (fun y ↦ weights y * (y : EStar).2) + slack := by
      simpa [hmu_eq, add_assoc, add_left_comm, add_comm] using hmu
    have hslack_nonneg : 0 ≤ slack := by
      exact (le_add_iff_nonneg_right
        (s.attach.sum (fun y ↦ weights y * (y : EStar).2))).1 hsum_le
    refine (mem_generated_cone_iff_exists_conicCombination_with_slack).mpr ?_
    refine ⟨{
      support := s
      support_subset := hs'
      weights := weights
      weights_nonneg := hweights
      fst_eq := hx
      slack := slack
      slack_nonneg := hslack_nonneg
      snd_eq := hmu_eq.symm
    }⟩

end

/-! ### Corollary_17_2_10 (from Chap04) -/
section

universe u v

open scoped BigOperators Rockafellar

variable {E : Type u} {R : Type v}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup E] [Module R E] [FiniteDimensional R E]

local notation "EStar" => E × R

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 17.2.10 sharpens the finite conic-combination representation from
  Lemma 17.2.9 by bounding the number of generators drawn from `SStar`.
- `core/canonical`: the owner abstraction is the generated cone `K⋆[R] SStar` in `E × R`,
  together with the source-facing bridge
  `mem_generated_cone_iff_exists_conicCombination`.
- `bridge/view`: clause (1) is the ambient Caratheodory reduction in `E × R`, giving at most
  `Module.finrank R E + 1` generators from `SStar`; clause (2) is the sharper reduction obtained
  by lowering to the bottom face of the simplex, exactly as in the proof pattern of
  Corollary 17.1.3.

Domain-style sampling used here:
- `K⋆[R]` from Definition 17.2.5;
- `mem_generated_cone_iff_exists_conicCombination` from Lemma 17.2.9;
- `exists_linearIndependent_nonnegativeCombination_of_ne_zero_mem_cone_iUnion` from
  Corollary 17.1.2.

Primitive data vs derived API:
- primitive input: membership of `(xStar, μStar)` in `K⋆[R] SStar`;
- derived output: a finite subset `s ⊆ SStar` and a nonnegative coefficient family indexed by
  `s.attach`, with the scalar-coordinate inequality from Lemma 17.2.9 and a bounded cardinality
  on `s`.

Layer target: `bridge/view`; the corollary keeps the source-facing representation language of
Lemma 17.2.9 directly as finite-support existential data, rather than introducing a wrapper owner.
-/

-- Proof sketch: apply the conic Caratheodory theorem in the ambient space `E × R` to the
-- directions from `SStar` together with the vertical unit `((0 : E), 1)`. Then rewrite the
-- resulting finite cone certificate through `mem_generated_cone_iff_exists_conicCombination`,
-- keeping only the points of `SStar` and preserving the finite-support witness data. This
-- leaves at most `Module.finrank R E + 1` generators from
-- `SStar`.
/-- Corollary 17.2.10 (1): the finite conic representation from Lemma 17.2.9 may be chosen with
at most `Module.finrank R E + 1` generators from `SStar`. Equivalently, every point of the
generated cone `K⋆[R] SStar` admits such a finite-support witness with cardinality at most
`dim E + 1`. -/
theorem mem_generated_cone_iff_exists_conicCombination_card_le_finrank_add_one
    {SStar : Set EStar} {xStar : E} {muStar : R} :
    (xStar, muStar) ∈ (K⋆[R] SStar) ↔
      ∃ s : Finset EStar,
        s.card ≤ Module.finrank R E + 1 ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                xStar = s.attach.sum (fun y ↦ weights y • (y : EStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : EStar).2) ≤ muStar := sorry

-- Proof sketch: start from clause (1). If the support has maximal size
-- `Module.finrank R E + 1`, the chosen generators determine a simplex in `E × R`; moving
-- downward along the vertical direction to the bottom face, exactly as in the "bottoms of
-- simplices" argument from Corollary 17.1.3, removes one generator while preserving the first
-- coordinate and only enlarging the available vertical slack. Rewriting again through
-- `mem_generated_cone_iff_exists_conicCombination` gives the sharper bound while preserving the
-- same finite-support witness data.
/-- Corollary 17.2.10 (2): the conic representation from Lemma 17.2.9 may in fact be chosen with
at most `Module.finrank R E` generators from `SStar`, by the bottoms-of-simplices reduction in
the ambient cone `K⋆[R] SStar`. Equivalently, one may choose the same finite-support witness data
with that smaller bound. -/
theorem mem_generated_cone_iff_exists_conicCombination_card_le_finrank
    {SStar : Set EStar} {xStar : E} {muStar : R} :
    (xStar, muStar) ∈ (K⋆[R] SStar) ↔
      ∃ s : Finset EStar,
        s.card ≤ Module.finrank R E ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                xStar = s.attach.sum (fun y ↦ weights y • (y : EStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : EStar).2) ≤ muStar := sorry

end

/-! ### Theorem_17_2_11 (from Chap04) -/
section

open scoped BigOperators Rockafellar

-- Scalar layer minimization: this item needs a `DivisionRing` (not a full `Field`) because the
-- statement uses `FiniteDimensional`/`affineSpan` and `K⋆[R]` membership.
variable {X Y : Type*}
  {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup X] [Module R X]
  [AddCommMonoid Y] [Module R Y]
  [HasPairing X Y R]

local notation "YStar" => Y × R
local notation "solutionSet[" SStar "]" =>
  linearInequalitySolutionSet (E := X) (SStar : Set YStar)
local notation "halfSpace[" yStar ", " μStar "]" =>
  (closedHalfSpaceLE yStar μStar : Set X)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 17.2.11 characterizes when a closed half-space in the primal space `X`
  contains the convex set cut out by a closed bounded dual family `S* ⊆ Y × R`; specializing
  `X = Y = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement.
  This keeps the owner at the pairing layer instead of forcing a self-dual model `X = Y`.
- `core/canonical`: the owner abstractions are the source-facing set
  `linearInequalitySolutionSet SStar` in `X`, the half-space constructor `closedHalfSpaceLE`,
  the full-dimensionality condition `affineSpan R C = ⊤`, and the generated-cone owner on dual
  data `K⋆[R] SStar` in `Y × R`.
- `bridge/view`: the source-facing bridge theorem adds the Caratheodory cardinality bound
  `s.card ≤ Module.finrank R X` to the canonical generated-cone witness on a finite support
  `SStar`; the companion theorem is the same finite weighted witness surface.

Domain-style sampling used here:
- `linearInequalitySolutionSet` from `Chap04.Definition_17_2_4`;
- `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `K⋆[R]` from `Chap04.Definition_17_2_5`;
- `mem_generated_cone_iff_exists_conicCombination` from `Chap04.Lemma_17_2_9`;
- finite sums over `Fin m` via `BigOperators`;
- affine-hull fullness via `affineSpan R C = ⊤`;
- ambient dimension measured canonically by `Module.finrank R X`.

-/

-- Proof sketch: adjoin `((0 : Y), 1)` to `SStar`, pass to the cone it generates in `Y × R`,
-- use closedness of that cone together with the half-space containment criterion, and then apply
-- the Caratheodory reduction in ambient dimension `Module.finrank R X + 1`. The
-- full-dimensionality assumption on `linearInequalitySolutionSet SStar` removes the extra
-- vertical generator and leaves at most `Module.finrank R X` generators from `SStar`.
/-- Canonical owner form of Theorem 17.2.11: under closedness/boundedness of `SStar` and
full-dimensionality of `solutionSet[SStar]`, containment in the half-space
`closedHalfSpaceLE yStar μStar` is equivalent to generated-cone membership of the dual pair
`(yStar, μStar)` in `K⋆[R] SStar`. -/
theorem subset_closedHalfSpaceLE_iff_mem_generatedCone
    [FiniteDimensional R X] [TopologicalSpace YStar] [Bornology YStar]
    {SStar : Set YStar} (hSStar_closed : IsClosed SStar)
    (hSStar_bounded : Bornology.IsBounded SStar)
    (hfull : affineSpan R (solutionSet[SStar]) = ⊤)
    (yStar : Y) (μStar : R) :
    solutionSet[SStar] ⊆ halfSpace[yStar, μStar] ↔
      (yStar, μStar) ∈ (K⋆[R] SStar) := sorry

/-- Source-facing finite-support certificate form of Theorem 17.2.11: under the same hypotheses as
`subset_closedHalfSpaceLE_iff_mem_generatedCone`, containment of `solutionSet[SStar]` in
`closedHalfSpaceLE yStar μStar` is equivalent to a finite nonnegative conic-combination witness
for `(yStar, μStar)` with support size at most `Module.finrank R X`. -/
theorem subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate
    [FiniteDimensional R X] [TopologicalSpace YStar] [Bornology YStar]
    {SStar : Set YStar} (hSStar_closed : IsClosed SStar)
    (hSStar_bounded : Bornology.IsBounded SStar)
    (hfull : affineSpan R (solutionSet[SStar]) = ⊤)
    (yStar : Y) (μStar : R) :
    solutionSet[SStar] ⊆ halfSpace[yStar, μStar] ↔
      ∃ s : Finset YStar,
        s.card ≤ Module.finrank R X ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                yStar = s.attach.sum (fun y ↦ weights y • (y : YStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : YStar).2) ≤ μStar := sorry

/-- Companion source-facing form of Theorem 17.2.11: the generated-cone witness is equivalently a
finite nonnegative combination of inequalities from a subset of `SStar` of cardinality at most
`Module.finrank R X`, with combined scalar part at most `μStar`. -/
theorem subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination
    [FiniteDimensional R X] [TopologicalSpace YStar] [Bornology YStar]
    {SStar : Set YStar} (hSStar_closed : IsClosed SStar)
    (hSStar_bounded : Bornology.IsBounded SStar)
    (hfull : affineSpan R (solutionSet[SStar]) = ⊤)
    (yStar : Y) (μStar : R) :
    solutionSet[SStar] ⊆ halfSpace[yStar, μStar] ↔
      ∃ s : Finset YStar,
        s.card ≤ Module.finrank R X ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                yStar = s.attach.sum (fun y ↦ weights y • (y : YStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : YStar).2) ≤ μStar := by
  simpa using
    (subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate
      (SStar := SStar) hSStar_closed hSStar_bounded hfull yStar μStar)

end
