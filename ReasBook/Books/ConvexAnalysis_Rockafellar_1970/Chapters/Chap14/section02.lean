import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_14_2_1 (from Chap03) -/
section

open scoped PolarCone Rockafellar

variable {𝕜 E : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜]
variable [TopologicalSpace 𝕜] [TopologicalSpace (WithBotTop 𝕜)] [ClosedIciTopology 𝕜]
variable [IsOrderedAddMonoid 𝕜] [PosSMulMono 𝕜 𝕜]
variable [IsStrictOrderedRing 𝕜] [FloorRing 𝕜]
variable [TopologicalSpace E] [AddCommGroup E] [Module 𝕜 E]
variable [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasContinuousPairing E E 𝕜] [HasPairingSwap E E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 14.2.1 states that for a nonempty closed convex set `C`, the polar of
  the barrier cone of `C` is exactly the recession cone of `C`.
- `core/canonical`: the owner abstractions already present in the project are the set-valued
  operators `barrierCone`, `polarCone`, and `recessionCone`, together with the chapter owner
  theorem
  `polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate`.
- `bridge/view`: the source proof specializes that owner theorem to `supportFunction C`.
  `Text_13_0_4` identifies the effective domain of `supportFunction C` with `barrierCone C`,
  nonemptiness of `C` gives the owner-side properness of `supportFunction C`, Theorem 13.2
  rewrites the conjugate of `supportFunction C` as `indicatorFunction C`, and Theorem 8.7
  identifies the resulting function-side recession cone directly with the set-side recession cone
  `0⁺ C`.

Domain-style sampling used here:
- `barrierCone_eq_effectiveDomain_supportFunction` from `Text_13_0_4`;
- `polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate`
  from `Theorem_14_2`;
- `supportFunction_def` from `Defintion_4_8_2`;
- `convexConjugate_supportFunction_eq_indicatorFunction` from `Theorem_13_2`;
- `functionRecessionCone_indicatorFunction_eq_recessionCone` from `Theorem_8_7`.

Primitive data vs derived API:
- primitive input: the subset `C : Set E`;
- owner hypotheses: nonemptiness, closedness, and convexity of `C`;
- derived output: the direct set equality `(barrierCone C)ᵒ = 0⁺ C`.

Layer target: `source-facing`, stated directly with the chapter owners for barrier cones, polars,
and recession cones, while deriving the result through the upstream owner theorem instead of
rebuilding a parallel local support-function wrapper.

Ambient refinement: the supporting owner theorems already live on arbitrary finite-dimensional
ordered-field pairing spaces with continuous symmetric pairing, so the corollary is stated at that
intrinsic layer rather than the concrete coordinate model `EuclideanSpace ℝ (Fin n)`.
-/

-- Proof sketch: apply the owner theorem
-- `polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate` to
-- `supportFunction C`. The bridge `barrierCone_eq_effectiveDomain_supportFunction` identifies its
-- effective domain with `barrierCone C`, and the polar of a generated cone simplifies directly to
-- the polar of the underlying set in the source-facing polar owner. Nonemptiness of `C` gives the
-- properness of `supportFunction C` directly from `supportFunction_def`. Theorem 13.2 rewrites the
-- conjugate of `supportFunction C` as `indicatorFunction C`, and the Chapter 8 owner theorem
-- `functionRecessionCone_indicatorFunction_eq_recessionCone` finishes the source-facing set
-- identity.
/-- Corollary 14.2.1: the polar `(barrierCone C)ᵒ` of the barrier cone of a nonempty closed convex
set `C` is the recession cone of `C`. Specializing to `EuclideanSpace ℝ (Fin n)` recovers the
textbook `R^n` statement. -/
theorem polarCone_barrierCone_eq_recessionCone
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex 𝕜 C) :
    ((((barr[𝕜](C) : Set E)ᵒ[𝕜] : PointedCone 𝕜 E) : Set E)) = 0⁺[𝕜] C := by
  have hsupport_proper : (δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜).IsProper := by
    rw [Function.isProper_iff]
    refine ⟨?_, ?_⟩
    · rcases hC_nonempty with ⟨y, hy⟩
      refine ⟨(0 : E), ?_⟩
      rw [mem_effectiveDomain]
      have h_upper : δᵛ[WithBotTop 𝕜]((0 : E) | C) ≤ (0 : WithBotTop 𝕜) := by
        rw [supportFunction_def]
        refine iSup_le ?_
        intro z
        change ((⟪(0 : E), (z : E)⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ 0
        simp
      have h_lower : (0 : WithBotTop 𝕜) ≤ δᵛ[WithBotTop 𝕜]((0 : E) | C) := by
        calc
          (0 : WithBotTop 𝕜) = ((⟪(0 : E), y⟫ₚ : 𝕜) : WithBotTop 𝕜) := by simp
          _ ≤ δᵛ[WithBotTop 𝕜]((0 : E) | C) := by
            rw [supportFunction_def]
            exact le_iSup (fun z : C ↦ ((⟪(0 : E), (z : E)⟫ₚ : 𝕜) : WithBotTop 𝕜)) ⟨y, hy⟩
      have h_eq : δᵛ[WithBotTop 𝕜]((0 : E) | C) = 0 := le_antisymm h_upper h_lower
      have htop : δᵛ[WithBotTop 𝕜]((0 : E) | C) < ⊤ := by
        rw [h_eq]
        exact WithBotTop.coe_lt_top 0
      exact htop
    · intro x
      rcases hC_nonempty with ⟨y, hy⟩
      have hbot : (⊥ : WithBotTop 𝕜) < δᵛ[WithBotTop 𝕜](x | C) := by
        rw [supportFunction_def]
        exact lt_of_lt_of_le (WithBotTop.bot_lt_coe _) <|
          (le_iSup (fun z : C ↦ ((⟪x, (z : E)⟫ₚ : 𝕜) : WithBotTop 𝕜)) ⟨y, hy⟩)
      exact ne_of_gt hbot
  calc
    (((barr[𝕜](C) : Set E)ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) =
        Function.recessionCone (((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆)₀⁺) := by
      let sDir : E → WithBotTop 𝕜 := fun x ↦
        @supportFunction E E (WithBotTop 𝕜) WithBot.instSupSet
          (@instHasPairingWithBotTop E E 𝕜 instHasPairingOfHasLinearPairing) C x
      let sSwp : E → WithBotTop 𝕜 := fun x ↦
        @supportFunction E E (WithBotTop 𝕜) WithBot.instSupSet
          (@instHasPairingWithBotTop E E 𝕜 instHasPairingYX) C x
      have hsupp_eq : sDir = sSwp := by
        funext x
        simp only [sDir, sSwp, supportFunction_def]
        refine iSup_congr ?_
        intro y
        have hpair : (⟪x, (y : E)⟫ₚ : 𝕜) = ⟪(y : E), x⟫ₚ := by
          simpa using (HasPairingSwap.pairing_swap (x := x) (y := (y : E)))
        exact congrArg (fun t : 𝕜 ↦ (t : WithBotTop 𝕜)) hpair
      have hdom_eq : dom(sDir) = dom(sSwp) := by
        simpa [hsupp_eq]
      have hbarrier : (barr[𝕜](C) : Set E) = dom(sSwp) := by
        simpa [sSwp] using
          (barrierCone_eq_effectiveDomain_supportFunction (R := 𝕜) (X := E) (Y := E) C)
      have hmain :
          (((dom(sDir))ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) =
            Function.recessionCone (((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆)₀⁺) := by
        simpa [sDir] using
          polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate
            (δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜) (Function.isConvex_supportFunction C)
            hsupport_proper
      calc
        (((barr[𝕜](C) : Set E)ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) =
            (((dom(sSwp))ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) := by
          simpa [hbarrier]
        _ = (((dom(sDir))ᵒ[𝕜] : PointedCone 𝕜 E) : Set E) := by simpa [hdom_eq]
        _ = Function.recessionCone (((δᵛ[WithBotTop 𝕜](· | C) : E → WithBotTop 𝕜)⋆)₀⁺) := hmain
    _ = Function.recessionCone (((δ[𝕜](· | C) : E → WithBotTop 𝕜))₀⁺) := by
      rw [convexConjugate_supportFunction_eq_indicatorFunction C hC_convex hC_closed]
    _ = 0⁺[𝕜] C := by
      simpa using
        (functionRecessionCone_indicatorFunction_eq_recessionCone
          (α := 𝕜) (C := C) hC_convex)

end

/-! ### Corollary_14_2_2 (from Chap03) -/
section

open Bornology
open scoped Rockafellar

variable {E Y : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable [TopologicalSpace Y] [AddCommMonoid Y] [Module ℝ Y]
variable [HasLinearPairing E Y ℝ]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 14.2.2 characterizes when every real sublevel set
  `{x | f x ≤ α}` of a closed proper convex function is bounded.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.IsClosedProperConvex`, `Function.recessionFunction`,
  `Function.recessionCone`, `convexConjugate`, the interior operator on subsets of `Y`, and
  mathlib's boundedness predicate `Bornology.IsBounded`, together with the chapter owner
  `dom(f⋆)` for `dom f*`.
- `bridge/view`: this file is stated on the pairing-level dual ambient owner `Y`, so the dual
  effective-domain side is `dom(f⋆)` without fixing the concrete model `StrongDual ℝ E`.

Domain-style sampling used here:
- `Function.IsClosedProperConvex`;
- `Function.IsConvex.isBounded_sublevel_of_nonempty_bounded_sublevel`;
- `recessionCone_sublevelSet_eq_functionRecessionCone`;
- `Convex.isBounded_iff_recessionCone_eq_singleton_zero`;
- `mem_interior_iff_forall_ne_zero_dual_lt_supportFunction`;
- the Chapter 13 effective-domain/support-function recession bridge for Fenchel conjugates.

Primitive data vs derived API:
- primitive input: the function `f : E → WithTopBot ℝ`;
- owner hypothesis: `f.IsClosedProperConvex`;
- owner invariant: `Function.recessionCone (Function.recessionFunction f)`;
- derived API: boundedness of every real sublevel set and the interior criterion at the origin for
  `dom(f⋆)` on the dual ambient owner `Y`.

Layer target: `source-facing`, stated directly in the bounded-sublevel-set language of the source
and the canonical dual effective-domain owner for `dom f*`.

Ambient refinement: the source-facing owner statement only needs the finite-dimensional real
normed-space layer on the primal side and a pairing-level real topological module ambient `Y`, so
the surface avoids fixing a concrete dual realization (for example `StrongDual ℝ E`) or an
`InnerProductSpace` identification.

Scalar/codomain/topology checks for this item:
- codomain: the statement is kept at `WithTopBot ℝ`, matching the reused Chapter 8/13 recession
  and support-function bridge owners;
- scalar: this corollary remains genuinely `ℝ`-scalar in this dependency closure, since the
  boundedness/recession owner route it uses is currently developed on the real layer;
- topology: ambient `interior` is the source-facing primary clause and is the direct output owner
  of this Chapter 14 criterion, while the intrinsic/relative surface is exposed immediately below
  as a canonical consequence via `interior_subset_intrinsicInterior`.
-/

-- Proof sketch: choose one finite point of `f` from properness, hence one canonical nonempty real
-- sublevel set `S α0`. Corollary 8.7.1 packages the source fact that boundedness of this one
-- nonempty sublevel set is equivalent to boundedness of every real sublevel set, so it remains to
-- compare `IsBounded (S α0)` with `0 ∈ interior dom(f⋆)`. Theorem 8.4 makes boundedness of
-- `S α0` equivalent to triviality of its recession cone, and Theorem 8.7 identifies that cone
-- with the common owner `Function.recessionCone (f0⁺)`. This triviality is equivalent to strict
-- positivity of `f0⁺` on every nonzero direction, and the Chapter 13 interior/support and
-- effective-domain/recession bridges identify that positivity criterion with
-- `0 ∈ interior dom(f⋆)` on the paired dual side.
/- Corollary 14.2.2: for a closed proper convex function `f` on a finite-dimensional real normed
space with a real pairing into a dual topological module `Y`, every real sublevel set
`{x | f x ≤ α}` is bounded if and only if the dual-side origin lies in the interior of the
effective domain `dom(f⋆)`. -/
namespace Function.IsClosedProperConvex

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-- Primitive owner form for Corollary 14.2.2: boundedness of one nonempty real sublevel set is
equivalent to interior membership of `0` in `dom(f⋆)`. -/
theorem exists_nonempty_bounded_sublevelSet_iff_zero_mem_interior_effectiveDomain_convexConjugate
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (∃ α : ℝ, ({x : E | f x ≤ α}).Nonempty ∧ IsBounded {x : E | f x ≤ α}) ↔
      0 ∈ interior dom(f⋆) := by
  sorry

theorem all_sublevelSets_bounded_iff_zero_mem_interior_effectiveDomain_convexConjugate
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (∀ α : ℝ, IsBounded {x : E | f x ≤ α}) ↔
      0 ∈ interior dom(f⋆) := by
  constructor
  · intro hall
    rcases (Function.isProper_iff.mp hf.proper) with ⟨⟨x0, hx0_dom⟩, hnot_bot⟩
    lift (f x0) to ℝ using ⟨hx0_dom.ne, hnot_bot x0⟩ with α0 hα0
    have hnonempty : ({x : E | f x ≤ α0}).Nonempty := by
      refine ⟨x0, ?_⟩
      change f x0 ≤ (α0 : WithTopBot ℝ)
      simpa [hα0]
    have hexists :
        ∃ α : ℝ, ({x : E | f x ≤ α}).Nonempty ∧ IsBounded {x : E | f x ≤ α} :=
      ⟨α0, hnonempty, hall α0⟩
    exact
      (hf.exists_nonempty_bounded_sublevelSet_iff_zero_mem_interior_effectiveDomain_convexConjugate).1
        hexists
  · intro h0
    rcases
        (hf.exists_nonempty_bounded_sublevelSet_iff_zero_mem_interior_effectiveDomain_convexConjugate).2
          h0 with
      ⟨α0, hnonempty, hbounded⟩
    exact
      hf.convex.isBounded_sublevel_of_nonempty_bounded_sublevel
        hf.closed α0 hnonempty hbounded

/-- Intrinsic/relative consequence of Corollary 14.2.2: boundedness of every real sublevel set
forces `0` to lie in `ri(dom(f⋆))`. -/
theorem all_sublevelSets_bounded_imp_zero_mem_riDom_convexConjugate
    {f : E → WithTopBot ℝ} (hf : IsClosedProperConvex[ℝ] f) :
    (∀ α : ℝ, IsBounded {x : E | f x ≤ α}) →
      0 ∈ riDom(f⋆) := by
  intro hbounded
  exact interior_subset_intrinsicInterior
    ((hf.all_sublevelSets_bounded_iff_zero_mem_interior_effectiveDomain_convexConjugate).1
      hbounded)

end Function.IsClosedProperConvex

end

/-! ### Theorem_14_2 (from Chap03) -/
noncomputable section

universe u

section

open scoped Rockafellar PolarCone

variable {𝕜 : Type*} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type u} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

private theorem mem_polarCone_cone_iff_supportFunction_le_zero
    (C : Set X) {xStar : Y} :
    xStar ∈ (cone[𝕜] C)ᵒ[𝕜] ↔
      δᵛ[WithTopBot 𝕜](xStar | C) ≤ 0 := by
  calc
    xStar ∈ (cone[𝕜] C)ᵒ[𝕜] ↔ xStar ∈ Cᵒ[𝕜] := by
      simp
    _ ↔ C ⊆ closedHalfSpaceLE xStar (0 : 𝕜) := by
      constructor
      · intro hx x hxC
        exact (mem_polarCone_iff_pairing (K := C)).1 hx x hxC
      · intro hx
        exact (mem_polarCone_iff_pairing (K := C)).2 hx
    _ ↔ δᵛ[WithTopBot 𝕜](xStar | C) ≤ 0 := by
      simpa using subset_closedHalfSpaceLE_iff_supportFunction_le_withTopBot C xStar (0 : 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 14.2 identifies the polar of the convex cone generated by `dom f` with
  the recession cone of `f*`, and in the closed case identifies the polar of the recession cone of
  `f` with the closure of the convex cone generated by `dom f*`.
- `core/canonical`: the owner constructions already present in the project are `polarCone`,
  `PointedCone.hull` (notation `cone[𝕜]`), `PointedCone.closure`, `Function.recessionCone`,
  `recessionFunction`, `convexConjugate`,
  `Function.IsConvex`, `Function.IsProper`, and `Function.IsClosedProperConvex`.
- `bridge/view`: Rockafellar's `dom f` and `dom f*` are represented by the established chapter
  finite-value sets `dom(f)` and `dom(f⋆)`; the generated convex cone is rendered by
  `cone[𝕜]`, and the closed generated cone in the dual clause by the bundled owner
  `PointedCone.closure`.

Domain-style sampling used here:
- `polarCone` from `Text_14_0_1`;
- `cone[𝕜]` and `PointedCone.closure`;
- `Function.recessionCone` from `Definiton_8_5_0`;
- `supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate` and
  `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from `Theorem_13_3`.

Primitive data vs derived API:
- primitive input: an extended-codomain function `f : X → WithTopBot 𝕜` for clause (1), and an
  extended-real-valued function `f : E → WithTopBot ℝ` for clause (2);
- owner hypotheses: convexity and properness for the first clause, and the chapter owner predicate
  `f.IsClosedProperConvex` for the dual closed-case clause;
- derived API: the two polar/generated-cone equalities, with clause (2) on bundled
  `PointedCone` owners.

Layer target: `source-facing`, stated directly with the chapter owners for polars, generated
cones, and function recession cones rather than via a surrogate support-function package.

Ambient refinement: the upstream owner theorem `Theorem_13_3` already has a swap-compatible
pairing layer for clause (1), so this item keeps clause (1) at that intrinsic pairing owner level.
Clause (2) uses the real pairing-owner bipolar theorem `polarCone_polarCone_eq_closure`.
-/

section

variable (f : X → WithTopBot 𝕜)

-- Proof sketch: by Theorem 13.3, the support function of `dom(f)` is the recession function of
-- `f⋆`. Taking the zero sublevel set of that equality gives
-- `Function.recessionCone ((f⋆)₀⁺)`. For a generated cone, the
-- defining inequalities for `polarCone` are unchanged when one passes from a set to its generated
-- cone hull, because nonnegative scalar multiples preserve the sign condition.
/-- Theorem 14.2 (1): for a proper convex function `f` on a swap-compatible pairing
`X ↔ Y` over an ordered scalar ring `𝕜`,
the polar of the convex cone generated by its effective domain `dom(f)` is the recession cone of
its Fenchel conjugate `f*`. -/
theorem polarCone_hull_effectiveDomain_eq_functionRecessionCone_convexConjugate
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper) :
    (((cone[𝕜] dom(f))ᵒ[𝕜] : Set Y) =
      Function.recessionCone ((f⋆)₀⁺)) := by
  ext xStar
  change xStar ∈ (cone[𝕜] dom(f))ᵒ[𝕜] ↔
    xStar ∈ Function.recessionCone ((f⋆)₀⁺)
  rw [mem_polarCone_cone_iff_supportFunction_le_zero, Function.mem_recessionCone_iff]
  have hpoint :=
    congrArg (fun g : Y → WithTopBot 𝕜 ↦ g xStar)
      (supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate
        (f := f) hf_convex hf_proper)
  simp [hpoint]

end

section

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ] [HasPairingSwap E E ℝ]
variable [((HasLinearPairing.pairingLinear : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)).IsContPerfPair]
local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

-- Proof sketch: Theorem 13.3 already provides the closed-case owner identity
-- `supportFunction dom(f⋆) = (f)₀⁺`. Taking its zero sublevel set yields
-- `(cone[ℝ] dom(f⋆) : Set E)ᵒ[ℝ] = Function.recessionCone ((f)₀⁺)` at the set view.
-- The pointed-cone bipolar theorem `polarCone_polarCone_eq_closure` then identifies the double
-- polar with the closure of the generated cone.
/-- Theorem 14.2 (2): if `f` is closed as well as proper convex on a finite-dimensional real
locally-convex topological module equipped with a continuous symmetric perfect pairing,
then the polar of the recession cone of `f` is the closure of the
convex cone generated by the effective domain `dom(f⋆)`, in bundled `PointedCone` owner form. -/
theorem polarCone_functionRecessionCone_eq_closure_hull_effectiveDomain_convexConjugate
    (f : E → WithTopBot ℝ)
    (hf : IsClosedProperConvex[ℝ] f) :
    ((Function.recessionCone (f₀⁺))ᵒ[ℝ] : PointedCone ℝ E) =
      (cone[ℝ] dom(f⋆)).closure := by
  sorry

end
