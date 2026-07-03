import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_7_3_1 (from Chap02) -/
section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul r x := (r : WithTopBot 𝕜) * x

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_bot_lt_coe (a : 𝕜) :
    (⊥ : WithTopBot 𝕜) < (a : WithTopBot 𝕜) := by
  change (((⊥ : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
    (((a : WithBot 𝕜) : WithTop (WithBot 𝕜))))
  exact WithTop.coe_lt_coe.mpr (WithBot.bot_lt_coe a)

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_coe_lt_top (a : 𝕜) :
    (a : WithTopBot 𝕜) < (⊤ : WithTopBot 𝕜) := by
  change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) < (⊤ : WithTop (WithBot 𝕜)))
  exact WithTop.coe_lt_top _

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_coe_lt_coe_iff {a b : 𝕜} :
    (a : WithTopBot 𝕜) < (b : WithTopBot 𝕜) ↔ a < b := by
  constructor
  · intro h
    change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
      (((b : WithBot 𝕜) : WithTop (WithBot 𝕜)))) at h
    exact WithBot.coe_lt_coe.mp (WithTop.coe_lt_coe.mp h)
  · intro h
    change (((a : WithBot 𝕜) : WithTop (WithBot 𝕜)) <
      (((b : WithBot 𝕜) : WithTop (WithBot 𝕜))))
    exact WithTop.coe_lt_coe.mpr (WithBot.coe_lt_coe.mpr h)

omit [NontriviallyNormedField 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜] in
private theorem withTopBot_coe_lt_coe {a b : 𝕜} (h : a < b) :
    (a : WithTopBot 𝕜) < (b : WithTopBot 𝕜) :=
  withTopBot_coe_lt_coe_iff.mpr h

omit [OrderTopology 𝕜] [CompleteSpace 𝕜] in
private theorem exists_between_coe_of_lt [DenselyOrdered 𝕜]
    {x y : WithTopBot 𝕜} (h : x < y) :
    ∃ a : 𝕜, x < (a : WithTopBot 𝕜) ∧ (a : WithTopBot 𝕜) < y := by
  cases x with
  | none =>
      have hyle : y ≤ (⊤ : WithTopBot 𝕜) := le_top
      exact (not_lt_of_ge hyle h).elim
  | some x' =>
      cases x' with
      | bot =>
          cases y with
          | none =>
              exact ⟨0, withTopBot_bot_lt_coe 0, withTopBot_coe_lt_top 0⟩
          | some y' =>
              cases y' with
              | bot =>
                  exact (lt_irrefl _ h).elim
              | coe b =>
                  obtain ⟨a, ha⟩ := exists_lt b
                  exact ⟨a, withTopBot_bot_lt_coe a, withTopBot_coe_lt_coe ha⟩
      | coe x =>
          cases y with
          | none =>
              obtain ⟨a, hxa⟩ := exists_gt x
              exact ⟨a, withTopBot_coe_lt_coe hxa, withTopBot_coe_lt_top a⟩
          | some y' =>
              cases y' with
              | bot =>
                  exact (not_lt_of_ge (bot_le : (⊥ : WithTopBot 𝕜) ≤ (x : WithTopBot 𝕜)) h).elim
              | coe y =>
                  have hxy : x < y := withTopBot_coe_lt_coe_iff.mp h
                  obtain ⟨a, hxa, hay⟩ := exists_between hxy
                  exact ⟨a, withTopBot_coe_lt_coe hxa, withTopBot_coe_lt_coe hay⟩

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 7.3.1 says that if a convex function on a finite-dimensional
  ordered-normed-field ambient has a strict sublevel point below an extended level `α`, then that
  strict sublevel
  set already meets the relative
  interior of `dom f`.
- `core/canonical`: the owner abstraction is `ConvexOn 𝕜 (Set.univ : Set E) f`, together with the
  chapter effective-domain owner `dom(·)` and mathlib's
  `intrinsicInterior 𝕜`.
- `bridge/view`: the proof route factors through the canonical epigraph theorem `Lemma_7_3` and
  the convex-set owner theorem
  `Convex.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty`; no parallel local
  finiteness-set wrapper is needed because `dom(f)` already owns that notion upstream.
- Domain-style sampling used here: the owner predicate `ConvexOn 𝕜 (Set.univ : Set E) f`, the nearby
  epigraph-relative-interior bridge
  `Function.IsConvex.mem_ri_epi_iff`
  from `Lemma_7_3`, and the owner-style relative-interior open-set bridge
  `Convex.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty` from
  `Corollary_6_3_2`.
- Primitive data vs derived API: the primitive data are the convex function `f`, the level
  `α : WithTopBot 𝕜`, and a strict sublevel witness. The conclusion is the derived existence
  of a strict sublevel point on the relative interior of the effective domain.
- Layer target: this item remains `source-facing`, but its convexity input is now expressed through
  the chapter owner predicate, and its domain conclusion through the owner `dom(f)` instead of a
  duplicate raw set expression.
- Ambient-space refinement: the textbook `R^n` presentation is only a coordinate model for this
  argument, so the public theorem is stated at the owner level of finite-dimensional ordered
  normed-field spaces.
-/

/-- Corollary 7.3.1, existential owner form: if a convex function on a finite-dimensional ordered
normed-field ambient has a strict sublevel point below `α`, then one can choose such a point in
`riDom[𝕜](f)`. Specializing to `𝕜 = ℝ` recovers the textbook `R^n` statement. -/
-- Proof sketch: apply Corollary 6.3.2 to the open half-space
-- `{p : E × 𝕜 | p.2 < β}` (with `β : 𝕜`, `β < α`) and the epigraph `epi f`.
-- A relative-interior point `(x, μ)` of the epigraph with `μ < β` projects to
-- `x ∈ riDom[𝕜](f)`, and `f x ≤ μ < α` gives the desired strict inequality.
theorem exists_lt_on_riDom_of_exists_lt
    (hf : ConvexOn 𝕜 (Set.univ : Set E) f) (α : WithTopBot 𝕜)
    (hα : ∃ x : E, f x < α) :
    ∃ x, x ∈ riDom[𝕜](f) ∧ f x < α := by
  have hEpi : Convex 𝕜 (epi f) := by
    simpa using hf.convex_finiteHeight_epigraph
  rcases hα with ⟨x, hxlt⟩
  rcases exists_between_coe_of_lt hxlt with ⟨β, hxβ, hβα⟩
  rcases exists_between_coe_of_lt hxβ with ⟨γ, hxγ, hγβ⟩
  let U : Set (E × 𝕜) := {p | p.2 < β}
  have hU : IsOpen U := isOpen_lt continuous_snd continuous_const
  have hclosure :
      (intrinsicClosure 𝕜 (epi f) ∩ U).Nonempty := by
    refine ⟨(x, γ), ?_⟩
    refine ⟨subset_intrinsicClosure ?_, ?_⟩
    · simpa [epi] using hxγ.le
    · simpa [U] using hγβ
  obtain ⟨⟨y, μ⟩, hyi, hyμlt⟩ :=
    Convex.inter_ri_nonempty_of_isOpen_of_inter_intrinsicClosure_nonempty
      hEpi hU hclosure
  have hyμβ : (μ : WithTopBot 𝕜) < β := by
    simpa [U] using hyμlt
  have hyμα : (μ : WithTopBot 𝕜) < α := lt_trans hyμβ hβα
  rcases (Function.IsConvex.mem_ri_epi_iff (f := f) hf).1 hyi with ⟨hy_dom, hfyμ⟩
  exact ⟨y, hy_dom, lt_trans hfyμ hyμα⟩

/-- Corollary 7.3.1, set-nonempty bridge form:
if the strict `α`-sublevel set is nonempty, it meets `riDom[𝕜](f)`. -/
theorem riDom_inter_nonempty_of_sublevel_nonempty
    (hf : ConvexOn 𝕜 (Set.univ : Set E) f) (α : WithTopBot 𝕜)
    (hα : ({x : E | f x < α} : Set E).Nonempty) :
    (riDom[𝕜](f) ∩ {x : E | f x < α}).Nonempty := by
  rcases hα with ⟨x, hxlt⟩
  rcases Function.IsConvex.exists_lt_on_riDom_of_exists_lt (f := f) hf α ⟨x, hxlt⟩ with
    ⟨y, hyri, hylt⟩
  exact ⟨y, hyri, hylt⟩

end Function.IsConvex

end

/-! ### Corollary_7_3_2 (from Chap02) -/
section

open scoped Rockafellar

universe u

variable
    {𝕜 : Type*} {E : Type u}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul r x := (r : WithTopBot 𝕜) * x

namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.3.2 says that if a convex function has a point of the closure of a
  convex set `C` lying strictly below a level `α`, and the relative interior of `C` lies in
  the effective domain of the function, then the same strict sublevel set already meets
  `ri[𝕜](C)`.
- `core/canonical`: the owner abstraction is `ConvexOn 𝕜 (Set.univ : Set E) f`,
  mathlib's `Convex 𝕜 C`, the closure operator `closure`, the relative interior operator
  `intrinsicInterior 𝕜`, and the chapter owner notation `riDom[𝕜](·)` for relative interiors of
  effective domains.
- `bridge/view`: Rockafellar's `ri C` is represented by the local source-facing notation
  `ri[𝕜](C) = intrinsicInterior 𝕜 C`, while the effective domain is expressed through the chapter
  owner `dom(f)`.
- Domain-style sampling used here: the owner predicate
  `ConvexOn 𝕜 (Set.univ : Set E) f`, the owner closure/relative-interior identity
  `Convex.intrinsicInterior_closure_eq_intrinsicInterior`, and the nearby strict-sublevel
  relative-interior result
  `Function.IsConvex.riDom_inter_nonempty_of_sublevel_nonempty` from
  Corollary 7.3.1.
- Primitive data vs derived API: the primitive inputs are the convex function `f`, the convex set
  `C`, the domain inclusion on `ri[𝕜](C)`, the level `α : WithTopBot 𝕜`, and a strict sublevel
  witness on `closure C`; the conclusion is the derived existence of a strict sublevel point on
  `ri[𝕜](C)`.
- Layer target: this item stays `source-facing`, and is expressed
  directly in the canonical convex-function/relative-interior language.
- Ambient-space refinement: the proof is coordinate-free and only uses the finite-dimensional
  ordered normed-field owner layer already fixed in Chapter 7.
-/

-- Proof sketch: apply Corollary 7.3.1 to the auxiliary function obtained from the restriction of
-- `f` to `closure C` by the canonical `Set.piecewise` extension with value `⊤` off `closure C`.
-- Its convexity is read through the restricted epigraph owner `epi[closure C] f`, and its
-- effective domain has relative interior `ri[𝕜](C)`, using
-- `Convex.intrinsicInterior_closure_eq_intrinsicInterior hC` together with the hypothesis
-- `ri[𝕜](C) ⊆ dom(f)`. Translate the resulting strict-sublevel point on `riDom[𝕜](g)` back to the
-- relative interior of that effective domain back to a point of `ri[𝕜](C)` for the original `f`.
/-- Corollary 7.3.2, intrinsic-closure existential owner form: if a strict `α`-sublevel witness
exists on `intrinsicClosure 𝕜 C`, and if `ri[𝕜](C)` lies in `dom(f)`, then a strict
`α`-sublevel witness exists on `ri[𝕜](C)`. -/
theorem exists_lt_on_ri_of_exists_lt_on_intrinsicClosure
    {C : Set E} (hf : ConvexOn 𝕜 (closure C) f) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ intrinsicClosure 𝕜 C, f x < α) :
    ∃ x ∈ ri[𝕜](C), f x < α := by
  classical
  let g : E → WithTopBot 𝕜 := (closure C).piecewise f ⊤
  have hEpi_g : epi g = epi[closure C] f := by
    ext p
    rcases p with ⟨x, μ⟩
    by_cases hx : x ∈ closure C
    · simp [g, epi, hx]
    · constructor
      · intro hp
        exfalso
        have htop :
            ¬ ((⊤ : WithTopBot 𝕜) ≤ (μ : WithTopBot 𝕜)) := by
          have hμtop : (μ : WithTopBot 𝕜) < (⊤ : WithTopBot 𝕜) := by
            change (((μ : WithBot 𝕜) : WithTop (WithBot 𝕜)) < (⊤ : WithTop (WithBot 𝕜)))
            exact WithTop.coe_lt_top _
          exact not_le_of_gt hμtop
        have hgx : g x = ⊤ := by
          simp [g, hx]
        rw [mem_epi_iff] at hp
        rw [hgx] at hp
        exact htop hp
      · intro hp
        exact False.elim (hx hp.1)
  have hg_epi : Convex 𝕜 (epi g) := by
    rw [hEpi_g]
    simpa using hf.convex_finiteHeight_epigraph
  have hg : ConvexOn 𝕜 (Set.univ : Set E) g := by
    exact convexOn_of_convex_finiteHeight_epigraph
      (s := (Set.univ : Set E)) (f := g) (by simpa [epi_univ] using hg_epi) convex_univ
  obtain ⟨x, hxC, hxlt⟩ := hα
  have hxC' : x ∈ closure C := by
    simpa [intrinsicClosure_eq_closure 𝕜 C] using hxC
  have hglt : g x < α := by
    simpa [g, hxC'] using hxlt
  obtain ⟨y, hy, hylt⟩ :=
    Function.IsConvex.exists_lt_on_riDom_of_exists_lt (f := g) hg α ⟨x, hglt⟩
  have hdom_eq : dom(g) = closure C ∩ dom(f) := by
    ext z
    by_cases hzC : z ∈ closure C
    · simp [g, hzC, mem_effectiveDomain]
    · constructor
      · intro hz
        exfalso
        change g z < ⊤ at hz
        have hz_top : g z = ⊤ := by
          simp [g, hzC]
        exact ((lt_irrefl (⊤ : WithTopBot 𝕜)) (hz_top ▸ hz)).elim
      · intro hz
        exact False.elim (hzC hz.1)
  have hg_convexDom : Convex 𝕜 dom(g) := by
    rw [effectiveDomain_eq_image_fst_epi g]
    simpa using Convex.linear_image (hs := hg.convex_finiteHeight_epigraph)
      (f := LinearMap.fst 𝕜 E 𝕜)
  have hri_eq : riDom[𝕜](g) = ri[𝕜](C) := by
    have hclosure : closure dom(g) = closure C := by
      apply subset_antisymm
      · simpa [hdom_eq, closure_closure] using
          closure_mono (Set.inter_subset_left : closure C ∩ dom(f) ⊆ closure C)
      · calc
          closure C = closure (ri[𝕜](C)) := by
            simpa using hC.closure_intrinsicInterior_eq_closure.symm
          _ ⊆ closure dom(g) := by
            apply closure_mono
            intro z hz
            rw [hdom_eq]
            exact ⟨subset_closure (intrinsicInterior_subset hz), hdom hz⟩
    change intrinsicInterior 𝕜 dom(g) = ri[𝕜](C)
    calc
      intrinsicInterior 𝕜 dom(g) = intrinsicInterior 𝕜 (closure dom(g)) := by
        simpa using hg_convexDom.intrinsicInterior_closure_eq_intrinsicInterior.symm
      _ = intrinsicInterior 𝕜 (closure C) := by simp [hclosure]
      _ = ri[𝕜](C) := hC.intrinsicInterior_closure_eq_intrinsicInterior
  rw [hri_eq] at hy
  have hyC : y ∈ closure C := subset_closure (intrinsicInterior_subset hy)
  exact ⟨y, hy, by simpa [g, hyC] using hylt⟩

/-- Corollary 7.3.2, intrinsic-closure nonempty-intersection bridge. -/
theorem ri_inter_nonempty_of_intrinsicClosure_inter_openSublevel_nonempty
    {C : Set E} (hf : ConvexOn 𝕜 (closure C) f) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ intrinsicClosure 𝕜 C, f x < α) :
    (ri[𝕜](C) ∩ {x : E | f x < α}).Nonempty := by
  rcases hα with ⟨x, hxC, hxlt⟩
  rcases
      exists_lt_on_ri_of_exists_lt_on_intrinsicClosure
        hf hC α hdom ⟨x, hxC, hxlt⟩ with
    ⟨y, hyri, hylt⟩
  exact ⟨y, hyri, hylt⟩

/-- Corollary 7.3.2, ambient-closure existential bridge. -/
theorem exists_lt_on_ri_of_exists_lt_on_closure
    {C : Set E} (hf : ConvexOn 𝕜 (closure C) f) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ closure C, f x < α) :
    ∃ x ∈ ri[𝕜](C), f x < α := by
  rcases hα with ⟨x, hx, hxlt⟩
  exact
    exists_lt_on_ri_of_exists_lt_on_intrinsicClosure hf hC α hdom
      ⟨x, by simpa [intrinsicClosure_eq_closure 𝕜 C] using hx, hxlt⟩

/-- Corollary 7.3.2, ambient-closure bridge for strict-open-sublevel intersections. -/
theorem ri_inter_nonempty_of_closure_inter_openSublevel_nonempty
    {C : Set E} (hf : ConvexOn 𝕜 (closure C) f) (hC : Convex 𝕜 C)
    (α : WithTopBot 𝕜) (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ∃ x ∈ closure C, f x < α) :
    (ri[𝕜](C) ∩ {x : E | f x < α}).Nonempty := by
  rcases hα with ⟨x, hx, hxlt⟩
  rcases exists_lt_on_ri_of_exists_lt_on_closure hf hC α hdom ⟨x, hx, hxlt⟩ with
    ⟨y, hyri, hylt⟩
  exact ⟨y, hyri, hylt⟩

end Function.IsConvex

end

/-! ### Corollary_7_3_3 (from Chap02) -/
section

open scoped Rockafellar

universe u

variable
    {𝕜 : Type*} {E : Type u}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.3.3 says that a lower bound for a convex function on `ri[𝕜](C)`
  extends to `closure C`, provided the relative interior of `C` lies in the effective domain of
  the function.
- `core/canonical`: the owner abstraction already fixed upstream is `f.IsConvex` from
  `Theorem_4_2`, together with the canonical set-theoretic notions `Convex 𝕜`,
  `intrinsicInterior 𝕜 C`, and `closure`; the chapter source-facing notation `ri[𝕜](C)` is the
  canonical surface for that relative interior in this section.
- `bridge/view`: the effective domain is expressed by the chapter owner `dom(f)`, and the lower
  bound `f(x) ≥ α` by `α ≤ f x` at the same extended-codomain layer as `f`.

Domain-style sampling used here:
- the chapter owner predicate `f.IsConvex` from `Theorem_4_2`;
- mathlib's owner predicate `Convex 𝕜 C` for convex subsets;
- mathlib's convex relative-interior API `Convex.intrinsicInterior` and
  `Convex.closure_intrinsicInterior_eq_closure`;
- mathlib's closure operator `closure`;
- the preceding intrinsic-closure-to-relative-interior bridge
  `ri_inter_nonempty_of_intrinsicClosure_inter_openSublevel_nonempty` from
  `Corollary_7_3_2`.
- Primitive data vs derived API: the primitive inputs are the convex function `f`, the convex set
  `C`, the level `α`, the owner convexity hypothesis `hf : f.IsConvex`, the effective-domain
  inclusion on `ri[𝕜](C)`, and the lower-bound hypothesis on `ri[𝕜](C)`; the lower bound on
  `closure C` is the source-facing conclusion.
- Layer target: this item remains `source-facing`, but its corollaries are attached directly to
  the upstream owner namespace `Function.IsConvex` rather than kept as parallel global wrappers.
- Ambient-space refinement: the proof is coordinate-free and uses only the Chapter 7 owner layer
  on finite-dimensional ordered normed-field spaces.
-/

-- Proof sketch: argue by contradiction and first choose a scalar level `β : 𝕜` with
-- `f x < β ≤ α`. If a point of `intrinsicClosure 𝕜 C` lies below that scalar level, Corollary
-- 7.3.2 gives a strict-sublevel point in `ri[𝕜](C)`; this contradicts the lower-bound hypothesis
-- there.
namespace Function.IsConvex

variable {f : E → WithTopBot 𝕜}

/-- Corollary 7.3.3, intrinsic-closure pointwise owner form: if a convex function on a
finite-dimensional ordered normed-field space is bounded below by the level `α : WithTopBot 𝕜` on
`ri[𝕜](C)`, and if `ri[𝕜](C)` lies in the effective domain `dom(f)`, then every point of
`intrinsicClosure 𝕜 C` also satisfies the same lower bound. -/
theorem lower_bound_of_mem_intrinsicClosure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α)
    {x : E} (hx : x ∈ intrinsicClosure 𝕜 C) :
    α ≤ f x := by
  by_contra hxα
  have hxα' : ¬ α ≤ f x := by
    intro hle
    exact hxα hle
  obtain ⟨β, hβx, hβα⟩ : ∃ β : 𝕜, f x < (β : WithTopBot 𝕜) ∧ (β : WithTopBot 𝕜) ≤ α := by
    cases α using WithBotTop.rec with
    | bot =>
        exact False.elim (hxα' bot_le)
    | coe a =>
        exact ⟨a, lt_of_not_ge hxα', le_rfl⟩
    | top =>
        have hfx_top : f x < (⊤ : WithTopBot 𝕜) := lt_of_not_ge hxα'
        by_cases hfx_bot : f x = ⊥
        · exact ⟨0, by simp [hfx_bot], le_top⟩
        · have hfx_ne_top : f x ≠ ⊤ := (lt_top_iff_ne_top.mp hfx_top)
          lift f x to 𝕜 using ⟨hfx_ne_top, hfx_bot⟩ with γ hγ
          refine ⟨γ + 1, ?_, le_top⟩
          simpa [hγ] using (WithBotTop.coe_lt_coe.mpr (lt_add_of_pos_right γ zero_lt_one))
  obtain ⟨y, hyri, hylt⟩ :=
    ri_inter_nonempty_of_intrinsicClosure_inter_openSublevel_nonempty
      (hf := hf.mono (Set.subset_univ (closure C)))
      (hC := hC) (α := β) (hdom := hdom) (hα := ⟨x, hx, hβx⟩)
  have hy_ge : α ≤ f y := by
    simpa [Set.mem_Ici] using hα hyri
  exact not_lt_of_ge (hβα.trans hy_ge) hylt

/-- Corollary 7.3.3, intrinsic-closure set-theoretic bridge. -/
theorem lower_bound_on_intrinsicClosure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α) :
    intrinsicClosure 𝕜 C ⊆ f ⁻¹' Set.Ici α := by
  intro x hx
  exact lower_bound_of_mem_intrinsicClosure_of_lower_bound_on_ri hf hC α hdom hα hx

/-- Corollary 7.3.3, ambient-closure pointwise bridge: if a convex function is bounded below by
`α` on `ri[𝕜](C)` and `ri[𝕜](C) ⊆ dom(f)`, then every point of `closure C` satisfies the same lower
bound. -/
theorem lower_bound_of_mem_closure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α)
    {x : E} (hx : x ∈ closure C) :
    α ≤ f x :=
  lower_bound_of_mem_intrinsicClosure_of_lower_bound_on_ri hf hC α hdom hα <| by
    simpa [intrinsicClosure_eq_closure 𝕜 C] using hx

/-- Corollary 7.3.3, ambient-closure set-theoretic bridge. -/
theorem lower_bound_on_closure_of_lower_bound_on_ri
    (hf : f.IsConvex 𝕜) {C : Set E} (hC : Convex 𝕜 C) (α : WithTopBot 𝕜)
    (hdom : ri[𝕜](C) ⊆ dom(f))
    (hα : ri[𝕜](C) ⊆ f ⁻¹' Set.Ici α) :
    closure C ⊆ f ⁻¹' Set.Ici α := by
  intro x hx
  exact lower_bound_of_mem_closure_of_lower_bound_on_ri hf hC α hdom hα hx

end Function.IsConvex

end

/-! ### Lemma_7_3 (from Chap02) -/
section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
    [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

local instance : SMul 𝕜 (WithTopBot 𝕜) where
  smul r x := (r : WithTopBot 𝕜) * x

/-
Source/core/bridge triage:
- `source-facing`: Lemma 7.3 identifies the relative interior of the epigraph of a convex function
  with the strict vertical region above the function over the relative interior of its effective
  domain.
- `core/canonical`: the owner notion is `ConvexOn 𝕜 (Set.univ : Set E) f`, together with the
  effective-domain owner `dom(·)`, the chapter epigraph owner `epi`, mathlib's
  `intrinsicInterior 𝕜`, and the product-fiber owner theorem
  `Convex.mem_ri_iff_mem_ri_base_and_fiber`.
  `ri[𝕜](epi f)` and `riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f)`. This theorem is the
  epigraph specialization of the owner product-fiber statement from Theorem 6.8, with the base
  projection identified by `effectiveDomain_eq_image_fst_epi`. The source clause `μ < ∞` becomes
  automatic because the epigraph height coordinate is already a scalar `μ : 𝕜`.
- Domain-style sampling used here: the chapter owner `ConvexOn 𝕜 (Set.univ : Set E) f`,
  `epi` from Definition 4.1, and `dom(·)` from Definition 4.4, together with the projection
  bridge `effectiveDomain_eq_image_fst_epi`, the product relative-interior theorem
  `Convex.mem_ri_iff_mem_ri_base_and_fiber` from Theorem 6.8, and
  the upper-ray pullback theorem `ri_preimage_coe_Ici` from Text 6.12.
- Primitive data vs derived API: the primitive datum is only the function `f`; the epigraph and
  effective domain are canonical derived owner expressions and are kept unbundled.
- Layer target: this item is a source-facing theorem stated directly in the canonical
  `intrinsicInterior` language.
- Ambient-space refinement: the textbook `R^n` statement is only a coordinate model, so the public
  theorem is stated on the scalar-generic finite-dimensional normed-space owner layer and
  specializes to the real case.
-/

-- Proof sketch: specialize
-- `Convex.mem_ri_iff_mem_ri_base_and_fiber` to the convex
-- epigraph `epi f`, using `hf` to supply convexity. The projection of that epigraph to the base
-- is exactly `dom(f)`. For each fixed base point `x`, the fiber is the upper ray
-- `{μ : 𝕜 | f x ≤ μ}`, whose relative interior is the strict ray `{μ : 𝕜 | f x < μ}` whenever
-- `f x` is finite.
/- Lemma 7.3: for a convex function `f : E → WithTopBot 𝕜`, the relative interior of its epigraph
consists exactly of pairs `(x, μ)` such that `x` lies in `riDom[𝕜](f)` and `f x < μ`. Specializing
to `𝕜 = ℝ` recovers the textbook `R^n` statement with codomain `EReal = WithTopBot ℝ`. -/
namespace Function.IsConvexOn

@[simp] theorem mem_ri_epi_restrict_iff
    {f : E → WithTopBot 𝕜} {s : Set E} (hf : ConvexOn 𝕜 s f) {p : E × 𝕜} :
    p ∈ ri[𝕜](epi[s] f) ↔
      p.1 ∈ ri[𝕜](s ∩ dom(f)) ∧ f p.1 < p.2 := by
  rcases p with ⟨x, μ⟩
  have hEpi : Convex 𝕜 (epi[s] f) := by
    simpa using hf.convex_finiteHeight_epigraph
  have hmem :
      (x, μ) ∈ ri[𝕜](epi[s] f) ↔
        x ∈ ri[𝕜](Prod.fst '' epi[s] f) ∧
          μ ∈ ri[𝕜](Prod.mk x ⁻¹' epi[s] f) :=
    hEpi.mem_ri_iff_mem_ri_base_and_fiber
  rw [← effectiveDomain_inter_eq_image_fst_epi (f := f) (S := s)] at hmem
  have hUpper :
      μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) ↔ f x < μ := by
    have hUpper' :
        μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) ↔
          μ ∈ {r : 𝕜 | f x < r} := by
      simpa using
        congrArg (fun t : Set 𝕜 => μ ∈ t) (ri_preimage_coe_Ici (a := f x))
    simpa using hUpper'
  constructor
  · intro hxμ
    rcases hmem.mp hxμ with ⟨hx, hμ⟩
    have hxs : x ∈ s := (intrinsicInterior_subset hx).1
    have hμ' : μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) := by
      simpa [epi, hxs] using hμ
    exact ⟨hx, hUpper.mp hμ'⟩
  · rintro ⟨hx, hlt⟩
    have hxs : x ∈ s := (intrinsicInterior_subset hx).1
    have hμ' : μ ∈ ri[𝕜]({r : 𝕜 | f x ≤ r}) := hUpper.mpr hlt
    have hμ : μ ∈ ri[𝕜](Prod.mk x ⁻¹' epi[s] f) := by
      simpa [epi, hxs] using hμ'
    exact hmem.mpr ⟨hx, hμ⟩

theorem ri_epi_restrict_eq
    {f : E → WithTopBot 𝕜} {s : Set E} (hf : ConvexOn 𝕜 s f) :
    ri[𝕜](epi[s] f) = {p : E × 𝕜 | p.1 ∈ ri[𝕜](s ∩ dom(f)) ∧ f p.1 < p.2} := by
  ext p
  simpa using (Function.IsConvexOn.mem_ri_epi_restrict_iff (f := f) (s := s) hf (p := p))

end Function.IsConvexOn

namespace Function.IsConvex

@[simp] theorem mem_ri_epi_iff
    {f : E → WithTopBot 𝕜} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) {p : E × 𝕜} :
    p ∈ ri[𝕜](epi f) ↔
      p.1 ∈ riDom[𝕜](f) ∧ f p.1 < p.2 := by
  simpa [Set.univ_inter] using
    (Function.IsConvexOn.mem_ri_epi_restrict_iff
      (f := f) (s := Set.univ) hf (p := p))

theorem ri_epi_eq
    {f : E → WithTopBot 𝕜} (hf : ConvexOn 𝕜 (Set.univ : Set E) f) :
    ri[𝕜](epi f) = {p : E × 𝕜 | p.1 ∈ riDom[𝕜](f) ∧ f p.1 < p.2} := by
  ext p
  simpa using (Function.IsConvex.mem_ri_epi_iff (f := f) hf (p := p))

end Function.IsConvex

end

/-! ### Corollary_7_3_4 (from Chap02) -/
section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [LinearOrder 𝕜]
    [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 7.3.4 says that the closure `cl f` of a convex function is completely
  determined by the values of `f` on `ri (dom f)`, rendered here as `riDom[𝕜](f)`.
- `core/canonical`: the owner abstractions already present in the chapter are
  `lowerSemicontinuousHull` for the lower-semicontinuous hull, `Function.IsConvex` for convexity,
  and mathlib's `intrinsicInterior 𝕜` for relative interior. In this project, Rockafellar's
  closure `cl f` is represented directly by the chapter notation `cl(f)` for the owner
  `lowerSemicontinuousHull`.
- `bridge/view`: Rockafellar's `dom f` is the chapter owner set `dom(f)`, and agreement
  "on `ri (dom f)`" is expressed canonically by `Set.EqOn` on `riDom[𝕜](f)`.

Domain-style sampling used here:
- the chapter effective-domain owner `dom(·)` from `Definition_4_4`;
- the chapter owner predicate `Function.IsConvex` from `Theorem_4_2`;
- the chapter owner construction `lowerSemicontinuousHull` from `Text_7_0_4`;
- the epigraph owner `Function.verticalInfimum` and its comparison theorem
  `le_verticalInfimum_of_subset_epi` from `Chap01.Theorem_5_3`;
- the nearby epigraph-relative-interior bridge
  `Function.IsConvex.mem_ri_epi_iff`
  from `Lemma_7_3`, which is the source theorem's main geometric input.

Primitive data vs derived API:
- primitive datum: an extended-codomain function `f : E → WithTopBot 𝕜`;
- owner construction: `cl(f)`;
- derived API: equality of closures from equality of relative interiors of the owner effective
  domains and agreement on that common relative interior `riDom[𝕜](f)`.

Layer target: the theorem remains `source-facing`, but it belongs on the chapter owner namespace
`Function.IsConvex`, and is stated directly using the chapter owner construction
`cl(·)`, the canonical set-theoretic owner APIs, and the scoped chapter notation `riDom[𝕜](·)` for
the relative interior of the effective domain.
-/

namespace Function.IsConvex

/-- Corollary 7.3.4, primitive epigraph-relative-interior form. -/
theorem ri_epi_eq_of_riDom_eq_and_eqOn
    {f g : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) (hg : g.IsConvex 𝕜)
    (hri : riDom[𝕜](f) = riDom[𝕜](g)) (hfg : Set.EqOn f g riDom[𝕜](f)) :
    ri[𝕜](epi f) = ri[𝕜](epi g) := by
  ext p
  rcases p with ⟨x, μ⟩
  rw [hf.mem_ri_epi_iff, hg.mem_ri_epi_iff]
  constructor
  · rintro ⟨hx, hlt⟩
    exact ⟨hri ▸ hx, by simpa [hfg hx] using hlt⟩
  · rintro ⟨hx, hlt⟩
    have hx' : x ∈ riDom[𝕜](f) := hri.symm ▸ hx
    exact ⟨hx', by simpa [hfg hx'] using hlt⟩

/-- Corollary 7.3.4, primitive epigraph-closure form. -/
theorem closure_epi_eq_of_riDom_eq_and_eqOn
    {f g : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) (hg : g.IsConvex 𝕜)
    (hri : riDom[𝕜](f) = riDom[𝕜](g)) (hfg : Set.EqOn f g riDom[𝕜](f)) :
    closure (epi f) = closure (epi g) := by
  calc
    closure (epi f) = closure (ri[𝕜](epi f)) := by
      simpa using hf.closure_intrinsicInterior_eq_closure.symm
    _ = closure (ri[𝕜](epi g)) := by
      rw [hf.ri_epi_eq_of_riDom_eq_and_eqOn hg hri hfg]
    _ = closure (epi g) := by
      simpa using hg.closure_intrinsicInterior_eq_closure

end Function.IsConvex

end

section

open scoped Rockafellar

variable {𝕜 E : Type*}
    [ConditionallyCompleteLattice 𝕜] [TopologicalSpace 𝕜] [TopologicalSpace E]

namespace Function

/-- Primitive owner bridge: equality of closed epigraphs implies equality of Rockafellar closures
`cl(·)`. This stays at the minimal codomain abstraction layer of `lowerSemicontinuousHull`. -/
theorem lowerSemicontinuousHull_eq_of_closure_epi_eq
    {f g : E → WithTopBot 𝕜} (hclosure : closure (epi f) = closure (epi g)) :
    cl(f) = cl(g) := by
  simpa [lowerSemicontinuousHull] using congrArg Function.verticalInfimum hclosure

end Function

end

section

open scoped Rockafellar

variable
    {𝕜 E : Type*}
    [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

namespace Function.IsConvex

/-- Corollary 7.3.4: if two convex functions on a finite-dimensional ordered normed-field space have
same relative interior of their effective domains and agree there, then their closures `cl f` and
`cl g`, represented here by `cl(f)` and `cl(g)`, are equal. -/
-- Proof sketch: Lemma 7.3 identifies agreement on the common relative interior of the effective
-- domains with agreement on the relative interiors of the epigraphs. The convex-set closure
-- theorem for equal relative interiors then yields equality of the epigraph closures, and then the
-- primitive owner bridge `Function.lowerSemicontinuousHull_eq_of_closure_epi_eq` identifies the
-- closures.
theorem cl_eq_of_riDom_eq_and_eqOn
    {f g : E → WithTopBot 𝕜} (hf : f.IsConvex 𝕜) (hg : g.IsConvex 𝕜)
    (hri : riDom[𝕜](f) = riDom[𝕜](g)) (hfg : Set.EqOn f g riDom[𝕜](f)) :
    cl(f) = cl(g) := by
  exact Function.lowerSemicontinuousHull_eq_of_closure_epi_eq
    (hf.closure_epi_eq_of_riDom_eq_and_eqOn hg hri hfg)

end Function.IsConvex

end
