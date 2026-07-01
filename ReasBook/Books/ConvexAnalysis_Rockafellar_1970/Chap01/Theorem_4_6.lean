import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section ClosedSublevel

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

/-!
Source/core/bridge triage:

-- `source-facing`: Theorem 4.6 asserts convexity of the strict and closed sublevel sets of a
  convex function at a fixed height. The source states this on `R^n`; the owner theorem is
  formalized at the intrinsic ordered-module level for `WithTopBot α`-valued functions, with
  `R^n` as a specialization.
- `core/canonical`: the owner abstraction is first relative-domain
  `Function.IsConvexOn 𝕜 s f`, with global `Function.IsConvex 𝕜 f` recovered by the
  specialization `s = Set.univ`; quasiconvexity is similarly exposed first on `s`.
- `bridge/view`: scalar-height closed sublevels are projections of intersections of the canonical
  epigraph with horizontal closed half-spaces, while strict sublevels are then obtained from
  the canonical ordered bridge `QuasiconvexOn.convex_lt`.

Domain-style sampling used here:
- the chapter owner abstractions `Function.IsConvexOn` / `Function.IsConvex` from `Theorem_4_2`;
- `Function.IsConvex.convex_epigraph`;
- `convex_halfSpace_le`;
- `QuasiconvexOn.convex_lt`.

Textual repair note: the source uses the same symbol `x` both for the point variable and for the
level value in `[-∞, +∞]`. The Lean statements below use `μ : WithTopBot α` for the level height.
-/

omit [AddCommMonoid α] [PartialOrder α] [IsOrderedAddMonoid α] [NoBotOrder α] in
private theorem withTopBot_exists_coe_of_ne_top_ne_bot {x : WithTopBot α}
    (hxtop : x ≠ ⊤) (hxbot : x ≠ ⊥) :
    ∃ a : α, (a : WithTopBot α) = x := by
  cases x with
  | none =>
      exact (hxtop rfl).elim
  | some x' =>
      cases x' with
      | bot =>
          exact (hxbot rfl).elim
      | coe a =>
          exact ⟨a, rfl⟩

omit [NoBotOrder α] in
/-- Primitive finite-height closed-sublevel form: if `f` is convex on `s`, then for each
finite level `r : α`, the relative closed sublevel `{x ∈ s | f x ≤ r}` is convex. -/
theorem Function.IsConvexOn.convex_le_coe {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (r : α) :
    Convex 𝕜 {x : E | x ∈ s ∧ f x ≤ (r : WithTopBot α)} := by
  have hset :
      {x : E | x ∈ s ∧ f x ≤ (r : WithTopBot α)} =
        Prod.fst '' ((epi[s] f : Set (E × α)) ∩ {p : E × α | p.2 ≤ r}) := by
    ext x
    constructor
    · intro hx
      refine ⟨(x, r), ?_, rfl⟩
      constructor
      · exact (mem_epi_restrict_iff).2 hx
      · simp
    · rintro ⟨⟨x, t⟩, hpt, rfl⟩
      rcases hpt with ⟨hxt, htr⟩
      have hsx : x ∈ s := (mem_epi_restrict_iff.1 hxt).1
      have hfx : f x ≤ (t : WithTopBot α) := (mem_epi_restrict_iff.1 hxt).2
      have htr' : (t : WithTopBot α) ≤ (r : WithTopBot α) := by
        change (((t : WithBot α) : WithTop (WithBot α)) ≤
          ((r : WithBot α) : WithTop (WithBot α)))
        exact WithTop.coe_le_coe.mpr (WithBot.coe_le_coe.mpr (by simpa using htr))
      exact ⟨hsx, le_trans hfx htr'⟩
  rw [hset]
  have hconv_epi : Convex 𝕜 (epi[s] f) := by
    simpa [Function.IsConvexOn] using hf
  simpa using
    (hconv_epi.inter (by
      simpa using convex_halfSpace_le (LinearMap.snd 𝕜 E α).isLinear r)).linear_image
      (LinearMap.fst 𝕜 E α)

/-- Relative owner form of Theorem 4.6 (2): if `f` is convex on `s`, then for any level
`μ ∈ [-∞, +∞]` the relative closed sublevel set `{x ∈ s | f x ≤ μ}` is convex. -/
theorem Function.IsConvexOn.convex_le {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (hs : Convex 𝕜 s)
    (μ : WithTopBot α) :
    Convex 𝕜 {x : E | x ∈ s ∧ f x ≤ μ} := by
  by_cases hμ_top : μ = ⊤
  · subst hμ_top
    simpa using hs
  by_cases hμ_bot : μ = ⊥
  · subst hμ_bot
    have hset :
        {x : E | x ∈ s ∧ f x ≤ (⊥ : WithTopBot α)} =
          ⋂ r : α, {x : E | x ∈ s ∧ f x ≤ (r : WithTopBot α)} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hx r
        exact ⟨hx.1, le_trans hx.2 bot_le⟩
      · intro hx
        have hsx : x ∈ s := by
          let r0 : α := Classical.choice (inferInstance : Nonempty α)
          exact (hx r0).1
        refine ⟨hsx, ?_⟩
        by_contra hfx_bot
        have hfx_ne_bot : f x ≠ (⊥ : WithTopBot α) := by
          intro hfx
          exact hfx_bot (hfx ▸ le_rfl)
        have hfx_ne_top : f x ≠ (⊤ : WithTopBot α) := by
          intro hfx
          have htop_le : (⊤ : WithTopBot α) ≤ (0 : α) := by
            simpa [hfx] using (hx 0).2
          have hzero_top : ((0 : α) : WithTopBot α) = ⊤ := top_le_iff.mp htop_le
          simpa using hzero_top.symm
        rcases withTopBot_exists_coe_of_ne_top_ne_bot hfx_ne_top hfx_ne_bot with ⟨a, ha⟩
        rcases exists_not_ge a with ⟨r, hr⟩
        have hxr : (a : WithTopBot α) ≤ (r : WithTopBot α) := by
          simpa [ha] using (hx r).2
        have har : a ≤ r := by
          change (((a : WithBot α) : WithTop (WithBot α)) ≤
            ((r : WithBot α) : WithTop (WithBot α))) at hxr
          exact WithBot.coe_le_coe.mp (WithTop.coe_le_coe.mp hxr)
        exact hr har
    rw [hset]
    exact convex_iInter fun r ↦ hf.convex_le_coe r
  rcases withTopBot_exists_coe_of_ne_top_ne_bot hμ_top hμ_bot with ⟨r, hr⟩
  simpa [hr] using hf.convex_le_coe r

/-- A `WithTopBot α`-valued function convex on `s` is quasiconvex on `s`. -/
theorem Function.IsConvexOn.quasiconvexOn {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (hs : Convex 𝕜 s) :
    QuasiconvexOn 𝕜 s f := by
  intro r
  exact hf.convex_le hs r

/-- Theorem 4.6 (2): for a convex `WithTopBot α`-valued function on a `𝕜`-module and any level
`μ ∈ [-∞, +∞]`, the closed sublevel set `{x | f x ≤ μ}` is convex. -/
theorem Function.IsConvex.convex_le {f : E → WithTopBot α} (hf : Function.IsConvex 𝕜 f)
    (μ : WithTopBot α) :
    Convex 𝕜 {x : E | f x ≤ μ} := by
  simpa [Function.IsConvex] using
    (Function.IsConvexOn.convex_le
      (𝕜 := 𝕜)
      (s := Set.univ)
      (f := f)
      hf
      (convex_univ : Convex 𝕜 (Set.univ : Set E))
      μ)

/-- A convex `WithTopBot α`-valued function is quasiconvex on its whole ambient space. -/
theorem Function.IsConvex.quasiconvexOn {f : E → WithTopBot α} (hf : Function.IsConvex 𝕜 f) :
    QuasiconvexOn 𝕜 (Set.univ : Set E) f := by
  simpa [Function.IsConvex] using
    (Function.IsConvexOn.quasiconvexOn
      (𝕜 := 𝕜)
      (s := Set.univ)
      (f := f)
      hf
      (convex_univ : Convex 𝕜 (Set.univ : Set E)))

end ClosedSublevel

section StrictSublevel

variable {𝕜 : Type v} {E : Type u} {α : Type w}
variable [Semiring 𝕜] [PartialOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommMonoid α] [LinearOrder α] [IsOrderedAddMonoid α]
variable [Module 𝕜 α] [PosSMulMono 𝕜 α] [NoBotOrder α]

/-- Relative owner form of Theorem 4.6 (1): if `f` is convex on `s`, then for any level
`μ ∈ [-∞, +∞]` the relative strict sublevel set `{x ∈ s | f x < μ}` is convex. -/
theorem Function.IsConvexOn.convex_lt {s : Set E} {f : E → WithTopBot α}
    (hf : Function.IsConvexOn 𝕜 s f) (hs : Convex 𝕜 s) (μ : WithTopBot α) :
    Convex 𝕜 {x : E | x ∈ s ∧ f x < μ} := by
  simpa using (hf.quasiconvexOn hs).convex_lt μ

/-- Theorem 4.6 (1): for a convex `WithTopBot α`-valued function on a `𝕜`-module and any level
`μ ∈ [-∞, +∞]`, the strict sublevel set `{x | f x < μ}` is convex. -/
theorem Function.IsConvex.convex_lt {f : E → WithTopBot α} (hf : Function.IsConvex 𝕜 f)
    (μ : WithTopBot α) :
    Convex 𝕜 {x : E | f x < μ} := by
  simpa [Function.IsConvex] using
    (Function.IsConvexOn.convex_lt
      (𝕜 := 𝕜)
      (s := Set.univ)
      (f := f)
      hf
      (convex_univ : Convex 𝕜 (Set.univ : Set E))
      μ)

end StrictSublevel
