import ConvexAnalysis_Rockafellar_1970.Chap02.Definiton_8_7_0
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_6
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_0

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

universe u

variable {𝕜 : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {α : Type*} [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable {E : Type u} [AddCommGroup E] [Module 𝕜 E]

open scoped Rockafellar

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 8.6.1 characterizes the directions `y` along which every translate
  profile `λ ↦ f (x + λ • y)` is constant, and then gives a closed-case criterion from a single
  line on which `f` is bounded above.
- `core/canonical`: the owner API is the canonical namespace `Function`, especially
  `f.IsProper`, `recessionFunction`,
  `forall_antitone_translate_iff_mem_recessionCone`, and
  `forall_antitone_translate_of_closed_of_antitone_translate`, together with the
  function-facing owner set `Function.lineal`.
- `bridge/view`: Rockafellar's phrase "constant function of `λ` for every `x`" is expressed
  directly as pairwise equality `f (x + s • y) = f (x + t • y)` for arbitrary scalar parameters
  `s, t`, while the symmetric recession inequalities are packaged by
  `y ∈ lin(f)`.

Domain-style sampling used here:
- `Function.forall_antitone_translate_iff_mem_recessionCone`;
- `Function.antitone_translate_of_liminf_lt_top`;
- `Function.forall_antitone_translate_of_closed_of_antitone_translate`;
- `Function.lineal` and `Function.mem_lineal_iff`;
- `Antitone`, `Monotone`, and the order-theoretic constant-function criterion on the scalar line.

Primitive data vs derived API:
- primitive inputs: the function `f`, the direction `y`, and the translate profiles
  `t ↦ f (x + t • y)`;
- owner hypotheses: `f.IsConvex 𝕜` and `f.IsProper` for part (1), while in the
  closed bounded-line criterion of part (2) the primitive owner hypotheses are exactly
  `f.IsConvex 𝕜`, `f.IsProper`, and `LowerSemicontinuous f` on the ordered-field/topological
  scalar layer used by the closed-case propagation owner from Theorem 8.6;
- derived API: the source-facing constancy criterion and the owner-level membership
  `y ∈ lin(f)`.

Layer target: this item stays `source-facing`, but it is stated directly in the canonical
function-facing owner language `lin(f)`, rather than duplicating a second local symmetry
predicate or keeping the over-concrete
`EuclideanSpace ℝ (Fin n)` model in the public surface.
-/

-- Proof sketch: apply Theorem 8.6 to `y` and to `-y`. The first inequality gives that every
-- profile `t ↦ f (x + t • y)` is antitone; the second gives antitonicity of
-- `t ↦ f (x + t • (-y)) = f (x - t • y)`, which is equivalent to monotonicity of the original
-- profile. A function on the directed scalar line that is both monotone and antitone is constant,
-- and conversely a constant profile is both non-increasing and non-decreasing, so Theorem 8.6
-- yields the two recession inequalities.
/-- Corollary 8.6.1 (1): for a proper convex function `f`, every translate profile
`λ ↦ f (x + λ • y)` is constant on `𝕜`, for every base point `x`, if and only if both recession
values `((f)₀⁺) y` and `((f)₀⁺) (-y)` are nonpositive. -/
theorem forall_translate_profile_constant_iff_mem_constancySpace
    (f : E → WithTopBot α)
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (y : E) :
    (∀ x : E, ∀ s t : 𝕜, f (x + s • y) = f (x + t • y)) ↔
      y ∈ lin(f) := by
  constructor
  · intro hconst
    rw [Function.mem_lineal_iff_mem_recessionCone]
    constructor
    · exact
        (Function.forall_antitone_translate_iff_mem_recessionCone
            f hf_convex hf_proper y).1
          (fun x s t _ ↦ by
            simp [hconst x s t])
    · exact
        (Function.forall_antitone_translate_iff_mem_recessionCone
            f hf_convex hf_proper (-y)).1
          (fun x s t _ ↦ by
            simpa [smul_neg, add_assoc, add_left_comm, add_comm] using
              le_of_eq (hconst x (-t) (-s)))
  · intro hy
    rw [Function.mem_lineal_iff_mem_recessionCone] at hy
    rcases hy with ⟨hy, hneg_y⟩
    have hy_antitone : ∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • y)) :=
      (Function.forall_antitone_translate_iff_mem_recessionCone
          f hf_convex hf_proper y).2 hy
    have hneg_antitone : ∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • (-y))) :=
      (Function.forall_antitone_translate_iff_mem_recessionCone
          f hf_convex hf_proper (-y)).2 hneg_y
    intro x s t
    rcases le_total s t with hst | hts
    · apply le_antisymm
      · have h := hneg_antitone (x + (s + t) • y) hst
        simpa [add_assoc, add_left_comm, add_comm, add_smul, smul_neg] using h
      · exact hy_antitone x hst
    · apply le_antisymm
      · exact hy_antitone x hts
      · have h := hneg_antitone (x + (t + s) • y) hts
        simpa [add_assoc, add_left_comm, add_comm, add_smul, smul_neg] using h

section

variable {F : Type u}
variable {𝕜' : Type*}
variable [Field 𝕜'] [ConditionallyCompleteLinearOrder 𝕜'] [IsStrictOrderedRing 𝕜']
variable [TopologicalSpace 𝕜'] [OrderTopology 𝕜']
variable [TopologicalSpace (WithTopBot 𝕜')] [OrderTopology (WithTopBot 𝕜')]
variable [AddCommGroup F] [Module 𝕜' F]
variable [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul 𝕜' F]

-- Proof sketch: the assumed upper bound gives `x ∈ dom(f)` and
-- `liminf (fun t ↦ f (x + t • y)) atTop < ⊤`, so `antitone_translate_of_liminf_lt_top` yields
-- antitonicity of `t ↦ f (x + t • y)` at that base point. The closed-case
-- propagation theorem from Theorem 8.6 extends this antitonicity to every parallel line; applying
-- the same argument to `-y`, using `x + t • (-y) = x + (-t) • y`, gives the opposite-direction
-- inequality, and part (1) then yields `y ∈ lin(f)`.
/-- Corollary 8.6.1 (2): if `f` is closed and one affine line parallel to `y` is bounded above by
some finite codomain value, then both recession values `((f)₀⁺) y` and `((f)₀⁺) (-y)` are
nonpositive. -/
theorem mem_constancySpace_of_exists_upper_bound_along_line
    (f : F → WithTopBot 𝕜')
    (hf_convex : f.IsConvex 𝕜')
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (y : F)
    (hbounded : ∃ x : F, ∃ β : WithTopBot 𝕜', β < ⊤ ∧ ∀ t : 𝕜', f (x + t • y) ≤ β) :
    y ∈ lin(f) := by
  rcases hbounded with ⟨x, β, hβ_top, hβ⟩
  have hx_dom : x ∈ dom(f) := by
    rw [mem_effectiveDomain]
    exact lt_of_le_of_lt (by simpa using hβ (0 : 𝕜')) hβ_top
  have hy_antitone_x : Antitone (fun t : 𝕜' ↦ f (x + t • y)) := by
    refine Function.antitone_translate_of_liminf_lt_top f hf_convex ?_
    refine lt_of_le_of_lt
      (Filter.liminf_le_of_frequently_le' <| Filter.Frequently.of_forall (fun t ↦ hβ t))
      hβ_top
  have hy_antitone : ∀ z : F, Antitone (fun t : 𝕜' ↦ f (z + t • y)) :=
    Function.forall_antitone_translate_of_closed_of_antitone_translate
      (f := f) hf_convex hf_proper hf_closed y hx_dom hy_antitone_x
  have hneg_antitone_x : Antitone (fun t : 𝕜' ↦ f (x + t • (-y))) := by
    refine Function.antitone_translate_of_liminf_lt_top f hf_convex ?_
    refine lt_of_le_of_lt
      (Filter.liminf_le_of_frequently_le' <|
        Filter.Frequently.of_forall (fun t ↦ by
          simpa [smul_neg, neg_smul] using hβ (-t)))
      hβ_top
  have hneg_antitone : ∀ z : F, Antitone (fun t : 𝕜' ↦ f (z + t • (-y))) :=
    Function.forall_antitone_translate_of_closed_of_antitone_translate
      (f := f) hf_convex hf_proper hf_closed (-y) hx_dom hneg_antitone_x
  have hy_mem_recession : y ∈ Function.recessionCone ((f)₀⁺) :=
    (Function.forall_antitone_translate_iff_mem_recessionCone
      (f := f) hf_convex hf_proper y).1 hy_antitone
  have hneg_mem_recession : -y ∈ Function.recessionCone ((f)₀⁺) :=
    (Function.forall_antitone_translate_iff_mem_recessionCone
      (f := f) hf_convex hf_proper (-y)).1 hneg_antitone
  exact (Function.mem_lineal_iff_mem_recessionCone).2 ⟨hy_mem_recession, hneg_mem_recession⟩

end

end Function

end
