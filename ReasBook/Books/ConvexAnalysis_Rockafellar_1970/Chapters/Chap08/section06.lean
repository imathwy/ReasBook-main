import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Order.LiminfLimsup

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_8_6_1 (from Chap02) -/
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
    (f : E → WithBotTop α)
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
variable [TopologicalSpace (WithBotTop 𝕜')] [OrderTopology (WithBotTop 𝕜')]
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
    (f : F → WithBotTop 𝕜')
    (hf_convex : f.IsConvex 𝕜')
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (y : F)
    (hbounded : ∃ x : F, ∃ β : WithBotTop 𝕜', β < ⊤ ∧ ∀ t : 𝕜', f (x + t • y) ≤ β) :
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

/-! ### Corollary_8_6_2 (from Chap02) -/
section

variable {𝕜 E α : Type*} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
  [AddCommGroup E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 8.6.2 says that a convex function bounded above on an affine set is
  constant there.
- `core/canonical`: this file now exposes the codomain at the ordered-extended layer
  `WithTopBot α` (rather than the concrete alias `EReal`) together with
  the set owner `ConvexOn 𝕜 (M : Set E)`, `AffineSubspace 𝕜 E`, and the Chapter 8 owner theorem
  `Function.antitone_translate_of_liminf_lt_top`.
- `bridge/view`: the affine line through two points of `M` is packaged canonically by
  `AffineMap.lineMap`; constancy on `M` is then read off from the endpoint values at
  `t = 0, 1`.

Domain-style sampling used here:
- `Function.antitone_translate_of_liminf_lt_top` from `Theorem_8_6`;
- `Filter.liminf_le_of_frequently_le'`;
- `AffineMap.lineMap_mem`;
- `AffineMap.lineMap_apply_module'`;
- `AffineMap.lineMap_apply_zero` and `AffineMap.lineMap_apply_one`.

- Primitive data vs derived API: the primitive inputs are the convex function `f`, the affine
  subspace `M`, and one finite codomain upper bound `b : WithTopBot α` with `b < ⊤` on `M`;
  the antitone line profiles
  and the final constancy conclusion are derived from those canonical inputs.
- Layer target: this item remains `source-facing`, but the proof now reuses the chapter owner
  theorem controlling bounded-above translate profiles instead of rebuilding that argument with a
  local Archimedean construction.
-/

namespace ConvexOn

variable {f : E → WithTopBot α}

private theorem antitone_lineMap_of_affineSubspace_of_le_lt_top
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    {b : WithTopBot α} (hb_top : b < ⊤) (hb : ∀ z : M, f z ≤ b)
    (x y : M) :
    Antitone (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t)) := by
  let L : 𝕜 →ₗ[𝕜] E :=
    { toFun := fun t => t • ((y : E) - (x : E))
      map_add' := by intro s t; simp [add_smul]
      map_smul' := by intro s t; simp [mul_smul] }
  have hprofile_convex_pre :
      ConvexOn 𝕜 (L ⁻¹' ((fun z : E ↦ (x : E) + z) ⁻¹' (M : Set E)))
        (fun t : 𝕜 ↦ f ((x : E) + L t)) := by
    simpa [Function.comp] using
      (hf.translate_right (x : E)).comp_linearMap L
  have hpre_univ :
      (Set.univ : Set 𝕜) ⊆ L ⁻¹' ((fun z : E ↦ (x : E) + z) ⁻¹' (M : Set E)) := by
    intro t ht
    change (x : E) + t • ((y : E) - (x : E)) ∈ M
    simpa [AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc] using
      (AffineMap.lineMap_mem t x.2 y.2)
  have hprofile_convex :
      ConvexOn 𝕜 (Set.univ : Set 𝕜) (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t)) := by
    refine (hprofile_convex_pre.subset hpre_univ convex_univ)
    intro t
    simp [L, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc]
  have hprofile_isConvex :
      (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t)).IsConvex 𝕜 := by
    simpa [Function.IsConvex, Function.IsConvexOn] using hprofile_convex
  have hliminf :
      Filter.liminf (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t)) Filter.atTop < ⊤ := by
    refine lt_of_le_of_lt
      (Filter.liminf_le_of_frequently_le' <| Filter.Frequently.of_forall ?_)
      hb_top
    intro t
    exact hb ⟨AffineMap.lineMap (x : E) (y : E) t, AffineMap.lineMap_mem t x.2 y.2⟩
  simpa [zero_add, one_smul] using
    (Function.antitone_translate_of_liminf_lt_top
      (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t))
      hprofile_isConvex
      (x := (0 : 𝕜)) (y := (1 : 𝕜))
      hliminf)

-- Proof sketch: on the affine line through `x` and `y`, the global upper bound on `M` gives a
-- finite liminf at `+∞`. The Chapter 8 owner theorem `antitone_translate_of_liminf_lt_top` then
-- shows that the translate profile along the direction `y - x` is antitone, so `f y ≤ f x`.
-- Repeating the same argument with `x` and `y` exchanged gives `f x ≤ f y`, hence equality.
/-- Corollary 8.6.2, canonical pointwise form: if `f` is bounded above on an affine set `M` by a
finite codomain value `b < ⊤`, then any two intrinsic points of `M` have equal `f`-value. -/
theorem eq_of_affineSubspace_of_le_lt_top
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    {b : WithTopBot α} (hb_top : b < ⊤) (hb : ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  have hxy := antitone_lineMap_of_affineSubspace_of_le_lt_top hf M hb_top hb x y
  have hyx := antitone_lineMap_of_affineSubspace_of_le_lt_top hf M hb_top hb y x
  exact le_antisymm
    (by simpa using hyx zero_le_one)
    (by simpa using hxy zero_le_one)

/-- Corollary 8.6.2, canonical set-owner form: a convex function on a module
is constant on an affine set `M`, expressed by subsingleton image `Set.Subsingleton (f '' M)`,
whenever it is bounded above there by a finite codomain value `< ⊤`. -/
theorem subsingleton_image_affineSubspace_of_le_lt_top
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    {b : WithTopBot α} (hb_top : b < ⊤) (hb : ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  intro fx hfx fy hfy
  rcases hfx with ⟨x, hx, rfl⟩
  rcases hfy with ⟨y, hy, rfl⟩
  exact eq_of_affineSubspace_of_le_lt_top hf M hb_top hb ⟨x, hx⟩ ⟨y, hy⟩

/-- Corollary 8.6.2, canonical set-owner form with an existential finite codomain upper bound. -/
theorem subsingleton_image_affineSubspace_of_bddAbove_lt_top
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    (hbounded : ∃ b : WithTopBot α, b < ⊤ ∧ ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  rcases hbounded with ⟨b, hb_top, hb⟩
  exact subsingleton_image_affineSubspace_of_le_lt_top hf M hb_top hb

/-! Source-facing finite-codomain specializations. -/

/-- Corollary 8.6.2, pointwise finite-codomain form. -/
theorem eq_of_affineSubspace_of_le
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    {b : α} (hb : ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  exact eq_of_affineSubspace_of_le_lt_top hf M (WithTopBot.coe_lt_top b) hb x y

/-- Corollary 8.6.2, finite-codomain set-owner form. -/
theorem subsingleton_image_affineSubspace_of_le
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    {b : α} (hb : ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  exact subsingleton_image_affineSubspace_of_le_lt_top hf M (WithTopBot.coe_lt_top b) hb

/-- Corollary 8.6.2, finite-codomain existential set-owner form. -/
theorem subsingleton_image_affineSubspace_of_bddAbove
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    (hbounded : ∃ b : α, ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  rcases hbounded with ⟨b, hb⟩
  exact subsingleton_image_affineSubspace_of_bddAbove_lt_top hf M
    ⟨(b : WithTopBot α), WithTopBot.coe_lt_top b, hb⟩

/-- Corollary 8.6.2, pointwise form: if `f` is bounded above by a finite value on an affine set
`M`, then any two intrinsic points of `M` have equal `f`-value. -/
theorem eq_of_affineSubspace_of_bddAbove_lt_top
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    (hbounded : ∃ b : WithTopBot α, b < ⊤ ∧ ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  rcases hbounded with ⟨b, hb_top, hb⟩
  exact eq_of_affineSubspace_of_le_lt_top hf M hb_top hb x y

/-- Corollary 8.6.2, pointwise finite-codomain existential form. -/
theorem eq_of_affineSubspace_of_bddAbove
    [ZeroLEOneClass 𝕜]
    (hf : ConvexOn 𝕜 (M : Set E) f) (M : AffineSubspace 𝕜 E)
    (hbounded : ∃ b : α, ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  rcases hbounded with ⟨b, hb⟩
  exact eq_of_affineSubspace_of_bddAbove_lt_top hf M
    ⟨(b : WithTopBot α), WithTopBot.coe_lt_top b, hb⟩ x y

end ConvexOn

end

/-! ### Theorem_8_6 (from Chap02) -/
noncomputable section

universe u

section

variable {E : Type u}

open scoped Rockafellar
open Filter

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 8.6 studies, for a fixed direction `y`, when the translate profile
  `λ ↦ f (x + λ • y)` is non-increasing, first from a one-point `liminf` hypothesis, then
  globally in terms of membership in `((f)₀⁺).recessionCone`, equivalently
  `((f)₀⁺) y ≤ 0`, and finally in the closed case from one base point in `dom(f)`.
- `core/canonical`: the owner abstraction is the canonical namespace `Function`, with the
  owner declarations `Function.IsConvex 𝕜`, `Function.IsProper`, `recessionFunction`,
  `Function.recessionCone`, and
  `recessionFunction_isLeast_translationUpperBounds`,
  `tendsto_differenceQuotient_atTop_recessionFunction`.
- `bridge/view`: Rockafellar's phrase "non-increasing in `λ`, `-∞ < λ < +∞`" is rendered directly
  by the canonical order-theoretic predicate `Antitone` on the scalar-parameterized profile.

Domain-style sampling used here:
- `Function.recessionFunction`;
- `Function.recessionFunction_isLeast_translationUpperBounds`;
- `Function.recessionFunction_eq_sSup_differenceQuotients_at_point`;
- `Function.tendsto_differenceQuotient_atTop_recessionFunction`;
- `Filter.liminf` and `Antitone`.

Primitive data vs derived API:
- primitive inputs: a `WithBotTop α`-valued function `f : E → WithBotTop α` on a `𝕜`-module `E`,
  a direction
  `y`, and the translate profiles `t ↦ f (x + t • y)`;
- owner hypotheses: the first two clauses separate ambient geometry (`𝕜`, `E`) from codomain
  order-additive data (`α`) on the same canonical layer as
  `recessionFunction_isLeast_translationUpperBounds`; `f.IsConvex 𝕜` is needed first, then the
  theorem-level primitive assumptions are local `dom`-non-`⊥` (for the cone equivalence) and
  global non-`⊥` (for closed-case propagation), while `f.IsProper` is kept as a derived wrapper
  layer; the closed-case propagation theorem keeps the current scalar-codomain owner from Theorem
  8.5 and alone upgrades to
  `[AddCommGroup E]` plus the topological hypotheses needed for the limit formula;
- derived API: the order-theoretic antitonicity statements for translate profiles and their
  canonical reformulation via membership in `((f)₀⁺).recessionCone`, with the textbook
  inequality `((f)₀⁺) y ≤ 0` recovered by `Function.mem_recessionCone_iff`.

Layer target: this item stays `source-facing`, but it is stated directly in the canonical owner
language of `Function.recessionFunction` on the intrinsic module layer rather than through a
coordinate model or a wrapper namespace.
-/

namespace Function

section

variable {𝕜 : Type*} {α : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable (f : E → WithBotTop α)

-- Proof sketch: apply the one-variable convex analysis of the restriction
-- `λ ↦ f (x + λ • y)`. Finiteness of `liminf` at `+∞` rules out positive asymptotic slope, so the
-- convex profile must be antitone on all of the scalar line.
/-- If the liminf of `f` along the ray `x + λ • y` is finite at `+∞`, then the profile
`λ ↦ f (x + λ • y)` is non-increasing on the scalar line. -/
theorem antitone_translate_of_liminf_lt_top
    (hf_convex : f.IsConvex 𝕜)
    {x y : E}
    (hliminf : liminf (fun t : 𝕜 ↦ f (x + t • y)) atTop < ⊤) :
    Antitone (fun t : 𝕜 ↦ f (x + t • y)) := sorry

end

section

variable {𝕜 : Type*} {α : Type*}
variable [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]
variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [Module 𝕜 α]
variable (f : E → WithBotTop α)

-- Proof sketch: if every translate profile is antitone, then the constant function `0` is a
-- translation upper bound for `f`, so the leastness statement for `(f)₀⁺` gives
-- `y ∈ ((f)₀⁺).recessionCone`. Conversely, that membership rewrites to the nonpositivity
-- inequality needed to show, via positive homogeneity, that `((f)₀⁺) ((t - s) • y) ≤ 0` for
-- `s ≤ t`; applying the
-- translation-upper-bound inequality with base point `x + s • y` and displacement `(t - s) • y`
-- gives `f (x + t • y) ≤ f (x + s • y)`, i.e. antitonicity of each translate profile.
/-- Primitive-layer form of Theorem 8.6: under the local non-`⊥` condition on `dom(f)`, every
translate profile `λ ↦ f (x + λ • y)` is non-increasing in `λ` for all base points if and only if
`y` lies in `((f)₀⁺).recessionCone`. -/
theorem forall_antitone_translate_iff_mem_recessionCone_of_dom_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ x ∈ dom(f), f x ≠ (⊥ : WithBotTop α))
    (y : E) :
    (∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • y))) ↔
      y ∈ ((f)₀⁺).recessionCone := sorry

/-- Theorem 8.6 (proper specialization): for a proper convex function, every translate profile
`λ ↦ f (x + λ • y)` is non-increasing in `λ` if and only if `y` lies in the recession cone
`((f)₀⁺).recessionCone`. -/
theorem forall_antitone_translate_iff_mem_recessionCone
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (y : E) :
    (∀ x : E, Antitone (fun t : 𝕜 ↦ f (x + t • y))) ↔
      y ∈ ((f)₀⁺).recessionCone :=
  forall_antitone_translate_iff_mem_recessionCone_of_dom_ne_bot (f := f) hf_convex
    (fun x _ => hf_proper.ne_bot x) y

end

section

open scoped Topology

variable {𝕜 : Type*}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable (f : E → WithBotTop 𝕜)

-- Proof sketch: by the assumed antitonicity at the chosen base point `x`, every positive
-- difference quotient based at `x` is nonpositive. The closed-case limit formula from Theorem 8.5
-- gives `y ∈ ((f)₀⁺).recessionCone`, and then the preceding equivalence upgrades this to
-- antitonicity for every base point.
/-- Primitive-layer closed-case propagation: antitonicity along one translate line through a point
of `dom(f)` propagates to every parallel translate line under convexity, lower semicontinuity, and
global non-`⊥` codomain values. -/
theorem forall_antitone_translate_of_closed_of_antitone_translate_of_ne_bot
    (hf_convex : f.IsConvex 𝕜)
    (hf_ne_bot : ∀ z : E, f z ≠ (⊥ : WithBotTop 𝕜))
    (hf_closed : LowerSemicontinuous f)
    (y : E)
    {x : E} (hx : x ∈ dom(f))
    (hmono : Antitone (fun t : 𝕜 ↦ f (x + t • y))) :
    ∀ z : E, Antitone (fun t : 𝕜 ↦ f (z + t • y)) := sorry

/-- Proper specialization of the closed-case propagation theorem. -/
theorem forall_antitone_translate_of_closed_of_antitone_translate
    (hf_convex : f.IsConvex 𝕜)
    (hf_proper : f.IsProper)
    (hf_closed : LowerSemicontinuous f)
    (y : E)
    {x : E} (hx : x ∈ dom(f))
    (hmono : Antitone (fun t : 𝕜 ↦ f (x + t • y))) :
    ∀ z : E, Antitone (fun t : 𝕜 ↦ f (z + t • y)) :=
  forall_antitone_translate_of_closed_of_antitone_translate_of_ne_bot (f := f)
    hf_convex (fun z => hf_proper.ne_bot z) hf_closed y hx hmono

end

end Function

end
