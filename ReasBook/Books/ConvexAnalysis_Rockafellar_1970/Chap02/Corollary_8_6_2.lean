import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_8_6
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Order.LiminfLimsup

-- Declarations for this item will be appended below by the statement pipeline.

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

local instance instSMulWithTopBotCorollary862 : SMul 𝕜 (WithTopBot α) where
  smul c x :=
    match x with
    | ⊥ => ⊥
    | (a : α) => (c • a : α)
    | ⊤ => ⊤

private theorem antitone_lineMap_of_affineSubspace_of_le_lt_top
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    {b : WithTopBot α} (hb_top : b < ⊤) (hb : ∀ z : M, f z ≤ b)
    (x y : M) :
    Antitone (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t)) := by
  let L : 𝕜 →ₗ[𝕜] E :=
    { toFun := fun t => t • ((y : E) - (x : E))
      map_add' := by intro s t; simp [add_smul]
      map_smul' := by intro s t; simp [mul_smul] }
  have hprofile_isConvex :
      (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t)).IsConvex 𝕜 := by
    let A : (𝕜 × α) →ᵃ[𝕜] (E × α) :=
      (L.prodMap LinearMap.id).toAffineMap +
        AffineMap.const 𝕜 (𝕜 × α) ((x : E), 0)
    rw [Function.isConvex_iff_convex_epigraph]
    simpa [A, L, AffineMap.lineMap_apply_module', add_comm, add_left_comm, add_assoc,
      LinearMap.prodMap_apply] using hf.convex_epigraph.affine_preimage A
  have hliminf :
      Filter.liminf (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t)) Filter.atTop < ⊤ := by
    refine lt_of_le_of_lt
      (Filter.liminf_le_of_frequently_le' <| Filter.Frequently.of_forall ?_)
      hb_top
    intro t
    exact hb ⟨AffineMap.lineMap (x : E) (y : E) t, AffineMap.lineMap_mem t x.2 y.2⟩
  have hliminf' :
      Filter.liminf
          (fun t : 𝕜 ↦
            (fun s : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) s))
              (0 + t • (1 : 𝕜))) Filter.atTop < ⊤ := by
    simpa using hliminf
  simpa [zero_add, one_smul] using
    (Function.antitone_translate_of_liminf_lt_top
      (fun t : 𝕜 ↦ f (AffineMap.lineMap (x : E) (y : E) t))
      hprofile_isConvex
      (x := (0 : 𝕜)) (y := (1 : 𝕜))
      hliminf')

-- Proof sketch: on the affine line through `x` and `y`, the global upper bound on `M` gives a
-- finite liminf at `+∞`. The Chapter 8 owner theorem `antitone_translate_of_liminf_lt_top` then
-- shows that the translate profile along the direction `y - x` is antitone, so `f y ≤ f x`.
-- Repeating the same argument with `x` and `y` exchanged gives `f x ≤ f y`, hence equality.
/-- Corollary 8.6.2, canonical pointwise form: if `f` is bounded above on an affine set `M` by a
finite codomain value `b < ⊤`, then any two intrinsic points of `M` have equal `f`-value. -/
theorem eq_of_affineSubspace_of_le_lt_top
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    {b : WithTopBot α} (hb_top : b < ⊤) (hb : ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  have hxy := antitone_lineMap_of_affineSubspace_of_le_lt_top M hf hb_top hb x y
  have hyx := antitone_lineMap_of_affineSubspace_of_le_lt_top M hf hb_top hb y x
  exact le_antisymm
    (by simpa using hyx zero_le_one)
    (by simpa using hxy zero_le_one)

/-- Corollary 8.6.2, canonical set-owner form: a convex function on a module
is constant on an affine set `M`, expressed by subsingleton image `Set.Subsingleton (f '' M)`,
whenever it is bounded above there by a finite codomain value `< ⊤`. -/
theorem subsingleton_image_affineSubspace_of_le_lt_top
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    {b : WithTopBot α} (hb_top : b < ⊤) (hb : ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  intro fx hfx fy hfy
  rcases hfx with ⟨x, hx, rfl⟩
  rcases hfy with ⟨y, hy, rfl⟩
  exact eq_of_affineSubspace_of_le_lt_top M hf hb_top hb ⟨x, hx⟩ ⟨y, hy⟩

/-- Corollary 8.6.2, canonical set-owner form with an existential finite codomain upper bound. -/
theorem subsingleton_image_affineSubspace_of_bddAbove_lt_top
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    (hbounded : ∃ b : WithTopBot α, b < ⊤ ∧ ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  rcases hbounded with ⟨b, hb_top, hb⟩
  exact subsingleton_image_affineSubspace_of_le_lt_top M hf hb_top hb

/-! Source-facing finite-codomain specializations. -/

/-- Corollary 8.6.2, pointwise finite-codomain form. -/
theorem eq_of_affineSubspace_of_le
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    {b : α} (hb : ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  exact eq_of_affineSubspace_of_le_lt_top M hf
    (WithTop.coe_lt_top (b : WithBot α)) hb x y

/-- Corollary 8.6.2, finite-codomain set-owner form. -/
theorem subsingleton_image_affineSubspace_of_le
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    {b : α} (hb : ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  exact subsingleton_image_affineSubspace_of_le_lt_top M hf
    (WithTop.coe_lt_top (b : WithBot α)) hb

/-- Corollary 8.6.2, finite-codomain existential set-owner form. -/
theorem subsingleton_image_affineSubspace_of_bddAbove
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    (hbounded : ∃ b : α, ∀ x : M, f x ≤ b) :
    Set.Subsingleton (f '' M) := by
  rcases hbounded with ⟨b, hb⟩
  exact subsingleton_image_affineSubspace_of_bddAbove_lt_top M hf
    ⟨(b : WithTopBot α), WithTop.coe_lt_top (b : WithBot α), hb⟩

/-- Corollary 8.6.2, pointwise form: if `f` is bounded above by a finite value on an affine set
`M`, then any two intrinsic points of `M` have equal `f`-value. -/
theorem eq_of_affineSubspace_of_bddAbove_lt_top
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    (hbounded : ∃ b : WithTopBot α, b < ⊤ ∧ ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  rcases hbounded with ⟨b, hb_top, hb⟩
  exact eq_of_affineSubspace_of_le_lt_top M hf hb_top hb x y

/-- Corollary 8.6.2, pointwise finite-codomain existential form. -/
theorem eq_of_affineSubspace_of_bddAbove
    [ZeroLEOneClass 𝕜]
    (M : AffineSubspace 𝕜 E) (hf : f.IsConvex 𝕜)
    (hbounded : ∃ b : α, ∀ x : M, f x ≤ b)
    (x y : M) :
    f x = f y := by
  rcases hbounded with ⟨b, hb⟩
  exact eq_of_affineSubspace_of_bddAbove_lt_top M hf
    ⟨(b : WithTopBot α), WithTop.coe_lt_top (b : WithBot α), hb⟩ x y

end ConvexOn

end
