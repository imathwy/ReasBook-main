import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_32_4_1 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [CommRing 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {f : E → WithTopBot 𝕜}

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 32.4.1 says that if a convex function attains its supremum on an
  arbitrary set `S` at a point `x ∈ ri(dom f)`, then every subgradient at `x` defines a linear
  functional whose supremum on `S` is attained at the same point `x`.
- `core/canonical`: the owner-level mechanism is the normal-cone theorem
  `mem_normalCone_of_mem_subdifferentialAt_of_isMaxOn` from Theorem 32.4 together with the
  owner bridge `isMaxOn_pairing_of_mem_normalCone` from `Chap01.Definition_2_7_10`.
- `bridge/view`: the source phrase “yields a linear functional attaining its supremum over `S`
  at `x`” is represented directly by `IsMaxOn (fun y ↦ (⟪y, xStar⟫ₚ : 𝕜)) S x`.

Domain-style sampling used here:
- `mem_normalCone_of_mem_subdifferentialAt_of_isMaxOn` from `Chap06.Theorem_32_4`;
- `isMaxOn_pairing_of_mem_normalCone` from `Chap01.Definition_2_7_10`;
- `riDom[𝕜](·)` from `Chap01.Definition_4_4`;
- `IsMaxOn` from mathlib's extrema API.

Primitive data vs derived API:
- primitive inputs on the source theorem surface: `x ∈ riDom[𝕜](f)`, `f x ≠ ⊥`, the maximizing
  point data `x ∈ S` and `IsMaxOn f S x`, and a chosen subgradient
  `xStar ∈ ∂[Y]f(x)`;
- derived API: `intrinsicInterior_subset` supplies the owner-level finiteness datum
  `x ∈ dom(f)`, and the two upstream owner theorems compose to the linear-maximizer conclusion for
  the pairing functional
  `y ↦ (⟪y, xStar⟫ₚ : 𝕜)` on `S`.

Layer target: `source-facing`, as a thin direct corollary on `riDom[𝕜](f)` with no extra local
owner-layer wrapper theorem.
-/

-- Proof sketch: `x ∈ riDom[𝕜](f)` implies `x ∈ dom(f)` by `intrinsicInterior_subset`, then apply
-- the two canonical owner theorems directly.
/-- Source-facing `riDom[𝕜]` specialization of Corollary 32.4.1. -/
theorem isMaxOn_pairing_of_mem_subdifferentialAt_of_mem_riDom
    {S : Set E} {x : E} (hxri : x ∈ riDom[𝕜](f)) (hx_bot : f x ≠ ⊥)
    (hxS : x ∈ S) (hmax : IsMaxOn f S x)
    {Y : Type (max u v)} [AddCommMonoid Y] [Module 𝕜 Y]
    [HasLinearPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜] {xStar : Y}
    (hxStar : xStar ∈ ∂[Y]f(x)) :
    IsMaxOn (fun y : E ↦ (⟪y, xStar⟫ₚ : 𝕜)) S x := by
  have hx : x ∈ dom(f) := intrinsicInterior_subset hxri
  exact isMaxOn_pairing_of_mem_normalCone
    (mem_normalCone_of_mem_subdifferentialAt_of_isMaxOn hxStar hxS hmax hx hx_bot)

end

/-! ### Theorem_32_4 (from Chap06) -/
noncomputable section

open scoped Rockafellar

universe u v

section

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 32.4 says that if a function attains a relative maximum on `C` at `x`,
  then every subgradient at `x` is normal to `C`, and if the value on `C` is not constant then
  such a subgradient is nonzero.
- `core/canonical`: the owner abstractions already present upstream are `IsMaxOn`,
  `_root_.subdifferentialAt`, and `N[𝕜](· | ·)`, all naturally pairing-based.
- `bridge/view`: the textbook phrase “`x⋆` is normal to `C` at `x`” is exactly
  `xStar ∈ N[𝕜](x | C)`, while the source phrase “`f` attains its supremum on `C` at `x`” is
  expressed canonically by the pair `x ∈ C` and `IsMaxOn f C x`, since mathlib's owner
  `IsMaxOn` does not itself include feasibility of the base point.

Domain-style sampling used here:
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `N[𝕜](· | ·)` and `mem_normalCone_iff` from `Chap01.Definition_2_7_10`;
- `HasPairing` plus compatibility classes (`HasPairingSubLeft`, `HasPairingZeroRight`) from
  `Chap01.HasPairing` as the canonical codomain-agnostic duality layer;
- `IsMaxOn` from mathlib's order-extrema API.

Primitive data vs derived API:
- primitive inputs for the normal-cone clause: the function `f`, the set `C`, the feasible
  maximizing point data `x ∈ C` and `IsMaxOn f C x`, the Chapter 23 finite-point hypotheses
  `x ∈ dom(f)` and `f x ≠ ⊥`, and a candidate subgradient
  `xStar ∈ subdifferentialAt f x Y` in an arbitrary pairing codomain `Y`;
- derived API: normality of `xStar` at `x` relative to `C`, and under source-facing nonconstancy
  of `f` on `C` at the maximizing value `f x`, the nonvanishing conclusion `xStar ≠ 0`; the
  stronger global strict-inequality hypothesis `∃ y, f y < f x` is kept only as a companion.

Layer target: `source-facing`. The source theorem is refined to two atomic owner statements rather
than one conjunction with mismatched hypothesis layers: a minimal normal-cone theorem on
the canonical feasibility/maximizer data `x ∈ C` and `IsMaxOn f C x`, and a separate
source-facing nonzero corollary whose primitive inputs are only `IsMaxOn f C x` and
nonconstancy on `C`. A stronger global strict-inequality statement is retained only as a
companion theorem.

Ambient minimization:
- `_root_.subdifferentialAt` is dual-valued and pairing-based, so the theorem surface stays at
  the primitive layer `[Sub E]` with arbitrary codomain `Y` carrying pairing data; finite
  dimensionality, normed/inner-product structure, module structure, convexity of `f`, and
  `x ∈ riDom[𝕜](f)` are not part of the owner-level statements once a specific subgradient is
  given;
- `AddLeftMono 𝕜` is required only by the normal-cone clause, to use the chapter bridge
  `mem_normalCone_iff_sub_nonpos` and right-translation monotonicity in the scalar inequality
  step; the nonzero clauses below do not require it;
- `PartialOrder 𝕜` is needed only for the `EqOn`-based nonzero clause, where `le_antisymm`
  converts two inequalities into equality on `C`;
- upstream-first scalar check: both owner signatures used here are already scalar-parameterized in
  this project closure (`_root_.subdifferentialAt : (E → WithTopBot 𝕜) → ...` and `N[𝕜](· | ·)`),
  so the theorem is stated directly at that owner layer instead of keeping a real-only wrapper;
- the base-point finiteness hypotheses `x ∈ dom(f)` and `f x ≠ ⊥` are essential, because the
  Chapter 23 subdifferential degenerates outside the finite branch.
-/

section NormalConeClause

variable {𝕜 : Type v} [AddCommGroup 𝕜] [Preorder 𝕜] [AddLeftMono 𝕜]
variable {E : Type u} [Sub E]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜]
variable {f : E → WithTopBot 𝕜} {C : Set E} {x : E}

-- Proof sketch: on the finite branch `x ∈ dom(f)` and `f x ≠ ⊥`, combine the subgradient
-- inequality at `x` with the maximality inequality on `C`. The explicit feasibility hypothesis
-- `x ∈ C` supplies the base-point membership required by `mem_normalCone_iff`, since `IsMaxOn`
-- alone does not include it. For each `z ∈ C`, maximality gives `f z ≤ f x`, while subgradient
-- membership gives
-- `f z ≥ f x + (⟪z - x, xStar⟫ₚ : 𝕜)`. Hence `(⟪x - z, xStar⟫ₚ : 𝕜) ≥ 0`, i.e.
-- `xStar ∈ N[𝕜](x | C)`.
/-- Theorem 32.4, normal-cone clause in owner-set form: at a finite relative maximizer, the whole
subdifferential is contained in the normal cone. -/
theorem subdifferentialAt_subset_normalCone_of_isMaxOn
    (hxC : x ∈ C) (hmax : IsMaxOn f C x) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    (∂[Y]f(x)) ⊆ N[𝕜](x | C) := by
  intro xStar hxStar
  rw [mem_normalCone_iff_sub_nonpos]
  refine ⟨hxC, ?_⟩
  have hx_top : f x ≠ ⊤ := ne_of_lt hx
  obtain ⟨fx, hfx⟩ : ∃ fx : 𝕜, f x = (fx : WithTopBot 𝕜) := by
    rcases hfx' : f x with _ | a
    · exact (hx_top hfx').elim
    · rcases ha : a with _ | fx
      · subst ha
        exact (hx_bot (by simpa using hfx')).elim
      · exact ⟨fx, rfl⟩
  intro z hzC
  have hz_sub : f z ≥ f x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
    (mem_subdifferentialAt_pairing.mp hxStar) z
  have hz_le : f z ≤ f x := (isMaxOn_iff.mp hmax) z hzC
  have hz_sub' : ((fx : 𝕜) : WithTopBot 𝕜) +
      ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ f z := by
    simpa [hfx] using hz_sub
  have hz_le' : f z ≤ ((fx : 𝕜) : WithTopBot 𝕜) := by
    simpa [hfx] using hz_le
  have hz_add_le : ((fx : 𝕜) : WithTopBot 𝕜) +
      ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ ((fx : 𝕜) : WithTopBot 𝕜) :=
    le_trans hz_sub' hz_le'
  have hz_add_le_scalar : fx + (⟪z - x, xStar⟫ₚ : 𝕜) ≤ fx := by
    have hz_add_le_coe :
        (((fx + (⟪z - x, xStar⟫ₚ : 𝕜) : 𝕜) : WithTopBot 𝕜) ≤
          ((fx : 𝕜) : WithTopBot 𝕜)) := by
      change ((fx : 𝕜) : WithTopBot 𝕜) +
          ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ ((fx : 𝕜) : WithTopBot 𝕜)
      exact hz_add_le
    have hz_add_le_coe' :
        ((fx + (⟪z - x, xStar⟫ₚ : 𝕜) : 𝕜) : WithBot 𝕜) ≤
          ((fx : 𝕜) : WithBot 𝕜) :=
      WithTop.coe_le_coe.mp hz_add_le_coe
    exact WithBot.coe_le_coe.mp hz_add_le_coe'
  have hz_pair_nonpos : (⟪z - x, xStar⟫ₚ : 𝕜) ≤ 0 := by
    have hz_shift : (-fx) + (fx + (⟪z - x, xStar⟫ₚ : 𝕜)) ≤ (-fx) + fx :=
      add_le_add_right hz_add_le_scalar (-fx)
    simpa [add_assoc, add_left_comm, add_comm] using hz_shift
  exact hz_pair_nonpos

/-- Pointwise corollary of
`subdifferentialAt_subset_normalCone_of_isMaxOn`. -/
theorem mem_normalCone_of_mem_subdifferentialAt_of_isMaxOn
    {xStar : Y} (hxStar : xStar ∈ (∂[Y]f(x)))
    (hxC : x ∈ C) (hmax : IsMaxOn f C x) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥) :
    xStar ∈ N[𝕜](x | C) := by
  exact (subdifferentialAt_subset_normalCone_of_isMaxOn
    hxC hmax hx hx_bot) hxStar

end NormalConeClause

section NonzeroEqOnClause

variable {𝕜 : Type v} [AddCommMonoid 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [Sub E]
variable {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
variable {f : E → WithTopBot 𝕜} {C : Set E} {x : E}

-- Proof sketch: if `xStar = 0`, the defining subgradient inequality reduces to `f y ≥ f x` for
-- every `y ∈ C`. Combined with maximality on `C`, this forces `f` to be constant on `C`, so any
-- source-facing nonconstancy assumption on `C` rules out the zero subgradient.
/-- Theorem 32.4, nonzero clause in source-facing owner form: at a relative maximizer, if `f` is
not constant on `C`, then every subgradient at `x` is nonzero. -/
theorem subdifferentialAt_subset_ne_zero_of_isMaxOn
    (hmax : IsMaxOn f C x)
    (hnot_const : ¬ Set.EqOn f (fun _ ↦ f x) C) :
    (∂[Y]f(x)) ⊆ {xStar : Y | xStar ≠ 0} := by
  intro xStar hxStar hxStar_zero
  have hEqOn : Set.EqOn f (fun _ ↦ f x) C := by
    intro y hyC
    have hy_sub : f y ≥ f x + ((⟪y - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
      (mem_subdifferentialAt_pairing.mp hxStar) y
    subst hxStar_zero
    have hy_ge : f x ≤ f y := by
      simpa using hy_sub
    have hy_le : f y ≤ f x := (isMaxOn_iff.mp hmax) y hyC
    exact le_antisymm hy_le hy_ge
  exact hnot_const hEqOn

/-- Pointwise corollary of
`subdifferentialAt_subset_ne_zero_of_isMaxOn`. -/
theorem ne_zero_of_mem_subdifferentialAt_of_isMaxOn
    {xStar : Y} (hxStar : xStar ∈ (∂[Y]f(x)))
    (hmax : IsMaxOn f C x)
    (hnot_const : ¬ Set.EqOn f (fun _ ↦ f x) C) :
    xStar ≠ 0 := by
  exact (subdifferentialAt_subset_ne_zero_of_isMaxOn
    hmax hnot_const) hxStar

end NonzeroEqOnClause

section NonzeroExistsLtClause

variable {𝕜 : Type v} [AddCommMonoid 𝕜] [Preorder 𝕜]
variable {E : Type u} [Sub E]
variable {Y : Type (max u v)} [Zero Y] [HasPairing E Y 𝕜] [HasPairingZeroRight E Y 𝕜]
variable {f : E → WithTopBot 𝕜} {C : Set E} {x : E}

-- Proof sketch: if `xStar = 0`, the defining subgradient inequality reduces to `f z ≥ f x` for
-- all `z`, contradicting any strict inequality `f y < f x`.
/-- Companion strict-inequality form of the nonzero clause: if some value of `f` is strictly below
`f x`, then every subgradient at `x` is nonzero. -/
theorem subdifferentialAt_subset_ne_zero_of_exists_lt
    (hnot_const : ∃ y, f y < f x) :
    (∂[Y]f(x)) ⊆ {xStar : Y | xStar ≠ 0} := by
  intro xStar hxStar hxStar_zero
  rcases hnot_const with ⟨y, hy_lt⟩
  have hy_sub : f y ≥ f x + ((⟪y - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
    (mem_subdifferentialAt_pairing.mp hxStar) y
  subst hxStar_zero
  have hy_ge : f x ≤ f y := by
    simpa using hy_sub
  exact (not_le_of_gt hy_lt) hy_ge

/-- Pointwise corollary of `subdifferentialAt_subset_ne_zero_of_exists_lt`. -/
theorem ne_zero_of_mem_subdifferentialAt_of_exists_lt
    {xStar : Y} (hxStar : xStar ∈ (∂[Y]f(x))) (hnot_const : ∃ y, f y < f x) :
    xStar ≠ 0 := by
  exact (subdifferentialAt_subset_ne_zero_of_exists_lt hnot_const) hxStar

end NonzeroExistsLtClause

end
