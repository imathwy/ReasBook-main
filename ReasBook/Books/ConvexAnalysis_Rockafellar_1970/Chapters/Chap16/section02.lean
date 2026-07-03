import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_16_2_1 (from Chap03) -/
noncomputable section

open scoped Rockafellar

section

universe u v

variable {E : Type u} {F : Type v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.2.1 characterizes when the image subspace `A(E)` meets the
  relative interior of the effective domain of a proper convex function `g`.
- `core/canonical`: the owner abstractions already present in the project are
  `riDom(·)`, `supportFunction`, `convexConjugate`, `Function.recessionFunction`, and
  the
  subspace criterion
  `submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction`.
- `bridge/view`: the source equation `A^* y⋆ = 0` is the canonical `LinearMap.adjoint` rendering
  of orthogonality to the range subspace `LinearMap.range A`, while Theorem 13.3 supplies the
  companion support-function rendering of `g⋆0⁺`.

Domain-style sampling used here:
- `submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction`
  from `Lemma_16_2`;
- `convexConjugate` from `Defn_12_2`;
- `recessionFunction` from `Corollary_8_5_1`;
- `LinearMap.orthogonal_range` from the finite-dimensional adjoint API;
- `riDom(·)` for Rockafellar's `ri (dom ·)`.

Primitive data vs derived API:
- primitive inputs: a linear map `A : E →ₗ[𝕜] F` and a function `g : F → WithBotTop 𝕜`;
- owner hypotheses: `g.IsConvex 𝕜` and `g.IsProper`;
- derived output: the range-relative-interior criterion, first at the pairing-orthogonal owner
  layer and then via the adjoint equation `A.adjoint y⋆ = 0`.

Layer target: owner-first at pairing orthogonality, with an inner-product bridge corollary.
-/

/-- Corollary 16.2.1 at the canonical pairing-owner layer: for a linear map `A` and a proper
convex `g`, the image range meets `ri (dom g)` iff no range-annihilator vector has the asymmetric
recession-sign pattern. -/
theorem exists_image_mem_riDom_iff_no_range_pairingOrthogonal_asymmetric_recession
    {𝕜 : Type*}
    [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommMonoid E] [Module 𝕜 E]
    [TopologicalSpace F] [AddCommGroup F] [IsTopologicalAddGroup F]
    [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
    [HasLinearPairing F F 𝕜] [HasPairingSwap F F 𝕜]
    (A : E →ₗ[𝕜] F) (g : F → WithBotTop 𝕜)
    (hg_convex : g.IsConvex 𝕜) (hg_proper : g.IsProper) :
    (∃ x : E, A x ∈ riDom[𝕜](g)) ↔
      ¬ ∃ yStar : F,
        yStar ∈ A.rangeᗮₚ ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop 𝕜) < (g⋆)₀⁺ (-yStar) := by
  have hrange :=
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction
      (𝕜 := 𝕜) (Y := F) (L := A.range) (f := g)
      hg_convex.convex_dom hg_proper.nonempty_dom
  simpa [LinearMap.mem_range, Set.Nonempty,
    supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate
      (f := g) hg_convex hg_proper]
    using hrange

section

open scoped RealInnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

-- Proof sketch: apply the pairing-owner theorem above, then rewrite membership in
-- `(LinearMap.range A)ᗮₚ` as `A.adjoint yStar = 0` by identifying `ᗮₚ` with `ᗮ` and using
-- `LinearMap.orthogonal_range`.
/-- Corollary 16.2.1 (adjoint bridge): for a linear map `A : R^n → R^m` and a proper convex
function `g` on `R^m`, there is no vector `y⋆` with `A^* y⋆ = 0`, `(g⋆0⁺)(y⋆) ≤ 0`, and
`(g⋆0⁺)(-y⋆) > 0` iff `Ax ∈ ri (dom g)` for some `x`. -/
theorem exists_image_mem_intrinsicInterior_effectiveDomain_iff_no_adjoint_asymmetric_recession
    (A : E →ₗ[ℝ] F) (g : F → WithBotTop ℝ)
    (hg_convex : g.IsConvex ℝ) (hg_proper : g.IsProper) :
    (∃ x : E, A x ∈ riDom[ℝ](g)) ↔
      ¬ ∃ yStar : F,
        A.adjoint yStar = 0 ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop ℝ) < (g⋆)₀⁺ (-yStar) := by
  have hrange :=
    exists_image_mem_riDom_iff_no_range_pairingOrthogonal_asymmetric_recession
      (A := A) (g := g) hg_convex hg_proper
  have hmem :
      ∀ yStar : F, yStar ∈ A.rangeᗮₚ ↔ A.adjoint yStar = 0 := by
    intro yStar
    have hpairEq : A.rangeᗮₚ = (A.rangeᗮ : Submodule ℝ F) :=
      Submodule.pairingOrthogonal_eq_orthogonal_real (K := A.range)
    constructor
    · intro hyPair
      have hyOrth : yStar ∈ A.rangeᗮ := hpairEq ▸ hyPair
      have hyKer : yStar ∈ A.adjoint.ker := (LinearMap.orthogonal_range (A := A)) ▸ hyOrth
      exact hyKer
    · intro hyAdj
      have hyKer : yStar ∈ A.adjoint.ker := hyAdj
      have hyOrth : yStar ∈ A.rangeᗮ := (LinearMap.orthogonal_range (A := A)).symm ▸ hyKer
      exact hpairEq.symm ▸ hyOrth
  constructor
  · intro hx
    have hnoPair : ¬ ∃ yStar : F,
        yStar ∈ A.rangeᗮₚ ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop ℝ) < (g⋆)₀⁺ (-yStar) := (hrange.mp hx)
    intro hAdj
    apply hnoPair
    rcases hAdj with ⟨yStar, hyAdj, hle, hlt⟩
    exact ⟨yStar, (hmem yStar).2 hyAdj, hle, hlt⟩
  · intro hx
    have hnoPair : ¬ ∃ yStar : F,
        yStar ∈ A.rangeᗮₚ ∧
          (g⋆)₀⁺ yStar ≤ 0 ∧
            (0 : WithBotTop ℝ) < (g⋆)₀⁺ (-yStar) := by
      intro hPair
      apply hx
      rcases hPair with ⟨yStar, hyPair, hle, hlt⟩
      exact ⟨yStar, (hmem yStar).1 hyPair, hle, hlt⟩
    exact hrange.mpr hnoPair

end

end

/-! ### Corollary_16_2_2 (from Chap03) -/
open scoped BigOperators Rockafellar

noncomputable section

section

universe u v

variable {ι : Type v} [Fintype ι]
variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
variable [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable [HasLinearPairing E E 𝕜] [HasPairingSwap E E 𝕜]
local instance : HasPairing E E (WithBotTop 𝕜) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 16.2.2 characterizes nonemptiness of the common relative interior
  `ri (dom f₁) ∩ ··· ∩ ri (dom f_m)` for a finite family of proper convex functions by excluding
  a zero-sum family of dual vectors with one-sided inequalities for the conjugate recession
  functions `fᵢ⋆0⁺`.
- `core/canonical`: the owner abstractions already present in the project are
  `Function.IsConvex`, `Function.IsProper`, `riDom[𝕜](·)`, `f⋆`, `f0⁺`,
  `Function.NoZeroSumAsymmetricRecession`, and the subspace criterion of `Lemma_16_2`.
- `bridge/view`: Rockafellar's vectors `x₁⋆, …, x_m⋆` are encoded as one family
  `xStar : ι → E`; the condition `x₁⋆ + ··· + x_m⋆ = 0` becomes `∑ i, xStar i = 0`, and the
  diagonal-subspace orthogonality condition from `Lemma_16_2` becomes exactly that zero-sum
  equation.

Domain-style sampling used here:
- `submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction`
  from `Lemma_16_2`;
- `supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate` from `Theorem_13_3`,
  used through the canonical surface `f⋆` and `f⋆0⁺`;
- `riDom[𝕜](·)` from `Definition_4_4`;
- `Function.IsConvex` and `Function.IsProper` for the chapter-owned convexity and properness
  predicates on `WithBotTop 𝕜`-valued functions;
- finite sums over a `Fintype`.

Primitive data vs derived API:
- primitive inputs: the family `f`;
- owner hypotheses: each `f i` is convex and proper in the chapter sense;
- derived output: the equivalence between common relative-interior nonemptiness and the canonical
  family-level owner condition `Function.NoZeroSumAsymmetricRecession` on the conjugate family.

Layer target: `source-facing`, with the public surface on the finite-dimensional topological
pairing-space layer over `𝕜` rather than the inner-product-only model, and without introducing a
product-space wrapper into the public API.
-/

-- Proof sketch: apply Lemma 16.2 to the sum function on the product space `E^ι` and to the
-- diagonal subspace of constant families. The relative interior of the effective domain
-- of that sum is the product of the relative interiors `riDom[𝕜](f i)`, so meeting the diagonal
-- is exactly nonemptiness of `⋂ i, riDom[𝕜](f i)`. The orthogonal
-- complement of the diagonal consists of the families `xStar` with `∑ i, xStar i = 0`, and the
-- recession function of the conjugate of the product-space sum splits as the sum of the
-- individual functions `((f i)⋆)₀⁺`.
/-- Corollary 16.2.2: for a finite family of proper convex functions on a finite-dimensional
topological pairing space over `𝕜`, the common relative interior
`ri (dom f₁) ∩ ··· ∩ ri (dom f_m)` is nonempty if and only if the conjugate family satisfies the
canonical recession-kernel owner
`Function.NoZeroSumAsymmetricRecession`. -/
theorem common_riDom_nonempty_iff_no_zero_sum_asymmetric_conjugate_recession
    (f : ι → E → WithBotTop 𝕜)
    (hf_convex : ∀ i, (f i).IsConvex 𝕜)
    (hf_proper : ∀ i, (f i).IsProper) :
    (⋂ i, riDom[𝕜](f i)).Nonempty ↔
      Function.NoZeroSumAsymmetricRecession (fun i ↦ ((f i)⋆ : E → WithBotTop 𝕜)) := by
  sorry

end

/-! ### Lemma_16_2 (from Chap03) -/
noncomputable section

open scoped Rockafellar

universe u

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsOrderedRing 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
variable {Y : Type*} [AddCommGroup Y] [Module 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasPairing Y E 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 16.2 characterizes when a subspace `L` meets `ri (dom f)` for a proper
  convex function `f` by excluding annihilator directions with an asymmetric support-function
  behavior for `dom f`, i.e. for Rockafellar's `f⋆0⁺`.
- `core/canonical`: the owner abstractions already present in the project are
  `supportFunction`, `Function.IsConvex`, `Function.IsProper`, the chapter notation `riDom(·)`
  for relative interiors of effective domains, the effective-domain set `dom(f)`, and
  `Submodule.pairingOrthogonal`.
- `bridge/view`: Rockafellar's `ri (dom f)` is rendered directly by the established chapter
  notation `riDom[𝕜](f) = intrinsicInterior 𝕜 dom(f)`.

Domain-style sampling used here:
- `supportFunction` from `Defintion_4_8_2`;
- `riDom(·)` from `Definition_4_4`, reexported through the Chapter 1 effective-domain API;
- `exists_hyperplane_separating_properly_iff_supportFunction_conditions` from
  `Chap03/Theorem_11_1`;
- `exists_separatesProperly_iff_disjoint_ri` from
  `Chap03/Theorem_11_3`;
- `Submodule.pairingOrthogonal` for `Lᗮₚ`.

Primitive data vs derived API:
- primitive inputs (core theorem): the subspace `L` and a nonempty convex set `C`;
- source-facing wrapper inputs: `f` with owner hypotheses `Function.IsConvex f` and
  `Function.IsProper f`, used only to derive `Convex 𝕜 dom(f)` and `dom(f).Nonempty`;
- derived API: the `riDom[𝕜](f)` statement is now a thin bridge over the primitive set-owner
  theorem, and recession-function rewrites belong downstream via Theorem 13.3.

Layer target: core owner-first at the intrinsic set layer, with the textbook `riDom[𝕜](f)` form
as a source-facing wrapper.

Ambient refinement:
- The separation and support-function owners used here already live on arbitrary finite-dimensional
  normed pairing spaces over conditionally complete linearly ordered fields, so the public
  statement is refined away from the concrete model `EuclideanSpace ℝ (Fin n)` and from the
  inner-product-only owner layer.
-/

-- Proof sketch: apply Theorem 11.3 to the convex sets `L` and `dom(f)`. Since a subspace is
-- relatively open in its affine hull, disjointness of `L` from `ri (dom f)` is equivalent to the
-- existence of a proper separating hyperplane. Then use Theorem 11.1 to rewrite proper
-- separation by one vector `xStar`, note that the extremal values on `L` force `xStar ∈ Lᗮₚ`.
/-- Primitive set-owner form of Lemma 16.2: for a subspace `L` and a nonempty convex set `C`,
`L` meets `ri[𝕜](C)` iff there is no pairing-orthogonal vector `x⋆ ∈ Lᗮₚ` with
`δᵛ(x⋆ | C) ≤ 0 < δᵛ(-x⋆ | C)`. -/
theorem
    submodule_meets_intrinsicInterior_iff_no_pairingOrthogonal_asymmetric_supportFunction
    (L : Submodule 𝕜 E) (C : Set E) (hC_conv : Convex 𝕜 C) (hC_nonempty : C.Nonempty) :
    ((L : Set E) ∩ ri[𝕜](C)).Nonempty ↔
      ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | C) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | C) := by
  classical
  have hL_nonempty : ((L : Set E)).Nonempty := ⟨0, L.zero_mem⟩
  have hL_ri : ri[𝕜]((L : Set E)) = (L : Set E) := by
    simpa only [Submodule.mem_toAffineSubspace] using
      (L.toAffineSubspace.intrinsicInterior_coe :
        intrinsicInterior 𝕜 ((L.toAffineSubspace : AffineSubspace 𝕜 E) : Set E) =
          ((L.toAffineSubspace : AffineSubspace 𝕜 E) : Set E))
  have hL_cone : Set.IsCone 𝕜 (L : Set E) := by
    intro c x _ hx
    exact L.smul_mem c hx
  have hL_support_eq_zero {xStar : Y} (hxStar : xStar ∈ Lᗮₚ) :
      δᵛ(xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
    have hsupport := congrFun
      (supportFunction_eq_indicatorFunction_polarCone (𝕜 := 𝕜)
        (K := (L : Set E)) hL_nonempty hL_cone) xStar
    have hxStar_polar : xStar ∈ (((L : Set E)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
      simpa [Submodule.polarCone_eq_pairingOrthogonal] using hxStar
    have hpolar_zero : δ[𝕜](xStar | ((L : Set E)ᵒ[𝕜] : Set Y)) = 0 := by
      simpa using indicator_of_mem (C := ((L : Set E)ᵒ[𝕜] : Set Y)) hxStar_polar
    exact hsupport.trans hpolar_zero
  have hL_support_eq_top {xStar : Y} (hxStar : xStar ∉ Lᗮₚ) :
      δᵛ(xStar | (L : Set E)) = (⊤ : WithBotTop 𝕜) := by
    have hsupport := congrFun
      (supportFunction_eq_indicatorFunction_polarCone (𝕜 := 𝕜)
        (K := (L : Set E)) hL_nonempty hL_cone) xStar
    have hxStar_polar : xStar ∉ (((L : Set E)ᵒ[𝕜] : PointedCone 𝕜 Y) : Set Y) := by
      simpa [Submodule.polarCone_eq_pairingOrthogonal] using hxStar
    have hpolar_top : δ[𝕜](xStar | ((L : Set E)ᵒ[𝕜] : Set Y)) = ⊤ := by
      simpa using indicator_of_notMem (C := ((L : Set E)ᵒ[𝕜] : Set Y)) hxStar_polar
    exact hsupport.trans hpolar_top
  have hsep_disjoint :
      (∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H (L : Set E) C) ↔
        Disjoint (L : Set E) (ri[𝕜](C)) := by
    simpa [hL_ri] using
      (exists_separatesProperly_iff_disjoint_ri
        L.convex hL_nonempty hC_conv hC_nonempty : (∃ H : AffineSubspace 𝕜 E,
          AffineSubspace.SeparatesProperly Y H (L : Set E) C) ↔
            Disjoint
              (ri[𝕜](
                ((L.toAffineSubspace : AffineSubspace 𝕜 E) : Set E))
              )
              (ri[𝕜](C)))
  have hsep_pairingOrthogonal :
      (∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H (L : Set E) C) ↔
        ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
          δᵛ(xStar | C) ≤ (0 : WithTopBot 𝕜) ∧
            (0 : WithTopBot 𝕜) < δᵛ(-xStar | C) := by
    constructor
    · intro hsep
      rcases
        (exists_hyperplane_separating_properly_iff_supportFunction_conditions
          hL_nonempty hC_nonempty).1 hsep with
        ⟨xStar, hxStar_left, hxStar_right⟩
      have hC_bot : ⊥ < δᵛ(xStar | C) := by
        rcases hC_nonempty with ⟨x, hx⟩
        have hx_le :
            (⟪xStar, x⟫ₚ : WithBotTop 𝕜) ≤ δᵛ(xStar | C) := by
          rw [supportFunction_def]
          exact le_iSup (fun z : C => (⟪xStar, (z : E)⟫ₚ : WithBotTop 𝕜)) ⟨x, hx⟩
        exact lt_of_lt_of_le (WithBotTop.bot_lt_coe _) hx_le
      have hxStar_mem : xStar ∈ Lᗮₚ := by
        by_contra hxStar_mem
        have hneg_top : δᵛ(-xStar | (L : Set E)) = (⊤ : WithBotTop 𝕜) := by
          have hxStar_not_mem : xStar ∉ Lᗮₚ := hxStar_mem
          have hneg_not_mem : -xStar ∉ Lᗮₚ := by
            intro hneg_mem
            exact hxStar_not_mem (by simpa using (Lᗮₚ).neg_mem hneg_mem)
          simpa using hL_support_eq_top hneg_not_mem
        have hbot_ge : (⊥ : WithBotTop 𝕜) ≥ δᵛ(xStar | C) := by
          simpa [hneg_top] using hxStar_left
        exact (not_le_of_gt hC_bot) hbot_ge
      refine ⟨xStar, hxStar_mem, ?_, ?_⟩
      · have hneg_zero : δᵛ(-xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          have hneg_mem : -xStar ∈ Lᗮₚ := by
            simpa using (Lᗮₚ).neg_mem hxStar_mem
          simpa using hL_support_eq_zero hneg_mem
        simpa [hneg_zero] using hxStar_left
      · have hzero : δᵛ(xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          simpa using hL_support_eq_zero hxStar_mem
        simpa [hzero] using hxStar_right
    · rintro ⟨xStar, hxStar_mem, hxStar_left, hxStar_right⟩
      refine
        (exists_hyperplane_separating_properly_iff_supportFunction_conditions
          hL_nonempty hC_nonempty).2 ?_
      refine ⟨xStar, ?_, ?_⟩
      · have hneg_zero : δᵛ(-xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          have hneg_mem : -xStar ∈ Lᗮₚ := by
            simpa using (Lᗮₚ).neg_mem hxStar_mem
          simpa using hL_support_eq_zero hneg_mem
        simpa [hneg_zero] using hxStar_left
      · have hzero : δᵛ(xStar | (L : Set E)) = (0 : WithBotTop 𝕜) := by
          simpa using hL_support_eq_zero hxStar_mem
        simpa [hzero] using hxStar_right
  calc
    ((L : Set E) ∩ ri[𝕜](C)).Nonempty ↔
        ¬ Disjoint (L : Set E) (ri[𝕜](C)) := by
      rw [Set.not_disjoint_iff_nonempty_inter]
    _ ↔ ¬ ∃ H : AffineSubspace 𝕜 E, AffineSubspace.SeparatesProperly Y H (L : Set E) C :=
      not_congr hsep_disjoint.symm
    _ ↔ ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | C) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | C) :=
      not_congr hsep_pairingOrthogonal

/-- Lemma 16.2 on the `riDom` notation surface, at primitive domain data:
a subspace `L` meets `riDom[𝕜](f)` iff there is no pairing-orthogonal vector `x⋆ ∈ Lᗮₚ`
with `δᵛ(x⋆ | dom(f)) ≤ 0 < δᵛ(-x⋆ | dom(f))`, assuming only convexity and nonemptiness of
`dom(f)`. -/
theorem
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction
    {β : Type*} [LT β] [Top β]
    (L : Submodule 𝕜 E) (f : E → β)
    (hdom_conv : Convex 𝕜 dom(f)) (hdom_nonempty : dom(f).Nonempty) :
    ((L : Set E) ∩ riDom[𝕜](f)).Nonempty ↔
      ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | dom(f)) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | dom(f)) := by
  simpa using
    (submodule_meets_intrinsicInterior_iff_no_pairingOrthogonal_asymmetric_supportFunction
      (L := L) (C := dom(f)) hdom_conv hdom_nonempty)

/-- Source-facing convex/proper bridge for Lemma 16.2. -/
theorem
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction_of_isConvex_isProper
    {α : Type*} [AddCommMonoid α] [Module 𝕜 α] [Preorder α]
    (L : Submodule 𝕜 E) (f : E → WithTopBot α) (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) :
    ((L : Set E) ∩ riDom[𝕜](f)).Nonempty ↔
      ¬ ∃ xStar : Y, xStar ∈ Lᗮₚ ∧
        δᵛ(xStar | dom(f)) ≤ (0 : WithTopBot 𝕜) ∧
          (0 : WithTopBot 𝕜) < δᵛ(-xStar | dom(f)) := by
  exact
    submodule_meets_riDom_iff_no_pairingOrthogonal_asymmetric_supportFunction
      (L := L) (f := f) hf_convex.convex_dom hf_proper.nonempty_dom
