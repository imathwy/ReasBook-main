import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0014_Remark_II_1_extra_8»
import DifferentialForms_Cartan_1970.II.section05.«0021_Lemma_II_1_extra_12»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Interval unitInterval

namespace Path

/-- Helper for Cartan section05 0018_Theorem_2: the closed unit square as the rectangle with
corners `(0,0)` and `(1,1)`. -/
abbrev unitSquare : Type := [[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]]

/-- Helper for Cartan section05 0018_Theorem_2: a point of the unit square has both coordinates in
the unit interval. -/
theorem unitSquare_bounds (p : unitSquare) :
    (0 ≤ p.1.1 ∧ 0 ≤ p.1.2) ∧ p.1.1 ≤ 1 ∧ p.1.2 ≤ 1 := by
  simpa [Set.mem_Icc, Prod.le_def] using p.2

-- Proof sketch: let `F : γ₀.Homotopy γ₁` be a homotopy whose image lies in `D`. Apply
-- `primitive_following_on_rectangle_exists_and_unique_up_to_constant` to the square map
-- `(s, t) ↦ F (t, s)` using the local primitives supplied by `hω`. The resulting primitive on the
-- square is constant on the vertical sides because the endpoints are fixed, so the endpoint
-- difference formula along the two horizontal sides gives equal integrals for `γ₀` and `γ₁`.
/-- Cartan section05 0018_Theorem_2 (Theorem 2): if two paths with the same endpoints are joined
by a homotopy whose image stays in `D`, then every closed form on `D` has the same integral along
both piecewise differentiable paths. -/
theorem curveIntegral_eq_of_homotopy_in_domain
    {D : Set ℂ} {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hω : IsClosedOn ω D)
    {z₀ z₁ : ℂ} {γ₀ γ₁ : Path z₀ z₁}
    (hγ₀_piecewise : γ₀.IsPiecewiseDifferentiable)
    (hγ₁_piecewise : γ₁.IsPiecewiseDifferentiable)
    (hγ₀_integrable : CurveIntegrable ω γ₀)
    (hγ₁_integrable : CurveIntegrable ω γ₁)
    (F : γ₀.Homotopy γ₁) (hF : Set.range F ⊆ D) :
    ∫ᶜ z in γ₀, ω z = ∫ᶜ z in γ₁, ω z := by
  -- Turn the homotopy into a square map whose horizontal edges are `γ₀` and `γ₁`.
  have hδ_cont : Continuous fun p : unitSquare ↦
      F (⟨p.1.2, (unitSquare_bounds p).1.2, (unitSquare_bounds p).2.2⟩,
        ⟨p.1.1, (unitSquare_bounds p).1.1, (unitSquare_bounds p).2.1⟩) := by
    fun_prop
  let δ : C(unitSquare, ℂ) := ⟨fun p ↦
    F (⟨p.1.2, (unitSquare_bounds p).1.2, (unitSquare_bounds p).2.2⟩,
      ⟨p.1.1, (unitSquare_bounds p).1.1, (unitSquare_bounds p).2.1⟩), hδ_cont⟩
  -- Closedness gives a local primitive at every point of the square image.
  have hlocal : ∀ p : unitSquare, HasPrimitiveWithinAt D ω (δ p) := by
    intro p
    apply hω
    exact hF ⟨((⟨p.1.2, (unitSquare_bounds p).1.2, (unitSquare_bounds p).2.2⟩ : I),
      (⟨p.1.1, (unitSquare_bounds p).1.1, (unitSquare_bounds p).2.1⟩ : I)), rfl⟩
  obtain ⟨f, hf, -⟩ :=
    primitive_following_on_rectangle_exists_and_unique_up_to_constant
      (ω := ω) (D := D) (a := 0) (a' := 0) (b := 1) (b' := 1) (δ := δ) hlocal
  -- Restrict the rectangle primitive to any edge whose image agrees with a path.
  have isPrimitiveAlongEdge
      {x y : ℂ} {γ : Path x y} {e : C(I, unitSquare)}
      (hedge : ∀ t : I, δ (e t) = γ t) :
      IsPrimitiveAlongPath ω D γ (f.comp e) := by
    intro τ
    rcases hf (e τ) with
      ⟨s, hs_open, hs_mem, U, hU_open, hδU, hUD, hmaps, primitive, hprimitive, hEq⟩
    refine ⟨e ⁻¹' s, hs_open.preimage e.continuous, hs_mem, U, hU_open, ?_, hUD, ?_,
      primitive, hprimitive, ?_⟩
    · simpa [hedge τ] using hδU
    · intro t ht
      simpa [hedge t] using hmaps ht
    · intro t ht
      have hEqt := hEq ht
      simpa [ContinuousMap.comp_apply, hedge t] using hEqt
  -- Build the four edge embeddings of the square as continuous maps.
  have hbottom_mem :
      ∀ t : I, (((t : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈
        ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    intro t
    simp [t.2.1, t.2.2]
  have htop_mem :
      ∀ t : I, (((t : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈
        ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    intro t
    simp [t.2.1, t.2.2]
  have hleft_mem :
      ∀ t : I, (((0 : ℝ), (t : ℝ)) : ℝ × ℝ) ∈
        ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    intro t
    simp [t.2.1, t.2.2]
  have hright_mem :
      ∀ t : I, (((1 : ℝ), (t : ℝ)) : ℝ × ℝ) ∈
        ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    intro t
    simp [t.2.1, t.2.2]
  have hbottom_cont :
      Continuous fun t : I ↦ (⟨((t : ℝ), (0 : ℝ)), hbottom_mem t⟩ : unitSquare) := by
    fun_prop
  have htop_cont :
      Continuous fun t : I ↦ (⟨((t : ℝ), (1 : ℝ)), htop_mem t⟩ : unitSquare) := by
    fun_prop
  have hleft_cont :
      Continuous fun t : I ↦ (⟨((0 : ℝ), (t : ℝ)), hleft_mem t⟩ : unitSquare) := by
    fun_prop
  have hright_cont :
      Continuous fun t : I ↦ (⟨((1 : ℝ), (t : ℝ)), hright_mem t⟩ : unitSquare) := by
    fun_prop
  let bottomEdge : C(I, unitSquare) := ⟨fun t ↦ ⟨((t : ℝ), (0 : ℝ)), hbottom_mem t⟩, hbottom_cont⟩
  let topEdge : C(I, unitSquare) := ⟨fun t ↦ ⟨((t : ℝ), (1 : ℝ)), htop_mem t⟩, htop_cont⟩
  let leftEdge : C(I, unitSquare) := ⟨fun t ↦ ⟨((0 : ℝ), (t : ℝ)), hleft_mem t⟩, hleft_cont⟩
  let rightEdge : C(I, unitSquare) := ⟨fun t ↦ ⟨((1 : ℝ), (t : ℝ)), hright_mem t⟩, hright_cont⟩
  -- The swapped square map identifies the four edges with the two given paths and two constants.
  have hbottom_edge : ∀ t : I, δ (bottomEdge t) = γ₀ t := by
    intro t
    simp [δ, bottomEdge]
  have htop_edge : ∀ t : I, δ (topEdge t) = γ₁ t := by
    intro t
    simp [δ, topEdge]
  have hleft_edge : ∀ t : I, δ (leftEdge t) = Path.refl z₀ t := by
    intro t
    simp [δ, leftEdge]
  have hright_edge : ∀ t : I, δ (rightEdge t) = Path.refl z₁ t := by
    intro t
    simp [δ, rightEdge]
  have hbottom_primitive : IsPrimitiveAlongPath ω D γ₀ (f.comp bottomEdge) :=
    isPrimitiveAlongEdge hbottom_edge
  have htop_primitive : IsPrimitiveAlongPath ω D γ₁ (f.comp topEdge) :=
    isPrimitiveAlongEdge htop_edge
  have hleft_primitive : IsPrimitiveAlongPath ω D (Path.refl z₀) (f.comp leftEdge) :=
    isPrimitiveAlongEdge hleft_edge
  have hright_primitive : IsPrimitiveAlongPath ω D (Path.refl z₁) (f.comp rightEdge) :=
    isPrimitiveAlongEdge hright_edge
  -- Name the four corners so the endpoint formulas read like the textbook proof.
  have hp00_mem : (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈
      ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    simp
  have hp10_mem : (((1 : ℝ), (0 : ℝ)) : ℝ × ℝ) ∈
      ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    simp
  have hp01_mem : (((0 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈
      ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    simp
  have hp11_mem : (((1 : ℝ), (1 : ℝ)) : ℝ × ℝ) ∈
      ([[((0 : ℝ), (0 : ℝ)), ((1 : ℝ), (1 : ℝ))]] : Set (ℝ × ℝ)) := by
    simp
  let p00 : unitSquare := ⟨((0 : ℝ), (0 : ℝ)), hp00_mem⟩
  let p10 : unitSquare := ⟨((1 : ℝ), (0 : ℝ)), hp10_mem⟩
  let p01 : unitSquare := ⟨((0 : ℝ), (1 : ℝ)), hp01_mem⟩
  let p11 : unitSquare := ⟨((1 : ℝ), (1 : ℝ)), hp11_mem⟩
  -- The horizontal edges recover the two curve integrals as endpoint differences of `f`.
  have hγ₀_int : ∫ᶜ z in γ₀, ω z = f p10 - f p00 := by
    simpa [ContinuousMap.comp_apply, bottomEdge, p10, p00] using
      hbottom_primitive.curveIntegral_eq_endpoint_sub hγ₀_piecewise hγ₀_integrable
  have hγ₁_int : ∫ᶜ z in γ₁, ω z = f p11 - f p01 := by
    simpa [ContinuousMap.comp_apply, topEdge, p11, p01] using
      htop_primitive.curveIntegral_eq_endpoint_sub hγ₁_piecewise hγ₁_integrable
  -- The vertical edges are constant, so their endpoint differences vanish.
  have hleft_zero : f p01 - f p00 = 0 := by
    calc
      f p01 - f p00 = ∫ᶜ z in Path.refl z₀, ω z := by
        symm
        simpa [ContinuousMap.comp_apply, leftEdge, p01, p00] using
          hleft_primitive.curveIntegral_eq_endpoint_sub (Path.isPiecewiseDifferentiable_refl z₀)
            (CurveIntegrable.refl ω z₀)
      _ = 0 := by
        rw [curveIntegral_refl]
  have hright_zero : f p11 - f p10 = 0 := by
    calc
      f p11 - f p10 = ∫ᶜ z in Path.refl z₁, ω z := by
        symm
        simpa [ContinuousMap.comp_apply, rightEdge, p11, p10] using
          hright_primitive.curveIntegral_eq_endpoint_sub (Path.isPiecewiseDifferentiable_refl z₁)
            (CurveIntegrable.refl ω z₁)
      _ = 0 := by
        rw [curveIntegral_refl]
  have hleft_eq : f p01 = f p00 := sub_eq_zero.mp hleft_zero
  have hright_eq : f p11 = f p10 := sub_eq_zero.mp hright_zero
  -- Substitute the two vanishing vertical jumps into the horizontal endpoint formulas.
  calc
    ∫ᶜ z in γ₀, ω z = f p10 - f p00 := hγ₀_int
    _ = f p11 - f p01 := by
      rw [hright_eq, hleft_eq]
    _ = ∫ᶜ z in γ₁, ω z := hγ₁_int.symm

end Path
