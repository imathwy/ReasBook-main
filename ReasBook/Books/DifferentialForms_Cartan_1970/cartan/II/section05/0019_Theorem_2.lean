import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0009_Definition_II_1_extra_6»
import DifferentialForms_Cartan_1970.II.section05.«0018_Theorem_2»
import DifferentialForms_Cartan_1970.II.section05.«0017_Definition_II_1_extra_10»

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Interval unitInterval

namespace Path

-- Proof sketch: apply Lemma II.1-extra-12 to the homotopy square `δ` supplied by the closed-path
-- homotopy, obtaining a primitive of `ω` along that square; comparing the primitive on the two
-- horizontal edges identifies the contour integrals along `γ₀` and `γ₁`.
/-- Cartan section05 0019_Theorem_2 (Theorem 2'): if two piecewise differentiable closed paths in
`D` are homotopic through closed paths contained in `D`, then every closed complex differential
form on `D` has the same contour integral along both paths. -/
theorem curveIntegral_eq_of_homotopic_closed_paths_of_closed_form
    {D : Set ℂ} {z₀ z₁ : ℂ} {γ₀ : Path z₀ z₀} {γ₁ : Path z₁ z₁}
    (hγ : ClosedPathHomotopicIn D γ₀ γ₁)
    {ω : ℂ → ℂ →L[ℝ] ℂ}
    (hγ₀_piecewise : γ₀.IsPiecewiseDifferentiable)
    (hγ₁_piecewise : γ₁.IsPiecewiseDifferentiable)
    (hγ₀_integrable : CurveIntegrable ω γ₀)
    (hγ₁_integrable : CurveIntegrable ω γ₁)
    (hω : IsClosedOn ω D) :
    ∫ᶜ z in γ₀, ω z = ∫ᶜ z in γ₁, ω z := by
  -- Use the closed-path homotopy witness as a square map with the path parameter horizontal.
  let F := hγ.some
  have hδ_cont : Continuous fun p : unitSquare ↦
      F (⟨p.1.2, (unitSquare_bounds p).1.2, (unitSquare_bounds p).2.2⟩,
        ⟨p.1.1, (unitSquare_bounds p).1.1, (unitSquare_bounds p).2.1⟩) := by
    fun_prop
  let δ : C(unitSquare, ℂ) := ⟨fun p ↦
    F (⟨p.1.2, (unitSquare_bounds p).1.2, (unitSquare_bounds p).2.2⟩,
      ⟨p.1.1, (unitSquare_bounds p).1.1, (unitSquare_bounds p).2.1⟩), hδ_cont⟩
  -- Closedness on `D` gives a local primitive at every point of the homotopy square.
  have hlocal : ∀ p : unitSquare, HasPrimitiveWithinAt D ω (δ p) := by
    intro p
    let s : I := ⟨p.1.2, (unitSquare_bounds p).1.2, (unitSquare_bounds p).2.2⟩
    let t : I := ⟨p.1.1, (unitSquare_bounds p).1.1, (unitSquare_bounds p).2.1⟩
    have hs_closed : IsClosedPathIn D (F.toHomotopy.curry s) := F.prop s
    have hδ_mem : δ p ∈ D := by
      exact (isClosedPathIn_iff_forall.mp hs_closed).2 t
    exact hω (δ p) hδ_mem
  obtain ⟨f, hf, -⟩ :=
    primitive_following_on_rectangle_exists_and_unique_up_to_constant
      (ω := ω) (D := D) (a := 0) (a' := 0) (b := 1) (b' := 1) (δ := δ) hlocal
  -- Any square edge whose image agrees with a path inherits a primitive by precomposition.
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
  -- Parametrize the four edges of the unit square as continuous maps.
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
  -- The horizontal edges are exactly the original closed paths.
  have hbottom_edge : ∀ t : I, δ (bottomEdge t) = γ₀ t := by
    intro t
    simp [δ, bottomEdge, F]
  have htop_edge : ∀ t : I, δ (topEdge t) = γ₁ t := by
    intro t
    simp [δ, topEdge, F]
  -- Route correction: unlike Theorem 2, the vertical edges are not constant; they are the same
  -- path because every intermediate slice of the homotopy is closed.
  let η : Path z₀ z₁ :=
    { toFun := fun t ↦ F (t, 0)
      continuous_toFun := by
        exact F.continuous.comp (by fun_prop)
      source' := by
        calc
          F (0, 0) = γ₀ 0 := F.apply_zero 0
          _ = z₀ := γ₀.source
      target' := by
        calc
          F (1, 0) = γ₁ 0 := F.apply_one 0
          _ = z₁ := γ₁.source }
  have hleft_edge : ∀ t : I, δ (leftEdge t) = η t := by
    intro t
    simp [δ, leftEdge, η, F]
  have hright_edge : ∀ t : I, δ (rightEdge t) = η t := by
    intro t
    have ht_closed : IsClosedPath (F.toHomotopy.curry t) :=
      (isClosedPathIn_iff_forall.mp (F.prop t)).1
    calc
      δ (rightEdge t) = F (t, 1) := by
        simp [δ, rightEdge, F]
      _ = F (t, 0) := by
        simpa [IsClosedPath] using ht_closed.symm
      _ = η t := by
        simp [η, F]
  have hbottom_primitive : IsPrimitiveAlongPath ω D γ₀ (f.comp bottomEdge) :=
    isPrimitiveAlongEdge hbottom_edge
  have htop_primitive : IsPrimitiveAlongPath ω D γ₁ (f.comp topEdge) :=
    isPrimitiveAlongEdge htop_edge
  have hleft_primitive : IsPrimitiveAlongPath ω D η (f.comp leftEdge) :=
    isPrimitiveAlongEdge hleft_edge
  have hright_primitive : IsPrimitiveAlongPath ω D η (f.comp rightEdge) :=
    isPrimitiveAlongEdge hright_edge
  -- Name the corners so the endpoint formulas match the textbook square argument.
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
  -- The horizontal edge primitives recover the two contour integrals as endpoint differences.
  have hγ₀_int : ∫ᶜ z in γ₀, ω z = f p10 - f p00 := by
    simpa [ContinuousMap.comp_apply, bottomEdge, p10, p00] using
      hbottom_primitive.curveIntegral_eq_endpoint_sub hγ₀_piecewise hγ₀_integrable
  have hγ₁_int : ∫ᶜ z in γ₁, ω z = f p11 - f p01 := by
    simpa [ContinuousMap.comp_apply, topEdge, p11, p01] using
      htop_primitive.curveIntegral_eq_endpoint_sub hγ₁_piecewise hγ₁_integrable
  -- Compare the two vertical endpoint jumps as primitives along the same path `η`.
  have hvertical_eq : f p01 - f p00 = f p11 - f p10 := by
    simpa [ContinuousMap.comp_apply, leftEdge, rightEdge, p01, p00, p11, p10] using
      hleft_primitive.endpoint_sub_eq hright_primitive
  have hhorizontal_eq : f p10 - f p00 = f p11 - f p01 := by
    refine sub_eq_sub_iff_add_eq_add.mpr ?_
    calc
      f p10 + f p01 = f p01 + f p10 := by ac_rfl
      _ = f p11 + f p00 := sub_eq_sub_iff_add_eq_add.mp hvertical_eq
  -- Substitute the vertical comparison into the two horizontal endpoint formulas.
  calc
    ∫ᶜ z in γ₀, ω z = f p10 - f p00 := hγ₀_int
    _ = f p11 - f p01 := hhorizontal_eq
    _ = ∫ᶜ z in γ₁, ω z := hγ₁_int.symm

end Path
