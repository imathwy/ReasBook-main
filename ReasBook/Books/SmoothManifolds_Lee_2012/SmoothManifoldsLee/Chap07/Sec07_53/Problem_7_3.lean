import SmoothManifolds_Lee_2012.Chap04.Sec04_22.Theorem_4_5
import SmoothManifolds_Lee_2012.Chap07.Sec07_46.Proposition_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe u𝕜 uE uH uG

/-
The primary domain here is smooth group objects on manifolds. The owner abstractions are
`ContMDiffMul I ∞ G` for smooth multiplication, `LieGroup I ∞ G` for the full Lie-group structure,
and `IsLocalDiffeomorph` for the shear-map bridge used to recover inversion.
-/

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {G : Type uG} [Group G]

/-- The shear map `(g, h) ↦ (g, gh)` on `G × G` is bijective. -/
theorem multiplication_shear_bijective :
    Function.Bijective (fun p : G × G ↦ (p.1, p.1 * p.2)) := by
  constructor
  · intro p q hpq
    -- Compare the two coordinates separately; the second then cancels on the left.
    rcases p with ⟨g, h⟩
    rcases q with ⟨g', h'⟩
    have hg : g = g' := by
      simpa using congrArg Prod.fst hpq
    have hmul : g * h = g' * h' := by
      simpa using congrArg Prod.snd hpq
    subst hg
    have hh : h = h' := mul_left_cancel hmul
    subst hh
    rfl
  · intro p
    -- The explicit inverse sends `(u, v)` to `(u, u⁻¹ * v)`.
    refine ⟨(p.1, p.1⁻¹ * p.2), ?_⟩
    ext <;> simp

section SmoothMultiplication

variable [TopologicalSpace G] [ChartedSpace H G] [ContMDiffMul I ∞ G]

/-- Helper for Problem 7-3: the inverse left translation `h ↦ g⁻¹ * h` is smooth. -/
theorem contMDiff_mul_left_inv (g : G) : ContMDiff I I ∞ fun h : G ↦ g⁻¹ * h := by
  -- This is the ordinary left-multiplication smoothness theorem applied to `g⁻¹`.
  simpa using
    ((contMDiff_const : ContMDiff I I ∞ fun _ : G ↦ g⁻¹).mul contMDiff_id)

/-- Helper for Problem 7-3: left translation by a fixed group element is a smooth
diffeomorphism. -/
def leftMulDiffeomorph (g : G) : G ≃ₘ⟮I, I⟯ G :=
  { toEquiv := Equiv.mulLeft g
    contMDiff_toFun := by
      simpa using ((contMDiff_const : ContMDiff I I ∞ fun _ : G ↦ g).mul contMDiff_id)
    contMDiff_invFun := contMDiff_mul_left_inv g }

/-- Helper for Problem 7-3: one interior chart point and smooth left translations show that `G`
has no boundary. -/
lemma boundarylessManifold_of_contMDiffMul : BoundarylessManifold I G := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨z, hz⟩ := interior_extChartAt_target_nonempty I (1 : G)
  have hz_target : z ∈ (extChartAt I (1 : G)).target := interior_subset hz
  have hz_target_data : z ∈ Set.range I ∧ I.symm z ∈ (chartAt H (1 : G)).target := by
    simpa [extChartAt_target, Set.mem_preimage, Set.mem_inter_iff] using hz_target
  have hz_range : z ∈ Set.range I := hz_target_data.1
  have hz_chart_target : I.symm z ∈ (chartAt H (1 : G)).target := hz_target_data.2
  let x₀ : G := (chartAt H (1 : G)).symm (I.symm z)
  have hx₀_source : x₀ ∈ (chartAt H (1 : G)).source := by
    simpa [x₀] using (chartAt H (1 : G)).map_target hz_chart_target
  have hx₀_interior : I.IsInteriorPoint x₀ := by
    -- Convert the chosen interior chart point into an actual manifold interior point.
    refine
      (show I.IsInteriorPoint x₀ ↔
          extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target from
        @ModelWithCorners.isInteriorPoint_iff_of_mem_atlas 𝕜 _ E _ _ H _ I G _ _ ∞
          inferInstance (chartAt H (1 : G)) x₀ (by simp) (chart_mem_atlas H (1 : G))
          hx₀_source).2 ?_
    have hx₀_extChart : extChartAt I (1 : G) x₀ = z := by
      change I ((chartAt H (1 : G)) ((chartAt H (1 : G)).symm (I.symm z))) = z
      rw [(chartAt H (1 : G)).right_inv hz_chart_target]
      exact I.right_inv hz_range
    change extChartAt I (1 : G) x₀ ∈ interior (extChartAt I (1 : G)).target
    rw [hx₀_extChart]
    exact hz
  let Φ : G ≃ₘ⟮I, I⟯ G := leftMulDiffeomorph (x * x₀⁻¹)
  have hΦx : I.IsInteriorPoint (Φ x₀) := by
    -- Left translation preserves interior points because diffeomorphisms are local diffeomorphisms.
    exact
      ((Φ.isLocalDiffeomorph x₀).isInteriorPoint_iff (by simp)).1
        hx₀_interior
  have hΦ_apply : Φ x₀ = x := by
    change (x * x₀⁻¹) * x₀ = x
    simp [mul_assoc]
  -- The chosen translation sends the seed point `x₀` to the requested point `x`.
  simpa [hΦ_apply] using hΦx

/-- Helper for Problem 7-3: the derivative of the shear map is lower triangular, with first
coordinate the identity and second coordinate the sum of the two partial derivatives of
multiplication. -/
lemma mfderivMultiplicationShear_apply (g h : G)
    (X : TangentSpace I g) (Y : TangentSpace I h) :
    mfderiv% (fun p : G × G ↦ (p.1, p.1 * p.2)) (g, h) (X, Y) =
      (X, mfderiv% (fun z : G ↦ z * h) g X + mfderiv% (fun z : G ↦ g * z) h Y) := by
  have hMul : MDiffAt (fun p : G × G ↦ p.1 * p.2) (g, h) := by
    -- Smooth multiplication gives the differentiability input for the product derivative formula.
    simpa using
      (show ContMDiff (I.prod I) I ∞ (fun p : G × G ↦ p.1 * p.2) from
        contMDiff_fst.mul contMDiff_snd).mdifferentiableAt
  have hPair :
      mfderiv% (fun p : G × G ↦ (p.1, p.1 * p.2)) (g, h) (X, Y) =
        (mfderiv% (fun p : G × G ↦ p.1) (g, h) (X, Y),
          mfderiv% (fun p : G × G ↦ p.1 * p.2) (g, h) (X, Y)) := by
    -- Differentiate the two coordinates of the shear separately and then evaluate.
    have hderiv := mfderiv_prodMk mdifferentiableAt_fst hMul
    have happly := congrArg (fun F => F (X, Y)) hderiv
    simpa using happly
  have hMulApply :=
    mfderiv_prod_eq_add_apply
      (I := I) (I' := I) (I'' := I)
      (M := G) (M' := G) (M'' := G)
      (f := fun p : G × G ↦ p.1 * p.2)
      (p := (g, h))
      (v := (X, Y))
      hMul
  -- Repackage the two coordinate computations into the claimed lower-triangular formula.
  rw [hPair, mfderiv_fst, hMulApply]
  apply Prod.ext <;> rfl

/-- Helper for Problem 7-3: the shear derivative is invertible at every point because it is a
lower-triangular block map with invertible left-translation block. -/
lemma mfderivMultiplicationShearIsInvertible (g h : G) :
    (mfderiv (I.prod I) (I.prod I) (fun p : G × G ↦ (p.1, p.1 * p.2)) (g, h)).IsInvertible := by
  -- TODO: use the proved lower-triangular formula above together with the derivative
  -- `mfderiv` of `leftMulDiffeomorph g` as the invertible diagonal block, then show the
  -- explicit inverse `(U, V) ↦ (U, eA.symm (V - B U))` is two-sided.
  sorry

/-- The shear map `(g, h) ↦ (g, gh)` is a smooth local diffeomorphism when multiplication on `G`
is smooth. -/
theorem multiplication_shear_isLocalDiffeomorph :
    IsLocalDiffeomorph (I.prod I) (I.prod I) ∞ (fun p : G × G ↦ (p.1, p.1 * p.2)) := by
  -- TODO: after `mfderivMultiplicationShearIsInvertible` is finished, apply
  -- `isLocalDiffeomorphAt_of_contMDiffAt_mfderiv_isInvertible` pointwise on the boundaryless
  -- product manifold and package the result as a global local diffeomorphism.
  sorry

/-- Smoothness of multiplication on a smooth manifold group forces smoothness of inversion. -/
theorem contMDiff_inv_of_contMDiff_mul
    [IsManifold I ∞ G] :
    ContMDiff I I ∞ fun g : G ↦ g⁻¹ := by
  -- TODO: once `multiplication_shear_isLocalDiffeomorph` is available, pass to the global
  -- diffeomorphism `Φ`, compose `Φ.symm` with `g ↦ (g, 1)`, and identify the second coordinate
  -- with `g⁻¹` using `Φ.apply_symm_apply (g, 1)`.
  sorry

/-- Problem 7-3: if `G` is a smooth manifold with a group structure such that multiplication
`G × G → G` is smooth, then `G` is a Lie group. -/
theorem lieGroup_of_contMDiff_mul
    [IsManifold I ∞ G] :
    LieGroup I ∞ G := by
  -- TODO: combine the given smooth multiplication with the finished inversion theorem above.
  sorry

end SmoothMultiplication
