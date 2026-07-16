import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap02.Sec02_12.Problem_2_7
import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap08.Sec08_54.Lemma_8_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local notation "SmoothVectorField" => Cₛ^∞⟮I; E, fun p : M ↦ TangentSpace I p⟯

-- Domain sampling for this item:
-- * core/canonical owner: mathlib's bundled smooth-section type `Cₛ^∞⟮I; E, TangentSpace I⟯`;
-- * bridge/view in the chapter: `smooth_vector_fields`, the rough-section submodule presentation
--   from `Example_8_36`.
-- This theorem is source-facing, but its public owner should be the canonical bundled smooth
-- section space. The submodule presentation is only a downstream bridge, and the ambient manifold
-- hypotheses match the Chapter 2 and Chapter 8 global existence results used to justify the
-- infinite-dimensionality statement.

/-- Helper for Problem 8-3: a supported smooth vector field must vanish outside the open set
containing the closure of its nonvanishing locus. -/
lemma smoothVectorField_eq_zero_of_not_mem_supportSubset
    {U : Set M} {X : SmoothVectorField} {x : M}
    (hSupp : closure {y : M | X y ≠ 0} ⊆ U) (hx : x ∉ U) :
    X x = 0 := by
  -- Any nonzero value would put `x` into the support set, hence into its closure.
  by_contra hX
  exact hx (hSupp (subset_closure hX))

/-- Helper for Problem 8-3: a tangent vector at `p` extends to a smooth global vector field whose
nonvanishing locus has closure contained in a prescribed open neighborhood of `p`. -/
lemma existsSupportedSmoothVectorField_eqAtPoint_of_memOpen
    {U : Set M} {p : M} (hU : IsOpen U) (hpU : p ∈ U) (v : TangentSpace I p) :
    ∃ X : SmoothVectorField, X p = v ∧ closure {x : M | X x ≠ 0} ⊆ U := by
  let Xsource : ∀ x : ({p} : Set M), TangentSpace I (x : M) := fun _ ↦ v
  have hlocal : ∀ x : ({p} : Set M), ContMDiffVectorFieldLocalExtension Xsource x := by
    intro x
    classical
    let V :=
      Classical.choose <| FiberBundle.exists_contMDiffOn_extend
        (I := I) (F := E) (V := TangentSpace I) (k := (∞ : ℕ∞ω)) (σ₀ := Xsource x)
    have hV_nhds : V ∈ nhds (x : M) := by
      exact (Classical.choose_spec <|
        FiberBundle.exists_contMDiffOn_extend
          (I := I) (F := E) (V := TangentSpace I) (k := (∞ : ℕ∞ω)) (σ₀ := Xsource x)).1
    have hV_smooth :
        ContMDiffOn I I.tangent (∞ : ℕ∞ω) (T% (FiberBundle.extend E (Xsource x))) V := by
      exact (Classical.choose_spec <|
        FiberBundle.exists_contMDiffOn_extend
          (I := I) (F := E) (V := TangentSpace I) (k := (∞ : ℕ∞ω)) (σ₀ := Xsource x)).2
    let W := Classical.choose <| mem_nhds_iff.mp hV_nhds
    have hW_sub : W ⊆ V := by
      exact (Classical.choose_spec <| mem_nhds_iff.mp hV_nhds).1
    have hW_open : IsOpen W := by
      exact (Classical.choose_spec <| mem_nhds_iff.mp hV_nhds).2.1
    have hxW : (x : M) ∈ W := by
      exact (Classical.choose_spec <| mem_nhds_iff.mp hV_nhds).2.2
    -- Use the bundle-local extension around `x`, then shrink to an open neighborhood.
    refine
      { V := W
        isOpen_V := hW_open
        mem_V := hxW
        Xloc := FiberBundle.extend E (Xsource x)
        contMDiffOn := hV_smooth.mono hW_sub
        eq_source := ?_ }
    intro y hy
    have hy_base : (y : M) = p := Set.mem_singleton_iff.mp y.2
    have hx_base : (x : M) = p := Set.mem_singleton_iff.mp x.2
    have hxy_base : (y : M) = (x : M) := hy_base.trans hx_base.symm
    have hxy : y = x := Subtype.ext hxy_base
    subst hxy
    simpa [Xsource] using FiberBundle.extend_apply_self (F := E) (v := Xsource x)
  obtain ⟨Ytilde, hYtilde⟩ :=
    exists_supported_contMDiff_vectorField_extension_of_isClosed
      (I := I) (A := ({p} : Set M)) (U := U) isClosed_singleton hU
      (by
        intro x hx
        simpa [Set.mem_singleton_iff.mp hx] using hpU)
      Xsource hlocal
  refine ⟨⟨Ytilde, hYtilde.contMDiff⟩, ?_, ?_⟩
  · -- Compare the supported extension back to the original field value at `p`.
    simpa [Xsource] using hYtilde.eq_source ⟨p, by simp⟩
  · simpa using hYtilde.support_subset

/-- Helper for Problem 8-3: a positive-dimensional smooth manifold contains arbitrarily large
finite linearly independent families of smooth vector fields. -/
lemma existsLinearlyIndependentSmoothVectorFieldFamily
    (p : M) (n : ℕ) (hn : 0 < n) (hpos : 0 < Module.finrank ℝ E) :
    ∃ X : Fin n → SmoothVectorField, LinearIndependent ℝ X := by
  classical
  obtain ⟨c, ρ, hρ, hc, hball, hdisj⟩ :=
    exists_pairwise_disjoint_chart_balls (I := I) p n hn hpos
  obtain ⟨e, he⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  let q : Fin n → M := fun i ↦ (extChartAt I p).symm (c i)
  let U : Fin n → Set M := fun i ↦
    (extChartAt I p).source ∩ (extChartAt I p) ⁻¹' Metric.ball (c i) ρ
  have hq_mem : ∀ i, q i ∈ U i := by
    intro i
    refine ⟨(extChartAt I p).map_target (hc i), ?_⟩
    change extChartAt I p ((extChartAt I p).symm (c i)) ∈ Metric.ball (c i) ρ
    rw [(extChartAt I p).right_inv (hc i)]
    exact Metric.mem_ball_self hρ
  have hU_open : ∀ i, IsOpen (U i) := by
    intro i
    simpa [U] using isOpen_extChartAt_preimage (I := I) p Metric.isOpen_ball
  have hq_not_mem : ∀ ⦃i j : Fin n⦄, i ≠ j → q i ∉ U j := by
    intro i j hij hqj
    -- Distinct chart balls are disjoint, so `q i` cannot belong to `U j`.
    exact (hdisj hij).le_bot ⟨(hq_mem i).2, hqj.2⟩
  have hX :
      ∀ i, ∃ X : SmoothVectorField, X (q i) = (e : TangentSpace I (q i)) ∧
        closure {x : M | X x ≠ 0} ⊆ U i := by
    intro i
    exact existsSupportedSmoothVectorField_eqAtPoint_of_memOpen
      (I := I) (hU_open i) (hq_mem i) (e : TangentSpace I (q i))
  choose X hXq hXsupp using hX
  let evalAtChosenPoints : SmoothVectorField →ₗ[ℝ] Fin n → E :=
    { toFun := fun Y i ↦ Y (q i)
      map_add' := by
        intro Y Z
        ext i
        rfl
      map_smul' := by
        intro a Y
        ext i
        rfl }
  have hEval_image : ∀ i, evalAtChosenPoints (X i) = Pi.single i e := by
    intro i
    ext j
    by_cases hji : j = i
    · subst j
      simpa [evalAtChosenPoints] using hXq i
    · have hzero : X i (q j) = 0 :=
        smoothVectorField_eq_zero_of_not_mem_supportSubset
          (I := I) (X := X i) (U := U i) (x := q j) (hXsupp i) (hq_not_mem hji)
      rw [show evalAtChosenPoints (X i) j = X i (q j) by rfl, hzero]
      have hsingle_zero : (Pi.single i e : Fin n → E) j = 0 := by
        simp [Pi.single_apply, hji]
      simpa using hsingle_zero.symm
  have hsingle :
      LinearIndependent ℝ (fun i : Fin n ↦ (Pi.single i e : Fin n → E)) := by
    have hsingle' :
        LinearIndependent ℝ (fun i : Fin n ↦ (Finsupp.single i e : Fin n →₀ E)) :=
      Finsupp.linearIndependent_single_of_ne_zero (v := fun _ : Fin n ↦ e) (by
        intro i
        exact he)
    have hsingle_fun :
        LinearIndependent ℝ
          (fun i : Fin n ↦
            (Finsupp.linearEquivFunOnFinite ℝ E (Fin n)) (Finsupp.single i e)) := by
      exact hsingle'.map' (Finsupp.linearEquivFunOnFinite ℝ E (Fin n)).toLinearMap (by simp)
    convert hsingle_fun using 1
    funext i
    simpa using Finsupp.linearEquivFunOnFinite_single (R := ℝ) (M := E) (α := Fin n) i e
  refine ⟨X, ?_⟩
  -- Route correction: instead of a direct sum chase, send the family to its values on the chosen
  -- points, where it becomes the standard coordinate family `Pi.single i e`.
  have hEval_li : LinearIndependent ℝ (evalAtChosenPoints ∘ X) := by
    convert hsingle using 1
    funext i
    exact hEval_image i
  exact LinearIndependent.of_comp evalAtChosenPoints hEval_li

/-- Problem 8-3: if `M` is a nonempty positive-dimensional smooth manifold, with or without
boundary, then the real vector space of smooth vector fields on `M` is not finite-dimensional. -/
theorem smoothVectorField_not_finiteDimensional
    (hM : Nonempty M) (hpos : 0 < Module.finrank ℝ E) :
    ¬ FiniteDimensional ℝ SmoothVectorField := by
  intro hfd
  letI := hfd
  let n := Module.finrank ℝ SmoothVectorField + 1
  have hn : 0 < n := Nat.succ_pos _
  obtain ⟨p⟩ := hM
  -- Build one more linearly independent vector field than the claimed finite dimension allows.
  obtain ⟨X, hX⟩ := existsLinearlyIndependentSmoothVectorFieldFamily
    (I := I) p n hn hpos
  have hcard :
      Fintype.card (Fin n) ≤ Module.finrank ℝ SmoothVectorField :=
    LinearIndependent.fintype_card_le_finrank hX
  -- `Fin n` has cardinality `finrank + 1`, contradicting the dimension bound.
  simpa [n] using hcard

end
