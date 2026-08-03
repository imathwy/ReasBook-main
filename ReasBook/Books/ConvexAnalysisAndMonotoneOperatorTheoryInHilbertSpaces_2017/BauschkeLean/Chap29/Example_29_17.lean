import BauschkeLean.Chap03.Proposition_3_19
import BauschkeLean.Chap03.Proposition_3_30
import BauschkeLean.Chap03.Corollary_3_32

open ContinuousLinearMap
open scoped ContinuousLinearMap InnerProductSpace Pointwise

universe u v

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The affine fiber of a continuous linear map at `y`, viewed canonically as the preimage of
the singleton `{y}`. -/
abbrev affineFiber (L : H →L[ℝ] K) (y : K) : Set H :=
  L ⁻¹' {y}

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem mem_affineFiber {L : H →L[ℝ] K} {y : K} {x : H} :
    x ∈ affineFiber L y ↔ L x = y :=
  Iff.rfl

omit [CompleteSpace H] [CompleteSpace K] in
/-- A fiber `affineFiber L y` is nonempty exactly when `y` lies in `range L`. -/
@[simp] theorem affineFiber_nonempty_iff {L : H →L[ℝ] K} {y : K} :
    (affineFiber L y).Nonempty ↔ y ∈ L.range := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, mem_affineFiber.mp hx⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, by simp [affineFiber]⟩

omit [CompleteSpace H] [CompleteSpace K] in
/-- Every affine fiber of a continuous linear map is closed. -/
theorem affineFiber_isClosed (L : H →L[ℝ] K) (y : K) :
    IsClosed (affineFiber L y) := by
  simpa [affineFiber] using isClosed_singleton.preimage L.continuous

omit [CompleteSpace H] [CompleteSpace K] in
/-- Every affine fiber of a continuous linear map is convex. -/
theorem affineFiber_convex (L : H →L[ℝ] K) (y : K) :
    Convex ℝ (affineFiber L y) := by
  intro x hx z hz a b ha hb hab
  rw [mem_affineFiber] at hx hz ⊢
  calc
    L (a • x + b • z) = a • L x + b • L z := by simp
    _ = a • y + b • y := by rw [hx, hz]
    _ = y := by rw [← add_smul, hab, one_smul]

omit [CompleteSpace K] in
/-- Every nonempty affine fiber of a continuous linear map between Hilbert spaces is Chebyshev. -/
theorem affineFiber_isChebyshev {L : H →L[ℝ] K} {y : K}
    (hy : (affineFiber L y).Nonempty) :
    IsChebyshev (affineFiber L y) :=
  isChebyshev_of_nonempty_isClosed_convex
    hy
    (affineFiber_isClosed L y)
    (affineFiber_convex L y)

omit [CompleteSpace K] in
/-- The metric projection onto a nonempty affine fiber. -/
noncomputable abbrev affineFiberProjection (L : H →L[ℝ] K) (y : K)
    (hy : (affineFiber L y).Nonempty) : H → H :=
  P[affineFiber L y, affineFiber_isChebyshev hy]

omit [CompleteSpace K] in
/-- Membership in an affine fiber supplies the nonemptiness needed for its metric projection. -/
theorem affineFiber_isChebyshev_of_mem {L : H →L[ℝ] K} {y : K} {z : H}
    (hz : z ∈ affineFiber L y) :
    IsChebyshev (affineFiber L y) :=
  affineFiber_isChebyshev ⟨z, hz⟩

/-- If `L ∘L L.adjoint` is invertible, then every affine fiber of `L` is nonempty. -/
theorem affineFiber_nonempty_of_isUnit_comp_adjoint (L : H →L[ℝ] K)
    [Fact (IsUnit (L ∘L L.adjoint))] (y : K) :
    (affineFiber L y).Nonempty := by
  refine ⟨L.adjoint ((L ∘L L.adjoint).inverse y), ?_⟩
  rw [mem_affineFiber]
  have hcancel :
      (L ∘L L.adjoint) ((L ∘L L.adjoint).inverse y) = y := by
    simpa [← ringInverse_eq_inverse, one_def] using
      congrArg (fun A : K →L[ℝ] K ↦ A y)
        (Ring.mul_inverse_cancel (L ∘L L.adjoint) (Fact.out : IsUnit (L ∘L L.adjoint)))
  simpa using hcancel

/-- A continuous linear map has closed range when its range is closed as a subset. -/
abbrev HasClosedRange (L : H →L[ℝ] K) : Prop :=
  IsClosed (L.range : Set K)

omit [CompleteSpace H] [CompleteSpace K] in
@[simp] theorem hasClosedRange_iff {L : H →L[ℝ] K} :
    HasClosedRange L ↔ IsClosed (L.range : Set K) :=
  Iff.rfl

section

variable {L : H →L[ℝ] K} {y : K}

/-- Helper for Example 29.17: a nonempty fiber of `L` is the translate of `ker L` by any point
it contains. -/
lemma affineFiber_eq_vadd_ker_of_mem {z : H} (hz : z ∈ affineFiber L y) :
    affineFiber L y = z +ᵥ (L.ker : Set H) := by
  ext x
  rw [Set.mem_vadd_set, mem_affineFiber]
  constructor
  · intro hx
    refine ⟨x - z, ?_, by simp [vadd_eq_add]⟩
    change L (x - z) = 0
    -- Rewrite the fiber condition into the kernel condition for `x - z`.
    calc
      L (x - z) = L x - L z := by simp
      _ = y - y := by rw [hx, mem_affineFiber.mp hz]
      _ = 0 := by simp
  · rintro ⟨u, hu, rfl⟩
    change L u = 0 at hu
    -- A translated kernel vector stays in the same fiber.
    calc
      L (z +ᵥ u) = L z + L u := by simp [vadd_eq_add]
      _ = y + 0 := by rw [mem_affineFiber.mp hz, hu]
      _ = y := by simp

/-- Helper for Example 29.17: the metric projection onto `ker L` is
`u - (L⁺[hL_closed]) (L u)`. -/
lemma projectionPoint_ker_eq_sub_moorePenroseInverseOperator_apply
    (hL_closed : HasClosedRange L) (u : H) :
    projectionPoint (L.ker : Set H)
        (isChebyshev_of_nonempty_isClosed_convex
          (show ((L.ker : Set H).Nonempty) by exact ⟨0, by simp⟩)
          L.isClosed_ker L.ker.convex)
        u =
      u - (L⁺[hL_closed]) (L u) := by
  have hproj :
      projectionPoint (L.ker : Set H)
          (isChebyshev_of_nonempty_isClosed_convex
            (show ((L.ker : Set H).Nonempty) by exact ⟨0, by simp⟩)
            L.isClosed_ker L.ker.convex)
          u =
        L.ker.starProjection u := by
    symm
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        (show ((L.ker : Set H).Nonempty) by exact ⟨0, by simp⟩)
        L.isClosed_ker L.ker.convex).2 ?_
    refine ⟨Submodule.starProjection_apply_mem L.ker u, ?_⟩
    intro w hw
    have hw_sub : w - L.ker.starProjection u ∈ L.ker := by
      exact Submodule.sub_mem L.ker hw (Submodule.starProjection_apply_mem L.ker u)
    have horth : u - L.ker.starProjection u ∈ L.kerᗮ := by
      exact L.ker.sub_starProjection_mem_orthogonal u
    have hzero :=
      (Submodule.mem_orthogonal' L.ker (u - L.ker.starProjection u)).1 horth
        (w - L.ker.starProjection u) hw_sub
    -- The projector characterization for a closed subspace is exactly the orthogonality condition.
    simpa [real_inner_comm] using le_of_eq hzero
  have hker :
      L.ker.starProjection u = u - (L⁺[hL_closed]) (L u) := by
    simpa using
      congrArg (fun A : H →L[ℝ] H ↦ A u)
        (ker_starProjection_eq_id_sub_moorePenroseInverseOperator_comp L hL_closed)
  -- Replace the abstract projection with the closed-range kernel formula.
  calc
    projectionPoint (L.ker : Set H)
        (isChebyshev_of_nonempty_isClosed_convex
          (show ((L.ker : Set H).Nonempty) by exact ⟨0, by simp⟩)
          L.isClosed_ker L.ker.convex)
        u = L.ker.starProjection u := hproj
    _ = u - (L⁺[hL_closed]) (L u) := hker

/-- Helper for Example 29.17: invertibility of `L ∘L L.adjoint` forces `range L` to be closed. -/
lemma hasClosedRange_of_isUnit_comp_adjoint (L : H →L[ℝ] K)
    [Fact (IsUnit (L ∘L L.adjoint))] :
    HasClosedRange L := by
  have hcomp_closed : IsClosed (((L ∘L L.adjoint).range : Set K)) := by
    have hrange_univ : ((L ∘L L.adjoint).range : Set K) = Set.univ := by
      ext v
      constructor
      · intro hv
        simp
      · intro _
        refine ⟨(L ∘L L.adjoint).inverse v, ?_⟩
        -- Invertibility gives a preimage for every `v`.
        simpa [← ringInverse_eq_inverse, one_def] using
          congrArg (fun A : K →L[ℝ] K ↦ A v)
            (Ring.mul_inverse_cancel (L ∘L L.adjoint)
              (Fact.out : IsUnit (L ∘L L.adjoint)))
    rw [hrange_univ]
    simpa using isClosed_univ
  exact (ContinuousLinearMap.isClosed_range_comp_adjoint_iff L).mp hcomp_closed

/-- Helper for Example 29.17: when `L ∘L L.adjoint` is invertible, the value of `L†` on `L u`
is `L.adjoint ((L ∘L L.adjoint).inverse (L u))`. -/
lemma moorePenroseInverseOperator_apply_comp_eq_adjoint_inverse_apply
    [Fact (IsUnit (L ∘L L.adjoint))] (hL_closed : HasClosedRange L) (u : H) :
    (L⁺[hL_closed]) (L u) = L.adjoint ((L ∘L L.adjoint).inverse (L u)) := by
  let q : H := L.adjoint ((L ∘L L.adjoint).inverse (L u))
  have hq_mem : q ∈ L.kerᗮ := by
    -- The candidate lies in `range L* = (ker L)ᗮ`.
    have hq_range : q ∈ ((adjoint L).range : Set H) := ⟨(L ∘L L.adjoint).inverse (L u), rfl⟩
    simpa [q, orthogonal_ker_eq_adjoint_range L hL_closed] using
      hq_range
  have hres_ker : u - q ∈ L.ker := by
    rw [LinearMap.mem_ker]
    -- The residual is killed by `L` because `(L ∘L L.adjoint)` cancels its inverse on `L u`.
    calc
      L (u - q) = L u - L q := by simp [q]
      _ = L u - (L ∘L L.adjoint) ((L ∘L L.adjoint).inverse (L u)) := by rfl
      _ = L u - L u := by
            rw [show (L ∘L L.adjoint) ((L ∘L L.adjoint).inverse (L u)) = L u by
              simpa [← ringInverse_eq_inverse, one_def] using
                congrArg (fun A : K →L[ℝ] K ↦ A (L u))
                  (Ring.mul_inverse_cancel (L ∘L L.adjoint)
                    (Fact.out : IsUnit (L ∘L L.adjoint)))]
      _ = 0 := by simp
  have hres_orth : u - q ∈ (L.kerᗮ : Submodule ℝ H)ᗮ := by
    simpa [Submodule.orthogonal_orthogonal_eq_closure,
      L.isClosed_ker.submodule_topologicalClosure_eq] using hres_ker
  have hq_proj : (L.kerᗮ : Submodule ℝ H).starProjection u = q := by
    exact (L.kerᗮ : Submodule ℝ H).eq_starProjection_of_mem_orthogonal hq_mem hres_orth
  have hmp_proj : (L.kerᗮ : Submodule ℝ H).starProjection u = (L⁺[hL_closed]) (L u) := by
    have hker :
        L.ker.starProjection u = u - (L⁺[hL_closed]) (L u) := by
      simpa using
        congrArg (fun A : H →L[ℝ] H ↦ A u)
          (ker_starProjection_eq_id_sub_moorePenroseInverseOperator_comp L hL_closed)
    calc
      (L.kerᗮ : Submodule ℝ H).starProjection u = u - L.ker.starProjection u := by
        simpa using L.ker.starProjection_orthogonal_val u
      _ = u - (u - (L⁺[hL_closed]) (L u)) := by rw [hker]
      _ = (L⁺[hL_closed]) (L u) := by abel_nf
  -- Both expressions are the orthogonal projection of `u` onto `(ker L)ᗮ`.
  calc
    (L⁺[hL_closed]) (L u) = (L.kerᗮ : Submodule ℝ H).starProjection u := hmp_proj.symm
    _ = q := hq_proj
    _ = L.adjoint ((L ∘L L.adjoint).inverse (L u)) := rfl

/-- Example 29.17 (1): if `range L` is closed and `z ∈ affineFiber L y = {u | L u = y}`, then
the metric projection onto `affineFiber L y` is `x - L⁺(L (x - z))`. -/
theorem projectionPoint_affineFiber_eq_sub_moorePenroseInverseOperator_of_mem
    (hL_closed : HasClosedRange L) {z : H} (hz : z ∈ affineFiber L y) (x : H) :
    affineFiberProjection L y ⟨z, hz⟩ x =
      x - (L⁺[hL_closed]) (L (x - z)) := by
  -- Translate the fiber to `z + ker L` and use the translation formula for metric projections.
  calc
    affineFiberProjection L y ⟨z, hz⟩ x =
        z + projectionPoint (L.ker : Set H)
          (isChebyshev_of_nonempty_isClosed_convex
            (show ((L.ker : Set H).Nonempty) by exact ⟨0, by simp⟩)
            L.isClosed_ker L.ker.convex)
          (x - z) := by
            simpa [affineFiberProjection, affineFiber_isChebyshev,
              affineFiber_eq_vadd_ker_of_mem (L := L) (y := y) hz] using
              (projectionPoint_vadd_set_eq_add_projectionPoint
                (C := (L.ker : Set H)) x z
                (show ((L.ker : Set H).Nonempty) by exact ⟨0, by simp⟩)
                L.isClosed_ker L.ker.convex)
    _ = z + ((x - z) - (L⁺[hL_closed]) (L (x - z))) := by
          rw [projectionPoint_ker_eq_sub_moorePenroseInverseOperator_apply
            (L := L) hL_closed (x - z)]
    _ = x - (L⁺[hL_closed]) (L (x - z)) := by
          abel_nf

/-- Example 29.17 (2): if `range L` is closed, then the metric projection onto
`affineFiber L y = {u | L u = y}` is `x - L⁺(L x - y)` whenever the fiber is nonempty. -/
theorem projectionPoint_affineFiber_eq_sub_moorePenroseInverseOperator
    (hL_closed : HasClosedRange L) (hy : (affineFiber L y).Nonempty) (x : H) :
    affineFiberProjection L y hy x =
      x - (L⁺[hL_closed]) (L x - y) := by
  obtain ⟨z, hz⟩ := hy
  -- Replace the chosen nonempty witness by an explicit fiber point and simplify the residual.
  calc
    affineFiberProjection L y ⟨z, hz⟩ x =
        x - (L⁺[hL_closed]) (L (x - z)) := by
          exact
            projectionPoint_affineFiber_eq_sub_moorePenroseInverseOperator_of_mem
              hL_closed hz x
    _ = x - (L⁺[hL_closed]) (L x - y) := by
          rw [show L (x - z) = L x - y by
            rw [ContinuousLinearMap.map_sub, mem_affineFiber.mp hz]]

/-- Example 29.17 (3): if `L ∘L L.adjoint` is invertible, then the metric projection onto
`affineFiber L y = {u | L u = y}` is
`x - L.adjoint ((L ∘L L.adjoint)⁻¹ (L x - y))`. -/
theorem projectionPoint_affineFiber_eq_sub_adjoint_inverse_apply_of_isUnit_comp_adjoint
    [Fact (IsUnit (L ∘L L.adjoint))] (x : H) :
    affineFiberProjection L y (affineFiber_nonempty_of_isUnit_comp_adjoint L y) x =
      x - L.adjoint ((L ∘L L.adjoint).inverse (L x - y)) := by
  let hy : (affineFiber L y).Nonempty := affineFiber_nonempty_of_isUnit_comp_adjoint L y
  let hL_closed : HasClosedRange L := hasClosedRange_of_isUnit_comp_adjoint L
  rcases hy with ⟨z, hz⟩
  -- Evaluate the closed-range formula at a concrete fiber point, then use the inverse formula on
  -- the range element `L (x - z) = L x - y`.
  change affineFiberProjection L y ⟨z, hz⟩ x =
      x - L.adjoint ((L ∘L L.adjoint).inverse (L x - y))
  calc
    affineFiberProjection L y ⟨z, hz⟩ x =
        x - (L⁺[hL_closed]) (L (x - z)) := by
          exact
            projectionPoint_affineFiber_eq_sub_moorePenroseInverseOperator_of_mem
              hL_closed hz x
    _ = x - L.adjoint ((L ∘L L.adjoint).inverse (L (x - z))) := by
          rw [moorePenroseInverseOperator_apply_comp_eq_adjoint_inverse_apply
            (L := L) hL_closed (x - z)]
    _ = x - L.adjoint ((L ∘L L.adjoint).inverse (L x - y)) := by
          rw [show L (x - z) = L x - y by
            rw [ContinuousLinearMap.map_sub, mem_affineFiber.mp hz]]

/-- Example 29.17 (4): if `L.adjoint ∘L L` is invertible and `affineFiber L y` is nonempty, then
`affineFiber L y = {((L.adjoint ∘L L)⁻¹ (L.adjoint y))}`. -/
theorem affineFiber_eq_singleton_inverse_adjoint_apply_of_isUnit_adjoint_comp
    [Fact (IsUnit (L.adjoint ∘L L))] (hy : (affineFiber L y).Nonempty) :
    affineFiber L y = {(L.adjoint ∘L L).inverse (L.adjoint y)} := by
  let A : H →L[ℝ] H := L.adjoint ∘L L
  have hA_inj : Function.Injective A := by
    have hA_ker : A.ker = ⊥ := by
      refine LinearMap.ker_eq_bot'.2 ?_
      intro x hx
      have hcancel : A.inverse (A x) = x := by
        simpa [A, ← ringInverse_eq_inverse, one_def] using
          congrArg (fun B : H →L[ℝ] H ↦ B x)
            (Ring.inverse_mul_cancel A (Fact.out : IsUnit A))
      calc
        x = A.inverse (A x) := by simpa using hcancel.symm
        _ = A.inverse 0 := by exact congrArg A.inverse hx
        _ = 0 := by simp
    exact (LinearMap.ker_eq_bot).mp hA_ker
  have hA_inverse_apply : A (A.inverse (L.adjoint y)) = L.adjoint y := by
    simpa [A, ← ringInverse_eq_inverse, one_def] using
      congrArg (fun B : H →L[ℝ] H ↦ B (L.adjoint y))
        (Ring.mul_inverse_cancel A (Fact.out : IsUnit A))
  rcases hy with ⟨z, hz⟩
  have hmem : A.inverse (L.adjoint y) ∈ affineFiber L y := by
    have hz_eq : A.inverse (L.adjoint y) = z := by
      apply hA_inj
      calc
        A (A.inverse (L.adjoint y)) = L.adjoint y := hA_inverse_apply
        _ = A z := by simp [A, mem_affineFiber.mp hz]
    rw [mem_affineFiber]
    rw [hz_eq]
    exact mem_affineFiber.mp hz
  ext x
  constructor
  · intro hx
    rw [Set.mem_singleton_iff]
    apply hA_inj
    calc
      A x = L.adjoint y := by simp [A, mem_affineFiber.mp hx]
      _ = A (A.inverse (L.adjoint y)) := hA_inverse_apply.symm
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hmem

end

end
