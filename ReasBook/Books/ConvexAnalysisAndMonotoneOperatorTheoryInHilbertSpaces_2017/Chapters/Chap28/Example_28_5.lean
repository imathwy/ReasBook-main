import BauschkeLean.Chap12.ScaledProximityOperator
import BauschkeLean.Chap19.Example_19_3
import BauschkeLean.Chap28.Corollary_28_4
import BauschkeLean.Chap09.Remark_9_37

open ContinuousLinearMap
open EuclideanGeometry
open Filter
open Set
open scoped BigOperators InnerProductSpace Topology

universe u

namespace ContinuousLinearMap

noncomputable section

section FiniteFamilyCoordinateSum

variable {m : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "ProductSpace" => lp (fun _ : Fin m ↦ H) 2

/-- The canonical continuous linear map from the finite Hilbert product `lp (Fin m → H) 2`
to `H` that sums the coordinates. -/
abbrev sumCoordinateMap : ProductSpace →L[ℝ] H :=
  (toLpOperator (fun _ : Fin m ↦ ContinuousLinearMap.id ℝ H)).adjoint

/-- Evaluating `sumCoordinateMap` returns the finite coordinate sum. -/
@[simp] theorem sumCoordinateMap_apply (z : ProductSpace) :
    sumCoordinateMap z = ∑ i, z i := by
  rw [sumCoordinateMap, toLpOperator_adjoint_apply_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  simp

/-- The adjoint of `sumCoordinateMap` is the diagonal embedding `x ↦ (x, ..., x)`. -/
@[simp] theorem sumCoordinateMap_adjoint_apply (x : H) (i : Fin m) :
    sumCoordinateMap.adjoint x i = x := by
  simpa [sumCoordinateMap] using
    (toLpOperator_apply (fun _ : Fin m ↦ ContinuousLinearMap.id ℝ H) x i)

/-- Composing `sumCoordinateMap` with its adjoint multiplies by the family cardinality `m`. -/
theorem sumCoordinateMap_comp_adjoint_eq_card_smul_id :
    ((sumCoordinateMap : ProductSpace →L[ℝ] H)).comp
        ((sumCoordinateMap : ProductSpace →L[ℝ] H)).adjoint =
      (m : ℝ) • (1 : H →L[ℝ] H) := by
  ext x
  rw [ContinuousLinearMap.comp_apply, sumCoordinateMap_apply]
  have hsum :
      ∑ i : Fin m, (sumCoordinateMap.adjoint x) i =
        ∑ i : Fin m, x := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [sumCoordinateMap_adjoint_apply]
  rw [hsum]
  calc
    ∑ i : Fin m, x = m • x := by simp
    _ = (m : ℝ) • x := by simpa using (Nat.cast_smul_eq_nsmul ℝ m x).symm

/-- Membership in the affine fiber of `sumCoordinateMap` is exactly the coordinate-sum
constraint `∑ i, z i = r`. -/
@[simp] theorem mem_affineFiber_sumCoordinateMap_iff (r : H) (z : ProductSpace) :
    z ∈ affineFiber sumCoordinateMap r ↔ ∑ i, z i = r := by
  rw [mem_affineFiber, sumCoordinateMap_apply]

/-- The affine fiber of `sumCoordinateMap` is the source constraint set
`{z | ∑ i, z i = r}`. -/
theorem affineFiber_sumCoordinateMap_eq (r : H) :
    affineFiber sumCoordinateMap r =
      {z : ProductSpace | ∑ i, z i = r} := by
  ext z
  simp

end FiniteFamilyCoordinateSum

end

end ContinuousLinearMap

namespace ERealFunction

noncomputable section

-- Semantic recall: the verified project-facing owners for this item are the finite direct-sum
-- objective `directSumFunction`, the finite-family coordinate-sum map
-- `ContinuousLinearMap.sumCoordinateMap`, and Corollary 28.4's linear-fiber
-- Douglas--Rachford sequences.

section DouglasRachfordFiniteFamilyLinearConstraint

variable {m : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "ProductSpace" => lp (fun _ : Fin m ↦ H) 2

private def familySizePosReal (hm : 0 < m) : PosReal :=
  ⟨m, by exact_mod_cast hm⟩

/-- Helper for Example 28.5: scaling a finite direct-sum objective by `γ` is the same as taking
the direct sum of the coordinatewise scaled objectives. -/
@[simp] theorem posReal_smul_directSumFunction
    (f : Fin m → H → Set.Ioi (⊥ : EReal)) (γ : PosReal) :
    γ • directSumFunction f = directSumFunction (fun i ↦ γ • f i) := by
  -- Compare the two subtype-valued functions through their `EReal` coercions.
  classical
  funext z
  apply Subtype.ext
  -- Push left multiplication by `γ` through the finite direct sum by induction on the summation
  -- finset.
  have hγ_nonneg : (0 : EReal) ≤ ((γ : ℝ) : EReal) := by
    exact_mod_cast γ.2.le
  have hγ_ne_top : ((γ : ℝ) : EReal) ≠ ⊤ := by
    simp
  have hsum (s : Finset (Fin m)) :
      ((γ : ℝ) : EReal) * (Finset.sum s fun i : Fin m ↦ (f i (z i) : EReal)) =
        Finset.sum s fun i : Fin m ↦ ((γ : ℝ) : EReal) * (f i (z i) : EReal) := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert i s hi ih =>
        simp [Finset.sum_insert, hi]
        rw [EReal.left_distrib_of_nonneg_of_ne_top hγ_nonneg hγ_ne_top]
        exact
          congrArg
            (fun t : EReal ↦ ((γ : ℝ) : EReal) * (f i (z i) : EReal) + t)
            ih
  simpa [directSumFunction_apply, posReal_smul_apply] using hsum Finset.univ

/-- Helper for Example 28.5: the affine fiber `affineFiber sumCoordinateMap r` is nonempty as
soon as `m > 0`. -/
theorem affineFiber_sumCoordinateMap_nonempty
    (hm : 0 < m) (r : H) :
    (affineFiber ContinuousLinearMap.sumCoordinateMap r : Set ProductSpace).Nonempty := by
  refine ⟨ContinuousLinearMap.sumCoordinateMap.adjoint ((m : ℝ)⁻¹ • r), ?_⟩
  rw [mem_affineFiber]
  have happly :=
    congrArg
      (fun T : H →L[ℝ] H ↦ T ((m : ℝ)⁻¹ • r))
      (ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id (m := m) (H := H))
  simpa [ContinuousLinearMap.comp_apply, smul_smul,
    inv_mul_cancel₀ (show (m : ℝ) ≠ 0 by exact_mod_cast Nat.ne_of_gt hm)] using happly

/-- Helper for Example 28.5: the affine fiber `affineFiber sumCoordinateMap r` is Chebyshev. -/
abbrev affineFiberSumCoordinateMapChebyshev
    (hm : 0 < m) (r : H) :
    IsChebyshev (affineFiber ContinuousLinearMap.sumCoordinateMap r : Set ProductSpace) :=
  affineFiber_isChebyshev (affineFiber_sumCoordinateMap_nonempty hm r)

/-- Helper for Example 28.5: applying `sumCoordinateMap.comp sumCoordinateMap.adjoint` multiplies
by the family cardinality `m`. -/
theorem sumCoordinateMap_comp_adjoint_apply_eq_card_smul
    (x : H) :
    (ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H)
        ((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).adjoint x) =
      (m : ℝ) • x := by
  have happly :=
    congrArg
      (fun T : H →L[ℝ] H ↦ T x)
      (ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id (m := m) (H := H))
  simpa [ContinuousLinearMap.comp_apply] using happly

/-- Helper for Example 28.5: the explicit affine correction
`z + m⁻¹ • sumCoordinateMap.adjoint (r - sumCoordinateMap z)` lies in the affine fiber
`affineFiber sumCoordinateMap r`. -/
theorem affineCorrection_mem_affineFiber_sumCoordinateMap
    (hm : 0 < m) (r : H) (z : ProductSpace) :
    z + (m : ℝ)⁻¹ •
        ContinuousLinearMap.sumCoordinateMap.adjoint
          (r - ContinuousLinearMap.sumCoordinateMap z) ∈
      affineFiber ContinuousLinearMap.sumCoordinateMap r := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hm
  rw [mem_affineFiber, ContinuousLinearMap.map_add, ContinuousLinearMap.map_smul,
    sumCoordinateMap_comp_adjoint_apply_eq_card_smul (m := m) (H := H)
      (r - ContinuousLinearMap.sumCoordinateMap z)]
  simp [smul_smul, hm0]

/-- Helper for Example 28.5: the diagonal image of `sumCoordinateMap.adjoint` is orthogonal to
`sumCoordinateMap.ker`. -/
theorem sumCoordinateMap_adjoint_mem_ker_orthogonal
    (x : H) :
    ((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).adjoint x) ∈
      ((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).ker)ᗮ := by
  refine
    (Submodule.mem_orthogonal'
      ((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).ker) _).2 ?_
  intro u hu
  have hu0 : (ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H) u = 0 :=
    LinearMap.mem_ker.mp hu
  rw [ContinuousLinearMap.adjoint_inner_left]
  simp [hu0]

/-- Helper for Example 28.5: the residual of the explicit affine correction belongs to
`sumCoordinateMap.kerᗮ`. -/
theorem affineCorrectionResidual_mem_sumCoordinateMapKerOrthogonal
    (r : H) (z : ProductSpace) :
    z - (z + (m : ℝ)⁻¹ •
        ContinuousLinearMap.sumCoordinateMap.adjoint
          (r - ContinuousLinearMap.sumCoordinateMap z)) ∈
      ((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).ker)ᗮ := by
  -- The residual is a negated scalar multiple of the adjoint image, so orthogonality is stable
  -- under the submodule operations on `kerᗮ`.
  have hadj :
      ContinuousLinearMap.sumCoordinateMap.adjoint
          (r - ContinuousLinearMap.sumCoordinateMap z) ∈
        ((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).ker)ᗮ :=
    sumCoordinateMap_adjoint_mem_ker_orthogonal (m := m) (H := H)
      (r - ContinuousLinearMap.sumCoordinateMap z)
  have hneg :
      -((m : ℝ)⁻¹ •
          ContinuousLinearMap.sumCoordinateMap.adjoint
            (r - ContinuousLinearMap.sumCoordinateMap z)) ∈
        ((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).ker)ᗮ := by
    exact
      (((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).ker)ᗮ).neg_mem
        ((((ContinuousLinearMap.sumCoordinateMap : ProductSpace →L[ℝ] H).ker)ᗮ).smul_mem
          _ hadj)
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hneg

/-- Helper for Example 28.5: a point in `affineFiber sumCoordinateMap r` identifies that fiber
with the affine subspace `AffineSubspace.mk' z0 sumCoordinateMap.ker`. -/
theorem affineSubspaceMk'_sumCoordinateMap_eq_affineFiber
    {r : H} {z0 : ProductSpace}
    (hz0 : z0 ∈ affineFiber ContinuousLinearMap.sumCoordinateMap r) :
    ((AffineSubspace.mk' z0 ContinuousLinearMap.sumCoordinateMap.ker :
        AffineSubspace ℝ ProductSpace) : Set ProductSpace) =
      affineFiber ContinuousLinearMap.sumCoordinateMap r := by
  have hz0_eq : ContinuousLinearMap.sumCoordinateMap z0 = r := mem_affineFiber.mp hz0
  ext w
  change
    ContinuousLinearMap.sumCoordinateMap (w - z0) = 0 ↔
      ContinuousLinearMap.sumCoordinateMap w = r
  rw [ContinuousLinearMap.map_sub]
  constructor
  · intro hw
    have hwz :
        ContinuousLinearMap.sumCoordinateMap w =
          ContinuousLinearMap.sumCoordinateMap z0 := sub_eq_zero.mp hw
    simpa [hz0_eq] using hwz
  · intro hw
    have hwz :
        ContinuousLinearMap.sumCoordinateMap w =
          ContinuousLinearMap.sumCoordinateMap z0 := by
      simpa [hz0_eq] using hw
    exact sub_eq_zero.mpr hwz

/-- Helper for Example 28.5: the metric projection onto
`affineFiber ContinuousLinearMap.sumCoordinateMap r` is the explicit affine correction
`z + m⁻¹ • sumCoordinateMap.adjoint (r - sumCoordinateMap z)`. -/
theorem projectionPoint_affineFiber_sumCoordinateMap_eq_affineCorrection
    (hm : 0 < m) (r : H) (z : ProductSpace) :
    P[affineFiber ContinuousLinearMap.sumCoordinateMap r,
      affineFiberSumCoordinateMapChebyshev hm r] z =
      z + (m : ℝ)⁻¹ •
        ContinuousLinearMap.sumCoordinateMap.adjoint
          (r - ContinuousLinearMap.sumCoordinateMap z) := by
  -- Route correction: first compute the orthogonal projection in a fixed affine model of the
  -- fiber, then translate that result back to the metric projector on `affineFiber`.
  obtain ⟨z0, hz0⟩ := affineFiber_sumCoordinateMap_nonempty (m := m) (H := H) hm r
  let C : AffineSubspace ℝ ProductSpace :=
    AffineSubspace.mk' z0 ContinuousLinearMap.sumCoordinateMap.ker
  have hC_set : (C : Set ProductSpace) = affineFiber ContinuousLinearMap.sumCoordinateMap r := by
    simpa [C] using
      affineSubspaceMk'_sumCoordinateMap_eq_affineFiber (m := m) (H := H) hz0
  have hC_nonempty : (C : Set ProductSpace).Nonempty := by
    refine ⟨z0, ?_⟩
    simpa [hC_set] using hz0
  have hC_closed : IsClosed (C : Set ProductSpace) := by
    simpa [hC_set] using
      affineFiber_isClosed ContinuousLinearMap.sumCoordinateMap r
  let p : ProductSpace :=
    z + (m : ℝ)⁻¹ •
      ContinuousLinearMap.sumCoordinateMap.adjoint
        (r - ContinuousLinearMap.sumCoordinateMap z)
  have hp_mem : p ∈ (C : Set ProductSpace) := by
    -- The explicit correction lands in the affine fiber, hence in the chosen affine model `C`.
    have hp_fiber :
        p ∈ affineFiber ContinuousLinearMap.sumCoordinateMap r := by
      simpa [p] using
        affineCorrection_mem_affineFiber_sumCoordinateMap (m := m) (H := H) hm r z
    simpa [hC_set] using hp_fiber
  have hp_orth : z - p ∈ C.directionᗮ := by
    -- The correction residual is already expressed in the stable `sumCoordinateMap.kerᗮ` normal
    -- form required by the affine orthogonal-projection criterion.
    simpa [C, p, AffineSubspace.direction_mk'] using
      affineCorrectionResidual_mem_sumCoordinateMapKerOrthogonal (m := m) (H := H) r z
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set ProductSpace) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set ProductSpace) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hp_proj : (orthogonalProjection C z : ProductSpace) = p := by
    -- Characterize the affine orthogonal projection by membership in `C` and orthogonality of
    -- the residual to the direction subspace.
    refine (coe_orthogonalProjection_eq_iff_mem (s := C) (p := z) (q := p)).2 ?_
    exact ⟨hp_mem, hp_orth⟩
  have hp_point :
      P[(C : Set ProductSpace),
        isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex] z = p := by
    -- Replace the metric projector by the affine orthogonal projection only after fixing `C`.
    exact
      (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
        hC_nonempty hC_closed z).trans hp_proj
  simpa [hC_set, affineFiberSumCoordinateMapChebyshev, p] using hp_point

/-- The Corollary 28.4 Douglas--Rachford `y`-orbit specialized to the finite-family sum constraint
`∑ i, z i = r` and the direct-sum objective `directSumFunction f`. -/
abbrev finiteFamilyLinearConstraintIteration
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace) :
    ℕ → ProductSpace :=
  linearFiberDouglasRachfordIteration
    (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
    ContinuousLinearMap.sumCoordinateMap
    r
    (familySizePosReal hm)
    ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
    γ lam y0

/-- The canonical proximal sequence `xₙ = Prox_{γ (⨁ i, fᵢ)}(yₙ)` for the finite-family linear
constraint problem. -/
abbrev finiteFamilyLinearConstraintPrimalSequence
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace) :
    ℕ → ProductSpace :=
  linearFiberDouglasRachfordPrimalSequence
    (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
    ContinuousLinearMap.sumCoordinateMap
    r
    (familySizePosReal hm)
    ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
    γ lam y0

/-- The canonical projected sequence `pₙ = P[{z | ∑ i, z i = r}] (yₙ)` for the finite-family
linear constraint problem. -/
abbrev finiteFamilyLinearConstraintProjectedSequence
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace) :
    ℕ → ProductSpace :=
  linearFiberDouglasRachfordProjectedSequence
    (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
    ContinuousLinearMap.sumCoordinateMap
    r
    (familySizePosReal hm)
    ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
    γ lam y0

/-- The auxiliary projected sequence `qₙ = P[{z | ∑ i, z i = r}] (xₙ)` from Corollary 28.4,
specialized to the finite-family linear constraint problem. -/
abbrev finiteFamilyLinearConstraintAuxiliaryProjectedSequence
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace) :
    ℕ → ProductSpace :=
  linearFiberDouglasRachfordAuxiliaryProjectionSequence
    (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
    ContinuousLinearMap.sumCoordinateMap
    r
    (familySizePosReal hm)
    ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
    γ lam y0

/-- The source set
`{s | ∃ z, (∀ i, z i ∈ effectiveDomain (f i)) ∧ ∑ i, z i = s}`
is the canonical image `sumCoordinateMap '' effectiveDomain (directSumFunction f)`. -/
theorem sumCoordinateMap_image_effectiveDomain_directSumFunction_eq
    (f : Fin m → H → Set.Ioi (⊥ : EReal)) :
    ContinuousLinearMap.sumCoordinateMap '' effectiveDomain (directSumFunction f) =
      {s : H |
        ∃ z : ProductSpace,
          (∀ i : Fin m, z i ∈ effectiveDomain (f i)) ∧
            (∑ i : Fin m, z i) = s} := by
  ext s
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z, (mem_effectiveDomain_directSumFunction_iff f z).1 hz, ?_⟩
    simp
  · rintro ⟨z, hz, hsum⟩
    refine ⟨z, (mem_effectiveDomain_directSumFunction_iff f z).2 hz, ?_⟩
    simpa [ContinuousLinearMap.sumCoordinateMap_apply] using hsum

/-- The canonical affine-fiber constraint `affineFiber sumCoordinateMap r` is exactly the source
set `{z | ∑ i, z i = r}` inside the `Argmin` owner. -/
theorem argmin_affineFiber_sumCoordinateMap_eq
    (f : Fin m → H → Set.Ioi (⊥ : EReal)) (r : H) :
    Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap r] (directSumFunction f).asEReal =
      Argmin[{z : ProductSpace | ∑ i : Fin m, z i = r}] (directSumFunction f).asEReal := by
  ext z
  simp [ContinuousLinearMap.affineFiber_sumCoordinateMap_eq]

/-- A triple of product-space sequences `p`, `x`, and `y`, together with scalar correction
sequences `u` and `v`, satisfies the componentwise Douglas--Rachford recursion `(28.23)` for the
finite family `f : Fin m → Γ₀(H)` under the linear constraint `∑ i, x i = r`. -/
structure IsFiniteFamilyLinearConstraintDouglasRachfordOrbit
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (r : H) (lam : ℕ → ℝ) (γ : PosReal) (y0 : ProductSpace)
    (u v : ℕ → H) (p x y : ℕ → ProductSpace) : Prop where
  /-- The orbit starts from the prescribed family `y0`. -/
  y_zero : y 0 = y0
  /-- The first affine correction is `u_n = m⁻¹ (r - ∑ j, yⱼ,n)`. -/
  u_eq (n : ℕ) : u n = (m : ℝ)⁻¹ • (r - ∑ j : Fin m, y n j)
  /-- The projected family is `pᵢ,n = yᵢ,n + u_n`. -/
  p_eq (n : ℕ) (i : Fin m) : p n i = y n i + u n
  /-- The proximal family is `xᵢ,n = Prox_{γ fᵢ}(yᵢ,n)`. -/
  x_eq (n : ℕ) (i : Fin m) : x n i = Prox[γ, f i, hf i] (y n i)
  /-- The second affine correction is `v_n = m⁻¹ (r - ∑ j, xⱼ,n)`. -/
  v_eq (n : ℕ) : v n = (m : ℝ)⁻¹ • (r - ∑ j : Fin m, x n j)
  /-- The relaxed update is
  `yᵢ,n+1 = yᵢ,n + λ_n (xᵢ,n - yᵢ,n + 2 v_n - u_n)`. -/
  y_succ_eq (n : ℕ) (i : Fin m) :
      y (n + 1) i = y n i + lam n • (x n i - y n i + (2 : ℝ) • v n - u n)

/-- The canonical projected sequence is the source affine correction
`pᵢ,n = yᵢ,n + m⁻¹ • (r - ∑ j, yⱼ,n)`. -/
theorem finiteFamilyLinearConstraintProjectedSequence_apply_eq_affineCorrection
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace)
    (n : ℕ) (i : Fin m) :
    finiteFamilyLinearConstraintProjectedSequence f hf hm r γ lam y0 n i =
      finiteFamilyLinearConstraintIteration f hf hm r γ lam y0 n i +
        (m : ℝ)⁻¹ •
          (r - ∑ j : Fin m, finiteFamilyLinearConstraintIteration f hf hm r γ lam y0 n j) := by
  simpa [finiteFamilyLinearConstraintIteration, finiteFamilyLinearConstraintProjectedSequence] using
    congrArg
      (fun z : ProductSpace ↦ z i)
      (linearFiberDouglasRachfordProjectedSequence_eq_affineCorrection
        (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
        ContinuousLinearMap.sumCoordinateMap
        r
        (familySizePosReal hm)
        ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
        γ lam y0 n)

/-- The auxiliary projected sequence is the source affine correction
`qᵢ,n = xᵢ,n + m⁻¹ • (r - ∑ j, xⱼ,n)`. -/
theorem finiteFamilyLinearConstraintAuxiliaryProjectedSequence_apply_eq_affineCorrection
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace)
    (n : ℕ) (i : Fin m) :
    finiteFamilyLinearConstraintAuxiliaryProjectedSequence f hf hm r γ lam y0 n i =
      finiteFamilyLinearConstraintPrimalSequence f hf hm r γ lam y0 n i +
        (m : ℝ)⁻¹ •
          (r - ∑ j : Fin m, finiteFamilyLinearConstraintPrimalSequence f hf hm r γ lam y0 n j) := by
  simpa [finiteFamilyLinearConstraintAuxiliaryProjectedSequence,
    finiteFamilyLinearConstraintPrimalSequence] using
    congrArg
      (fun z : ProductSpace ↦ z i)
      (linearFiberDouglasRachfordAuxiliaryProjectionSequence_eq_affineCorrection
        (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
        ContinuousLinearMap.sumCoordinateMap
        r
        (familySizePosReal hm)
        ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
        γ lam y0 n)

/-- The canonical projected sequence stays in the source constraint set
`{z | ∑ i, z i = r}`. -/
@[simp] theorem finiteFamilyLinearConstraintProjectedSequence_sum_eq
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace)
    (n : ℕ) :
    ∑ i : Fin m, finiteFamilyLinearConstraintProjectedSequence f hf hm r γ lam y0 n i = r := by
  exact
    (ContinuousLinearMap.mem_affineFiber_sumCoordinateMap_iff
      r (finiteFamilyLinearConstraintProjectedSequence f hf hm r γ lam y0 n)).1
      (linearFiberDouglasRachfordProjectedSequence_mem_affineFiber
        (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
        ContinuousLinearMap.sumCoordinateMap
        r
        (familySizePosReal hm)
        ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
        γ lam y0 n)

/-- The auxiliary projected sequence likewise stays in the source constraint set
`{z | ∑ i, z i = r}`. -/
@[simp] theorem finiteFamilyLinearConstraintAuxiliaryProjectedSequence_sum_eq
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H) (γ : PosReal) (lam : ℕ → ℝ) (y0 : ProductSpace)
    (n : ℕ) :
    ∑ i : Fin m, finiteFamilyLinearConstraintAuxiliaryProjectedSequence f hf hm r γ lam y0 n i =
      r := by
  exact
    (ContinuousLinearMap.mem_affineFiber_sumCoordinateMap_iff
      r (finiteFamilyLinearConstraintAuxiliaryProjectedSequence f hf hm r γ lam y0 n)).1
      (linearFiberDouglasRachfordAuxiliaryProjectionSequence_mem_affineFiber
        (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
        ContinuousLinearMap.sumCoordinateMap
        r
        (familySizePosReal hm)
        ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
        γ lam y0 n)

namespace IsFiniteFamilyLinearConstraintDouglasRachfordOrbit

variable
    {f : Fin m → H → Set.Ioi (⊥ : EReal)}
    {hf : ∀ i : Fin m, f i ∈ Γ₀(H)}
    {r : H} {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {u v : ℕ → H} {p x y : ℕ → ProductSpace}

/-- The source `y`-orbit from `(28.23)` agrees with the canonical Corollary 28.4 iterate
specialized to the direct-sum objective and the coordinate-sum map. -/
theorem y_eq_finiteFamilyLinearConstraintIteration
    (hm : 0 < m)
    (hOrbit :
      IsFiniteFamilyLinearConstraintDouglasRachfordOrbit f hf r lam γ y0 u v p x y) :
    y = finiteFamilyLinearConstraintIteration f hf hm r γ lam y0 := by
  -- Route correction: normalize the canonical relaxed iteration first, then rewrite its
  -- resolvent pieces to the source affine-correction recursion `(28.23)`.
  funext n
  induction n with
  | zero =>
      -- Both recursions start from the prescribed initial family `y0`.
      simpa using hOrbit.y_zero
  | succ n ih =>
      have ih' :
          relaxedOperatorIteration
            (fun _ ↦
                  douglasRachfordOperator
                (resolventMap
                  N[affineFiber ContinuousLinearMap.sumCoordinateMap r]
                  (Set.normalCone_isMaximallyMonotone
                    (affineFiber_sumCoordinateMap_nonempty hm r)
                    (affineFiber_isClosed ContinuousLinearMap.sumCoordinateMap r)
                    (affineFiber_convex ContinuousLinearMap.sumCoordinateMap r))
                  γ)
                (resolventMap
                  (∂ (directSumFunction f))
                  (subdifferential_isMaximallyMonotone_of_mem_gammaZero
                    (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf))
                  γ))
            lam y0 n = y n := by
        -- Rewrite the induction hypothesis back to the raw relaxed-iteration owner.
        simpa [finiteFamilyLinearConstraintIteration, linearFiberDouglasRachfordIteration] using
          ih.symm
      have hxProd :
          resolventMap
              (∂ (directSumFunction f))
              (subdifferential_isMaximallyMonotone_of_mem_gammaZero
                (directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf))
              γ
              (y n) =
            x n := by
        -- Proposition 24.11 identifies the direct-sum resolvent with the coordinatewise proximal
        -- family from the source orbit.
        rw [resolventMap_subdifferential_eq_scaledProximityOperator]
        ext i
        have hprox :=
          congrArg
            (fun z : ProductSpace ↦ z i)
            (prox_directSumFunction_eq_directSumCoordinatewiseProx
              (fun j ↦ γ • f j)
              (fun j ↦ smul_mem_gammaZero (f j) (hf j) γ)
              (y n))
        calc
          Prox[γ, directSumFunction f,
              directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf]
              (y n) i
              =
              Prox[directSumFunction (fun j ↦ γ • f j),
                directSumFunction_mem_gammaZero_of_forall_mem_gammaZero
                  (fun j ↦ γ • f j)
                  (fun j ↦ smul_mem_gammaZero (f j) (hf j) γ)]
                (y n) i := by
                  simp [scaledProximityOperator]
          _ =
              directSumCoordinatewiseProx
                (fun j ↦ γ • f j)
                (fun j ↦ smul_mem_gammaZero (f j) (hf j) γ)
                (y n) i := hprox
          _ = Prox[γ, f i, hf i] (y n i) := by
                simp [scaledProximityOperator]
          _ = x n i := by
                rw [hOrbit.x_eq n i]
      have hreflCorrection :
          (m : ℝ)⁻¹ •
              (r - ContinuousLinearMap.sumCoordinateMap ((2 : ℝ) • x n - y n)) =
            (2 : ℝ) • v n - u n := by
        -- Normalize the reflected affine-fiber correction to the source `u_n` and `v_n`.
        rw [ContinuousLinearMap.sumCoordinateMap_apply, ContinuousLinearMap.sumCoordinateMap_apply,
          Finset.smul_sum, Finset.sum_sub_distrib, hOrbit.v_eq n, hOrbit.u_eq n]
        abel_nf
      have hreflProj :
          P[affineFiber ContinuousLinearMap.sumCoordinateMap r,
            affineFiberSumCoordinateMapChebyshev hm r]
              ((2 : ℝ) • x n - y n) =
            ((2 : ℝ) • x n - y n) +
              ContinuousLinearMap.sumCoordinateMap.adjoint ((2 : ℝ) • v n - u n) := by
        -- Reuse the local affine-fiber projection formula on the reflected point.
        calc
          P[affineFiber ContinuousLinearMap.sumCoordinateMap r,
              affineFiberSumCoordinateMapChebyshev hm r]
              ((2 : ℝ) • x n - y n)
              =
              ((2 : ℝ) • x n - y n) +
                (m : ℝ)⁻¹ •
                  ContinuousLinearMap.sumCoordinateMap.adjoint
                    (r - ContinuousLinearMap.sumCoordinateMap ((2 : ℝ) • x n - y n)) := by
                      simpa [smul_sub] using
                        projectionPoint_affineFiber_sumCoordinateMap_eq_affineCorrection
                          hm r ((2 : ℝ) • x n - y n)
          _ =
              ((2 : ℝ) • x n - y n) +
                ContinuousLinearMap.sumCoordinateMap.adjoint ((2 : ℝ) • v n - u n) := by
                  rw [← ContinuousLinearMap.map_smul, hreflCorrection]
      have hySucc :
          y (n + 1) =
            y n + lam n •
              (x n - y n +
                ContinuousLinearMap.sumCoordinateMap.adjoint ((2 : ℝ) • v n - u n)) := by
        -- Repackage the source coordinate update as a product-space identity.
        ext i
        rw [hOrbit.y_succ_eq n i]
        simp [ContinuousLinearMap.sumCoordinateMap_adjoint_apply]
        abel_nf
      -- Rewrite the canonical successor through the identified resolvent and projector pieces.
      calc
        finiteFamilyLinearConstraintIteration f hf hm r γ lam y0 (n + 1)
            =
              y n + lam n •
                (x n - y n +
                  ContinuousLinearMap.sumCoordinateMap.adjoint ((2 : ℝ) • v n - u n)) := by
                rw [finiteFamilyLinearConstraintIteration, linearFiberDouglasRachfordIteration,
                  douglasRachfordIteration, relaxedOperatorIteration_succ, ih']
                rw [douglasRachfordOperator_apply]
                rw [resolventMap_subdifferential_eq_scaledProximityOperator]
                have hnonempty :
                    (affineFiber ContinuousLinearMap.sumCoordinateMap r).Nonempty :=
                  affineFiber_sumCoordinateMap_nonempty hm r
                let C : AffineSubspace ℝ ProductSpace :=
                  AffineSubspace.mk'
                    (Classical.choose hnonempty)
                    ContinuousLinearMap.sumCoordinateMap.ker
                have hC_mem : (Classical.choose hnonempty) ∈ (C : Set ProductSpace) := by
                  change ContinuousLinearMap.sumCoordinateMap
                      (Classical.choose hnonempty - Classical.choose hnonempty) = 0
                  simp [C]
                have hC_set : (C : Set ProductSpace) =
                    affineFiber ContinuousLinearMap.sumCoordinateMap r := by
                  ext w
                  change
                    ContinuousLinearMap.sumCoordinateMap
                        (w - Classical.choose hnonempty) = 0 ↔
                      ContinuousLinearMap.sumCoordinateMap w = r
                  rw [ContinuousLinearMap.map_sub]
                  constructor
                  · intro hw
                    have hwz :
                        ContinuousLinearMap.sumCoordinateMap w =
                          ContinuousLinearMap.sumCoordinateMap (Classical.choose hnonempty) := by
                      exact sub_eq_zero.mp hw
                    simpa using hwz
                  · intro hw
                    have hwz :
                        ContinuousLinearMap.sumCoordinateMap w =
                          ContinuousLinearMap.sumCoordinateMap (Classical.choose hnonempty) := by
                      simpa using hw
                    exact sub_eq_zero.mpr hwz
                have hC_nonempty : (C : Set ProductSpace).Nonempty := by
                  exact ⟨Classical.choose hnonempty, hC_mem⟩
                have hC_closed : IsClosed (C : Set ProductSpace) := by
                  simpa [hC_set] using
                    affineFiber_isClosed ContinuousLinearMap.sumCoordinateMap r
                let hC_cheb : IsChebyshev (C : Set ProductSpace) :=
                  isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
                have hprojEq :
                    resolventMap
                        N[affineFiber ContinuousLinearMap.sumCoordinateMap r]
                        (Set.normalCone_isMaximallyMonotone
                          (affineFiber_sumCoordinateMap_nonempty hm r)
                          (affineFiber_isClosed ContinuousLinearMap.sumCoordinateMap r)
                          (affineFiber_convex ContinuousLinearMap.sumCoordinateMap r))
                        γ
                        ((2 : ℝ) • x n - y n)
                      =
                    P[affineFiber ContinuousLinearMap.sumCoordinateMap r,
                      affineFiberSumCoordinateMapChebyshev hm r]
                      ((2 : ℝ) • x n - y n) := by
                  simpa [hC_set, hC_cheb] using
                    resolventMap_normalConeAffine_eq_projectionPoint
                      (C := C)
                      (hC_nonempty := hC_nonempty)
                      (hC_closed := hC_closed)
                      (hNC := Set.normalCone_isMaximallyMonotone hC_nonempty hC_closed C.convex)
                      (hC := hC_cheb)
                      (γ := γ)
                      ((2 : ℝ) • x n - y n)
                rw [hxProd, hprojEq, hreflProj]
                abel_nf
        _ = y (n + 1) := hySucc.symm

/-- The source projected family `p` agrees with the canonical projected sequence from Corollary
28.4 for the finite-family linear constraint problem. -/
theorem p_eq_finiteFamilyLinearConstraintProjectedSequence
    (hm : 0 < m)
    (hOrbit :
      IsFiniteFamilyLinearConstraintDouglasRachfordOrbit f hf r lam γ y0 u v p x y) :
    p = finiteFamilyLinearConstraintProjectedSequence f hf hm r γ lam y0 := by
  -- Compare the source projected family with the canonical affine-correction formula.
  funext n
  apply Subtype.ext
  funext i
  calc
    p n i = y n i + (m : ℝ)⁻¹ • (r - ∑ j : Fin m, y n j) := by
      rw [hOrbit.p_eq n i, hOrbit.u_eq n]
    _ =
        finiteFamilyLinearConstraintIteration f hf hm r γ lam y0 n i +
          (m : ℝ)⁻¹ •
            (r - ∑ j : Fin m, finiteFamilyLinearConstraintIteration f hf hm r γ lam y0 n j) := by
              rw [hOrbit.y_eq_finiteFamilyLinearConstraintIteration hm]
    _ = finiteFamilyLinearConstraintProjectedSequence f hf hm r γ lam y0 n i := by
          symm
          exact finiteFamilyLinearConstraintProjectedSequence_apply_eq_affineCorrection
            f hf hm r γ lam y0 n i

end IsFiniteFamilyLinearConstraintDouglasRachfordOrbit

section

omit [CompleteSpace H]

/-- Helper for Example 28.5: weak convergence in the product space implies weak convergence of
each coordinate sequence under coordinate evaluation. -/
theorem tendsto_toWeakSpace_coordinate_of_tendsto_toWeakSpaceProductSpace
    {zSeq : ℕ → ProductSpace} {z : ProductSpace}
    (hz :
      Tendsto (fun n ↦ toWeakSpace ℝ ProductSpace (zSeq n)) atTop
        (𝓝 (toWeakSpace ℝ ProductSpace z)))
    (i : Fin m) :
    Tendsto (fun n ↦ toWeakSpace ℝ H (zSeq n i)) atTop
      (𝓝 (toWeakSpace ℝ H (z i))) := by
  let evali : ProductSpace →L[ℝ] H := coordinateCLM i
  -- Map the product weak limit through the continuous coordinate evaluation map.
  have hmap :
      Tendsto
        (fun n ↦ WeakSpace.map evali (toWeakSpace ℝ ProductSpace (zSeq n)))
        atTop
        (𝓝 (WeakSpace.map evali (toWeakSpace ℝ ProductSpace z))) := by
    exact ((WeakSpace.map evali).continuous.tendsto
      (toWeakSpace ℝ ProductSpace z)).comp hz
  simpa [evali, WeakSpace.map_apply, coordinateCLM_apply] using hmap

end

/-- Canonical bridge for Example 28.5: the source constraint
`{z | ∑ i, z i = r}` and strong-relative-interior hypothesis are expressed through
`affineFiber ContinuousLinearMap.sumCoordinateMap r` and
`ContinuousLinearMap.sumCoordinateMap '' effectiveDomain (directSumFunction f)`. Under the
componentwise Douglas--Rachford recursion `(28.23)`, there exists a constrained minimizer `pbar`
such that each coordinate sequence `(p n i)` converges weakly to `pbar i`. -/
theorem
    finiteFamilyLinearConstraintDouglasRachford_exists_componentwise_weakLimit_mem_argmin_canonical
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H)
    (hargmin :
      (Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap r]
        (directSumFunction f).asEReal).Nonempty)
    (hsri : r ∈ sri (ContinuousLinearMap.sumCoordinateMap '' effectiveDomain (directSumFunction f)))
    (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : ProductSpace)
    {u v : ℕ → H} {p x y : ℕ → ProductSpace}
    (hOrbit :
      IsFiniteFamilyLinearConstraintDouglasRachfordOrbit f hf r lam γ y0 u v p x y) :
    ∃ pbar ∈ Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap r]
        (directSumFunction f).asEReal,
      ∀ i : Fin m,
        Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (p n i)) atTop
          (𝓝 (toWeakSpace ℝ H (pbar i))) := by
  -- Apply the canonical Corollary 28.4 convergence theorem once, then project coordinatewise.
  obtain ⟨pbar, hpbar, hpbar_tendsto⟩ :=
    linearFiberDouglasRachford_exists_weakLimit_mem_argmin
      (hf := directSumFunction_mem_gammaZero_of_forall_mem_gammaZero f hf)
      ContinuousLinearMap.sumCoordinateMap
      r
      (familySizePosReal hm)
      ContinuousLinearMap.sumCoordinateMap_comp_adjoint_eq_card_smul_id
      hsri
      hargmin
      lam
      hlam
      hdiv
      γ
      y0
  refine ⟨pbar, hpbar, ?_⟩
  intro i
  have hpweakProd :
      Tendsto
        (fun n : ℕ ↦
          toWeakSpace ℝ ProductSpace
            (finiteFamilyLinearConstraintProjectedSequence f hf hm r γ lam y0 n))
        atTop
        (𝓝 (toWeakSpace ℝ ProductSpace pbar)) := by
    simpa using hpbar_tendsto
  have hpweakProd_orbit :
      Tendsto
        (fun n : ℕ ↦ toWeakSpace ℝ ProductSpace (p n))
        atTop
        (𝓝 (toWeakSpace ℝ ProductSpace pbar)) := by
    rw [hOrbit.p_eq_finiteFamilyLinearConstraintProjectedSequence hm]
    exact hpweakProd
  simpa using
    tendsto_toWeakSpace_coordinate_of_tendsto_toWeakSpaceProductSpace hpweakProd_orbit i

/-- Example 28.5: the source states this finite-family Douglas--Rachford specialization for
`m ≥ 2`; the linear-fiber specialization used here needs only the induced positivity `0 < m`.
Let `f : Fin m → Γ₀(H)` represent the source family `(f_i)_{i ∈ {1, …, m}}`, let `r ∈ H`,
assume the constrained minimization problem for `∑ i, f i` over the affine set
`{x | ∑ i, x i = r}` has a solution, and assume
`r ∈ sri {∑ i, x i | ∀ i, x i ∈ effectiveDomain (f i)}`. Let `lam` take values in `[0, 2]`
with `∑ λ_n (2 - λ_n) = +∞`, let `γ ∈ ℝ_{++}`, and let `u`, `v`, `p`, `x`, and `y` satisfy the
componentwise recursion `(28.23)` from `y0`. Then there exists a solution family `pbar` of the
constrained problem such that, for every `i`, the sequence `(p n i)` converges weakly to
`pbar i`. -/
theorem finiteFamilyLinearConstraintDouglasRachford_exists_componentwise_weakLimit_mem_argmin
    (f : Fin m → H → Set.Ioi (⊥ : EReal))
    (hf : ∀ i : Fin m, f i ∈ Γ₀(H))
    (hm : 0 < m) (r : H)
    (hargmin :
      (Argmin[{z : ProductSpace | ∑ i : Fin m, z i = r}] (directSumFunction f).asEReal).Nonempty)
    (hsri :
      r ∈ sri {s : H |
        ∃ z : ProductSpace,
          (∀ i : Fin m, z i ∈ effectiveDomain (f i)) ∧
            (∑ i : Fin m, z i) = s})
    (lam : ℕ → ℝ) (hlam : ∀ n : ℕ, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N : ℕ ↦
          (Finset.range N).sum
            (fun n : ℕ ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : ProductSpace)
    {u v : ℕ → H} {p x y : ℕ → ProductSpace}
    (hOrbit :
      IsFiniteFamilyLinearConstraintDouglasRachfordOrbit f hf r lam γ y0 u v p x y) :
    ∃ pbar ∈ Argmin[{z : ProductSpace | ∑ i : Fin m, z i = r}] (directSumFunction f).asEReal,
      ∀ i : Fin m,
        Tendsto (fun n : ℕ ↦ toWeakSpace ℝ H (p n i)) atTop
          (𝓝 (toWeakSpace ℝ H (pbar i))) := by
  have hargmin' :
      (Argmin[affineFiber ContinuousLinearMap.sumCoordinateMap r]
        (directSumFunction f).asEReal).Nonempty := by
    rw [argmin_affineFiber_sumCoordinateMap_eq f r]
    exact hargmin
  have hsri' :
      r ∈ sri (ContinuousLinearMap.sumCoordinateMap '' effectiveDomain (directSumFunction f)) := by
    rw [sumCoordinateMap_image_effectiveDomain_directSumFunction_eq f]
    exact hsri
  simpa [argmin_affineFiber_sumCoordinateMap_eq] using
    finiteFamilyLinearConstraintDouglasRachford_exists_componentwise_weakLimit_mem_argmin_canonical
      f hf hm r hargmin' hsri' lam hlam hdiv γ y0 hOrbit

end DouglasRachfordFiniteFamilyLinearConstraint

end

end ERealFunction
