import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Defs

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Projectivization
open scoped LinearAlgebra.Projectivization Manifold

/-- The real projective space `ℝPⁿ`, realized as the projectivization of `ℝ^(n+1)`. -/
abbrev RealProjectiveSpace (n : ℕ) :=
  ℙ ℝ (EuclideanSpace ℝ (Fin (n + 1)))

notation "ℝP[" n "]" => RealProjectiveSpace n

/-- The quotient topology on `ℝPⁿ` inherited from the projectivization construction. -/
instance realProjectiveSpaceTopologicalSpace (n : ℕ) :
    TopologicalSpace (ℝP[n]) :=
  inferInstanceAs
    (TopologicalSpace (Quotient
      (projectivizationSetoid ℝ (EuclideanSpace ℝ (Fin (n + 1))))))

/-- The standard affine chart domain `U_i` in `ℝPⁿ`, consisting of lines with nonzero `i`th
homogeneous coordinate. -/
private def realProjectiveChartDomainPred {n : ℕ} (i : Fin (n + 1)) :
    { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 } → Prop :=
  fun v ↦ v.1 i ≠ 0

private theorem realProjectiveChartDomainPred_smul {n : ℕ} (i : Fin (n + 1))
    (a b : { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 }) (t : ℝ)
    (h : a = t • (b : EuclideanSpace ℝ (Fin (n + 1)))) :
    realProjectiveChartDomainPred i a = realProjectiveChartDomainPred i b := by
  -- The common scale factor cannot vanish because `a` is nonzero.
  have ht : t ≠ 0 := by
    intro ht
    apply a.2
    rw [h, ht, zero_smul]
  have hcoord : a.1 i = t * b.1 i := by
    simpa [Pi.smul_apply] using congrArg (fun v ↦ v i) h
  dsimp [realProjectiveChartDomainPred]
  exact propext ⟨fun ha hb ↦ ha <| by rw [hcoord, hb, mul_zero], fun hb ↦ by
    rw [hcoord]
    exact mul_ne_zero ht hb⟩

def realProjectiveChartDomain (n : ℕ) (i : Fin (n + 1)) : Set (ℝP[n]) :=
  { x | Projectivization.lift (realProjectiveChartDomainPred i)
      (realProjectiveChartDomainPred_smul i) x }

private def realProjectiveAffineCoordinates {n : ℕ} (i : Fin (n + 1)) :
    { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 } → EuclideanSpace ℝ (Fin n) :=
  fun v ↦ WithLp.toLp 2 (fun j ↦ v.1 (i.succAbove j) / v.1 i)

private theorem realProjectiveAffineCoordinates_smul {n : ℕ} (i : Fin (n + 1))
    (a b : { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 }) (t : ℝ)
    (h : a = t • (b : EuclideanSpace ℝ (Fin (n + 1)))) :
    realProjectiveAffineCoordinates i a = realProjectiveAffineCoordinates i b := by
  -- The affine coordinates are unchanged after canceling the common nonzero scale factor.
  have ht : t ≠ 0 := by
    intro ht
    apply a.2
    rw [h, ht, zero_smul]
  apply WithLp.ofLp_injective
  funext j
  have hnum : a.1 (i.succAbove j) = t * b.1 (i.succAbove j) := by
    simpa [Pi.smul_apply] using congrArg (fun v ↦ v (i.succAbove j)) h
  have hden : a.1 i = t * b.1 i := by
    simpa [Pi.smul_apply] using congrArg (fun v ↦ v i) h
  by_cases hb0 : b.1 i = 0
  · have ha0 : a.1 i = 0 := by rw [hden, hb0, mul_zero]
    simp [realProjectiveAffineCoordinates, hden, hb0, ha0]
  · simp [realProjectiveAffineCoordinates, hnum, hden]
    simpa using mul_div_mul_left (b.1 (i.succAbove j)) (b.1 i) ht

private def realProjectiveChartToFun (n : ℕ) (i : Fin (n + 1)) :
    ℝP[n] → EuclideanSpace ℝ (Fin n) :=
  Projectivization.lift (realProjectiveAffineCoordinates i)
    (realProjectiveAffineCoordinates_smul i)

/-- On a homogeneous representative, the affine chart domain condition is the nonvanishing of the
`i`th coordinate. -/
@[simp] theorem realProjectiveChartDomain_mk (n : ℕ) (i : Fin (n + 1))
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ≠ 0) :
    mk ℝ v hv ∈ realProjectiveChartDomain n i ↔ v i ≠ 0 := by
  simp [realProjectiveChartDomain, realProjectiveChartDomainPred]

/-- On a homogeneous representative, the affine chart map is given by the standard coordinate
ratios. -/
@[simp] theorem realProjectiveChartToFun_mk (n : ℕ) (i : Fin (n + 1))
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ≠ 0) :
    realProjectiveChartToFun n i (mk ℝ v hv) =
      WithLp.toLp 2 (fun j ↦ v (i.succAbove j) / v i) := by
  simp [realProjectiveChartToFun, realProjectiveAffineCoordinates]

/-- The homogeneous vector obtained from affine coordinates by inserting `1` in the `i`th slot. -/
def realProjectiveChartInvVector (n : ℕ) (i : Fin (n + 1)) (u : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.insertNth i (1 : ℝ) u)

-- Proof sketch: the inserted homogeneous vector has `i`th coordinate equal to `1`, so it cannot
-- be the zero vector.
/-- The homogeneous coordinates obtained by inserting `1` in the `i`th slot define a nonzero
vector. -/
theorem realProjectiveChartInvVector_ne_zero (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) :
    realProjectiveChartInvVector n i u ≠ 0 := by
  -- The inserted representative has `1` in the distinguished coordinate.
  intro hzero
  have hi : WithLp.ofLp (realProjectiveChartInvVector n i u) i = (1 : ℝ) := by
    simp [realProjectiveChartInvVector]
  have h0i : WithLp.ofLp (realProjectiveChartInvVector n i u) i = 0 := by
    simpa [hzero]
  exact one_ne_zero (hi.symm.trans h0i)

-- Proof sketch: evaluate the chosen representative `realProjectiveChartInvVector n i u` at the
-- distinguished index `i`; the value is `1`, so the corresponding projective point lies in `U_i`.
/-- The explicit inverse chart lands in the standard affine domain `U_i`. -/
theorem realProjectiveChartInv_mem_domain (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) :
    mk ℝ (realProjectiveChartInvVector n i u)
      (realProjectiveChartInvVector_ne_zero n i u) ∈ realProjectiveChartDomain n i := by
  -- The inserted representative lies in the chart domain because its `i`th coordinate is `1`.
  rw [realProjectiveChartDomain_mk]
  simp [realProjectiveChartInvVector]

private def realProjectiveChartInv (n : ℕ) (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) → ℝP[n] :=
  fun u ↦
    mk ℝ (realProjectiveChartInvVector n i u)
      (realProjectiveChartInvVector_ne_zero n i u)

private def realProjectiveChartInvToDomain (n : ℕ) (i : Fin (n + 1)) :
    EuclideanSpace ℝ (Fin n) → realProjectiveChartDomain n i :=
  fun u ↦ ⟨realProjectiveChartInv n i u, realProjectiveChartInv_mem_domain n i u⟩

-- Proof sketch: `realProjectiveChartDomain n i` is defined by the quotient-invariant predicate
-- that the `i`th homogeneous coordinate is nonzero, so it is the preimage of `{t : ℝ | t ≠ 0}`
-- under the induced coordinate function on projective space.
/-- The standard affine chart domain `U_i` is open in `ℝPⁿ`. -/
theorem realProjectiveChartDomain_isOpen (n : ℕ) (i : Fin (n + 1)) :
    IsOpen (realProjectiveChartDomain n i) := by
  let q : { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 } → ℝP[n] := Projectivization.mk' ℝ
  have hq : Topology.IsQuotientMap q := by
    simpa [q, Projectivization.mk'] using
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap
          (@Quotient.mk'
            { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 }
            (projectivizationSetoid ℝ (EuclideanSpace ℝ (Fin (n + 1))))))
  have hpre :
      q ⁻¹' realProjectiveChartDomain n i =
        { v : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 } | v.1 i ≠ 0 } := by
    ext v
    simp [q, realProjectiveChartDomain, realProjectiveChartDomainPred, Projectivization.mk'_eq_mk]
  have hopen :
      IsOpen { v : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 } | v.1 i ≠ 0 } := by
    have hcoord :
        Continuous fun v : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 } ↦ v.1 i := by
      have hOfLp :
          Continuous
            (WithLp.ofLp : EuclideanSpace ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ)) :=
        PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) ↦ ℝ)
      exact
        ((continuous_apply i).comp hOfLp).comp continuous_subtype_val
    simpa using hcoord.isOpen_preimage _ (isOpen_ne (x := (0 : ℝ)))
  have hpreOpen : IsOpen (q ⁻¹' realProjectiveChartDomain n i) := by
    rwa [hpre]
  exact hq.isOpen_preimage.mp hpreOpen

-- Proof sketch: compute the homogeneous coordinates of `realProjectiveChartInv n i u`; after
-- dividing by the inserted `1`, the resulting affine coordinates are exactly `u`.
private theorem realProjectiveChart_left_inv (n : ℕ) (i : Fin (n + 1)) :
    Function.LeftInverse (realProjectiveChartInvToDomain n i)
      ((realProjectiveChartDomain n i).restrict (realProjectiveChartToFun n i)) := by
  -- Route correction: this is the hard normalization step on projective space, not the easy
  -- `[u,1]` computation.
  intro x
  apply Subtype.ext
  change realProjectiveChartInv n i (realProjectiveChartToFun n i x.1) = x.1
  have hxi : x.1.rep i ≠ 0 := by
    have hrep_mem : mk ℝ x.1.rep x.1.rep_nonzero ∈ realProjectiveChartDomain n i := by
      simpa [x.1.mk_rep] using x.2
    exact (realProjectiveChartDomain_mk n i x.1.rep x.1.rep_nonzero).1 hrep_mem
  have hchart :
      realProjectiveChartToFun n i x.1 =
        WithLp.toLp 2 (fun j ↦ x.1.rep (i.succAbove j) / x.1.rep i) := by
    simpa [x.1.mk_rep] using realProjectiveChartToFun_mk n i x.1.rep x.1.rep_nonzero
  rw [← x.1.mk_rep]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ (realProjectiveChartInvVector_ne_zero n i _) x.1.rep_nonzero).2
  refine ⟨(x.1.rep i)⁻¹, ?_⟩
  apply WithLp.ofLp_injective
  funext k
  by_cases hk : k = i
  · subst hk
    simp [realProjectiveChartInv, realProjectiveChartInvVector, hchart, hxi]
  · rcases Fin.exists_succAbove_eq hk with ⟨j, rfl⟩
    simp [realProjectiveChartInv, realProjectiveChartInvVector, hchart, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc]

-- Proof sketch: normalize a representative of a point in `U_i` by dividing all coordinates by the
-- nonzero `i`th coordinate, then compare projective classes using scale invariance.
private theorem realProjectiveChart_right_inv (n : ℕ) (i : Fin (n + 1)) :
    Function.RightInverse (realProjectiveChartInvToDomain n i)
      ((realProjectiveChartDomain n i).restrict (realProjectiveChartToFun n i)) := by
  -- Route correction: this is the easy computation on the affine slice `[u,1]`.
  intro u
  apply WithLp.ofLp_injective
  funext j
  simp [realProjectiveChartInvToDomain, realProjectiveChartInv, realProjectiveChartInvVector,
    realProjectiveChartToFun, realProjectiveAffineCoordinates]

private theorem realProjectiveChartToFun_continuousOn (n : ℕ) (i : Fin (n + 1)) :
    ContinuousOn (realProjectiveChartToFun n i) (realProjectiveChartDomain n i) := by
  rw [continuousOn_iff_continuous_restrict]
  let q : { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 } → ℝP[n] := Projectivization.mk' ℝ
  have hq : Topology.IsQuotientMap q := by
    simpa [q, Projectivization.mk'] using
      (isQuotientMap_quotient_mk' :
        Topology.IsQuotientMap
          (@Quotient.mk'
            { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 }
            (projectivizationSetoid ℝ (EuclideanSpace ℝ (Fin (n + 1))))))
  have hq' :
      Topology.IsQuotientMap ((realProjectiveChartDomain n i).restrictPreimage q) :=
    hq.restrictPreimage_isOpen (realProjectiveChartDomain_isOpen n i)
  refine (hq'.continuous_iff).2 ?_
  have hOfLp :
      Continuous
        (WithLp.ofLp : EuclideanSpace ℝ (Fin (n + 1)) → (Fin (n + 1) → ℝ)) :=
    PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) ↦ ℝ)
  have hToLp :
      Continuous
        (WithLp.toLp (p := (2 : ENNReal)) : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n ↦ ℝ)
  have hcomp :
      (realProjectiveChartDomain n i).restrict (realProjectiveChartToFun n i) ∘
          (realProjectiveChartDomain n i).restrictPreimage q =
        fun v : q ⁻¹' realProjectiveChartDomain n i ↦ realProjectiveAffineCoordinates i v.1 := by
    funext v
    simp [q, realProjectiveChartToFun, Projectivization.mk'_eq_mk]
  rw [hcomp]
  let s : Set { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 } := q ⁻¹' realProjectiveChartDomain n i
  have hvec :
      Continuous fun v : s ↦ (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1 :=
    continuous_subtype_val.comp continuous_subtype_val
  have hcoord :
      ∀ k : Fin (n + 1),
        Continuous
          (fun v : s ↦ (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1 k) := by
    intro k
    exact ((continuous_apply k).comp hOfLp).comp hvec
  have hden_ne : ∀ v : s, (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1 i ≠ 0 := by
    intro v
    have hmem : q v.1 ∈ realProjectiveChartDomain n i := v.2
    have hmem' :
        mk ℝ (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1
          (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).2 ∈ realProjectiveChartDomain n i := by
      simpa [q, Projectivization.mk'_eq_mk] using hmem
    exact
      (realProjectiveChartDomain_mk n i
        (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1
        (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).2).1 hmem'
  have hnum :
      ∀ j : Fin n,
        Continuous
          (fun v : s ↦
            (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1 (i.succAbove j)) := by
    intro j
    exact hcoord (i.succAbove j)
  have hden :
      Continuous fun v : s ↦ (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1 i := by
    exact hcoord i
  have hcoords :
      Continuous
        (fun v : s ↦
          fun j ↦
            (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1 (i.succAbove j) /
              (v.1 : { w : EuclideanSpace ℝ (Fin (n + 1)) // w ≠ 0 }).1 i) := by
    refine continuous_pi fun j ↦ ?_
    exact (hnum j).div hden fun v ↦ hden_ne v
  simpa [realProjectiveAffineCoordinates] using hToLp.comp hcoords

private theorem realProjectiveChartInv_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (realProjectiveChartInv n i) := by
  -- The inverse chart is the quotient of the continuous insertion map `u ↦ [u,1]`.
  let f : EuclideanSpace ℝ (Fin n) →
      { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 } := fun u ↦
        ⟨realProjectiveChartInvVector n i u, realProjectiveChartInvVector_ne_zero n i u⟩
  have hOfLp :
      Continuous (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ)) :=
    PiLp.continuous_ofLp (p := (2 : ENNReal)) (β := fun _ : Fin n ↦ ℝ)
  have hToLp :
      Continuous
        (WithLp.toLp (p := (2 : ENNReal)) :
          (Fin (n + 1) → ℝ) → EuclideanSpace ℝ (Fin (n + 1))) :=
    PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin (n + 1) ↦ ℝ)
  have hcoord :
      ∀ j : Fin n, Continuous fun u : EuclideanSpace ℝ (Fin n) ↦ u j := by
    intro j
    exact (continuous_apply j).comp hOfLp
  have hfvec :
      Continuous fun u : EuclideanSpace ℝ (Fin n) ↦
        @Fin.insertNth n (fun _ : Fin (n + 1) ↦ ℝ) i (1 : ℝ) (fun j : Fin n ↦ u j) := by
    exact
      continuous_const.finInsertNth i (continuous_pi fun j ↦ hcoord j)
  have hf : Continuous f := by
    exact (hToLp.comp hfvec).subtype_mk fun u ↦ realProjectiveChartInvVector_ne_zero n i u
  have hq :
      Continuous
        (Projectivization.mk' ℝ :
          { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 } → ℝP[n]) := by
    simpa [Projectivization.mk'] using
      (continuous_quotient_mk' :
        Continuous
          (@Quotient.mk'
            { v : EuclideanSpace ℝ (Fin (n + 1)) // v ≠ 0 }
            (projectivizationSetoid ℝ (EuclideanSpace ℝ (Fin (n + 1))))))
  have hmk :
      realProjectiveChartInv n i = Projectivization.mk' ℝ ∘ f := by
    funext u
    simp [realProjectiveChartInv, f, Projectivization.mk'_eq_mk]
  rw [hmk]
  exact hq.comp hf

/-- The standard affine chart on `ℝPⁿ` as an open partial homeomorphism. -/
noncomputable def realProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ℝP[n]) (EuclideanSpace ℝ (Fin n)) where
  toPartialEquiv :=
    { toFun := realProjectiveChartToFun n i
      invFun := realProjectiveChartInv n i
      source := realProjectiveChartDomain n i
      target := Set.univ
      map_source' := fun _ _ ↦ Set.mem_univ _
      map_target' := fun u _ ↦ realProjectiveChartInv_mem_domain n i u
      left_inv' := fun x hx ↦ by
        exact congrArg Subtype.val (realProjectiveChart_left_inv n i ⟨x, hx⟩)
      right_inv' := fun u _ ↦ by
        simpa [realProjectiveChartInvToDomain] using realProjectiveChart_right_inv n i u }
  open_source := realProjectiveChartDomain_isOpen n i
  open_target := isOpen_univ
  continuousOn_toFun := realProjectiveChartToFun_continuousOn n i
  continuousOn_invFun := (realProjectiveChartInv_continuous n i).continuousOn

/-- On a homogeneous representative, the standard affine chart is given by the standard coordinate
ratios. -/
@[simp] theorem realProjectiveChart_mk (n : ℕ) (i : Fin (n + 1))
    (v : EuclideanSpace ℝ (Fin (n + 1))) (hv : v ≠ 0) :
    realProjectiveChart n i (Projectivization.mk ℝ v hv) =
      WithLp.toLp 2 (fun j ↦ v (i.succAbove j) / v i) := by
  exact realProjectiveChartToFun_mk n i v hv

/-- The inverse chart is the homogeneous coordinate insertion `u ↦ [u,1]`. -/
@[simp] theorem realProjectiveChart_symm_apply (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) :
    (realProjectiveChart n i).symm u =
      mk ℝ (realProjectiveChartInvVector n i u)
        (realProjectiveChartInvVector_ne_zero n i u) := rfl

/-- The inverse chart lands in the standard affine domain `U_i`. -/
theorem realProjectiveChart_symm_mem_domain (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℝ (Fin n)) :
    (realProjectiveChart n i).symm u ∈ realProjectiveChartDomain n i :=
  realProjectiveChartInv_mem_domain n i u

-- Proof sketch: choose a nonzero representative of `x`; one of its `n + 1` coordinates is
-- nonzero, placing `x` in the corresponding standard affine chart domain.
/-- Example 1.5: every point of `ℝPⁿ` lies in the source of one of the standard affine charts,
equivalently in a chart whose coordinate map is a homeomorphism with `ℝⁿ`. -/
theorem real_projective_space_has_standard_chart (n : ℕ) (x : ℝP[n]) :
    ∃ i : Fin (n + 1), x ∈ realProjectiveChartDomain n i := by
  -- A nonzero representative has some nonzero homogeneous coordinate.
  classical
  by_contra hx
  push_neg at hx
  apply x.rep_nonzero
  ext i
  by_contra hi
  have hmem : mk ℝ x.rep x.rep_nonzero ∈ realProjectiveChartDomain n i := by
    exact (realProjectiveChartDomain_mk n i x.rep x.rep_nonzero).2 hi
  exact hx i <| by simpa [x.mk_rep] using hmem
