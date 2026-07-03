import Mathlib
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Defs

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_5_extra_1 (from Chap01/Sec01_05) -/
open scoped Manifold

noncomputable section

universe u

-- Semantic search tooling was unavailable in this environment; this file follows the local
-- `LeeBoundaryModelSpace` precedent already used in Proposition 1.38.

/-- Lee's model upper half-space `H^n`: in dimension `0` this is `ℝ^0`, and in positive
dimensions it is mathlib's Euclidean half-space. -/
abbrev LeeBoundaryModelSpace : ℕ → Type
  | 0 => EuclideanSpace ℝ (Fin 0)
  | n + 1 => EuclideanHalfSpace (n + 1)

scoped[Manifold] notation "ℍ^{" n:max "}" => LeeBoundaryModelSpace n

/-- The source's model upper half-space carries the natural topology inherited from its
two cases. -/
instance leeBoundaryModelSpaceTopologicalSpace (n : ℕ) :
    TopologicalSpace (ℍ^{n}) := by
  cases n with
  | zero => infer_instance
  | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      change TopologicalSpace (EuclideanHalfSpace (n + 1))
      infer_instance

/-- Lee's model with corners for a topological manifold with boundary: in dimension `0` this is
the Euclidean model `𝓡 0`, and in positive dimensions it is the half-space model `𝓡∂ (n + 1)`. -/
abbrev leeBoundaryModelWithCorners :
    (n : ℕ) → ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (LeeBoundaryModelSpace n)
  | 0 => 𝓡 0
  | n + 1 => 𝓡∂ (n + 1)

/-- Lee's model upper half-space is Hausdorff in every dimension. -/
instance leeBoundaryModelSpaceT2Space (n : ℕ) :
    T2Space (ℍ^{n}) := by
  cases n with
  | zero =>
      simpa [LeeBoundaryModelSpace] using
        (inferInstance : T2Space (EuclideanSpace ℝ (Fin 0)))
  | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      simpa [LeeBoundaryModelSpace, EuclideanHalfSpace] using
        (inferInstance : T2Space { x : EuclideanSpace ℝ (Fin (n + 1)) // 0 ≤ x 0 })

/-- Lee's model upper half-space is second countable in every dimension. -/
instance leeBoundaryModelSpaceSecondCountableTopology (n : ℕ) :
    SecondCountableTopology (ℍ^{n}) := by
  cases n with
  | zero =>
      simpa [LeeBoundaryModelSpace] using
        (inferInstance : SecondCountableTopology (EuclideanSpace ℝ (Fin 0)))
  | succ n =>
      let _ : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      simpa [LeeBoundaryModelSpace, EuclideanHalfSpace] using
        (inferInstance :
          SecondCountableTopology { x : EuclideanSpace ℝ (Fin (n + 1)) // 0 ≤ x 0 })

/-- Lee's model upper half-space carries its canonical self-charted-space structure. -/
instance leeBoundaryModelSpaceChartedSpace (n : ℕ) :
    ChartedSpace (ℍ^{n}) (ℍ^{n}) :=
  chartedSpaceSelf _

/-- Definition 1.5-extra-1: An `n`-dimensional topological manifold with boundary is a
second-countable Hausdorff charted space modelled on Lee's upper half-space `ℍ^n`, together with
the corresponding canonical `C^0` manifold structure. -/
class TopologicalManifoldWithBoundary (n : ℕ) (M : Type u)
    [TopologicalSpace M] extends
    T2Space M, SecondCountableTopology M, ChartedSpace (ℍ^{n}) M,
    IsManifold (leeBoundaryModelWithCorners n) 0 M

attribute [instance] TopologicalManifoldWithBoundary.toT2Space
attribute [instance] TopologicalManifoldWithBoundary.toSecondCountableTopology
attribute [instance] TopologicalManifoldWithBoundary.toIsManifold

instance instChartedSpaceOfTopologicalManifoldWithBoundaryZero (M : Type u)
    [TopologicalSpace M] [h : TopologicalManifoldWithBoundary 0 M] :
    ChartedSpace (ℍ^{0}) M :=
  h.toChartedSpace

instance instChartedSpaceOfTopologicalManifoldWithBoundarySucc (n : ℕ) (M : Type u)
    [TopologicalSpace M] [h : TopologicalManifoldWithBoundary (n + 1) M] :
    ChartedSpace (LeeBoundaryModelSpace (n + 1)) M :=
  h.toChartedSpace

/-- The model upper half-space is itself a topological manifold with boundary. -/
instance instTopologicalManifoldWithBoundaryLeeBoundaryModelSpace (n : ℕ) :
    TopologicalManifoldWithBoundary n (ℍ^{n}) where
  toT2Space := leeBoundaryModelSpaceT2Space n
  toSecondCountableTopology := leeBoundaryModelSpaceSecondCountableTopology n
  toChartedSpace := leeBoundaryModelSpaceChartedSpace n
  toIsManifold := inferInstance

/-! ### Example_1_5 (from Chap01/Sec01) -/
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

/-! ### Problem_1_5 (from Chap01/Sec01_07) -/
universe u

open Set TopologicalSpace

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Helper for Problem 1-5: if every connected component is `σ`-compact and the quotient of
components is countable, then the whole space is `σ`-compact. -/
theorem sigmaCompactSpace_of_countable_sigmaCompact_connectedComponents
    {M : Type u} [TopologicalSpace M]
    (hcount : Countable (ConnectedComponents M))
    (hcomponent : ∀ x : M, IsSigmaCompact (connectedComponent x : Set M)) :
    SigmaCompactSpace M := by
  -- Assemble the space as a countable union of the fibers of the quotient to connected components.
  rw [← isSigmaCompact_univ_iff]
  letI : Countable (ConnectedComponents M) := hcount
  have hunion :
      IsSigmaCompact
        (⋃ c : ConnectedComponents M, ((↑) ⁻¹' ({c} : Set (ConnectedComponents M)) : Set M)) := by
    -- Each fiber is one connected component, so the countable union is `σ`-compact.
    refine isSigmaCompact_iUnion
      (fun c : ConnectedComponents M ↦
        ((↑) ⁻¹' ({c} : Set (ConnectedComponents M)) : Set M))
      ?_
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    simpa [connectedComponents_preimage_singleton] using hcomponent x
  have huniv :
      (⋃ c : ConnectedComponents M, ((↑) ⁻¹' ({c} : Set (ConnectedComponents M)) : Set M)) =
        (univ : Set M) := by
    -- Every point lies in the fiber of its own connected component.
    ext x
    simp
  simpa [huniv] using hunion

/-- Helper for Problem 1-5: in a relation with finitely many outgoing neighbors from each vertex,
the vertices reachable from a fixed root form a countable set. -/
theorem countable_reachable_of_finite_neighbors
    {ι : Type*} (R : ι → ι → Prop) (i₀ : ι)
    (hfinite : ∀ i, {j | R i j}.Finite) :
    {j | Relation.ReflTransGen R i₀ j}.Countable := by
  classical
  let layer : ℕ → Set ι :=
    Nat.rec ({i₀} : Set ι) fun _ s ↦ ⋃ i ∈ s, {j | R i j}
  have hlayer_finite : ∀ n, (layer n).Finite := by
    intro n
    induction n with
    | zero =>
        -- The zeroth layer contains only the root.
        simp [layer]
    | succ n ih =>
        -- The next layer is a finite union of finite neighbor sets.
        simpa [layer] using
          Set.Finite.biUnion ih fun i _ ↦ hfinite i
  have hsubset :
      {j | Relation.ReflTransGen R i₀ j} ⊆ ⋃ n, layer n := by
    intro j hj
    -- Any reachability proof has a finite length, so `j` lies in some layer.
    induction hj with
    | refl =>
        exact mem_iUnion.2 ⟨0, by simp [layer]⟩
    | @tail b c hbc hR ih =>
        rcases mem_iUnion.1 ih with ⟨n, hn⟩
        exact mem_iUnion.2 ⟨n + 1, mem_iUnion₂.2 ⟨b, hn, hR⟩⟩
  -- Countable union of finite layers gives the countability of the reachable set.
  exact (Set.countable_iUnion fun n ↦ (hlayer_finite n).countable).mono hsubset

/-- Helper for Problem 1-5: a connected space with a locally finite open cover by sets with
compact closure admits a countable subcover. -/
theorem countable_subcover_of_connected_from_locallyFinite_precompact_cover
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X]
    {ι : Type*} (U : ι → Set X) (hU_open : ∀ i, IsOpen (U i))
    (hU_cover : ⋃ i, U i = univ) (hU_locallyFinite : LocallyFinite U)
    (hU_compactClosure : ∀ i, IsCompact (closure (U i))) :
    ∃ s : Set ι, s.Countable ∧ ⋃ i ∈ s, U i = univ := by
  classical
  let R : ι → ι → Prop := fun i j ↦ (U i ∩ U j).Nonempty
  let x₀ : X := Classical.choice inferInstance
  obtain ⟨i₀, hx₀⟩ : ∃ i : ι, x₀ ∈ U i := by
    exact iUnion_eq_univ_iff.mp hU_cover x₀
  have hfinite_neighbors : ∀ i, {j | R i j}.Finite := by
    intro i
    -- Local finiteness around the compact closure of `U i` leaves only finitely many overlaps.
    refine (hU_locallyFinite.finite_nonempty_inter_compact (hU_compactClosure i)).subset ?_
    intro j hj
    rcases hj with ⟨x, hxUi, hxUj⟩
    exact ⟨x, hxUj, subset_closure hxUi⟩
  let s : Set ι := {j | Relation.ReflTransGen R i₀ j}
  have hs_countable : s.Countable :=
    countable_reachable_of_finite_neighbors R i₀ hfinite_neighbors
  have hi₀ : i₀ ∈ s := Relation.ReflTransGen.refl
  have hsubcover : ⋃ i ∈ s, U i = univ := by
    let A : Set X := ⋃ i ∈ s, U i
    have hA_open : IsOpen A := by
      -- The union over the reachable indices is open because each cover member is open.
      simpa [A] using isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ hU_open i
    have hA_nonempty : A.Nonempty := by
      -- The root cover element lies in the reachable union.
      refine ⟨x₀, ?_⟩
      exact mem_iUnion₂.2 ⟨i₀, hi₀, hx₀⟩
    have hA_compl_open : IsOpen Aᶜ := by
      -- Any cover set meeting the reachable union is itself reachable, so the complement is open.
      rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨j, hyj⟩ : ∃ j : ι, y ∈ U j := by
        exact iUnion_eq_univ_iff.mp hU_cover y
      refine Filter.mem_of_superset ((hU_open j).mem_nhds hyj) ?_
      intro z hzj
      rw [mem_compl_iff]
      intro hzA
      rcases mem_iUnion₂.1 hzA with ⟨k, hk, hzk⟩
      have hj_reachable : Relation.ReflTransGen R i₀ j :=
        Relation.ReflTransGen.tail hk ⟨z, hzk, hzj⟩
      exact hy <| mem_iUnion₂.2 ⟨j, hj_reachable, hyj⟩
    have hA_clopen : IsClopen A := ⟨isOpen_compl_iff.mp hA_compl_open, hA_open⟩
    -- A nonempty clopen set in a connected space must be all of `X`.
    exact IsClopen.eq_univ hA_clopen hA_nonempty
  exact ⟨s, hs_countable, hsubcover⟩

/-- Helper for Problem 1-5: every connected paracompact locally compact Hausdorff space is
`σ`-compact. -/
theorem sigmaCompactSpace_of_connected_paracompact_locallyCompact_t2
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
    [ParacompactSpace X] [LocallyCompactSpace X] :
    SigmaCompactSpace X := by
  classical
  choose W hW_open hxW hW_compact using
    fun x : X ↦ exists_isOpen_mem_isCompact_closure x
  -- Refine the pointwise precompact neighborhood cover to a locally finite one.
  obtain ⟨V, hV_open, hV_cover, hV_locallyFinite, hV_subset⟩ :=
    precise_refinement W hW_open (iUnion_eq_univ_iff.2 fun x ↦ ⟨x, hxW x⟩)
  have hV_compact : ∀ x, IsCompact (closure (V x)) := by
    intro x
    -- Compactness is preserved because `closure (V x)` sits inside `closure (W x)`.
    exact (hW_compact x).of_isClosed_subset isClosed_closure (closure_mono (hV_subset x))
  obtain ⟨s, hs_countable, hs_cover⟩ :=
    countable_subcover_of_connected_from_locallyFinite_precompact_cover
      V hV_open hV_cover hV_locallyFinite hV_compact
  -- The compact closures of the countable subcover cover the whole space.
  refine SigmaCompactSpace.of_countable ((fun i ↦ closure (V i)) '' s) (hs_countable.image _) ?_ ?_
  · intro K hK
    rcases hK with ⟨i, hi, rfl⟩
    exact hV_compact i
  · ext x
    constructor
    · intro _
      simp
    · intro _
      have hxcover : x ∈ ⋃ i ∈ s, V i := by
        simp [hs_cover]
      rcases mem_iUnion.1 hxcover with ⟨i, hxi⟩
      rcases mem_iUnion.1 hxi with ⟨hi, hxVi⟩
      exact mem_sUnion.2 ⟨closure (V i), mem_image_of_mem _ hi, subset_closure hxVi⟩

/-- Helper for Problem 1-5: in a paracompact Hausdorff space locally modelled on `ℝ^n`, each
connected component is `σ`-compact. -/
theorem isSigmaCompact_connectedComponent_of_paracompact_t2_euclidean
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [ParacompactSpace M] [LocallyCompactSpace M] [LocallyConnectedSpace M] (x : M) :
    IsSigmaCompact (connectedComponent x : Set M) := by
  -- Route correction: work on the subtype `connectedComponent x`, where connectedness is built in,
  -- and apply the general connected-paracompact-locally-compact `σ`-compactness theorem.
  rw [isSigmaCompact_iff_sigmaCompactSpace]
  letI : ConnectedSpace (connectedComponent x) :=
    Subtype.connectedSpace isConnected_connectedComponent
  letI : ParacompactSpace (connectedComponent x) :=
    (isClosed_connectedComponent (x := x)).isClosedEmbedding_subtypeVal.paracompactSpace
  letI : LocallyCompactSpace (connectedComponent x) :=
    (isClosed_connectedComponent (x := x)).isClosedEmbedding_subtypeVal.locallyCompactSpace
  exact sigmaCompactSpace_of_connected_paracompact_locallyCompact_t2

/-- Problem 1-5: a Hausdorff space locally modelled on `ℝ^n` is second-countable if and only if it
is paracompact and has countably many connected components. Under these ambient hypotheses, this is
equivalently the condition for Lee's `TopologicalManifold` owner abstraction. -/
-- Proof sketch: if `M` is a topological manifold, then `Theorem_1_15` gives paracompactness and
-- `Proposition_1_11` gives countably many connected components. Conversely, connected components
-- are open in the locally connected space induced from the Euclidean chart model; under
-- paracompactness each connected component is `σ`-compact, so countably many components make `M`
-- `σ`-compact. Apply `Problem_1_3` to identify `σ`-compactness with `TopologicalManifold n M`.
theorem secondCountableTopology_iff_paracompact_and_countable_components_of_t2_euclidean
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] :
    SecondCountableTopology M ↔ ParacompactSpace M ∧ Countable (ConnectedComponents M) := by
  constructor
  · intro hM
    letI : SecondCountableTopology M := hM
    letI : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    letI : LocallyConnectedSpace M :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
    constructor
    · -- Combine local compactness with second countability to get `σ`-compactness, hence
      -- paracompactness in the Hausdorff setting.
      letI : SigmaCompactSpace M := sigmaCompactSpace_of_locallyCompact_secondCountable
      infer_instance
    · -- The connected-components quotient is discrete and Lindelöf, hence countable.
      letI : LindelofSpace M := inferInstance
      letI : DiscreteTopology (ConnectedComponents M) := inferInstance
      letI : LindelofSpace (ConnectedComponents M) :=
        LindelofSpace.of_continuous_surjective ConnectedComponents.continuous_coe
          ConnectedComponents.surjective_coe
      exact countable_of_Lindelof_of_discrete
  · rintro ⟨hparacompact, hcount⟩
    letI : ParacompactSpace M := hparacompact
    letI : LocallyCompactSpace M :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
    letI : LocallyConnectedSpace M :=
      ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
    have hcomponent :
        ∀ x : M, IsSigmaCompact (connectedComponent x : Set M) := by
      -- Reduce the reverse implication to the componentwise `σ`-compactness statement.
      intro x
      exact isSigmaCompact_connectedComponent_of_paracompact_t2_euclidean (n := n) x
    letI : SigmaCompactSpace M :=
      sigmaCompactSpace_of_countable_sigmaCompact_connectedComponents hcount hcomponent
    -- A `σ`-compact Hausdorff Euclidean charted space is second-countable.
    exact ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin n)) M
