import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.ProperAction.Basic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Mathlib.Topology.Homeomorph.Defs

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Projectivization
open scoped LinearAlgebra.Projectivization Manifold ContDiff

instance (n : ℕ) : TopologicalSpace (ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))) :=
  inferInstanceAs
    (TopologicalSpace
      (Quotient (projectivizationSetoid ℂ (EuclideanSpace ℂ (Fin (n + 1))))))

/-- The complex projective space `ℂPⁿ`, realized as the projectivization of `ℂ^(n+1)`. -/
abbrev ComplexProjectiveSpace (n : ℕ) :=
  ℙ ℂ (EuclideanSpace ℂ (Fin (n + 1)))

notation "ℂP[" n "]" => ComplexProjectiveSpace n

/-- The standard affine chart domain `U_i` in `ℂPⁿ`, consisting of lines with nonzero `i`th
homogeneous coordinate. -/
private def complexProjectiveChartDomainPred {n : ℕ} (i : Fin (n + 1)) :
    { v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0 } → Prop :=
  fun v ↦ v.1 i ≠ 0

private theorem complexProjectiveChartDomainPred_smul {n : ℕ} (i : Fin (n + 1))
    (a b : { v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0 }) (t : ℂ)
    (h : a = t • (b : EuclideanSpace ℂ (Fin (n + 1)))) :
    complexProjectiveChartDomainPred i a = complexProjectiveChartDomainPred i b := by
  -- The scalar relating two representatives is nonzero because both representatives are nonzero.
  have ht : t ≠ 0 := by
    intro ht
    apply a.2
    rw [h, ht, zero_smul]
  -- Once `t ≠ 0`, the `i`th coordinate is nonzero on one representative iff it is nonzero on the other.
  apply propext
  change a.1 i ≠ 0 ↔ b.1 i ≠ 0
  rw [h]
  simp [complexProjectiveChartDomainPred, ht]

def complexProjectiveChartDomain (n : ℕ) (i : Fin (n + 1)) : Set (ℂP[n]) :=
  { x | Projectivization.lift (complexProjectiveChartDomainPred i)
      (complexProjectiveChartDomainPred_smul i) x }

private def complexProjectiveAffineCoordinates {n : ℕ} (i : Fin (n + 1)) :
    { v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0 } → EuclideanSpace ℂ (Fin n) :=
  fun v ↦
    (EuclideanSpace.equiv (Fin n) ℂ).symm fun j ↦
      v.1 (i.succAbove j) / v.1 i

private theorem complexProjectiveAffineCoordinates_smul {n : ℕ} (i : Fin (n + 1))
    (a b : { v : EuclideanSpace ℂ (Fin (n + 1)) // v ≠ 0 }) (t : ℂ)
    (h : a = t • (b : EuclideanSpace ℂ (Fin (n + 1)))) :
    complexProjectiveAffineCoordinates i a = complexProjectiveAffineCoordinates i b := by
  -- The scale factor is nonzero because it sends a nonzero representative to a nonzero representative.
  have ht : t ≠ 0 := by
    intro ht
    apply a.2
    rw [h, ht, zero_smul]
  -- Coordinatewise, the common factor cancels from numerator and denominator.
  ext j
  change a.1 (i.succAbove j) / a.1 i = b.1 (i.succAbove j) / b.1 i
  rw [h]
  simp [complexProjectiveAffineCoordinates, ht, mul_div_mul_left]

private def complexProjectiveChartToFun (n : ℕ) (i : Fin (n + 1)) :
    ℂP[n] → EuclideanSpace ℂ (Fin n) :=
  Projectivization.lift (complexProjectiveAffineCoordinates i)
    (complexProjectiveAffineCoordinates_smul i)

/-- On a homogeneous representative, the affine chart domain condition is the nonvanishing of the
`i`th coordinate. -/
@[simp] theorem complexProjectiveChartDomain_mk (n : ℕ) (i : Fin (n + 1))
    (v : EuclideanSpace ℂ (Fin (n + 1))) (hv : v ≠ 0) :
    mk ℂ v hv ∈ complexProjectiveChartDomain n i ↔ v i ≠ 0 := by
  simp [complexProjectiveChartDomain, complexProjectiveChartDomainPred]

/-- On a homogeneous representative, the affine chart map is given by the standard coordinate
ratios. -/
@[simp] private theorem complexProjectiveChartToFun_mk (n : ℕ) (i : Fin (n + 1))
    (v : EuclideanSpace ℂ (Fin (n + 1))) (hv : v ≠ 0) :
    complexProjectiveChartToFun n i (mk ℂ v hv) =
      (EuclideanSpace.equiv (Fin n) ℂ).symm (fun j ↦ v (i.succAbove j) / v i) := by
  simp [complexProjectiveChartToFun, complexProjectiveAffineCoordinates]

/-- The homogeneous vector obtained from affine coordinates by inserting `1` in the `i`th slot. -/
def complexProjectiveChartInvVector (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin (n + 1)) :=
  (EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm (Fin.insertNth i (1 : ℂ) u)

/-- Helper for Problem 1-9: inserting `1` into the `i`th homogeneous slot gives the expected
coordinates. -/
private theorem complexProjectiveChartInvVector_coordinates (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    complexProjectiveChartInvVector n i u i = 1 ∧
      ∀ j, complexProjectiveChartInvVector n i u (i.succAbove j) = u j := by
  constructor
  · -- The inserted coordinate is exactly the distinguished homogeneous coordinate.
    simp [complexProjectiveChartInvVector]
  · intro j
    -- Away from the distinguished index, insertion recovers the original affine coordinates.
    simp [complexProjectiveChartInvVector]

-- Proof sketch: the inserted homogeneous vector has `i`th coordinate equal to `1`, so it cannot
-- be the zero vector.
/-- The homogeneous coordinates obtained by inserting `1` in the `i`th slot define a nonzero
vector. -/
theorem complexProjectiveChartInvVector_ne_zero (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    complexProjectiveChartInvVector n i u ≠ 0 := by
  -- The `i`th coordinate is `1`, so the inserted vector cannot be zero.
  intro hzero
  have hcoords := complexProjectiveChartInvVector_coordinates n i u
  have hi := congrArg (fun v : EuclideanSpace ℂ (Fin (n + 1)) => v i) hzero
  simpa [hcoords.1] using hi

-- Proof sketch: evaluate the chosen representative `complexProjectiveChartInvVector n i u` at the
-- distinguished index `i`; the value is `1`, so the corresponding projective point lies in `U_i`.
private def complexProjectiveChartInv (n : ℕ) (i : Fin (n + 1)) :
    EuclideanSpace ℂ (Fin n) → ℂP[n] :=
  fun u ↦
    mk ℂ (complexProjectiveChartInvVector n i u)
      (complexProjectiveChartInvVector_ne_zero n i u)

/-- The explicit inverse chart lands in the standard affine domain `U_i`. -/
private theorem complexProjectiveChartInv_mem_domain (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    complexProjectiveChartInv n i u ∈ complexProjectiveChartDomain n i := by
  -- The inserted representative has `i`th homogeneous coordinate equal to `1`.
  have hcoords := complexProjectiveChartInvVector_coordinates n i u
  rw [complexProjectiveChartInv, complexProjectiveChartDomain_mk]
  simpa [hcoords.1] using (show (1 : ℂ) ≠ 0 from one_ne_zero)

private def complexProjectiveChartInvToDomain (n : ℕ) (i : Fin (n + 1)) :
    EuclideanSpace ℂ (Fin n) → complexProjectiveChartDomain n i :=
  fun u ↦ ⟨complexProjectiveChartInv n i u, complexProjectiveChartInv_mem_domain n i u⟩

-- Proof sketch: `complexProjectiveChartDomain n i` is defined by the quotient-invariant predicate
-- that the `i`th homogeneous coordinate is nonzero, so it is the preimage of `{z : ℂ | z ≠ 0}`
-- under the induced coordinate function on projective space.
/-- The standard affine chart domain `U_i` is open in `ℂPⁿ`. -/
theorem complexProjectiveChartDomain_isOpen (n : ℕ) (i : Fin (n + 1)) :
    IsOpen (complexProjectiveChartDomain n i) := by
  let E := EuclideanSpace ℂ (Fin (n + 1))
  let q : { v : E // v ≠ 0 } → ℂP[n] := @Quotient.mk' _ (projectivizationSetoid ℂ E)
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  -- The quotient topology says that openness is detected on the space of nonzero representatives.
  exact (hq.isOpen_preimage).mp <| by
    -- On representatives, the domain is cut out by the open nonvanishing condition `v i ≠ 0`.
    simpa [q, complexProjectiveChartDomain, complexProjectiveChartDomainPred] using
      isOpen_ne_fun
        ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val)
        continuous_const

-- Proof sketch: compute the homogeneous coordinates of `complexProjectiveChartInv n i u`; after
-- dividing by the inserted `1`, the resulting affine coordinates are exactly `u`.
private theorem complexProjectiveChart_left_inv (n : ℕ) (i : Fin (n + 1)) :
    Function.LeftInverse (complexProjectiveChartInvToDomain n i)
      ((complexProjectiveChartDomain n i).restrict (complexProjectiveChartToFun n i)) := by
  intro x
  rcases x with ⟨x, hx⟩
  revert hx
  refine Projectivization.ind (K := ℂ)
    (V := EuclideanSpace ℂ (Fin (n + 1))) ?_ x
  intro v hv hx
  apply Subtype.ext
  -- Rescaling the inserted affine representative by the nonzero `i`th coordinate recovers `v`.
  change complexProjectiveChartInv n i (complexProjectiveChartToFun n i (mk ℂ v hv)) =
    mk ℂ v hv
  have hv_i : v i ≠ 0 := (complexProjectiveChartDomain_mk n i v hv).1 hx
  rw [complexProjectiveChartInv]
  apply (mk_eq_mk_iff' ℂ _ _ (complexProjectiveChartInvVector_ne_zero n i _) hv).2
  refine ⟨(v i)⁻¹, ?_⟩
  ext k
  cases k using i.succAboveCases with
  | x =>
      have hcoords := complexProjectiveChartInvVector_coordinates n i
        (complexProjectiveChartToFun n i (mk ℂ v hv))
      simpa [hv_i] using hcoords.1.symm
  | p j =>
      have hcoords := complexProjectiveChartInvVector_coordinates n i
        (complexProjectiveChartToFun n i (mk ℂ v hv))
      simpa [complexProjectiveChartToFun_mk, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using (hcoords.2 j).symm

-- Proof sketch: normalize a representative of a point in `U_i` by dividing all coordinates by the
-- nonzero `i`th coordinate, then compare projective classes using scale invariance.
private theorem complexProjectiveChart_right_inv (n : ℕ) (i : Fin (n + 1)) :
    Function.RightInverse (complexProjectiveChartInvToDomain n i)
      ((complexProjectiveChartDomain n i).restrict (complexProjectiveChartToFun n i)) := by
  intro u
  -- On the inserted representative `[u,1]`, the affine coordinate ratios recover `u`.
  ext j
  have hcoords := complexProjectiveChartInvVector_coordinates n i u
  simp [complexProjectiveChartInvToDomain, complexProjectiveChartInv, complexProjectiveChartToFun_mk,
    hcoords.1, hcoords.2 j]

/-- Helper for Problem 1-9: the affine-coordinate insertion map `u ↦ [u,1]` is continuous on the
ambient Euclidean space. -/
private theorem complexProjectiveChartInvVector_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (complexProjectiveChartInvVector n i) := by
  -- The insertion map is coordinatewise either constant `1` or one of the affine coordinates.
  refine (EuclideanSpace.equiv (Fin (n + 1)) ℂ).symm.continuous.comp ?_
  refine continuous_pi fun j ↦ ?_
  cases j using i.succAboveCases with
  | x =>
      simpa using (continuous_const : Continuous fun _ : EuclideanSpace ℂ (Fin n) => (1 : ℂ))
  | p j =>
      simpa using (PiLp.continuous_apply 2 _ j : Continuous fun a : EuclideanSpace ℂ (Fin n) => a j)

/-- Helper for Problem 1-9: the affine coordinate map is continuous on the nonvanishing locus of
the distinguished homogeneous coordinate. -/
private theorem complexProjectiveAffineCoordinates_continuousOn (n : ℕ) (i : Fin (n + 1)) :
    ContinuousOn (complexProjectiveAffineCoordinates i)
      { v : { w : EuclideanSpace ℂ (Fin (n + 1)) // w ≠ 0 } | v.1 i ≠ 0 } := by
  -- Each affine coordinate is a quotient of continuous coordinate projections with nonvanishing denominator.
  refine (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp_continuousOn ?_
  refine continuousOn_pi.2 fun j ↦ ?_
  have hnum :
      ContinuousOn (fun v : { w : EuclideanSpace ℂ (Fin (n + 1)) // w ≠ 0 } ↦
        v.1 (i.succAbove j))
        { v : { w : EuclideanSpace ℂ (Fin (n + 1)) // w ≠ 0 } | v.1 i ≠ 0 } :=
    ((PiLp.continuous_apply 2 _ (i.succAbove j)).comp continuous_subtype_val).continuousOn
  have hden :
      ContinuousOn (fun v : { w : EuclideanSpace ℂ (Fin (n + 1)) // w ≠ 0 } ↦ v.1 i)
        { v : { w : EuclideanSpace ℂ (Fin (n + 1)) // w ≠ 0 } | v.1 i ≠ 0 } :=
    ((PiLp.continuous_apply 2 _ i).comp continuous_subtype_val).continuousOn
  exact hnum.div hden fun v hv ↦ hv

private theorem complexProjectiveChartToFun_continuousOn (n : ℕ) (i : Fin (n + 1)) :
    ContinuousOn (complexProjectiveChartToFun n i) (complexProjectiveChartDomain n i) := by
  let E := EuclideanSpace ℂ (Fin (n + 1))
  let q : { v : E // v ≠ 0 } → ℂP[n] := @Quotient.mk' _ (projectivizationSetoid ℂ E)
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  -- The quotient map is a quotient map, so continuity on the chart domain is checked on representatives.
  exact (hq.continuousOn_isOpen_iff (complexProjectiveChartDomain_isOpen n i)).2 <| by
  -- On representatives with nonzero `i`th coordinate, the chart map is the explicit ratio map.
    simpa [q, complexProjectiveChartDomain, complexProjectiveChartToFun,
      complexProjectiveChartDomainPred]
      using complexProjectiveAffineCoordinates_continuousOn n i

private theorem complexProjectiveChartInv_continuous (n : ℕ) (i : Fin (n + 1)) :
    Continuous (complexProjectiveChartInv n i) := by
  let E := EuclideanSpace ℂ (Fin (n + 1))
  -- The inverse chart is the quotient map applied to the continuous insertion `u ↦ [u,1]`.
  change Continuous
    (fun u ↦
      ((@Quotient.mk' { v : E // v ≠ 0 } (projectivizationSetoid ℂ E))
        ⟨complexProjectiveChartInvVector n i u,
        complexProjectiveChartInvVector_ne_zero n i u⟩ : ℂP[n]))
  exact continuous_quotient_mk'.comp <|
    Continuous.subtype_mk (complexProjectiveChartInvVector_continuous n i)
      (fun u ↦ complexProjectiveChartInvVector_ne_zero n i u)

/-- The standard affine chart on `ℂPⁿ` as an open partial homeomorphism. -/
noncomputable def complexProjectiveChart (n : ℕ) (i : Fin (n + 1)) :
    OpenPartialHomeomorph (ℂP[n]) (EuclideanSpace ℂ (Fin n)) where
  toPartialEquiv :=
    { toFun := complexProjectiveChartToFun n i
      invFun := complexProjectiveChartInv n i
      source := complexProjectiveChartDomain n i
      target := Set.univ
      map_source' := fun _ _ ↦ Set.mem_univ _
      map_target' := fun u _ ↦ complexProjectiveChartInv_mem_domain n i u
      left_inv' := fun x hx ↦ by
        exact congrArg Subtype.val (complexProjectiveChart_left_inv n i ⟨x, hx⟩)
      right_inv' := fun u _ ↦ complexProjectiveChart_right_inv n i u }
  open_source := complexProjectiveChartDomain_isOpen n i
  open_target := isOpen_univ
  continuousOn_toFun := complexProjectiveChartToFun_continuousOn n i
  continuousOn_invFun := (complexProjectiveChartInv_continuous n i).continuousOn

/-- On a homogeneous representative, the standard affine chart is given by the standard coordinate
ratios. -/
@[simp] theorem complexProjectiveChart_mk (n : ℕ) (i : Fin (n + 1))
    (v : EuclideanSpace ℂ (Fin (n + 1))) (hv : v ≠ 0) :
    complexProjectiveChart n i (mk ℂ v hv) =
      (EuclideanSpace.equiv (Fin n) ℂ).symm (fun j ↦ v (i.succAbove j) / v i) := by
  exact complexProjectiveChartToFun_mk n i v hv

/-- The inverse chart is the homogeneous coordinate insertion `u ↦ [u,1]`. -/
@[simp] theorem complexProjectiveChart_symm_apply (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    (complexProjectiveChart n i).symm u =
      mk ℂ (complexProjectiveChartInvVector n i u)
        (complexProjectiveChartInvVector_ne_zero n i u) := rfl

/-- The inverse chart lands in the standard affine domain `U_i`. -/
theorem complexProjectiveChart_symm_mem_domain (n : ℕ) (i : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    (complexProjectiveChart n i).symm u ∈ complexProjectiveChartDomain n i :=
  complexProjectiveChartInv_mem_domain n i u

-- Proof sketch: choose a nonzero representative of `x`; one of its `n + 1` homogeneous
-- coordinates is nonzero, placing `x` in the corresponding standard affine chart domain.
/-- Every point of `ℂPⁿ` lies in a standard affine chart whose coordinate map is a homeomorphism
with `ℂⁿ`; equivalently, it lies in the source of one of the bundled affine charts. -/
theorem complex_projective_space_has_standard_chart (n : ℕ) (x : ℂP[n]) :
    ∃ i : Fin (n + 1), x ∈ complexProjectiveChartDomain n i := by
  classical
  -- A nonzero homogeneous representative has at least one nonzero coordinate.
  have hnonzero_coord : ∃ i : Fin (n + 1), x.rep i ≠ 0 := by
    by_contra h
    push_neg at h
    apply x.rep_nonzero
    ext i
    exact h i
  rcases hnonzero_coord with ⟨i, hi⟩
  -- The chart indexed by such a coordinate contains the corresponding projective point.
  refine ⟨i, ?_⟩
  simpa [x.mk_rep] using (complexProjectiveChartDomain_mk n i x.rep x.rep_nonzero).2 hi

-- Proof sketch: identify `ℂPⁿ` with the quotient of the unit sphere in `ℂ^(n+1)` by the circle
-- action; the sphere is compact, and a continuous image of a compact space is compact.
/-- Problem 1-9 (1): complex projective space is compact. -/
instance complexProjectiveSpaceCompactSpace (n : ℕ) :
    CompactSpace (ℂP[n]) := by
  let E := EuclideanSpace ℂ (Fin (n + 1))
  let sphereToComplexProjectiveSpace : Metric.sphere (0 : E) 1 → ℂP[n] :=
    fun x ↦ mk ℂ (x : E) (Metric.ne_of_mem_sphere x.2 one_ne_zero)
  have hq_cont : Continuous sphereToComplexProjectiveSpace := by
    -- The quotient map is continuous, so the restriction to the unit sphere is continuous.
    let q : { v : E // v ≠ 0 } → ℂP[n] := @Quotient.mk' _ (projectivizationSetoid ℂ E)
    change Continuous
      (fun x : Metric.sphere (0 : E) 1 ↦
        (q ⟨(x : E), Metric.ne_of_mem_sphere x.2 one_ne_zero⟩ : ℂP[n]))
    exact continuous_quotient_mk'.comp <| continuous_subtype_val.subtype_mk _
  have hq_surj : Function.Surjective sphereToComplexProjectiveSpace := by
    intro x
    have hx_norm_ne : ‖(x.rep : E)‖ ≠ 0 := norm_ne_zero_iff.mpr x.rep_nonzero
    have hx_norm_ne' : ((‖(x.rep : E)‖ : ℂ)) ≠ 0 := by
      exact_mod_cast hx_norm_ne
    refine ⟨⟨((‖(x.rep : E)‖ : ℂ)⁻¹) • x.rep, by
      simp [mem_sphere_zero_iff_norm, norm_smul, norm_inv, hx_norm_ne]⟩, ?_⟩
    change mk ℂ (((‖(x.rep : E)‖ : ℂ)⁻¹) • x.rep)
      (smul_ne_zero (by simpa using (inv_ne_zero hx_norm_ne' : (‖(x.rep : E)‖ : ℂ)⁻¹ ≠ 0))
        x.rep_nonzero) = x
    have hmk :
        mk ℂ (((‖(x.rep : E)‖ : ℂ)⁻¹) • x.rep)
          (smul_ne_zero (by simpa using (inv_ne_zero hx_norm_ne' : (‖(x.rep : E)‖ : ℂ)⁻¹ ≠ 0))
            x.rep_nonzero) =
          mk ℂ x.rep x.rep_nonzero := by
      exact (mk_eq_mk_iff' ℂ _ _ (smul_ne_zero
        (by simpa using (inv_ne_zero hx_norm_ne' : (‖(x.rep : E)‖ : ℂ)⁻¹ ≠ 0))
        x.rep_nonzero)
        x.rep_nonzero).2 ⟨((‖(x.rep : E)‖ : ℂ)⁻¹), rfl⟩
    simpa [x.mk_rep] using hmk
  have hrange : Set.range sphereToComplexProjectiveSpace = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rcases hq_surj x with ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  have hcompact : IsCompact (Set.univ : Set (ℂP[n])) := by
    simpa [hrange] using isCompact_range hq_cont
  exact isCompact_univ_iff.mp hcompact

/-- Helper for Problem 1-9: the ambient complex vector space used to model `ℂPⁿ`. -/
private abbrev complexProjectiveAmbient (n : ℕ) :=
  EuclideanSpace ℂ (Fin (n + 1))

/-- Helper for Problem 1-9: the unit sphere in the ambient space. -/
private abbrev complexProjectiveSphere (n : ℕ) :=
  Metric.sphere (0 : complexProjectiveAmbient n) 1

/-- Helper for Problem 1-9: the unit circle acting on the normalized sphere representatives. -/
private abbrev complexProjectiveUnitCircle :=
  Metric.sphere (0 : ℂ) 1

/-- Helper for Problem 1-9: the quotient of the unit sphere by the circle action. -/
private abbrev complexProjectiveSphereQuotient (n : ℕ) :=
  Quotient (MulAction.orbitRel complexProjectiveUnitCircle (complexProjectiveSphere n))

/-- Helper for Problem 1-9: the quotient map from the unit sphere to its circle-orbit quotient. -/
private def complexProjectiveSphereQuotientMk (n : ℕ) :
    complexProjectiveSphere n → complexProjectiveSphereQuotient n :=
  @Quotient.mk' _ (MulAction.orbitRel complexProjectiveUnitCircle (complexProjectiveSphere n))

/-- Helper for Problem 1-9: normalize a nonzero vector to a unit vector in the same complex line. -/
private def complexProjectiveNormalizedSphereVector (n : ℕ) :
    { v : complexProjectiveAmbient n // v ≠ 0 } → complexProjectiveAmbient n :=
  fun v ↦ ((‖(v : complexProjectiveAmbient n)‖ : ℂ)⁻¹) • (v : complexProjectiveAmbient n)

/-- Helper for Problem 1-9: the normalized representative lies on the unit sphere. -/
private theorem complexProjectiveNormalizedSphereVector_mem_sphere (n : ℕ)
    (v : { w : complexProjectiveAmbient n // w ≠ 0 }) :
    complexProjectiveNormalizedSphereVector n v ∈ complexProjectiveSphere n := by
  -- The norm of the normalized representative is `‖v‖⁻¹ * ‖v‖ = 1`.
  have hv_norm_ne : ‖(v : complexProjectiveAmbient n)‖ ≠ 0 := norm_ne_zero_iff.mpr v.2
  simpa [complexProjectiveNormalizedSphereVector, complexProjectiveSphere,
    mem_sphere_zero_iff_norm, norm_smul, norm_inv, hv_norm_ne]

/-- Helper for Problem 1-9: choose the normalized point on the sphere representing a projective
class. -/
private def complexProjectiveNormalizedSpherePoint (n : ℕ) :
    { v : complexProjectiveAmbient n // v ≠ 0 } → complexProjectiveSphere n :=
  fun v ↦
    ⟨complexProjectiveNormalizedSphereVector n v,
      complexProjectiveNormalizedSphereVector_mem_sphere n v⟩

/-- Helper for Problem 1-9: the normalization map on nonzero representatives is continuous. -/
private theorem complexProjectiveNormalizedSpherePoint_continuous (n : ℕ) :
    Continuous (complexProjectiveNormalizedSpherePoint n) := by
  -- The scale factor `‖v‖⁻¹` varies continuously away from the zero vector.
  have hscale : Continuous fun v : { w : complexProjectiveAmbient n // w ≠ 0 } ↦
      ((‖(v : complexProjectiveAmbient n)‖ : ℂ)⁻¹) := by
    refine Continuous.inv₀ ?_ ?_
    · exact Complex.continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val)
    · intro v
      exact_mod_cast (norm_ne_zero_iff.mpr v.2)
  -- Multiplying the representative by this continuous scale gives the normalized vector field.
  refine Continuous.subtype_mk ?_ (fun v ↦ complexProjectiveNormalizedSphereVector_mem_sphere n v)
  simpa [complexProjectiveNormalizedSpherePoint, complexProjectiveNormalizedSphereVector] using
    hscale.smul continuous_subtype_val

/-- Helper for Problem 1-9: normalizing projectively equivalent representatives changes only by a
circle scalar, so the sphere quotient class is well defined. -/
private theorem complex_projective_normalized_orbit_eq (n : ℕ)
    (a b : { v : complexProjectiveAmbient n // v ≠ 0 }) (t : ℂ)
    (h : a = t • (b : complexProjectiveAmbient n)) :
    complexProjectiveSphereQuotientMk n (complexProjectiveNormalizedSpherePoint n a) =
      complexProjectiveSphereQuotientMk n (complexProjectiveNormalizedSpherePoint n b) := by
  -- Route correction: descend normalization to the circle quotient first, then compare projective
  -- classes through that quotient instead of attempting a monolithic quotient/homeomorphism bridge.
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  dsimp at h ⊢
  have ht : t ≠ 0 := by
    intro ht
    apply ha
    rw [h, ht, zero_smul]
  have hz : ‖t / (‖t‖ : ℂ)‖ = 1 := by
    have hnorm_coe : ‖((‖t‖ : ℂ))‖ = ‖t‖ := by
      simpa using (RCLike.norm_ofReal ‖t‖ : ‖((‖t‖ : ℂ))‖ = |‖t‖|)
    calc
      ‖t / (‖t‖ : ℂ)‖ = ‖t‖ / ‖((‖t‖ : ℂ))‖ := by rw [norm_div]
      _ = ‖t‖ / ‖t‖ := by rw [hnorm_coe]
      _ = 1 := div_self (norm_ne_zero_iff.mpr ht)
  let z : complexProjectiveUnitCircle := ⟨t / ‖t‖, by
    simpa [complexProjectiveUnitCircle, mem_sphere_zero_iff_norm] using hz⟩
  apply Quotient.sound
  change complexProjectiveNormalizedSpherePoint n ⟨a, ha⟩ ∈
    MulAction.orbit complexProjectiveUnitCircle (complexProjectiveNormalizedSpherePoint n ⟨b, hb⟩)
  refine ⟨z, ?_⟩
  apply Subtype.ext
  have hb_norm_ne : ‖b‖ ≠ 0 := norm_ne_zero_iff.mpr hb
  have hscalar :
      (((z : complexProjectiveUnitCircle) : ℂ) * ((‖b‖ : ℂ)⁻¹)) =
        t * ((‖t • b‖ : ℂ)⁻¹) := by
    rw [show (((z : complexProjectiveUnitCircle) : ℂ)) = t / ‖t‖ by rfl, norm_smul,
      Complex.ofReal_mul]
    field_simp [norm_ne_zero_iff.mpr ht, hb_norm_ne]
  have hleft :
      ↑(z • complexProjectiveNormalizedSpherePoint n ⟨b, hb⟩) =
        (((z : complexProjectiveUnitCircle) : ℂ) • (((‖b‖ : ℂ)⁻¹) • b)) := rfl
  calc
    ↑(z • complexProjectiveNormalizedSpherePoint n ⟨b, hb⟩)
        = (((z : complexProjectiveUnitCircle) : ℂ) • (((‖b‖ : ℂ)⁻¹) • b)) := hleft
    _ = ((((z : complexProjectiveUnitCircle) : ℂ) * ((‖b‖ : ℂ)⁻¹)) • b) := by rw [smul_smul]
    _ = (t * ((‖t • b‖ : ℂ)⁻¹)) • b := congrArg (fun c : ℂ ↦ c • b) hscalar
    _ = ↑(complexProjectiveNormalizedSpherePoint n ⟨a, ha⟩) := by
      simp [complexProjectiveNormalizedSpherePoint, complexProjectiveNormalizedSphereVector, h,
        smul_smul, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Problem 1-9: the normalization map descends continuously from nonzero vectors to
projective space. -/
private def complexProjectiveToSphereQuotient (n : ℕ) :
    ℂP[n] → complexProjectiveSphereQuotient n :=
  Projectivization.lift
    (fun v ↦ complexProjectiveSphereQuotientMk n (complexProjectiveNormalizedSpherePoint n v))
    (complex_projective_normalized_orbit_eq n)

/-- Helper for Problem 1-9: the descended normalization map is continuous by the quotient-topology
criterion. -/
private theorem complexProjectiveToSphereQuotient_continuous (n : ℕ) :
    Continuous (complexProjectiveToSphereQuotient n) := by
  let q : { v : complexProjectiveAmbient n // v ≠ 0 } → ℂP[n] :=
    @Quotient.mk' _ (projectivizationSetoid ℂ (complexProjectiveAmbient n))
  have hq : Topology.IsQuotientMap q := isQuotientMap_quotient_mk'
  have hmk : Continuous (complexProjectiveSphereQuotientMk n) := by
    simpa [complexProjectiveSphereQuotientMk] using
      (continuous_quotient_mk' :
        Continuous (@Quotient.mk' (complexProjectiveSphere n)
          (MulAction.orbitRel complexProjectiveUnitCircle (complexProjectiveSphere n))))
  -- Check continuity on the space of nonzero representatives where the formula is explicit.
  refine hq.continuous_iff.mpr ?_
  simpa [q, complexProjectiveToSphereQuotient, Function.comp] using
    (hmk.comp (complexProjectiveNormalizedSpherePoint_continuous n))

/-- Helper for Problem 1-9: a point of the unit sphere is nonzero in the ambient vector space. -/
private theorem complexProjectiveSpherePoint_ne_zero (n : ℕ)
    (x : complexProjectiveSphere n) :
    (x : complexProjectiveAmbient n) ≠ 0 :=
  Metric.ne_of_mem_sphere x.2 one_ne_zero

/-- Helper for Problem 1-9: projectivizing a sphere point depends only on its circle orbit. -/
private theorem sphereQuotientToComplexProjectiveSpace_wellDefined (n : ℕ)
    {a b : complexProjectiveSphere n}
    (h : MulAction.orbitRel complexProjectiveUnitCircle (complexProjectiveSphere n) a b) :
    mk ℂ (a : complexProjectiveAmbient n) (complexProjectiveSpherePoint_ne_zero n a) =
      mk ℂ (b : complexProjectiveAmbient n) (complexProjectiveSpherePoint_ne_zero n b) := by
  -- A circle scalar is a nonzero complex scalar, so it preserves the projective class.
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h
  rcases h with ⟨z, hz⟩
  apply (mk_eq_mk_iff' ℂ _ _ _ _).2
  refine ⟨(z : ℂ), ?_⟩
  simpa using congrArg (fun x : complexProjectiveSphere n =>
    (x : complexProjectiveAmbient n)) hz

/-- Helper for Problem 1-9: the sphere quotient maps to projective space by forgetting the chosen
unit representative. -/
private def sphereQuotientToComplexProjectiveSpace (n : ℕ) :
    complexProjectiveSphereQuotient n → ℂP[n] :=
  Quotient.lift
    (fun x : complexProjectiveSphere n ↦
      mk ℂ (x : complexProjectiveAmbient n) (complexProjectiveSpherePoint_ne_zero n x))
    (fun _ _ h ↦ sphereQuotientToComplexProjectiveSpace_wellDefined n h)

/-- Helper for Problem 1-9: a point already on the unit sphere is fixed by normalization. -/
private theorem complexProjectiveNormalizedSpherePoint_of_sphere (n : ℕ)
    (x : complexProjectiveSphere n) :
    complexProjectiveNormalizedSpherePoint n
      ⟨(x : complexProjectiveAmbient n), complexProjectiveSpherePoint_ne_zero n x⟩ = x := by
  -- On the unit sphere the norm is `1`, so normalization does nothing.
  apply Subtype.ext
  have hx_norm : ‖(x : complexProjectiveAmbient n)‖ = 1 := mem_sphere_zero_iff_norm.1 x.2
  simp [complexProjectiveNormalizedSpherePoint, complexProjectiveNormalizedSphereVector, hx_norm]

/-- Helper for Problem 1-9: normalization and projectivization give inverse maps between `ℂPⁿ`
and the circle quotient of the unit sphere. -/
private theorem complex_projective_sphere_quotient_inverse (n : ℕ) :
    Function.LeftInverse (sphereQuotientToComplexProjectiveSpace n)
      (complexProjectiveToSphereQuotient n) ∧
    Function.RightInverse (sphereQuotientToComplexProjectiveSpace n)
      (complexProjectiveToSphereQuotient n) := by
  constructor
  · intro x
    -- Normalizing a nonzero representative does not change its projective class.
    refine Projectivization.ind (K := ℂ) (V := complexProjectiveAmbient n) ?_ x
    intro v hv
    change
      mk ℂ (complexProjectiveNormalizedSphereVector n ⟨v, hv⟩)
        (complexProjectiveSpherePoint_ne_zero n (complexProjectiveNormalizedSpherePoint n ⟨v, hv⟩)) =
        mk ℂ v hv
    apply (mk_eq_mk_iff' ℂ _ _ _ hv).2
    refine ⟨((‖v‖ : ℂ)⁻¹), ?_⟩
    simp [sphereQuotientToComplexProjectiveSpace, complexProjectiveToSphereQuotient,
      complexProjectiveNormalizedSpherePoint, complexProjectiveNormalizedSphereVector]
  · intro q
    -- A sphere representative stays fixed after projectivizing and re-normalizing.
    refine Quotient.inductionOn q ?_
    intro x
    simpa [sphereQuotientToComplexProjectiveSpace, complexProjectiveToSphereQuotient] using
      congrArg (complexProjectiveSphereQuotientMk n)
        (complexProjectiveNormalizedSpherePoint_of_sphere n x)

/-- Helper for Problem 1-9: the circle action on the unit sphere is proper because the smul-pair
map has compact source and Hausdorff target. -/
private instance complexProjectiveSphereProperSMul (n : ℕ) :
    ProperSMul complexProjectiveUnitCircle (complexProjectiveSphere n) where
  isProperMap_smul_pair := by
    -- The source `Circle × S` is compact, so every continuous map to the Hausdorff target `S × S`
    -- is proper.
    have hcont : Continuous fun gx : complexProjectiveUnitCircle × complexProjectiveSphere n ↦
        ((gx.1 • gx.2, gx.2) : complexProjectiveSphere n × complexProjectiveSphere n) := by
      fun_prop
    exact hcont.isProperMap

-- Proof sketch: two distinct complex lines can be separated by disjoint neighborhoods after
-- passing to normalized representatives on the unit sphere, so the quotient topology is Hausdorff.
/-- Problem 1-9 (2): complex projective space is Hausdorff. -/
instance complexProjectiveSpaceT2Space (n : ℕ) :
    T2Space (ℂP[n]) := by
  -- The normalized-sphere quotient is Hausdorff by properness of the circle action, and
  -- `ℂPⁿ` is homeomorphic to that quotient via the compact-to-T2 criterion.
  let e : ℂP[n] ≃ complexProjectiveSphereQuotient n :=
    { toFun := complexProjectiveToSphereQuotient n
      invFun := sphereQuotientToComplexProjectiveSpace n
      left_inv := (complex_projective_sphere_quotient_inverse n).1
      right_inv := (complex_projective_sphere_quotient_inverse n).2 }
  let h : ℂP[n] ≃ₜ complexProjectiveSphereQuotient n :=
    (complexProjectiveToSphereQuotient_continuous n).homeoOfEquivCompactToT2 (f := e)
  exact h.symm.t2Space

-- Proof sketch: use the standard affine charts `complexProjectiveChart n i`; every point has a
-- nonzero homogeneous coordinate, so these chart domains cover `ℂPⁿ` and give a charted-space
-- structure modelled on `ℂⁿ`, viewed as a real `2n`-dimensional vector space.
/-- Problem 1-9 (3): the standard affine charts make `ℂPⁿ` into a topological manifold modelled on
`ℂⁿ`, equivalently on `ℝ^(2n)`. -/
private def complexProjectiveChartAtlas (n : ℕ) :
    Set (OpenPartialHomeomorph (ℂP[n]) (EuclideanSpace ℂ (Fin n))) :=
  { e | ∃ i : Fin (n + 1), e = complexProjectiveChart n i }

private noncomputable def complexProjectiveChartAt (n : ℕ) (x : ℂP[n]) :
    OpenPartialHomeomorph (ℂP[n]) (EuclideanSpace ℂ (Fin n)) :=
  let i := Classical.choose (complex_projective_space_has_standard_chart n x)
  complexProjectiveChart n i

private theorem mem_complexProjectiveChartAt_source (n : ℕ) (x : ℂP[n]) :
    x ∈ (complexProjectiveChartAt n x).source := by
  let hx := Classical.choose_spec (complex_projective_space_has_standard_chart n x)
  simpa [complexProjectiveChartAt]
    using hx

private theorem complexProjectiveChartAt_mem_atlas (n : ℕ) (x : ℂP[n]) :
    complexProjectiveChartAt n x ∈ complexProjectiveChartAtlas n := by
  refine ⟨Classical.choose (complex_projective_space_has_standard_chart n x), ?_⟩
  simp [complexProjectiveChartAt]

instance complexProjectiveSpaceChartedSpace (n : ℕ) :
    ChartedSpace (EuclideanSpace ℂ (Fin n)) (ℂP[n]) where
  atlas := complexProjectiveChartAtlas n
  chartAt := complexProjectiveChartAt n
  mem_chart_source := mem_complexProjectiveChartAt_source n
  chart_mem_atlas := complexProjectiveChartAt_mem_atlas n

/-- Helper for Problem 1-9: membership in the overlap of the `i`th and `j`th affine charts is
equivalent to the nonvanishing of the `j`th inserted homogeneous coordinate. -/
private theorem mem_complexProjectiveChartOverlap_iff (n : ℕ) (i j : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    u ∈ ((complexProjectiveChart n i).symm.trans (complexProjectiveChart n j)).source ↔
      complexProjectiveChartInvVector n i u j ≠ 0 := by
  -- Route correction: smooth compatibility only needs the overlap source rewritten as the
  -- nonvanishing denominator condition for the explicit rational transition formula.
  rw [OpenPartialHomeomorph.trans_source]
  simp only [complexProjectiveChart, Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, true_and]
  simpa [complexProjectiveChartInv] using
    (complexProjectiveChartDomain_mk n j (complexProjectiveChartInvVector n i u)
      (complexProjectiveChartInvVector_ne_zero n i u))

/-- Helper for Problem 1-9: each inserted homogeneous coordinate depends smoothly on the affine
coordinates. -/
private theorem complexProjectiveChartInvVector_coordinate_contDiff (n : ℕ) (i : Fin (n + 1))
    (j : Fin (n + 1)) :
    ContDiff ℝ ω
      (fun u : EuclideanSpace ℂ (Fin n) ↦ complexProjectiveChartInvVector n i u j) := by
  -- The inserted coordinate is constant `1`, while every other coordinate is an affine projection.
  cases j using i.succAboveCases with
  | x =>
      simpa [complexProjectiveChartInvVector] using
        (contDiff_const :
          ContDiff ℝ ω (fun _ : EuclideanSpace ℂ (Fin n) => (1 : ℂ)))
  | p k =>
      simpa [complexProjectiveChartInvVector] using
        ((contDiff_piLp_apply (p := 2) (i := k)) :
          ContDiff ℝ ω (fun u : EuclideanSpace ℂ (Fin n) => u k))

/-- Helper for Problem 1-9: the transition from the `i`th affine chart to the `j`th affine chart
is given by the usual quotient formula in inserted homogeneous coordinates. -/
private theorem complexProjectiveChartTransition_apply (n : ℕ) (i j : Fin (n + 1))
    (u : EuclideanSpace ℂ (Fin n)) :
    ((complexProjectiveChart n i).symm.trans (complexProjectiveChart n j)) u =
      WithLp.toLp 2
        (fun k ↦
          complexProjectiveChartInvVector n i u (j.succAbove k) /
            complexProjectiveChartInvVector n i u j) := by
  -- Apply the `j`th chart to the inserted homogeneous representative `[u,1]`.
  simpa [EuclideanSpace.equiv] using
    (by
      rw [OpenPartialHomeomorph.trans_apply, complexProjectiveChart_symm_apply,
        complexProjectiveChart_mk] :
        ((complexProjectiveChart n i).symm.trans (complexProjectiveChart n j)) u =
          (EuclideanSpace.equiv (Fin n) ℂ).symm
            (fun k ↦
              complexProjectiveChartInvVector n i u (j.succAbove k) /
                complexProjectiveChartInvVector n i u j))

/-- Helper for Problem 1-9: the affine chart transition map is smooth on its overlap domain. -/
private theorem complexProjectiveChartTransition_contDiffOn (n : ℕ) (i j : Fin (n + 1)) :
    ContDiffOn ℝ ω ((complexProjectiveChart n i).symm.trans (complexProjectiveChart n j))
      (((complexProjectiveChart n i).symm.trans (complexProjectiveChart n j)).source) := by
  let s : Set (EuclideanSpace ℂ (Fin n)) :=
    ((complexProjectiveChart n i).symm.trans (complexProjectiveChart n j)).source
  have hden :
      ContDiffOn ℝ ω
        (fun u : EuclideanSpace ℂ (Fin n) ↦ complexProjectiveChartInvVector n i u j) s :=
    (complexProjectiveChartInvVector_coordinate_contDiff n i j).contDiffOn
  have hnum :
      ∀ k : Fin n,
        ContDiffOn ℝ ω
          (fun u : EuclideanSpace ℂ (Fin n) ↦ complexProjectiveChartInvVector n i u (j.succAbove k))
          s := fun k ↦
            (complexProjectiveChartInvVector_coordinate_contDiff n i (j.succAbove k)).contDiffOn
  have hcoord :
      ∀ k : Fin n,
        ContDiffOn ℝ ω
          (fun u : EuclideanSpace ℂ (Fin n) ↦
            complexProjectiveChartInvVector n i u (j.succAbove k) /
              complexProjectiveChartInvVector n i u j)
          s := by
    intro k
    -- Each coordinate is a product with the inverse of the nonvanishing denominator coordinate.
    simpa [div_eq_mul_inv] using
      (hnum k).mul (hden.inv fun u hu ↦ (mem_complexProjectiveChartOverlap_iff n i j u).1 hu)
  have hformula :
      ContDiffOn ℝ ω
        (fun u : EuclideanSpace ℂ (Fin n) ↦
          WithLp.toLp 2
            (fun k ↦
              complexProjectiveChartInvVector n i u (j.succAbove k) /
                complexProjectiveChartInvVector n i u j))
        s := by
    -- Assemble the coordinatewise smooth quotient formula and transport back to `EuclideanSpace`.
    have htoLp :
        ContDiffOn ℝ ω
          (WithLp.toLp 2 : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n))
          Set.univ :=
      (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin n => ℂ)).contDiffOn
    refine htoLp.comp ?_ fun _ _ ↦ by simp
    exact contDiffOn_pi.2 hcoord
  -- Replace the explicit formula by the bundled chart transition.
  refine hformula.congr ?_
  intro u hu
  exact (complexProjectiveChartTransition_apply n i j u).symm

-- Proof sketch: on overlaps, the transition maps between the standard affine charts are rational
-- affine-coordinate changes with denominator a chosen nonzero coordinate, hence smooth as real
-- maps on their domains.
/-- Problem 1-9 (4): the standard affine atlas gives `ℂPⁿ` a smooth manifold structure analogous
to the standard smooth atlas on `ℝPⁿ`. -/
instance complexProjectiveSpaceIsManifold (n : ℕ) :
    IsManifold (𝓘(ℝ, EuclideanSpace ℂ (Fin n))) (⊤ : WithTop ℕ∞)
      (ℂP[n]) := by
  -- The standard affine atlas is smooth because every overlap transition is the explicit rational
  -- coordinate change proved above.
  refine isManifold_of_contDiffOn (I := 𝓘(ℝ, EuclideanSpace ℂ (Fin n)))
    (n := (⊤ : WithTop ℕ∞)) (ℂP[n]) ?_
  intro e e' he he'
  rcases he with ⟨i, rfl⟩
  rcases he' with ⟨j, rfl⟩
  simpa using complexProjectiveChartTransition_contDiffOn n i j
