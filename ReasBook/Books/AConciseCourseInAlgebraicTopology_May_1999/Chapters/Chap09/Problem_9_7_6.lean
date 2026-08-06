import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap07.Criterion_7_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Criterion_8_5_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_6_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Problem_9_7_6.ProjectivizationBundle
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Remark_9_4_13.BasepointTransport

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open scoped LinearAlgebra.Projectivization Topology Topology.Homotopy unitInterval

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch` plus local Chapter 9 precedent: the repo models
-- projective spaces with the canonical projectivization owner `ℙ 𝕜 V`.

/-- The topology on the countably supported real coordinates used in the `RP^∞` model. -/
instance realProjectiveInfinityCoordinatesTopologicalSpace : TopologicalSpace (ℕ →₀ ℝ) :=
  TopologicalSpace.induced (fun f ↦ (f : ℕ → ℝ)) inferInstance

/-- Helper for Problem 9.7.6: the induced topology on `ℕ →₀ ℝ` is compatible with addition. -/
private instance realProjectiveInfinityCoordinatesContinuousAdd : ContinuousAdd (ℕ →₀ ℝ) := by
  -- Transfer continuity from the ambient product topology on `ℕ → ℝ`.
  refine ⟨continuous_induced_rng.2 ?_⟩
  exact
    (continuous_induced_dom.fst'.add continuous_induced_dom.snd' :
      Continuous fun p : (ℕ →₀ ℝ) × (ℕ →₀ ℝ) => ((p.1 : ℕ → ℝ) + (p.2 : ℕ → ℝ)))

/-- Helper for Problem 9.7.6: the induced topology on `ℕ →₀ ℝ` is compatible with real scalar
multiplication. -/
private instance realProjectiveInfinityCoordinatesContinuousSMul : ContinuousSMul ℝ (ℕ →₀ ℝ) := by
  -- Again we reduce to the ambient function-space scalar action.
  refine ⟨continuous_induced_rng.2 ?_⟩
  exact
    (continuous_fst.smul continuous_induced_dom.snd' :
      Continuous fun p : ℝ × (ℕ →₀ ℝ) => p.1 • ((p.2 : ℕ → ℝ)))

/-- The workspace's canonical projectivization model of `RP^∞`. -/
abbrev RealProjectiveInfinity := ℙ ℝ (ℕ →₀ ℝ)

/-- The quotient topology on the projectivization model of `RP^∞`. -/
instance realProjectiveInfinityTopologicalSpace : TopologicalSpace RealProjectiveInfinity :=
  instTopologicalSpaceQuotient

/-- A concrete basepoint of `RP^∞`, represented by the first coordinate line. -/
def realProjectiveInfinityBasepoint : RealProjectiveInfinity :=
  Projectivization.mk ℝ (Finsupp.single 0 (1 : ℝ)) <| by
    simp

/-- Helper for Problem 9.7.6: the explicit two-coordinate vector used to test whether compact
subsets of the induced-topology `RP^∞` model can escape every finite support stage. -/
private def escapingCoordinateVector (𝕜 : Type*) [DivisionRing 𝕜] (n : ℕ) : ℕ →₀ 𝕜 :=
  Finsupp.single 0 (1 : 𝕜) + Finsupp.single (n + 1) (1 : 𝕜)

/-- Helper for Problem 9.7.6: the escaping coordinate vector is nonzero because its `(n + 1)`st
coordinate is `1`. -/
private theorem escapingCoordinateVector_nonzero
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] (n : ℕ) :
    escapingCoordinateVector 𝕜 n ≠ 0 := by
  intro hv
  have hzero := congrArg (fun f : ℕ →₀ 𝕜 ↦ f (n + 1)) hv
  have hone : (1 : 𝕜) ≠ 0 := one_ne_zero
  exact hone (by simpa [escapingCoordinateVector] using hzero)

/-- Helper for Problem 9.7.6: embed a finite coordinate vector `𝕜^(m + 1)` into the finitely
supported countable coordinate space by extending it by zero outside `Fin (m + 1)`. -/
private noncomputable def finiteCoordinateLinear (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) :
    (Fin (m + 1) → 𝕜) →ₗ[𝕜] (ℕ →₀ 𝕜) :=
  (Finsupp.lmapDomain 𝕜 𝕜 (fun i : Fin (m + 1) ↦ (i : ℕ))).comp
    (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin (m + 1))).symm.toLinearMap

/-- Helper for Problem 9.7.6: on the first `m + 1` coordinates, the finite-to-infinity embedding
agrees with the original finite vector. -/
private theorem finiteCoordinateLinear_apply_cast
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) (v : Fin (m + 1) → 𝕜) (i : Fin (m + 1)) :
    finiteCoordinateLinear 𝕜 m v i = v i := by
  -- Unfold the finite-support encoding and evaluate at a coordinate in the embedding range.
  change
    ((Finsupp.lmapDomain 𝕜 𝕜 fun i : Fin (m + 1) ↦ (i : ℕ))
        ((Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin (m + 1))).symm v)) i = v i
  rw [Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_apply (fun i j hij => Fin.ext hij)]
  rw [Finsupp.linearEquivFunOnFinite_symm_apply]

/-- Helper for Problem 9.7.6: outside `Fin (m + 1)`, the finite-to-infinity embedding is zero. -/
private theorem finiteCoordinateLinear_apply_of_not_mem_range
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) (v : Fin (m + 1) → 𝕜) {n : ℕ}
    (hn : n ∉ Finset.range (m + 1)) :
    finiteCoordinateLinear 𝕜 m v n = 0 := by
  -- Reinterpret the excluded coordinate as lying outside the image of `Fin (m + 1) ↪ ℕ`.
  have hrange : n ∉ Set.range (fun i : Fin (m + 1) ↦ (i : ℕ)) := by
    simpa [Finset.mem_range] using hn
  change
    ((Finsupp.lmapDomain 𝕜 𝕜 fun i : Fin (m + 1) ↦ (i : ℕ))
        ((Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin (m + 1))).symm v)) n = 0
  rw [Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_notin_range _ _ hrange]

/-- Helper for Problem 9.7.6: the finite-to-infinity coordinate embedding is injective. -/
private theorem finiteCoordinateLinear_injective
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) :
    Function.Injective (finiteCoordinateLinear 𝕜 m) := by
  intro v w h
  -- First cancel the domain-extension map on finitely supported functions.
  apply (Finsupp.linearEquivFunOnFinite 𝕜 𝕜 (Fin (m + 1))).symm.injective
  apply Finsupp.mapDomain_injective (fun i j hij => Fin.ext hij)
  simpa [finiteCoordinateLinear, Finsupp.lmapDomain_apply] using h

/-- Helper for Problem 9.7.6: the image of a finite vector is supported inside the first
`m + 1` coordinates. -/
private theorem finiteCoordinateLinear_support_subset
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) (v : Fin (m + 1) → 𝕜) :
    ↑((finiteCoordinateLinear 𝕜 m v).support) ⊆ Finset.range (m + 1) := by
  -- Outside the first `m + 1` coordinates, the embedded vector vanishes.
  rw [Finset.subset_range]
  intro n hn
  by_contra hnot
  have hnotRange : n ∉ Finset.range (m + 1) := by
    simpa [Finset.mem_range] using hnot
  have hzero := finiteCoordinateLinear_apply_of_not_mem_range 𝕜 m v hnotRange
  have hnotMem : n ∉ (finiteCoordinateLinear 𝕜 m v).support := by
    simpa [Finsupp.mem_support_iff] using hzero
  exact hnotMem hn

/-- Helper for Problem 9.7.6: the `m`th support-bounded stage in the projectivization model
`ℙ 𝕜 (ℕ →₀ 𝕜)` consists of classes admitting a representative supported in the first `m + 1`
coordinates. -/
private def projectivizationSupportStage
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) : Set (ℙ 𝕜 (ℕ →₀ 𝕜)) :=
  {x | ∃ v : ℕ →₀ 𝕜, ∃ hv : v ≠ 0,
      Projectivization.mk 𝕜 v hv = x ∧ ↑v.support ⊆ Finset.range (m + 1)}

/-- Helper for Problem 9.7.6: the support stages of `RP^∞` are the bounded-support projective
classes in `ℙ ℝ (ℕ →₀ ℝ)`. -/
private abbrev realProjectiveInfinitySupportStage (m : ℕ) : Set RealProjectiveInfinity :=
  projectivizationSupportStage ℝ m

/-- Helper for Problem 9.7.6: a projective class lies in the `m`th support stage exactly when
any chosen representative is supported in the first `m + 1` coordinates. -/
private theorem mk_mem_projectivizationSupportStage_iff_support_subset
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) (v : ℕ →₀ 𝕜) (hv : v ≠ 0) :
    Projectivization.mk 𝕜 v hv ∈ projectivizationSupportStage 𝕜 m ↔
      ↑v.support ⊆ Finset.range (m + 1) := by
  constructor
  · intro hx
    rcases hx with ⟨w, hw, hEq, hsupport⟩
    rcases (Projectivization.mk_eq_mk_iff' 𝕜 w v hw hv).1 hEq with ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      have hw0 : w = 0 := by
        simpa [ha0] using ha.symm
      exact hw hw0
    intro n hn
    have hvn : v n ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using hn
    have hwn : w n ≠ 0 := by
      intro hwn
      apply hvn
      have hmul : a * v n = 0 := by simpa [smul_eq_mul, hwn] using congrArg (fun f ↦ f n) ha
      exact (mul_eq_zero.mp hmul).resolve_left ha0
    exact hsupport (by simpa [Finsupp.mem_support_iff] using hwn)
  · intro hsupport
    refine ⟨v, hv, rfl, hsupport⟩

/-- Helper for Problem 9.7.6: the projective class of the vector supported on coordinates
`0` and `m + 1` cannot lie in the `m`th support stage. -/
private theorem single_add_single_not_mem_projectivizationSupportStage
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] (m : ℕ) :
    let v : ℕ →₀ 𝕜 := escapingCoordinateVector 𝕜 m
    Projectivization.mk 𝕜 v (by
        exact escapingCoordinateVector_nonzero 𝕜 m) ∉ projectivizationSupportStage 𝕜 m := by
  intro v
  intro hx
  have hsupport :
      ↑v.support ⊆ Finset.range (m + 1) :=
    (mk_mem_projectivizationSupportStage_iff_support_subset 𝕜 m v
      (escapingCoordinateVector_nonzero 𝕜 m) ).1 hx
  have hmem : m + 1 ∈ v.support := by
    rw [Finsupp.mem_support_iff]
    simp [v, escapingCoordinateVector]
  have : m + 1 ∈ Finset.range (m + 1) := hsupport hmem
  simpa [Finset.mem_range] using this

/-- Helper for Problem 9.7.6: enlarging the cutoff enlarges the bounded-support projective stage. -/
private theorem projectivizationSupportStage_mono
    (𝕜 : Type*) [DivisionRing 𝕜] :
    Monotone (projectivizationSupportStage 𝕜) := by
  intro i j hij x hx
  rcases hx with ⟨v, hv, rfl, hsupport⟩
  refine ⟨v, hv, rfl, ?_⟩
  -- The same representative works after increasing the allowed support range.
  exact hsupport.trans (Finset.range_subset_range.2 (Nat.succ_le_succ hij))

/-- Helper for Problem 9.7.6: every point of `ℙ 𝕜 (ℕ →₀ 𝕜)` lies in some finite support stage. -/
private theorem mem_projectivizationSupportStage
    (𝕜 : Type*) [DivisionRing 𝕜] (x : ℙ 𝕜 (ℕ →₀ 𝕜)) :
    ∃ m, x ∈ projectivizationSupportStage 𝕜 m := by
  refine ⟨x.rep.support.sup id, x.rep, x.rep_nonzero, Projectivization.mk_rep x, ?_⟩
  -- A finite-support representative is contained in the range cut off at one plus its support sup.
  simpa using Finset.subset_range_sup_succ x.rep.support

/-- Helper for Problem 9.7.6: the chosen basepoint of `RP^∞` already lies in the initial support
stage. -/
private theorem realProjectiveInfinityBasepoint_mem_supportStage_zero :
    realProjectiveInfinityBasepoint ∈ realProjectiveInfinitySupportStage 0 := by
  refine ⟨Finsupp.single 0 (1 : ℝ), by simp, rfl, ?_⟩
  -- The chosen representative uses only the zeroth coordinate.
  intro n hn
  have hzero : n = 0 := by
    by_contra hne
    have hn' : (Finsupp.single 0 (1 : ℝ)) n ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using hn
    exact hn' (by simp [hne])
  simp [hzero]

/-- Helper for Problem 9.7.6: every point of `RP^∞` has a representative supported in some finite
initial segment. -/
private theorem realProjectiveInfinity_mem_supportStage (x : RealProjectiveInfinity) :
    ∃ m, x ∈ realProjectiveInfinitySupportStage m :=
  mem_projectivizationSupportStage ℝ x

/-- Helper for Problem 9.7.6: the finite projective space `ℙ 𝕜 (Fin (m + 1) → 𝕜)` maps into the
countable projective model by extending coordinates by zero. -/
private noncomputable def finiteProjectivizationToInfinity
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) :
    ℙ 𝕜 (Fin (m + 1) → 𝕜) → ℙ 𝕜 (ℕ →₀ 𝕜) :=
  Projectivization.map (finiteCoordinateLinear 𝕜 m) (finiteCoordinateLinear_injective 𝕜 m)

/-- Helper for Problem 9.7.6: the finite-coordinate projectivization map lands in the bounded
support stage with the same cutoff. -/
private theorem finiteProjectivizationToInfinity_mem_supportStage
    (𝕜 : Type*) [DivisionRing 𝕜] (m : ℕ) (x : ℙ 𝕜 (Fin (m + 1) → 𝕜)) :
    finiteProjectivizationToInfinity 𝕜 m x ∈ projectivizationSupportStage 𝕜 m := by
  induction x using Projectivization.ind with
  | h v hv =>
      refine ⟨finiteCoordinateLinear 𝕜 m v, ?_, ?_, finiteCoordinateLinear_support_subset 𝕜 m v⟩
      · intro hzero
        have hzero' : (finiteCoordinateLinear 𝕜 m) v = (finiteCoordinateLinear 𝕜 m) 0 := by
          simpa using hzero
        exact hv ((finiteCoordinateLinear_injective 𝕜 m) hzero')
      · -- The projectivization map is defined by applying the linear embedding to representatives.
        simpa [finiteProjectivizationToInfinity] using
          (Projectivization.map_mk (finiteCoordinateLinear 𝕜 m)
            (finiteCoordinateLinear_injective 𝕜 m) v hv).symm

/-- Helper for Problem 9.7.6: the real coordinate space `ℕ →₀ ℝ` has rank greater than `1`. -/
private theorem realProjectiveInfinityCoordinates_one_lt_rank :
    1 < Module.rank ℝ (ℕ →₀ ℝ) := by
  -- Two standard basis vectors already witness a real two-dimensional subspace.
  have hlin : LinearIndependent ℝ (fun i : Fin 2 ↦ Finsupp.single (i : ℕ) (1 : ℝ)) := by
    simpa [Finsupp.coe_basisSingleOne] using
      (Finsupp.basisSingleOne (ι := ℕ) (R := ℝ)).linearIndependent.comp
        (fun i : Fin 2 ↦ (i : ℕ)) fun i j hij => Fin.ext hij
  have htwo : (2 : Cardinal) ≤ Module.rank ℝ (ℕ →₀ ℝ) := by
    simpa using hlin.cardinal_lift_le_rank
  exact lt_of_lt_of_le (by norm_num : (1 : Cardinal) < 2) htwo

/-- Helper for Problem 9.7.6: removing the origin from `ℕ →₀ ℝ` leaves a path-connected space. -/
private theorem realProjectiveInfinityCoordinates_nonzero_pathConnected :
    PathConnectedSpace {v : ℕ →₀ ℝ // v ≠ 0} := by
  -- The complement of a point in a real vector space of rank `> 1` is path connected.
  rw [pathConnectedSpace_iff_univ]
  simpa [Set.setOf_mem_eq] using
    (isPathConnected_compl_singleton_of_one_lt_rank
      realProjectiveInfinityCoordinates_one_lt_rank 0).preimage_coe subset_rfl

/-- Helper for Problem 9.7.6: `RP^∞ = ℙ ℝ (ℕ →₀ ℝ)` is path connected. -/
private theorem realProjectiveInfinity_pathConnected :
    PathConnectedSpace RealProjectiveInfinity := by
  -- Pass path connectedness through the quotient map defining projectivization.
  let _ : PathConnectedSpace {v : ℕ →₀ ℝ // v ≠ 0} :=
    realProjectiveInfinityCoordinates_nonzero_pathConnected
  letI : Setoid {v : ℕ →₀ ℝ // v ≠ 0} := projectivizationSetoid ℝ (ℕ →₀ ℝ)
  exact Function.Surjective.pathConnectedSpace Quotient.mk'_surjective continuous_quotient_mk'

/-- The topology on countably supported complex coordinates induced from the product space
`ℕ → ℂ`. -/
instance complexProjectiveInfinityCoordinatesTopologicalSpace : TopologicalSpace (ℕ →₀ ℂ) :=
  TopologicalSpace.induced (fun f ↦ (f : ℕ → ℂ)) inferInstance

/-- Helper for Problem 9.7.6: the induced topology on `ℕ →₀ ℂ` is compatible with addition. -/
private instance complexProjectiveInfinityCoordinatesContinuousAdd : ContinuousAdd (ℕ →₀ ℂ) := by
  -- Transfer continuity from the ambient product topology on `ℕ → ℂ`.
  refine ⟨continuous_induced_rng.2 ?_⟩
  exact
    (continuous_induced_dom.fst'.add continuous_induced_dom.snd' :
      Continuous fun p : (ℕ →₀ ℂ) × (ℕ →₀ ℂ) => ((p.1 : ℕ → ℂ) + (p.2 : ℕ → ℂ)))

/-- Helper for Problem 9.7.6: the induced topology on `ℕ →₀ ℂ` is compatible with complex scalar
multiplication. -/
private instance complexProjectiveInfinityCoordinatesContinuousSMul :
    ContinuousSMul ℂ (ℕ →₀ ℂ) := by
  -- This is the ambient function-space `ℂ`-action restricted to finite support.
  refine ⟨continuous_induced_rng.2 ?_⟩
  exact
    (continuous_fst.smul continuous_induced_dom.snd' :
      Continuous fun p : ℂ × (ℕ →₀ ℂ) => p.1 • ((p.2 : ℕ → ℂ)))

/-- Helper for Problem 9.7.6: the induced topology on `ℕ →₀ ℂ` is compatible with the restricted
real scalar action. -/
private instance complexProjectiveInfinityCoordinatesContinuousRealSMul :
    ContinuousSMul ℝ (ℕ →₀ ℂ) := by
  -- We rewrite the real action through `Complex.ofReal` and use coordinatewise multiplication.
  refine ⟨continuous_induced_rng.2 ?_⟩
  refine continuous_pi fun i ↦ ?_
  let hvec : Continuous fun p : ℝ × (ℕ →₀ ℂ) => (p.2 : ℕ → ℂ) := continuous_induced_dom.snd'
  simpa [smul_eq_mul, mul_comm] using
    (Continuous.mul
      ((continuous_apply i).comp hvec)
      (show Continuous fun p : ℝ × (ℕ →₀ ℂ) => (p.1 : ℂ) from
        Complex.continuous_ofReal.comp continuous_fst) :
      Continuous fun p : ℝ × (ℕ →₀ ℂ) => ((p.2 : ℕ → ℂ) i) * (p.1 : ℂ))

/-- The workspace's canonical projectivization model of `CP^∞`. -/
abbrev ComplexProjectiveInfinity := ℙ ℂ (ℕ →₀ ℂ)

/-- The quotient topology on the projectivization model of `CP^∞`. -/
instance complexProjectiveInfinityTopologicalSpace : TopologicalSpace ComplexProjectiveInfinity :=
  instTopologicalSpaceQuotient

/-- A concrete basepoint of `CP^∞`, represented by the first coordinate line. -/
def complexProjectiveInfinityBasepoint : ComplexProjectiveInfinity :=
  Projectivization.mk ℂ (Finsupp.single 0 (1 : ℂ)) <| by
    simp

/-- Helper for Problem 9.7.6: the support stages of `CP^∞` are the bounded-support projective
classes in `ℙ ℂ (ℕ →₀ ℂ)`. -/
private abbrev complexProjectiveInfinitySupportStage (m : ℕ) : Set ComplexProjectiveInfinity :=
  projectivizationSupportStage ℂ m

/-- Helper for Problem 9.7.6: the chosen basepoint of `CP^∞` already lies in the initial support
stage. -/
private theorem complexProjectiveInfinityBasepoint_mem_supportStage_zero :
    complexProjectiveInfinityBasepoint ∈ complexProjectiveInfinitySupportStage 0 := by
  refine ⟨Finsupp.single 0 (1 : ℂ), by simp, rfl, ?_⟩
  -- The chosen representative uses only the zeroth coordinate.
  intro n hn
  have hzero : n = 0 := by
    by_contra hne
    have hn' : (Finsupp.single 0 (1 : ℂ)) n ≠ 0 := by
      simpa [Finsupp.mem_support_iff] using hn
    exact hn' (by simp [hne])
  simp [hzero]

/-- Helper for Problem 9.7.6: every point of `CP^∞` has a representative supported in some finite
initial segment. -/
private theorem complexProjectiveInfinity_mem_supportStage (x : ComplexProjectiveInfinity) :
    ∃ m, x ∈ complexProjectiveInfinitySupportStage m :=
  mem_projectivizationSupportStage ℂ x

/-- Helper for Problem 9.7.6: the complex coordinate space `ℕ →₀ ℂ`, viewed as a real vector
space, has rank greater than `1`. -/
private theorem complexProjectiveInfinityCoordinates_one_lt_realRank :
    1 < Module.rank ℝ (ℕ →₀ ℂ) := by
  -- Restrict scalars on two complex coordinate vectors to obtain a real two-dimensional family.
  have hlin : LinearIndependent ℝ (fun i : Fin 2 ↦ Finsupp.single (i : ℕ) (1 : ℂ)) := by
    simpa [Finsupp.coe_basisSingleOne] using
      LinearIndependent.restrict_scalars' ℝ
        ((Finsupp.basisSingleOne (ι := ℕ) (R := ℂ)).linearIndependent.comp
          (fun i : Fin 2 ↦ (i : ℕ)) fun i j hij => Fin.ext hij)
  have htwo : (2 : Cardinal) ≤ Module.rank ℝ (ℕ →₀ ℂ) := by
    simpa using hlin.cardinal_lift_le_rank
  exact lt_of_lt_of_le (by norm_num : (1 : Cardinal) < 2) htwo

/-- Helper for Problem 9.7.6: removing the origin from `ℕ →₀ ℂ` leaves a path-connected space. -/
private theorem complexProjectiveInfinityCoordinates_nonzero_pathConnected :
    PathConnectedSpace {v : ℕ →₀ ℂ // v ≠ 0} := by
  -- The same complement-of-a-point argument works after restricting scalars to `ℝ`.
  rw [pathConnectedSpace_iff_univ]
  simpa [Set.setOf_mem_eq] using
    (isPathConnected_compl_singleton_of_one_lt_rank
      complexProjectiveInfinityCoordinates_one_lt_realRank 0).preimage_coe subset_rfl

/-- Helper for Problem 9.7.6: `CP^∞ = ℙ ℂ (ℕ →₀ ℂ)` is path connected. -/
private theorem complexProjectiveInfinity_pathConnected :
    PathConnectedSpace ComplexProjectiveInfinity := by
  -- As in the real case, projectivization is a quotient of the punctured coordinate space.
  let _ : PathConnectedSpace {v : ℕ →₀ ℂ // v ≠ 0} :=
    complexProjectiveInfinityCoordinates_nonzero_pathConnected
  letI : Setoid {v : ℕ →₀ ℂ // v ≠ 0} := projectivizationSetoid ℂ (ℕ →₀ ℂ)
  exact Function.Surjective.pathConnectedSpace Quotient.mk'_surjective continuous_quotient_mk'

/-- Helper for Problem 9.7.6: if the coordinate shift on `ℕ →₀ 𝕜` is continuous, then the
punctured coordinate space contracts to the first basis vector by the shift homotopy. -/
private theorem puncturedCoordinates_contractible_of_shiftContinuous
    (𝕜 : Type*) [NormedDivisionRing 𝕜] [NormedAlgebra ℝ 𝕜]
    [TopologicalSpace (ℕ →₀ 𝕜)] [ContinuousAdd (ℕ →₀ 𝕜)] [ContinuousSMul ℝ (ℕ →₀ 𝕜)]
    (hshift : Continuous fun v : ℕ →₀ 𝕜 ↦ Finsupp.mapDomain Nat.succ v) :
    ContractibleSpace {v : ℕ →₀ 𝕜 // v ≠ 0} := by
  -- Route correction: the support-stage filtration is the wrong skeleton here, so we contract the
  -- punctured coordinate space directly by shifting support while keeping a nonzero zeroth
  -- coordinate throughout the homotopy.
  rw [contractible_iff_id_nullhomotopic]
  -- First fix the target basepoint at the first basis vector.
  have hx0 :
      (Finsupp.single 0 (1 : 𝕜) : ℕ →₀ 𝕜) ≠ 0 := by
    simp
  let x0 : {v : ℕ →₀ 𝕜 // v ≠ 0} := ⟨Finsupp.single 0 (1 : 𝕜), hx0⟩
  -- The shift always kills the zeroth coordinate.
  have hshift_zero :
      ∀ v : ℕ →₀ 𝕜, Finsupp.mapDomain Nat.succ v 0 = 0 := by
    intro v
    exact Finsupp.mapDomain_notin_range v 0 (by simp)
  -- The intermediate map adds the shifted vector to the fixed basis vector.
  have hshiftBasepoint_nonzero :
      ∀ v : {v : ℕ →₀ 𝕜 // v ≠ 0},
        Finsupp.single 0 (1 : 𝕜) + Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜) ≠ 0 := by
    intro v
    intro hzero
    have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f 0) hzero
    simpa [hshift_zero (v : ℕ →₀ 𝕜)] using hcoord
  -- This map is continuous because it is built from addition and the continuous shift.
  have hshiftBasepoint_continuous :
      Continuous fun v : {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
        (⟨Finsupp.single 0 (1 : 𝕜) + Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜),
          hshiftBasepoint_nonzero v⟩ : {v : ℕ →₀ 𝕜 // v ≠ 0}) := by
    have hambient :
        Continuous fun v : {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          Finsupp.single 0 (1 : 𝕜) + Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜) := by
      exact continuous_const.add (hshift.comp continuous_subtype_val)
    exact hambient.subtype_mk hshiftBasepoint_nonzero
  let shiftBasepoint :
      C({v : ℕ →₀ 𝕜 // v ≠ 0}, {v : ℕ →₀ 𝕜 // v ≠ 0}) :=
    ⟨fun v ↦
      ⟨Finsupp.single 0 (1 : 𝕜) + Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜),
        hshiftBasepoint_nonzero v⟩,
      hshiftBasepoint_continuous⟩
  -- Stage one interpolates from the identity to the shifted-basepoint map.
  have hstageOne_nonzero :
      ∀ sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0},
        (1 - (sv.1 : ℝ)) • (sv.2 : ℕ →₀ 𝕜) +
            (sv.1 : ℝ) • Finsupp.single 0 (1 : 𝕜) +
            (sv.1 : ℝ) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜) ≠ 0 := by
    intro sv
    by_cases hs : (sv.1 : ℝ) = 0
    · intro hzero
      have : (sv.2 : ℕ →₀ 𝕜) = 0 := by
        simpa [hs] using hzero
      exact sv.2.2 this
    · have hsupp :
          (sv.2 : ℕ →₀ 𝕜).support.Nonempty :=
        Finsupp.support_nonempty_iff.mpr sv.2.2
      let n := (sv.2 : ℕ →₀ 𝕜).support.max' hsupp
      have hvn : (sv.2 : ℕ →₀ 𝕜) n ≠ 0 := by
        exact Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
      have hnotMem : n + 1 ∉ (sv.2 : ℕ →₀ 𝕜).support := by
        intro hmem
        have hle : n + 1 ≤ n :=
          Finset.le_max' _ _ hmem
        omega
      have hzeroNext : (sv.2 : ℕ →₀ 𝕜) (n + 1) = 0 := by
        by_contra hnext
        exact hnotMem (Finsupp.mem_support_iff.mpr hnext)
      intro hzero
      have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f (n + 1)) hzero
      have hsmulZero :
          (sv.1 : ℝ) • (sv.2 : ℕ →₀ 𝕜) n = 0 := by
        simpa [Finsupp.mapDomain_apply (by
          intro a b h
          exact Nat.succ.inj h), hzeroNext, Nat.succ_ne_zero] using hcoord
      exact hvn ((smul_eq_zero.mp hsmulZero).resolve_left hs)
  -- The ambient formula is continuous term-by-term.
  have hstageOne_continuous :
      Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
        (⟨(1 - (sv.1 : ℝ)) • (sv.2 : ℕ →₀ 𝕜) +
            (sv.1 : ℝ) • Finsupp.single 0 (1 : 𝕜) +
            (sv.1 : ℝ) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜),
          hstageOne_nonzero sv⟩ : {v : ℕ →₀ 𝕜 // v ≠ 0}) := by
    have hs :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦ (sv.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hv :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦ (sv.2 : ℕ →₀ 𝕜) :=
      continuous_subtype_val.comp continuous_snd
    have hshiftSub :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜) :=
      hshift.comp hv
    have hleft :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          (1 - (sv.1 : ℝ)) • (sv.2 : ℕ →₀ 𝕜) := by
      exact (continuous_const.sub hs).smul hv
    have hmid :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          (sv.1 : ℝ) • Finsupp.single 0 (1 : 𝕜) := by
      exact hs.smul continuous_const
    have hright :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          (sv.1 : ℝ) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜) := by
      exact hs.smul hshiftSub
    have hambient :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          (1 - (sv.1 : ℝ)) • (sv.2 : ℕ →₀ 𝕜) +
            (sv.1 : ℝ) • Finsupp.single 0 (1 : 𝕜) +
            (sv.1 : ℝ) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜) := by
      simpa [add_assoc] using hleft.add (hmid.add hright)
    exact hambient.subtype_mk hstageOne_nonzero
  -- Checking the endpoints shows that stage one starts at `id` and ends at `shiftBasepoint`.
  have hstageOne_zero :
      ∀ v : {v : ℕ →₀ 𝕜 // v ≠ 0},
        (⟨(1 - ((0 : I) : ℝ)) • (v : ℕ →₀ 𝕜) +
            ((0 : I) : ℝ) • Finsupp.single 0 (1 : 𝕜) +
            ((0 : I) : ℝ) • Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜),
          hstageOne_nonzero (0, v)⟩ : {v : ℕ →₀ 𝕜 // v ≠ 0}) = v := by
    intro v
    apply Subtype.ext
    simp
  have hstageOne_one :
      ∀ v : {v : ℕ →₀ 𝕜 // v ≠ 0},
        (⟨(1 - ((1 : I) : ℝ)) • (v : ℕ →₀ 𝕜) +
            ((1 : I) : ℝ) • Finsupp.single 0 (1 : 𝕜) +
            ((1 : I) : ℝ) • Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜),
          hstageOne_nonzero (1, v)⟩ : {v : ℕ →₀ 𝕜 // v ≠ 0}) = shiftBasepoint v := by
    intro v
    apply Subtype.ext
    simp [shiftBasepoint]
  refine ⟨x0, ?_⟩
  let H₁ : (ContinuousMap.id {v : ℕ →₀ 𝕜 // v ≠ 0}).Homotopy shiftBasepoint := by
    exact
      { toFun := fun sv ↦
          ⟨(1 - (sv.1 : ℝ)) • (sv.2 : ℕ →₀ 𝕜) +
              (sv.1 : ℝ) • Finsupp.single 0 (1 : 𝕜) +
              (sv.1 : ℝ) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜),
            hstageOne_nonzero sv⟩
        continuous_toFun := hstageOne_continuous
        map_zero_left := hstageOne_zero
        map_one_left := hstageOne_one }
  -- Stage two collapses the shifted tail while keeping the zeroth coordinate equal to `1`.
  have hstageTwo_nonzero :
      ∀ sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0},
        Finsupp.single 0 (1 : 𝕜) +
            (1 - (sv.1 : ℝ)) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜) ≠ 0 := by
    intro sv
    intro hzero
    have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f 0) hzero
    simpa [hshift_zero (sv.2 : ℕ →₀ 𝕜)] using hcoord
  -- This second stage is also continuous by the same coordinatewise argument.
  have hstageTwo_continuous :
      Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
        (⟨Finsupp.single 0 (1 : 𝕜) +
            (1 - (sv.1 : ℝ)) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜),
          hstageTwo_nonzero sv⟩ : {v : ℕ →₀ 𝕜 // v ≠ 0}) := by
    have hs :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦ (sv.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hv :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦ (sv.2 : ℕ →₀ 𝕜) :=
      continuous_subtype_val.comp continuous_snd
    have hshiftSub :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜) :=
      hshift.comp hv
    have hambient :
        Continuous fun sv : I × {v : ℕ →₀ 𝕜 // v ≠ 0} ↦
          Finsupp.single 0 (1 : 𝕜) +
            (1 - (sv.1 : ℝ)) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜) := by
      exact continuous_const.add ((continuous_const.sub hs).smul hshiftSub)
    exact hambient.subtype_mk hstageTwo_nonzero
  -- The endpoints identify stage two with `shiftBasepoint` and the constant map.
  have hstageTwo_zero :
      ∀ v : {v : ℕ →₀ 𝕜 // v ≠ 0},
        (⟨Finsupp.single 0 (1 : 𝕜) +
            (1 - ((0 : I) : ℝ)) • Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜),
          hstageTwo_nonzero (0, v)⟩ : {v : ℕ →₀ 𝕜 // v ≠ 0}) = shiftBasepoint v := by
    intro v
    apply Subtype.ext
    simp [shiftBasepoint]
  have hstageTwo_one :
      ∀ v : {v : ℕ →₀ 𝕜 // v ≠ 0},
        (⟨Finsupp.single 0 (1 : 𝕜) +
            (1 - ((1 : I) : ℝ)) • Finsupp.mapDomain Nat.succ (v : ℕ →₀ 𝕜),
          hstageTwo_nonzero (1, v)⟩ : {v : ℕ →₀ 𝕜 // v ≠ 0}) =
          ContinuousMap.const _ x0 v := by
    intro v
    apply Subtype.ext
    simp [x0]
  let H₂ :
      shiftBasepoint.Homotopy
        (ContinuousMap.const {v : ℕ →₀ 𝕜 // v ≠ 0} x0) := by
    exact
      { toFun := fun sv ↦
          ⟨Finsupp.single 0 (1 : 𝕜) +
              (1 - (sv.1 : ℝ)) • Finsupp.mapDomain Nat.succ (sv.2 : ℕ →₀ 𝕜),
            hstageTwo_nonzero sv⟩
        continuous_toFun := hstageTwo_continuous
        map_zero_left := hstageTwo_zero
        map_one_left := hstageTwo_one }
  exact ⟨H₁.trans H₂⟩

/-- Helper for Problem 9.7.6: the coordinate shift on `ℕ →₀ ℝ` is continuous in the induced
product topology. -/
private theorem realCoordinateShift_continuous :
    Continuous fun v : ℕ →₀ ℝ ↦ Finsupp.mapDomain Nat.succ v := by
  -- Each output coordinate is either zero or one of the input coordinates.
  refine continuous_induced_rng.2 ?_
  refine continuous_pi fun n ↦ ?_
  cases n with
  | zero =>
      have hzero :
          (fun v : ℕ →₀ ℝ ↦ (Finsupp.mapDomain Nat.succ v) 0) = fun _ : ℕ →₀ ℝ ↦ (0 : ℝ) := by
        funext v
        exact Finsupp.mapDomain_notin_range v 0 (by simp)
      simpa [hzero] using (continuous_const : Continuous fun _ : ℕ →₀ ℝ ↦ (0 : ℝ))
  | succ m =>
      simpa [Finsupp.mapDomain_apply (by
        intro a b h
        exact Nat.succ.inj h)] using
        (show Continuous fun v : ℕ →₀ ℝ ↦ (v : ℕ → ℝ) m from
          (continuous_apply m).comp continuous_induced_dom)

/-- Helper for Problem 9.7.6: the punctured real coordinate space is contractible. -/
private theorem realProjectiveInfinityPuncturedCoordinates_contractible :
    ContractibleSpace {v : ℕ →₀ ℝ // v ≠ 0} := by
  -- Specialize the generic shift homotopy to the real coordinate model.
  exact puncturedCoordinates_contractible_of_shiftContinuous ℝ realCoordinateShift_continuous

/-- Helper for Problem 9.7.6: all homotopy groups of the punctured real coordinate space are
trivial. -/
private theorem realProjectiveInfinityPuncturedCoordinates_homotopyGroup_subsingleton
    (n : ℕ) (x : {v : ℕ →₀ ℝ // v ≠ 0}) :
    Subsingleton (π_ n {v : ℕ →₀ ℝ // v ≠ 0} x) := by
  -- Contractibility reduces every homotopy group to the singleton group.
  let _ : ContractibleSpace {v : ℕ →₀ ℝ // v ≠ 0} :=
    realProjectiveInfinityPuncturedCoordinates_contractible
  exact homotopyGroup_subsingleton_of_contractible n x

/-- Helper for Problem 9.7.6: the coordinate shift on `ℕ →₀ ℂ` is continuous in the induced
product topology. -/
private theorem complexCoordinateShift_continuous :
    Continuous fun v : ℕ →₀ ℂ ↦ Finsupp.mapDomain Nat.succ v := by
  -- The complex case is the same coordinatewise continuity argument as the real case.
  refine continuous_induced_rng.2 ?_
  refine continuous_pi fun n ↦ ?_
  cases n with
  | zero =>
      have hzero :
          (fun v : ℕ →₀ ℂ ↦ (Finsupp.mapDomain Nat.succ v) 0) = fun _ : ℕ →₀ ℂ ↦ (0 : ℂ) := by
        funext v
        exact Finsupp.mapDomain_notin_range v 0 (by simp)
      simpa [hzero] using (continuous_const : Continuous fun _ : ℕ →₀ ℂ ↦ (0 : ℂ))
  | succ m =>
      simpa [Finsupp.mapDomain_apply (by
        intro a b h
        exact Nat.succ.inj h)] using
        (show Continuous fun v : ℕ →₀ ℂ ↦ (v : ℕ → ℂ) m from
          (continuous_apply m).comp continuous_induced_dom)

/-- Helper for Problem 9.7.6: the punctured complex coordinate space is contractible. -/
private theorem complexProjectiveInfinityPuncturedCoordinates_contractible :
    ContractibleSpace {v : ℕ →₀ ℂ // v ≠ 0} := by
  -- Specialize the generic shift homotopy to the complex coordinate model.
  exact
    @puncturedCoordinates_contractible_of_shiftContinuous
      ℂ inferInstance inferInstance complexProjectiveInfinityCoordinatesTopologicalSpace
      complexProjectiveInfinityCoordinatesContinuousAdd
      complexProjectiveInfinityCoordinatesContinuousRealSMul
      complexCoordinateShift_continuous

/-- Helper for Problem 9.7.6: all homotopy groups of the punctured complex coordinate space are
trivial. -/
private theorem complexProjectiveInfinityPuncturedCoordinates_homotopyGroup_subsingleton
    (n : ℕ) (x : {v : ℕ →₀ ℂ // v ≠ 0}) :
    Subsingleton (π_ n {v : ℕ →₀ ℂ // v ≠ 0} x) := by
  -- Contractibility reduces every homotopy group to the singleton group.
  let _ : ContractibleSpace {v : ℕ →₀ ℂ // v ≠ 0} :=
    complexProjectiveInfinityPuncturedCoordinates_contractible
  exact homotopyGroup_subsingleton_of_contractible n x

/-- Helper for Problem 9.7.6: the quotient map from punctured real coordinates to `RP^∞` is
surjective on points. -/
private theorem realProjectivizationQuotientMap_surjective :
    Function.Surjective (Projectivization.mk' ℝ : {v : ℕ →₀ ℝ // v ≠ 0} → RealProjectiveInfinity) := by
  -- Every projective point comes with a nonzero representative.
  intro x
  refine ⟨⟨x.rep, x.rep_nonzero⟩, ?_⟩
  simpa [Projectivization.mk'_eq_mk] using Projectivization.mk_rep x

/-- Helper for Problem 9.7.6: the quotient map from punctured complex coordinates to `CP^∞` is
surjective on points. -/
private theorem complexProjectivizationQuotientMap_surjective :
    Function.Surjective (Projectivization.mk' ℂ : {v : ℕ →₀ ℂ // v ≠ 0} → ComplexProjectiveInfinity) := by
  -- Every projective point comes with a nonzero representative.
  intro x
  refine ⟨⟨x.rep, x.rep_nonzero⟩, ?_⟩
  simpa [Projectivization.mk'_eq_mk] using Projectivization.mk_rep x

/-- Helper for Problem 9.7.6: a punctured coordinate vector projects to the basepoint line exactly
when it is a scalar multiple of the first basis vector, with scalar equal to its zeroth
coordinate. -/
private theorem projectivizationMk'_eq_basepoint_iff
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜]
    (v : {w : ℕ →₀ 𝕜 // w ≠ 0}) :
    Projectivization.mk' 𝕜 v =
        Projectivization.mk 𝕜 (Finsupp.single 0 (1 : 𝕜)) (by simp) ↔
      (v : ℕ →₀ 𝕜) = v.1 0 • Finsupp.single 0 (1 : 𝕜) := by
  constructor
  · intro hv
    -- First rewrite the projective equality as a scalar-multiple relation on representatives.
    rcases (Projectivization.mk_eq_mk_iff' 𝕜 (v : ℕ →₀ 𝕜)
        (Finsupp.single 0 (1 : 𝕜)) v.2 (by simp)).1 (by
          simpa [Projectivization.mk'_eq_mk] using hv) with ⟨a, ha⟩
    -- Evaluating at the zeroth coordinate identifies the scalar with `v 0`.
    have hcoord0 : a = v.1 0 := by
      simpa using congrArg (fun f : ℕ →₀ 𝕜 ↦ f 0) ha
    calc
      (v : ℕ →₀ 𝕜) = a • Finsupp.single 0 (1 : 𝕜) := ha.symm
      _ = v.1 0 • Finsupp.single 0 (1 : 𝕜) := by rw [hcoord0]
  · intro hv
    -- Conversely, a scalar multiple of the first basis vector spans the basepoint line.
    have hmk :
        Projectivization.mk 𝕜 (v : ℕ →₀ 𝕜) v.2 =
          Projectivization.mk 𝕜 (Finsupp.single 0 (1 : 𝕜)) (by simp) := by
      apply (Projectivization.mk_eq_mk_iff' 𝕜 (v : ℕ →₀ 𝕜)
        (Finsupp.single 0 (1 : 𝕜)) v.2 (by simp)).2
      exact ⟨v.1 0, hv.symm⟩
    simpa [Projectivization.mk'_eq_mk] using hmk

/-- Helper for Problem 9.7.6: the raw fiber of the projectivization quotient over the first
coordinate line is equivalent to the nonzero scalars on that line. -/
private noncomputable def projectivizationFiberEquivNonzeroScalars
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] :
    {v : {w : ℕ →₀ 𝕜 // w ≠ 0} //
        Projectivization.mk' 𝕜 v =
          Projectivization.mk 𝕜 (Finsupp.single 0 (1 : 𝕜)) (by simp)} ≃
      {a : 𝕜 // a ≠ 0} where
  toFun x := by
    -- The fiber equation forces the vector to be `(x 0) • e₀`, so the zeroth coordinate is
    -- the required nonzero scalar.
    refine ⟨x.1.1 0, ?_⟩
    intro hzero
    have hline :
        (x.1 : ℕ →₀ 𝕜) = x.1.1 0 • Finsupp.single 0 (1 : 𝕜) :=
      (projectivizationMk'_eq_basepoint_iff 𝕜 x.1).1 x.2
    apply x.1.2
    simpa [hzero] using hline
  invFun a := by
    -- A nonzero scalar on the first basis vector gives a nonzero representative of the basepoint
    -- line.
    refine ⟨⟨a.1 • Finsupp.single 0 (1 : 𝕜), ?_⟩, ?_⟩
    · intro hzero
      apply a.2
      have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f 0) hzero
      simpa using hcoord
    · have hmk :
          Projectivization.mk 𝕜 (a.1 • Finsupp.single 0 (1 : 𝕜)) (by
            intro hzero
            apply a.2
            have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f 0) hzero
            simpa using hcoord) =
            Projectivization.mk 𝕜 (Finsupp.single 0 (1 : 𝕜)) (by simp) := by
        apply (Projectivization.mk_eq_mk_iff' 𝕜
          (a.1 • Finsupp.single 0 (1 : 𝕜)) (Finsupp.single 0 (1 : 𝕜)) (by
            intro hzero
            apply a.2
            have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f 0) hzero
            simpa using hcoord) (by simp)).2
        exact ⟨a.1, rfl⟩
      simpa [Projectivization.mk'_eq_mk] using hmk
  left_inv x := by
    -- The normalization lemma reconstructs the original fiber point from its zeroth coordinate.
    apply Subtype.ext
    apply Subtype.ext
    exact ((projectivizationMk'_eq_basepoint_iff 𝕜 x.1).1 x.2).symm
  right_inv a := by
    -- Taking the zeroth coordinate of `a • e₀` recovers the original scalar.
    apply Subtype.ext
    simp

/-- Helper for Problem 9.7.6: the first basis vector gives the canonical punctured-coordinate
basepoint for the projectivization quotient. -/
private theorem projectivizationFirstBasis_nonzero
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] :
    (Finsupp.single 0 (1 : 𝕜) : ℕ →₀ 𝕜) ≠ 0 := by
  -- The zeroth coordinate is `1`, so the vector cannot vanish.
  simp

/-- Helper for Problem 9.7.6: the first basis vector gives the canonical punctured-coordinate
basepoint for the projectivization quotient. -/
private def projectivizationPuncturedBasepoint
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] :
    {w : ℕ →₀ 𝕜 // w ≠ 0} :=
  ⟨Finsupp.single 0 (1 : 𝕜), projectivizationFirstBasis_nonzero 𝕜⟩

/-- Helper for Problem 9.7.6: the first coordinate line is the canonical basepoint of
`ℙ 𝕜 (ℕ →₀ 𝕜)`. -/
private def projectivizationBasepoint
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] :
    ℙ 𝕜 (ℕ →₀ 𝕜) :=
  Projectivization.mk 𝕜 (Finsupp.single 0 (1 : 𝕜)) (projectivizationPuncturedBasepoint 𝕜).2

/-- Helper for Problem 9.7.6: the quotient map sends the chosen punctured-coordinate basepoint to
the chosen projective basepoint. -/
private theorem projectivizationMk'_puncturedBasepoint
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] :
    Projectivization.mk' 𝕜 (projectivizationPuncturedBasepoint 𝕜) =
      projectivizationBasepoint 𝕜 := by
  -- Both sides are the class of the first basis vector.
  simp [projectivizationPuncturedBasepoint, projectivizationBasepoint, Projectivization.mk'_eq_mk]

/-- Helper for Problem 9.7.6: rewriting the projective basepoint through
`projectivizationBasepoint 𝕜` keeps the scalar-line criterion unchanged. -/
private theorem projectivizationMk'_eq_projectivizationBasepoint_iff
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜]
    (v : {w : ℕ →₀ 𝕜 // w ≠ 0}) :
    Projectivization.mk' 𝕜 v = projectivizationBasepoint 𝕜 ↔
      (v : ℕ →₀ 𝕜) = v.1 0 • Finsupp.single 0 (1 : 𝕜) := by
  -- This is the earlier basepoint-line characterization with the canonical basepoint spelling.
  simpa [projectivizationBasepoint, projectivizationPuncturedBasepoint] using
    projectivizationMk'_eq_basepoint_iff 𝕜 v

/-- Helper for Problem 9.7.6: scaling the first basis vector by a nonzero scalar still gives a
nonzero punctured-coordinate representative. -/
private theorem projectivizationScaledFirstBasis_nonzero
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] (a : {z : 𝕜 // z ≠ 0}) :
    a.1 • Finsupp.single 0 (1 : 𝕜) ≠ 0 := by
  -- The zeroth coordinate equals the chosen nonzero scalar.
  intro hzero
  apply a.2
  have hcoord := congrArg (fun f : ℕ →₀ 𝕜 ↦ f 0) hzero
  simpa using hcoord

/-- Helper for Problem 9.7.6: any nonzero scalar multiple of the first basis vector projects to
the canonical projective basepoint. -/
private theorem projectivizationScaledFirstBasis_projectsToBasepoint
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] (a : {z : 𝕜 // z ≠ 0}) :
    Projectivization.mk' 𝕜
        ⟨a.1 • Finsupp.single 0 (1 : 𝕜), projectivizationScaledFirstBasis_nonzero 𝕜 a⟩ =
      projectivizationBasepoint 𝕜 := by
  -- Both representatives span the same projective line, so they define the same point.
  have hmk :
      Projectivization.mk 𝕜
          (a.1 • Finsupp.single 0 (1 : 𝕜))
          (projectivizationScaledFirstBasis_nonzero 𝕜 a) =
        projectivizationBasepoint 𝕜 := by
    -- The scalar `a` witnesses the projective equality directly.
    apply (Projectivization.mk_eq_mk_iff' 𝕜
      (a.1 • Finsupp.single 0 (1 : 𝕜))
      (Finsupp.single 0 (1 : 𝕜))
      (projectivizationScaledFirstBasis_nonzero 𝕜 a)
      (projectivizationPuncturedBasepoint 𝕜).2).2
    exact ⟨a.1, rfl⟩
  simpa [projectivizationBasepoint, Projectivization.mk'_eq_mk] using hmk

/-- Helper for Problem 9.7.6: the raw fiber over `projectivizationBasepoint 𝕜` is equivalent to
the nonzero scalars on the distinguished line. -/
private noncomputable def projectivizationBaseFiberEquivNonzeroScalars
    (𝕜 : Type*) [DivisionRing 𝕜] [Nontrivial 𝕜] :
    {v : {w : ℕ →₀ 𝕜 // w ≠ 0} //
        Projectivization.mk' 𝕜 v = projectivizationBasepoint 𝕜} ≃
      {a : 𝕜 // a ≠ 0} := by
  refine
    { toFun := fun x ↦ ?_
      invFun := fun a ↦ ?_
      left_inv := ?_
      right_inv := ?_ }
  · -- The zeroth coordinate is the nonzero scalar describing the point on the distinguished line.
    refine ⟨x.1.1 0, ?_⟩
    intro hzero
    have hline :
        (x.1 : ℕ →₀ 𝕜) = x.1.1 0 • Finsupp.single 0 (1 : 𝕜) :=
      (projectivizationMk'_eq_projectivizationBasepoint_iff 𝕜 x.1).1 x.2
    exact x.1.2 (by simpa [hzero] using hline)
  · -- Rebuild the fiber point from the scalar multiple of the first basis vector.
    exact
      ⟨⟨a.1 • Finsupp.single 0 (1 : 𝕜), projectivizationScaledFirstBasis_nonzero 𝕜 a⟩,
        projectivizationScaledFirstBasis_projectsToBasepoint 𝕜 a⟩
  · intro x
    -- The basepoint-line criterion reconstructs the original punctured vector.
    apply Subtype.ext
    apply Subtype.ext
    exact ((projectivizationMk'_eq_projectivizationBasepoint_iff 𝕜 x.1).1 x.2).symm
  · intro a
    -- Evaluating the rebuilt vector at coordinate `0` recovers the original scalar.
    apply Subtype.ext
    simp

/-- Helper for Problem 9.7.6: the projectivization of the finitely supported coordinate space
inherits the quotient topology from punctured coordinates. -/
private instance projectivizationCoordinatesTopologicalSpace
    (𝕜 : Type*) [DivisionRing 𝕜] [TopologicalSpace (ℕ →₀ 𝕜)] :
    TopologicalSpace (ℙ 𝕜 (ℕ →₀ 𝕜)) :=
  instTopologicalSpaceQuotient

/-- Helper for Problem 9.7.6: the quotient map from punctured coordinates to the projectivization
model is a quotient map. -/
private theorem projectivizationMk'_isQuotientMap
    (𝕜 : Type*) [DivisionRing 𝕜] [TopologicalSpace 𝕜] [TopologicalSpace (ℕ →₀ 𝕜)] :
    Topology.IsQuotientMap
      (Projectivization.mk' 𝕜 : {w : ℕ →₀ 𝕜 // w ≠ 0} → ℙ 𝕜 (ℕ →₀ 𝕜)) := by
  -- TODO: rewrite `Projectivization.mk'` through the quotient projection `Quotient.mk'` without
  -- the current coercion mismatch on `projectivizationSetoid`, then reuse
  -- `isQuotientMap_quotient_mk'`.
  sorry

/-- Helper for Problem 9.7.6: each standard coordinate chart in the projectivization model is
open. -/
private theorem projectivizationCoordinateBaseSet_open
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜]
    [TopologicalSpace 𝕜] [T1Space 𝕜] [TopologicalSpace (ℕ →₀ 𝕜)] (n : ℕ) :
    IsOpen (Problem_9_7_6.projectivizationCoordinateBaseSet 𝕜 n) := by
  -- TODO: once `projectivizationMk'_isQuotientMap` is available, transport openness from the
  -- representative locus `{v | v n ≠ 0}` through the quotient-map characterization.
  sorry

/-- Helper for Problem 9.7.6: outside the chosen coordinate chart, the raw section falls back to
the distinguished punctured-coordinate basepoint. -/
private def projectivizationCoordinateSectionRaw
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜] [DecidableEq 𝕜] (n : ℕ)
    (v : {w : ℕ →₀ 𝕜 // w ≠ 0}) :
    {w : ℕ →₀ 𝕜 // w ≠ 0} :=
  if hv : (v : ℕ →₀ 𝕜) n ≠ 0 then
    ⟨Problem_9_7_6.projectivizationCoordinateNormalize 𝕜 n v,
      Problem_9_7_6.projectivizationCoordinateNormalize_nonzero (𝕜 := 𝕜) n v hv⟩
  else
    projectivizationPuncturedBasepoint 𝕜

/-- Helper for Problem 9.7.6: the raw chart-section formula is constant on projective equivalence
classes. -/
private theorem projectivizationCoordinateSectionRaw_eq_of_projectiveEq
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜] [DecidableEq 𝕜] (n : ℕ)
    (a b : {w : ℕ →₀ 𝕜 // w ≠ 0}) (t : 𝕜)
    (h : (a : ℕ →₀ 𝕜) = t • (b : ℕ →₀ 𝕜)) :
    projectivizationCoordinateSectionRaw 𝕜 n a =
      projectivizationCoordinateSectionRaw 𝕜 n b := by
  by_cases hb : (b : ℕ →₀ 𝕜) n = 0
  · have ha : (a : ℕ →₀ 𝕜) n = 0 := by
      have hcoord : (a : ℕ →₀ 𝕜) n = t * (b : ℕ →₀ 𝕜) n := by
        simpa using congrArg (fun f : ℕ →₀ 𝕜 ↦ f n) h
      simpa [hb] using hcoord
    simp [projectivizationCoordinateSectionRaw, ha, hb]
  · have ha : (a : ℕ →₀ 𝕜) n ≠ 0 := by
      intro hzero
      have ht : t ≠ 0 := by
        intro ht
        apply a.2
        simpa [h, ht] using h
      have hcoord : (a : ℕ →₀ 𝕜) n = t * (b : ℕ →₀ 𝕜) n := by
        simpa using congrArg (fun f : ℕ →₀ 𝕜 ↦ f n) h
      have hmul : t * (b : ℕ →₀ 𝕜) n = 0 := by
        simpa [hzero] using hcoord
      exact hb ((mul_eq_zero.mp hmul).resolve_left ht)
    simp [projectivizationCoordinateSectionRaw, ha, hb]
    exact Problem_9_7_6.projectivizationCoordinateNormalize_eq_of_projectiveEq
      (𝕜 := 𝕜) n a b t h

/-- Helper for Problem 9.7.6: descend the normalized representative on the `n`th coordinate chart
to a projective-space function. -/
private noncomputable def projectivizationCoordinateSectionDesc
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜] [DecidableEq 𝕜] (n : ℕ) :
    ℙ 𝕜 (ℕ →₀ 𝕜) → {w : ℕ →₀ 𝕜 // w ≠ 0} :=
  Projectivization.lift
    (projectivizationCoordinateSectionRaw 𝕜 n)
    (projectivizationCoordinateSectionRaw_eq_of_projectiveEq (𝕜 := 𝕜) n)

/-- Helper for Problem 9.7.6: the descended normalized representative is continuous on its
coordinate chart. -/
private theorem projectivizationCoordinateSectionDesc_continuousOn
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜] [DecidableEq 𝕜]
    [TopologicalSpace 𝕜] [T1Space 𝕜] [ContinuousInv 𝕜] [TopologicalSpace (ℕ →₀ 𝕜)]
    [ContinuousSMul 𝕜 (ℕ →₀ 𝕜)] (n : ℕ) :
    ContinuousOn (projectivizationCoordinateSectionDesc 𝕜 n)
      (Problem_9_7_6.projectivizationCoordinateBaseSet 𝕜 n) := by
  -- TODO: combine `projectivizationCoordinateBaseSet_open` with the quotient-map criterion
  -- `Topology.IsQuotientMap.continuousOn_isOpen_iff`, then compare the restricted quotient lift
  -- with the explicit normalization map on the representative chart locus.
  sorry

/-- Helper for Problem 9.7.6: the `n`th coordinate chart admits a canonical normalized section
into the punctured coordinate space. -/
private noncomputable def projectivizationCoordinateSection
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜] [DecidableEq 𝕜]
    [TopologicalSpace 𝕜] [T1Space 𝕜] [ContinuousInv 𝕜] [TopologicalSpace (ℕ →₀ 𝕜)]
    [ContinuousSMul 𝕜 (ℕ →₀ 𝕜)] (n : ℕ) :
    C({x : ℙ 𝕜 (ℕ →₀ 𝕜) // x ∈ Problem_9_7_6.projectivizationCoordinateBaseSet 𝕜 n},
      {w : ℕ →₀ 𝕜 // w ≠ 0}) :=
  ⟨fun x ↦ projectivizationCoordinateSectionDesc 𝕜 n x.1,
    (projectivizationCoordinateSectionDesc_continuousOn (𝕜 := 𝕜) n).restrict⟩

/-- Helper for Problem 9.7.6: the canonical chart section is normalized so that its `n`th
coordinate equals `1`. -/
private theorem projectivizationCoordinateSection_apply
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜] [DecidableEq 𝕜]
    [TopologicalSpace 𝕜] [T1Space 𝕜] [ContinuousInv 𝕜] [TopologicalSpace (ℕ →₀ 𝕜)]
    [ContinuousSMul 𝕜 (ℕ →₀ 𝕜)] (n : ℕ)
    (x : {x : ℙ 𝕜 (ℕ →₀ 𝕜) // x ∈ Problem_9_7_6.projectivizationCoordinateBaseSet 𝕜 n}) :
    ((projectivizationCoordinateSection 𝕜 n x : ℕ →₀ 𝕜) n) = 1 := by
  -- TODO: perform quotient induction on `x.1`, reduce to a representative in the chart, and then
  -- evaluate `Problem_9_7_6.projectivizationCoordinateNormalize_apply`.
  sorry

/-- Helper for Problem 9.7.6: applying `Projectivization.mk'` to the canonical chart section
recovers the original chart point. -/
private theorem projectivizationCoordinateSection_mk'
    (𝕜 : Type*) [Field 𝕜] [Nontrivial 𝕜] [DecidableEq 𝕜]
    [TopologicalSpace 𝕜] [T1Space 𝕜] [ContinuousInv 𝕜] [TopologicalSpace (ℕ →₀ 𝕜)]
    [ContinuousSMul 𝕜 (ℕ →₀ 𝕜)] (n : ℕ)
    (x : {x : ℙ 𝕜 (ℕ →₀ 𝕜) // x ∈ Problem_9_7_6.projectivizationCoordinateBaseSet 𝕜 n}) :
    Projectivization.mk' 𝕜 (projectivizationCoordinateSection 𝕜 n x) = x.1 := by
  -- TODO: use the same quotient-induction reduction as
  -- `projectivizationCoordinateSection_apply`, then apply
  -- `Problem_9_7_6.mk_projectivizationCoordinateNormalize_eq`.
  sorry

/-- Helper for Problem 9.7.6: on the real model, the raw projectivization fiber over the
distinguished basepoint is homeomorphic to `ℝˣ`. -/
private noncomputable def realProjectivizationBaseFiberHomeomorphNonzeroScalars :
    {v : {w : ℕ →₀ ℝ // w ≠ 0} //
        Projectivization.mk' ℝ v = projectivizationBasepoint ℝ} ≃ₜ
      {a : ℝ // a ≠ 0} := by
  let e := projectivizationBaseFiberEquivNonzeroScalars ℝ
  refine
    { toEquiv := e
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · -- The forward map just reads the zeroth coordinate of the punctured representative.
    have hfun :
        Continuous fun x : {v : {w : ℕ →₀ ℝ // w ≠ 0} //
            Projectivization.mk' ℝ v = projectivizationBasepoint ℝ} ↦
          ((((x : {w : ℕ →₀ ℝ // w ≠ 0}) : ℕ →₀ ℝ) : ℕ → ℝ)) := by
      exact continuous_induced_dom.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hcoord :
        Continuous fun x : {v : {w : ℕ →₀ ℝ // w ≠ 0} //
            Projectivization.mk' ℝ v = projectivizationBasepoint ℝ} ↦
          (((x : {w : ℕ →₀ ℝ // w ≠ 0}) : ℕ →₀ ℝ) 0) := by
      exact (continuous_apply 0).comp hfun
    exact hcoord.subtype_mk fun x ↦ by
      change x.1.1 0 ≠ 0
      exact (e x).2
  · -- The inverse map is scalar multiplication of the fixed first basis vector.
    have hsmul :
        Continuous fun a : {z : ℝ // z ≠ 0} ↦ a.1 • Finsupp.single 0 (1 : ℝ) := by
      exact continuous_subtype_val.smul continuous_const
    have hpunctured :
        Continuous fun a : {z : ℝ // z ≠ 0} ↦
          (⟨a.1 • Finsupp.single 0 (1 : ℝ),
            projectivizationScaledFirstBasis_nonzero ℝ a⟩ :
            {w : ℕ →₀ ℝ // w ≠ 0}) := by
      exact hsmul.subtype_mk (projectivizationScaledFirstBasis_nonzero ℝ)
    exact hpunctured.subtype_mk fun a ↦ by
      simpa using projectivizationScaledFirstBasis_projectsToBasepoint ℝ a

/-- Helper for Problem 9.7.6: on the complex model, the raw projectivization fiber over the
distinguished basepoint is homeomorphic to `ℂˣ`. -/
private noncomputable def complexProjectivizationBaseFiberHomeomorphNonzeroScalars :
    {v : {w : ℕ →₀ ℂ // w ≠ 0} //
        Projectivization.mk' ℂ v = projectivizationBasepoint ℂ} ≃ₜ
      {a : ℂ // a ≠ 0} := by
  let e := projectivizationBaseFiberEquivNonzeroScalars ℂ
  refine
    { toEquiv := e
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · -- The forward map again reads the zeroth coordinate.
    have hfun :
        Continuous fun x : {v : {w : ℕ →₀ ℂ // w ≠ 0} //
            Projectivization.mk' ℂ v = projectivizationBasepoint ℂ} ↦
          ((((x : {w : ℕ →₀ ℂ // w ≠ 0}) : ℕ →₀ ℂ) : ℕ → ℂ)) := by
      exact continuous_induced_dom.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hcoord :
        Continuous fun x : {v : {w : ℕ →₀ ℂ // w ≠ 0} //
            Projectivization.mk' ℂ v = projectivizationBasepoint ℂ} ↦
          (((x : {w : ℕ →₀ ℂ // w ≠ 0}) : ℕ →₀ ℂ) 0) := by
      exact (continuous_apply 0).comp hfun
    exact hcoord.subtype_mk fun x ↦ by
      change x.1.1 0 ≠ 0
      exact (e x).2
  · -- The inverse map is the same scalar-multiple parametrization on the complex line.
    have hsmul :
        Continuous fun a : {z : ℂ // z ≠ 0} ↦ a.1 • Finsupp.single 0 (1 : ℂ) := by
      exact continuous_subtype_val.smul continuous_const
    have hpunctured :
        Continuous fun a : {z : ℂ // z ≠ 0} ↦
          (⟨a.1 • Finsupp.single 0 (1 : ℂ),
            projectivizationScaledFirstBasis_nonzero ℂ a⟩ :
            {w : ℕ →₀ ℂ // w ≠ 0}) := by
      exact hsmul.subtype_mk (projectivizationScaledFirstBasis_nonzero ℂ)
    exact hpunctured.subtype_mk fun a ↦ by
      simpa using projectivizationScaledFirstBasis_projectsToBasepoint ℂ a

/-- Helper for Problem 9.7.6: the real punctured coordinate space becomes a based space by
choosing the first basis vector. -/
private abbrev realProjectivizationPuncturedBasedSpace : BasedSpace :=
  basedSpaceAtPoint (TopCat.of {w : ℕ →₀ ℝ // w ≠ 0}) (projectivizationPuncturedBasepoint ℝ)

/-- Helper for Problem 9.7.6: the real projectivization target becomes a based space by choosing
the first coordinate line. -/
private abbrev realProjectivizationBasedSpace : BasedSpace :=
  basedSpaceAtPoint (TopCat.of RealProjectiveInfinity) realProjectiveInfinityBasepoint

/-- Helper for Problem 9.7.6: the real quotient map as a bundled continuous map. -/
private def realProjectivizationContinuousMap :
    C({w : ℕ →₀ ℝ // w ≠ 0}, RealProjectiveInfinity) :=
  ⟨Projectivization.mk' ℝ, continuous_quotient_mk'⟩

/-- Helper for Problem 9.7.6: the real quotient map sends the chosen punctured-coordinate
basepoint to the chosen projective basepoint. -/
private theorem realProjectivizationBasedMap_w :
    realProjectivizationPuncturedBasedSpace.hom ≫ TopCat.ofHom realProjectivizationContinuousMap =
      realProjectivizationBasedSpace.hom := by
  -- Both maps out of the terminal object are determined by the chosen basepoint image.
  ext u
  simpa [realProjectiveInfinityBasepoint] using projectivizationMk'_puncturedBasepoint ℝ

/-- Helper for Problem 9.7.6: package the real projectivization quotient as a based map. -/
private def realProjectivizationBasedMap :
    realProjectivizationPuncturedBasedSpace ⟶ realProjectivizationBasedSpace :=
  Under.homMk (TopCat.ofHom realProjectivizationContinuousMap) realProjectivizationBasedMap_w

/-- Helper for Problem 9.7.6: the actual fiber of the real projectivization quotient over the
first coordinate line is the already-normalized scalar fiber. -/
private noncomputable def realProjectivizationActualFiberSetEquivNonzeroScalars :
    actualFiberSet realProjectivizationBasedMap ≃ {a : ℝ // a ≠ 0} := by
  -- Unfold `actualFiberSet` to the raw subtype fiber over the chosen basepoint line.
  simpa [actualFiberSet, fiber, realProjectiveInfinityBasepoint, realProjectivizationContinuousMap]
    using projectivizationFiberEquivNonzeroScalars ℝ

/-- Helper for Problem 9.7.6: the actual fiber of the real quotient map is homeomorphic to the
nonzero real scalars on the distinguished coordinate line. -/
private noncomputable def realProjectivizationActualFiberHomeomorphNonzeroScalars :
    actualFiberSet realProjectivizationBasedMap ≃ₜ {a : ℝ // a ≠ 0} := by
  -- The actual fiber is definitionally the raw scalar-line fiber used above.
  simpa [actualFiberSet, fiber, realProjectiveInfinityBasepoint, realProjectivizationContinuousMap,
    projectivizationBasepoint, projectivizationPuncturedBasepoint] using
    realProjectivizationBaseFiberHomeomorphNonzeroScalars

/-- Helper for Problem 9.7.6: the complex punctured coordinate space becomes a based space by
choosing the first basis vector. -/
private abbrev complexProjectivizationPuncturedBasedSpace : BasedSpace :=
  basedSpaceAtPoint (TopCat.of {w : ℕ →₀ ℂ // w ≠ 0}) (projectivizationPuncturedBasepoint ℂ)

/-- Helper for Problem 9.7.6: the complex projectivization target becomes a based space by
choosing the first coordinate line. -/
private abbrev complexProjectivizationBasedSpace : BasedSpace :=
  basedSpaceAtPoint (TopCat.of ComplexProjectiveInfinity) complexProjectiveInfinityBasepoint

/-- Helper for Problem 9.7.6: the complex quotient map as a bundled continuous map. -/
private def complexProjectivizationContinuousMap :
    C({w : ℕ →₀ ℂ // w ≠ 0}, ComplexProjectiveInfinity) :=
  ⟨Projectivization.mk' ℂ, continuous_quotient_mk'⟩

/-- Helper for Problem 9.7.6: the complex quotient map sends the chosen punctured-coordinate
basepoint to the chosen projective basepoint. -/
private theorem complexProjectivizationBasedMap_w :
    complexProjectivizationPuncturedBasedSpace.hom ≫ TopCat.ofHom complexProjectivizationContinuousMap =
      complexProjectivizationBasedSpace.hom := by
  -- Both maps out of the terminal object are determined by the chosen basepoint image.
  ext u
  simpa [complexProjectiveInfinityBasepoint] using projectivizationMk'_puncturedBasepoint ℂ

/-- Helper for Problem 9.7.6: package the complex projectivization quotient as a based map. -/
private def complexProjectivizationBasedMap :
    complexProjectivizationPuncturedBasedSpace ⟶ complexProjectivizationBasedSpace :=
  Under.homMk (TopCat.ofHom complexProjectivizationContinuousMap) complexProjectivizationBasedMap_w

/-- Helper for Problem 9.7.6: the actual fiber of the complex projectivization quotient over the
first coordinate line is the already-normalized scalar fiber. -/
private noncomputable def complexProjectivizationActualFiberSetEquivNonzeroScalars :
    actualFiberSet complexProjectivizationBasedMap ≃ {a : ℂ // a ≠ 0} := by
  -- Unfold `actualFiberSet` to the raw subtype fiber over the chosen basepoint line.
  simpa [actualFiberSet, fiber, complexProjectiveInfinityBasepoint,
    complexProjectivizationContinuousMap]
    using projectivizationFiberEquivNonzeroScalars ℂ

/-- Helper for Problem 9.7.6: the actual fiber of the complex quotient map is homeomorphic to the
nonzero complex scalars on the distinguished coordinate line. -/
private noncomputable def complexProjectivizationActualFiberHomeomorphNonzeroScalars :
    actualFiberSet complexProjectivizationBasedMap ≃ₜ {a : ℂ // a ≠ 0} := by
  -- The actual fiber is definitionally the raw scalar-line fiber used above.
  simpa [actualFiberSet, fiber, complexProjectiveInfinityBasepoint,
    complexProjectivizationContinuousMap, projectivizationBasepoint,
    projectivizationPuncturedBasepoint] using
    complexProjectivizationBaseFiberHomeomorphNonzeroScalars

/-- Helper for Problem 9.7.6: the punctured complex plane is homeomorphic to the complex units. -/
private noncomputable def complexUnitsHomeomorphNonzeroScalars :
    ℂˣ ≃ₜ {a : ℂ // a ≠ 0} :=
  unitsHomeomorphNeZero

/-- Helper for Problem 9.7.6: normalize a nonzero complex number to the unit circle. -/
private noncomputable def complexNonzeroScalarsNormalize
    (z : {a : ℂ // a ≠ 0}) : ℂ :=
  (z : ℂ) / ‖(z : ℂ)‖

/-- Helper for Problem 9.7.6: the normalization of a nonzero complex number lies on `Circle`. -/
private theorem complexNonzeroScalarsNormalize_mem_circle
    (z : {a : ℂ // a ≠ 0}) :
    complexNonzeroScalarsNormalize z ∈ (Metric.sphere (0 : ℂ) 1) := by
  -- Dividing by the norm rescales `z` to norm `1`.
  rw [mem_sphere_zero_iff_norm]
  have hnorm : ‖(z : ℂ)‖ ≠ 0 := by
    exact norm_ne_zero_iff.mpr z.2
  simp [complexNonzeroScalarsNormalize, Complex.norm_real, hnorm]

/-- Helper for Problem 9.7.6: normalization varies continuously on the punctured complex plane. -/
private theorem complexNonzeroScalarsNormalize_continuous :
    Continuous fun z : {a : ℂ // a ≠ 0} ↦ complexNonzeroScalarsNormalize z := by
  -- The denominator never vanishes on the punctured plane, so ordinary quotient continuity applies.
  change Continuous fun z : {a : ℂ // a ≠ 0} ↦ (z : ℂ) / ‖(z : ℂ)‖
  refine Continuous.div continuous_subtype_val
    (Complex.continuous_ofReal.comp (continuous_norm.comp continuous_subtype_val)) ?_
  intro z
  exact_mod_cast norm_ne_zero_iff.mpr z.2

/-- Helper for Problem 9.7.6: the normalization map `ℂ \ {0} → S¹`. -/
private noncomputable def complexNonzeroScalarsToCircle :
    C({a : ℂ // a ≠ 0}, Circle) :=
  ⟨fun z ↦ ⟨complexNonzeroScalarsNormalize z,
      complexNonzeroScalarsNormalize_mem_circle z⟩,
    Continuous.subtype_mk complexNonzeroScalarsNormalize_continuous
      (fun z ↦ complexNonzeroScalarsNormalize_mem_circle z)⟩

/-- Helper for Problem 9.7.6: the circle includes into the punctured complex plane. -/
private noncomputable def complexNonzeroScalarsFromCircle :
    C(Circle, {a : ℂ // a ≠ 0}) :=
  ⟨fun z ↦ ⟨(z : ℂ), Circle.coe_ne_zero z⟩,
    Continuous.subtype_mk continuous_subtype_val (fun z ↦ Circle.coe_ne_zero z)⟩

/-- Helper for Problem 9.7.6: normalizing a point of `Circle` does nothing. -/
private theorem complexNonzeroScalarsToCircle_comp_fromCircle_eq_id :
    complexNonzeroScalarsToCircle.comp complexNonzeroScalarsFromCircle =
      ContinuousMap.id Circle := by
  -- On `Circle`, every point already has norm `1`, so normalization is the identity.
  ext z
  simp [complexNonzeroScalarsToCircle, complexNonzeroScalarsFromCircle,
    complexNonzeroScalarsNormalize]

/-- Helper for Problem 9.7.6: the punctured complex plane is homeomorphic to
`Circle × Set.Ioi (0 : ℝ)` via polar coordinates. -/
private noncomputable def complexNonzeroScalarsHomeomorphCircleProd :
    {a : ℂ // a ≠ 0} ≃ₜ Circle × Set.Ioi (0 : ℝ) :=
  homeomorphUnitSphereProd ℂ

/-- Helper for Problem 9.7.6: the constant section of the projection
`Circle × Set.Ioi (0 : ℝ) → Circle` picks the radius `1`. -/
private noncomputable def circleProdPositiveRaySection :
    C(Circle, Circle × Set.Ioi (0 : ℝ)) :=
  ⟨fun z ↦ (z, ⟨1, by simp⟩), continuous_id.prodMk continuous_const⟩

/-- Helper for Problem 9.7.6: deforming the positive-ray factor from radius `1` to the actual
radius retracts `Circle × Set.Ioi (0 : ℝ)` onto the circle section. -/
private theorem circleProdPositiveRaySection_comp_proj_homotopic_id :
    (circleProdPositiveRaySection.comp ContinuousMap.fst).Homotopic
      (ContinuousMap.id (Circle × Set.Ioi (0 : ℝ))) := by
  -- Keep the circle coordinate fixed and linearly interpolate the positive radius from `1` to the
  -- target radius.
  have hpos :
      ∀ p : I × (Circle × Set.Ioi (0 : ℝ)),
        0 < 1 - (p.1 : ℝ) + (p.1 : ℝ) * (p.2.2 : ℝ) := by
    intro p
    have ht0 : 0 ≤ (p.1 : ℝ) := p.1.2.1
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    have hr : 0 < (p.2.2 : ℝ) := p.2.2.2
    by_cases ht : (p.1 : ℝ) = 1
    · simpa [ht] using hr
    · have hlt : (p.1 : ℝ) < 1 := lt_of_le_of_ne ht1 ht
      have hhead : 0 < 1 - (p.1 : ℝ) := sub_pos.mpr hlt
      have htail : 0 ≤ (p.1 : ℝ) * (p.2.2 : ℝ) := mul_nonneg ht0 hr.le
      linarith
  refine ⟨{
    toFun := fun p ↦
      (p.2.1, ⟨1 - (p.1 : ℝ) + (p.1 : ℝ) * (p.2.2 : ℝ), hpos p⟩)
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_
  }⟩
  · -- Continuity is coordinatewise: the circle factor is constant along the homotopy, and the
    -- radius factor is an affine function of the time parameter and the original radius.
    have hCircle :
        Continuous fun p : I × (Circle × Set.Ioi (0 : ℝ)) ↦ p.2.1 :=
      (show Continuous fun q : Circle × Set.Ioi (0 : ℝ) ↦ q.1 from continuous_fst).comp
        continuous_snd
    have ht :
        Continuous fun p : I × (Circle × Set.Ioi (0 : ℝ)) ↦ (p.1 : ℝ) :=
      continuous_subtype_val.comp continuous_fst
    have hr :
        Continuous fun p : I × (Circle × Set.Ioi (0 : ℝ)) ↦ (p.2.2 : ℝ) :=
      continuous_subtype_val.comp
        (show Continuous fun p : I × (Circle × Set.Ioi (0 : ℝ)) ↦ p.2.2 from
          continuous_snd.comp continuous_snd)
    have hRadius :
        Continuous fun p : I × (Circle × Set.Ioi (0 : ℝ)) ↦
          1 - (p.1 : ℝ) + (p.1 : ℝ) * (p.2.2 : ℝ) := by
      exact (continuous_const.sub ht).add (ht.mul hr)
    exact hCircle.prodMk (hRadius.subtype_mk hpos)
  · -- At time `0`, the radius is forced to be `1`, so we recover the section of the projection.
    intro z
    ext <;> simp [circleProdPositiveRaySection]
  · -- At time `1`, the interpolated radius is the original radius, so the homotopy reaches the
    -- identity map.
    intro z
    ext <;> simp

/-- Helper for Problem 9.7.6: `Circle × Set.Ioi (0 : ℝ)` is homotopy equivalent to `Circle`. -/
private noncomputable def circleProdPositiveRayHomotopyEquivCircle :
    ContinuousMap.HomotopyEquiv (Circle × Set.Ioi (0 : ℝ)) Circle where
  toFun := ContinuousMap.fst
  invFun := circleProdPositiveRaySection
  left_inv := circleProdPositiveRaySection_comp_proj_homotopic_id
  right_inv := by
    -- Projecting the constant section returns the original circle point strictly.
    simpa [circleProdPositiveRaySection] using
      (ContinuousMap.Homotopic.refl (ContinuousMap.id Circle))

/-- Helper for Problem 9.7.6: the punctured complex plane is homotopy equivalent to `Circle`. -/
private noncomputable def complexNonzeroScalars_homotopyEquivCircle :
    ContinuousMap.HomotopyEquiv {a : ℂ // a ≠ 0} Circle :=
  (complexNonzeroScalarsHomeomorphCircleProd.toHomotopyEquiv).trans
    circleProdPositiveRayHomotopyEquivCircle

/-- Helper for Problem 9.7.6: the actual fiber of the complex projectivization quotient is
homotopy equivalent to `Circle`. -/
private noncomputable def complexProjectivizationActualFiber_homotopyEquivCircle :
    ContinuousMap.HomotopyEquiv (actualFiberSet complexProjectivizationBasedMap) Circle :=
  -- First identify the fiber with `ℂˣ`, then reuse the existing circle normalization equivalence.
  (complexProjectivizationActualFiberHomeomorphNonzeroScalars.toHomotopyEquiv).trans
    complexNonzeroScalars_homotopyEquivCircle

/-
The former raw-to-based path-lift adapter mixed the k-ified Chapter 7 mapping-path topology with
the raw Chapter 8 subtype topology. It was unused (the later occurrence is only a TODO note), so
it is intentionally kept out of the compiled API.

/-- Helper for Problem 9.7.6: a continuous path lift upgrades to a based path lift once it sends
the canonical mapping-path-space basepoint to the constant basepoint path. -/
private theorem basedPathLiftOfContinuousPathLift
    {E B : BasedSpace} (p : E ⟶ B)
    (s : ContinuousPathLiftingFunction p.right.hom)
    (hbase :
      s.toContinuousMap (basedMappingPathSpaceBasepoint p) =
        ContinuousMap.const I (underTopBasepoint E)) :
    Nonempty (BasedPathLiftingFunction p) := by
  -- The based mapping-path space is definitionally the same subtype as the unbased one, so the
  -- same continuous family of lifts satisfies the Chapter 8 axioms once the basepoint value is
  -- fixed explicitly.
  refine ⟨{
    toContinuousMap := s.toContinuousMap
    source_eq := ?_
    proj_comp_eq := ?_
    map_basepoint := hbase
  }⟩
  · intro x
    exact s.source_eq x
  · intro x
    exact s.proj_comp_eq x

/-- Helper for Problem 9.7.6: a surjective map with a continuous path lift satisfying the
canonical basepoint condition is a based fibration. -/
private theorem isBasedFibrationOfContinuousPathLift
    {E B : BasedSpace} (p : E ⟶ B) (hsurj : Function.Surjective p.right.hom)
    (s : ContinuousPathLiftingFunction p.right.hom)
    (hbase :
      s.toContinuousMap (basedMappingPathSpaceBasepoint p) =
        ContinuousMap.const I (underTopBasepoint E)) :
    IsBasedFibration p := by
  -- Convert the unbased path-lifting witness to the Chapter 8 based owner and apply the local
  -- criterion for based fibrations.
  let _ : Nonempty (BasedPathLiftingFunction p) :=
    basedPathLiftOfContinuousPathLift p s hbase
  exact (IsBasedFibration.iff_surjective_and_nonempty_basedPathLiftingFunction p).2
    ⟨hsurj, inferInstance⟩
-/

/-- Helper for Problem 9.7.6: a path-connected space has trivial `π_ 0`. -/
private theorem pi0SubsingletonOfPathConnected (X : Type*) [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) :
    Subsingleton (π_ 0 X x) := by
  -- First collapse the set of path components to a singleton.
  let _ : Subsingleton (ZerothHomotopy X) := by
    refine ⟨fun a b ↦ ?_⟩
    refine Quotient.inductionOn₂ a b ?_
    intro y z
    exact Quotient.sound (PathConnectedSpace.joined y z)
  -- Then pull that fact back along the canonical `π_ 0` equivalence.
  refine ⟨fun a b ↦ ?_⟩
  apply (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X).injective
  exact Subsingleton.elim _ _

/-- Helper for Problem 9.7.6: `π_ q X x` can be read as the path components of the Section 9.5
sphere-evaluation fiber at `x`. -/
private noncomputable def homotopyGroupEquivSphereBasepointFiberZeroth
    {X : Type u} [TopologicalSpace X] (q : ℕ) (x : X) :
    π_ q X x ≃ ZerothHomotopy (sphereBasepointFiber q x) :=
  let e := Classical.choice (sphereBasepointFiber_homeomorphic_iteratedLoopSpace q x)
  -- First rewrite `π_ q` as path components of iterated loops, then transport through the
  -- canonical Section 9.5 sphere-fiber model.
  (homotopyGroupEquivZerothHomotopyGenLoop q x).trans
    (zerothHomotopyEquivOfHomotopyEquiv e.symm.toHomotopyEquiv)

/-- Helper for Problem 9.7.6: a path between basepoints transports the path components of the
Section 9.5 sphere-evaluation fibers. -/
private noncomputable def homotopyGroupFiberZerothEquivOfPath
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (q : ℕ) {x x' : X} (β : Path x x') :
    ZerothHomotopy (sphereBasepointFiber q x) ≃ ZerothHomotopy (sphereBasepointFiber q x') :=
  sphereBasepointFiberZerothEquivOfPathClass q (Path.Homotopic.Quotient.mk β)

/-- Helper for Problem 9.7.6: a path between basepoints induces an equivalence on all homotopy
groups. -/
private noncomputable def homotopyGroupBasepointChangeEquiv
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (q : ℕ) {x x' : X} (β : Path x x') :
    π_ q X x ≃ π_ q X x' :=
  -- Compare both homotopy groups with the common sphere-fiber model and translate along `β`.
  (homotopyGroupEquivSphereBasepointFiberZeroth q x).trans
    ((homotopyGroupFiberZerothEquivOfPath q β).trans
      (homotopyGroupEquivSphereBasepointFiberZeroth q x').symm)

/-- Helper for Problem 9.7.6: subsingleton homotopy groups transport along a path between
basepoints. -/
private theorem homotopyGroupSubsingleton_of_path
    {X : Type u} [TopologicalSpace X] [CompactlyGeneratedWeakHausdorffSpace.{u, u} X]
    (q : ℕ) {x x' : X} (β : Path x x')
    [Subsingleton (π_ q X x)] :
    Subsingleton (π_ q X x') := by
  let e := homotopyGroupBasepointChangeEquiv q β
  -- Pull the subsingleton structure across the basepoint-change equivalence.
  exact Equiv.subsingleton e.symm

/-- Problem 9.7.6 (1): the path-component group `π_ 0 (RP^∞)` is trivial. -/
theorem realProjectiveInfinity_pi0_subsingleton (x : RealProjectiveInfinity) :
    Subsingleton (π_ 0 RealProjectiveInfinity x) := by
  -- The real infinite projective space is path connected, so its component group is trivial.
  let _ : PathConnectedSpace RealProjectiveInfinity := realProjectiveInfinity_pathConnected
  exact pi0SubsingletonOfPathConnected RealProjectiveInfinity x

/-- Problem 9.7.6 (2): the fundamental group of `RP^∞` at
`realProjectiveInfinityBasepoint` is the cyclic group of order two. -/
theorem realProjectiveInfinity_pi1_mulEquiv_zmod_two :
    Nonempty
      (π_ 1 RealProjectiveInfinity realProjectiveInfinityBasepoint ≃*
        Multiplicative (ZMod 2)) := by
  -- Route correction: the support-stage filtration is not stable in this induced-topology model.
  -- The punctured total space is now proved contractible, and the quotient map is surjective; the
  -- scalar-normalization identities for the standard coordinate charts now live in
  -- `Problem_9_7_6.ProjectivizationBundle`; the remaining blocker is to package those chartwise
  -- formulas into a continuous local trivialization / based-fibration bridge and then identify the
  -- resulting fiber with the nonzero real scalars.
  -- TODO: construct a `ContinuousPathLiftingFunction realProjectivizationContinuousMap` whose
  -- value at `basedMappingPathSpaceBasepoint realProjectivizationBasedMap` is the constant path at
  -- `projectivizationPuncturedBasepoint ℝ`, then use `isBasedFibrationOfContinuousPathLift` and
  -- the long exact sequence tail to identify `π_ 1(RP^∞)` with `π_ 0(ℝˣ)`.
  sorry

/-- Problem 9.7.6 (3): every higher homotopy group `π_ n (RP^∞)` with `n > 1` is trivial. -/
theorem realProjectiveInfinity_homotopyGroup_subsingleton {n : ℕ} (hn : 1 < n)
    (x : RealProjectiveInfinity) :
    Subsingleton (π_ n RealProjectiveInfinity x) := by
  sorry
/-
  let _ : PathConnectedSpace RealProjectiveInfinity := realProjectiveInfinity_pathConnected
  rcases PathConnectedSpace.joined realProjectiveInfinityBasepoint x with ⟨β⟩
  -- Route correction: the arbitrary-basepoint statement is now isolated from the LES blocker.
  -- Once the basepoint computation is closed, transport finishes this theorem immediately.
  let _ : Subsingleton (π_ n RealProjectiveInfinity realProjectiveInfinityBasepoint) := by
    -- TODO: after the real projectivization quotient is packaged as a based fibration, collapse
    -- the total-space terms by
    -- `realProjectiveInfinityPuncturedCoordinates_homotopyGroup_subsingleton`, identify the fiber
    -- with `ℝˣ`, and use `hn` to show the fiber contribution vanishes at the basepoint.
    sorry
  -- Transport the basepoint computation along a chosen path to `x`.
  exact homotopyGroupSubsingleton_of_path n β
-/

/-- Problem 9.7.6 (4): the path-component group `π_ 0 (CP^∞)` is trivial. -/
theorem complexProjectiveInfinity_pi0_subsingleton (x : ComplexProjectiveInfinity) :
    Subsingleton (π_ 0 ComplexProjectiveInfinity x) := by
  -- The complex infinite projective space is path connected, so its component group is trivial.
  let _ : PathConnectedSpace ComplexProjectiveInfinity := complexProjectiveInfinity_pathConnected
  exact pi0SubsingletonOfPathConnected ComplexProjectiveInfinity x

/-- Problem 9.7.6 (5): the fundamental group of `CP^∞` is trivial. -/
theorem complexProjectiveInfinity_pi1_subsingleton (x : ComplexProjectiveInfinity) :
    Subsingleton (π_ 1 ComplexProjectiveInfinity x) := by
  sorry
/-
  let _ : PathConnectedSpace ComplexProjectiveInfinity := complexProjectiveInfinity_pathConnected
  rcases PathConnectedSpace.joined complexProjectiveInfinityBasepoint x with ⟨β⟩
  -- Route correction: basepoint transport is no longer mixed into the fiber-sequence blocker.
  let _ : Subsingleton (π_ 1 ComplexProjectiveInfinity complexProjectiveInfinityBasepoint) := by
    -- TODO: construct the based-fibration package for `complexProjectivizationBasedMap`, identify
    -- its fiber with `ℂˣ`, and use the LES tail together with path connectedness of `ℂˣ` to force
    -- `π_ 1(CP^∞)` to be trivial at the chosen basepoint.
    sorry
  -- Transport the basepoint vanishing to the requested point `x`.
  exact homotopyGroupSubsingleton_of_path 1 β
-/

/-- Problem 9.7.6 (6): the second homotopy group of `CP^∞` at
`complexProjectiveInfinityBasepoint` is infinite cyclic. -/
theorem complexProjectiveInfinity_pi2_mulEquiv_int :
    Nonempty
      (π_ 2 ComplexProjectiveInfinity complexProjectiveInfinityBasepoint ≃*
        Multiplicative ℤ) := by
  -- Route correction: the contractible total space for the quotient model is now available. The
  -- remaining blocker is identifying the quotient fiber with `ℂˣ` and then with `Circle` in the
  -- long exact sequence.
  -- TODO: once `complexProjectivizationBasedMap` is a based fibration, identify
  -- `actualFiberSet complexProjectivizationBasedMap` with `ℂˣ`, transport `π_ 1(ℂˣ)` to `π_ 1(S¹)`
  -- through the normalization homotopy equivalence, and read off `π_ 2(CP^∞)` from exactness at
  -- the boundary map.
  sorry

/-- Problem 9.7.6 (7): every higher homotopy group `π_ n (CP^∞)` with `n > 2` is trivial. -/
theorem complexProjectiveInfinity_homotopyGroup_subsingleton {n : ℕ} (hn : 2 < n)
    (x : ComplexProjectiveInfinity) :
    Subsingleton (π_ n ComplexProjectiveInfinity x) := by
  sorry
/-
  let _ : PathConnectedSpace ComplexProjectiveInfinity := complexProjectiveInfinity_pathConnected
  rcases PathConnectedSpace.joined complexProjectiveInfinityBasepoint x with ⟨β⟩
  -- Route correction: the higher arbitrary-basepoint statement now only waits on the basepoint
  -- LES computation.
  let _ : Subsingleton (π_ n ComplexProjectiveInfinity complexProjectiveInfinityBasepoint) := by
    -- TODO: after the complex quotient is a based fibration, collapse the total-space terms,
    -- replace the fiber by `ℂˣ`, transport its higher homotopy groups to the circle through
    -- `complexNonzeroScalars_homotopyEquivCircle`, and conclude the basepoint computation by
    -- exactness.
    sorry
  -- Transport the basepoint computation along the chosen path to `x`.
  exact homotopyGroupSubsingleton_of_path n β
-/
