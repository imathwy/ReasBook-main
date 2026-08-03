import BauschkeLean.Chap03.Corollary_3_22
import BauschkeLean.Chap05.Corollary_5_17
import BauschkeLean.Chap06.Definition_6_38
import BauschkeLean.Chap20.Example_20_26
import BauschkeLean.Chap26.Proposition_26_1
import BauschkeLean.Chap26.Proposition_26_4

open EuclideanGeometry
open Filter
open Function
open ERealFunction
open scoped BigOperators InnerProductSpace Pointwise Set SetValuedOperator Topology

universe u

namespace SetValuedOperator

noncomputable section

-- Source/core/bridge triage:
-- - `source-facing`: the parallel splitting recursion `(26.45)` and Proposition 26.12.
-- - `core/canonical`: the Chapter 26 relaxed Douglas--Rachford owners on the product space with
--   the diagonal normal cone and the family operator.
-- - `bridge/view`: the orbit predicate below keeps the source recursion explicit while the proof of
--   Proposition 26.12 is expected to pass through the product-space Douglas--Rachford API.

variable {m : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "ProductSpace" => lp (fun _ : Fin m ↦ H) 2
local notation "DiagonalSet" =>
  (((diagonalSubmodule : Submodule ℝ ProductSpace) : Set ProductSpace))
abbrev diagonalAffineSubspace : AffineSubspace ℝ ProductSpace :=
  ((diagonalSubmodule : Submodule ℝ ProductSpace).toAffineSubspace)

/-- Helper for Proposition 26.12: the Douglas--Rachford orbit attached to `A`, `B`, `γ`, `lam`,
and `y0`. -/
def douglasRachfordIteration
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  relaxedOperatorIteration
    (fun _ ↦ douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ))
    lam
    y0

/-- Helper for Proposition 26.12: the primal Douglas--Rachford sequence `xₙ = J_{γB} yₙ`. -/
def douglasRachfordPrimalSequence
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (γ : PosReal) (lam : ℕ → ℝ) (y0 : H) : ℕ → H :=
  fun n ↦ resolventMap B hB γ (douglasRachfordIteration A B hA hB γ lam y0 n)

/-- Helper for Proposition 26.12: the Douglas--Rachford orbit converges weakly to a fixed point
whenever the primal inclusion solution set is nonempty. -/
theorem douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
    (A B : SetValuedOperator H H) (hA : Maximal IsMonotone A) (hB : Maximal IsMonotone B)
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : H)
    (hzero : (primal_inclusion_solution_set A B).Nonempty)
    (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop) :
    ∃ y ∈ fixedPoints (reflectedResolventComposition A B hA hB γ),
      Tendsto
        (fun n ↦ toWeakSpace ℝ H (douglasRachfordIteration A B hA hB γ lam y0 n))
        atTop (𝓝 (toWeakSpace ℝ H y)) := by
  let T := douglasRachfordOperator (resolventMap A hA γ) (resolventMap B hB γ)
  have hT : FirmlyNonexpansive T := by
    -- Proposition 26.1 records firm nonexpansiveness of the Douglas--Rachford splitting map.
    simpa [T] using douglasRachfordSplittingOperator_firmlyNonexpansive A B hA hB γ
  have hfix : (fixedPoints T).Nonempty := by
    -- Repackage a primal solution as a fixed point through Proposition 26.1(6).
    rcases hzero with ⟨x, hx⟩
    rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      A B hA hB γ] at hx
    rcases hx with ⟨y, hyfix, _⟩
    rw [fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      A B hA hB γ]
    exact ⟨y, hyfix⟩
  obtain ⟨y, hyfix, hy_tendsto⟩ :=
    exists_tendsto_weakly_to_fixedPoint_of_relaxedOperatorIteration_of_firmlyNonexpansive
      hT hfix lam hlam hdiv y0
  refine ⟨y, ?_, ?_⟩
  · -- Transport the fixed point back to the reflected-resolvent presentation.
    rw [← fixedPoints_douglasRachfordOperator_resolvent_eq_fixedPoints_reflectedResolventComposition
      A B hA hB γ]
    exact hyfix
  · -- The local Douglas--Rachford orbit is exactly the Chapter 5 relaxed iteration of `T`.
    simpa [douglasRachfordIteration, T] using hy_tendsto

/-- Helper for Proposition 26.12: for a nonempty closed affine subspace `C`, the normal-cone
resolvent agrees with the metric projector onto `C`. -/
theorem resolventMap_normalConeAffine_eq_projectionPoint
    {C : AffineSubspace ℝ H} (hC_nonempty : (C : Set H).Nonempty)
    (hC_closed : IsClosed (C : Set H))
    (hNC : Maximal IsMonotone N[(C : Set H)]) (γ : PosReal) (x : H) :
    let hC_cheb : IsChebyshev (C : Set H) :=
      isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
    resolventMap N[(C : Set H)] hNC γ x = P[(C : Set H), hC_cheb] x := by
  let hC_cheb : IsChebyshev (C : Set H) :=
    isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed C.convex
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  have hdir_closed : IsClosed (C.direction : Set H) :=
    (AffineSubspace.isClosed_direction_iff C).mpr hC_closed
  letI : IsClosed (C.direction : Set H) := hdir_closed
  letI : CompleteSpace C.direction := IsClosed.completeSpace_coe
  letI : C.direction.HasOrthogonalProjection := by
    infer_instance
  have hpC : P[(C : Set H), hC_cheb] x ∈ (C : Set H) := by
    -- The metric projector always lands back in the affine subspace.
    exact projectionPoint_mem (C : Set H) hC_cheb x
  have horth : x - P[(C : Set H), hC_cheb] x ∈ C.directionᗮ := by
    -- Replace the metric projector with the affine orthogonal projection and read off the
    -- orthogonality of the residual.
    have hEq : x - P[(C : Set H), hC_cheb] x = x -ᵥ (orthogonalProjection C x : C) := by
      simpa [hC_cheb, vsub_eq_sub] using congrArg (fun z : H ↦ x - z)
        (projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
          hC_nonempty hC_closed x)
    rw [hEq]
    exact vsub_orthogonalProjection_mem_direction_orthogonal C x
  have hscaled :
      (γ : ℝ)⁻¹ • (x - P[(C : Set H), hC_cheb] x) ∈ (C.directionᗮ : Set H) := by
    -- The normal cone of an affine subspace is the orthogonal complement of its direction.
    exact Submodule.smul_mem (C.directionᗮ) _ horth
  have hp_mem :
      P[(C : Set H), hC_cheb] x ∈ J[((γ : ℝ) • N[(C : Set H)])] x := by
    -- The projector point satisfies the resolvent graph criterion for the normal cone.
    refine (mem_resolvent_smul_iff_mem_graph N[(C : Set H)] γ x _).2 ?_
    simpa [mem_graph, normalCone_affineSubspace_eq_direction_orthogonal_of_mem C hpC] using
      hscaled
  -- Singleton-valuedness of the maximal-monotone resolvent identifies the chosen realizer.
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal N[(C : Set H)] hNC γ x] at hp_mem
  simpa using hp_mem.symm

/-- Helper for Proposition 26.12: evaluating a diagonal point at any coordinate recovers the
underlying vector. -/
@[simp] theorem coordinateCLM_diagonalPoint (i : Fin m) (z : H) :
    coordinateCLM i (diagonalPoint z) = z := by
  -- The coordinate map reads one entry of the constant diagonal family.
  simp [coordinateCLM_apply, diagonalPoint_apply]

/-- Helper for Proposition 26.12: the diagonal affine subspace is nonempty. -/
theorem diagonalAffineSubspace_nonempty :
    (((diagonalAffineSubspace : AffineSubspace ℝ ProductSpace) : Set ProductSpace)).Nonempty := by
  refine ⟨0, ?_⟩
  exact (Submodule.mem_toAffineSubspace).2 (by simp)

/-- The sequences `p`, `x`, `q`, and `y` satisfy the parallel splitting recursion `(26.45)` for
the finite family `A`, relaxation parameters `lam`, step size `γ`, and initial family `y0`. -/
structure IsParallelSplittingOrbit
    (A : Fin m → SetValuedOperator H H) (hA : ∀ i, Maximal IsMonotone (A i))
    (lam : ℕ → ℝ) (γ : PosReal) (y0 : ProductSpace)
    (p q : ℕ → H) (x y : ℕ → ProductSpace) : Prop where
  /-- The orbit starts from the prescribed family `y0`. -/
  y_zero : y 0 = y0
  /-- The averaged family is `pₙ = m⁻¹ • ∑ i, yₙᵢ`. -/
  p_eq (n : ℕ) : p n = (m : ℝ)⁻¹ • ∑ i, y n i
  /-- The componentwise backward step is `xₙᵢ = J_{γ Aᵢ}(yₙᵢ)`. -/
  x_eq (n : ℕ) (i : Fin m) : x n i = resolventMap (A i) (hA i) γ (y n i)
  /-- The averaged backward step is `qₙ = m⁻¹ • ∑ i, xₙᵢ`. -/
  q_eq (n : ℕ) : q n = (m : ℝ)⁻¹ • ∑ i, x n i
  /-- The relaxed update is `yₙ₊₁,ᵢ = yₙᵢ + λₙ (2 qₙ - pₙ - xₙᵢ)`. -/
  y_succ_eq (n : ℕ) (i : Fin m) :
    y (n + 1) i = y n i + lam n • ((2 : ℝ) • q n - p n - x n i)

/-- The diagonal normal cone is maximally monotone in the product Hilbert space. -/
theorem diagonalNormalCone_maximal :
    Maximal IsMonotone
      (Set.normalCone DiagonalSet
        : SetValuedOperator ProductSpace ProductSpace) := by
  exact Set.normalCone_isMaximallyMonotone
    ⟨0, by simp⟩
    isClosed_diagonalSubmodule
    (by
      simpa [Submodule.mem_toAffineSubspace] using
        ((
          (diagonalSubmodule : Submodule ℝ ProductSpace).toAffineSubspace :
            AffineSubspace ℝ ProductSpace
        ).convex))

namespace IsParallelSplittingOrbit

/-- The diagonal projection of the product-space orbit is the constant family with value `p n`. -/
theorem diagonal_starProjection_eq
    {A : Fin m → SetValuedOperator H H} {hA : ∀ i, Maximal IsMonotone (A i)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : IsParallelSplittingOrbit A hA lam γ y0 p q x y) (n : ℕ) :
    diagonalSubmodule.starProjection (y n) = diagonalPoint (p n) := by
  simpa [hOrbit.p_eq n] using
    starProjection_diagonalSubmodule_eq_diagonalPoint_average (y n)

/-- Helper for Proposition 26.12: the product-space resolvent of `familyOperator A` along the
parallel splitting orbit is exactly the backward step `x n`. -/
theorem familyOperator_resolvent_eq_backwardStep
    {A : Fin m → SetValuedOperator H H} {hA : ∀ i, Maximal IsMonotone (A i)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : IsParallelSplittingOrbit A hA lam γ y0 p q x y) (n : ℕ) :
    resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ (y n) = x n := by
  have hscaled :
      ((γ : ℝ) • familyOperator A : SetValuedOperator ProductSpace ProductSpace) =
        familyOperator (fun i ↦ ((γ : ℝ) • A i)) := by
    ext z u
    constructor
    · intro hu
      rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne', mem_familyOperator_iff] at hu
      rw [mem_familyOperator_iff]
      intro i
      have hui := hu i
      rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne']
      exact hui
    · intro hu
      rw [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne', mem_familyOperator_iff]
      intro i
      simpa [Pi.smul_apply, Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] using hu i
  have hmem :
      resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ (y n) ∈
        J[((γ : ℝ) • familyOperator A)] (y n) := by
    -- The maximal-monotone realizer is the unique point of the scaled resolvent singleton.
    rw [resolvent_smul_eq_singleton_resolventMap_of_maximal
      (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ (y n)]
    simp
  rw [hscaled, resolvent_familyOperator_eq_familyOperator_resolvent, mem_familyOperator_iff] at hmem
  ext i
  have hi := hmem i
  rw [resolvent_smul_eq_singleton_resolventMap_of_maximal (A i) (hA i) γ (y n i)] at hi
  simpa [hOrbit.x_eq n i] using hi

/-- Helper for Proposition 26.12: projecting `2 • x n - y n` onto the diagonal submodule yields
the constant family with value `2 • q n - p n`. -/
theorem diagonalStarProjection_twoPrimalSub_eq
    {A : Fin m → SetValuedOperator H H} {hA : ∀ i, Maximal IsMonotone (A i)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : IsParallelSplittingOrbit A hA lam γ y0 p q x y) (n : ℕ) :
    diagonalSubmodule.starProjection ((2 : ℝ) • x n - y n) =
      diagonalPoint ((2 : ℝ) • q n - p n) := by
  -- Normalize the diagonal average of `2 • x n - y n` into the source averages `q n` and `p n`.
  rw [starProjection_diagonalSubmodule_eq_diagonalPoint_average]
  ext i
  simp [diagonalPoint_apply, hOrbit.q_eq n, hOrbit.p_eq n]
  change
    (m : ℝ)⁻¹ • ∑ j, ((2 : ℝ) • x n j - y n j) =
      (2 : ℝ) • ((m : ℝ)⁻¹ • ∑ j, x n j) - (m : ℝ)⁻¹ • ∑ j, y n j
  calc
    (m : ℝ)⁻¹ • ∑ j, ((2 : ℝ) • x n j - y n j)
        = (m : ℝ)⁻¹ • ((2 : ℝ) • ∑ j, x n j - ∑ j, y n j) := by
            rw [Finset.sum_sub_distrib, Finset.smul_sum]
    _ = (2 : ℝ) • ((m : ℝ)⁻¹ • ∑ j, x n j) - (m : ℝ)⁻¹ • ∑ j, y n j := by
          rw [smul_sub, smul_smul, smul_smul]
          have hcomm : (m : ℝ)⁻¹ * 2 = 2 * (m : ℝ)⁻¹ := by ring
          rw [hcomm]

/-- Helper for Proposition 26.12: the affine projector onto the diagonal affine subspace agrees
with the diagonal star projection. -/
theorem diagonalAffineProjector_eq_starProjection
    (hC_closed :
      IsClosed
        ((((diagonalSubmodule : Submodule ℝ ProductSpace).toAffineSubspace :
            AffineSubspace ℝ ProductSpace) : Set ProductSpace)))
    (z : ProductSpace) :
    P[((diagonalAffineSubspace : AffineSubspace ℝ ProductSpace) : Set ProductSpace),
      isChebyshev_of_nonempty_isClosed_convex
        (diagonalAffineSubspace_nonempty (m := m) (H := H))
        hC_closed diagonalAffineSubspace.convex] z =
      diagonalSubmodule.starProjection z := by
  let C : AffineSubspace ℝ ProductSpace := diagonalAffineSubspace
  have hC_nonempty : (C : Set ProductSpace).Nonempty := by
    simpa [C] using (diagonalAffineSubspace_nonempty (m := m) (H := H))
  let hC_cheb : IsChebyshev (C : Set ProductSpace) :=
    isChebyshev_of_nonempty_isClosed_convex
      hC_nonempty
      hC_closed C.convex
  letI : Nonempty C := nonempty_subtype.mpr hC_nonempty
  letI : C.direction.HasOrthogonalProjection := by
    simpa [C, diagonalAffineSubspace, Submodule.toAffineSubspace_direction] using
      (inferInstance : (diagonalSubmodule : Submodule ℝ ProductSpace).HasOrthogonalProjection)
  have horth :
      (orthogonalProjection C z : ProductSpace) = diagonalSubmodule.starProjection z := by
    -- Route correction: compare the diagonal affine orthogonal projection directly with the
    -- diagonal star projection instead of introducing an existential Chebyshev witness.
    refine (coe_orthogonalProjection_eq_iff_mem).2 ?_
    constructor
    · exact (Submodule.mem_toAffineSubspace).2 (diagonalSubmodule.starProjection_apply_mem z)
    · simpa [C, diagonalAffineSubspace, Submodule.toAffineSubspace_direction] using
        (diagonalSubmodule.sub_starProjection_mem_orthogonal z)
  -- Replace the metric projector by the affine orthogonal projection and then by `starProjection`.
  rw [projectionPoint_eq_orthogonalProjection_of_nonempty_isClosed_affineSubspace
    hC_nonempty
    hC_closed z]
  simpa [C] using horth

/-- Helper for Proposition 26.12: the diagonal normal-cone resolvent is the diagonal
orthogonal projection, hence the diagonal star projection. -/
theorem diagonalAffineSubspace_closed :
    IsClosed
      ((((diagonalAffineSubspace : AffineSubspace ℝ ProductSpace) : Set ProductSpace))) := by
  simpa [diagonalAffineSubspace, Submodule.mem_toAffineSubspace] using
    (isClosed_diagonalSubmodule :
      IsClosed ((diagonalSubmodule : Submodule ℝ ProductSpace) : Set ProductSpace))

/-- Helper for Proposition 26.12: the diagonal affine normal cone is maximally monotone. -/
theorem diagonalAffineNormalCone_maximal :
    Maximal IsMonotone
      N[(((diagonalAffineSubspace : AffineSubspace ℝ ProductSpace) : Set ProductSpace))] := by
  simpa [diagonalAffineSubspace, Submodule.mem_toAffineSubspace] using
    (diagonalNormalCone_maximal (m := m) (H := H))

/-- Helper for Proposition 26.12: the diagonal normal-cone resolvent is the metric projector onto
the diagonal affine subspace. -/
theorem diagonalNormalCone_resolvent_eq_projectionPoint
    (γ : PosReal) (z : ProductSpace) :
    resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ z =
      P[((diagonalAffineSubspace : AffineSubspace ℝ ProductSpace) : Set ProductSpace),
        isChebyshev_of_nonempty_isClosed_convex
          (diagonalAffineSubspace_nonempty (m := m) (H := H))
          (diagonalAffineSubspace_closed (m := m) (H := H))
          diagonalAffineSubspace.convex] z := by
  simpa [diagonalAffineSubspace, Submodule.mem_toAffineSubspace] using
    (resolventMap_normalConeAffine_eq_projectionPoint
      (C := diagonalAffineSubspace)
      (hC_nonempty := diagonalAffineSubspace_nonempty (m := m) (H := H))
      (hC_closed := diagonalAffineSubspace_closed (m := m) (H := H))
      (hNC := diagonalAffineNormalCone_maximal (m := m) (H := H))
      (γ := γ) z)

/-- Helper for Proposition 26.12: the diagonal normal-cone resolvent is the diagonal
orthogonal projection, hence the diagonal star projection. -/
theorem diagonalNormalCone_resolvent_eq_starProjection
    (γ : PosReal) (z : ProductSpace) :
    resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ z =
      diagonalSubmodule.starProjection z := by
  rw [diagonalNormalCone_resolvent_eq_projectionPoint (m := m) (H := H) (γ := γ)]
  exact diagonalAffineProjector_eq_starProjection
    (hC_closed := diagonalAffineSubspace_closed (m := m) (H := H)) z

/-- The `y`-sequence of `(26.45)` is the Chapter 26 Douglas--Rachford orbit on the product space
for the diagonal normal cone and the family operator. -/
theorem y_eq_douglasRachfordIteration
    {A : Fin m → SetValuedOperator H H} {hA : ∀ i, Maximal IsMonotone (A i)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : IsParallelSplittingOrbit A hA lam γ y0 p q x y) :
    y =
      douglasRachfordIteration
        (Set.normalCone DiagonalSet)
        (familyOperator A)
        diagonalNormalCone_maximal
        (familyOperator_maximal_of_maximal A hA) γ lam y0 := by
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
                (resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ)
                (resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ))
            lam y0 n =
            y n := by
        simpa [douglasRachfordIteration] using ih.symm
      have hdiag_step :
          resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ
            ((2 : ℝ) •
                resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ
                  (y n) -
              y n) =
            diagonalPoint ((2 : ℝ) • q n - p n) := by
        rw [diagonalNormalCone_resolvent_eq_starProjection (m := m) (H := H) (γ := γ)]
        rw [hOrbit.familyOperator_resolvent_eq_backwardStep n,
          hOrbit.diagonalStarProjection_twoPrimalSub_eq n]
      have hdiag_step' :
          resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ
            ((2 : ℝ) • x n - y n) =
            diagonalPoint ((2 : ℝ) • q n - p n) := by
        simpa [hOrbit.familyOperator_resolvent_eq_backwardStep n] using hdiag_step
      ext i
      -- Rewrite both successor formulas to the same coordinatewise relaxed update.
      rw [hOrbit.y_succ_eq n, douglasRachfordIteration, relaxedOperatorIteration_succ, ih']
      change
        y n i + lam n • ((2 : ℝ) • q n - p n - x n i) =
          (y n + lam n •
            (douglasRachfordOperator
                (resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ)
                (resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ)
                (y n) -
              y n)) i
      rw [douglasRachfordOperator_apply, hOrbit.familyOperator_resolvent_eq_backwardStep n]
      have hcoord :
          (resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ
            ((2 : ℝ) • x n - y n)) i =
            (2 : ℝ) • q n - p n := by
        simpa [diagonalPoint_apply] using
          congrArg (fun z : ProductSpace ↦ z i) hdiag_step'
      simp [Pi.add_apply, Pi.sub_apply]
      change
        y n i + lam n • ((2 : ℝ) • q n - p n - x n i) =
          y n i +
            lam n •
              (((resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ
                    ((2 : ℝ) • x n - y n)) i) +
                y n i - x n i - y n i)
      rw [hcoord]
      abel_nf

/-- The `x`-sequence of `(26.45)` is the Chapter 26 Douglas--Rachford primal sequence on the
product space for the diagonal normal cone and the family operator. -/
theorem x_eq_douglasRachfordPrimalSequence
    {A : Fin m → SetValuedOperator H H} {hA : ∀ i, Maximal IsMonotone (A i)}
    {lam : ℕ → ℝ} {γ : PosReal} {y0 : ProductSpace}
    {p q : ℕ → H} {x y : ℕ → ProductSpace}
    (hOrbit : IsParallelSplittingOrbit A hA lam γ y0 p q x y) :
    x =
      douglasRachfordPrimalSequence
        (Set.normalCone DiagonalSet)
        (familyOperator A)
        diagonalNormalCone_maximal
        (familyOperator_maximal_of_maximal A hA) γ lam y0 := by
  -- Rewrite the canonical primal sequence through the already identified Douglas--Rachford orbit.
  funext n
  calc
    x n = resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ (y n) := by
      symm
      exact hOrbit.familyOperator_resolvent_eq_backwardStep n
    _ =
        resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ
          (douglasRachfordIteration
            (Set.normalCone DiagonalSet)
            (familyOperator A)
            diagonalNormalCone_maximal
            (familyOperator_maximal_of_maximal A hA) γ lam y0 n) := by
              rw [hOrbit.y_eq_douglasRachfordIteration]
    _ =
        douglasRachfordPrimalSequence
          (Set.normalCone DiagonalSet)
          (familyOperator A)
          diagonalNormalCone_maximal
          (familyOperator_maximal_of_maximal A hA) γ lam y0 n := by
            rfl

end IsParallelSplittingOrbit

/-- Helper for Proposition 26.12: a fixed point of the product-space reflected-resolvent
composition has the same diagonal projection as its `familyOperator` resolvent shadow. -/
theorem diagonalStarProjection_eq_resolventLimit_of_fixedPoint
    (A : Fin m → SetValuedOperator H H) (hA : ∀ i, Maximal IsMonotone (A i))
    (γ : PosReal) {yFix : ProductSpace}
    (hyFix :
      yFix ∈ fixedPoints
        (reflectedResolventComposition
          (Set.normalCone DiagonalSet)
          (familyOperator A)
          diagonalNormalCone_maximal
          (familyOperator_maximal_of_maximal A hA) γ)) :
    diagonalSubmodule.starProjection yFix =
      resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ yFix := by
  let x : ProductSpace :=
    resolventMap (familyOperator A) (familyOperator_maximal_of_maximal A hA) γ yFix
  have hproj :
      diagonalSubmodule.starProjection ((2 : ℝ) • x - yFix) = x := by
    have hfix_eq :
        resolventMap (Set.normalCone DiagonalSet) diagonalNormalCone_maximal γ
          ((2 : ℝ) • x - yFix) = x := by
      -- Rewrite the fixed-point equation into the canonical resolvent equality.
      have hyFix' :=
        (mem_fixedPoints_reflectedResolventComposition_iff_resolventMap_eq
          (Set.normalCone DiagonalSet) (familyOperator A) diagonalNormalCone_maximal
          (familyOperator_maximal_of_maximal A hA) γ yFix).1 hyFix
      simpa [x] using hyFix'
    rw [IsParallelSplittingOrbit.diagonalNormalCone_resolvent_eq_starProjection
      (m := m) (H := H) (γ := γ)] at hfix_eq
    exact hfix_eq
  have hx_mem : x ∈ (diagonalSubmodule : Submodule ℝ ProductSpace) := by
    -- The diagonal projection always lands in the diagonal submodule.
    rw [← hproj]
    exact diagonalSubmodule.starProjection_apply_mem ((2 : ℝ) • x - yFix)
  have hx_proj : diagonalSubmodule.starProjection x = x := by
    simpa using
      ((Submodule.starProjection_eq_self_iff).2 hx_mem :
        diagonalSubmodule.starProjection x = x)
  have hcore : (2 : ℝ) • x - diagonalSubmodule.starProjection yFix = x := by
    -- Apply linearity of `starProjection` to the already identified diagonal point.
    calc
      (2 : ℝ) • x - diagonalSubmodule.starProjection yFix
          = (2 : ℝ) • diagonalSubmodule.starProjection x -
              diagonalSubmodule.starProjection yFix := by rw [hx_proj]
      _ = diagonalSubmodule.starProjection ((2 : ℝ) • x - yFix) := by simp
      _ = x := hproj
  have hsum : x + x = x + diagonalSubmodule.starProjection yFix := by
    have hcore' : (2 : ℝ) • x = x + diagonalSubmodule.starProjection yFix :=
      sub_eq_iff_eq_add.mp hcore
    simpa [two_smul, add_assoc, add_left_comm, add_comm] using hcore'
  exact (add_left_cancel hsum).symm

/-- Proposition 26.12: let `m ≥ 2`, let `A : Fin m → SetValuedOperator H H` be maximally
monotone with `zer (∑ i, A i) ≠ ∅`, formalized as `((∑ i, A i).zeros).Nonempty`, let
`lam` take values in `[0, 2]` with `∑ lam n * (2 - lam n) = +∞`, let `γ ∈ ℝ_{++}`, and let
`p`, `x`, `q`, and `y` satisfy the parallel splitting recursion `(26.45)` from the initial family
`y0`, formalized by `IsParallelSplittingOrbit A hA lam γ y0 p q x y`. Then `(p n)` converges
weakly to a point of `zer (∑ i, A i)`, formalized as `(∑ i, A i).zeros`. The refined Lean
statement keeps the weaker positivity hypothesis `0 < m`, which is the only size condition used by
the product-space argument. -/
theorem parallelSplittingAlgorithm_average_tendsto_weakly_to_zeroSet
    (A : Fin m → SetValuedOperator H H) (hm : 0 < m)
    (hA : ∀ i, Maximal IsMonotone (A i))
    (hzero : ((∑ i, A i).zeros).Nonempty)
    (lam : ℕ → ℝ) (hlam : ∀ n, lam n ∈ Set.Icc (0 : ℝ) 2)
    (hdiv :
      Tendsto
        (fun N ↦
          Finset.sum (Finset.range N)
            (fun n ↦ lam n * (2 - lam n)))
        atTop atTop)
    (γ : PosReal) (y0 : ProductSpace)
    (p q : ℕ → H) (x y : ℕ → ProductSpace)
    (hOrbit : IsParallelSplittingOrbit A hA lam γ y0 p q x y) :
    ∃ xLim ∈ (∑ i, A i).zeros,
      Tendsto (fun n ↦ toWeakSpace ℝ H (p n)) atTop (𝓝 (toWeakSpace ℝ H xLim)) := by
  have hfamilyA : Maximal IsMonotone (familyOperator A) :=
    familyOperator_maximal_of_maximal A hA
  have hzeroDiag :
      ((N[DiagonalSet] + familyOperator A).zeros).Nonempty := by
    -- Transport a zero of `∑ i, A i` to the diagonal zero set of the product-space operator.
    rw [← diagonalPoint_image_zeros_sum_eq_zeros_normalCone_add_familyOperator A]
    rcases hzero with ⟨x0, hx0⟩
    exact ⟨diagonalPoint x0, ⟨x0, hx0, rfl⟩⟩
  have hzeroProd :
      (primal_inclusion_solution_set (Set.normalCone DiagonalSet) (familyOperator A)).Nonempty := by
    simpa [primal_inclusion_solution_set] using hzeroDiag
  obtain ⟨yFix, hyFix, hy_tendsto⟩ :=
    douglasRachfordAlgorithm_exists_fixedPoint_tendsto_weakly
      (A := Set.normalCone DiagonalSet) (B := familyOperator A)
      diagonalNormalCone_maximal hfamilyA lam γ y0 hzeroProd hlam hdiv
  have hy_tendsto' :
      Tendsto
        (fun n ↦ toWeakSpace ℝ ProductSpace (y n))
        atTop
        (𝓝 (toWeakSpace ℝ ProductSpace yFix)) := by
    -- Replace the canonical Chapter 26 orbit with the source recursion `(26.45)`.
    simpa [hOrbit.y_eq_douglasRachfordIteration] using hy_tendsto
  let proj : ProductSpace →L[ℝ] ProductSpace := diagonalSubmodule.starProjection
  have hproj_tendsto :
      Tendsto
        (fun n ↦ toWeakSpace ℝ ProductSpace (diagonalSubmodule.starProjection (y n)))
        atTop
        (𝓝 (toWeakSpace ℝ ProductSpace (diagonalSubmodule.starProjection yFix))) := by
    have hmap :
        Tendsto
          (fun n ↦ WeakSpace.map proj (toWeakSpace ℝ ProductSpace (y n)))
          atTop
          (𝓝 (WeakSpace.map proj (toWeakSpace ℝ ProductSpace yFix))) := by
      exact ((WeakSpace.map proj).continuous.tendsto (toWeakSpace ℝ ProductSpace yFix)).comp
        hy_tendsto'
    simpa [proj, WeakSpace.map_apply] using hmap
  have hstar_primal :
      diagonalSubmodule.starProjection yFix ∈
        primal_inclusion_solution_set (Set.normalCone DiagonalSet) (familyOperator A) := by
    rw [primal_inclusion_solution_set_eq_image_resolvent_fixedPoints_reflectedResolventComposition
      (Set.normalCone DiagonalSet) (familyOperator A) diagonalNormalCone_maximal hfamilyA γ]
    refine ⟨yFix, hyFix, ?_⟩
    exact (diagonalStarProjection_eq_resolventLimit_of_fixedPoint A hA γ hyFix).symm
  have hstar_zero :
      diagonalSubmodule.starProjection yFix ∈ (N[DiagonalSet] + familyOperator A).zeros := by
    simpa [primal_inclusion_solution_set] using hstar_primal
  rw [← diagonalPoint_image_zeros_sum_eq_zeros_normalCone_add_familyOperator A] at hstar_zero
  rcases hstar_zero with ⟨xLim, hxLim, hdiag_eq⟩
  have hproj_eq :
      (fun n ↦ diagonalSubmodule.starProjection (y n)) = fun n ↦ diagonalPoint (p n) := by
    funext n
    exact hOrbit.diagonal_starProjection_eq n
  have hweakDiag :
      Tendsto
        (fun n ↦ toWeakSpace ℝ ProductSpace (diagonalPoint (p n)))
        atTop
        (𝓝 (toWeakSpace ℝ ProductSpace (diagonalPoint xLim))) := by
    have hleft :
        (fun n ↦ toWeakSpace ℝ ProductSpace (diagonalSubmodule.starProjection (y n))) =
          fun n ↦ toWeakSpace ℝ ProductSpace (diagonalPoint (p n)) := by
      funext n
      rw [hOrbit.diagonal_starProjection_eq n]
    have hright :
        toWeakSpace ℝ ProductSpace (diagonalSubmodule.starProjection yFix) =
          toWeakSpace ℝ ProductSpace (diagonalPoint xLim) := by
      rw [← hdiag_eq]
    rw [hleft, hright] at hproj_tendsto
    exact hproj_tendsto
  let i0 : Fin m := ⟨0, hm⟩
  let eval0 : ProductSpace →L[ℝ] H := coordinateCLM i0
  have hmapCoord :
      Tendsto
        (fun n ↦ WeakSpace.map eval0 (toWeakSpace ℝ ProductSpace (diagonalPoint (p n))))
        atTop
        (𝓝 (WeakSpace.map eval0 (toWeakSpace ℝ ProductSpace (diagonalPoint xLim)))) := by
    exact ((WeakSpace.map eval0).continuous.tendsto
      (toWeakSpace ℝ ProductSpace (diagonalPoint xLim))).comp hweakDiag
  have hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (p n)) atTop (𝓝 (toWeakSpace ℝ H xLim)) := by
    have hmapCoord' :
        Tendsto
          (fun n ↦ toWeakSpace ℝ H (eval0 (diagonalPoint (p n))))
          atTop
          (𝓝 (toWeakSpace ℝ H (eval0 (diagonalPoint xLim)))) := by
      simpa [WeakSpace.map_apply] using hmapCoord
    simpa [eval0] using hmapCoord'
  exact ⟨xLim, hxLim, hweak⟩

end

end SetValuedOperator
