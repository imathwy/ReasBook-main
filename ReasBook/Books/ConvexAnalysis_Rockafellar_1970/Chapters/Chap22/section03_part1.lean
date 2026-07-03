import Mathlib
import Mathlib.Algebra.Group.Support
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_22_3_1 (from Chap04) -/
open scoped BigOperators RealInnerProductSpace Rockafellar

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*} [Fintype I]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 22.3.1 is the homogeneous zero-right-hand-side form of Farkas' lemma
  for a finite family of weak linear inequalities in a real inner-product space.
- `core/canonical`: the chapter owner theorem
  `linear_inequality_consequence_iff_exists_nonnegative_multiplier`, stated on the intrinsic
  pairing owner layer and whose left-hand side is owner inclusion of the weak feasible set into
  the target half-space.
- `bridge/view`: this item applies that owner theorem to the canonical functional pairing obtained
  from `InnerProductSpace.toDualMap`, then uses injectivity of `toDualMap` to rewrite the
  pointwise weighted-pairing identity certificate as the textbook vector conic-combination
  identity. Consistency is automatic because `x = 0` satisfies every homogeneous weak inequality,
  and the scalar inequality in the multiplier certificate becomes vacuous.

Domain-style sampling used here:
- the project theorem `linear_inequality_consequence_iff_exists_nonnegative_multiplier`;
- `InnerProductSpace.toDualMap` from the chapter inner-product bridge material;
- finite sums over an arbitrary finite index type `[Fintype I]`.

Primitive data vs derived API:
- primitive inputs: the target vector `a0` and the finite family `a`;
- owner abstraction: `linear_inequality_consequence_iff_exists_nonnegative_multiplier` applied to
  the homogeneous scalar family `fun _ ↦ 0` after converting vectors to functionals with
  `InnerProductSpace.toDualMap`;
- derived API: the nonnegative conic-combination characterization, after discarding the vacuous
  scalar inequality.

Layer target: `source-facing`. The corollary remains in the textbook homogeneous form, but its
implementation and supporting API now come directly from the chapter owner theorem.
-/

-- Proof sketch: apply
-- `is_linear_inequality_consequence_iff_exists_nonnegative_multiplier` to the functional family
-- `fun i ↦ ((InnerProductSpace.toDualMap ℝ E) (a i)).toLinearMap` with all right-hand sides equal
-- to `0`. The consistency hypothesis is witnessed by `x = 0`,
-- `InnerProductSpace.toDualMap_apply_apply` rewrites the resulting pointwise inequalities back
-- to the textbook inner-product form, and the scalar inequality `∑ i, λ i * 0 ≤ 0` is automatic.
/-- Corollary 22.3.1: (Farkas' Lemma). The homogeneous inequality `⟪a₀, x⟫ ≤ 0` is a consequence
of the system `⟪aᵢ, x⟫ ≤ 0` for `i ∈ I` if and only if there are nonnegative real numbers `λᵢ`
such that `∑ i, λᵢ • aᵢ = a₀`. -/
theorem homogeneous_farkas_lemma
    (a0 : E) (a : I → E) :
    (∀ x : E, (∀ i : I, ⟪a i, x⟫ ≤ 0) → ⟪a0, x⟫ ≤ 0) ↔
      ∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∑ i, weights i • a i) = a0 := by
  let toDualMap := InnerProductSpace.toDualMap ℝ E
  let a0' : E →ₗ[ℝ] ℝ := (toDualMap a0).toLinearMap
  let a' : I → E →ₗ[ℝ] ℝ := fun i ↦ (toDualMap (a i)).toLinearMap
  have hcertificate :
      (∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E, ∑ i, weights i * (⟪x, a' i⟫ₚ : ℝ) = (⟪x, a0'⟫ₚ : ℝ))) ↔
        ∃ weights : I → ℝ,
          (∀ i : I, 0 ≤ weights i) ∧
            (∑ i, weights i • a i) = a0 := by
    constructor
    · rintro ⟨weights, hnonneg, hsum⟩
      refine ⟨weights, hnonneg, ?_⟩
      have hsum_cont : ∑ i, weights i • toDualMap (a i) = toDualMap a0 := by
        ext x
        simpa [a0', a', smul_eq_mul] using hsum x
      apply toDualMap.injective
      simpa using hsum_cont
    · rintro ⟨weights, hnonneg, hsum⟩
      refine ⟨weights, hnonneg, ?_⟩
      have hsum_cont : ∑ i, weights i • toDualMap (a i) = toDualMap a0 := by
        simpa using congrArg toDualMap hsum
      intro x
      have hsum_cont_x :
          (∑ i, weights i • toDualMap (a i)) x = toDualMap a0 x := by
        simpa using congrArg (fun b : E →L[ℝ] ℝ => b x) hsum_cont
      simpa [a0', a', smul_eq_mul] using hsum_cont_x
  have hmain :
      (∀ x : E, (∀ i : I, ⟪a i, x⟫ ≤ 0) → ⟪a0, x⟫ ≤ 0) ↔
        (∃ weights : I → ℝ,
          (∀ i : I, 0 ≤ weights i) ∧
            (∀ x : E, ∑ i, weights i * (⟪x, a' i⟫ₚ : ℝ) = (⟪x, a0'⟫ₚ : ℝ))) := by
    simpa [a0', a', InnerProductSpace.toDualMap_apply_apply] using
      (is_linear_inequality_consequence_iff_exists_nonnegative_multiplier
        a0' 0 a' (fun _ ↦ (0 : ℝ))
        (by
          refine ⟨(0 : E), ?_⟩
          intro i
          simp [a']))
  exact hmain.trans hcertificate

end

/-! ### Text_22_3_2 (from Chap04) -/
open scoped PolarCone Rockafellar

section

variable {𝕜 : Type*} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {X : Type*} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type*} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜] [HasLinearPairing Y X 𝕜]
variable {I : Type*}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 22.3.2 studies the cone generated by a family `a`, its polar, the double
  polar, and the consequence reading of double-polar membership.
- `core/canonical`: in this project, generated convex cones live at the owner
  `cone[𝕜] (Set.range a)`, and the chapter polar owner is `polarCone` with notation `Kᵒ[𝕜]`
  across the pairing directions `X ⟂ Y` and `Y ⟂ X`.
- `bridge/view`: clause (2) rewrites membership in `Kᵒᵒ` into the textbook homogeneous
  consequence statement, while clause (3) derives closedness of the finitely generated cone from
  the Chapter 19 finite-generator/polyhedral bridge and then applies the chapter bipolar owner
  theorem directly.

Domain-style sampling used here:
- `cone[𝕜] (Set.range a)`;
- `polarCone`;
- `polarCone_cone_range_eq_generator_inequalities`;
- `polarCone_polarCone_eq`;
- `Set.IsPolyhedral.cone`.

Primitive data vs derived API:
- primitive input: the finite generator family `a : I → X`;
- owner object: `cone[𝕜] (Set.range a)`;
- derived API: the double-polar consequence criterion and the bipolar equality; the half-space
description itself is reused directly from
  `polarCone_cone_range_eq_generator_inequalities`, while closedness of the generated cone is
  derived from the upstream finite-generator/polyhedral owner API, and the bipolar identity is
  reused directly from `polarCone_polarCone_eq`.

Layer target: `source-facing`, stated directly with the canonical chapter generated-cone owner and
reusing the earlier chapter half-space theorem instead of introducing a second exact-interface
wrapper. Clause (2) lives directly at the pairing owner layer inherited from
`mem_polarCone_iff_pairing` and `polarCone_cone_range_eq_generator_inequalities`; clause (3) moves
to a separate stronger section because closedness uses the normed finite-dimensional ambient and
the bipolar endpoint uses the complete real inner-product owner layer.
-/

-- Proof sketch: unfold membership in the double polar with `mem_polarCone_iff_pairing`, then
-- rewrite the first polar by `polarCone_cone_range_eq_generator_inequalities`. The remaining
-- statement is
-- exactly the homogeneous consequence condition in canonical pairing orientation.
/-- Text 22.3.2 (2), pairing layer: the homogeneous inequality `⟪x, a₀⟫ₚ ≤ 0` is a consequence of
the system `⟪aᵢ, x⟫ₚ ≤ 0`, `i ∈ I`, if and only if `a₀` lies in the double polar of the finitely
generated cone `K = cone[𝕜] (Set.range a)`. -/
theorem homogeneous_inequality_consequence_iff_mem_doublePolarCone_hull_range
    (a0 : X) (a : I → X) :
    let K : Set X := cone[𝕜] (Set.range a)
    (∀ x : Y, (∀ i : I, ⟪a i, x⟫ₚ ≤ (0 : 𝕜)) → ⟪x, a0⟫ₚ ≤ (0 : 𝕜)) ↔
      a0 ∈ ((Kᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X) := by
  let K : Set X := cone[𝕜] (Set.range a)
  change (∀ x : Y, (∀ i : I, ⟪a i, x⟫ₚ ≤ (0 : 𝕜)) → ⟪x, a0⟫ₚ ≤ (0 : 𝕜)) ↔
    a0 ∈ ((Kᵒ[𝕜] : Set Y)ᵒ[𝕜] : Set X)
  rw [mem_polarCone_iff_pairing, polarCone_cone_range_eq_generator_inequalities]
  rfl

end

section

variable {𝕜 : Type*} [CommRing 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type*} [AddCommMonoid E] [Module 𝕜 E]
variable {I : Type*}

private theorem cone_insert_zero_eq_cone (S : Set E) :
    (cone[𝕜] (insert (0 : E) S) : Set E) = (cone[𝕜] S : Set E) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact Submodule.span_le.2 <| by
      rintro x (rfl | hx)
      · exact (cone[𝕜] S).zero_mem
      · exact PointedCone.subset_hull hx
  · exact Submodule.span_le.2 <| fun x hx ↦ PointedCone.subset_hull (by simp [hx])

private theorem cone_convexHull_eq_cone (S : Set E) :
    (cone[𝕜] (convexHull 𝕜 S) : Set E) = (cone[𝕜] S : Set E) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact
      Submodule.span_le.2 <|
        convexHull_min (fun x hx ↦ PointedCone.subset_hull hx) (cone[𝕜] S).convex
  · exact Submodule.span_le.2 <| fun x hx ↦ PointedCone.subset_hull (subset_convexHull 𝕜 S hx)

end

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]
  [IsStrictOrderedRing 𝕜] [CompleteSpace 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [T2Space E]
variable {I : Type*}

-- Proof sketch: `convexHull 𝕜 (insert 0 (Set.range a))` is a polytope generated by finitely many
-- points, so Corollary 19.7.1 gives polyhedrality of the generated cone; finite-dimensionality
-- then gives closedness, and `cone_convexHull_eq_cone` / `cone_insert_zero_eq_cone` identify this
-- cone with `cone[𝕜] (Set.range a)`.
private theorem isClosed_cone_hull_range
    [FiniteDimensional 𝕜 E] [Finite I] (a : I → E) :
    IsClosed (cone[𝕜] (Set.range a) : Set E) := by
  let K : Set E := cone[𝕜] (Set.range a)
  let C : Set E := convexHull 𝕜 (insert (0 : E) (Set.range a))
  have hC_polytope : C.IsPolytope 𝕜 := by
    refine Set.IsPolytope.mk 𝕜 ?_
    exact (Set.finite_singleton 0).union (Set.finite_range a)
  have h0C : (0 : E) ∈ C := subset_convexHull 𝕜 (insert (0 : E) (Set.range a)) (by simp)
  have hcone_polyhedral : (cone[𝕜] C : Set E).IsPolyhedral 𝕜 := hC_polytope.isPolyhedral.cone h0C
  have hcone_closed : IsClosed (cone[𝕜] C : Set E) := hcone_polyhedral.isClosed_of_finiteDimensional
  simpa [K, C, cone_convexHull_eq_cone, cone_insert_zero_eq_cone] using
    hcone_closed

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {I : Type*}

-- Proof sketch: closedness of `K = cone[ℝ] (Set.range a)` is provided by the scalar-generic
-- bridge `isClosed_cone_hull_range`; then the chapter bipolar owner theorem
-- `polarCone_polarCone_eq` applies at the complete real inner-product layer.
/-- Text 22.3.2 (3): the bipolar of the finitely generated cone
`K = cone[ℝ] (Set.range a)` is `K` itself. -/
theorem doublePolarCone_hull_range_eq_hull_range
    [FiniteDimensional ℝ E] [Finite I]
    (a : I → E) :
    let K : Set E := cone[ℝ] (Set.range a)
    ((Kᵒ[ℝ] : Set E)ᵒ[ℝ] : Set E) = K := by
  let K : Set E := cone[ℝ] (Set.range a)
  change ((Kᵒ[ℝ] : Set E)ᵒ[ℝ] : Set E) = K
  have hK_closed : IsClosed K := by
    simpa [K] using isClosed_cone_hull_range (𝕜 := ℝ) (E := E) a
  have hK_nonempty : K.Nonempty := by
    exact ⟨0, (cone[ℝ] (Set.range a)).zero_mem⟩
  have hK_convexCone : Set.IsConvexCone ℝ K := by
    refine ⟨?_, ?_⟩
    · simpa [K] using ((cone[ℝ] (Set.range a) : ConvexCone ℝ E).isCone)
    · simpa [K] using ((cone[ℝ] (Set.range a)).convex : Convex ℝ (cone[ℝ] (Set.range a) : Set E))
  exact polarCone_polarCone_eq K hK_nonempty hK_closed hK_convexCone

end

/-! ### Text_22_3_3 (from Chap04) -/
section

open scoped BigOperators Rockafellar

universe u

variable {X Y : Type*}
  {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup X] [Module R X] [FiniteDimensional R X]
  [AddCommMonoid Y] [Module R Y]
  [TopologicalSpace (Y × R)] [Bornology (Y × R)]
variable {I : Type u}

local notation "YStar" => Y × R
local notation "coefficientSet[" a ", " α "]" => Set.range (fun i ↦ (a i, α i))
local notation "solutionSet[" a ", " α "]" =>
  (LinearConstraintRelation.leFeasible (X := X) a α : Set X)

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.3.3 is the indexed-family version of the criterion for when one linear
  inequality is a consequence of a closed bounded system of linear inequalities in a
  finite-dimensional pairing `⟪·, ·⟫ₚ : X × Y → R`.
- `core/canonical`: the owner abstractions already present in the project are
  `LinearConstraintRelation.leFeasible`, `linearInequalitySolutionSet`, `closedHalfSpaceLE`,
  `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination`, and finitely supported
  multiplier families `I →₀ R`.
- `bridge/view`: this file keeps the source indexing data `a : I → Y` and `α : I → R`, but
  states the indexed system through the canonical weak owner
  `LinearConstraintRelation.leFeasible a α`, while
  re-expressing the owner theorem on the coefficient set `coefficientSet[a, α]` as a finitely
  supported multiplier certificate on the original index type `I` and preserving the owner-side
  Caratheodory bound
  `weights.support.card ≤ Module.finrank R X`.

Domain-style sampling used here:
- `LinearConstraintRelation.leFeasible`;
- `linearInequalitySolutionSet`;
- `closedHalfSpaceLE`;
- `subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination`;
- `affineSpan`;
- `Finsupp.sum` and `weights.support.card`.

Primitive data vs derived API:
- primitive inputs: the indexed coefficient family `i ↦ (a i, α i)` and the target inequality
  `(a0, α0)`;
- derived API: the equivalence between consequence of the full indexed system and existence of a
  finitely supported nonnegative multiplier family on `I` with support cardinality at most
  `Module.finrank R X`, expressed directly by the weighted-sum conditions coming from the chapter
  owner theorem.

Semantic-fidelity note:
- the source assumptions that the system is consistent and that `(0, 0)` is absent from the
  coefficient set are omitted from the public theorem statement because they are redundant once the
  indexed solution set has full affine span and the coefficient set is closed and bounded.

Layer target: `bridge/view`. The theorem keeps the source indexed family, while the public
certificate surface stays on the canonical existential `I →₀ R` multiplier witness, rather than a
secondary `Fin m` enumeration layer.
-/

-- Proof sketch: translate finite subset certificates on `coefficientSet[a, α]` into finitely
-- supported multipliers on the index type `I`, and conversely evaluate any such indexed
-- multiplier certificate pointwise on a feasible `x`.
omit [FiniteDimensional R X] [IsOrderedRing R]
  [TopologicalSpace (Y × R)] [Bornology (Y × R)] in
private theorem exists_finsupp_of_range_conicCombination
    (a : I → Y) (α : I → R) {s : Finset YStar}
    (hs : (↑s : Set YStar) ⊆ coefficientSet[a, α])
    (weights : {y // y ∈ s} → R)
    (hnonneg : ∀ y, 0 ≤ weights y) :
    ∃ weights' : I →₀ R,
      weights'.support.card ≤ s.card ∧
        (∀ i : I, 0 ≤ weights' i) ∧
          weights'.sum (fun i w ↦ w • a i) =
            s.attach.sum (fun y ↦ weights y • (y : YStar).1) ∧
          weights'.sum (fun i w ↦ w * α i) =
            s.attach.sum (fun y ↦ weights y * (y : YStar).2) := by
  classical
  let chooseIndex : {y // y ∈ s} → I := fun y ↦ Classical.choose (hs y.2)
  have hchoose_spec (y : {y // y ∈ s}) :
      (a (chooseIndex y), α (chooseIndex y)) = (y : Y × R) :=
    Classical.choose_spec (hs y.2)
  have hchoose_fst (y : {y // y ∈ s}) : a (chooseIndex y) = (y : YStar).1 :=
    congrArg Prod.fst (hchoose_spec y)
  have hchoose_snd (y : {y // y ∈ s}) : α (chooseIndex y) = (y : YStar).2 :=
    congrArg Prod.snd (hchoose_spec y)
  have hchoose_inj : Function.Injective chooseIndex := by
    intro y z hyz
    apply Subtype.ext
    calc
      (y : Y × R) = (a (chooseIndex y), α (chooseIndex y)) := (hchoose_spec y).symm
      _ = (a (chooseIndex z), α (chooseIndex z)) := by rw [hyz]
      _ = (z : Y × R) := hchoose_spec z
  let weightsSubtype : {y // y ∈ s} →₀ R := Finsupp.equivFunOnFinite.symm weights
  let weights' : I →₀ R := weightsSubtype.mapDomain chooseIndex
  refine ⟨weights', ?_, ?_, ?_, ?_⟩
  · calc
      weights'.support.card = (weightsSubtype.support.image chooseIndex).card := by
        simpa [weights'] using congrArg Finset.card
          (Finsupp.mapDomain_support_of_injective hchoose_inj weightsSubtype)
      _ = weightsSubtype.support.card := by
        exact Finset.card_image_of_injective weightsSubtype.support hchoose_inj
      _ ≤ Fintype.card {y // y ∈ s} := Finset.card_le_univ weightsSubtype.support
      _ = s.card := by simp
  · intro i
    by_cases hi : i ∈ Set.range chooseIndex
    · rcases hi with ⟨y, rfl⟩
      simpa [weights', weightsSubtype] using
        (show 0 ≤ Finsupp.mapDomain chooseIndex weightsSubtype (chooseIndex y) from by
          rw [Finsupp.mapDomain_apply hchoose_inj weightsSubtype y]
          exact hnonneg y)
    · simpa [weights'] using
        (show 0 ≤ Finsupp.mapDomain chooseIndex weightsSubtype i from by
          rw [Finsupp.mapDomain_notin_range weightsSubtype i hi])
  · calc
      weights'.sum (fun i w ↦ w • a i)
          = weightsSubtype.sum (fun y w ↦ w • a (chooseIndex y)) := by
              simpa [weights'] using
                (Finsupp.sum_mapDomain_index_inj hchoose_inj : _)
      _ = ∑ y, weightsSubtype y • a (chooseIndex y) := by
            rw [Finsupp.sum_fintype]
            intro y
            simp
      _ = s.attach.sum (fun y ↦ weights y • (y : YStar).1) := by
            rw [Finset.univ_eq_attach s]
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hchoose_fst y]
            simp [weightsSubtype]
  · calc
      weights'.sum (fun i w ↦ w * α i)
          = weightsSubtype.sum (fun y w ↦ w * α (chooseIndex y)) := by
              simpa [weights'] using
                (Finsupp.sum_mapDomain_index_inj hchoose_inj : _)
      _ = ∑ y, weightsSubtype y * α (chooseIndex y) := by
            rw [Finsupp.sum_fintype]
            intro y
            simp
      _ = s.attach.sum (fun y ↦ weights y * (y : YStar).2) := by
            rw [Finset.univ_eq_attach s]
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [hchoose_snd y]
            simp [weightsSubtype]

omit [PartialOrder R] [IsOrderedRing R] [AddCommGroup X] [Module R X]
  [FiniteDimensional R X] [TopologicalSpace (Y × R)] [Bornology (Y × R)] in
private theorem pairing_finset_sum_right
    [HasPairing X Y R] [HasPairingAddRight X Y R] [HasPairingSMulRight X Y R]
    (x : X) (s : Finset I) (f : I → Y) :
    (⟪x, ∑ i ∈ s, f i⟫ₚ : R) = ∑ i ∈ s, (⟪x, f i⟫ₚ : R) := by
  classical
  have hpair_zero : (⟪x, (0 : Y)⟫ₚ : R) = 0 := by
    simpa using (pairing_smul_right (x := x) (c := (0 : R)) (y := (0 : Y)))
  induction s using Finset.induction_on with
  | empty =>
      simp [hpair_zero]
  | @insert i s hi hs =>
      simp [Finset.sum_insert, hi, hs, HasPairingAddRight.pairing_add_right]

/-- Indexed bridge form of Text 22.3.3: if the coefficient set `coefficientSet[a, α]` is closed
and bounded and the indexed solution set `solutionSet[a, α]` is full-dimensional, then the
consequence condition `solutionSet[a, α] ⊆ closedHalfSpaceLE a0 α0` is equivalent to the
canonical finitely supported multiplier certificate on the original index type `I`, with support
bound `Module.finrank R X`. -/
theorem indexed_subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate
    [HasPairing X Y R] [HasPairingAddRight X Y R] [HasPairingSMulRight X Y R]
    (a : I → Y) (α : I → R) (a0 : Y) (α0 : R)
    (hclosed : IsClosed (coefficientSet[a, α]))
    (hbounded : Bornology.IsBounded (coefficientSet[a, α]))
    (hfull : affineSpan R (solutionSet[a, α]) = ⊤) :
    solutionSet[a, α] ⊆ closedHalfSpaceLE a0 α0 ↔
      ∃ weights : I →₀ R,
        weights.support.card ≤ Module.finrank R X ∧
          (∀ i : I, 0 ≤ weights i) ∧
            weights.sum (fun i w ↦ w • a i) = a0 ∧
            weights.sum (fun i w ↦ w * α i) ≤ α0 := by
  constructor
  · intro hsubset
    have hfull' : affineSpan R
        ((linearInequalitySolutionSet (Set.range fun i ↦ (a i, α i))) : Set X) = ⊤ := by
      simpa [linearInequalitySolutionSet_range_eq_leFeasible] using hfull
    have hsubset' :
        ((linearInequalitySolutionSet (Set.range fun i ↦ (a i, α i))) : Set X) ⊆
          closedHalfSpaceLE a0 α0 :=
      by simpa [linearInequalitySolutionSet_range_eq_leFeasible] using hsubset
    rcases
      (subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination
        hclosed hbounded hfull' a0 α0).mp hsubset' with
      ⟨s, hcert_card, hs, weights, hnonneg, hvector, hscalar⟩
    rcases
      exists_finsupp_of_range_conicCombination
        a α hs weights hnonneg with
      ⟨weights', hcard, hnonneg', hvector', hscalar'⟩
    refine ⟨weights', le_trans hcard hcert_card, hnonneg', ?_, ?_⟩
    · calc
        weights'.sum (fun i w ↦ w • a i)
            = s.attach.sum (fun y ↦ weights y • (y : YStar).1) := hvector'
        _ = a0 := hvector.symm
    · calc
        weights'.sum (fun i w ↦ w * α i)
            = s.attach.sum (fun y ↦ weights y * (y : YStar).2) := hscalar'
        _ ≤ α0 := hscalar
  · rintro ⟨weights, _hcard, hnonneg, hweighted_sum_fst, hweighted_sum_snd_le⟩ x hx
    rw [mem_closedHalfSpaceLE_iff]
    rw [LinearConstraintRelation.mem_leFeasible] at hx
    have hsum_le :
        weights.sum (fun i w ↦ w * ⟪x, a i⟫ₚ) ≤
          weights.sum (fun i w ↦ w * α i) := by
      rw [Finsupp.sum, Finsupp.sum]
      exact Finset.sum_le_sum fun i hi ↦
        mul_le_mul_of_nonneg_left (hx i) (hnonneg i)
    have hpair_sum :
        (⟪x, weights.sum (fun i w ↦ w • a i)⟫ₚ : R) =
          weights.sum (fun i w ↦ w * ⟪x, a i⟫ₚ) := by
      rw [Finsupp.sum, Finsupp.sum]
      calc
        (⟪x, ∑ i ∈ weights.support, weights i • a i⟫ₚ : R) =
            ∑ i ∈ weights.support, (⟪x, weights i • a i⟫ₚ : R) :=
              pairing_finset_sum_right (x := x) (s := weights.support)
                (f := fun i ↦ weights i • a i)
        _ = ∑ i ∈ weights.support, weights i * (⟪x, a i⟫ₚ : R) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [pairing_smul_right]
    calc
      (⟪x, a0⟫ₚ : R) = ⟪x, weights.sum (fun i w ↦ w • a i)⟫ₚ := by
        simp [hweighted_sum_fst]
      _ = weights.sum (fun i w ↦ w * ⟪x, a i⟫ₚ) := hpair_sum
      _ ≤ weights.sum (fun i w ↦ w * α i) := hsum_le
      _ ≤ α0 := hweighted_sum_snd_le

end

/-! ### Theorem_22_3 (from Chap04) -/
open scoped BigOperators Rockafellar

section

variable {E : Type*} {Y : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" a ", " α "]" =>
  (LinearConstraintRelation.leFeasible (X := E) a α : Set E)
local notation "targetSet[" a0 ", " α0 "]" =>
  (closedHalfSpaceLE a0 α0 : Set E)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 22.3 is the finite-system Farkas criterion for when one weak linear
  inequality is a consequence of a consistent finite family of weak linear inequalities.
- `core/canonical`: the left-hand side is the owner inclusion
  `solutionSet[a, α] ⊆ targetSet[a0, α0]`, reusing the chapter feasible-set owner
  `LinearConstraintRelation.leFeasible` and half-space owner `closedHalfSpaceLE`, with coefficient
  data organized on the intrinsic pairing side `a : I → Y`; the right-hand side is the standard
  finite nonnegative-multiplier certificate written as a pointwise weighted-pairing identity over
  all `x : E`, plus the scalar bound inequality.
- `bridge/view`: the functional-dual and textbook vector forms are recovered by specializing
  `Y` to canonical pairing models (`E →ₗ[ℝ] ℝ`, `E →L[ℝ] ℝ`, or `E` with inner product). The pointwise
  implication surface is already owned upstream by
  `is_linear_inequality_consequence_leFeasible_iff`, so this file keeps that implication form only as a
  thin companion theorem rather than as a second main public entry.

Domain-style sampling used here:
- `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `LinearConstraintRelation.leFeasible` from `Chap01.Corollary_2_1_1`;
- `is_linear_inequality_consequence_leFeasible_iff` from `Chap04.Text_22_2_2`;
- `xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate` and the
  chapter owner layer `a : I → E →ₗ[ℝ] ℝ` from `Chap04.Theorem_22_1`.

Primitive data vs derived API:
- primitive inputs: the pairing-side coefficient family `a : I → Y`, the bounds `α : I → ℝ`, and
  the target inequality `(a0, α0)` with `a0 : Y`;
- core owner abstraction: `solutionSet[a, α]` and `targetSet[a0, α0]`;
- derived API: the pointwise implication form of consequence, obtained from the owner inclusion by
  `is_linear_inequality_consequence_leFeasible_iff`, and concrete functional/vector specializations
  obtained by canonical pairing instances.

Layer target: `core/canonical`, with the main theorem stated on the chapter owner objects and the
textbook implication form retained as a bridge/view companion.

Abstraction checks for this item:
- ambient structure: this file now lives on the pairing owner layer
  `[HasLinearPairing E Y ℝ]`; no norm/topology/finite-dimensional assumptions are required to state
  the owner inclusion or the multiplier certificate.
- scalar layer: the theorem remains over `ℝ` because the Chapter 22 multiplier certificate and the
  upstream alternative used to justify it are real-valued in this project (`aᵢ x ≤ αᵢ` with
  `αᵢ : ℝ` and multipliers `λᵢ : ℝ`). A genuine scalar generalization should start upstream at the
  Chapter 21/22 certificate owners rather than adding a local ad hoc scalar parameter here.
-/

-- Proof sketch: the functional inequality `a₀ x ≤ α₀` is a consequence exactly when the
-- augmented mixed system consisting of the strict inequality `(-a₀) x < -α₀` together with the
-- original weak inequalities is infeasible. Apply Theorem 22.2 with `k = 1` to this mixed
-- system. Its transposition certificate has a positive coefficient on the strict inequality;
-- divide the other coefficients by that positive coefficient to obtain the desired nonnegative
-- multipliers, and conversely clear denominators to recover the Theorem 22.2 certificate.
/-- Theorem 22.3 on the chapter functional-owner layer: if the weak owner feasible set
`solutionSet[a, α]` is nonempty, then the inequality `a₀ x ≤ α₀` is a consequence of this system
if and only if there is a nonnegative multiplier family with weighted pairing identity
`∀ x, ∑ i, λᵢ * ⟪x, aᵢ⟫ = ⟪x, a₀⟫` and
`∑ i, λᵢ αᵢ ≤ α₀`. The textbook finite-dimensional real inner-product-space statement is
recovered by `InnerProductSpace.toDual`. -/
theorem linear_inequality_consequence_iff_exists_nonnegative_multiplier
    (a0 : Y) (α0 : ℝ) (a : I → Y) (α : I → ℝ)
    (hconsistent : (solutionSet[a, α]).Nonempty) :
    solutionSet[a, α] ⊆ targetSet[a0, α0] ↔
      ∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E,
            ∑ i, weights i * (⟪x, a i⟫ₚ : ℝ) = (⟪x, a0⟫ₚ : ℝ)) ∧
          (∑ i, weights i * α i) ≤ α0 := sorry

/-- Companion pointwise form of Theorem 22.3: the owner inclusion
`solutionSet[a, α] ⊆ targetSet[a0, α0]` is exactly the textbook implication that every
simultaneous solution of the system satisfies the target inequality. -/
theorem is_linear_inequality_consequence_iff_exists_nonnegative_multiplier
    (a0 : Y) (α0 : ℝ) (a : I → Y) (α : I → ℝ)
    (hconsistent : ∃ x : E, ∀ i : I, (⟪x, a i⟫ₚ : ℝ) ≤ α i) :
    (∀ x : E, (∀ i : I, (⟪x, a i⟫ₚ : ℝ) ≤ α i) → (⟪x, a0⟫ₚ : ℝ) ≤ α0) ↔
      ∃ weights : I → ℝ,
        (∀ i : I, 0 ≤ weights i) ∧
          (∀ x : E,
            ∑ i, weights i * (⟪x, a i⟫ₚ : ℝ) = (⟪x, a0⟫ₚ : ℝ)) ∧
          (∑ i, weights i * α i) ≤ α0 := by
  have hsolutionSet : (solutionSet[a, α]).Nonempty := by
    simpa [Set.Nonempty, LinearConstraintRelation.mem_leFeasible] using hconsistent
  simpa using
    (is_linear_inequality_consequence_leFeasible_iff a0 α0 a α).symm.trans
      (linear_inequality_consequence_iff_exists_nonnegative_multiplier
        a0 α0 a α hsolutionSet)

end

/-! ### Text_22_3_4 (from Chap04) -/
section

universe u

variable {X Y : Type*}
  {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup X] [Module R X] [FiniteDimensional R X]
  [AddCommMonoid Y] [Module R Y]
  [TopologicalSpace (Y × R)] [Bornology (Y × R)]
  [HasPairing X Y R] [HasPairingAddRight X Y R] [HasPairingSMulRight X Y R]
variable {I : Type u}

local notation "solutionSet[" a "]" =>
  ((LinearConstraintRelation.leFeasible (X := X) a (fun _ : I ↦ (0 : R))) : Set X)
local notation "coefficientSet[" a "]" =>
  (Set.range (fun i : I ↦ (a i, (0 : R))) : Set (Y × R))

/-!
Source/core/bridge triage:

- `source-facing`: Text 22.3.4 is the homogeneous indexed-family specialization of the infinite
  linear-inequality consequence criterion from Text 22.3.3.
- `core/canonical`: the indexed homogeneous weak system owner is
  `LinearConstraintRelation.leFeasible a (fun _ ↦ (0 : R))`, and the closed/bounded hypothesis is
  stated on the canonical coefficient owner `coefficientSet[a]` used by the indexed bridge
  theorem from Text 22.3.3.
- `bridge/view`: the theorem remains on the homogeneous-feasible-set owner and target half-space
  owner `closedHalfSpaceLE a0 0`; only the vacuous scalar inequality is discarded from the
  certificate conclusion.

Domain-style sampling used here:
- `LinearConstraintRelation.leFeasible`;
- `LinearConstraintRelation.mem_leFeasible`;
- `closedHalfSpaceLE`;
- `indexed_subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate`;
- `Finsupp.sum` and `weights.support.card`.

Primitive data vs derived API:
- primitive inputs: the indexed coefficient family `a : I → Y` and the target vector `a0 : Y`;
- primitive coefficient owner: `coefficientSet[a]`;
- primitive owner object: `solutionSet[a]`;
- derived API: the equivalence between homogeneous consequence and a finitely supported conic
  combination of support cardinality at most `Module.finrank R X`. The general scalar inequality
  is derived and vacuous in this homogeneous case, so it does not remain in the public theorem
  surface.

Layer target: `source-facing`. This file records the homogeneous theorem itself, not a new wrapper
around the certificate data already used in the preceding indexed theorem.
-/

-- Proof sketch: apply
-- `indexed_subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate` to the
-- homogeneous scalar family `fun _ ↦ (0 : R)`. The scalar inequality in the resulting finitely
-- supported certificate simplifies to `0 ≤ 0`, leaving the usual nonnegative
-- conic-combination conclusion with the same support bound.
/-- Text 22.3.4, stated on the canonical ambient owner: for a closed bounded family of vectors in
a pairing `⟪·, ·⟫ₚ : X × Y → R` over an ordered division ring `R`, with
finite-dimensional primal space
`X`, whose canonical
homogeneous feasible set is
full-dimensional (`affineSpan R _ = ⊤`), the homogeneous inequality `⟪a₀, x⟫ ≤ 0` is a
consequence of the system `⟪aᵢ, x⟫ ≤ 0` if and only if `a₀` is a nonnegative linear combination
of at most `Module.finrank R X` vectors from the family. -/
theorem indexed_homogeneous_consequence_iff_exists_dualCaratheodory_conicCombination
    (a : I → Y) (a0 : Y)
    (hclosed : IsClosed (coefficientSet[a]))
    (hbounded : Bornology.IsBounded (coefficientSet[a]))
    (hfull : affineSpan R (solutionSet[a]) = ⊤) :
    solutionSet[a] ⊆ closedHalfSpaceLE a0 (0 : R) ↔
      ∃ weights : I →₀ R,
        weights.support.card ≤ Module.finrank R X ∧
          (∀ i : I, 0 ≤ weights i) ∧
            weights.sum (fun i w ↦ w • a i) = a0 := by
  have hindexed :
      solutionSet[a] ⊆ closedHalfSpaceLE a0 (0 : R) ↔
        ∃ weights : I →₀ R,
          weights.support.card ≤ Module.finrank R X ∧
            (∀ i : I, 0 ≤ weights i) ∧
              weights.sum (fun i w ↦ w • a i) = a0 ∧
              weights.sum (fun i w ↦ w * (0 : R)) ≤ (0 : R) :=
    indexed_subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate
      a (fun _ ↦ (0 : R)) a0 (0 : R) hclosed hbounded hfull
  constructor
  · intro hsubset
    rcases hindexed.mp hsubset with ⟨weights, hcard, hnonneg, hsum, _hscalar⟩
    exact ⟨weights, hcard, hnonneg, hsum⟩
  · rintro ⟨weights, hcard, hnonneg, hsum⟩
    refine hindexed.mpr ⟨weights, hcard, hnonneg, hsum, ?_⟩
    simp

end

/-! ### Text_22_3_5 (from Chap04) -/
open scoped BigOperators RealInnerProductSpace Rockafellar
open LinearConstraintRelation

noncomputable section

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 22.3.5 is Rockafellar's mixed alternative in which a chosen subset of a
  finite family of linear constraints is imposed as equalities while the complementary indices
  remain weak inequalities.
- `core/canonical`: the owner layer is `LinearConstraintRelation.feasibleSet` together with
  `LinearConstraintRelation.eqOn`, and the mixed alternative is exposed at the pairing layer
  `a : I → Y` under `[HasLinearPairing E Y ℝ]`.
- `bridge/view`: the pairing-side nonemptiness reformulation of the owner feasible set and the
  linear-functional and inner-product specializations.

Domain-style sampling used here:
- the Chapter 1 owners `LinearConstraintRelation.eqOn` and `LinearConstraintRelation.feasibleSet`;
- the owner-side membership theorem `LinearConstraintRelation.mem_feasibleSet`;
- the Chapter 4 weak-alternative theorems
  `xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate` and
  `xor_exists_feasible_point_or_weak_linear_inequality_farkas_certificate`;
- the Fréchet-Riesz bridge `InnerProductSpace.toDual`.

Primitive data vs derived API:
- primitive source data for the main theorem: a finite index type `I`, pairing-side coefficients
  `a : I → Y`, bounds `α : I → ℝ`, and the equality-index set `eqIndices : Set I`;
- owner object: the mixed feasible set `feasibleSet (eqOn eqIndices) a α`;
- derived API: the functional linear-map specialization and the textbook inner-product vector
  restatement.

Layer target: `core/canonical` for the pairing-owner theorem, with `bridge/view` companions for
the linear-functional and inner-product presentations.

Abstraction checks for this item:
- Codomain/owner layer: the source-facing nonemptiness bridge is stated directly on the pairing
  owner `feasibleSet (eqOn eqIndices) a α`, with pointwise pairing notation `⟪x, a i⟫ₚ`.
- Scalar layer: multiplier alternatives remain over `ℝ` in this file because they are reused from
  Theorem 22.1, whose upstream proof route is currently real-linear.
- Ambient structure: no inner-product assumptions appear on the primary mixed owner theorem; the
  inner-product formulation is retained only as a downstream bridge.
-/

section PairingOwner

variable {𝕜 : Type*} [LE 𝕜] [LT 𝕜]
variable {X Y : Type*} [HasPairing X Y 𝕜]
variable {I : Type*}

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set X)

/-- The owner mixed feasible set is nonempty exactly when the pairing-side mixed
equality/inequality system has a solution. -/
theorem mixed_linear_constraint_solution_set_nonempty_iff
    (a : I → Y) (α : I → 𝕜) (eqIndices : Set I) :
    (solutionSet[eqIndices; a, α]).Nonempty ↔
      ∃ x : X,
        (∀ i : I, i ∉ eqIndices → (⟪x, a i⟫ₚ ≤ α i)) ∧
          (∀ i : I, i ∈ eqIndices → (⟪x, a i⟫ₚ = α i)) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      have hxi := (mem_feasibleSet _ _ _ _).1 hx i
      simpa [eqOn, hi] using hxi
    · intro i hi
      have hxi := (mem_feasibleSet _ _ _ _).1 hx i
      simpa [eqOn, hi] using hxi
  · rintro ⟨x, hxle, hxeq⟩
    refine ⟨x, (mem_feasibleSet _ _ _ _).2 ?_⟩
    intro i
    by_cases hi : i ∈ eqIndices
    · simpa [eqOn, hi] using hxeq i hi
    · simpa [eqOn, hi] using hxle i hi

end PairingOwner

section FunctionalOwner

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set E)

private def mixedLinearConstraintFarkasFunctional
    (a : I → E →ₗ[ℝ] ℝ) (eqIndices : Set I) : I ⊕ I → E →ₗ[ℝ] ℝ :=
  let _ : DecidablePred (· ∈ eqIndices) := Classical.decPred eqIndices
  Sum.elim a fun i ↦ if i ∈ eqIndices then -a i else 0

private def mixedLinearConstraintFarkasScalar
    (α : I → ℝ) (eqIndices : Set I) : I ⊕ I → ℝ :=
  let _ : DecidablePred (· ∈ eqIndices) := Classical.decPred eqIndices
  Sum.elim α fun i ↦ if i ∈ eqIndices then -α i else 0

private def mixedLinearConstraintWeakSolutionSet
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) : Set E :=
  linearInequalitySolutionSet
    (Set.range fun j : I ⊕ I ↦
      (mixedLinearConstraintFarkasFunctional a eqIndices j,
        mixedLinearConstraintFarkasScalar α eqIndices j))

omit [FiniteDimensional ℝ E] [Fintype I] in
private theorem weakSolutionSet_eq_mixed_linear_constraint_solutionSet
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    mixedLinearConstraintWeakSolutionSet a α eqIndices = solutionSet[eqIndices; a, α] := by
  classical
  ext x
  rw [mixedLinearConstraintWeakSolutionSet, mem_linearInequalitySolutionSet_range_iff,
    mem_feasibleSet]
  constructor
  · intro hx i
    by_cases hi : i ∈ eqIndices
    · have hle : a i x ≤ α i := by
        simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar] using
          hx (Sum.inl i)
      have hge : α i ≤ a i x := by
        have hneg :
            (mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)) x ≤
              mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) :=
          hx (Sum.inr i)
        simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi] using
          hneg
      have heq : a i x = α i := le_antisymm hle hge
      simpa [eqOn, hi] using heq
    · simpa [eqOn, hi, mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar] using
        hx (Sum.inl i)
  · intro hx j
    cases j with
    | inl i =>
        by_cases hi : i ∈ eqIndices
        · have heq : a i x = α i := by
            simpa [eqOn, hi] using hx i
          simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi] using
            heq.le
        · simpa [eqOn, hi, mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar] using
            hx i
    | inr i =>
        by_cases hi : i ∈ eqIndices
        · have heq : a i x = α i := by
            simpa [eqOn, hi] using hx i
          have hneg : ⟪x, (-a i : E →ₗ[ℝ] ℝ)⟫ₚ ≤ -α i := by
            change (-a i) x ≤ -α i
            simp [heq]
          simpa [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi] using
            hneg
        · have hzero :
            (mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)) x ≤
              mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
            simp [mixedLinearConstraintFarkasFunctional, mixedLinearConstraintFarkasScalar, hi]
          exact hzero

omit [FiniteDimensional ℝ E] in
private theorem exists_mixed_linear_constraint_farkas_certificate_iff
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    (∃ u : I ⊕ I → ℝ,
      (∀ j : I ⊕ I, 0 ≤ u j) ∧
        (∑ j : I ⊕ I, u j • mixedLinearConstraintFarkasFunctional a eqIndices j = 0) ∧
          (∑ j : I ⊕ I, u j * mixedLinearConstraintFarkasScalar α eqIndices j) < 0) ↔
      ∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0 := by
  classical
  constructor
  · rintro ⟨u, hu_nonneg, hu_vec, hu_scalar⟩
    let w : I → ℝ := fun i ↦ if hi : i ∈ eqIndices then u (Sum.inl i) - u (Sum.inr i) else u (Sum.inl i)
    refine ⟨w, ?_, ?_, ?_⟩
    · intro i hi
      simpa [w, hi] using hu_nonneg (Sum.inl i)
    · have hu_vec' :
        ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) =
          0 := by
        simpa [Fintype.sum_sum_type] using hu_vec
      calc
        ∑ i : I, w i • a i
            = ∑ i : I,
                (u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
                  u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    w i • a i = (u (Sum.inl i) - u (Sum.inr i)) • a i := by
                      simp [w, hi]
                    _ = u (Sum.inl i) • a i + u (Sum.inr i) • (-a i) := by
                          simp [sub_eq_add_neg, add_smul]
                    _ = u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
                          u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) := by
                          simp [mixedLinearConstraintFarkasFunctional, hi]
                · simp [w, mixedLinearConstraintFarkasFunctional, hi]
        _ = ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) := by
                rw [Finset.sum_add_distrib]
        _ = 0 := hu_vec'
    · have hu_scalar' :
        ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) <
          0 := by
        simpa [Fintype.sum_sum_type] using hu_scalar
      calc
        ∑ i : I, w i * α i
            = ∑ i : I,
                (u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
                  u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i)) := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    w i * α i = (u (Sum.inl i) - u (Sum.inr i)) * α i := by
                      simp [w, hi]
                    _ = u (Sum.inl i) * α i + u (Sum.inr i) * (-α i) := by
                          ring
                    _ = u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
                          u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
                          simp [mixedLinearConstraintFarkasScalar, hi]
                · simp [w, mixedLinearConstraintFarkasScalar, hi]
        _ = ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
                rw [Finset.sum_add_distrib]
        _ < 0 := hu_scalar'
  · rintro ⟨w, hw_nonneg, hw_vec, hw_scalar⟩
    let u : I ⊕ I → ℝ :=
      Sum.elim
        (fun i ↦ if hi : i ∈ eqIndices then max (w i) 0 else w i)
        (fun i ↦ if hi : i ∈ eqIndices then max (-w i) 0 else 0)
    refine ⟨u, ?_, ?_, ?_⟩
    · intro j
      cases j with
      | inl i =>
          by_cases hi : i ∈ eqIndices
          · simp [u, hi]
          · simp [u, hi, hw_nonneg i hi]
      | inr i =>
          by_cases hi : i ∈ eqIndices
          · simp [u, hi]
          · simp [u, hi]
    · have hsum :
        ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) =
          ∑ i : I, w i • a i := by
        calc
          ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i)
              = ∑ i : I, u (Sum.inl i) • a i +
                  ∑ i : I, u (Sum.inr i) • (if i ∈ eqIndices then -a i else 0) := by
                    simp [mixedLinearConstraintFarkasFunctional]
          _ = ∑ i : I, (u (Sum.inl i) • a i + u (Sum.inr i) • (if i ∈ eqIndices then -a i else 0)) := by
                rw [← Finset.sum_add_distrib]
          _ = ∑ i : I, w i • a i := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    u (Sum.inl i) • a i + u (Sum.inr i) • (if i ∈ eqIndices then -a i else 0)
                        = max (w i) 0 • a i + max (-w i) 0 • (-a i) := by
                            simp [u, hi]
                    _ = (max (w i) 0 - max (-w i) 0) • a i := by
                          simp [sub_eq_add_neg, add_smul]
                    _ = w i • a i := by rw [max_zero_sub_eq_self]
                · simp [u, hi]
      calc
        ∑ j : I ⊕ I, u j • mixedLinearConstraintFarkasFunctional a eqIndices j
            = ∑ i : I, u (Sum.inl i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inl i) +
                ∑ i : I, u (Sum.inr i) • mixedLinearConstraintFarkasFunctional a eqIndices (Sum.inr i) := by
                  rw [Fintype.sum_sum_type]
        _ = ∑ i : I, w i • a i := hsum
        _ = 0 := hw_vec
    · have hsum :
        ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
            ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) =
          ∑ i : I, w i * α i := by
        calc
          ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
              ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i)
              = ∑ i : I, u (Sum.inl i) * α i +
                  ∑ i : I, u (Sum.inr i) * (if i ∈ eqIndices then -α i else 0) := by
                    simp [mixedLinearConstraintFarkasScalar]
          _ = ∑ i : I, (u (Sum.inl i) * α i + u (Sum.inr i) * (if i ∈ eqIndices then -α i else 0)) := by
                rw [← Finset.sum_add_distrib]
          _ = ∑ i : I, w i * α i := by
                refine Finset.sum_congr rfl ?_
                intro i _
                by_cases hi : i ∈ eqIndices
                · calc
                    u (Sum.inl i) * α i + u (Sum.inr i) * (if i ∈ eqIndices then -α i else 0)
                        = max (w i) 0 * α i + max (-w i) 0 * (-α i) := by
                            simp [u, hi]
                    _ = (max (w i) 0 - max (-w i) 0) * α i := by
                          ring
                    _ = w i * α i := by rw [max_zero_sub_eq_self]
                · simp [u, hi]
      calc
        ∑ j : I ⊕ I, u j * mixedLinearConstraintFarkasScalar α eqIndices j
            = ∑ i : I, u (Sum.inl i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inl i) +
                ∑ i : I, u (Sum.inr i) * mixedLinearConstraintFarkasScalar α eqIndices (Sum.inr i) := by
                  rw [Fintype.sum_sum_type]
        _ = ∑ i : I, w i * α i := hsum
        _ < 0 := hw_scalar

-- Proof sketch: rewrite each equality constraint indexed by `eqIndices` as the pair of
-- inequalities `aᵢ x ≤ αᵢ` and `(-aᵢ) x ≤ -αᵢ`, apply Theorem 22.1 to that enlarged family, and
-- then combine the two nonnegative multipliers on each equality index into the signed coefficient
-- `λ i = μ⁺ i - μ⁻ i`.
/-- Text 22.3.5 on the functional-owner layer: for linear functionals `aᵢ`, scalars
`αᵢ`, and an equality-index set `eqIndices`, exactly one of the following holds: either the mixed
owner feasible set `feasibleSet (eqOn eqIndices) a α` is nonempty, or there is a multiplier
family `λ` with `λᵢ ≥ 0` on the inequality indices, `∑ i, λᵢ • aᵢ = 0`, and
`∑ i, λᵢ αᵢ < 0`. -/
theorem xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (solutionSet[eqIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  have hmain :
      Xor'
        (mixedLinearConstraintWeakSolutionSet a α eqIndices).Nonempty
        (∃ u : I ⊕ I → ℝ,
          (∀ j : I ⊕ I, 0 ≤ u j) ∧
            (∑ j : I ⊕ I, u j • mixedLinearConstraintFarkasFunctional a eqIndices j = 0) ∧
              (∑ j : I ⊕ I, u j * mixedLinearConstraintFarkasScalar α eqIndices j) < 0) :=
    xor_linearInequalitySolutionSet_nonempty_or_weak_linear_inequality_farkas_certificate
      (mixedLinearConstraintFarkasFunctional a eqIndices)
      (mixedLinearConstraintFarkasScalar α eqIndices)
  rcases hmain with h | h
  · left
    refine ⟨by
      simpa [weakSolutionSet_eq_mixed_linear_constraint_solutionSet a α eqIndices] using h.1, ?_⟩
    intro hw
    exact h.2 ((exists_mixed_linear_constraint_farkas_certificate_iff a α eqIndices).2 hw)
  · right
    refine ⟨(exists_mixed_linear_constraint_farkas_certificate_iff a α eqIndices).1 h.1, ?_⟩
    intro hs
    exact h.2 (by
      simpa [weakSolutionSet_eq_mixed_linear_constraint_solutionSet a α eqIndices] using hs)

/-- Companion pointwise form of Text 22.3.5 on the functional-owner layer. -/
theorem xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate
    (a : I → E →ₗ[ℝ] ℝ) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → ⟪x, a i⟫ₚ ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → ⟪x, a i⟫ₚ = α i)
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  simpa [mixed_linear_constraint_solution_set_nonempty_iff] using
    xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate
      a α eqIndices

end FunctionalOwner

section PairingFunctionalBridge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {Y : Type*} [AddCommMonoid Y] [Module ℝ Y] [HasLinearPairing E Y ℝ]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set E)

/-- Pairing-owner pointwise formulation of Text 22.3.5, obtained by transporting the
linear-functional mixed alternative through `HasLinearPairing.pairingLinear`. -/
theorem xor_exists_feasible_point_or_mixed_pairing_constraint_farkas_certificate
    (a : I → Y) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → (⟪x, a i⟫ₚ : ℝ) ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → (⟪x, a i⟫ₚ : ℝ) = α i)
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∀ x : E, ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  let aLin : I → E →ₗ[ℝ] ℝ :=
    fun i ↦ (HasLinearPairing.pairingLinear (𝕜 := ℝ) (X := E) (Y := Y)).flip (a i)
  have hmain :
      Xor'
        (∃ x : E,
          (∀ i : I, i ∉ eqIndices → ⟪x, aLin i⟫ₚ ≤ α i) ∧
            ∀ i : I, i ∈ eqIndices → ⟪x, aLin i⟫ₚ = α i)
        (∃ w : I → ℝ,
          (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
            (∑ i : I, w i • aLin i = 0) ∧
              (∑ i : I, w i * α i) < 0) :=
    xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate aLin α eqIndices
  have hsolution :
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → ⟪x, aLin i⟫ₚ ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → ⟪x, aLin i⟫ₚ = α i) ↔
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → (⟪x, a i⟫ₚ : ℝ) ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → (⟪x, a i⟫ₚ : ℝ) = α i) := by
    constructor
    · rintro ⟨x, hxle, hxeq⟩
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxle i hi
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxeq i hi
    · rintro ⟨x, hxle, hxeq⟩
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxle i hi
      · intro i hi
        simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear] using hxeq i hi
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • aLin i = 0) ∧
            (∑ i : I, w i * α i) < 0) ↔
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∀ x : E, ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, ?_, hw_scalar⟩
      intro x
      have hw_sum_x : (∑ i : I, w i • aLin i) x = 0 := by
        simpa using congrArg (fun b : E →ₗ[ℝ] ℝ ↦ b x) hw_sum
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
    · rintro ⟨w, hw_nonneg, hw_sum, hw_scalar⟩
      refine ⟨w, hw_nonneg, ?_, hw_scalar⟩
      ext x
      have hw_sum_x : ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0 := hw_sum x
      simpa [aLin, HasLinearPairing.pairing_eq_pairingLinear, smul_eq_mul] using hw_sum_x
  rcases hmain with h | h
  · left
    refine ⟨(hsolution.mp h.1), ?_⟩
    intro hw
    exact h.2 (hcertificate.mpr hw)
  · right
    refine ⟨(hcertificate.mp h.1), ?_⟩
    intro hs
    exact h.2 (hsolution.mpr hs)

/-- Pairing-owner feasible-set form of Text 22.3.5. -/
theorem xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_pairing_constraint_farkas_certificate
    (a : I → Y) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (solutionSet[eqIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∀ x : E, ∑ i : I, w i * (⟪x, a i⟫ₚ : ℝ) = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  simpa [mixed_linear_constraint_solution_set_nonempty_iff] using
    xor_exists_feasible_point_or_mixed_pairing_constraint_farkas_certificate a α eqIndices

end PairingFunctionalBridge

section InnerProductSpecialization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {I : Type*} [Fintype I]

local notation "solutionSet[" eqIndices "; " a ", " α "]" =>
  (feasibleSet (eqOn eqIndices) a α : Set E)

/-- Inner-product specialization of the source-facing mixed alternative, recovered from the
functional-owner theorem via the canonical Fréchet-Riesz bridge `InnerProductSpace.toDual`. -/
theorem xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate_innerProduct
    (a : I → E) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (∃ x : E,
        (∀ i : I, i ∉ eqIndices → ⟪a i, x⟫ ≤ α i) ∧
          ∀ i : I, i ∈ eqIndices → ⟪a i, x⟫ = α i)
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcertificate :
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • ((InnerProductSpace.toDual ℝ E) (a i)).toLinearMap = 0) ∧
            (∑ i : I, w i * α i) < 0) ↔
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
    constructor
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      have hw_sum_cont : ∑ i : I, w i • (InnerProductSpace.toDual ℝ E) (a i) = 0 := by
        ext x
        have hw_sum_x :
            (∑ i : I, w i • ((InnerProductSpace.toDual ℝ E) (a i)).toLinearMap) x = 0 := by
          simpa using congrArg (fun b : E →ₗ[ℝ] ℝ => b x) hw_sum
        simpa using hw_sum_x
      apply (InnerProductSpace.toDual ℝ E).injective
      simpa using hw_sum_cont
    · rintro ⟨w, hw_nonneg, hw_sum, hw_α⟩
      refine ⟨w, hw_nonneg, ?_, hw_α⟩
      have hw_sum_cont : ∑ i : I, w i • (InnerProductSpace.toDual ℝ E) (a i) = 0 := by
        simpa using congrArg (InnerProductSpace.toDual ℝ E) hw_sum
      ext x
      have hw_sum_cont_x :
          (∑ i : I, w i • (InnerProductSpace.toDual ℝ E) (a i)) x = 0 := by
        simpa using congrArg (fun b : E →L[ℝ] ℝ => b x) hw_sum_cont
      simpa using hw_sum_cont_x
  simpa [InnerProductSpace.toDual_apply_apply, Xor', hcertificate] using
    (xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate
      (fun i ↦ ((InnerProductSpace.toDual ℝ E) (a i)).toLinearMap) α eqIndices)

/-- Inner-product owner-form specialization of Text 22.3.5, obtained from the functional-owner
theorem through `InnerProductSpace.toDual`. -/
theorem xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate_innerProduct
    (a : I → E) (α : I → ℝ) (eqIndices : Set I) :
    Xor'
      (solutionSet[eqIndices; a, α]).Nonempty
      (∃ w : I → ℝ,
        (∀ i : I, i ∉ eqIndices → 0 ≤ w i) ∧
          (∑ i : I, w i • a i = 0) ∧
            (∑ i : I, w i * α i) < 0) := by
  simpa [mixed_linear_constraint_solution_set_nonempty_iff, real_inner_comm] using
    xor_exists_feasible_point_or_mixed_linear_constraint_farkas_certificate_innerProduct
      a α eqIndices

end InnerProductSpecialization

/-! ### Text_22_3_6 (from Chap04) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 22.3.6 is the weak-inequality Farkas alternative.
- `core/canonical`: the project owner is
  `xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate`, stated on finite
  families of pairing-side coefficients.
- `bridge/view`: functional and concrete matrix-coordinate formulations are downstream
  specializations and should not be the primary public owner surface in this source-item file.

Layer target: canonical owner recall.
-/

/- Text 22.3.6 is recorded at the canonical pairing owner layer. Functional and
matrix-coordinate spellings are downstream bridge views of this theorem. -/
recall xor_exists_feasible_point_or_weak_pairing_inequality_farkas_certificate

/-! ### Text_22_3_8 (from Chap04) -/
open scoped BigOperators Matrix RealInnerProductSpace
open LinearConstraintRelation

noncomputable section

section

variable {m n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Rm" => Fin m → ℝ
local notation "Rn" => Fin n → ℝ
set_option linter.style.longLine false in
local notation "xorMixedAlternative" =>
  xor_mixed_linear_constraint_solution_set_nonempty_or_mixed_linear_constraint_farkas_certificate_innerProduct

/-!
Source/core/bridge triage for this item.

- `core/canonical`: the owner abstractions are the mixed-constraint solution-set API
  `LinearConstraintRelation.feasibleSet`, the relation owner
  `LinearConstraintRelation.eqOn`, and the mixed equality/inequality alternative,
  here used through the inner-product bridge theorem from `Text_22_3_5`.
- `bridge/view`: this file is the matrix specialization of that owner theorem, obtained by encoding
  the constraints `x_j ≥ 0` as the weak inequalities `⟪-e_j, x⟫ ≤ 0` and the equations
  `Ax = a` as row equalities. The bridge uses the disjoint-union index `Fin n ⊕ Fin m`, so the
  nonnegativity and equality blocks remain separate without arithmetic index bookkeeping.

Domain-style sampling used here:
- `LinearConstraintRelation.feasibleSet`;
- `mixed_linear_constraint_solution_set_nonempty_iff`;
- the inner-product mixed-alternative theorem from `Text_22_3_5`;
- `row_inner_eq_mulVec` and `rowCombination_toLp_eq_mulVec_transpose`.

Primitive data vs derived API:
- primitive inputs: a real matrix `A : ℝ^{m×n}` and a right-hand side vector `a : ℝ^m`;
- derived API: the exclusive alternative between solvability of the nonnegative equality system
  and solvability of the transposed strict-separation certificate. No separate public primal or
  dual wrapper predicates are introduced.

Layer target: `bridge/view`, since the source statement is a direct matrix
reformulation of the chapter owner theorem for mixed weak inequalities and
equalities.
-/

private def constraintVec
    (A : Matrix (Fin m) (Fin n) ℝ) : Fin n ⊕ Fin m → E :=
  Sum.elim
    (fun j : Fin n ↦ EuclideanSpace.single j (-1 : ℝ))
    (fun i : Fin m ↦ WithLp.toLp 2 (A i))

private def constraintScalar (a : Rm) : Fin n ⊕ Fin m → ℝ :=
  Sum.elim (fun _ : Fin n ↦ (0 : ℝ)) a

private def eqIndices : Set (Fin n ⊕ Fin m) :=
  Set.range Sum.inr

private theorem inl_not_mem_eqIndices (j : Fin n) :
    Sum.inl j ∉ (eqIndices : Set (Fin n ⊕ Fin m)) := by
  rintro ⟨i, hi⟩
  cases hi

private theorem inr_mem_eqIndices (i : Fin m) :
    Sum.inr i ∈ (eqIndices : Set (Fin n ⊕ Fin m)) :=
  ⟨i, rfl⟩

private theorem inner_negSingle_eq_neg_coord (j : Fin n) (x : E) :
    ⟪EuclideanSpace.single j (-1 : ℝ), x⟫ = -x j := by
  simpa using EuclideanSpace.inner_single_left j (-1 : ℝ) x

private theorem sum_negSingle_eq (v : Rn) :
    (∑ j : Fin n, (-v j) • EuclideanSpace.single j (-1 : ℝ) : E) = WithLp.toLp 2 v := by
  ext j
  simp [EuclideanSpace.single, Pi.single_apply]

private theorem inner_negSingle_toLp_eq_neg_coord (j : Fin n) (x : Rn) :
    ⟪EuclideanSpace.single j (-1 : ℝ), WithLp.toLp 2 x⟫ = -x j := by
  simpa using inner_negSingle_eq_neg_coord j (WithLp.toLp 2 x)

private theorem row_inner_eq_mulVec
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (x : E) :
    ⟪WithLp.toLp 2 (A i), x⟫ = (A *ᵥ x) i := by
  have hdot : ⟪WithLp.toLp 2 (A i), x⟫ = A i ⬝ᵥ x := by
    simpa [dotProduct, mul_comm] using
      EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 (A i)) x
  simpa [Matrix.mulVec] using hdot

private theorem row_inner_toLp_eq_mulVec
    (A : Matrix (Fin m) (Fin n) ℝ) (i : Fin m) (x : Rn) :
    ⟪WithLp.toLp 2 (A i), WithLp.toLp 2 x⟫ = (A *ᵥ x) i := by
  simpa using row_inner_eq_mulVec A i (WithLp.toLp 2 x)

private theorem rowCombination_eq_mulVec_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Rm) :
    (∑ i : Fin m, w i • A i : Rn) = Aᵀ *ᵥ w := by
  simpa [Matrix.mulVec_transpose] using (Matrix.vecMul_eq_sum w A).symm

private theorem rowCombination_toLp_eq_mulVec_transpose
    (A : Matrix (Fin m) (Fin n) ℝ) (w : Rm) :
    (∑ i : Fin m, w i • WithLp.toLp 2 (A i) : E) = WithLp.toLp 2 (Aᵀ *ᵥ w) := by
  simpa using congrArg (WithLp.toLp 2) (rowCombination_eq_mulVec_transpose A w)

local notation "solutionSet[" A "; " a "]" =>
  (feasibleSet (eqOn eqIndices) (constraintVec A) (constraintScalar a) : Set E)

/-- Primal owner for Text 22.3.8: nonnegative vectors solving `A *ᵥ x = a`. -/
def nonnegativeEqualityPrimal
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) : Set Rn :=
  {x | 0 ≤ x ∧ A *ᵥ x = a}

/-- Dual owner for Text 22.3.8: transpose certificates with nonpositive `Aᵀ *ᵥ w`
and positive pairing `a ⬝ᵥ w`. -/
def nonpositiveDualCertificate
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) : Set Rm :=
  {w | Aᵀ *ᵥ w ≤ 0 ∧ 0 < a ⬝ᵥ w}

private theorem nonnegative_equality_solutionSet_nonempty_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) :
    (solutionSet[A; a]).Nonempty ↔
      (nonnegativeEqualityPrimal A a).Nonempty := by
  rw [mixed_linear_constraint_solution_set_nonempty_iff]
  constructor
  · rintro ⟨x, hxle, hxeq⟩
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj :
          ⟪constraintVec A (Sum.inl j : Fin n ⊕ Fin m), x⟫ ≤
            constraintScalar a (Sum.inl j : Fin n ⊕ Fin m) :=
        by
          simpa [real_inner_comm] using
            hxle (Sum.inl j : Fin n ⊕ Fin m) (inl_not_mem_eqIndices j)
      have hj0 : -x j ≤ 0 := by
        simpa [constraintVec, constraintScalar, inner_negSingle_eq_neg_coord] using hj
      exact neg_nonpos.mp hj0
    · ext i
      have hi :
          ⟪constraintVec A (Sum.inr i : Fin n ⊕ Fin m), x⟫ =
            constraintScalar a (Sum.inr i : Fin n ⊕ Fin m) :=
        by
          simpa [real_inner_comm] using
            hxeq (Sum.inr i : Fin n ⊕ Fin m) (inr_mem_eqIndices i)
      simpa [constraintVec, constraintScalar, row_inner_eq_mulVec A i x] using hi
  · rintro ⟨x, hx_nonneg, hx_eq⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · intro i hi
      cases i with
      | inl j =>
          have hj0 : -x j ≤ 0 := neg_nonpos.mpr (hx_nonneg j)
          change ⟪WithLp.toLp 2 x, EuclideanSpace.single j (-1 : ℝ)⟫ ≤ (0 : ℝ)
          rw [real_inner_comm, inner_negSingle_toLp_eq_neg_coord]
          exact hj0
      | inr i =>
          exfalso
          exact hi (inr_mem_eqIndices i)
    · intro i hi
      cases i with
      | inl j =>
          exfalso
          exact inl_not_mem_eqIndices j hi
      | inr i =>
          simpa [real_inner_comm, constraintVec, constraintScalar,
            row_inner_toLp_eq_mulVec A i x] using
            congrFun hx_eq i

private theorem nonnegative_equality_certificate_iff
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) :
    (∃ u : Fin n ⊕ Fin m → ℝ,
      (∀ i : Fin n ⊕ Fin m, i ∉ eqIndices → 0 ≤ u i) ∧
        (∑ i : Fin n ⊕ Fin m, u i • constraintVec A i = 0) ∧
          (∑ i : Fin n ⊕ Fin m, u i * constraintScalar a i) < 0) ↔
      (nonpositiveDualCertificate A a).Nonempty := by
  constructor
  · rintro ⟨u, hu_nonneg, hu_sum, hu_scalar⟩
    let w : Rm := fun i ↦ -u (Sum.inr i)
    refine ⟨w, ?_, ?_⟩
    · intro j
      have hcoord :
          -u (Sum.inl j) + ∑ i : Fin m, A i j * u (Sum.inr i) = 0 := by
        have hsingle :
            ∑ x : Fin n, u (Sum.inl x) * ((Pi.single x (-1 : ℝ) : Fin n → ℝ) j) =
              -u (Sum.inl j) := by
          simp [Pi.single_apply]
        have h := congrArg (fun v : E ↦ v j) hu_sum
        simpa [constraintVec, Fintype.sum_sum_type, hsingle, mul_comm] using h
      have huj : 0 ≤ u (Sum.inl j) :=
        hu_nonneg (Sum.inl j) (inl_not_mem_eqIndices j)
      have hmulVec : (Aᵀ *ᵥ w) j = -u (Sum.inl j) := by
        have hcoord' : ∑ i : Fin m, A i j * u (Sum.inr i) = u (Sum.inl j) := by
          linarith
        calc
          (Aᵀ *ᵥ w) j = ∑ i : Fin m, A i j * (-u (Sum.inr i)) := by
            simp [Matrix.mulVec, dotProduct, w]
          _ = -∑ i : Fin m, A i j * u (Sum.inr i) := by
              simp_rw [mul_neg]
              rw [Finset.sum_neg_distrib]
          _ = -u (Sum.inl j) := by rw [hcoord']
      simpa [hmulVec] using neg_nonpos.mpr huj
    · simpa [w, constraintScalar, Fintype.sum_sum_type, dotProduct, mul_comm] using
        (neg_pos.mpr hu_scalar)
  · rintro ⟨w, hw_nonpos, hw_scalar⟩
    let u : Fin n ⊕ Fin m → ℝ :=
      Sum.elim (fun j : Fin n ↦ -(Aᵀ *ᵥ w) j) (fun i : Fin m ↦ -w i)
    refine ⟨u, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | inl j =>
          simpa [u] using neg_nonneg.mpr (hw_nonpos j)
      | inr i =>
          exfalso
          exact hi (inr_mem_eqIndices i)
    · calc
        ∑ i : Fin n ⊕ Fin m, u i • constraintVec A i
            = ∑ j : Fin n, (-(Aᵀ *ᵥ w) j) • EuclideanSpace.single j (-1 : ℝ) +
                ∑ i : Fin m, (-w i) • WithLp.toLp 2 (A i) := by
                  simp [u, constraintVec, Fintype.sum_sum_type]
        _ = WithLp.toLp 2 (Aᵀ *ᵥ w) - ∑ i : Fin m, w i • WithLp.toLp 2 (A i) := by
              rw [sum_negSingle_eq]
              simp_rw [neg_smul]
              rw [Finset.sum_neg_distrib]
              simp [sub_eq_add_neg]
        _ = 0 := by
              rw [rowCombination_toLp_eq_mulVec_transpose A w]
              simp
    · simpa [u, constraintScalar, Fintype.sum_sum_type, dotProduct, mul_comm] using
        (neg_neg_iff_pos.mpr hw_scalar)

-- Proof sketch: encode `x_j ≥ 0` as `⟪-e_j, x⟫ ≤ 0` on the `Fin n` summand and `Ax = a`
-- as equality constraints on the `Fin m` summand. Apply the mixed equality/inequality
-- alternative from `Text_22_3_5`. In the multiplier alternative, the first-block coefficients are
-- exactly `-(Aᵀ *ᵥ w)`, so the nonnegativity condition on those coefficients
-- is equivalent to `Aᵀ *ᵥ w ≤ 0`; the scalar inequality becomes
-- `0 < a ⬝ᵥ w` after negating the equality-block multipliers.
/-- Text 22.3.8: for a real matrix `A` and vector `a`, exactly one of the systems
`x ≥ 0`, `Ax = a` and `Aᵀ w ≤ 0`, `⟪a, w⟫ > 0` has a solution. -/
theorem xor_nonnegative_equality_primal_solution_or_dual_nonpositive_certificate
    (A : Matrix (Fin m) (Fin n) ℝ) (a : Rm) :
    Xor'
      (nonnegativeEqualityPrimal A a).Nonempty
      (nonpositiveDualCertificate A a).Nonempty := by
  rcases
    xorMixedAlternative (constraintVec A)
      (constraintScalar a)
      eqIndices with h | h
  · left
    exact ⟨(nonnegative_equality_solutionSet_nonempty_iff A a).mp h.1, fun hw ↦
      h.2 ((nonnegative_equality_certificate_iff A a).mpr hw)⟩
  · right
    exact ⟨(nonnegative_equality_certificate_iff A a).mp h.1, fun hx ↦
      h.2 ((nonnegative_equality_solutionSet_nonempty_iff A a).mpr hx)⟩
end

/-! ### Text_22_3_9 (from Chap04) -/
/- Text 22.3.9 is split across the following source-facing components:
- `Text_22_3_9_1`: the owner abstraction `GeneralPrimalSystem` with intrinsic relation owner
  `GeneralPrimalSystem.relation`;
- `Text_22_3_9_2`: the specialization constructor `GeneralPrimalSystem.ofLe` encoding `Ax ≤ a`;
- `Text_22_3_9_3`: the specialization constructor `GeneralPrimalSystem.ofNonnegativeEq`
  encoding `x ≥ 0`, `Ax = a`.
-/
