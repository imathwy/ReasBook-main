import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Theorem_17_2_11

-- Declarations for this item will be appended below by the statement pipeline.

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
