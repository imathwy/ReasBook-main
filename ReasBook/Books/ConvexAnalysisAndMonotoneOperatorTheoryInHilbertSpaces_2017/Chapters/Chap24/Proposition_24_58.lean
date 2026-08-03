import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.InnerProductSpace.PiL2
import BauschkeLean.Chap02.Fact_2_18
import BauschkeLean.Chap13.Proposition_13_23
import BauschkeLean.Chap17.Proposition_17_45
import BauschkeLean.Chap18.Theorem_18_3
import BauschkeLean.Chap24.CoordinatePermutationInvariant

open scoped Gradient InnerProductSpace Pointwise

/-- The Chapter 2 nonincreasing rearrangement transported to `EuclideanSpace ℝ (Fin N)`. -/
noncomputable abbrev euclideanNonincreasingRearrangement {N : ℕ}
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm <|
    nonincreasingRearrangement ((EuclideanSpace.equiv (Fin N) ℝ) x)

scoped[EuclideanRearrangement] postfix:max "↓" => euclideanNonincreasingRearrangement

/-- `euclideanNonincreasingRearrangement` is coordinatewise the Chapter 2 sorted rearrangement. -/
theorem euclideanNonincreasingRearrangement_eq
    {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    (euclideanNonincreasingRearrangement x : Fin N → ℝ) =
      nonincreasingRearrangement ((EuclideanSpace.equiv (Fin N) ℝ) x) := by
  -- This is just the defining coordinate description of the transported rearrangement.
  rfl

/-- Helper: coordinate permutations act by continuous linear equivalences on
the canonical Euclidean model. -/
noncomputable abbrev coordinatePermutationContinuousLinearEquiv {N : ℕ}
    (σ : Equiv.Perm (Fin N)) :
    EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).toContinuousLinearEquiv

/-- Helper: the permutation equivalence acts on vectors exactly by
reindexing their coordinates. -/
@[simp] theorem coordinatePermutationContinuousLinearEquiv_apply
    {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    coordinatePermutationContinuousLinearEquiv σ x = permuteCoordVec σ x := by
  -- Both sides are the same transported coordinate reindexing map.
  ext i
  rfl

/-- Helper: the inverse permutation equivalence acts by the inverse
coordinate permutation. -/
@[simp] theorem coordinatePermutationContinuousLinearEquiv_symm_apply
    {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    (coordinatePermutationContinuousLinearEquiv σ).symm x = permuteCoordVec σ.symm x := by
  -- Inverting the transported permutation just inverts the coordinate permutation.
  ext i
  simp [coordinatePermutationContinuousLinearEquiv, permuteCoordVec]

/-- Helper: taking the inverse of the permutation equivalence corresponds to inverting the
underlying permutation. -/
@[simp] theorem coordinatePermutationContinuousLinearEquiv_symm
    {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (coordinatePermutationContinuousLinearEquiv σ).symm =
      coordinatePermutationContinuousLinearEquiv σ.symm := by
  ext x i
  simp

/-- Helper: coordinate permutations preserve the Euclidean inner product. -/
theorem coordinatePermutationContinuousLinearEquiv_inner
    {N : ℕ} (σ : Equiv.Perm (Fin N))
    (x y : EuclideanSpace ℝ (Fin N)) :
    ⟪coordinatePermutationContinuousLinearEquiv σ x,
      coordinatePermutationContinuousLinearEquiv σ y⟫_ℝ = ⟪x, y⟫_ℝ := by
  -- After rewriting into coordinates, the permutation just reindexes the finite sum.
  convert (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).inner_map_map x y using 1

/-- Helper: the adjoint of the inverse permutation operator is the same
permutation operator. -/
theorem coordinatePermutationContinuousLinearEquiv_symm_adjoint
    {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (((coordinatePermutationContinuousLinearEquiv σ).symm :
        EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).adjoint) =
      coordinatePermutationContinuousLinearEquiv σ := by
  -- An orthogonal coordinate permutation has adjoint equal to its inverse, hence here to `σ`.
  convert LinearIsometryEquiv.adjoint_eq_symm
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).symm) using 1

/-- The adjoint of a coordinate permutation is its inverse coordinate permutation. -/
theorem coordinatePermutationContinuousLinearEquiv_adjoint
    {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ((((coordinatePermutationContinuousLinearEquiv σ :
        EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) :
          EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).adjoint)) =
      coordinatePermutationContinuousLinearEquiv σ.symm := by
  -- Rewriting the inverse-permutation adjoint formula at `σ.symm` gives the desired adjoint rule.
  calc
    ((((coordinatePermutationContinuousLinearEquiv σ :
        EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) :
          EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).adjoint)) =
        (((coordinatePermutationContinuousLinearEquiv σ.symm).symm :
            EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).adjoint) := by
          simp
    _ = coordinatePermutationContinuousLinearEquiv σ.symm :=
      coordinatePermutationContinuousLinearEquiv_symm_adjoint σ.symm

/-- Helper: every vector can be sent to its nonincreasing rearrangement by a
single coordinate permutation. -/
theorem exists_permuteCoordVec_eq_nonincreasingRearrangement
    {N : ℕ} (x : EuclideanSpace ℝ (Fin N)) :
    ∃ σ : Equiv.Perm (Fin N),
      permuteCoordVec σ x = euclideanNonincreasingRearrangement x := by
  -- Choose the sorting permutation from the Chapter 2 rearrangement owner.
  refine ⟨(Tuple.sort (OrderDual.toDual ∘ ((EuclideanSpace.equiv (Fin N) ℝ) x))).symm, ?_⟩
  ext i
  simp [permuteCoordVec, euclideanNonincreasingRearrangement, nonincreasingRearrangement]

/-- Helper: the Euclidean inner product is the coordinate dot product. -/
theorem euclidean_inner_eq_dotProduct
    {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) :
    ⟪x, y⟫_ℝ =
      dotProduct ((EuclideanSpace.equiv (Fin N) ℝ) x)
        ((EuclideanSpace.equiv (Fin N) ℝ) y) := by
  -- The canonical Euclidean model already identifies its inner product with the coordinate
  -- `dotProduct`.
  simpa [EuclideanSpace.equiv, dotProduct_comm] using EuclideanSpace.inner_eq_star_dotProduct x y

/-- Helper: sorting both vectors cannot decrease their Euclidean inner
product. -/
theorem inner_le_inner_nonincreasingRearrangement
    {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) :
    ⟪x, y⟫_ℝ ≤
      ⟪euclideanNonincreasingRearrangement x,
        euclideanNonincreasingRearrangement y⟫_ℝ := by
  let xCoords : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) x
  let yCoords : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) y
  -- This is exactly Fact 2.18 after transporting the Euclidean model to coordinates.
  rw [euclidean_inner_eq_dotProduct, euclidean_inner_eq_dotProduct]
  simpa [euclideanNonincreasingRearrangement_eq] using
    (hardy_littlewood_polya_inequality :
      dotProduct xCoords yCoords ≤
        dotProduct (nonincreasingRearrangement xCoords)
          (nonincreasingRearrangement yCoords))

/-- Helper: a coordinate-permutation invariant function has the same value at
`x` and at its nonincreasing rearrangement. -/
theorem CoordinatePermutationInvariant.eq_nonincreasingRearrangement
    {N : ℕ} {α : Type*} {φ : EuclideanSpace ℝ (Fin N) → α}
    (hφ : CoordinatePermutationInvariant φ) (x : EuclideanSpace ℝ (Fin N)) :
    φ (euclideanNonincreasingRearrangement x) = φ x := by
  -- Apply the symmetry hypothesis to a permutation that sorts `x`.
  obtain ⟨σ, hσ⟩ := exists_permuteCoordVec_eq_nonincreasingRearrangement x
  rw [← hσ]
  exact hφ σ x

namespace ERealFunction

section SymmetricFiniteFunctions

variable {N : ℕ}
variable {φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal)}

-- Semantic recall: `lean_leansearch` only surfaced generic permutation and calculus lemmas, so
-- this item uses the local Chapter 2 rearrangement owner `nonincreasingRearrangement`, the
-- Chapter 16 subdifferential owner `∂`, and the Chapter 17 gradient owner `∇` through the
-- canonical Euclidean model `EuclideanSpace ℝ (Fin N)`.

/-- Companion to clause `(i)`: if `φ` is symmetric, then its Fenchel conjugate `φ.asEReal∗` is
symmetric as well. -/
theorem conjugate_coordinatePermutationInvariant
    (hφsymm : CoordinatePermutationInvariant φ) :
    CoordinatePermutationInvariant (φ.asEReal∗) := by
  intro σ x
  -- Transport the conjugate through the permutation equivalence used in the source proof.
  have hcomp :
      φ.asEReal ∘ coordinatePermutationContinuousLinearEquiv σ = φ.asEReal := by
    funext z
    simpa [Function.comp, coordinatePermutationContinuousLinearEquiv_apply] using
      congrArg (fun t : Set.Ioi (⊥ : EReal) ↦ (t : EReal)) (hφsymm σ z)
  have hcomp_star :
      (φ.asEReal ∘ coordinatePermutationContinuousLinearEquiv σ)∗ = φ.asEReal∗ := by
    exact congrArg (fun g : EuclideanSpace ℝ (Fin N) → EReal ↦ g∗) hcomp
  have hstar :
      φ.asEReal∗ =
        φ.asEReal∗ ∘ (((coordinatePermutationContinuousLinearEquiv σ).symm :
          EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).adjoint) := by
    calc
      φ.asEReal∗ = (φ.asEReal ∘ coordinatePermutationContinuousLinearEquiv σ)∗ := by
        simpa using hcomp_star.symm
      _ = φ.asEReal∗ ∘ (((coordinatePermutationContinuousLinearEquiv σ).symm :
          EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)).adjoint) := by
            exact
              conjugate_comp_continuousLinearEquiv φ.asEReal
                (coordinatePermutationContinuousLinearEquiv σ)
  -- The adjoint of the inverse permutation is the forward permutation itself.
  simpa [Function.comp, coordinatePermutationContinuousLinearEquiv_symm_adjoint,
    coordinatePermutationContinuousLinearEquiv_apply] using (congrFun hstar x).symm

/-- Clause `(ii)` companion: a subgradient contact pair remains in Fenchel--Young contact
after sorting both vectors, and the rearrangement inequality is saturated. -/
theorem sorted_fenchel_young_contact_and_inner_eq_of_mem_subdifferential
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    {x y : EuclideanSpace ℝ (Fin N)} (hy : y ∈ (∂ φ) x) :
    (φ (euclideanNonincreasingRearrangement x) : EReal) +
        φ.asEReal∗ (euclideanNonincreasingRearrangement y) =
      ((⟪euclideanNonincreasingRearrangement x,
          euclideanNonincreasingRearrangement y⟫_ℝ : ℝ) : EReal) ∧
      ⟪x, y⟫_ℝ =
        ⟪euclideanNonincreasingRearrangement x,
          euclideanNonincreasingRearrangement y⟫_ℝ := by
  let xs := euclideanNonincreasingRearrangement x
  let ys := euclideanNonincreasingRearrangement y
  have hproper_asEReal : IsProper φ.asEReal := by
    refine ⟨fun z ↦ ne_of_gt (φ z).2, ?_⟩
    simpa [effectiveDomain, dom] using hproper
  have hφstarSymm : CoordinatePermutationInvariant (φ.asEReal∗) :=
    conjugate_coordinatePermutationInvariant hφsymm
  have hcontact :
      (φ xs : EReal) + φ.asEReal∗ ys = ((⟪x, y⟫_ℝ : ℝ) : EReal) := by
    -- Rewrite the Fenchel--Young contact at `(x,y)` through symmetry of `φ` and `φ*`.
    calc
      (φ xs : EReal) + φ.asEReal∗ ys = (φ x : EReal) + φ.asEReal∗ y := by
        rw [CoordinatePermutationInvariant.eq_nonincreasingRearrangement hφsymm x,
          CoordinatePermutationInvariant.eq_nonincreasingRearrangement hφstarSymm y]
      _ = ((⟪x, y⟫_ℝ : ℝ) : EReal) :=
        (mem_subdifferential_iff_fenchel_young_eq φ hproper x y).1 hy
  have hinner_le :
      ((⟪x, y⟫_ℝ : ℝ) : EReal) ≤ ((⟪xs, ys⟫_ℝ : ℝ) : EReal) := by
    exact EReal.coe_le_coe_iff.mpr (inner_le_inner_nonincreasingRearrangement x y)
  have hfy_sorted :
      ((⟪xs, ys⟫_ℝ : ℝ) : EReal) ≤ (φ xs : EReal) + φ.asEReal∗ ys := by
    -- Fenchel--Young gives the reverse inequality at the sorted pair.
    simpa [xs, ys] using fenchel_young_inequality hproper_asEReal xs ys
  have hcontact_sorted :
      (φ xs : EReal) + φ.asEReal∗ ys = ((⟪xs, ys⟫_ℝ : ℝ) : EReal) := by
    -- The rearrangement inequality is squeezed between the two Fenchel--Young bounds.
    apply le_antisymm
    · calc
        (φ xs : EReal) + φ.asEReal∗ ys = ((⟪x, y⟫_ℝ : ℝ) : EReal) := hcontact
        _ ≤ ((⟪xs, ys⟫_ℝ : ℝ) : EReal) := hinner_le
    · exact hfy_sorted
  have hinner_eq :
      ⟪x, y⟫_ℝ = ⟪xs, ys⟫_ℝ := by
    -- Once both `EReal` inequalities are equalities, the original real pairings coincide.
    apply EReal.coe_eq_coe_iff.mp
    calc
      ((⟪x, y⟫_ℝ : ℝ) : EReal) = (φ xs : EReal) + φ.asEReal∗ ys := by
        exact hcontact.symm
      _ = ((⟪xs, ys⟫_ℝ : ℝ) : EReal) := hcontact_sorted
  exact ⟨hcontact_sorted, hinner_eq⟩

/-- Companion to clause `(ii)`: sorted
subgradients are characterized by sorted subdifferential membership together with preservation of
the inner product under nonincreasing rearrangement. -/
theorem mem_subdifferential_iff_mem_subdifferential_nonincreasingRearrangement_and_inner_eq
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    {x y : EuclideanSpace ℝ (Fin N)} :
    y ∈ (∂ φ) x ↔
      euclideanNonincreasingRearrangement y ∈
          (∂ φ) (euclideanNonincreasingRearrangement x) ∧
        ⟪x, y⟫_ℝ =
          ⟪euclideanNonincreasingRearrangement x,
            euclideanNonincreasingRearrangement y⟫_ℝ := by
  have hφstarSymm : CoordinatePermutationInvariant (φ.asEReal∗) :=
    conjugate_coordinatePermutationInvariant hφsymm
  constructor
  · intro hy
    rcases
        sorted_fenchel_young_contact_and_inner_eq_of_mem_subdifferential
          hproper hφsymm hy
      with ⟨hcontact_sorted, hinner_eq⟩
    -- Convert the sorted Fenchel--Young contact back to sorted subdifferential membership.
    refine ⟨?_, hinner_eq⟩
    exact
      (mem_subdifferential_iff_fenchel_young_eq φ hproper
        (euclideanNonincreasingRearrangement x)
        (euclideanNonincreasingRearrangement y)).2 hcontact_sorted
  · rintro ⟨hy_sorted, hinner_eq⟩
    have hcontact_sorted :
        (φ (euclideanNonincreasingRearrangement x) : EReal) +
            φ.asEReal∗ (euclideanNonincreasingRearrangement y) =
          ((⟪euclideanNonincreasingRearrangement x,
              euclideanNonincreasingRearrangement y⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq φ hproper
        (euclideanNonincreasingRearrangement x)
        (euclideanNonincreasingRearrangement y)).1 hy_sorted
    have hcontact :
        (φ x : EReal) + φ.asEReal∗ y = ((⟪x, y⟫_ℝ : ℝ) : EReal) := by
      -- Rewrite the sorted contact equality back to the original pair using symmetry.
      calc
        (φ x : EReal) + φ.asEReal∗ y =
            (φ (euclideanNonincreasingRearrangement x) : EReal) +
              φ.asEReal∗ (euclideanNonincreasingRearrangement y) := by
                rw [CoordinatePermutationInvariant.eq_nonincreasingRearrangement hφsymm x,
                  CoordinatePermutationInvariant.eq_nonincreasingRearrangement hφstarSymm y]
        _ = ((⟪euclideanNonincreasingRearrangement x,
                euclideanNonincreasingRearrangement y⟫_ℝ : ℝ) : EReal) :=
            hcontact_sorted
        _ = ((⟪x, y⟫_ℝ : ℝ) : EReal) := by
            exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner_eq.symm
    exact (mem_subdifferential_iff_fenchel_young_eq φ hproper x y).2 hcontact

/-- Clause `(ii)` helper: the sorted
inner-product equality with the existence of one coordinate permutation sending both `x` and `y`
to their nonincreasing rearrangements. -/
theorem inner_eq_sorted_inner_iff_exists_perm
    {x y : EuclideanSpace ℝ (Fin N)} :
    ⟪x, y⟫_ℝ =
        ⟪euclideanNonincreasingRearrangement x,
          euclideanNonincreasingRearrangement y⟫_ℝ ↔
      ∃ σ : Equiv.Perm (Fin N),
        permuteCoordVec σ x = euclideanNonincreasingRearrangement x ∧
          permuteCoordVec σ y = euclideanNonincreasingRearrangement y := by
  let xCoords : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) x
  let yCoords : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) y
  have hEqIff :
      dotProduct xCoords yCoords =
          dotProduct (nonincreasingRearrangement xCoords)
            (nonincreasingRearrangement yCoords) ↔
        ∃ σ : Equiv.Perm (Fin N),
          nonincreasingRearrangement xCoords = xCoords ∘ σ ∧
            nonincreasingRearrangement yCoords = yCoords ∘ σ :=
    hardy_littlewood_polya_inequality_eq_iff
  -- Rewrite the Euclidean statement into the Chapter 2 coordinate statement.
  rw [euclidean_inner_eq_dotProduct, euclidean_inner_eq_dotProduct]
  constructor
  · intro hEq
    have hEqCoords :
        dotProduct xCoords yCoords =
          dotProduct (nonincreasingRearrangement xCoords)
            (nonincreasingRearrangement yCoords) := by
      simpa [xCoords, yCoords, euclideanNonincreasingRearrangement_eq] using hEq
    rcases hEqIff.1 hEqCoords with ⟨τ, hxτ, hyτ⟩
    refine ⟨τ.symm, ?_, ?_⟩
    · -- Convert the common sorting permutation from coordinates back to Euclidean vectors.
      apply (EuclideanSpace.equiv (Fin N) ℝ).injective
      simpa [xCoords, euclideanNonincreasingRearrangement, permuteCoordVec,
        nonincreasingRearrangement] using hxτ.symm
    · -- The same permutation sorts `y`.
      apply (EuclideanSpace.equiv (Fin N) ℝ).injective
      simpa [yCoords, euclideanNonincreasingRearrangement, permuteCoordVec,
        nonincreasingRearrangement] using hyτ.symm
  · rintro ⟨σ, hxσ, hyσ⟩
    have hxσCoords :
        nonincreasingRearrangement xCoords = xCoords ∘ σ.symm := by
      have hxσ' := congrArg (EuclideanSpace.equiv (Fin N) ℝ) hxσ
      simpa [xCoords, euclideanNonincreasingRearrangement, permuteCoordVec,
        nonincreasingRearrangement] using hxσ'.symm
    have hyσCoords :
        nonincreasingRearrangement yCoords = yCoords ∘ σ.symm := by
      have hyσ' := congrArg (EuclideanSpace.equiv (Fin N) ℝ) hyσ
      simpa [yCoords, euclideanNonincreasingRearrangement, permuteCoordVec,
        nonincreasingRearrangement] using hyσ'.symm
    have hEqCoords :
        dotProduct xCoords yCoords =
          dotProduct (nonincreasingRearrangement xCoords)
            (nonincreasingRearrangement yCoords) := by
      exact hEqIff.2 ⟨σ.symm, hxσCoords, hyσCoords⟩
    simpa [xCoords, yCoords, euclideanNonincreasingRearrangement_eq] using hEqCoords

/-- Companion to clause `(ii)`: sorted subgradients are characterized by
sorted subdifferential membership together with the existence of one coordinate permutation sending
both vectors to their nonincreasing rearrangements. -/
theorem mem_subdifferential_iff_mem_subdifferential_nonincreasingRearrangement_and_exists_perm
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    {x y : EuclideanSpace ℝ (Fin N)} :
    y ∈ (∂ φ) x ↔
      euclideanNonincreasingRearrangement y ∈
          (∂ φ) (euclideanNonincreasingRearrangement x) ∧
        ∃ σ : Equiv.Perm (Fin N),
          permuteCoordVec σ x = euclideanNonincreasingRearrangement x ∧
            permuteCoordVec σ y = euclideanNonincreasingRearrangement y := by
  have hpermIff :
      ⟪x, y⟫_ℝ =
          ⟪euclideanNonincreasingRearrangement x,
            euclideanNonincreasingRearrangement y⟫_ℝ ↔
        ∃ σ : Equiv.Perm (Fin N),
          permuteCoordVec σ x = euclideanNonincreasingRearrangement x ∧
            permuteCoordVec σ y = euclideanNonincreasingRearrangement y :=
    inner_eq_sorted_inner_iff_exists_perm
  constructor
  · intro hy
    rcases
        (mem_subdifferential_iff_mem_subdifferential_nonincreasingRearrangement_and_inner_eq
          hproper hφsymm).1 hy with ⟨hySorted, hInner⟩
    exact ⟨hySorted, hpermIff.1 hInner⟩
  · rintro ⟨hySorted, hperm⟩
    exact
      (mem_subdifferential_iff_mem_subdifferential_nonincreasingRearrangement_and_inner_eq
        hproper hφsymm).2 ⟨hySorted, hpermIff.2 hperm⟩

/-- Companion to clause `(iii)`: the nonincreasing rearrangements of the subgradients at
`x` belong to the subdifferential at `euclideanNonincreasingRearrangement x`. -/
theorem image_rearrangement_subdifferential_subset_subdifferential_rearrangement
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    euclideanNonincreasingRearrangement '' ((∂ φ) x) ⊆
      (∂ φ) (euclideanNonincreasingRearrangement x) := by
  intro z hz
  rcases hz with ⟨y, hy, rfl⟩
  -- Clause `(iii)` is exactly the first component of the clause `(ii)` bridge.
  exact
    (mem_subdifferential_iff_mem_subdifferential_nonincreasingRearrangement_and_inner_eq
      hproper hφsymm).1 hy |>.1

/-- Helper: coordinate permutations preserve the Euclidean norm. -/
@[simp] theorem coordinatePermutationContinuousLinearEquiv_norm
    (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    ‖coordinatePermutationContinuousLinearEquiv σ x‖ = ‖x‖ := by
  -- This is the transported `LinearIsometryEquiv.norm_map` statement for coordinate permutations.
  convert (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ σ).norm_map x using 1

/-- Helper: coordinate permutations preserve Euclidean distance. -/
@[simp] theorem coordinatePermutationContinuousLinearEquiv_dist
    (σ : Equiv.Perm (Fin N)) (x y : EuclideanSpace ℝ (Fin N)) :
    dist (coordinatePermutationContinuousLinearEquiv σ x)
      (coordinatePermutationContinuousLinearEquiv σ y) = dist x y := by
  -- Distance preservation follows by applying the norm preservation result to `x - y`.
  rw [dist_eq_norm, dist_eq_norm]
  simpa [map_sub] using coordinatePermutationContinuousLinearEquiv_norm σ (x - y)

/-- Helper: symmetry of `φ` transfers to the finite-valued representative
`fun z ↦ (φ z : EReal).toReal` along any coordinate permutation. -/
theorem coordinatePermutationInvariant_toReal
    (hφsymm : CoordinatePermutationInvariant φ) (σ : Equiv.Perm (Fin N)) :
    (fun z : EuclideanSpace ℝ (Fin N) ↦
        (φ (coordinatePermutationContinuousLinearEquiv σ z) : EReal).toReal) =
      fun z ↦ (φ z : EReal).toReal := by
  -- Apply the symmetry equality to the subtype-valued function and then coerce to `ℝ`.
  funext z
  simpa [coordinatePermutationContinuousLinearEquiv_apply] using
    congrArg (fun t : Set.Ioi (⊥ : EReal) ↦ ((t : EReal).toReal)) (hφsymm σ z)

/-- Helper: Fréchet differentiability of the finite representative is
invariant under coordinate permutations. -/
theorem differentiableAt_toReal_coordinatePermutation_iff
    (hφsymm : CoordinatePermutationInvariant φ) (σ : Equiv.Perm (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x ↔
      DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal)
        (coordinatePermutationContinuousLinearEquiv σ x) := by
  let P : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    coordinatePermutationContinuousLinearEquiv σ
  let f : EuclideanSpace ℝ (Fin N) → ℝ := fun z ↦ (φ z : EReal).toReal
  have hcomp : f ∘ P = f := by
    -- Symmetry makes the finite representative literally invariant under the permutation.
    simpa [f, P, Function.comp] using coordinatePermutationInvariant_toReal hφsymm σ
  -- Transport differentiability through the permutation equivalence after normalizing `f ∘ P = f`.
  have hiff : DifferentiableAt ℝ (f ∘ P) x ↔ DifferentiableAt ℝ f (P x) :=
    P.comp_right_differentiableAt_iff (f := f) (x := x)
  calc
    DifferentiableAt ℝ f x ↔ DifferentiableAt ℝ (f ∘ P) x := by
      simp [hcomp]
    _ ↔ DifferentiableAt ℝ f (P x) := hiff

/-- Helper for Proposition 24.58: effective-domain membership is invariant under coordinate
permutations. -/
lemma mem_effectiveDomain_coordinatePermutation_iff
    (hφsymm : CoordinatePermutationInvariant φ) (σ : Equiv.Perm (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    coordinatePermutationContinuousLinearEquiv σ x ∈ effectiveDomain φ ↔
      x ∈ effectiveDomain φ := by
  have hvalue :
      φ (coordinatePermutationContinuousLinearEquiv σ x) = φ x := by
    -- The source symmetry hypothesis identifies the two function values exactly.
    simpa [coordinatePermutationContinuousLinearEquiv_apply] using hφsymm σ x
  -- Effective-domain membership is just the finiteness condition `φ x < ⊤`.
  rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff, hvalue]

/-- Helper: the Chapter 18 continuity set `cont φ` is invariant under
coordinate permutations. -/
theorem mem_cont_coordinatePermutation_iff
    (hφsymm : CoordinatePermutationInvariant φ) (σ : Equiv.Perm (Fin N))
    (x : EuclideanSpace ℝ (Fin N)) :
    x ∈ cont φ ↔ coordinatePermutationContinuousLinearEquiv σ x ∈ cont φ := by
  let P : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    coordinatePermutationContinuousLinearEquiv σ
  let f : EuclideanSpace ℝ (Fin N) → ℝ := fun z ↦ (φ z : EReal).toReal
  have hforward :
      ∀ {τ : Equiv.Perm (Fin N)} {u : EuclideanSpace ℝ (Fin N)},
        u ∈ cont φ → coordinatePermutationContinuousLinearEquiv τ u ∈ cont φ := by
    intro τ u hu
    let Q : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
      coordinatePermutationContinuousLinearEquiv τ
    rcases hu with ⟨ρ, hρ, hball, hcont⟩
    refine ⟨ρ, hρ, ?_, ?_⟩
    · intro z hz
      have hzpre : Q.symm z ∈ Metric.ball u ρ := by
        -- Pull the point back through the inverse permutation and use distance preservation.
        have hdist :
            dist (Q.symm z) u = dist z (Q u) := by
          calc
            dist (Q.symm z) u = dist (Q (Q.symm z)) (Q u) := by
              symm
              exact coordinatePermutationContinuousLinearEquiv_dist τ (Q.symm z) u
            _ = dist z (Q u) := by
              rw [Q.apply_symm_apply]
        simpa [Metric.mem_ball, hdist] using hz
      have hzdom : Q.symm z ∈ effectiveDomain φ := hball hzpre
      have hzdom' :
          coordinatePermutationContinuousLinearEquiv τ.symm z ∈ effectiveDomain φ := by
        simpa [Q, coordinatePermutationContinuousLinearEquiv_symm] using hzdom
      -- Push the effective-domain witness forward again using symmetry.
      exact (mem_effectiveDomain_coordinatePermutation_iff hφsymm τ.symm z).1 hzdom'
    · have hcomp :
          f ∘ Q.symm = f := by
        -- The finite representative is invariant under the inverse permutation as well.
        simpa [f, Q, Function.comp, coordinatePermutationContinuousLinearEquiv_symm] using
          coordinatePermutationInvariant_toReal hφsymm τ.symm
      have hcont_comp : ContinuousAt (f ∘ Q.symm) (Q u) := by
        -- Homeomorphism transport moves continuity from `u` to `Q u`.
        change ContinuousAt (f ∘ Q.symm.toHomeomorph) (Q u)
        have hcont_u : ContinuousAt f (Q.symm (Q u)) := by
          simpa [f] using (Q.symm_apply_apply u ▸ hcont)
        exact ((Q.symm.toHomeomorph).comp_continuousAt_iff' f (Q u)).2 hcont_u
      simpa [f, hcomp] using hcont_comp
  constructor
  · intro hx
    -- Apply the generic forward transport to the requested permutation.
    simpa [P] using (hforward (τ := σ) (u := x) hx)
  · intro hx
    -- Apply the same transport to the inverse permutation and simplify.
    have hx' : coordinatePermutationContinuousLinearEquiv σ.symm (P x) ∈ cont φ :=
      hforward (τ := σ.symm) (u := P x) hx
    have hPx : coordinatePermutationContinuousLinearEquiv σ.symm (P x) = x := by
      simpa [P] using P.symm_apply_apply x
    exact hPx ▸ hx'

/-- Helper: the Chapter 18 continuity set `cont φ` is invariant under
nonincreasing rearrangement. -/
theorem mem_cont_nonincreasingRearrangement_iff
    (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    x ∈ cont φ ↔ euclideanNonincreasingRearrangement x ∈ cont φ := by
  obtain ⟨σ, hσx⟩ := exists_permuteCoordVec_eq_nonincreasingRearrangement x
  -- Specialize the permutation-invariance statement to a sorting permutation of `x`.
  simpa [coordinatePermutationContinuousLinearEquiv_apply, hσx] using
    mem_cont_coordinatePermutation_iff hφsymm σ x

/-- The range of a coordinate permutation operator is all of the
ambient Euclidean space, so the chain-rule regularity hypothesis reduces to the `dom g - univ`
pattern. -/
theorem zero_mem_sri_sub_effectiveDomain_of_perm_range_univ
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N))) (σ : Equiv.Perm (Fin N)) :
    (0 : EuclideanSpace ℝ (Fin N)) ∈
      Set.strongRelativeInterior (effectiveDomain φ -
        Set.range
          (((coordinatePermutationContinuousLinearEquiv σ :
              EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) :
                EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)))) := by
  have hrange :
      Set.range
          (((coordinatePermutationContinuousLinearEquiv σ :
              EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) :
                EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N))) =
        (Set.univ : Set (EuclideanSpace ℝ (Fin N))) := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      refine ⟨(coordinatePermutationContinuousLinearEquiv σ).symm y, ?_⟩
      simpa using (coordinatePermutationContinuousLinearEquiv σ).apply_symm_apply y
  -- Once the range is `univ`, this is the standard `dom f - univ = univ` strong-relative-interior
  -- calculation.
  rw [hrange]
  obtain ⟨x, hx⟩ : (effectiveDomain φ).Nonempty := ConvexOn.nonempty hφ.2
  have hsub :
      effectiveDomain φ - (Set.univ : Set (EuclideanSpace ℝ (Fin N))) =
        (Set.univ : Set (EuclideanSpace ℝ (Fin N))) := by
    ext y
    constructor
    · intro hy
      simp
    · intro hy
      exact Set.mem_sub.mpr ⟨x, hx, x - y, by simp, by abel⟩
  rw [hsub]
  rw [Set.mem_strongRelativeInterior_iff]
  refine ⟨by simp, ?_⟩
  ext y
  constructor
  · intro hy
    simp
  · intro hy
    rw [Set.cone_def]
    exact ConvexCone.subset_hull (by simp)

/-- A symmetric `Γ₀` function transports its whole subdifferential
fiber through any coordinate permutation. -/
theorem image_subdifferential_coordinatePermutation_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (σ : Equiv.Perm (Fin N)) (x : EuclideanSpace ℝ (Fin N)) :
    coordinatePermutationContinuousLinearEquiv σ '' ((∂ φ) x) =
      (∂ φ) (coordinatePermutationContinuousLinearEquiv σ x) := by
  let P : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    coordinatePermutationContinuousLinearEquiv σ
  have hproper : (effectiveDomain φ).Nonempty := hφ.2.nonempty
  have hφstarSymm : CoordinatePermutationInvariant (φ.asEReal∗) :=
    conjugate_coordinatePermutationInvariant hφsymm
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    have hcontact :
        (φ x : EReal) + φ.asEReal∗ v = ((⟪x, v⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq φ hproper x v).1 hv
    have hφPx : φ (P x) = φ x := by
      simpa [P, coordinatePermutationContinuousLinearEquiv_apply] using hφsymm σ x
    have hφstarPv : φ.asEReal∗ (P v) = φ.asEReal∗ v := by
      simpa [P, coordinatePermutationContinuousLinearEquiv_apply] using hφstarSymm σ v
    have hcontact_perm :
        (φ (P x) : EReal) + φ.asEReal∗ (P v) =
          ((⟪P x, P v⟫_ℝ : ℝ) : EReal) := by
      -- Symmetry of `φ` and `φ*`, together with inner-product preservation, keeps the
      -- Fenchel--Young equality unchanged under a common coordinate permutation.
      calc
        (φ (P x) : EReal) + φ.asEReal∗ (P v) = (φ x : EReal) + φ.asEReal∗ v := by
          rw [hφPx, hφstarPv]
        _ = ((⟪x, v⟫_ℝ : ℝ) : EReal) := hcontact
        _ = ((⟪P x, P v⟫_ℝ : ℝ) : EReal) := by
            exact congrArg (fun r : ℝ ↦ (r : EReal))
              (coordinatePermutationContinuousLinearEquiv_inner σ x v).symm
    exact
      (mem_subdifferential_iff_fenchel_young_eq φ hproper (P x) (P v)).2
        hcontact_perm
  · intro hu
    refine ⟨P.symm u, ?_, ?_⟩
    · have hcontact :
          (φ (P x) : EReal) + φ.asEReal∗ u =
            ((⟪P x, u⟫_ℝ : ℝ) : EReal) :=
        (mem_subdifferential_iff_fenchel_young_eq φ hproper (P x) u).1 hu
      have hφPx : φ (P x) = φ x := by
        simpa [P, coordinatePermutationContinuousLinearEquiv_apply] using hφsymm σ x
      have hφstarPsu : φ.asEReal∗ (P.symm u) = φ.asEReal∗ u := by
        calc
          φ.asEReal∗ (P.symm u) = φ.asEReal∗ (P (P.symm u)) := by
            simpa [P, coordinatePermutationContinuousLinearEquiv_apply] using
              (hφstarSymm σ (P.symm u)).symm
          _ = φ.asEReal∗ u := by rw [P.apply_symm_apply]
      have hinner : ⟪P x, u⟫_ℝ = ⟪x, P.symm u⟫_ℝ := by
        calc
          ⟪P x, u⟫_ℝ = ⟪P x, P (P.symm u)⟫_ℝ := by
            rw [P.apply_symm_apply u]
          _ = ⟪x, P.symm u⟫_ℝ :=
            coordinatePermutationContinuousLinearEquiv_inner σ x (P.symm u)
      have hcontact_perm :
          (φ x : EReal) + φ.asEReal∗ (P.symm u) =
            ((⟪x, P.symm u⟫_ℝ : ℝ) : EReal) := by
        -- Apply the same Fenchel--Young transport along the inverse permutation.
        calc
          (φ x : EReal) + φ.asEReal∗ (P.symm u) =
              (φ (P x) : EReal) + φ.asEReal∗ u := by
                rw [← hφPx, hφstarPsu]
          _ = ((⟪P x, u⟫_ℝ : ℝ) : EReal) := hcontact
          _ = ((⟪x, P.symm u⟫_ℝ : ℝ) : EReal) := by
              exact congrArg (fun r : ℝ ↦ (r : EReal)) hinner
      exact
        (mem_subdifferential_iff_fenchel_young_eq φ hproper x (P.symm u)).2
          hcontact_perm
    · simpa [P] using P.apply_symm_apply u

/-- Auxiliary strengthening of clause `(iv)`: under the stronger convex-analysis hypotheses used by
Corollary 16.53 and Proposition 17.45, source differentiability at `x` and `x↓` is equivalent,
and the gradient of the finite representative sorts compatibly. -/
theorem differentiableAt_iff_differentiableAt_nonincreasingRearrangement_and_gradient_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    (DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x ↔
      DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal)
        (euclideanNonincreasingRearrangement x)) ∧
      (DifferentiableAt ℝ
          (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x →
        ∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal)
            (euclideanNonincreasingRearrangement x) =
          euclideanNonincreasingRearrangement
            (∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x)) := by
  let xs := euclideanNonincreasingRearrangement x
  let f : EuclideanSpace ℝ (Fin N) → ℝ := fun z ↦ (φ z : EReal).toReal
  obtain ⟨σ, hσx⟩ := exists_permuteCoordVec_eq_nonincreasingRearrangement x
  let P : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N) :=
    coordinatePermutationContinuousLinearEquiv σ
  have hPx : P x = xs := by
    -- The chosen permutation is exactly the sorting permutation of `x`.
    simpa [P, xs, coordinatePermutationContinuousLinearEquiv_apply] using hσx
  have hPimage :
      P '' ((∂ φ) x) = (∂ φ) xs := by
    -- Transport the whole subdifferential fiber to the sorted base point.
    simpa [P, xs, hPx] using
      image_subdifferential_coordinatePermutation_eq hφ hφsymm σ x
  have hPxs : P.symm xs = x := by
    -- Inverting the sorting permutation recovers the original base point.
    rw [← hPx]
    exact P.symm_apply_apply x
  have hPxs' : coordinatePermutationContinuousLinearEquiv σ.symm xs = x := by
    simpa [P] using hPxs
  have hPinvimage :
      P.symm '' ((∂ φ) xs) = (∂ φ) x := by
    -- The inverse permutation transports the sorted fiber back to the original base point.
    calc
      P.symm '' ((∂ φ) xs) =
          coordinatePermutationContinuousLinearEquiv σ.symm '' ((∂ φ) xs) := by
            simp [P]
      _ = (∂ φ) (coordinatePermutationContinuousLinearEquiv σ.symm xs) := by
            exact
              image_subdifferential_coordinatePermutation_eq hφ hφsymm σ.symm xs
      _ = (∂ φ) x := by rw [hPxs']
  have hforward : DifferentiableAt ℝ f x → DifferentiableAt ℝ f xs := by
    intro hdiff
    let gx := ∇ f x
    have hsub_x : (∂ φ) x = ({gx} : Set (EuclideanSpace ℝ (Fin N))) := by
      -- Proposition 17.45 turns differentiability at `x` into a singleton subdifferential fiber.
      exact
        (subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
          hφ gx).2 ⟨hdiff, rfl⟩
    have hsub_xs : (∂ φ) xs = ({P gx} : Set (EuclideanSpace ℝ (Fin N))) := by
      -- Transport the singleton fiber through the sorting permutation.
      calc
        (∂ φ) xs = P '' ((∂ φ) x) := hPimage.symm
        _ = ({P gx} : Set (EuclideanSpace ℝ (Fin N))) := by
            rw [hsub_x, Set.image_singleton]
    exact
      (subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
        hφ (P gx)).1 hsub_xs |>.1
  have hbackward : DifferentiableAt ℝ f xs → DifferentiableAt ℝ f x := by
    intro hdiff
    let gs := ∇ f xs
    have hsub_xs : (∂ φ) xs = ({gs} : Set (EuclideanSpace ℝ (Fin N))) := by
      -- Proposition 17.45 gives the singleton fiber at the sorted point as well.
      exact
        (subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
          hφ gs).2 ⟨hdiff, rfl⟩
    have hsub_x : (∂ φ) x = ({P.symm gs} : Set (EuclideanSpace ℝ (Fin N))) := by
      -- Pull the sorted singleton fiber back along the inverse permutation.
      calc
        (∂ φ) x = P.symm '' ((∂ φ) xs) := by
          symm
          exact hPinvimage
        _ = ({P.symm gs} : Set (EuclideanSpace ℝ (Fin N))) := by
            rw [hsub_xs, Set.image_singleton]
    exact
      (subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
        hφ (P.symm gs)).1 hsub_x |>.1
  refine ⟨⟨hforward, hbackward⟩, ?_⟩
  intro hdiff
  let gx := ∇ f x
  have hsub_x : (∂ φ) x = ({gx} : Set (EuclideanSpace ℝ (Fin N))) := by
    -- Start the gradient computation from the singleton fiber at `x`.
    exact
      (subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
        hφ gx).2 ⟨hdiff, rfl⟩
  have hgx_mem : gx ∈ (∂ φ) x := by
    simp [hsub_x]
  have hsub_xs : (∂ φ) xs = ({P gx} : Set (EuclideanSpace ℝ (Fin N))) := by
    -- The transported singleton fiber at `xs` is still the whole subdifferential there.
    calc
      (∂ φ) xs = P '' ((∂ φ) x) := hPimage.symm
      _ = ({P gx} : Set (EuclideanSpace ℝ (Fin N))) := by
          rw [hsub_x, Set.image_singleton]
  have hgrad_sorted :
      P gx = ∇ f xs := by
    -- Proposition 17.45 recovers the gradient from the singleton sorted fiber.
    exact
      (subdifferential_eq_singleton_iff_differentiableAt_and_eq_gradient_of_mem_gammaZero
        hφ (P gx)).1 hsub_xs |>.2
  have hsorted_grad_mem : euclideanNonincreasingRearrangement gx ∈ (∂ φ) xs := by
    -- Clause `(iii)` places the rearranged original gradient in the sorted subdifferential.
    exact
      image_rearrangement_subdifferential_subset_subdifferential_rearrangement
        hφ.2.nonempty hφsymm x ⟨gx, hgx_mem, rfl⟩
  have hPgx_eq : P gx = euclideanNonincreasingRearrangement gx := by
    -- Since the sorted subdifferential is a singleton, both sorted candidates must agree.
    have : euclideanNonincreasingRearrangement gx ∈ ({P gx} : Set (EuclideanSpace ℝ (Fin N))) := by
      simpa [hsub_xs] using hsorted_grad_mem
    simpa using this.symm
  calc
    ∇ f xs = P gx := hgrad_sorted.symm
    _ = euclideanNonincreasingRearrangement gx := hPgx_eq
    _ = euclideanNonincreasingRearrangement (∇ f x) := rfl

/-- The source pointwise differentiability predicate for the rearrangement clause in this file:
`φ` is continuous at `x` and the finite representative of `φ` is Fréchet differentiable at `x`. -/
abbrev sourceDifferentiableAt
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (x : EuclideanSpace ℝ (Fin N)) : Prop :=
  x ∈ sourceDifferentiabilitySet φ

/-- The source gradient for the rearrangement clause in this file, namely the gradient of the finite
representative of `φ`. -/
noncomputable abbrev sourceGradient
    (φ : EuclideanSpace ℝ (Fin N) → Set.Ioi (⊥ : EReal))
    (x : EuclideanSpace ℝ (Fin N)) : EuclideanSpace ℝ (Fin N) :=
  ∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x

/-- Expanding `sourceDifferentiableAt` recovers the Chapter 18 continuity-plus-Fréchet
differentiability package for the finite representative. -/
@[simp] theorem sourceDifferentiableAt_iff
    (x : EuclideanSpace ℝ (Fin N)) :
    sourceDifferentiableAt φ x ↔
      x ∈ cont φ ∧
        DifferentiableAt ℝ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x := by
  simp [sourceDifferentiableAt, sourceDifferentiabilitySet]

/-- Expanding `sourceGradient` recovers the gradient of the finite representative. -/
@[simp] theorem sourceGradient_eq
    (x : EuclideanSpace ℝ (Fin N)) :
    sourceGradient φ x =
      ∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x :=
  rfl

/-- Companion to clause `(iv)` on the source-facing differentiability and gradient surface. -/
theorem sourceDifferentiableAt_rearrangement_iff_and_sourceGradient_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N)))
    (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    (sourceDifferentiableAt φ x ↔
      sourceDifferentiableAt φ (euclideanNonincreasingRearrangement x)) ∧
      (sourceDifferentiableAt φ x →
        sourceGradient φ (euclideanNonincreasingRearrangement x) =
          euclideanNonincreasingRearrangement (sourceGradient φ x)) := by
  let xs := euclideanNonincreasingRearrangement x
  have hdiff :=
    differentiableAt_iff_differentiableAt_nonincreasingRearrangement_and_gradient_eq
      hφ hφsymm x
  refine ⟨?_, ?_⟩
  · rw [@sourceDifferentiableAt_iff N φ x, @sourceDifferentiableAt_iff N φ xs]
    constructor
    · rintro ⟨hxcont, hxdiff⟩
      exact ⟨(mem_cont_nonincreasingRearrangement_iff hφsymm x).1 hxcont, hdiff.1.1 hxdiff⟩
    · rintro ⟨hxscont, hxsdiff⟩
      exact ⟨(mem_cont_nonincreasingRearrangement_iff hφsymm x).2 hxscont, hdiff.1.2 hxsdiff⟩
  · intro hxsource
    exact hdiff.2 ((@sourceDifferentiableAt_iff N φ x).1 hxsource).2

/-- Clause `(iv)` auxiliary on the stronger Chapter 18 source-differentiability surface used by
the current convex-analysis proof route. -/
theorem mem_sourceDifferentiabilitySet_iff_mem_nonincreasingRearrangement_and_gradient_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N))) (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    (x ∈ sourceDifferentiabilitySet φ ↔
      euclideanNonincreasingRearrangement x ∈ sourceDifferentiabilitySet φ) ∧
      (x ∈ sourceDifferentiabilitySet φ →
        ∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal)
            (euclideanNonincreasingRearrangement x) =
          euclideanNonincreasingRearrangement
                (∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x)) := by
  simpa [sourceDifferentiableAt, sourceGradient] using
    sourceDifferentiableAt_rearrangement_iff_and_sourceGradient_eq hφ hφsymm x

/-! Source-facing clause wrappers and companions for Proposition 24.58.

Let `φ : ℝ^N → ]-∞,+∞]` be proper and symmetric, and let `x` and `y` be in `ℝ^N`. Then:

- `(i)` `φ^*` is symmetric.
- `(ii)` `y ∈ ∂ φ(x)` iff `y↓ ∈ ∂ φ(x↓)` together with the corresponding inner-product equality,
  equivalently iff there is one coordinate permutation sending both `x` and `y` to their
  nonincreasing rearrangements.
- `(iii)` `(∂ φ(x))↓ ⊆ ∂ φ(x↓)`.
- `(iv)` `φ` is differentiable at `x` iff it is differentiable at `x↓`, in which case
  `∇ φ (x↓) = (∇ φ x)↓`, represented here by the source-facing owners
  `sourceDifferentiableAt` and `sourceGradient`.
-/

/-- Companion to clause `(i)`: if `φ` is proper and symmetric, then `φ.asEReal∗` is symmetric. -/
theorem symmetricFunction_rearrangement_conjugate
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ) :
    CoordinatePermutationInvariant (φ.asEReal∗) := by
  let _ := hproper
  -- This textbook-facing wrapper is exactly the proved clause `(i)` companion.
  simpa using conjugate_coordinatePermutationInvariant hφsymm

/- Clause `(ii)` is formalized first in the
inner-product-equality form and then in the equivalent permutation form below. -/

/-- Companion to clause `(ii)`: `y ∈ ∂ φ(x)` iff `y↓ ∈ ∂ φ(x↓)` and
`⟪x, y⟫_ℝ = ⟪x↓, y↓⟫_ℝ`. -/
theorem symmetricFunction_rearrangement_subdifferential_iff_sorted_and_inner_eq
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    (x y : EuclideanSpace ℝ (Fin N)) :
    y ∈ (∂ φ) x ↔
      euclideanNonincreasingRearrangement y ∈
          (∂ φ) (euclideanNonincreasingRearrangement x) ∧
        ⟪x, y⟫_ℝ =
          ⟪euclideanNonincreasingRearrangement x,
            euclideanNonincreasingRearrangement y⟫_ℝ := by
  -- This wrapper just exposes the clause `(ii)` companion under the textbook-facing name.
  simpa using
    (mem_subdifferential_iff_mem_subdifferential_nonincreasingRearrangement_and_inner_eq
      hproper hφsymm :
        y ∈ (∂ φ) x ↔
          euclideanNonincreasingRearrangement y ∈
              (∂ φ) (euclideanNonincreasingRearrangement x) ∧
            ⟪x, y⟫_ℝ =
              ⟪euclideanNonincreasingRearrangement x,
                euclideanNonincreasingRearrangement y⟫_ℝ)

/-- Companion to clause `(ii)`: equivalent permutation form of the sorted subdifferential
criterion. -/
theorem symmetricFunction_rearrangement_subdifferential_iff_sorted_and_exists_perm
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    (x y : EuclideanSpace ℝ (Fin N)) :
    y ∈ (∂ φ) x ↔
      euclideanNonincreasingRearrangement y ∈
          (∂ φ) (euclideanNonincreasingRearrangement x) ∧
        ∃ σ : Equiv.Perm (Fin N),
          permuteCoordVec σ x = euclideanNonincreasingRearrangement x ∧
            permuteCoordVec σ y = euclideanNonincreasingRearrangement y := by
  -- This wrapper just exposes the second clause `(ii)` companion.
  simpa using
    (mem_subdifferential_iff_mem_subdifferential_nonincreasingRearrangement_and_exists_perm
      hproper hφsymm :
        y ∈ (∂ φ) x ↔
          euclideanNonincreasingRearrangement y ∈
              (∂ φ) (euclideanNonincreasingRearrangement x) ∧
            ∃ σ : Equiv.Perm (Fin N),
              permuteCoordVec σ x = euclideanNonincreasingRearrangement x ∧
                permuteCoordVec σ y = euclideanNonincreasingRearrangement y)

/-- Companion to clause `(iii)`: the nonincreasing rearrangements of the subgradients at `x`
belong to `∂ φ(x↓)`. -/
theorem symmetricFunction_rearrangement_image_subdifferential_subset
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    euclideanNonincreasingRearrangement '' ((∂ φ) x) ⊆
      (∂ φ) (euclideanNonincreasingRearrangement x) := by
  -- This textbook-facing wrapper is exactly the proved clause `(iii)` companion.
  simpa using
    image_rearrangement_subdifferential_subset_subdifferential_rearrangement
      hproper hφsymm x

/-- Auxiliary transport of Fréchet differentiability of the finite representative of `φ` across
nonincreasing rearrangement. -/
theorem symmetricFunction_rearrangement_differentiableAt_toReal_iff
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x ↔
      DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal)
        (euclideanNonincreasingRearrangement x) := by
  let _ := hproper
  obtain ⟨σ, hσx⟩ := exists_permuteCoordVec_eq_nonincreasingRearrangement x
  -- Use the direct calculus transport across a sorting permutation of `x`.
  simpa [coordinatePermutationContinuousLinearEquiv_apply, hσx] using
    differentiableAt_toReal_coordinatePermutation_iff hφsymm σ x

/-- Auxiliary `Γ₀`-strengthening of clause `(iv)`: when the finite representative of `φ` is
Fréchet differentiable at `x`, its gradient sorts compatibly. -/
theorem symmetricFunction_rearrangement_gradient_toReal_nonincreasingRearrangement_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N))) (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    DifferentiableAt ℝ
        (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x →
      ∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal)
          (euclideanNonincreasingRearrangement x) =
        euclideanNonincreasingRearrangement
          (∇ (fun z : EuclideanSpace ℝ (Fin N) ↦ (φ z : EReal).toReal) x) := by
  -- This clause is exactly the gradient projection from the stronger rearrangement theorem above.
  simpa using
    (differentiableAt_iff_differentiableAt_nonincreasingRearrangement_and_gradient_eq
      hφ hφsymm x).2

/-- Stronger Chapter 17/18 companion to clause `(iv)`: under the convex-analysis
hypothesis `φ ∈ Γ₀(ℝ^N)`, the source differentiability predicate is invariant under
nonincreasing rearrangement, and the source gradient sorts compatibly. -/
theorem symmetricFunction_rearrangement_sourceDifferentiableAt_iff_and_sourceGradient_eq
    (hφ : φ ∈ Γ₀(EuclideanSpace ℝ (Fin N))) (hφsymm : CoordinatePermutationInvariant φ)
    (x : EuclideanSpace ℝ (Fin N)) :
    (sourceDifferentiableAt φ x ↔
      sourceDifferentiableAt φ (euclideanNonincreasingRearrangement x)) ∧
    (sourceDifferentiableAt φ x →
        sourceGradient φ (euclideanNonincreasingRearrangement x) =
          euclideanNonincreasingRearrangement (sourceGradient φ x)) := by
  simpa using sourceDifferentiableAt_rearrangement_iff_and_sourceGradient_eq hφ hφsymm x

/-- Proposition 24.58: let `φ : ℝ^N → ]-∞,+∞]` be proper and symmetric, and let `x` and `y` be
in `ℝ^N`. Then `(i)` `φ^*` is symmetric, `(ii)` the source subdifferential conditions at `x` and
`x↓` are equivalent in both the inner-product and permutation forms, `(iii)` the nonincreasing
rearrangements of subgradients at `x` belong to `∂ φ(x↓)`, and `(iv)` the source-facing
differentiability predicate is invariant under rearrangement, in which case the source gradient
sorts compatibly. -/
theorem symmetricFunction_rearrangement
    (hproper : (effectiveDomain φ).Nonempty) (hφsymm : CoordinatePermutationInvariant φ)
    (x y : EuclideanSpace ℝ (Fin N)) :
    (let xs := euclideanNonincreasingRearrangement x
     let ys := euclideanNonincreasingRearrangement y
     let sortedInner : Prop :=
       ys ∈ (∂ φ) xs ∧
         ⟪x, y⟫_ℝ = ⟪xs, ys⟫_ℝ
     let sortedPerm : Prop :=
       ys ∈ (∂ φ) xs ∧
         ∃ σ : Equiv.Perm (Fin N),
           permuteCoordVec σ x = xs ∧
             permuteCoordVec σ y = ys
     CoordinatePermutationInvariant (φ.asEReal∗) ∧
       (y ∈ (∂ φ) x ↔ sortedInner) ∧
       (sortedInner ↔ sortedPerm) ∧
       (euclideanNonincreasingRearrangement '' ((∂ φ) x) ⊆ (∂ φ) xs) ∧
       ((sourceDifferentiableAt φ x ↔ sourceDifferentiableAt φ xs) ∧
         (sourceDifferentiableAt φ x →
           sourceGradient φ xs =
             euclideanNonincreasingRearrangement (sourceGradient φ x)))) := by
  -- Route correction: clause `(iv)` is false under the current header. The source proof invokes
  -- Corollary 16.53 and Proposition 17.45, both of which assume `φ ∈ Γ₀(ℝ^N)`.
  -- A concrete counterexample is the symmetric polynomial
  -- `f(a, b) = a^2 + 3 * a * b + b^2` on `ℝ^2`, viewed in `Set.Ioi (⊥ : EReal)`: at the already
  -- sorted point `(2, 1)`, one has `∇ f = (7, 8)`, so `∇ f (x↓) ≠ (∇ f x)↓`.
  let _ := hproper
  let _ := hφsymm
  let _ := x
  let _ := y
  sorry

end SymmetricFiniteFunctions

end ERealFunction
