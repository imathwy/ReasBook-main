import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_1_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_5_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Observation_9_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TopCat Topology Topology.Homotopy

noncomputable section

-- Semantic recall via repository search: Chapter 3 already fixes `RealProjectiveSpace` together
-- with the standard double cover `sphereToRealProjectiveSpace`, Chapter 9 fixes
-- `relativeHomotopyGroup` as the source-facing owner for pair-relative homotopy groups. The
-- public API below therefore keeps the RP-pair term source-facing and uses a direct quotient type
-- for collapsing `RP^(n + 1) ⊆ RP^(n + 2)` only as the target in part (2).

/-- The relation collapsing a subset `A ⊆ X` to a single point. -/
private def collapseSubsetRel {X : Type*} [TopologicalSpace X] (A : Set X) : X → X → Prop :=
  fun x y ↦ x = y ∨ (x ∈ A ∧ y ∈ A)

/-- The quotient setoid collapsing `A ⊆ X` to one point, generated from `collapseSubsetRel A`. -/
private abbrev collapseSubsetSetoid {X : Type*} [TopologicalSpace X] (A : Set X) : Setoid X :=
  Relation.EqvGen.setoid (collapseSubsetRel A)

/-- The equatorial copy of `S^(n-1)` inside `S^n`, cut out by the last coordinate equation. -/
def sphereEquatorLocus (n : ℕ) : Set (𝕊 n) :=
  {x | x.down.1 (Fin.last n) = 0}

/-- A concrete point on the equator of `S^(n+2)`, given by the first standard basis vector. -/
private def sphereEquatorBasepoint (n : ℕ) : 𝕊 (n + 2) :=
  ULift.up <| ⟨EuclideanSpace.single 0 (1 : ℝ), by simp⟩

/-- The chosen sphere basepoint lies on the equator `S^(n+1) ⊆ S^(n+2)`. -/
private theorem sphereEquatorBasepoint_mem (n : ℕ) :
    sphereEquatorBasepoint n ∈ sphereEquatorLocus (n + 2) := by
  simp [sphereEquatorBasepoint, sphereEquatorLocus]

/-- The equatorial image in `RP^(n + 2)`, representing the standard copy of `RP^(n + 1)`. -/
def realProjectiveSpaceEquatorLocus (n : ℕ) : Set (RealProjectiveSpace (n + 2)) :=
  (sphereToRealProjectiveSpace (n + 2)) '' sphereEquatorLocus (n + 2)

/-- The chosen projective-space basepoint lies on the equatorial copy of `RP^(n + 1)`. -/
private theorem realProjectiveSpaceEquatorBasepoint_mem (n : ℕ) :
    sphereToRealProjectiveSpace (n + 2) (sphereEquatorBasepoint n) ∈
      realProjectiveSpaceEquatorLocus n := by
  exact ⟨sphereEquatorBasepoint n, sphereEquatorBasepoint_mem n, rfl⟩

/-- The chosen basepoint of the source pair `(RP^(n + 2), RP^(n + 1))`. -/
def realProjectiveSpaceEquatorBasepoint (n : ℕ) : realProjectiveSpaceEquatorLocus n :=
  ⟨sphereToRealProjectiveSpace (n + 2) (sphereEquatorBasepoint n),
    realProjectiveSpaceEquatorBasepoint_mem n⟩

/-- The equatorial copy of `RP^(n + 1)` inside `RP^(n + 2)` is nonempty. -/
theorem realProjectiveSpaceEquatorLocus_nonempty (n : ℕ) :
    (realProjectiveSpaceEquatorLocus n).Nonempty :=
  ⟨_, realProjectiveSpaceEquatorBasepoint_mem n⟩

/-- The source-facing relative homotopy group `π_(n+2)(RP^(n + 2), RP^(n + 1))`, expressed using
the Chapter 9 pair-relative owner and the equatorial copy of `RP^(n + 1)` inside `RP^(n + 2)`. -/
abbrev realProjectiveSpacePairRelativeHomotopyGroup (n : ℕ) :=
  relativeHomotopyGroup
    (n + 1).succPNat
    (realProjectiveSpaceEquatorLocus n)
    (realProjectiveSpaceEquatorBasepoint n)

/-- Applying `relativeHomotopyGroup_succ` to
`realProjectiveSpacePairRelativeHomotopyGroup n` recovers the shifted path-space model for
`π_(n+2)(RP^(n + 2), RP^(n + 1))`. -/
@[simp] theorem realProjectiveSpacePairRelativeHomotopyGroup_eq_pi (n : ℕ) :
    realProjectiveSpacePairRelativeHomotopyGroup n =
      π_ (n + 1)
        (PathToSet
          (realProjectiveSpaceEquatorLocus n)
          (realProjectiveSpaceEquatorBasepoint n).1)
        (PathToSet.refl (realProjectiveSpaceEquatorBasepoint n)) := by
  exact
    relativeHomotopyGroup_succ
      (n + 1)
      (realProjectiveSpaceEquatorLocus n)
      (realProjectiveSpaceEquatorBasepoint n)

/-- The canonical quotient space `RP^(n + 2) / RP^(n + 1)` obtained by collapsing the equatorial
copy of `RP^(n + 1)` in `RP^(n + 2)` to a point. -/
abbrev realProjectiveSpaceEquatorQuotient (n : ℕ) :=
  Quotient (collapseSubsetSetoid (realProjectiveSpaceEquatorLocus n))

/-- The distinguished collapsed point of `RP^(n + 2) / RP^(n + 1)`. -/
abbrev realProjectiveSpaceEquatorQuotientBasepoint (n : ℕ) :
    realProjectiveSpaceEquatorQuotient n :=
  Quotient.mk'' (realProjectiveSpaceEquatorBasepoint n).1

/-- The canonical quotient map `RP^(n + 2) ⟶ RP^(n + 2) / RP^(n + 1)`. -/
def realProjectiveSpaceEquatorQuotientMap (n : ℕ) :
    C(RealProjectiveSpace (n + 2), realProjectiveSpaceEquatorQuotient n) :=
  ⟨fun x ↦ Quotient.mk'' x, continuous_quotient_mk'⟩

/-- The canonical quotient map sends the equatorial copy of `RP^(n + 1)` to the collapsed
basepoint of `RP^(n + 2) / RP^(n + 1)`. -/
private theorem realProjectiveSpaceEquatorQuotientMap_mapsEquator (n : ℕ) :
    Set.MapsTo
      (realProjectiveSpaceEquatorQuotientMap n)
      (realProjectiveSpaceEquatorLocus n)
      ({realProjectiveSpaceEquatorQuotientBasepoint n} :
        Set (realProjectiveSpaceEquatorQuotient n)) := by
  intro x hx
  change Quotient.mk'' x = realProjectiveSpaceEquatorQuotientBasepoint n
  exact Quot.sound <|
    Relation.EqvGen.rel x (realProjectiveSpaceEquatorBasepoint n).1 <|
      Or.inr ⟨hx, realProjectiveSpaceEquatorBasepoint_mem n⟩

/-- The distinguished point of the singleton subspace `{*} ⊆ RP^(n + 2) / RP^(n + 1)`. -/
abbrev realProjectiveSpaceEquatorQuotientSingletonBasepoint (n : ℕ) :
    ({realProjectiveSpaceEquatorQuotientBasepoint n} :
      Set (realProjectiveSpaceEquatorQuotient n)) :=
  ⟨realProjectiveSpaceEquatorQuotientBasepoint n, by simp⟩

private abbrev RPRelativeModel (n : ℕ) :=
  ∀ a : realProjectiveSpaceEquatorLocus n,
    relativeHomotopyGroup
        (n + 1).succPNat
        (realProjectiveSpaceEquatorLocus n)
        a ≃
      basedDiskBoundaryPairMapHomotopyClass
        (n + 1).succPNat
        (realProjectiveSpaceEquatorLocus n)
        a

private abbrev RPQuotientRelativeModel (n : ℕ) :=
  ∀ a :
      ({realProjectiveSpaceEquatorQuotientBasepoint n} :
        Set (realProjectiveSpaceEquatorQuotient n)),
    relativeHomotopyGroup
        (n + 1).succPNat
        ({realProjectiveSpaceEquatorQuotientBasepoint n} :
          Set (realProjectiveSpaceEquatorQuotient n))
        a ≃
      basedDiskBoundaryPairMapHomotopyClass
        (n + 1).succPNat
        ({realProjectiveSpaceEquatorQuotientBasepoint n} :
          Set (realProjectiveSpaceEquatorQuotient n))
        a

/-- The image of the chosen equatorial basepoint under the quotient pair map is the canonical point
of the singleton target subspace `{*}`. -/
private theorem realProjectiveSpaceEquatorQuotientSingletonBasepoint_eq_image (n : ℕ) :
    pairMapSubspace
        (realProjectiveSpaceEquatorQuotientMap n)
        (realProjectiveSpaceEquatorQuotientMap_mapsEquator n)
        (realProjectiveSpaceEquatorBasepoint n) =
      realProjectiveSpaceEquatorQuotientSingletonBasepoint n := by
  apply Subtype.ext
  change realProjectiveSpaceEquatorQuotientMap n
      (realProjectiveSpaceEquatorBasepoint n).1 =
    realProjectiveSpaceEquatorQuotientBasepoint n
  exact realProjectiveSpaceEquatorQuotientMap_mapsEquator n
    (realProjectiveSpaceEquatorBasepoint_mem n)

/-- The quotient map of pairs `(RP^(n + 2), RP^(n + 1)) ⟶ (RP^(n + 2) / RP^(n + 1), *)` induces
the corresponding map on the Chapter 9 relative homotopy-group owner, relative to the supplied
disk-boundary model comparisons for the source and target pairs. -/
noncomputable def realProjectiveSpacePairQuotientRelativeHomotopyGroupMap
    (n : ℕ) (eRP : RPRelativeModel n) (eQuot : RPQuotientRelativeModel n) :
    realProjectiveSpacePairRelativeHomotopyGroup n →
      relativeHomotopyGroup
        (n + 1).succPNat
        ({realProjectiveSpaceEquatorQuotientBasepoint n} :
          Set (realProjectiveSpaceEquatorQuotient n))
        (realProjectiveSpaceEquatorQuotientSingletonBasepoint n) :=
  relativeHomotopyGroupEquivOfPathClass eQuot
      ⟦by
        simpa [realProjectiveSpaceEquatorQuotientSingletonBasepoint_eq_image n] using
          Joined.refl (realProjectiveSpaceEquatorQuotientSingletonBasepoint n)
            |>.somePath⟧ ∘
    relativeHomotopyGroupMapOfPairMap eRP eQuot
      (realProjectiveSpaceEquatorQuotientMap n)
      (realProjectiveSpaceEquatorQuotientMap_mapsEquator n)
      (realProjectiveSpaceEquatorBasepoint n)

/-- Applying `realProjectiveSpacePairQuotientRelativeHomotopyGroupMap` first uses the quotient map
of pairs and then changes the singleton target basepoint to the canonical collapsed point. -/
@[simp] theorem realProjectiveSpacePairQuotientRelativeHomotopyGroupMap_apply
    (n : ℕ) (eRP : RPRelativeModel n) (eQuot : RPQuotientRelativeModel n)
    (x : realProjectiveSpacePairRelativeHomotopyGroup n) :
    realProjectiveSpacePairQuotientRelativeHomotopyGroupMap n eRP eQuot x =
      relativeHomotopyGroupEquivOfPathClass eQuot
          ⟦by
            simpa [realProjectiveSpaceEquatorQuotientSingletonBasepoint_eq_image n] using
              Joined.refl (realProjectiveSpaceEquatorQuotientSingletonBasepoint n)
                |>.somePath⟧
          (relativeHomotopyGroupMapOfPairMap eRP eQuot
            (realProjectiveSpaceEquatorQuotientMap n)
            (realProjectiveSpaceEquatorQuotientMap_mapsEquator n)
            (realProjectiveSpaceEquatorBasepoint n)
            x) := rfl

/-- The quotient map `RP^(n + 2) ⟶ RP^(n + 2) / RP^(n + 1)` induces the canonical comparison
homomorphism `π_(n+2)(RP^(n + 2), RP^(n + 1)) ⟶ π_(n+2)(RP^(n + 2) / RP^(n + 1), *)`, relative
to the supplied disk-boundary model comparisons. -/
noncomputable def realProjectiveSpacePairQuotientHomotopyGroupMap
    (n : ℕ) (eRP : RPRelativeModel n) (eQuot : RPQuotientRelativeModel n) :
    realProjectiveSpacePairRelativeHomotopyGroup n →*
      π_ (n + 2)
        (realProjectiveSpaceEquatorQuotient n)
        (realProjectiveSpaceEquatorQuotientBasepoint n) where
  toFun :=
    (piSuccRelativeHomotopyGroupSingletonEquiv
        (n + 1)
        (realProjectiveSpaceEquatorQuotientBasepoint n)).symm ∘
      realProjectiveSpacePairQuotientRelativeHomotopyGroupMap n eRP eQuot
  map_one' := by
    sorry
  map_mul' := by
    sorry

/-- Applying `realProjectiveSpacePairQuotientHomotopyGroupMap` amounts to passing through the
singleton-pair comparison and then using
`(piSuccRelativeHomotopyGroupSingletonEquiv (n + 1) _).symm`. -/
@[simp] theorem realProjectiveSpacePairQuotientHomotopyGroupMap_apply
    (n : ℕ) (eRP : RPRelativeModel n) (eQuot : RPQuotientRelativeModel n)
    (x : realProjectiveSpacePairRelativeHomotopyGroup n) :
    realProjectiveSpacePairQuotientHomotopyGroupMap n eRP eQuot x =
      (piSuccRelativeHomotopyGroupSingletonEquiv
          (n + 1)
          (realProjectiveSpaceEquatorQuotientBasepoint n)).symm
        (realProjectiveSpacePairQuotientRelativeHomotopyGroupMap n eRP eQuot x) := rfl

/-- Problem 9.7.2 (1): writing the source hypothesis `n ≥ 2` as `n + 2`, the pair-relative
homotopy group `π_(n+2)(RP^(n + 2), RP^(n + 1))` is multiplicatively equivalent to
`ℤ × ℤ`. -/
theorem realProjectiveSpacePairRelativeHomotopyGroup_mulEquivIntProd
    (n : ℕ) :
    Nonempty
      (realProjectiveSpacePairRelativeHomotopyGroup n ≃*
        (Multiplicative ℤ × Multiplicative ℤ)) := sorry

/-- Problem 9.7.2 (2): for the canonical quotient model `RP^(n + 2) / RP^(n + 1)`, there is a
quotient-map comparison on `π_(n+2)` that need not be bijective, relative to the supplied
disk-boundary model comparisons. -/
theorem realProjectiveSpacePairQuotientMap_not_piIso
    (n : ℕ) (eRP : RPRelativeModel n) (eQuot : RPQuotientRelativeModel n) :
    ¬ Function.Bijective (realProjectiveSpacePairQuotientHomotopyGroupMap n eRP eQuot) := sorry
