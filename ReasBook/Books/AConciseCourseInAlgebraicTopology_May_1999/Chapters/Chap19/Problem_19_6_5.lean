import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Convention_5_2_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap19.Problem_19_6_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open SpacePair
open scoped TensorProduct unitInterval

noncomputable section

universe u v w

-- Semantic recall via `lean_leansearch` did not surface a suspension-specific reduced cup-product
-- owner in the current environment. This file therefore keeps only the suspension-cover geometry
-- needed to reuse the contractible-cover vanishing theorem from Problem 19.6.4, while the main
-- labeled theorem is stated directly on the reduced suspension owner `reducedSuspension Y`.

/-- The reduced suspension `ΣY`, viewed as a based space in `Under (⊤_ TopCat)` via its
distinguished suspension point. -/
abbrev reducedSuspensionUnder (Y : PointedCompactlyGenerated.{u, w}) : Under (⊤_ TopCat.{w}) :=
  PointedCompactlyGenerated.toBasedSpace
    (reducedSuspension Y : PointedCompactlyGenerated.{u, w})

/-- The lower cone in the standard two-cone cover of the reduced suspension `ΣY`. -/
def reducedSuspensionLowerCone
    (Y : PointedCompactlyGenerated.{u, w}) : Set (reducedSuspensionUnder Y).right :=
  { z | ∃ p : Y.toCompactlyGenerated × I, p.2 ≠ 1 ∧ reducedSuspensionMk Y p = z }

/-- The upper cone in the standard two-cone cover of the reduced suspension `ΣY`. -/
def reducedSuspensionUpperCone
    (Y : PointedCompactlyGenerated.{u, w}) : Set (reducedSuspensionUnder Y).right :=
  { z | ∃ p : Y.toCompactlyGenerated × I, p.2 ≠ 0 ∧ reducedSuspensionMk Y p = z }

/-- The distinguished suspension point lies in the lower cone of the standard two-cone cover. -/
theorem underTopBasepoint_mem_reducedSuspensionLowerCone
    (Y : PointedCompactlyGenerated.{u, w}) :
    underTopBasepoint (reducedSuspensionUnder Y) ∈ reducedSuspensionLowerCone Y := sorry

/-- The distinguished suspension point lies in the upper cone of the standard two-cone cover. -/
theorem underTopBasepoint_mem_reducedSuspensionUpperCone
    (Y : PointedCompactlyGenerated.{u, w}) :
    underTopBasepoint (reducedSuspensionUnder Y) ∈ reducedSuspensionUpperCone Y := sorry

/-- The standard lower and upper cones cover the reduced suspension `ΣY`. -/
theorem reducedSuspensionLowerCone_union_upperCone
    (Y : PointedCompactlyGenerated.{u, w}) :
    reducedSuspensionLowerCone Y ∪ reducedSuspensionUpperCone Y = Set.univ := sorry

/-- The lower cone in the standard cover of `ΣY` is open. -/
theorem isOpen_reducedSuspensionLowerCone
    (Y : PointedCompactlyGenerated.{u, w}) :
    IsOpen (reducedSuspensionLowerCone Y) := sorry

/-- The upper cone in the standard cover of `ΣY` is open. -/
theorem isOpen_reducedSuspensionUpperCone
    (Y : PointedCompactlyGenerated.{u, w}) :
    IsOpen (reducedSuspensionUpperCone Y) := sorry

/-- The lower cone in the standard cover of `ΣY` is contractible. -/
instance reducedSuspensionLowerCone_contractible
    (Y : PointedCompactlyGenerated.{u, w}) :
    ContractibleSpace (reducedSuspensionLowerCone Y) := sorry

/-- The upper cone in the standard cover of `ΣY` is contractible. -/
instance reducedSuspensionUpperCone_contractible
    (Y : PointedCompactlyGenerated.{u, w}) :
    ContractibleSpace (reducedSuspensionUpperCone Y) := sorry

/-- The distinguished suspension point lies in the intersection of the standard two-cone cover. -/
theorem underTopBasepoint_mem_reducedSuspensionLowerCone_inter_upperCone
    (Y : PointedCompactlyGenerated.{u, w}) :
    underTopBasepoint (reducedSuspensionUnder Y) ∈
      reducedSuspensionLowerCone Y ∩ reducedSuspensionUpperCone Y := by
  exact ⟨underTopBasepoint_mem_reducedSuspensionLowerCone Y,
    underTopBasepoint_mem_reducedSuspensionUpperCone Y⟩

/-- Problem 19.6.5. Under the same pair-theoretic cup-product compatibility hypotheses used for
Problem 19.6.4, the canonical reduced cup product on `reducedCohomology E` of the reduced
suspension `ΣY` vanishes in positive degrees. -/
theorem reducedCohomology_cup_eq_zero_of_reducedSuspension
    (E : ℤ → (X : TopCat) → Set X → Type v)
    [∀ q (X : TopCat) (S : Set X), AddCommGroup (E q X S)]
    [∀ q (X : TopCat) (S : Set X), Module ℤ (E q X S)]
    {π : Type w} [AddCommGroup π]
    (pairTheory : PairCohomologyTheory π)
    (pairTheoryComparison :
      ∀ (n : ℤ) (X : TopCat.{w}) (S : Set X),
        E n X S ≃ₗ[ℤ] pairTheory.relativeCohomology n X S)
    (theoryCup : PairCohomologyTheory.RelativeCupProductMap pairTheory)
    (cupProduct : RelativeCupProductMap E)
    (hCupTheory :
      relativeCupProductCompatibleWithPairTheory
        E pairTheory pairTheoryComparison theoryCup cupProduct)
    (Y : PointedCompactlyGenerated.{u, w})
    {p q : ℤ} (hp : 0 < p) (hq : 0 < q)
    (α : reducedCohomology E p (reducedSuspensionUnder Y))
    (β : reducedCohomology E q (reducedSuspensionUnder Y)) :
    reducedCohomologyCup E cupProduct
      (reducedSuspensionUnder Y) p q
      (TensorProduct.tmul ℤ α β) = 0 := by
  simpa [reducedCohomologyCup, reducedSuspensionUnder] using
    reducedCohomology_cup_eq_zero_of_contractible_cover
      E pairTheory pairTheoryComparison theoryCup cupProduct hCupTheory
      (reducedSuspensionUnder Y).right
      (reducedSuspensionLowerCone Y) (reducedSuspensionUpperCone Y)
      (reducedSuspensionLowerCone_union_upperCone Y)
      (isOpen_reducedSuspensionLowerCone Y)
      (isOpen_reducedSuspensionUpperCone Y)
      (underTopBasepoint (reducedSuspensionUnder Y))
      (underTopBasepoint_mem_reducedSuspensionLowerCone_inter_upperCone Y)
      hp hq α β
