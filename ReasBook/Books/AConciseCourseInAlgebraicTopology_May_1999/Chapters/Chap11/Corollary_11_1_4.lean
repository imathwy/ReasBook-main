import Mathlib.CategoryTheory.Category.Pointed
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Construction_8_7_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Lemma_8_3_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap08.Definition_8_5_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_4_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap11.Definition_11_1_1

open CategoryTheory
open scoped Topology Topology.Homotopy

noncomputable section

universe u

local notation "BasedSpace" => CategoryTheory.Under (⊤_ TopCat)

-- Semantic recall via `lean_leansearch`: only the generic owners `HomotopyGroup` and `LoopSpace`
-- surfaced. The verified local Chapter 8/11 owners for this corollary are
-- `homotopyCofiber`, `homotopyFiberToLoopHomotopyCofiber`, and
-- `SpacePair.Hom.IsNEquivalence.relativeBijective`.

variable {X Y : BasedSpace} (f : X ⟶ Y)

/-- The top copy of `X` sitting at time `1` inside the based mapping cylinder `M_f`. -/
abbrev basedMappingCylinderTopSubspace : Set (basedMappingCylinder f).right :=
  Set.range (basedMappingCylinderTopInclusion f).right.hom

/-- The pair `(M_f, X)` consisting of the based mapping cylinder and the top copy of `X`. -/
abbrev basedMappingCylinderPair : SpacePair where
  space := (basedMappingCylinder f).right
  subspace := basedMappingCylinderTopSubspace f

/-- The chosen basepoint of the top copy of `X` inside the based mapping cylinder `M_f`. -/
def basedMappingCylinderTopBasepoint : (basedMappingCylinderPair f).subspace :=
  ⟨(basedMappingCylinderTopInclusion f).right.hom (underTopBasepoint X),
    ⟨underTopBasepoint X, rfl⟩⟩

/-- The pair `(C_f, *)` consisting of the based homotopy cofiber and its basepoint singleton. -/
abbrev basedHomotopyCofiberPair : SpacePair where
  space := (homotopyCofiber f).right
  subspace := basedBasepointSet (homotopyCofiber f)

/-- The canonical map `M_f ⟶ C_f` sends the top copy of `X` in the based mapping cylinder to the
basepoint of the homotopy cofiber. -/
theorem basedMappingCylinderToHomotopyCofiber_maps_topSubspace
    {z : (basedMappingCylinder f).right}
    (hz : z ∈ basedMappingCylinderTopSubspace f) :
    (basedMappingCylinderToHomotopyCofiber f).right.hom z ∈
      (basedHomotopyCofiberPair f).subspace := sorry

/-- The quotient map `M_f ⟶ C_f` induces a map of pairs
`(M_f, basedMappingCylinderTopSubspace f) ⟶ (C_f, *)`. -/
def basedHomotopyCofiberPairMap :
    basedMappingCylinderPair f ⟶ basedHomotopyCofiberPair f where
  hom := (basedMappingCylinderToHomotopyCofiber f).right
  map_subspace' := basedMappingCylinderToHomotopyCofiber_maps_topSubspace f

/-- Companion instance for `basedMap_isNEquivalence_of_nConnected`. -/
instance basedMap_isNEquivalenceOfNConnected (n : ℕ+)
    [NConnectedSpace ((n : ℕ) - 1) X.right]
    [NConnectedSpace ((n : ℕ) - 1) Y.right] :
    IsNEquivalence ((n : ℕ) - 1) f.right.hom := sorry

/-- A based map between `(n - 1)`-connected based spaces is automatically an
`((n : ℕ) - 1)`-equivalence on the underlying unbased spaces. -/
theorem basedMap_isNEquivalence_of_nConnected (n : ℕ+)
    [NConnectedSpace ((n : ℕ) - 1) X.right]
    [NConnectedSpace ((n : ℕ) - 1) Y.right] :
    IsNEquivalence ((n : ℕ) - 1) f.right.hom :=
  inferInstance

/-- Companion instance for `homotopyCofiber_nConnected`. -/
instance homotopyCofiber_nConnectedSpace (n : ℕ+)
    [WellPointedBasedSpace X] [WellPointedBasedSpace Y]
    [NConnectedSpace ((n : ℕ) - 1) X.right]
    [NConnectedSpace ((n : ℕ) - 1) Y.right] :
    NConnectedSpace ((n : ℕ) - 1) (homotopyCofiber f).right := by
  sorry

/-- Corollary 11.1.4 (1): for a based map between `(n - 1)`-connected nondegenerately based
spaces, the homotopy cofiber `C_f` is `(n - 1)`-connected. Here nondegeneracy is recorded by the
canonical `WellPointedBasedSpace` instances on `X` and `Y`, and connectivity is stated on the
underlying space of the Chapter 8 based homotopy cofiber owner. -/
theorem homotopyCofiber_nConnected (n : ℕ+)
    [WellPointedBasedSpace X] [WellPointedBasedSpace Y]
    [NConnectedSpace ((n : ℕ) - 1) X.right]
    [NConnectedSpace ((n : ℕ) - 1) Y.right] :
    NConnectedSpace ((n : ℕ) - 1) (homotopyCofiber f).right :=
  inferInstance

/-- Corollary 11.1.4 (2): for a based map between `(n - 1)`-connected nondegenerately based
spaces, the canonical map of pairs `(M_f, X) ⟶ (C_f, *)` induces a bijection on the Chapter 11
path-space owner of `π_n(M_f, X) → π_n(C_f, *)`, based at the top-copy basepoint coming from the
chosen basepoint of `X`. -/
theorem basedHomotopyCofiberPairMap_relativeHomotopyGroup_bijective (n : ℕ+)
    [WellPointedBasedSpace X] [WellPointedBasedSpace Y]
    [NConnectedSpace ((n : ℕ) - 1) X.right]
    [NConnectedSpace ((n : ℕ) - 1) Y.right] :
    Function.Bijective
      ((basedHomotopyCofiberPairMap f).relativeHomotopyGroupMap n
        (basedMappingCylinderTopBasepoint f)) := by
  let hPair :
      SpacePair.Hom.IsNEquivalence (2 * (n : ℕ) - 1) (basedHomotopyCofiberPairMap f) := by
    sorry
  by_cases h1 : (n : ℕ) = 1
  · sorry
  · have hq : (n : ℕ) < 2 * (n : ℕ) - 1 := by
      sorry
    exact hPair.relativeBijective (basedMappingCylinderTopBasepoint f) hq

/-- Corollary 11.1.4 (3): for a based map between `(n - 1)`-connected nondegenerately based
spaces, the map `η : F_f ⟶ Ω C_f` from Construction 8.7.2 induces a bijection on the Chapter 9
loop-space model of `π_n(C_f)`. -/
theorem homotopyFiberToLoopHomotopyCofiber_homotopyGroup_bijective (n : ℕ+)
    [WellPointedBasedSpace X] [WellPointedBasedSpace Y]
    [NConnectedSpace ((n : ℕ) - 1) X.right]
    [NConnectedSpace ((n : ℕ) - 1) Y.right] :
    Function.Bijective
      (homotopyGroupMap (homotopyFiberToLoopHomotopyCofiber f).right.hom ((n : ℕ) - 1)
        (underTopBasepoint (homotopyFiber f))) := by
  have hRelative := basedHomotopyCofiberPairMap_relativeHomotopyGroup_bijective f n
  sorry
