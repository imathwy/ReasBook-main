import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ComplexProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Construction_9_2_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_6_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Theorem_9_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped LinearAlgebra.Projectivization TopCat Topology Topology.Homotopy

local notation "BasedSpace" => Under (⊤_ TopCat)

-- Semantic recall: `HomotopyGroup.Pi` is the canonical owner for `π_ n X x`. Local Chapter 9
-- precedent already fixes `sphereBasepoint n` for `𝕊 n`, and the project uses the standard
-- projectivization model `ℙ ℂ (Fin (n + 1) → ℂ)` for finite-dimensional complex projective space.

/-- The `j`th real coordinate in the `i`th complex slot of `ℂ^(n + 1)` inside
`ℝ^(2 * n + 2)`. -/
def oddSphereCoordinateIndex (n : ℕ) (i : Fin (n + 1)) (j : Fin 2) : Fin (2 * n + 1 + 1) :=
  ⟨(finProdFinEquiv (i, j)).1, by
    have h := (finProdFinEquiv (i, j)).2
    omega⟩

/-- Read the odd sphere `𝕊 (2 * n + 1)` as a unit vector in `ℂ^(n + 1)` by grouping consecutive
real coordinates into real-imaginary pairs. -/
def oddSphereToComplexCoordinates (n : ℕ) (x : 𝕊 (2 * n + 1)) : Fin (n + 1) → ℂ :=
  fun i ↦
    x.down.1 (oddSphereCoordinateIndex n i (0 : Fin 2)) +
      x.down.1 (oddSphereCoordinateIndex n i (1 : Fin 2)) * Complex.I

/-- The complex-coordinate vector underlying a point of the odd sphere is nonzero because the
sphere has radius `1`. -/
def oddSphereToComplexCoordinates_ne_zero (n : ℕ) (x : 𝕊 (2 * n + 1)) :
    oddSphereToComplexCoordinates n x ≠ 0 := by
  intro hzero
  have hxzero : x.down.1 = 0 := by
    ext k
    let kFin : Fin ((n + 1) * 2) := ⟨k.1, by omega⟩
    rcases h_ij : finProdFinEquiv.symm kFin with ⟨i, j⟩
    have hkFin : finProdFinEquiv (i, j) = kFin := by
      simpa [h_ij] using finProdFinEquiv.apply_symm_apply kFin
    have hk : oddSphereCoordinateIndex n i j = k := by
      ext
      simpa [oddSphereCoordinateIndex, kFin] using congrArg Fin.val hkFin
    fin_cases j
    · have hcoord := congrArg (fun f : Fin (n + 1) → ℂ ↦ f i) hzero
      have hre : x.down.1 (oddSphereCoordinateIndex n i 0) = 0 := by
        simpa [oddSphereToComplexCoordinates] using congrArg Complex.re hcoord
      exact hk ▸ hre
    · have hcoord := congrArg (fun f : Fin (n + 1) → ℂ ↦ f i) hzero
      have him : x.down.1 (oddSphereCoordinateIndex n i 1) = 0 := by
        simpa [oddSphereToComplexCoordinates] using congrArg Complex.im hcoord
      exact hk ▸ him
  have hnorm : ‖x.down.1‖ = 1 := mem_sphere_zero_iff_norm.mp x.down.2
  have hzero_norm : (0 : ℝ) = 1 := by
    simp [hxzero] at hnorm
  norm_num at hzero_norm

/-- The odd-sphere point determines a complex line in `ℂ^(n + 1)`, i.e. a point of `CP^n`. -/
def oddSphereToComplexProjectiveSpace (n : ℕ) (x : 𝕊 (2 * n + 1)) : ComplexProjectiveSpace n :=
  Projectivization.mk ℂ (oddSphereToComplexCoordinates n x) <|
    oddSphereToComplexCoordinates_ne_zero n x

/-- The chosen sphere basepoint corresponds to the chosen projective basepoint. -/
theorem oddSphereToComplexCoordinates_sphereBasepoint (n : ℕ) :
    oddSphereToComplexCoordinates n (sphereBasepoint (2 * n + 1)) = Pi.single 0 (1 : ℂ) := by
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [oddSphereToComplexCoordinates, oddSphereCoordinateIndex, sphereBasepoint]
  · simp [oddSphereToComplexCoordinates, oddSphereCoordinateIndex, sphereBasepoint, hi]

/-- The Hopf quotient sends the chosen odd-sphere basepoint to the chosen basepoint of `CP^n`. -/
theorem oddSphereToComplexProjectiveSpace_sphereBasepoint (n : ℕ) :
    oddSphereToComplexProjectiveSpace n (sphereBasepoint (2 * n + 1)) =
      complexProjectiveSpaceBasepoint n := by
  simp [oddSphereToComplexProjectiveSpace, complexProjectiveSpaceBasepoint,
    oddSphereToComplexCoordinates_sphereBasepoint]

/-- The standard Hopf quotient map `𝕊 (2 * n + 1) → CP^n`. -/
def oddSphereToComplexProjectiveSpaceMap (n : ℕ) :
    C(𝕊 (2 * n + 1), ComplexProjectiveSpace n) where
  toFun := oddSphereToComplexProjectiveSpace n
  continuous_toFun := by
    sorry

/-- The odd sphere `𝕊 (2 * n + 1)` viewed as a based space at `sphereBasepoint (2 * n + 1)`. -/
abbrev oddSphereBasedSpace (n : ℕ) : BasedSpace :=
  underTopOfPoint (𝕊 (2 * n + 1)) (sphereBasepoint (2 * n + 1))

/-- The projective space `CP^n` viewed as a based space at `complexProjectiveSpaceBasepoint n`.
-/
abbrev complexProjectiveSpaceBasedSpace (n : ℕ) : BasedSpace :=
  underTopOfPoint (ComplexProjectiveSpace n) (complexProjectiveSpaceBasepoint n)

instance complexProjectiveSpaceBasedSpace_pathConnected (n : ℕ)
    [PathConnectedSpace (ComplexProjectiveSpace n)] :
    PathConnectedSpace (complexProjectiveSpaceBasedSpace n).right :=
  by
    simpa [complexProjectiveSpaceBasedSpace, underTopOfPoint] using
      (inferInstance : PathConnectedSpace (ComplexProjectiveSpace n))

/-- The Hopf quotient as a based map `𝕊 (2 * n + 1) ⟶ CP^n`. -/
def oddSphereToComplexProjectiveSpaceBasedMap (n : ℕ) :
    oddSphereBasedSpace n ⟶ complexProjectiveSpaceBasedSpace n :=
  Under.homMk
    (TopCat.ofHom (oddSphereToComplexProjectiveSpaceMap n))
    (by
      ext u
      exact oddSphereToComplexProjectiveSpace_sphereBasepoint n)

/-- Problem 9.7.3 (1): `CP^0` is a point, so all of its based homotopy groups are trivial. -/
theorem complexProjectiveSpaceZero_homotopyGroup_subsingleton
    (i : ℕ) (x : ComplexProjectiveSpace 0) :
    Subsingleton (π_ i (ComplexProjectiveSpace 0) x) := sorry

/-- Problem 9.7.3 (2): for `1 ≤ n`, the canonical map on fundamental groups induced by the Hopf
quotient `𝕊 (2 * n + 1) → CP^n` is bijective. -/
theorem oddSphereToComplexProjectiveSpace_pi1_bijective {n : ℕ} (hn : 1 ≤ n) :
    Function.Bijective
      ((oddSphereToComplexProjectiveSpaceMap n).eStarMulHomOverEq 0
        (oddSphereToComplexProjectiveSpace_sphereBasepoint n)) := by
  sorry

/-- Problem 9.7.3 (3): for `1 ≤ n`, the long-exact-sequence boundary map attached to the Hopf
quotient is bijective in degree `2`. In the Chapter 9 owner
`FibrationHomotopyLongExactSequence (oddSphereToComplexProjectiveSpaceBasedMap n)`, this is the
named boundary map `les.boundary 0`, whose domain is the loop-space model of `π_ 2(CP^n)` and
whose codomain is `π_ 1` of the Hopf fiber; after identifying that fiber with `S¹`, this is the
source statement `π_ 2(CP^n) ≃ π_ 1(S¹)`. -/
theorem complexProjectiveSpace_pi2_boundary_bijective {n : ℕ} (hn : 1 ≤ n)
    [PathConnectedSpace (ComplexProjectiveSpace n)]
    (les : FibrationHomotopyLongExactSequence (oddSphereToComplexProjectiveSpaceBasedMap n)) :
    Function.Bijective (les.boundary 0) := by
  sorry

/-- Problem 9.7.3 (4): for `1 ≤ n` and every `k : ℕ`, the homotopy group
`π_ (k + 3) (CP^n)` agrees with `π_ (k + 3) (𝕊 (2 * n + 1))`, via the canonical map induced by
the Hopf quotient. -/
theorem oddSphereToComplexProjectiveSpace_pi_geThree_bijective {n k : ℕ} (hn : 1 ≤ n) :
    Function.Bijective
      ((oddSphereToComplexProjectiveSpaceMap n).eStarMulHomOverEq (k + 2)
        (oddSphereToComplexProjectiveSpace_sphereBasepoint n)) := by
  sorry
