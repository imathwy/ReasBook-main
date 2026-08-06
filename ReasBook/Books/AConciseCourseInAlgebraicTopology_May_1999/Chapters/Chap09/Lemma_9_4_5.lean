import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.HomotopyGroup
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Corollary_3_2_9
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.RealProjectiveSpace
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Lemma_9_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.ZerothHomotopyMap

open TopCat (SphereModel sphereModelHomeomorph)
open scoped TopCat Topology Topology.Homotopy

-- Semantic recall: Chapter 3 owns both the standard double cover `sphereToRealProjectiveSpace`
-- and its continuous-map form `sphereToRealProjectiveSpaceMap`.

private theorem sphere_pathConnectedSpace_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    PathConnectedSpace (𝕊 n) := by
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin (n + 1))) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace]
    have hnat : 1 < n + 1 := by
      simpa using Nat.succ_le_succ hn
    have hcard : 1 < (n + 1 : Cardinal) := by
      exact_mod_cast hnat
    simpa using hcard
  let _ : PathConnectedSpace (SphereModel n) := by
    exact isPathConnected_iff_pathConnectedSpace.mp <|
      by
        simpa [SphereModel] using
          (isPathConnected_sphere
            hdim
            (0 : EuclideanSpace ℝ (Fin (n + 1)))
            (by norm_num : 0 ≤ (1 : ℝ)))
  rw [pathConnectedSpace_iff_univ]
  have hs : IsPathConnected (Set.univ : Set (SphereModel n)) := isPathConnected_univ
  simpa using ((sphereModelHomeomorph n).symm.isPathConnected_image).2 hs

private theorem realProjectiveSpace_pathConnectedSpace_of_one_le {n : ℕ} (hn : 1 ≤ n) :
    PathConnectedSpace (RealProjectiveSpace n) := by
  let _ : PathConnectedSpace (𝕊 n) := sphere_pathConnectedSpace_of_one_le hn
  exact
    Function.Surjective.pathConnectedSpace
      (Quotient.mk''_surjective : Function.Surjective (sphereToRealProjectiveSpace n))
      ((sphereToRealProjectiveSpace_isCoveringMap n).continuous)

private theorem zerothHomotopy_subsingleton (X : Type*) [TopologicalSpace X]
    [PathConnectedSpace X] :
    Subsingleton (ZerothHomotopy X) := by
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn₂ a b ?_
  intro x y
  exact Quotient.sound (PathConnectedSpace.joined x y)

private theorem pi0_subsingleton (X : Type*) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Subsingleton (π_ 0 X x) := by
  let _ : Subsingleton (ZerothHomotopy X) := zerothHomotopy_subsingleton X
  refine ⟨fun a b ↦ ?_⟩
  apply (HomotopyGroup.pi0EquivZerothHomotopy : π_ 0 X x ≃ ZerothHomotopy X).injective
  exact Subsingleton.elim _ _

/-- Lemma 9.4.5 (1): for `i ≥ 2`, the fundamental group `π_ 1(RP^i)` is cyclic of order two. -/
theorem realProjectiveSpace_pi1_mulEquiv_zmod_two {i : ℕ} (hi : 2 ≤ i)
    (x : RealProjectiveSpace i) :
    Nonempty (π_ 1 (RealProjectiveSpace i) x ≃* Multiplicative (ZMod 2)) := by
  rcases realProjectiveSpace_fundamentalGroup_mulEquiv_zmod_two hi x with ⟨e⟩
  exact ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup x).trans e⟩

/-- Lemma 9.4.5 (2): for `i ≥ 1`, the standard double cover `S^i → RP^i` induces a bijection on
path components. -/
theorem sphereToRealProjectiveSpace_bijective_zerothHomotopyMap {i : ℕ} (hi : 1 ≤ i) :
    Function.Bijective (zerothHomotopyMap (sphereToRealProjectiveSpaceMap i)) := by
  let _ : PathConnectedSpace (𝕊 i) := sphere_pathConnectedSpace_of_one_le hi
  let _ : PathConnectedSpace (RealProjectiveSpace i) :=
    realProjectiveSpace_pathConnectedSpace_of_one_le hi
  let hdom : Subsingleton (ZerothHomotopy (𝕊 i)) := zerothHomotopy_subsingleton (𝕊 i)
  let hcod : Subsingleton (ZerothHomotopy (RealProjectiveSpace i)) :=
    zerothHomotopy_subsingleton (RealProjectiveSpace i)
  refine ⟨?_, ?_⟩
  · intro a b _
    exact Subsingleton.elim a b
  · have hsphere : Nonempty (𝕊 i) := PathConnectedSpace.nonempty
    rcases hsphere with ⟨x⟩
    intro q
    refine ⟨⟦x⟧, ?_⟩
    exact Subsingleton.elim _ q

/-- Companion form of Lemma 9.4.5 (2) in the Chapter 9 owner `π_ 0`. -/
theorem sphereToRealProjectiveSpace_bijective_pi0_homotopyGroupMap {i : ℕ} (hi : 1 ≤ i)
    (x : 𝕊 i) :
    Function.Bijective ((sphereToRealProjectiveSpaceMap i).eStar 0 x) := by
  let _ : PathConnectedSpace (𝕊 i) := sphere_pathConnectedSpace_of_one_le hi
  let _ : PathConnectedSpace (RealProjectiveSpace i) :=
    realProjectiveSpace_pathConnectedSpace_of_one_le hi
  let hdom : Subsingleton (π_ 0 (𝕊 i) x) := pi0_subsingleton (𝕊 i) x
  let hcod : Subsingleton (π_ 0 (RealProjectiveSpace i) ((sphereToRealProjectiveSpaceMap i) x)) :=
    pi0_subsingleton (RealProjectiveSpace i) ((sphereToRealProjectiveSpaceMap i) x)
  refine ⟨?_, ?_⟩
  · intro a b _
    exact Subsingleton.elim a b
  · intro q
    refine ⟨default, ?_⟩
    exact Subsingleton.elim _ q

/-- Lemma 9.4.5 (3): the canonical map on every higher homotopy group induced by the standard
double cover `S^i → RP^i` is bijective. -/
theorem sphereToRealProjectiveSpace_bijective_higherHomotopyGroupMap {i q : ℕ} (hq : 2 ≤ q)
    (x : 𝕊 i) :
    Function.Bijective ((sphereToRealProjectiveSpaceMap i).eStar q x) := by
  simpa using
    (sphereToRealProjectiveSpace_isCoveringMap i).bijective_homotopyGroupMap q hq x
