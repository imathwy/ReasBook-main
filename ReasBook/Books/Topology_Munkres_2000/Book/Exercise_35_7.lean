module

public import Topology_Munkres_2000.Book.Exercise_35_7.LogarithmicSpiral
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.TietzeExtension

public section

universe u v

/- Exercise 35.7 (1): A specific retraction of `ℝ × ℝ` onto the logarithmic spiral. -/
#check LogarithmicSpiral.retraction

/- Exercise 35.7 (1): The logarithmic spiral is a retract of `ℝ × ℝ`. -/
#check LogarithmicSpiral.isRetract

/-- Helper for Exercise 35.7: composing a homeomorphism with an extension of its inverse gives a
left inverse to the inclusion of the homeomorphic subspace. -/
private lemma homeomorphCompExtension_leftInverse {X : Type u} [TopologicalSpace X]
    {Y : Type v} [TopologicalSpace Y] {A : Set X} (e : Y ≃ₜ A) (g : C(X, Y))
    (hg : g.restrict A = (e.symm : C(A, Y))) :
    Function.LeftInverse ((e : C(Y, A)).comp g) Subtype.val := by
  intro a
  -- Evaluate the restriction identity to identify the extension on the closed copy.
  have hga := ContinuousMap.congr_fun hg a
  change g a = e.symm a at hga
  -- The homeomorphism then cancels its inverse at that point.
  change e (g a) = a
  rw [hga]
  exact e.apply_symm_apply a

/-- Helper for Exercise 35.7: a closed subspace homeomorphic to a Tietze extension space is a
retract of a normal ambient space. -/
private lemma closedCopyOfTietzeExtension_isRetract {X : Type u} [TopologicalSpace X]
    [NormalSpace X] {Y : Type v} [TopologicalSpace Y] [TietzeExtension.{u, v} Y]
    {A : Set X} (hA : IsClosed A) (e : Y ≃ₜ A) : Set.IsRetract A := by
  -- Extend the inverse coordinate map from the closed copy to the ambient space.
  obtain ⟨g, hg⟩ := ContinuousMap.exists_restrict_eq hA (e.symm : C(A, Y))
  rw [Set.isRetract_iff]
  -- Composing the extension with the original homeomorphism produces the retraction.
  refine ⟨(e : C(Y, A)).comp g, ?_⟩
  exact homeomorphCompExtension_leftInverse e g hg

/-- Exercise 35.7 (2): Every closed knotted copy of the real axis in Euclidean
three-space is a retract of the ambient space. -/
theorem knottedAxis_isRetract (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsClosed K)
    (e : ℝ ≃ₜ K) : Set.IsRetract K := by
  -- Euclidean space is normal, so the generic closed-copy construction applies directly.
  exact closedCopyOfTietzeExtension_isRetract hK e
