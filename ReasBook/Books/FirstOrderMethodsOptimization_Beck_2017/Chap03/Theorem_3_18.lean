import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_16
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open Bornology
open scoped BigOperators Pointwise

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.18 is `source-facing` in the chapter extendedRealSubdifferential API. The owner notions
`effective_domain`, `is_convex_function`, `extendedRealSubdifferential`, `intrinsicInterior ℝ`, and
`strongDualSubdifferential` already live upstream, so this file contributes only the
relative-interior qualification for the existing finite-sum rule. Under the qualification
hypothesis, nonemptiness of every effective domain is already forced, so the only primitive
codomain restriction in the main theorem is that no summand takes the value `⊥`. -/
recall effective_domain
recall is_convex_function
recall extendedRealSubdifferential
recall strongDualSubdifferential
recall strongDualSubdifferential_eq_image_subdifferential

-- Proof sketch: the inclusion `⊇` is the weak sum rule obtained by summing subgradient
-- inequalities. For `⊆`, use Rockafellar's conjugate sum theorem under the qualification
-- `(\⋂ i, ri(dom fᵢ)).Nonempty`, choose an optimal decomposition of a conjugate subgradient of the
-- sum, and apply Fenchel--Young equality termwise to show that each component lies in the
-- corresponding extendedRealSubdifferential. The relative-interior qualification already implies every
-- `effective_domain (f i)` is nonempty, so only the no-`⊥` half of properness is primitive data.
/-- Theorem 3.18: if a finite family of convex extended-real-valued functions never takes the
value `-∞` and has nonempty intersection of the relative interiors of its effective domains, then
the extendedRealSubdifferential of the pointwise sum equals the pointwise sum of the individual
subdifferentials at every point. Here the relative interior hypothesis is rendered by
`intrinsicInterior ℝ`. -/
theorem subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
    {m : ℕ} (f : Fin m → E → EReal) (x : E)
    (h_ne_bot : ∀ i : Fin m, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i : Fin m, is_convex_function (f i))
    (hqual : (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (f i))).Nonempty) :
    extendedRealSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x =
      ∑ i : Fin m, extendedRealSubdifferential (f i) x := sorry

private theorem image_finset_sum
    {m : ℕ} (f : Fin m → Set (Module.Dual ℝ E)) :
    (LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) ''
        (∑ i : Fin m, f i) =
      ∑ i : Fin m,
        ((LinearMap.toContinuousLinearMap : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) '' f i) := by
  induction m with
  | zero =>
      ext g
      simp
  | succ m ihm =>
      simp [Fin.sum_univ_succ, ihm, Set.image_add]

/-- The continuous-dual bridge/view of Theorem 3.18. -/
theorem
    strongDualSubdifferential_finset_sum_eq_sum_strongDualSubdifferential_of_nonempty_iInter_relativeInterior
    {m : ℕ} (f : Fin m → E → EReal) (x : E)
    (h_ne_bot : ∀ i : Fin m, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i : Fin m, is_convex_function (f i))
    (hqual : (⋂ i : Fin m, intrinsicInterior ℝ (effective_domain (f i))).Nonempty) :
    strongDualSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x =
      ∑ i : Fin m, strongDualSubdifferential (f i) x := by
  let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  calc
    strongDualSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x =
        e '' extendedRealSubdifferential (fun y ↦ ∑ i : Fin m, f i y) x :=
      strongDualSubdifferential_eq_image_subdifferential _ _
    _ =
        e '' ∑ i : Fin m, extendedRealSubdifferential (f i) x := by
      rw [subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
        f x h_ne_bot hconvex hqual]
    _ =
        ∑ i : Fin m, e '' extendedRealSubdifferential (f i) x :=
      image_finset_sum (fun i ↦ extendedRealSubdifferential (f i) x)
    _ = ∑ i : Fin m, strongDualSubdifferential (f i) x := by
      have himage :
          (fun i : Fin m ↦ e '' extendedRealSubdifferential (f i) x) =
            fun i : Fin m ↦ strongDualSubdifferential (f i) x := by
        funext i
        simpa [e] using (strongDualSubdifferential_eq_image_subdifferential (f i) x).symm
      simp [himage]

end
