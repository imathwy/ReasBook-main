import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_5_1

open scoped ContinuousMap Topology.Homotopy

universe u v

/-- Any weak equivalence induces bijections on all based homotopy groups. -/
theorem IsWeakEquivalence.bijective_homotopyGroupMap
    {Γ : Type u} {X : Type v} [TopologicalSpace Γ] [TopologicalSpace X]
    {γ : C(Γ, X)} (hγ : IsWeakEquivalence γ) (q : ℕ) (x : Γ) :
    Function.Bijective (homotopyGroupMap γ q x) := by
  simpa using (hγ.isNEquivalence (q + 1)).bijective x (Nat.lt_succ_self q)

/-- ProofStep 10.5.6: a CW approximation of `X` can be chosen so that its comparison map induces
bijections on all based homotopy groups. -/
theorem exists_cwApproximation_bijective_homotopyGroupMap (X : TopCat.{u}) :
    ∃ approx : CWApproximation.{u, u} X,
      ∀ q : ℕ, ∀ x : approx.Γ,
        Function.Bijective (homotopyGroupMap approx.γ q x) := by
  obtain ⟨approx⟩ := exists_cwApproximation X
  have hWeak : IsWeakEquivalence approx.γ := approx.isCWApproximation.toIsWeakEquivalence
  exact ⟨approx, fun q x ↦ hWeak.bijective_homotopyGroupMap q x⟩
