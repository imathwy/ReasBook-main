import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Theorem_10_6_1

open CategoryTheory
open SpacePair.Hom

universe u

-- Semantic recall via local Chapter 7 precedent and the `SpacePair` owner:
-- `SpacePair.Hom.Homotopic` is the repository's pair-level owner for homotopies through maps of
-- pairs, while
-- `SpacePair.Hom.IsNEquivalence` records the approximation comparison condition. The source
-- therefore stays on `SpacePair` with CW-pair hypotheses and comparison morphisms between chosen
-- pair approximations.

section

variable {P Q Γ Δ : SpacePair.{u}}
variable [Topology.CWComplex (Set.univ : Set Γ.space)]
variable [Topology.RelCWComplex (Set.univ : Set Γ.space) Γ.subspace]
variable [Topology.CWComplex (Set.univ : Set Δ.space)]
variable [Topology.RelCWComplex (Set.univ : Set Δ.space) Δ.subspace]
variable (qΓ : Γ ⟶ P) (qΔ : Δ ⟶ Q)
variable (f : P ⟶ Q)

/-- Theorem 10.6.2 (1): a map of pairs `f : P ⟶ Q` induces a map between any chosen CW pair
approximations `qΓ : Γ ⟶ P` and `qΔ : Δ ⟶ Q`, in the sense that there is a pair map
`φ : Γ ⟶ Δ` whose composite with `qΔ` is homotopic to `f ∘ qΓ` through maps carrying the
distinguished subspace of `Γ` into that of `Q`. -/
theorem exists_map_between_cwPairApproximations
    (hqΓ : ∀ n : ℕ, SpacePair.Hom.IsNEquivalence n qΓ)
    (hqΔ : ∀ n : ℕ, SpacePair.Hom.IsNEquivalence n qΔ) :
    ∃ φ : Γ ⟶ Δ,
      Homotopic (φ ≫ qΔ) (qΓ ≫ f) := sorry

/-- Theorem 10.6.2 (2): two maps between chosen CW pair approximations of `f : P ⟶ Q` that make
the comparison square commute up to homotopy through maps of pairs are themselves homotopic
through maps carrying the distinguished subspace of `Γ` into that of `Δ`. -/
theorem homotopic_of_maps_between_cwPairApproximations
    (hqΓ : ∀ n : ℕ, SpacePair.Hom.IsNEquivalence n qΓ)
    (hqΔ : ∀ n : ℕ, SpacePair.Hom.IsNEquivalence n qΔ)
    {φ₀ φ₁ : Γ ⟶ Δ} (hφ₀ : Homotopic (φ₀ ≫ qΔ) (qΓ ≫ f))
    (hφ₁ : Homotopic (φ₁ ≫ qΔ) (qΓ ≫ f)) :
    Homotopic φ₀ φ₁ := sorry

end
