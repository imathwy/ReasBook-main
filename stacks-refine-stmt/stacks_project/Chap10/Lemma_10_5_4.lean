import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open RelSeries Submodule LinearMap

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Two submodules form one cyclic-quotient step when the larger contains the smaller and the
quotient is isomorphic to `R ⧸ I` for some ideal `I`. -/
def IsQuotientEquivQuotient (N₁ N₂ : Submodule R M) : Prop :=
  N₁ ≤ N₂ ∧ ∃ I : Ideal R, Nonempty ((N₂ ⧸ N₁.submoduleOf N₂) ≃ₗ[R] R ⧸ I)

/-- The owner relation series whose successive quotients are cyclic quotients `R ⧸ I`. -/
abbrev CyclicFiltration (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M] :=
  RelSeries {(N₁, N₂) : Submodule R M × Submodule R M | IsQuotientEquivQuotient N₁ N₂}

omit [Module.Finite R M] in
-- Proof sketch: use the map `R → (N ⊔ R x) / N` sending `1` to the class of `x`; its kernel is
-- the ideal of scalars carrying `x` into `N`, and the induced quotient map is an isomorphism.
/-- Adjoining one element to a submodule gives a cyclic-quotient step. -/
private theorem isQuotientEquivQuotient_sup_span (N : Submodule R M) (x : M) :
    IsQuotientEquivQuotient N (N ⊔ span R {x}) := sorry

omit [Module.Finite R M] in
-- Proof sketch: induct on the tuple, starting with the singleton relation series at `⊥` and
-- using `isQuotientEquivQuotient_sup_span` to append the next generated submodule.
/-- A finite tuple of elements yields a cyclic filtration from `0` to the span of the tuple. -/
private theorem exists_relSeries_cyclic_of_tuple :
    ∀ {n : ℕ} (m : Fin n → M),
      ∃ s : CyclicFiltration R M,
        s.head = ⊥ ∧ s.last = span R (Set.range m) := sorry

-- Proof sketch: choose a finite generating family of `M`, build the filtration by adjoining the
-- generators one at a time, and identify each successive quotient with a quotient `R ⧸ I` via the
-- canonical map `R → M / N` sending `1` to the class of the new generator.
/-- Lemma 10.5.4: a finite `R`-module admits a finite filtration
`0 = M₀ ≤ M₁ ≤ ⋯ ≤ Mₙ = M` by finite submodules such that each successive quotient
  `Mᵢ₊₁ / Mᵢ` is linearly isomorphic to a quotient `R ⧸ Iᵢ` of the ring. -/
theorem exists_finite_cyclic_filtration :
    ∃ s : CyclicFiltration R M, s.head = ⊥ ∧ s.last = ⊤ := sorry

end
