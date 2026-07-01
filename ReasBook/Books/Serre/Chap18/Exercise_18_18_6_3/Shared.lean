import Mathlib
import Serre.RepresentationTheory.RealizableOver

noncomputable section

universe u

namespace Representation

local notation "A5" => alternatingGroup (Fin 5)

/-- Helper for Exercise 18-18.6-3: realizability over a smaller field is preserved by
equivariant isomorphism. -/
theorem isRealizableOver_of_equiv
    {k : Type*} [Field k]
    {k₀ : Type*} [Field k₀] [Algebra k₀ k]
    {G : Type*} [Group G]
    {V : Type u} [AddCommGroup V] [Module k V]
    {W : Type u} [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    (hσ : IsRealizableOver k₀ σ) (e : ρ.Equiv σ) :
    IsRealizableOver k₀ ρ := by
  -- Pull the chosen smaller-field model for `σ` back along the equivariant equivalence.
  rcases hσ with ⟨W₀, _, _, _, σ₀, ⟨e₀⟩⟩
  refine ⟨W₀, inferInstance, inferInstance, inferInstance, σ₀, ?_⟩
  exact ⟨e₀.trans e.symm⟩

/-- Helper for Exercise 18-18.6-3: every multiplicative character `A₅ → Lˣ` is trivial over any
field. -/
theorem alternatingGroup_fin5_units_hom_eq_one_over_any_field
    {L : Type*} [Field L] (χ : A5 →* Lˣ) :
    χ = 1 := by
  -- Route correction: the determinant argument later needs a field-independent trivial-character
  -- owner, so use that `A₅` is perfect rather than a finite-cardinality argument over one field.
  ext g
  have hcomm_top : commutator A5 = ⊤ := by
    simpa using
      (commutator_alternatingGroup_eq_top (α := Fin 5) (by decide :
        5 ≤ Fintype.card (Fin 5)))
  have hker_top : (⊤ : Subgroup A5) ≤ χ.ker := by
    -- Any homomorphism to the abelian group `Lˣ` kills the commutator subgroup.
    rw [← hcomm_top]
    exact Abelianization.commutator_subset_ker χ
  have hgker : g ∈ χ.ker := hker_top (by simp)
  simpa using hgker

end Representation
