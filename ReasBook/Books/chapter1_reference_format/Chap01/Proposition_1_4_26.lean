import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open scoped BigOperators

/-- Proposition 1.4.26: a finite family of subspaces of a finite-dimensional `K`-vector space is
an internal direct sum exactly when the subspaces span the whole space and the dimension of the
ambient space is the sum of their dimensions. -/
-- Proof sketch: for the forward implication, use `DirectSum.IsInternal` to identify `V` with the
-- direct sum `⨁ i, Vₛ i`, then apply `Module.finrank_directSum`. For the converse, the canonical
-- linear map `⨁ i, Vₛ i →ₗ[K] V` is surjective because `⨆ i, Vₛ i = ⊤`, and equality of
-- dimensions forces this map to be injective, hence `DirectSum.IsInternal Vₛ`.
theorem submodule_isInternal_iff_iSup_eq_top_and_finrank_eq_sum_finrank
    {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    {ι : Type w} [Fintype ι] [DecidableEq ι] (Vₛ : ι → Submodule K V) :
    DirectSum.IsInternal Vₛ ↔
      (⨆ i, Vₛ i) = ⊤ ∧ Module.finrank K V = ∑ i, Module.finrank K (Vₛ i) := by
  constructor
  · intro h
    refine ⟨h.submodule_iSup_eq_top, ?_⟩
    let e : DirectSum ι (fun i ↦ Vₛ i) ≃ₗ[K] V :=
      LinearEquiv.ofBijective (DirectSum.coeLinearMap Vₛ) h
    calc
      Module.finrank K V = Module.finrank K (DirectSum ι fun i ↦ Vₛ i) := e.finrank_eq.symm
      _ = ∑ i, Module.finrank K (Vₛ i) := Module.finrank_directSum K (fun i ↦ Vₛ i)
  · rintro ⟨hsup, hdim⟩
    change Function.Bijective (DirectSum.coeLinearMap Vₛ)
    have hsurj : Function.Surjective (DirectSum.coeLinearMap Vₛ) := by
      rw [← LinearMap.range_eq_top, DirectSum.range_coeLinearMap]
      exact hsup
    have hfin : Module.finrank K (DirectSum ι fun i ↦ Vₛ i) = Module.finrank K V := by
      calc
        Module.finrank K (DirectSum ι fun i ↦ Vₛ i) = ∑ i, Module.finrank K (Vₛ i) :=
          Module.finrank_directSum K (fun i ↦ Vₛ i)
        _ = Module.finrank K V := hdim.symm
    exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).2 hsurj, hsurj⟩
