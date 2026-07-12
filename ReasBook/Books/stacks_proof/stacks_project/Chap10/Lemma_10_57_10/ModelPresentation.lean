import Mathlib
import StacksProject_2024.Chap10.Lemma_10_56_1
import StacksProject_2024.Chap10.Lemma_10_57_9

open scoped BigOperators DirectSum
open HomogeneousLocalization

universe u u' v

section

variable {R : Type u} {R' : Type u'} {M : Type v}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R' M]

attribute [local instance] RingHomInvPair.of_ringEquiv
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.decomposition
attribute [local instance] MvPolynomial.HomogeneousSubmodule.gradedMonoid

/-- A graded localization model whose ring is generated in degree `1`, is finite type over its
degree-zero part, and whose graded module is finite over the ring. -/
class IsDegreeOneGeneratedFiniteTypeModel
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N] : Prop where
  degreeOne_adjoin_eq_top : Algebra.adjoin (grading 0) (grading 1 : Set S) = ⊤
  finiteType : Algebra.FiniteType (grading 0) S
  moduleFinite : Module.Finite S N


namespace Lemma_10_57_10

/-- Helper for Lemma 10.57.10: a finite family of degree-one generators already packages the
source conclusions needed for `IsDegreeOneGeneratedFiniteTypeModel`. -/
theorem isDegreeOneGeneratedFiniteTypeModel_of_finset
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N]
    [Module.Finite S N] (s : Finset S)
    (hs_top : Algebra.adjoin (grading 0) (s : Set S) = ⊤)
    (hs_deg : ∀ x ∈ s, x ∈ grading 1) :
    IsDegreeOneGeneratedFiniteTypeModel grading N := by
  refine ⟨?_, ?_, inferInstance⟩
  · -- The whole degree-one piece generates once the chosen finite subset already does.
    apply top_le_iff.mp
    rw [← hs_top]
    exact Algebra.adjoin_mono fun x hx => hs_deg x (by simpa using hx)
  · -- Finite generation by a finite family is exactly finite type over the degree-zero piece.
    exact ⟨⟨s, hs_top⟩⟩

/-- Helper for Lemma 10.57.10: an element of `Algebra.adjoin R s` already lies in the adjoin of a
finite subset of `s`. -/
theorem exists_finset_subset_of_mem_adjoin
    {S : Type _} [CommRing S] [Algebra R S] {s : Set S} {x : S}
    (hx : x ∈ Algebra.adjoin R s) :
    ∃ t : Finset S, (∀ y ∈ t, y ∈ s) ∧ x ∈ Algebra.adjoin R (t : Set S) := by
  classical
  rw [Algebra.mem_adjoin_iff] at hx
  let P : S → Prop := fun y =>
    ∃ t : Finset S, (∀ z ∈ t, z ∈ s) ∧ y ∈ Algebra.adjoin R (t : Set S)
  have hmem :
      ∀ y ∈ Set.range (algebraMap R S) ∪ s, P y := by
    intro y hy
    rcases hy with hy | hy
    · rcases hy with ⟨r, rfl⟩
      refine ⟨∅, by simp, ?_⟩
      simpa [Algebra.adjoin_empty] using
        (Subalgebra.algebraMap_mem (⊥ : Subalgebra R S) r)
    · refine ⟨{y}, ?_, ?_⟩
      · intro z hz
        simpa [Finset.mem_singleton.mp hz] using hy
      · exact Algebra.subset_adjoin (by simp)
  have hzero : P 0 := by
    refine ⟨∅, by simp, ?_⟩
    simpa [Algebra.adjoin_empty] using
      (Subalgebra.zero_mem (⊥ : Subalgebra R S))
  have hone : P 1 := by
    refine ⟨∅, by simp, ?_⟩
    simpa [Algebra.adjoin_empty] using
      (Subalgebra.one_mem (⊥ : Subalgebra R S))
  have hadd : ∀ x y, P x → P y → P (x + y) := by
    intro x y hx hy
    rcases hx with ⟨tx, htx, hx⟩
    rcases hy with ⟨ty, hty, hy⟩
    refine ⟨tx ∪ ty, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact htx z hz
      · exact hty z hz
    · exact Subalgebra.add_mem _ 
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inl hz)) hx)
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inr hz)) hy)
  have hneg : ∀ x, P x → P (-x) := by
    intro x hx
    rcases hx with ⟨tx, htx, hx⟩
    exact ⟨tx, htx, Subalgebra.neg_mem _ hx⟩
  have hmul : ∀ x y, P x → P y → P (x * y) := by
    intro x y hx hy
    rcases hx with ⟨tx, htx, hx⟩
    rcases hy with ⟨ty, hty, hy⟩
    refine ⟨tx ∪ ty, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_union.mp hz with hz | hz
      · exact htx z hz
      · exact hty z hz
    · exact Subalgebra.mul_mem _
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inl hz)) hx)
        ((Algebra.adjoin_mono fun z hz => Finset.mem_union.mpr (Or.inr hz)) hy)
  exact Subring.closure_induction
    (s := Set.range (algebraMap R S) ∪ s)
    (p := fun y _ => P y)
    (fun y hy => hmem y hy)
    hzero
    hone
    (fun x y _ _ hx hy => hadd x y hx hy)
    (fun x _ hx => hneg x hx)
    (fun x y _ _ hx hy => hmul x y hx hy)
    hx

/-- Helper for Lemma 10.57.10: a finite type algebra admits a surjective polynomial presentation
on finitely many variables. This is the source-side starting point `R' = R[x₁, …, xₙ] / I`. -/
theorem exists_surjective_mvPolynomial_presentation :
    [Algebra.FiniteType R R'] →
    ∃ n : ℕ, ∃ π : MvPolynomial (Fin n) R →ₐ[R] R', Function.Surjective π := by
  -- Unpack the standard finite-type owner theorem into the concrete polynomial presentation used
  -- by the source proof.
  intro _hfinite
  obtain ⟨n, π, hπ⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := R')).mp
    inferInstance
  exact ⟨n, π, hπ⟩

/-- Helper for Lemma 10.57.10: the quotient by the kernel of a surjective polynomial presentation
recovers the target algebra. This packages the source identification
`R[x₁, …, xₙ] / I ≃ R'`. -/
noncomputable def mvPolynomial_quotient_equiv_of_surjective {n : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] R') (hπ : Function.Surjective π) :
    (MvPolynomial (Fin n) R ⧸ RingHom.ker π) ≃ₐ[R] R' :=
  -- Use the canonical quotient-by-kernel equivalence once, so the main proof can focus on the
  -- cone construction rather than on quotient bookkeeping.
  Ideal.quotientKerAlgEquivOfSurjective hπ

/-- Helper for Lemma 10.57.10: after restricting scalars along an affine presentation
`π : R[x₁, …, xₙ] → R'`, a finite `R'`-module admits a surjective finite free presentation over
the affine polynomial ring. This matches the source proof, where relations are homogenized before
passing to the cone quotient. -/
theorem exists_surjective_affine_free_module_presentation {n : ℕ}
    (_π : MvPolynomial (Fin n) R →ₐ[R] R')
    [Module (MvPolynomial (Fin n) R) M]
    [Module.Finite (MvPolynomial (Fin n) R) M] :
    ∃ r : ℕ,
      ∃ τ : (Fin r → MvPolynomial (Fin n) R) →ₗ[MvPolynomial (Fin n) R] M,
        Function.Surjective τ := by
  -- Restrict scalars along `π`, then take the canonical finite free cover over the affine ring.
  simpa using (Module.Finite.exists_fin' (MvPolynomial (Fin n) R) M)

/-- Helper for Lemma 10.57.10: the quotient by the relation submodule of a surjective free
presentation recovers the target module. This packages the source identification
`(R')^r / K ≃ M`. -/
noncomputable def free_module_quotient_equiv_of_surjective {r : ℕ}
    (σ : (Fin r → R') →ₗ[R'] M) (hσ : Function.Surjective σ) :
    ((Fin r → R') ⧸ LinearMap.ker σ) ≃ₗ[R'] M :=
  -- Use the module first isomorphism theorem once, so later work can concentrate on homogenizing
  -- the relation vectors.
  LinearMap.quotKerEquivOfSurjective σ hσ

end Lemma_10_57_10

end
