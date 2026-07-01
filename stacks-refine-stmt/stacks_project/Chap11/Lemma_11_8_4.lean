import Mathlib
import stacks_project.Chap11.Lemma_11_5_1
import stacks_project.Chap11.Lemma_11_5_4
import stacks_project.Chap11.Theorem_11_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open Matrix

variable {k : Type u} [Field k]
variable {K : Type v} [DivisionRing K] [Algebra k K] [FiniteDimensional k K]
variable [Algebra.IsCentral k K]
variable {k' : Type w} [Field k'] [Algebra k k'] [FiniteDimensional k k']

/- Layer note: this is `source-facing`. The owner abstraction `CSA` remains the right language for
splitness, but Lemma 11.8.4 is about the division-algebra representative itself, not arbitrary
finite central simple algebras. The proof must therefore pass through a Wedderburn decomposition of
the auxiliary `CSA` from Theorem 11.8.2 and the uniqueness of division representatives from
Lemma 11.5.1, rather than treating `CSA.degree` as a Brauer-class invariant. -/
-- Proof sketch: apply Theorem 11.8.2 to `CSA.mk (AlgCat.of k K)` to obtain a Brauer-equivalent
-- finite central simple algebra `B` containing `k'` with `k`-dimension `[k' : k]^2`. Write `B`
-- as a matrix algebra over a finite central division algebra `D` using Wedderburn. Since `B` is
-- Brauer equivalent to `CSA.mk (AlgCat.of k K)`, Lemma 11.5.1 identifies `D` with `K`; comparing
-- dimensions then shows `[k' : k] = n * (CSA.mk (AlgCat.of k K)).degree` for the matrix size `n`,
-- hence the stated divisibility.
/-- Lemma 11.8.4: the degree of the central simple algebra attached to a finite central skew field
`K/k` divides the degree of every finite splitting field. -/
lemma csa_degree_dvd_finrank_of_splitting_field
    (hk' : (CSA.mk (AlgCat.of k K)).IsSplitBy k') :
    (CSA.mk (AlgCat.of k K)).degree ∣ Module.finrank k k' :=
  by
    let A : CSA.{u, v} k := CSA.mk (AlgCat.of k K)
    rcases (A.isSplitBy_iff_exists_brauerEquivalent_with_subfield_finrank_sq k').1 hk' with
      ⟨B, hAB, _, hdim⟩
    letI : IsArtinianRing B := IsArtinianRing.of_finite k B
    obtain ⟨n, hn, D, hDdiv, hDalg, hDfin, ⟨e⟩⟩ :=
      IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite k B
    letI : DivisionRing D := hDdiv
    letI : Algebra k D := hDalg
    letI : Module.Finite k D := hDfin
    letI : FiniteDimensional k D := inferInstance
    letI : Algebra.IsCentral k (Matrix (Fin n) (Fin n) D) := Algebra.IsCentral.of_algEquiv k B _ e
    letI : Algebra.IsCentral k D := by
      refine ⟨fun x hx ↦ ?_⟩
      have hxM : scalar (Fin n) x ∈ (Subalgebra.center k D).map (scalarAlgHom (Fin n) k) := by
        exact ⟨x, hx, rfl⟩
      rw [← subalgebraCenter_eq_scalarAlgHom_map] at hxM
      obtain ⟨a, ha⟩ := (Algebra.IsCentral.mem_center_iff k).1 hxM
      rw [Algebra.mem_bot]
      refine ⟨a, ?_⟩
      let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
      simpa [i] using (congrArg (fun M : Matrix (Fin n) (Fin n) D ↦ M i i) ha).symm
    have hBD : IsBrauerEquivalent B (CSA.mk (AlgCat.of k D)) := by
      refine ⟨1, n, one_ne_zero, NeZero.ne n, ?_⟩
      exact ⟨((reindexAlgEquiv k B finOneEquiv).trans uniqueAlgEquiv).trans e⟩
    have hKD : Nonempty (K ≃ₐ[k] D) :=
      (division_algebras_are_similar_iff k K D).1 (IsBrauerEquivalent.trans hAB hBD)
    have hfinD : Module.finrank k D = Module.finrank k K := by
      rcases hKD with ⟨eKD⟩
      simpa using (LinearEquiv.finrank_eq eKD.toLinearEquiv).symm
    have hsq : Module.finrank k k' ^ 2 = (n * A.degree) ^ 2 := by
      calc
        Module.finrank k k' ^ 2 = Module.finrank k B := hdim.symm
        _ = Module.finrank k (Matrix (Fin n) (Fin n) D) := LinearEquiv.finrank_eq e.toLinearEquiv
        _ = n * n * Module.finrank k D := by
          simpa using (Module.finrank_matrix k D (Fin n) (Fin n))
        _ = n * n * A.degree ^ 2 := by rw [hfinD, A.degree_sq_eq_finrank]
        _ = (n * A.degree) ^ 2 := by
          simp [pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    refine ⟨n, ?_⟩
    calc
      Module.finrank k k' = Nat.sqrt (Module.finrank k k' ^ 2) := by
        simp [pow_two]
      _ = Nat.sqrt ((n * A.degree) ^ 2) := by rw [hsq]
      _ = n * A.degree := by simp [pow_two]
      _ = A.degree * n := by rw [Nat.mul_comm]

end
