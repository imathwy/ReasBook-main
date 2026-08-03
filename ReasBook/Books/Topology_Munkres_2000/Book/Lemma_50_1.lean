module

public import Mathlib.LinearAlgebra.AffineSpace.Independent

public section

open scoped Affine

/-- Lemma 50.1: If a finite family is affinely independent and `x` does not lie in
its affine span, then appending `x` yields an affinely independent family. -/
lemma AffineIndependent.finSnoc {k V P : Type*} [DivisionRing k] [AddCommGroup V]
    [Module k V] [AffineSpace V P] {n : ℕ} {p : Fin n → P} (hp : AffineIndependent k p)
    {x : P} (hx : x ∉ affineSpan k (Set.range p)) :
    AffineIndependent k (Fin.snoc p x) := by
  let q : Fin (n + 1) → P := Fin.snoc p x
  have hp' : AffineIndependent k (fun i : {j : Fin (n + 1) // j ≠ Fin.last n} ↦ q i) := by
    let e := (finSuccAboveEquiv (Fin.last n)).symm.toEmbedding
    convert hp.comp_embedding e using 1
    ext i
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr i.property
    rw [← hj]
    simp only [q, Fin.snoc_castSucc, Function.comp_apply, e]
    congr
    apply Fin.ext
    simpa [finSuccAboveEquiv_symm_apply_last] using congr_arg Fin.val hj
  refine hp'.affineIndependent_of_notMem_span ?_
  rw [show q '' {i | i ≠ Fin.last n} = Set.range p by
    ext z
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr hi
      exact ⟨j, by simp [q]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨j.castSucc, Fin.castSucc_ne_last j, by simp [q]⟩]
  simpa [q] using hx
