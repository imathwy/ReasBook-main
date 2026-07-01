import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MulAction

variable {A : Type u} {X : Type v} [Group A] [MulAction A X]

/-- Lemma VI.2-extra-1, in owner form: if a subgroup of automorphisms acts pretransitively on a
space and contains the stabilizer of one point, then it is already the full automorphism group. -/
theorem _root_.Subgroup.eq_top_of_isPretransitive_of_stabilizer_le
    (G : Subgroup A) [MulAction.IsPretransitive G X] (x : X)
    (hstab : stabilizer A x ≤ G) :
    G = ⊤ := by
  apply top_unique
  intro g
  obtain ⟨h, hh⟩ := exists_smul_eq G x (g • x)
  have hfix : ((h : A)⁻¹ * g) ∈ stabilizer A x := by
    rw [mem_stabilizer_iff]
    have hh' : (h : A)⁻¹ • (g • x) = x := by
      calc
        (h : A)⁻¹ • (g • x) = (h : A)⁻¹ • (h • x) := by
          simpa using congrArg (fun y ↦ (h : A)⁻¹ • y) hh.symm
        _ = x := by
          exact inv_smul_smul (h : A) x
    simpa [mul_smul] using hh'
  have hmem : ((h : A)⁻¹ * g) ∈ G := hstab hfix
  simpa [mul_assoc] using G.mul_mem h.2 hmem
