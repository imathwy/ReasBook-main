import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_42_1
import stacks_proof.stacks_project.Chap10.Definition_10_160_1
import stacks_proof.stacks_project.Chap10.Lemma_10_158_7
import stacks_proof.stacks_project.Chap15.Definition_15_37_3
import stacks_proof.stacks_project.Chap15.Lemma_15_37_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

variable (A : Type v) [CommRing A] [IsCompleteLocalRing A]

local notation "κA" => ResidueField A

/- Domain-style sampling for Lemma 15.38.3:
- primary domain: coefficient fields of complete local algebras, obtained by lifting the
  residue-field quotient through adic formal smoothness;
- sampled owner declarations:
  `Algebra.formallySmooth_of_isSeparableOver`,
  `RingHom.formally_smooth_for_adic`,
  `RingHom.exists_continuous_lift_of_formally_smooth_for_adic`,
  `IsLocalRing.residue`;
- best owner abstraction: this lemma is `source-facing`, but its section should be exposed in the
  canonical residue-map owner shape rather than through the derived `IsScalarTower.toAlgHom`
  wrapper;
- primitive data: the complete local `k`-algebra `A` and the separability of `ResidueField A / k`;
- derived API: a coefficient-field section of the canonical residue map `residue A`.

Source/core/bridge triage:
- `source-facing`: existence of a coefficient field in the complete local equal-characteristic case;
- `core/canonical`: `Algebra.FormallySmooth k (ResidueField A)` and the chapter owner
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the adic lifting theorem producing the section of the residue-field quotient.
-/

-- Proof sketch: use Proposition `10.158.9` to upgrade the separability hypothesis on
-- `ResidueField A / k` to formal smoothness of `k → ResidueField A`, then apply Lemma `15.37.2`
-- and Lemma `15.37.5` to the maximal-ideal-adic topology on `A` and the quotient map
-- `A → ResidueField A` to obtain a lift of the identity of `ResidueField A`.
/-- Lemma 15.38.3: if `A` is a complete local `k`-algebra and the residue field extension
`κA / k` is separable in the Stacks Project sense, then the residue map `residue A : A →+* κA`
admits a `k`-algebra section. -/
@[stacks 0C34]
theorem exists_residueField_section_of_isCompleteLocalRing_of_isSeparableOver
    (k : Type u) [Field k] [Algebra k A]
    [Algebra.IsSeparableOver k κA] :
    ∃ φ : κA →ₐ[k] A, (residue A).comp φ = RingHom.id κA := by
  letI : TopologicalSpace κA := ⊥
  letI : DiscreteTopology κA := ⟨rfl⟩
  letI : TopologicalSpace A := Ideal.adicTopology (maximalIdeal A)
  let f : k →+* κA := algebraMap k κA
  have hf : f.formally_smooth_for_adic (⊥ : Ideal κA) := by
    letI : TopologicalSpace k := ⊥
    letI : DiscreteTopology k := ⟨rfl⟩
    let B : RingFilterBasis κA := Ideal.ringFilterBasis (⊥ : Ideal κA)
    letI : TopologicalSpace κA := Ideal.adicTopology (⊥ : Ideal κA)
    letI : IsTopologicalRing κA := by
      change @IsTopologicalRing κA B.topology _
      infer_instance
    letI : TopologicalRing.IsPreadicRing κA :=
      { toIsTopologicalRing := ‹IsTopologicalRing κA›
        exists_ideal_isAdic := ⟨⊥, rfl⟩ }
    rw [RingHom.formally_smooth_for_adic_iff]
    have hfs : (algebraMap k κA).FormallySmooth := by
      rw [RingHom.formallySmooth_algebraMap]
      exact Algebra.formallySmooth_of_isSeparableOver
    simpa [f] using RingHom.FormallySmooth.toTopologically hfs continuous_of_discreteTopology
  have hA : IsAdic (maximalIdeal A) := rfl
  have hS : IsAdic (⊥ : Ideal κA) := by
    rw [is_bot_adic_iff]
    infer_instance
  have hJClosed : IsClosed ((maximalIdeal A : Ideal A) : Set A) := by
    have hOpen : IsOpen ((maximalIdeal A : Ideal A) : Set A) := by
      simpa [pow_one] using (isAdic_iff.mp hA).1 1
    simpa using AddSubgroup.isClosed_of_isOpen (maximalIdeal A).toAddSubgroup hOpen
  let ψ : κA →+* A ⧸ maximalIdeal A := RingHom.id κA
  have hψ : Continuous ψ := continuous_of_discreteTopology
  have hcomm :
      (Ideal.Quotient.mk (maximalIdeal A)).comp (algebraMap k A) = ψ.comp f := by
    ext x
    rfl
  have hpow : ∃ t : ℕ+, maximalIdeal A ^ (t : ℕ) ≤ maximalIdeal A := by
    exact ⟨1, by simpa using (le_rfl : maximalIdeal A ^ (1 : ℕ) ≤ maximalIdeal A)⟩
  have hlift :
      ∃ φ : κA →+* A,
        (Ideal.Quotient.mk (maximalIdeal A)).comp φ = RingHom.id κA ∧
          φ.comp f = algebraMap k A ∧ Continuous φ := by
    exact
      f.exists_continuous_lift_of_formally_smooth_for_adic
        (⊥ : Ideal κA) hf hS
        (maximalIdeal A) (maximalIdeal A) hA hJClosed hpow
        ψ hψ (algebraMap k A) hcomm
  rcases hlift with ⟨φ, hφ, hφk, _⟩
  have hφres : (residue A).comp φ = RingHom.id κA := by
    simpa using hφ
  refine ⟨{ toRingHom := φ, commutes' := DFunLike.congr_fun hφk }, by simpa using hφres⟩

end
