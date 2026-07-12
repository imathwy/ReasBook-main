import Mathlib
import StacksProject_2024.Chap10.Definition_10_136_5

-- Declarations for this item will be appended below by the statement pipeline.

open Polynomial
open scoped TensorProduct

noncomputable section

namespace MvPolynomial

variable (n m : ℕ)

/- Domain-style sampling:
* primary domain: generic factorization maps for monic polynomials in multivariable polynomial
  rings;
* inspected owner declarations:
  - `MvPolynomial.universalFactorizationMap`
  - `MvPolynomial.universalFactorizationMap_freeMonic`
  - `MvPolynomial.finite_universalFactorizationMap`
  - `MvPolynomial.tensorEquivSum`
* best owner abstraction:
  - `source-facing`: the textbook coefficient map
    `ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`
  - `core/canonical`: `MvPolynomial.universalFactorizationMap`
  - `bridge/view`: transport of that owner across `MvPolynomial.tensorEquivSum`
* primitive vs. derived:
  - primitive data: only `n`, `m`, and the canonical owner map
  - derived API: the source-facing sum-variable realization `genericFactorizationMap` and its
    consequences below
-/
/-- The textbook coefficient map
`ℤ[a₁, …, a_{n+m}] → ℤ[b₁, …, bₙ, c₁, …, cₘ]`, obtained by transporting the canonical owner
`MvPolynomial.universalFactorizationMap` across `MvPolynomial.tensorEquivSum` to the polynomial
ring with variables `Fin n ⊕ Fin m`. -/
abbrev genericFactorizationMap :
    MvPolynomial (Fin (n + m)) ℤ →ₐ[ℤ] MvPolynomial (Fin n ⊕ Fin m) ℤ :=
  (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toAlgHom.comp
    (universalFactorizationMap ℤ (n + m) n m rfl)

/-- Helper for Example 10.136.7: transporting the left tensor-factor coefficient map through
`tensorEquivSum` identifies it with the `Sum.inl` variable renaming. -/
lemma tensorEquivSum_comp_includeLeft :
    ((tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingHom.comp
      Algebra.TensorProduct.includeLeftRingHom) =
      (rename Sum.inl).toRingHom := by
  -- The two maps agree on constants and variables, so the `MvPolynomial` extensionality lemma
  -- reduces the comparison to the defining formulas of `tensorEquivSum`.
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-- Helper for Example 10.136.7: transporting the right tensor-factor coefficient map through
`tensorEquivSum` identifies it with the `Sum.inr` variable renaming. -/
lemma tensorEquivSum_comp_includeRight :
    ((tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingHom.comp
      Algebra.TensorProduct.includeRight.toRingHom) =
      (rename Sum.inr).toRingHom := by
  -- The right factor is handled by the symmetric generator computation under `tensorEquivSum`.
  apply MvPolynomial.ringHom_ext
  · intro r
    simp
  · intro i
    simp

/-- The bridge to the canonical owner: the textbook coefficient map sends the generic monic
polynomial of degree `n + m` to the product of the two generic monic factors of degrees `n`
and `m`. -/
theorem genericFactorizationMap_freeMonic :
    (freeMonic ℤ (n + m)).map (genericFactorizationMap n m) =
      ((freeMonic ℤ n).map (rename Sum.inl).toRingHom) *
        ((freeMonic ℤ m).map (rename Sum.inr).toRingHom) := by
  -- Route correction: the tensor-product factorization identity is already canonical in mathlib,
  -- so the remaining work is to transport it across `tensorEquivSum`.
  let e := (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingHom
  have htransport := congrArg (Polynomial.map e)
    (universalFactorizationMap_freeMonic ℤ (n + m) n m rfl)
  have htransport' :
      (freeMonic ℤ (n + m)).map (genericFactorizationMap n m) =
        (((freeMonic ℤ n).map Algebra.TensorProduct.includeLeftRingHom).map e) *
          (((freeMonic ℤ m).map Algebra.TensorProduct.includeRight.toRingHom).map e) := by
    -- First normalize the source side to the displayed coefficient map.
    simpa [genericFactorizationMap, e, Polynomial.map_map, Algebra.TensorProduct.algebraMap_def,
      AlgHom.toRingHom_eq_coe] using htransport
  -- Rewriting the transported coefficient maps with the adapter lemmas yields the displayed map.
  have hleft_map :
      (((freeMonic ℤ n).map Algebra.TensorProduct.includeLeftRingHom).map e) =
        (freeMonic ℤ n).map (rename Sum.inl).toRingHom := by
    -- Combine the two polynomial maps into one composed map and apply the left transport lemma.
    rw [Polynomial.map_map, tensorEquivSum_comp_includeLeft]
  have hright_map :
      (((freeMonic ℤ m).map Algebra.TensorProduct.includeRight.toRingHom).map e) =
        (freeMonic ℤ m).map (rename Sum.inr).toRingHom := by
    -- The right factor is identical after the symmetric transport rewrite.
    rw [Polynomial.map_map, tensorEquivSum_comp_includeRight]
  rw [hleft_map, hright_map] at htransport'
  exact htransport'

/-- Helper for Example 10.136.7: every nonempty fiber of the generic factorization map has Krull
dimension `0`. -/
lemma genericFactorizationMap_fiber_ringKrullDim_eq_zero :
    letI := (genericFactorizationMap n m).toAlgebra
    ∀ p : PrimeSpectrum (MvPolynomial (Fin (n + m)) ℤ),
      Nonempty (PrimeSpectrum (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ))) →
        ringKrullDim (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) = 0 := by
  letI := (genericFactorizationMap n m).toAlgebra
  intro p hp
  have hfinite_map : (genericFactorizationMap n m).Finite := by
    -- Finiteness is transported from the canonical tensor-product model.
    exact RingHom.Finite.comp
      (RingEquiv.finite (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingEquiv)
      (finite_universalFactorizationMap ℤ (n + m) n m rfl)
  letI : Module.Finite (MvPolynomial (Fin (n + m)) ℤ) (MvPolynomial (Fin n ⊕ Fin m) ℤ) :=
    (RingHom.finite_algebraMap).mp hfinite_map
  letI : Module.Finite p.asIdeal.ResidueField
      (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) := inferInstance
  letI : Nontrivial (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.mp hp
  -- A finite algebra over the residue field is Artinian, hence zero-dimensional.
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp <|
    (Module.finite_iff_krullDimLE_zero p.asIdeal.ResidueField
      (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ))).mp inferInstance

/-- Helper for Example 10.136.7: transporting the universal factorization presentation along
`tensorEquivSum` gives a relative global complete intersection presentation for the displayed map. -/
lemma genericFactorizationMap_presentation_isRelativeGlobalCompleteIntersection :
    letI := (genericFactorizationMap n m).toAlgebra
    ∃ P : Algebra.Presentation (MvPolynomial (Fin (n + m)) ℤ)
        (MvPolynomial (Fin n ⊕ Fin m) ℤ) (Fin (n + m)) (Fin (n + m)),
      P.IsRelativeGlobalCompleteIntersection := by
  letI := (genericFactorizationMap n m).toAlgebra
  letI := (universalFactorizationMap ℤ (n + m) n m rfl).toAlgebra
  let P₀ : Algebra.Presentation (MvPolynomial (Fin (n + m)) ℤ)
      (MvPolynomial (Fin n ⊕ Fin m) ℤ) (Fin n ⊕ Fin m) (Fin (n + m)) :=
    ((universalFactorizationMapPresentation ℤ (n + m) n m rfl).toPresentation).ofAlgEquiv
      { __ := tensorEquivSum ℤ (Fin n) (Fin m) ℤ
        commutes' := fun r ↦ rfl }
  let P : Algebra.Presentation (MvPolynomial (Fin (n + m)) ℤ)
      (MvPolynomial (Fin n ⊕ Fin m) ℤ) (Fin (n + m)) (Fin (n + m)) :=
    P₀.reindex (finSumFinEquiv.symm : Fin (n + m) ≃ Fin n ⊕ Fin m) (Equiv.refl _)
  have hdim :
      P.dimension = 0 := by
    -- Transport does not change presentation dimension, and here generators equal relations.
    calc
      P.dimension = P₀.dimension := by
            simpa [P] using P₀.dimension_reindex
              (finSumFinEquiv.symm : Fin (n + m) ≃ Fin n ⊕ Fin m) (Equiv.refl _)
      _ =
          (universalFactorizationMapPresentation ℤ (n + m) n m rfl).toPresentation.dimension := by
            simpa [P₀] using
              ((universalFactorizationMapPresentation ℤ (n + m) n m rfl).toPresentation
                .dimension_ofAlgEquiv
                  { __ := tensorEquivSum ℤ (Fin n) (Fin m) ℤ
                    commutes' := fun r ↦ rfl })
      _ = 0 := by
        simp [Algebra.Presentation.dimension]
  refine ⟨P, ?_⟩
  intro p hp
  -- The fiber calculation is the zero-dimensional part of the textbook argument.
  have hfiber :
      ringKrullDim (p.asIdeal.Fiber (MvPolynomial (Fin n ⊕ Fin m) ℤ)) = 0 :=
    genericFactorizationMap_fiber_ringKrullDim_eq_zero (n := n) (m := m) p hp
  simpa [hdim] using hfiber

-- Proof sketch: use `genericFactorizationMap_freeMonic` to identify the displayed coefficient map
-- with the canonical generic factorization map, and then transport the relative global complete
-- intersection structure across `tensorEquivSum`.
/-- Example 10.136.7: the coefficient ring map sending the coefficients of the generic monic
polynomial of degree `n + m` to the coefficients of the product of generic monic factors of
degrees `n` and `m` is a relative global complete intersection. -/
@[stacks 00SQ]
theorem genericFactorizationMap_isRelativeGlobalCompleteIntersection :
    letI := (genericFactorizationMap n m).toAlgebra
    Algebra.IsRelativeGlobalCompleteIntersection
      (MvPolynomial (Fin (n + m)) ℤ) (MvPolynomial (Fin n ⊕ Fin m) ℤ) := by
  letI := (genericFactorizationMap n m).toAlgebra
  -- Use the transported canonical presentation as the witness required by Definition 10.136.5.
  obtain ⟨P, hP⟩ :=
    genericFactorizationMap_presentation_isRelativeGlobalCompleteIntersection (n := n) (m := m)
  exact Algebra.Presentation.toIsRelativeGlobalCompleteIntersection (P := P) hP

-- Proof sketch: after identifying the displayed coefficient map with the canonical owner via
-- `genericFactorizationMap`, transport finiteness across `tensorEquivSum` and apply
-- `MvPolynomial.finite_universalFactorizationMap`.
/-- The generic factorization coefficient map is finite. -/
theorem genericFactorizationMap_finite :
    (genericFactorizationMap n m).Finite := by
  exact RingHom.Finite.comp
    (RingEquiv.finite (tensorEquivSum ℤ (Fin n) (Fin m) ℤ).toRingEquiv)
    (finite_universalFactorizationMap ℤ (n + m) n m rfl)

end MvPolynomial
