import StacksProject_2024.Chap23.Lemma_23_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open DividedPowers

noncomputable section

universe uA uW uC

/- Semantic search note: the shared indexed divided-power polynomial owner now lives upstream in
`Lemma_23_5_1`, and the `Fin t` algebra from that lemma is its specialization. This file keeps
only the new source-facing `Remark 23.5.2` constructions built on that common owner. -/

section

variable (A : Type uA) [CommRing A] (W : Type uW)

/-- The finite divided-power polynomial algebra on the variables indexed by a finite subset
`E ⊆ W`. -/
abbrev finiteSubsetDividedPowerPolynomial (E : Finset W) : Type (max uA uW) :=
  indexedDividedPowerPolynomial A E

variable {A W}

/-- The linear map on finitely supported variable modules induced by an inclusion of finite
subsets. This is the module-level part of the transition map between finite divided-power
polynomial algebras. -/
abbrev finiteSubsetDividedPowerPolynomialLinearMap (E F : Finset W) (hEF : E ⊆ F) :
    (E →₀ A) →ₗ[A] (F →₀ A) :=
  Finsupp.lmapDomain A A (fun e : E ↦ (⟨e.1, hEF e.2⟩ : F))

/-- The finite-subset inclusion sends a basis variable to the same variable viewed in the larger
finite subset. -/
theorem finiteSubsetDividedPowerPolynomialLinearMap_single
    (E F : Finset W) (hEF : E ⊆ F) (e : E) (a : A) :
    finiteSubsetDividedPowerPolynomialLinearMap E F hEF (Finsupp.single e a) =
      Finsupp.single (⟨e.1, hEF e.2⟩ : F) a := by
  simp [finiteSubsetDividedPowerPolynomialLinearMap]

/-- Remark 23.5.2 (1): for finite subsets `E ⊆ F` of the variable set, the transition map
`A⟨x_e : e ∈ E⟩ → A⟨x_f : f ∈ F⟩` is characterized by sending each divided-power generator
`m` to its image under the inclusion of finitely supported variable modules. -/
@[stacks 07H6]
theorem existsUnique_finiteSubsetDividedPowerPolynomialTransition
    (E F : Finset W) (hEF : E ⊆ F) :
    ∃! φ : finiteSubsetDividedPowerPolynomial A W E →ₐ[A]
        finiteSubsetDividedPowerPolynomial A W F,
      ∀ (n : ℕ) (m : E →₀ A),
        φ (DividedPowerAlgebra.dp A n m) =
          DividedPowerAlgebra.dp A n
            (finiteSubsetDividedPowerPolynomialLinearMap E F hEF m) := sorry

/-- Remark 23.5.2 (2): the indexed divided-power polynomial algebra admits divided powers on its
canonical ideal extending `(A, I, γ)` and sending the divided powers of every variable to the
canonical divided-power algebra classes. -/
@[stacks 07H6]
theorem existsUnique_indexedDividedPowerPolynomialDividedPowers
    (I : Ideal A) (γ : DividedPowers I) :
    ∃! δ : DividedPowers (indexedDividedPowerPolynomialIdeal A W I),
      (∀ (n : ℕ) (w : W),
        δ.dpow n (indexedDividedPowerPolynomialVariable A W w) =
          DividedPowerAlgebra.dp A n (Finsupp.single w (1 : A))) ∧
      IsDPMorphism γ δ (algebraMap A (indexedDividedPowerPolynomial A W)) := sorry

/-- Remark 23.5.2 (3): the universal mapping property of
`A⟨x_w : w ∈ W⟩` is analogous to Lemma 23.5.1: a divided-power morphism out of it is uniquely
determined by a divided-power morphism from `(A, I, γ)` and by the chosen target-ideal values of
all indexed variables. -/
@[stacks 07H6]
theorem existsUnique_indexedDividedPowerPolynomialLift
    (I : Ideal A) (γ : DividedPowers I)
    {C : Type uC} [CommRing C] (K : Ideal C) (ε : DividedPowers K)
    (δ : DividedPowers (indexedDividedPowerPolynomialIdeal A W I))
    (hδvar : ∀ (n : ℕ) (w : W),
      δ.dpow n (indexedDividedPowerPolynomialVariable A W w) =
        DividedPowerAlgebra.dp A n (Finsupp.single w (1 : A)))
    (hδbase : IsDPMorphism γ δ (algebraMap A (indexedDividedPowerPolynomial A W)))
    (f : DPMorphism γ ε) (k : W → K) :
    ∃! φ : indexedDividedPowerPolynomial A W →+* C,
      IsIndexedDividedPowerPolynomialLift I γ K ε δ f k φ := sorry

end
