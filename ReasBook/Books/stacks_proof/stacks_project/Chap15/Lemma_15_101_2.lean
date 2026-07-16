import Mathlib
import Mathlib.CategoryTheory.Functor.OfSequence
import stacks_proof.stacks_project.Chap12.Definition_12_31_2
import stacks_proof.stacks_project.Chap15.Definition_15_59_13
import stacks_proof.stacks_project.Chap15.Definition_15_65_1

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open Opposite

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat A)

/-- Helper for Lemma 15.101.2: the `n`th quotient stage `(A / I^(n+1))[0]` of the derived
ideal-power tower. -/
private abbrev idealPowerQuotientDerivedStage (I : Ideal A) (n : ℕ) : DMod :=
  (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj
    (ModuleCat.of A (A ⧸ I ^ (n + 1)))

/-- Helper for Lemma 15.101.2: the successor map in the derived ideal-power quotient tower. -/
private abbrev idealPowerQuotientDerivedStep (I : Ideal A) (n : ℕ) :
    idealPowerQuotientDerivedStage I (n + 1) ⟶
      idealPowerQuotientDerivedStage I n :=
  (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).map
    (ModuleCat.ofHom
      ((Ideal.Quotient.factorₐ A
          (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap))

/-- Helper for Lemma 15.101.2: the inverse system `((A / I^(n+1))[0])_n` in `D(A)`. -/
private abbrev idealPowerQuotientDerivedInverseSystem (I : Ideal A) : ℕᵒᵖ ⥤ DMod :=
  Functor.ofOpSequence (idealPowerQuotientDerivedStep I)

/-- Helper for Lemma 15.101.2: the derived quotient-tensor tower
`(K ⊗_A^L (A / I^(n+1))[0])_n`. -/
private abbrev idealPowerQuotientTensorDerivedInverseSystem
    (I : Ideal A) (K : DMod) : ℕᵒᵖ ⥤ DMod :=
  idealPowerQuotientDerivedInverseSystem I ⋙ derivedTensorProduct K

/-- Helper for Lemma 15.101.2: the cohomology tower of the quotient-tensor stages. -/
abbrev idealPowerQuotientTensorHomologyInverseSystem
    (I : Ideal A) (K : DMod) (i : ℤ) :
    CategoryTheory.SequentialInverseSystem (ModuleCat A) :=
  (idealPowerQuotientTensorDerivedInverseSystem I K) ⋙ H i

theorem idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    (idealPowerQuotientTensorHomologyInverseSystem I K i).IsMittagLeffler := by
  sorry

/-- Lemma 15.101.2: let `I` be an ideal of the Noetherian ring `A`, let `K ∈ D(A)` be
pseudo-coherent, and for each `n` set `K_n = K \otimes_A^{\mathbf L} A / I^(n+1)`. Then for every
`i : ℤ` the inverse system `(H^i(K_n))_n` is Mittag-Leffler, and the inverse limit of the
quotients `H^i(K) / I^(n+1) H^i(K)` is canonically isomorphic to the inverse limit of
`(H^i(K_n))_n`; equivalently, the `I`-adic completion of `H^i(K)` is canonically isomorphic to
that inverse limit. Lean starts the tower at `n = 0`, corresponding to the textbook power `I^1`.
-/
@[stacks 0EGV]
theorem idealPowerQuotientTensorHomology_isMittagLeffler_and_limit_iso_of_isPseudoCoherent
    (I : Ideal A) (K : DMod) (hK : K.IsPseudoCoherent) (i : ℤ) :
    (idealPowerQuotientTensorHomologyInverseSystem I K i).IsMittagLeffler ∧
      IsIsomorphic
        (ModuleCat.of A (AdicCompletion I ((H i).obj K)))
        (limit (idealPowerQuotientTensorHomologyInverseSystem I K i)) := by
  refine ⟨idealPowerQuotientTensorHomology_isMittagLeffler_of_isPseudoCoherent I K hK i, ?_⟩
  sorry

end
