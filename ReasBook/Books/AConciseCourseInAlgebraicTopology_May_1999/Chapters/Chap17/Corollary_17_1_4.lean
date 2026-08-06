import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap17.Theorem_17_1_3
import Mathlib.LinearAlgebra.Basis.VectorSpace

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

-- Semantic recall via `lean_leansearch`: `CategoryTheory.isZero_Tor_succ_of_projective` is the
-- canonical Tor-vanishing input. The instance
-- `ModuleCat.projective_of_categoryTheory_projective` supplies the bridge from module-theoretic
-- projectivity. The source-facing corollary is best exposed relative to a chosen
-- `UniversalCoefficientHomologyNaturality R X n`, since Theorem 17.1.3 supplies such a package
-- only existentially.

/-- Over a field, the `Tor(H_n(X), M)` term in the universal coefficient sequence vanishes. -/
theorem universalCoefficientHomologyTorTerm_isZero_of_field
    (R : Type u) [Field R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    IsZero (universalCoefficientHomologyTorTerm R X M n) := by
  letI : Module.Projective R M := inferInstance
  letI : Projective M := inferInstance
  change IsZero (ModuleCat.tor R (X.homology n) M)
  exact ModuleCat.isZero_tor_of_projective_right R (X.homology n) M

instance instIsZeroUniversalCoefficientHomologyTorTermOfField
    (R : Type u) [Field R] (X : ChainComplex (ModuleCat R) ℕ) (M : ModuleCat R) (n : ℕ) :
    IsZero (universalCoefficientHomologyTorTerm R X M n) :=
  universalCoefficientHomologyTorTerm_isZero_of_field R X M n

/-- Corollary 17.1.4. In the nat-indexed convention of Theorem 17.1.3, over a field `R` any
chosen degree-`n + 1` universal coefficient morphism
`(S M).tensorToHomology : H_(n + 1)(X) ⊗ M ⟶ H_(n + 1)(X; M)` is an isomorphism because the
`Tor(H_n(X), M)` term vanishes. -/
theorem universalCoefficientHomologyTensorToHomology_isIso_of_field
    (R : Type u) [Field R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (S : UniversalCoefficientHomologyNaturality R X n) (M : ModuleCat R) :
    IsIso ((S M).tensorToHomology) := by
  let T : ShortComplex (ModuleCat R) := (S M).toShortComplex
  have hT : T.ShortExact := (S M).shortExact
  have hzero : IsZero T.X₃ := by
    change IsZero (universalCoefficientHomologyTorTerm R X M n)
    exact universalCoefficientHomologyTorTerm_isZero_of_field R X M n
  change IsIso T.f
  exact (ShortComplex.ShortExact.isIso_f_iff hT).2 hzero

instance instIsIsoUniversalCoefficientHomologyTensorToHomologyOfField
    (R : Type u) [Field R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (S : UniversalCoefficientHomologyNaturality R X n) (M : ModuleCat R) :
    IsIso ((S M).tensorToHomology) :=
  universalCoefficientHomologyTensorToHomology_isIso_of_field R X n S M

/-- Corollary 17.1.4. For any chosen natural universal coefficient sequence over a field, the
degree-`n + 1` coefficient-homology term is isomorphic to `H_(n + 1)(X) ⊗ M`; the
inverse map is the chosen morphism `(S M).tensorToHomology`. -/
noncomputable def homologyWithCoefficientsIsoTensor_of_field
    (R : Type u) [Field R] (X : ChainComplex (ModuleCat R) ℕ) (n : ℕ)
    (S : UniversalCoefficientHomologyNaturality R X n) (M : ModuleCat R) :
    universalCoefficientHomologyTerm R X M n ≅ universalCoefficientHomologyTensorTerm R X M n :=
  (asIso ((S M).tensorToHomology)).symm
