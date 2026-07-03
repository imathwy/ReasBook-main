import Mathlib
import StacksProject_2024.Chap13.Lemma_13_34_6
import StacksProject_2024.Chap20.«20_38_0_1»
import StacksProject_2024.Chap20.Lemma_20_37_9

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open Opposite
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [IsGrothendieckAbelian.{v} (ringedSpaceModuleCat X)]

-- Proof sketch: apply Lemma `13.34.6` to the canonical comparison map `S.intoLimit`,
-- reducing the claim to showing that the induced map `Q.obj F ⟶ R lim_n τ_{\ge -n} Q.obj F` is
-- an isomorphism in the derived category. The basiswise vanishing hypothesis is exactly the input
-- of Lemma `20.37.9`, which yields that isomorphism.
/-- Lemma 20.38.1: in the situation of `20.38.0.1`, assume every open subset of `X` admits a
covering by opens from `𝓑`, and for each `U ∈ 𝓑` one has `H^p(U, H^q(F^\bullet)) = 0` for
`p > d` and `q < 0`. Then the canonical map `F^\bullet ⟶ I^\bullet` to the inverse-limit complex
of the chosen lower truncation injective system is a quasi-isomorphism. -/
theorem intoCandidateKInjective_quasiIso_of_basiswise_negative_cohomologySheaf_vanishing
    (F : CochainComplex (ringedSpaceModuleCat X) ℤ)
    (S : LowerTruncationResolutionSystem
      (fun A : ringedSpaceModuleCat X ↦ Injective A) F)
    [HasLimit S.diagram]
    (𝓑 : Set (Opens X.carrier))
    (hcover :
      ∀ W : Opens X.carrier, ∃ ι : Type u, ∃ U : ι → Opens X.carrier,
        (∀ i, U i ∈ 𝓑) ∧ iSup U = W)
    (d : ℕ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, d < p →
          ∀ q : ℤ, q < 0 →
            IsZero ((ringedSpaceCohomologySheaf X (Q.obj F) q).H' p U)) :
    QuasiIso S.intoLimit := sorry

end

end AlgebraicGeometry.RingedSpace
