import Mathlib
import StacksProject_2024.Chap20.Lemma_20_40_1

open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}} {ι : Type u} [Finite ι]
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- A family `𝓑` of open subsets of a ringed space covers every open subset if each open `W` is
the supremum of a family of members of `𝓑`. -/
abbrev BasisCoversEveryOpen (X : RingedSpace.{u}) (𝓑 : Set (Opens X.carrier)) : Prop :=
  ∀ W : Opens X.carrier, ∃ κ : Type u, ∃ V : κ → Opens X.carrier,
    (∀ k, V k ∈ 𝓑) ∧ iSup V = W

-- Proof sketch: choose the compatible comparison `τ` from Lemma `20.40.1`. For bounded-below
-- truncations `τ_{\ge -n} F`, Lemma `20.23.6` identifies alternating and ordinary Čech total
-- complexes, and Lemma `20.25.2` computes `RΓ(X, τ_{\ge -n} F)` from the ordinary Čech complex
-- using the basiswise acyclicity of the terms. The cokernel and cohomology-sheaf vanishing
-- hypotheses let one pass to a truncation-limit injective resolution as in Lemma `20.38.1`; the
-- resulting inverse systems are eventually constant in each total degree because the alternating
-- Čech complex is finite. Applying the Milnor-type limit comparison then shows that `τ.app F` is
-- an isomorphism in `D(Ab)`.
/-- Lemma 20.40.2: for a finite open covering `𝒰 : X = \bigcup_{i \in I} U_i` of a ringed space
`(X, \mathcal O_X)`, assume every open subset of `X` is covered by opens from `𝓑`, every finite
intersection `U_{i_0 \ldots i_p}` of members of `𝒰` lies in `𝓑`, and for every `U ∈ 𝓑` and
every `p > 0` the cohomology groups `H^p(U, \mathcal F^q)`,
`H^p(U, \operatorname{Coker}(\mathcal F^{q-1} \to \mathcal F^q))`, and
`H^p(U, H^q(\mathcal F^\bullet))` all vanish. Then there exists a comparison morphism of
Lemma `20.40.1` from the total alternating Čech complex of `\mathcal F^\bullet` to
`R\Gamma(X, \mathcal F^\bullet)` whose component at `\mathcal F^\bullet` is an isomorphism in
`D(\operatorname{Ab})`. -/
theorem exists_moduleAlternatingCechToDerivedGlobalSections_isIso_of_basiswise_acyclicity
    (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = ⊤)
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    (𝓑 : Set (Opens X.carrier))
    (hcover : BasisCoversEveryOpen X 𝓑)
    (hinter :
      ∀ (p : ℕ) (σ : Fin (p + 1) → ι), (⨅ a, 𝒰 (σ a)) ∈ 𝓑)
    (hterm :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ,
            IsZero (((moduleUnderlyingAdditiveSheaf X).obj (F.X q)).H' p U))
    (hcoker :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ,
            IsZero (((moduleUnderlyingAdditiveSheaf X).obj
              (cokernel (F.d (q - 1) q))).H' p U))
    (hcohom :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, 0 < p →
          ∀ q : ℤ,
            IsZero (((moduleUnderlyingAdditiveSheaf X).obj (F.homology q)).H' p U)) :
    ∃ τ :
      moduleAlternatingCechToDerivedFunctor X 𝒰 ⟶
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DerivedCategory (RingedSpace.Modules X)) ⋙
          moduleDerivedGlobalSectionsToAbelian X,
      (∀ K : CochainComplex (RingedSpace.Modules X) ℤ,
        DerivedCategory.Q.map (moduleGlobalSectionsToAlternatingCechTotalMap X 𝒰 K) ≫
            τ.app K =
          moduleGlobalSectionsAsAbelianDerivedUnitApp X K) ∧
        IsIso (τ.app F) := sorry

end AlgebraicGeometry.RingedSpace
