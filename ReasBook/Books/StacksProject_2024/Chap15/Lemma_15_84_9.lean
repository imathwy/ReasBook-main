import Mathlib
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Definition_15_67_1
import stacks_project.Chap15.Lemma_15_60_1
import stacks_project.Chap15.Lemma_15_76_7

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open IsLocalRing
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModR" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: pseudo-coherent derived complexes under prime localization and tor-amplitude over
  the base ring;
- sampled owner declarations:
  `derivedTensorWithAlgebra`,
  `primeResidueFieldDerivedHomology`,
  `HasTorAmplitudeIn`,
  `(ModuleCat.restrictScalars _).mapDerivedCategory`;
- best owner abstraction: the source-facing theorem should be stated directly on the canonical
  localized derived object `K ⊗[A]^L[Localization.AtPrime q.asIdeal]`, its restriction of scalars
  to `Localization.AtPrime p.asIdeal` and `R`, and the residue-field-fiber owner
  `primeResidueFieldDerivedHomology`, rather than through parallel local wrapper definitions;
- primitive vs. derived:
  primitive data are the chosen prime pair `p`, `q`, the localization map
  `Localization.localRingHom ...`, and the pseudo-coherent object `K`;
  derived API is the tor-amplitude conclusion for `KqOverR` and the residue-field homology
  vanishing condition for `KqOverRp`.
-/

-- Proof sketch: use the surjective polynomial presentation to view `K` as pseudo-coherent over
-- `R[x_1, …, x_d]`, which lets one reduce to the polynomial ring case by Lemma `15.83.8`. For
-- `R_𝔭 → A_𝔮`, apply Lemma `15.78.6` to the localized complex using the assumed vanishing of
-- `K_𝔮 ⊗_{R_𝔭}^{\mathbf L} κ(\mathfrak p)` outside `[a, b]`; this gives tor-amplitude
-- `[(a - d), b]` over `R_𝔭`. Finally descend the same tor-amplitude bound to `R` by the flatness
-- of `R_𝔭` over `R` via Lemma `15.67.11`.
/-- Lemma 15.84.9: let `A` be an `R`-algebra admitting a surjective polynomial presentation in
`d` variables and flat over `R`. Let `𝔮 ⊂ A` lie over `𝔭 ⊂ R`, and let `K ∈ D(A)` be
pseudo-coherent. If the localized derived fiber
`K_𝔮 \otimes_{R_𝔭}^{\mathbf L} κ(\mathfrak p)` has vanishing homology outside `[a, b]`, then
`K_𝔮`, viewed over `R`, has tor-amplitude in `[a - d, b]`. -/
theorem localized_hasTorAmplitudeIn_over_base_of_pseudoCoherent_of_baseResidueFieldHomology_vanishing
    (d : ℕ) (π : MvPolynomial (Fin d) R →ₐ[R] A) (hπ : Function.Surjective π)
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : Ideal.comap (algebraMap R A) q.asIdeal = p.asIdeal)
    (K : DModA) (a b : ℤ) [Module.Flat R A]
    (hK : K.IsPseudoCoherent)
    (hκ :
      let Aq := Localization.AtPrime q.asIdeal
      let KqOverRp : DerivedCategory (ModuleCat (Localization.AtPrime p.asIdeal)) :=
        ((ModuleCat.restrictScalars
            (Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) hq.symm)).mapDerivedCategory.obj
          (K ⊗[A]^L[Aq]))
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint (Localization.AtPrime p.asIdeal))
            KqOverRp
            i)) :
    let Aq := Localization.AtPrime q.asIdeal
    let KqOverR : DModR :=
      ((ModuleCat.restrictScalars
          ((algebraMap A Aq).comp (algebraMap R A))).mapDerivedCategory.obj
        (K ⊗[A]^L[Aq]))
    HasTorAmplitudeIn KqOverR (a - (d : ℤ)) b := sorry

end

end CategoryTheory
