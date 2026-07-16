import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_65_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_60_1
import StacksProject_2024.stacks_project.Chap15.Lemma_15_76_7

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

/-- Helper for Lemma 15.84.9: localizing a pseudo-coherent `A`-complex at `q` preserves
pseudo-coherence. -/
lemma localized_derivedTensor_isPseudoCoherent
    (q : PrimeSpectrum A) (K : DModA) (hK : K.IsPseudoCoherent) :
    let Aq := Localization.AtPrime q.asIdeal
    let Kq : DerivedCategory (ModuleCat Aq) := K ⊗[A]^L[Aq]
    Kq.IsPseudoCoherent := by
  let Aq := Localization.AtPrime q.asIdeal
  let Kq : DerivedCategory (ModuleCat Aq) := K ⊗[A]^L[Aq]
  -- Proof comment: localization at `q` is derived scalar extension, and pseudo-coherence is
  -- preserved by that base change.
  simpa [Aq, Kq] using derivedTensorWithAlgebra_isPseudoCoherent K hK

/-- Helper for Lemma 15.84.9: the residue-field homology vanishing hypothesis is already stated on
the canonical `R_p`-restriction of the localized complex. -/
lemma localized_base_residueFieldHomology_vanishing
    (p : PrimeSpectrum R) (q : PrimeSpectrum A)
    (hq : Ideal.comap (algebraMap R A) q.asIdeal = p.asIdeal)
    (K : DModA) (a b : ℤ)
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
    let ρp : Localization.AtPrime p.asIdeal →+* Aq :=
      Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) hq.symm
    let Kq : DerivedCategory (ModuleCat Aq) := K ⊗[A]^L[Aq]
    let KqOverRp : DerivedCategory (ModuleCat (Localization.AtPrime p.asIdeal)) :=
      ((ModuleCat.restrictScalars ρp).mapDerivedCategory.obj Kq)
    ∀ i : ℤ, i ∉ Set.Icc a b →
      IsZero
        (primeResidueFieldDerivedHomology
          (closedPoint (Localization.AtPrime p.asIdeal))
          KqOverRp
          i) := by
  let Aq := Localization.AtPrime q.asIdeal
  let ρp : Localization.AtPrime p.asIdeal →+* Aq :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) hq.symm
  let Kq : DerivedCategory (ModuleCat Aq) := K ⊗[A]^L[Aq]
  let KqOverRp : DerivedCategory (ModuleCat (Localization.AtPrime p.asIdeal)) :=
    ((ModuleCat.restrictScalars ρp).mapDerivedCategory.obj Kq)
  -- Proof comment: this is only a rebinding of the source hypothesis to the local notation used
  -- by the proof skeleton.
  simpa [Aq, ρp, Kq, KqOverRp] using hκ

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
    HasTorAmplitudeIn KqOverR (a - (d : ℤ)) b := by
  let P := MvPolynomial (Fin d) R
  let qP : PrimeSpectrum P := PrimeSpectrum.comap π.toRingHom q
  let Rp := Localization.AtPrime p.asIdeal
  let Pq := Localization.AtPrime qP.asIdeal
  let Aq := Localization.AtPrime q.asIdeal
  let ρp : Rp →+* Aq :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R A) hq.symm
  let Kq : DerivedCategory (ModuleCat Aq) := K ⊗[A]^L[Aq]
  let KqOverRp : DerivedCategory (ModuleCat Rp) :=
    ((ModuleCat.restrictScalars ρp).mapDerivedCategory.obj Kq)
  let KqOverR : DModR :=
    ((ModuleCat.restrictScalars
        ((algebraMap A Aq).comp (algebraMap R A))).mapDerivedCategory.obj
      Kq)
  have hKq_isPseudoCoherent : Kq.IsPseudoCoherent := by
    -- Proof comment: name the already-established localization invariance of pseudo-coherence so
    -- the main proof stays aligned with the source reduction.
    simpa [Aq, Kq] using localized_derivedTensor_isPseudoCoherent (R := R) (A := A) q K hK
  have hκ_localized :
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero
          (primeResidueFieldDerivedHomology
            (closedPoint Rp)
            KqOverRp
            i) := by
    -- Proof comment: the source hypothesis already has the right shape after introducing the local
    -- names `Aq`, `ρp`, `Kq`, and `KqOverRp`.
    simpa [Rp, Aq, ρp, Kq, KqOverRp] using
      localized_base_residueFieldHomology_vanishing
        (R := R) (A := A) p q hq K a b hκ
  have hqP :
      Ideal.comap π.toRingHom q.asIdeal = qP.asIdeal := rfl
  -- Route correction: the source proof first localizes the polynomial presentation, applies
  -- Lemma `15.83.8` to replace pseudo-coherence of `K_q` over `A_q` by pseudo-coherence of its
  -- restriction over `P_q`, then applies Lemma `15.78.6` to the local map `R_p → P_q`, and
  -- finally descends tor amplitude to `R` using Lemma `15.67.11`.
  -- TODO: the first blocked step is the localized `15.83.8` application. The source route needs
  -- `[Algebra.FinitePresentation Rp Aq]` (equivalently local finite presentation of `A_q` over
  -- `R_p`) in order to compare pseudo-coherence across the localized surjection `P_q ↠ A_q`.
  -- The current theorem statement only assumes a surjective polynomial presentation and flatness,
  -- so Lean has no way to instantiate that source lemma faithfully.
  let _ := Pq
  let _ := KqOverR
  let _ := hKq_isPseudoCoherent
  let _ := hκ_localized
  let _ := hqP
  sorry

end

end CategoryTheory
