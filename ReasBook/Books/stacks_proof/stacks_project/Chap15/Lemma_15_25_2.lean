import Mathlib
import StacksProject_2024.Chap15.Lemma_15_25_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open PrimeSpectrum

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Lemma 15.25.2: a finite type algebra admits a surjective finite-variable
polynomial presentation. -/
lemma exists_surjective_mvPolynomial_presentation [Algebra.FiniteType R S] :
    ∃ (n : ℕ) (π : MvPolynomial (Fin n) R →ₐ[R] S),
      Function.Surjective π := by
  -- Proof comment: this is exactly the quotient-presentation characterization of finite type.
  exact
    Algebra.FiniteType.iff_quotient_mvPolynomial''.1
      (inferInstance : Algebra.FiniteType R S)

/-- Helper for Lemma 15.25.2: finite presentation over a surjective polynomial cover upgrades to
finite presentation of the target algebra over the original base ring. -/
lemma algebraFinitePresentation_of_surjective_polynomial_cover
    {n : ℕ}
    (π : MvPolynomial (Fin n) R →ₐ[R] S) (hπ : Function.Surjective π)
    (hPS :
      let P := MvPolynomial (Fin n) R
      let _ : Module P S := Module.compHom S π.toRingHom
      Module.FinitePresentation P S) :
    Algebra.FinitePresentation R S := by
  let P := MvPolynomial (Fin n) R
  letI : Algebra P S := π.toAlgebra
  letI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq fun r ↦ by
    -- Proof comment: the scalar tower is the one induced by the chosen polynomial cover `π`.
    change algebraMap R S r = π (algebraMap R P r)
    exact (π.commutes r).symm
  letI : Module P S := Module.compHom S π.toRingHom
  letI : Module.FinitePresentation P S := by
    -- Proof comment: reinterpret the input as finite presentation over the chosen source ring.
    simpa [P] using hPS
  letI : Algebra.FinitePresentation P S := by
    -- Proof comment: a commutative algebra finitely presented as a module is finitely presented
    -- as an algebra over the same source ring.
    exact Algebra.FinitePresentation.of_finitePresentation P S
  letI : Algebra.FinitePresentation R P := by
    -- Proof comment: the polynomial source ring is finitely presented over `R`.
    simpa [P] using
      (Algebra.FinitePresentation.mvPolynomial_of_finitePresentation
        (R := R) (A := R) (Fin n))
  -- Proof comment: compose the finitely presented polynomial source with the finitely presented
  -- algebra map `P → S`.
  exact Algebra.FinitePresentation.trans R P S

-- Proof sketch: choose a surjection `MvPolynomial (Fin n) R →ₐ[R] S` from the finite-type
-- hypothesis, view `S` as a finite `MvPolynomial (Fin n) R`-module via this quotient, and apply
-- Lemma `15.25.1` to that module. The localized finite-presentation assumption on
-- `Localization.AtPrime p.asIdeal ⊗[R] S` gives the module-theoretic local finite-presentation
-- hypothesis over `MvPolynomial (Fin n) (Localization.AtPrime p.asIdeal)`, and the conclusion
-- identifies `S` as a finitely presented `R`-algebra.
/-- Lemma 15.25.2: if `R → S` is of finite type, `S` is flat over `R`, a finite family of prime
localizations of `R` detects equality, and for every prime `p` of `R` the localized algebra
`Localization.AtPrime p.asIdeal ⊗[R] S` is of finite presentation over `Localization.AtPrime
p.asIdeal`, then `S` is of finite presentation over `R`. -/
@[stacks 053B]
theorem finitePresentation_of_flat_of_finiteType_of_localizedAtPrimes_finitePresentation
    (hdetect : primeLocalizationsDetectEquality R)
    [Algebra.FiniteType R S] [Module.Flat R S]
    (hloc :
      ∀ p : PrimeSpectrum R,
        Algebra.FinitePresentation (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] S)) :
    Algebra.FinitePresentation R S := by
  obtain ⟨n, π, hπ⟩ := exists_surjective_mvPolynomial_presentation (R := R) (S := S)
  let P := MvPolynomial (Fin n) R
  letI : Algebra P S := π.toAlgebra
  letI : Module P S := Module.compHom S π.toRingHom
  letI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq fun r ↦ by
    -- Proof comment: the chosen polynomial presentation records the original `R`-algebra
    -- structure on `S`.
    change algebraMap R S r = π (algebraMap R P r)
    exact (π.commutes r).symm
  letI : Module.Finite P S := Module.Finite.of_surjective (Algebra.linearMap P S) hπ
  have hloc' :
      ∀ p : PrimeSpectrum R,
        Module.FinitePresentation
          ((Localization.AtPrime p.asIdeal) ⊗[R] P)
          (((Localization.AtPrime p.asIdeal) ⊗[R] P) ⊗[P] S) := by
    intro p
    let A := Localization.AtPrime p.asIdeal
    let Pp := A ⊗[R] P
    let B := A ⊗[R] S
    let πp : Pp →ₐ[A] B :=
      (Algebra.TensorProduct.map (AlgHom.id A A) π).restrictScalars A
    have hπp : Function.Surjective πp := by
      -- Proof comment: tensoring the fixed surjective polynomial cover with `A = R_p` keeps it
      -- surjective.
      simpa [πp] using
        Algebra.TensorProduct.map_surjective (AlgHom.id A A) π
          (by
            intro a
            exact ⟨a, rfl⟩)
          hπ
    letI : Algebra Pp B := πp.toAlgebra
    have hcompEq : πp.comp (Algebra.ofId A Pp) = Algebra.ofId A B := by
      -- Proof comment: the base-changed cover extends the localized base map `A → B`.
      ext a
      rfl
    have hcomp : (πp.comp (Algebra.ofId A Pp)).FinitePresentation := by
      rw [hcompEq]
      simpa [AlgHom.FinitePresentation] using
        (hloc p : Algebra.FinitePresentation A B)
    have hft : (Algebra.ofId A Pp).FiniteType := by
      -- Proof comment: the localized polynomial ring is still finite type over the localized
      -- base ring.
      simpa [AlgHom.FiniteType] using (inferInstance : Algebra.FiniteType A Pp)
    have hπp_fp : πp.FinitePresentation :=
      AlgHom.FinitePresentation.of_comp_finiteType (Algebra.ofId A Pp) hcomp hft
    letI : Module.Finite Pp B := Module.Finite.of_surjective (Algebra.linearMap Pp B) hπp
    letI : Algebra.FinitePresentation Pp B := by
      -- Proof comment: `of_comp_finiteType` upgrades the localized cover map itself to a
      -- finitely presented algebra map.
      simpa [AlgHom.FinitePresentation] using hπp_fp
    have hBfp : Module.FinitePresentation Pp B := by
      -- Proof comment: over a finite finitely presented algebra extension, finite presentation
      -- can be checked after restricting scalars.
      exact
        (Module.FinitePresentation.iff_of_finite_finitePresentation
          (R := Pp) (S := B) (M := B)).2
          (inferInstance : Module.FinitePresentation B B)
    let eBase :
        (Pp ⊗[P] S) ≃ₗ[Pp] (B ⊗[S] S) := by
      -- Proof comment: the tensor square built from the chosen global cover is the pushout that
      -- realizes prime-local base change.
      simpa [Pp, B] using
        ((Algebra.IsPushout.cancelBaseChange
          (R := P) (S := Pp) (A := S) (B := B) S).symm)
    let eRid : (B ⊗[S] S) ≃ₗ[Pp] B :=
      (TensorProduct.rid S B).restrictScalars Pp
    let eTensor : (Pp ⊗[P] S) ≃ₗ[Pp] B := eBase.trans eRid
    -- Proof comment: transport the finitely presented localized algebra along the canonical
    -- pushout comparison to the exact tensor-module owner used in Lemma `15.25.1`.
    exact Module.FinitePresentation.of_equiv eTensor.symm
  have hPS : Module.FinitePresentation P S := by
    -- Proof comment: Lemma `15.25.1` globalizes the prime-local finite-presentation statements
    -- for the fixed polynomial cover.
    simpa [P] using
      finitePresentation_of_flat_of_localized_finitePresentation
        (R := R) (n := n) (M := S) hdetect hloc'
  -- Proof comment: once `S` is finitely presented over the chosen polynomial cover, the
  -- polynomial cover descends this to finite presentation over `R`.
  exact
    algebraFinitePresentation_of_surjective_polynomial_cover
      (R := R) (S := S) π hπ (by simpa [P] using hPS)

end
