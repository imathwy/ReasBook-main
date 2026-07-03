import StacksProject_2024.Chap15.Definition_15_28_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open CategoryTheory
open ModuleCat

section

variable {R : Type u} [CommRing R]

/-- The linear form `(f₁, …, fᵣ) : R^r → R` attached to a finite family `f : Fin r → R`. -/
noncomputable abbrev koszulFamilyLinearMap {r : ℕ} (f : Fin r → R) : (Fin r → R) →ₗ[R] R :=
  Module.piEquiv (Fin r) R R f

-- Proof sketch: `Module.piEquiv` is defined from the standard basis of `Fin r → R`, so evaluating
-- on the `i`th basis vector returns the prescribed coefficient `f i`.
/-- The linear form attached to `f` sends the `i`th standard basis vector of `R^r` to `f i`. -/
theorem koszulFamilyLinearMap_basis {r : ℕ} (f : Fin r → R) (i : Fin r) :
    koszulFamilyLinearMap f (Pi.basisFun R (Fin r) i) = f i := sorry

/-- Definition 15.28.2: the Koszul complex on a finite family `f : Fin r → R` is the Koszul
complex associated to the linear form `(f₁, …, fᵣ) : R^r → R`. -/
noncomputable abbrev koszulComplexOn {r : ℕ} (f : Fin r → R) : ChainComplex (ModuleCat R) ℕ :=
  koszulComplex (koszulFamilyLinearMap f)

/-- The `n`th powered Koszul complex on `(f₁^(n+1), \ldots, fᵣ^(n+1))`, indexed so that stage
`0` is the ordinary Koszul complex on `f`. -/
noncomputable abbrev koszulPowerStage {r : ℕ} (f : Fin r → R) (n : ℕ) :
    ChainComplex (ModuleCat R) ℕ :=
  koszulComplexOn (fun i ↦ f i ^ (n + 1))

/-- The degree `n` object of the Koszul complex on `f` is the `n`th exterior power of `R^r`. -/
theorem koszulComplexOn_X {r : ℕ} (f : Fin r → R) (n : ℕ) :
    (koszulComplexOn f).X n = (ModuleCat.of R (Fin r → R)).exteriorPower n :=
  rfl

end
