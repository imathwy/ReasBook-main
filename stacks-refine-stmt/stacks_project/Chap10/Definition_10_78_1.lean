import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Module

section

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/-- Definition 10.78.1 (1): an `R`-module is locally free if some standard-open cover of
`Spec R` trivializes it as a free module after localization. -/
class LocallyFree : Prop where
  /-- A standard-open cover on which the localized module is free. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M)

/-- Definition 10.78.1 (2): an `R`-module is finite locally free if some standard-open cover of
`Spec R` trivializes it as a finite free module after localization. -/
class FiniteLocallyFree : Prop where
  /-- A standard-open cover on which the localized module is finite free. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s,
        Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Finite (Localization.Away f) (LocalizedModule.Away f M)

/-- Definition 10.78.1 (3): an `R`-module is finite locally free of rank `r` if some
standard-open cover of `Spec R` identifies each localization with the free module
`(Localization.Away f)^r`. -/
class FiniteLocallyFreeOfRank (r : ℕ) : Prop where
  /-- A standard-open cover on which the localized module has constant rank `r`. -/
  exists_standardOpen_cover :
    ∃ s : Set R, Ideal.span s = ⊤ ∧
      ∀ f ∈ s,
        Nonempty
          ((LocalizedModule.Away f M) ≃ₗ[Localization.Away f] (Fin r → Localization.Away f))

variable {R M}

-- Proof sketch: forget the finiteness part of each local finite free trivialization and keep the
-- same standard-open cover.
/-- A finite locally free module is locally free. -/
instance [FiniteLocallyFree R M] : LocallyFree R M := sorry

-- Proof sketch: a local linear equivalence with `(Localization.Away f)^r` gives both freeness and
-- finite generation over `Localization.Away f`, so the same cover witnesses finite local freeness.
/-- A finite locally free module of rank `r` is finite locally free. -/
theorem finiteLocallyFree_ofRank (r : ℕ) [FiniteLocallyFreeOfRank R M r] :
    FiniteLocallyFree R M := sorry

-- Proof sketch: the single standard open `D(1)` covers `Spec R`, and localizing `R` away from `1`
-- gives the rank-one free module over itself.
/-- The free rank-one module `R` is finite locally free of rank `1`. -/
instance : FiniteLocallyFreeOfRank R R 1 := sorry

/-- The free rank-one module `R` is finite locally free. -/
instance : FiniteLocallyFree R R :=
  finiteLocallyFree_ofRank 1

/-- The free rank-one module `R` is locally free. -/
instance : LocallyFree R R := inferInstance

end

end Module
