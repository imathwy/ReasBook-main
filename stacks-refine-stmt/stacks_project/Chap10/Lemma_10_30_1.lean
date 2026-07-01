import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

section

variable [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S]

/- Domain-style sampling:
* primary domain: finite type / finite presentation for localized commutative algebras;
* sampled owner declarations:
  `RingHom.FinitePresentation`,
  `RingHom.finitePresentation_algebraMap`,
  `Localization.awayMap`,
  `IsLocalization.Away.finitePresentation`,
  `RingHom.FinitePresentation.comp`;
* best owner abstraction: `RingHom.FinitePresentation` for the canonical comparison map
  `Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)`;
* primitive data: the localizing elements `f : R` and `g : S`, together with the explicit
  localized comparison ring hom `R_f → S_(fg)`;
* derived API: the induced `Algebra.FinitePresentation` statement for the algebra structure coming
  from that comparison map.
-/
/-- Lemma 10.30.1 (00FG): if `R ⊆ S` is an inclusion of domains and `R → S` is of finite type,
then there exist nonzero `f ∈ R` and `g ∈ S` such that the canonical map
`R_f → S_(fg)` is of finite presentation. -/
-- Proof sketch: argue by induction on the number of algebra generators of `S` over `R`.
-- In the one-generator case, represent `S` as `R[x] / q`, choose a nonzero relation of minimal
-- degree, and invert its leading coefficient to obtain a monic polynomial presentation. For more
-- generators, first make the subalgebra on `n - 1` generators finitely presented after localizing,
-- then apply the one-generator step to the final generator and combine the two localizations.
theorem exists_nonzero_localizationAwayProductMap_finitePresentation :
    ∃ (f : R) (_ : f ≠ 0) (g : S) (_ : g ≠ 0),
      (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
        (Localization.awayMap (algebraMap R S) f)) :
          Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)).FinitePresentation := by
  sorry

end

end
