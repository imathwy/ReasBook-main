import Mathlib
import StacksProject_2024.Chap10.Definition_10_112_5
import StacksProject_2024.Chap10.Definition_10_151_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w x

namespace Algebra

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/- Domain triage:
- primary domain: unramified commutative algebra via Kähler differentials, the unramified locus,
  and basic-open neighborhood criteria;
- sampled owner declarations:
  `Algebra.Unramified`,
  `Algebra.IsUnramifiedAt`,
  `Algebra.Unramified.comp`,
  `Algebra.basicOpen_subset_unramifiedLocus_iff`,
  `Algebra.unramifiedAt_iff_isUnramifiedAt`,
  `Algebra.gUnramifiedAt_iff_isUnramifiedAt`;
- best owner abstraction:
  `Algebra.Unramified` for the global notion and `Algebra.IsUnramifiedAt` for the canonical local
  owner, with the chapter's `UnramifiedAt` / `GUnramifiedAt` retained as the source-facing
  basic-open neighborhood predicates;
- primitive data: the algebra map `R → S` and, for the source-facing local notions, a principal
  open `D(g)` carrying the unramified or G-unramified structure;
- derived API: the finite type / finite presentation bridges
  `unramifiedAt_iff_isUnramifiedAt` and `gUnramifiedAt_iff_isUnramifiedAt`.

The finite-presentation clauses in this file are `source-facing`, so they should land in
`GUnramifiedAt`; any `IsUnramifiedAt` reformulation belongs only to the bridge layer.
-/

/- Lemma 10.151.3 (1): the base change of an unramified ring map is unramified. -/
example {R' : Type w} [CommRing R'] [Algebra R R'] [Unramified R S] :
    Unramified R' (R' ⊗[R] S) :=
  inferInstance

-- Proof sketch: combine base change for the owner predicate `Algebra.Unramified` with base change
-- for finite presentation.
/-- Lemma 10.151.3 (2): the base change of a G-unramified ring map is G-unramified. -/
theorem gUnramified_baseChange {R' : Type w} [CommRing R'] [Algebra R R'] [GUnramified R S] :
    GUnramified R' (R' ⊗[R] S) := by
  infer_instance

/- Lemma 10.151.3 (3): the composition of unramified ring maps is unramified. -/
example {T : Type x} [CommRing T] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
    [Unramified R S] [Unramified S T] :
    Unramified R T :=
  Unramified.comp R S T

-- Proof sketch: compose the owner predicate `Algebra.Unramified` via `Algebra.Unramified.comp`,
-- compose finite presentation via `Algebra.FinitePresentation.trans`, and package the two facts.
/-- Lemma 10.151.3 (4): the composition of G-unramified ring maps is G-unramified. -/
theorem gUnramified_comp {T : Type x} [CommRing T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [GUnramified R S] [GUnramified S T] :
    GUnramified R T := by
  letI : Unramified R T := Unramified.comp R S T
  letI : FinitePresentation R T := FinitePresentation.trans R S T
  infer_instance

/- Lemma 10.151.3 (5): any principal localization `R → R_f` is unramified. -/
example (f : R) :
    Unramified R (Localization.Away f) :=
  Unramified.of_isLocalization_Away f

-- Proof sketch: principal localization is unramified by the canonical localization theorem, and
-- `IsLocalization.Away.finitePresentation` supplies finite presentation.
/-- Lemma 10.151.3 (6): any principal localization `R → R_f` is G-unramified. -/
theorem localizationAway_gUnramified (f : R) :
    GUnramified R (Localization.Away f) := by
  infer_instance

-- Proof sketch: the quotient map is surjective, hence formally unramified by the quotient
-- instance, and quotients are finitely generated as algebras over the source.
/-- Lemma 10.151.3 (7): for any ideal `I ⊆ R`, the quotient map `R → R/I` is unramified. -/
theorem quotient_unramified (I : Ideal R) :
    Unramified R (R ⧸ I) := by
  letI : FormallyUnramified R (R ⧸ I) := by infer_instance
  letI : FiniteType R (R ⧸ I) := by infer_instance
  exact {}

-- Proof sketch: combine the quotient unramified map with finite presentation of the quotient map
-- for finitely generated ideals.
/-- Lemma 10.151.3 (8): for any finitely generated ideal `I ⊆ R`, the quotient map `R → R/I` is
G-unramified. -/
theorem quotient_gUnramified_of_fg (I : Ideal R) (hI : I.FG) :
    GUnramified R (R ⧸ I) := by
  letI : Unramified R (R ⧸ I) := quotient_unramified I
  letI : FinitePresentation R R := by infer_instance
  letI : FinitePresentation R (R ⧸ I) := FinitePresentation.quotient hI
  infer_instance

/- Lemma 10.151.3 (9): an étale ring map is unramified. -/
example [Etale R S] :
    Unramified R S :=
  inferInstance

-- Proof sketch: an étale algebra is unramified, and étale algebras are finitely presented.
/-- Lemma 10.151.3 (10): an étale ring map is G-unramified. -/
theorem etale_gUnramified [Etale R S] :
    GUnramified R S := by
  infer_instance

-- Bridge sketch: if the localization of `Ω[S⁄R]` at `q` is zero, then `q` lies in the unramified
-- locus by `Algebra.unramifiedLocus_eq_compl_support`, which is exactly the owner predicate
-- `Algebra.IsUnramifiedAt R q.asIdeal`.
/-- Bridge theorem: vanishing of the localized Kähler differentials gives the canonical local owner
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_kaehlerLocalized
    (q : PrimeSpectrum S) (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    IsUnramifiedAt R q.asIdeal := sorry

-- Proof sketch: under finite type, translate the owner-level conclusion above to the chapter's
-- source-facing local predicate via `Algebra.unramifiedAt_iff_isUnramifiedAt`.
/-- Lemma 10.151.3 (11): if the localization `(Ω[S⁄R])_q` is zero, then `R → S` is unramified at
`q`. -/
theorem unramifiedAt_of_subsingleton_kaehlerLocalized [FiniteType R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerLocalized q hOmega)

-- Proof sketch: first obtain the source-facing unramified-at statement from clause (11); under
-- finite presentation, that same basic-open neighborhood is automatically G-unramified.
/-- Lemma 10.151.3 (12): if `R → S` is of finite presentation and the localization
`(Ω[S⁄R])_q` is zero, then `R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_kaehlerLocalized
    [FinitePresentation R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (LocalizedModule.AtPrime q.asIdeal Ω[S⁄R])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerLocalized q hOmega)

-- Bridge sketch: by Nakayama over the local ring `S_q`, vanishing of
-- `Ω[S⁄R] ⊗[S] κ(q)` is equivalent to vanishing of the localized differential module, so the
-- localized owner-level criterion applies.
/-- Bridge theorem: under finite type, vanishing of `Ω[S⁄R] ⊗[S] κ(q)` gives
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_kaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R])) :
    IsUnramifiedAt R q.asIdeal := sorry

-- Proof sketch: after passing to the canonical owner-level criterion above, translate back to the
-- chapter's source-facing local predicate.
/-- Lemma 10.151.3 (13): if `R → S` is of finite type and
`Ω[S⁄R] ⊗[S] κ(q)` is zero, then `R → S` is unramified at `q`. -/
theorem unramifiedAt_of_subsingleton_kaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerResidueTensor q hOmega)

-- Proof sketch: reduce to the source-facing unramified-at criterion from clause (13); finite
-- presentation then upgrades that basic-open witness to a G-unramified one.
/-- Lemma 10.151.3 (14): if `R → S` is of finite presentation and
`Ω[S⁄R] ⊗[S] κ(q)` is zero, then `R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_kaehlerResidueTensor
    [FinitePresentation R S]
    (q : PrimeSpectrum S) (hOmega : Subsingleton (q.asIdeal.ResidueField ⊗[S] Ω[S⁄R])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_kaehlerResidueTensor q hOmega)

-- Bridge sketch: identify the Kähler differentials of the canonical fiber ring
-- `(q.asIdeal.under R).Fiber S` with the base change of `Ω[S⁄R]`, localize at the canonical fiber
-- prime `fiberPrimeAt R S q`, and reduce to the localized owner-level criterion above.
/-- Bridge theorem: under finite type, the fiber-localized differential criterion gives
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_fiberKaehlerLocalized [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    IsUnramifiedAt R q.asIdeal := sorry

-- Proof sketch: translate the owner-level fiber criterion above to the source-facing local
-- predicate `UnramifiedAt`.
/-- Lemma 10.151.3 (15): if `R → S` is of finite type and the localization of
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)]` at the canonical fiber prime corresponding to `q` is zero, then the
map is unramified at `q`. -/
theorem unramifiedAt_of_subsingleton_fiberKaehlerLocalized [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerLocalized q hOmega)

-- Proof sketch: the source-facing unramified-at criterion from clause (15) becomes
-- G-unramified-at after adding finite presentation.
/-- Lemma 10.151.3 (16): if `R → S` is of finite presentation and the localization of
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)]` at the canonical fiber prime corresponding to `q` is zero, then
`R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_fiberKaehlerLocalized
    [FinitePresentation R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton (LocalizedModule.AtPrime (fiberPrimeAt R S q).asIdeal
        Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerLocalized q hOmega)

-- Bridge sketch: over the local fiber ring, Nakayama identifies vanishing of the residue-field
-- tensor of the fiber differential with vanishing of its localization, so the previous owner-level
-- fiber criterion applies.
/-- Bridge theorem: under finite type, the fiber-residue differential criterion gives
`Algebra.IsUnramifiedAt R q.asIdeal`. -/
theorem isUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton
        ((fiberPrimeAt R S q).asIdeal.ResidueField ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    IsUnramifiedAt R q.asIdeal := sorry

-- Proof sketch: convert the owner-level fiber-residue criterion above to the chapter's
-- source-facing `UnramifiedAt` predicate.
/-- Lemma 10.151.3 (17): if `R → S` is of finite type and
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)] ⊗ κ(\bar q)` is zero at the canonical fiber prime corresponding to
`q`, then the map is unramified at `q`. -/
theorem unramifiedAt_of_subsingleton_fiberKaehlerResidueTensor [FiniteType R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton
        ((fiberPrimeAt R S q).asIdeal.ResidueField ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    UnramifiedAt R S q := by
  exact (unramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor q hOmega)

-- Proof sketch: the source-facing fiber-residue criterion from clause (17) upgrades to the
-- G-unramified-at statement once finite presentation is available.
/-- Lemma 10.151.3 (18): if `R → S` is of finite presentation and
`Ω[κ(q ∩ R) ⊗[R] S⁄κ(q ∩ R)] ⊗ κ(\bar q)` is zero at the canonical fiber prime corresponding to
`q`, then `R → S` is G-unramified at `q`. -/
theorem gUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor
    [FinitePresentation R S]
    (q : PrimeSpectrum S)
    (hOmega :
      Subsingleton
        ((fiberPrimeAt R S q).asIdeal.ResidueField ⊗[(q.asIdeal.under R).Fiber S]
          Ω[(q.asIdeal.under R).Fiber S⁄(q.asIdeal.under R).ResidueField])) :
    GUnramifiedAt R S q := by
  exact (gUnramifiedAt_iff_isUnramifiedAt R S q).2
    (isUnramifiedAt_of_subsingleton_fiberKaehlerResidueTensor q hOmega)

-- Proof sketch: each localization `S_f` is unramified on the corresponding basic open `D(f)`;
-- if the chosen elements generate the unit ideal, these basic opens cover `Spec S`, so
-- unramifiedness descends from the cover.
/-- Lemma 10.151.3 (19): if finitely many principal localizations `S_{g_j}` are unramified and the
elements `g_j` generate the unit ideal, then `R → S` is unramified. -/
theorem unramified_of_localizationAway_cover (s : Finset S)
    (hs : Ideal.span (↑s : Set S) = ⊤)
    (hlocal : ∀ f : s, Unramified R (Localization.Away f.1)) :
    Unramified R S := sorry

-- Proof sketch: finite presentation is local on a principal-open cover, and formal unramifiedness
-- is detected by vanishing of the differential on that same cover, so G-unramifiedness descends.
/-- Lemma 10.151.3 (20): if finitely many principal localizations `S_{g_j}` are G-unramified and
the elements `g_j` generate the unit ideal, then `R → S` is G-unramified. -/
theorem gUnramified_of_localizationAway_cover (s : Finset S)
    (hs : Ideal.span (↑s : Set S) = ⊤)
    (hlocal : ∀ f : s, GUnramified R (Localization.Away f.1)) :
    GUnramified R S := sorry

-- Proof sketch: every prime admits an unramified basic-open neighborhood, so by quasi-compactness
-- of `Spec S` finitely many such opens cover and clause (19) applies.
/-- Lemma 10.151.3 (21): if `R → S` is unramified at every prime of `S`, then `R → S` is
unramified. -/
theorem unramified_of_unramifiedAt
    (hlocal : ∀ q : PrimeSpectrum S, UnramifiedAt R S q) :
    Unramified R S := sorry

-- Proof sketch: under finite type, the source-facing and owner-level local predicates are
-- equivalent at every prime, so clause (21) applies after translating the hypothesis through
-- `Algebra.unramifiedAt_iff_isUnramifiedAt`.
/-- Bridge theorem: for finite type algebras, pointwise `Algebra.IsUnramifiedAt` implies global
`Algebra.Unramified`. -/
theorem unramified_of_isUnramifiedAt [FiniteType R S]
    (hlocal : ∀ q : PrimeSpectrum S, IsUnramifiedAt R q.asIdeal) :
    Unramified R S := by
  exact unramified_of_unramifiedAt
    (fun q ↦ (unramifiedAt_iff_isUnramifiedAt R S q).2 (hlocal q))

-- Proof sketch: the same quasi-compactness argument reduces the pointwise G-unramified
-- neighborhoods to a finite principal-open cover, then clause (20) gives the global result.
/-- Lemma 10.151.3 (22): if `R → S` is G-unramified at every prime of `S`, then `R → S` is
G-unramified. -/
theorem gUnramified_of_gUnramifiedAt
    (hlocal : ∀ q : PrimeSpectrum S, GUnramifiedAt R S q) :
    GUnramified R S := sorry

-- Proof sketch: for finitely presented algebras, the source-facing `GUnramifiedAt` predicate and
-- the canonical owner `Algebra.IsUnramifiedAt` are equivalent primewise, so clause (22) applies.
/-- Bridge theorem: for finitely presented algebras, pointwise `Algebra.IsUnramifiedAt` implies
global `Algebra.GUnramified`. -/
theorem gUnramified_of_isUnramifiedAt [FinitePresentation R S]
    (hlocal : ∀ q : PrimeSpectrum S, IsUnramifiedAt R q.asIdeal) :
    GUnramified R S := by
  exact gUnramified_of_gUnramifiedAt
    (fun q ↦ (gUnramifiedAt_iff_isUnramifiedAt R S q).2 (hlocal q))

-- Proof sketch: choose a finite presentation of `S` over `R`; the relations expressing the
-- vanishing of `Ω[S⁄R]` involve only finitely many coefficients, so they descend to a finitely
-- generated `ℤ`-subalgebra `R₀ ⊆ R` and a finitely presented formally unramified `R₀`-algebra
-- `S₀` whose base change recovers `S`.
/-- Lemma 10.151.3 (23): a G-unramified ring map is obtained by base change from a G-unramified
map of finite type `ℤ`-algebras. -/
theorem exists_gUnramified_approximation_over_Z [GUnramified R S] :
    ∃ (R₀ : Type w) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : FiniteType ℤ R₀)
      (S₀ : Type x) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : GUnramified R₀ S₀)
      (_ : Algebra R₀ R), Nonempty ((R ⊗[R₀] S₀) ≃ₐ[R] S) := sorry

-- Proof sketch: descend a finite type presentation together with the relations forcing the module
-- of Kähler differentials to vanish to finitely many coefficients over a finite type `ℤ`-subalgebra
-- `R₀`; the descended algebra `S₀` is unramified over `R₀`, and the original `S` is recovered as
-- a quotient of its base change to `R`.
/-- Lemma 10.151.3 (24): an unramified ring map is a quotient of a base change of an unramified map
of finite type `ℤ`-algebras. -/
theorem exists_unramified_approximation_over_Z [Unramified R S] :
    ∃ (R₀ : Type w) (_ : CommRing R₀) (_ : Algebra ℤ R₀) (_ : FiniteType ℤ R₀)
      (S₀ : Type x) (_ : CommRing S₀) (_ : Algebra R₀ S₀) (_ : Unramified R₀ S₀)
      (_ : Algebra R₀ R), ∃ φ : R ⊗[R₀] S₀ →ₐ[R] S, Function.Surjective φ := sorry

end Algebra
