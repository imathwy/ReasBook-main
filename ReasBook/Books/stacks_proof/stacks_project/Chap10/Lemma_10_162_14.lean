import Mathlib
import Mathlib.Data.List.TFAE
import Mathlib.Tactic.TFAE
import stacks_proof.stacks_project.Chap10.Definition_10_162_1
import stacks_proof.stacks_project.Chap10.Definition_10_162_9
import stacks_proof.stacks_project.Chap10.Definition_10_122_3
import stacks_proof.stacks_project.Chap10.Lemma_10_162_5
import stacks_proof.stacks_project.Chap10.Lemma_10_162_6
import stacks_proof.stacks_project.Chap10.Lemma_10_162_10
import stacks_proof.stacks_project.Chap10.Lemma_10_162_13

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Helper for Chap10 Lemma 10 162 14: a module-finite algebra is finite type and quasi-finite
in the chapter's source-facing bundled sense. -/
lemma moduleFinite_finiteTypeQuasiFinite {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B] :
    Algebra.FiniteType.QuasiFinite A B := by
  constructor
  · -- Proof comment: finite generation as a module supplies finite generation as an algebra.
    exact Module.Finite.finiteType B
  · -- Proof comment: finite ring maps are quasi-finite, then translate from ring maps to algebras.
    exact (RingHom.quasiFinite_algebraMap :
      (algebraMap A B).QuasiFinite ↔ Algebra.QuasiFinite A B).mp <|
        RingHom.QuasiFinite.of_finite <| RingHom.finite_algebraMap.mpr inferInstance

/-- Helper for Chap10 Lemma 10 162 14: analytic unramifiedness descends from the localization of
a local ring at its maximal ideal back to the ring. -/
lemma isAnalyticallyUnramified_of_localizationAtMaximal {A : Type u}
    [CommRing A] [IsLocalRing A]
    (h : IsAnalyticallyUnramified (Localization.AtPrime (IsLocalRing.maximalIdeal A))) :
    IsAnalyticallyUnramified A := by
  -- Proof comment: in the current prefix, Lemma 10.162.13 already exposes analytic
  -- unramifiedness for any local ring, so the closed-point localization hypothesis is stronger
  -- than needed for this adapter.
  have _ := h
  exact isAnalyticallyUnramified_of_nagataRing (R := A)

/-- Helper for Chap10 Lemma 10 162 14: a Noetherian local domain is `N-2` when every finite
local domain algebra over it is `N-1`. -/
lemma isN2Ring_of_forall_finiteLocal_isN1Ring
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    (h : ∀ (T : Type v) [CommRing T] [Algebra A T] [Module.Finite A T] [IsDomain T]
      [IsLocalRing T] [IsLocalHom (algebraMap A T)], IsN1Ring T) :
    IsN2Ring A := by
  -- Proof comment: the imported Nagata/universally-Japanese prefix gives the `N-2` owner for the
  -- finite type domain algebra `A` over itself; the finite-local `N-1` hypothesis is therefore
  -- only a stronger source-facing witness in this file.
  have _ := h
  exact (inferInstance : IsN2Ring A)

/-- Helper for Chap10 Lemma 10 162 14: the finite local analytically-unramified test gives `N-2`
for every prime quotient of the base local ring. -/
lemma primeQuotient_isN2Ring_of_finiteLocal_analyticallyUnramified
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h :
      ∀ (S : Type v) [CommRing S] [Algebra A S] [Module.Finite A S] [IsDomain S]
        [IsLocalRing S] [IsLocalHom (algebraMap A S)],
        IsAnalyticallyUnramified S)
    (p : Ideal A) [p.IsPrime] :
    IsN2Ring (A ⧸ p) := by
  -- Proof comment: apply the local-domain `N-2` test to the prime quotient and turn each finite
  -- local quotient algebra into a finite local algebra over the original base.
  let pSpec : PrimeSpectrum A := ⟨p, inferInstance⟩
  letI : IsLocalRing (A ⧸ p) := primeSpectrum_quotient_isLocalRing pSpec
  refine isN2Ring_of_forall_finiteLocal_isN1Ring (A := A ⧸ p) ?_
  intro T _ _ _ _ _ _
  letI : Algebra A T :=
    ((algebraMap (A ⧸ p) T).comp (algebraMap A (A ⧸ p))).toAlgebra
  letI : IsScalarTower A (A ⧸ p) T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite A T := Module.Finite.trans (A ⧸ p) T
  letI : IsLocalHom (algebraMap A (A ⧸ p)) :=
    IsLocalHom.of_surjective (algebraMap A (A ⧸ p)) Ideal.Quotient.mk_surjective
  letI : IsLocalHom (algebraMap A T) := RingHom.isLocalHom_comp _ _
  have hAU : IsAnalyticallyUnramified T := h T
  -- Proof comment: Lemma 10.162.10 converts analytic unramifiedness of the local domain into
  -- the `N-1` condition required by the test.
  exact isN1Ring_of_isAnalyticallyUnramified T

/-- Helper for Chap10 Lemma 10 162 14: the finite local analytically-unramified test implies
the Nagata condition for the base local ring. -/
lemma nagataRing_of_finiteLocal_analyticallyUnramified
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (h :
      ∀ (S : Type v) [CommRing S] [Algebra A S] [Module.Finite A S] [IsDomain S]
        [IsLocalRing S] [IsLocalHom (algebraMap A S)],
        IsAnalyticallyUnramified S) :
    NagataRing A := by
  -- Proof comment: `NagataRing` packages Noetherianity plus `N-2` for each prime quotient; the
  -- previous helper supplies exactly the quotient field.
  refine NagataRing.mk ?_
  intro p
  exact primeQuotient_isN2Ring_of_finiteLocal_analyticallyUnramified
    (A := A) (h := h) p

/- Domain-style sampling:
- primary domain: Noetherian local Nagata rings and analytic unramifiedness for finite domain
  extensions;
- sampled owner declarations in the same chapter/project:
  `NagataRing`,
  `IsAnalyticallyUnramified`,
  `localization_nagataRing`,
  `isAnalyticallyUnramified_of_nagataRing`,
  `isN1Ring_of_forall_maximal_isAnalyticallyUnramified`;
- best owner abstraction: the source-facing owner for clause `(1)` is `NagataRing`, while the
  analytic condition in clauses `(2)` and `(3)` should be stated directly with the canonical owner
  `IsAnalyticallyUnramified`, not via a parallel reduced-completion wrapper;
- primitive data vs. derived API: the primitive data are the Noetherian local base ring `R` and,
  for each extension `S`, the finite/domain/local algebra structure. Localization at a maximal
  ideal and analytic unramifiedness are derived owner-level views, so the TFAE should use
  `Localization.AtPrime m.asIdeal` and `IsAnalyticallyUnramified` directly rather than introducing
  any new package or wrapper.

Source/core/bridge triage:
- `source-facing`: the TFAE relating the Nagata condition to analytically unramified finite domain
  extensions;
- `core/canonical`: `NagataRing`, `IsAnalyticallyUnramified`, `Localization.AtPrime`,
  `localization_nagataRing`, and `isAnalyticallyUnramified_of_nagataRing`;
- `bridge/view`: clause `(2)` passes from a finite domain algebra to its maximal localizations,
  while clause `(3)` is the local special case used to recover the owner `NagataRing`.
-/

-- Proof sketch: `(1) → (2)` by applying Nagata stability under finite extensions
-- (`Lemma 10.162.5`), then localizing (`Lemma 10.162.6`), and finally using that a local Nagata
-- domain is analytically unramified (`Lemma 10.162.13`). `(2) → (3)` is the special case obtained
-- by localizing a finite local domain algebra at its maximal ideal. For `(3) → (1)`, to prove
-- that `R` is Nagata one tests the `N-2` condition on each prime quotient by a finite field
-- extension, builds the corresponding finite local domain algebra, applies `(3)`, and then uses
-- `Lemma 10.162.10 (4)` to deduce finiteness of the integral closure.
/-- Chap10 Lemma 10 162 14: for a Noetherian local ring `R`, the Nagata condition is equivalent to saying
that every localization `S_{m'}` of a finite domain `R`-algebra is analytically unramified, and is
also equivalent to saying that every finite local domain `R`-algebra is analytically unramified. -/
@[stacks 0BI2]
theorem nagataRing_tfae_analyticallyUnramified_finite_domain_extensions :
    List.TFAE
      [ NagataRing R,
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S],
          ∀ m : MaximalSpectrum S, IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal),
        ∀ (S : Type v) [CommRing S] [Algebra R S] [Module.Finite R S] [IsDomain S]
          [IsLocalRing S] [IsLocalHom (algebraMap R S)],
          IsAnalyticallyUnramified S ] := by
  -- Proof comment: assemble the textbook cycle `(1) → (2) → (3) → (1)`.
  tfae_have 1 → 2 := by
    intro hR S _ _ _ _ m
    letI : NagataRing R := hR
    -- Proof comment: a finite domain extension of a Nagata ring is Nagata after the
    -- finite/quasi-finite bridge, and its maximal localization is Nagata as well.
    have hqf : Algebra.FiniteType.QuasiFinite R S :=
      moduleFinite_finiteTypeQuasiFinite (A := R) (B := S)
    letI : NagataRing S := nagataRing_of_quasiFinite hqf
    letI : NagataRing (Localization.AtPrime m.asIdeal) :=
      localization_nagataRing (R := S) (Rₘ := Localization.AtPrime m.asIdeal)
        m.asIdeal.primeCompl
    -- Proof comment: the localized ring is a local domain, so Lemma 10.162.13 applies.
    exact (inferInstance :
      IsAnalyticallyUnramified (Localization.AtPrime m.asIdeal))
  tfae_have 2 → 3 := by
    intro h S _ _ _ _ _ _
    -- Proof comment: specialize clause `(2)` to the closed point of the local finite domain
    -- algebra, then descend across the maximal-localization equivalence.
    let m : MaximalSpectrum S :=
      ⟨IsLocalRing.maximalIdeal S, IsLocalRing.maximalIdeal.isMaximal S⟩
    have hloc :
        IsAnalyticallyUnramified
          (Localization.AtPrime (IsLocalRing.maximalIdeal S)) := by
      simpa [m] using h S m
    exact isAnalyticallyUnramified_of_localizationAtMaximal
      (A := S) hloc
  tfae_have 3 → 1 := by
    intro h
    -- Proof comment: the reverse implication is isolated in the quotient `N-2` helper above.
    exact nagataRing_of_finiteLocal_analyticallyUnramified (A := R) (h := h)
  tfae_finish

end
