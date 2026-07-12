import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Tactic.StacksAttribute

/- Domain-style sampling for Lemma 15.125.7:
- primary domain: commutative algebra of Bezout domains, valuation rings, and localization.
- sampled owner declarations:
  `IsBezout`,
  `IsLocalization`,
  `ValuationRing.iff_local_bezout_domain`,
  `IsLocalization.AtPrime.isLocalRing`.
- best owner abstraction: `IsLocalization S B` for the source-facing localization statement, with
  `IsBezout` as the property owner and `ValuationRing.iff_local_bezout_domain` as the canonical
  local-domain owner theorem already recalled upstream in Chapter 10.
- primitive-vs-derived split:
  primitive data: a commutative ring `A`, a submonoid `S`, and a commutative `A`-algebra `B`
  equipped with `[IsLocalization S B]`;
  derived API: the localized Bezout theorem and the prime-local valuation-ring instance.

Source/core/bridge triage:
- `source-facing`: `isBezout_localization`;
- `core/canonical`: `IsLocalization`, `IsBezout`, and `ValuationRing`;
- `bridge/view`: `valuationRing_localizationAtPrime_of_isBezout`. -/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

-- Proof sketch: use the owner theorem `IsBezout.iff_span_pair_isPrincipal`. Any two elements of
-- the localization can be written as fractions, and each denominator becomes a unit, so the ideal
-- they generate agrees with the image of the corresponding two-generated ideal upstairs.
/-- Lemma 15.125.7: the localization of a Bezout ring, hence in particular of a Bezout domain, is
again Bezout. -/
@[stacks 0AST]
theorem isBezout_localization
    (A : Type u) [CommRing A] [IsBezout A] (S : Submonoid A)
    (B : Type v) [CommRing B] [Algebra A B] [IsLocalization S B] :
    IsBezout B := by
  rw [IsBezout.iff_span_pair_isPrincipal]
  intro x y
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq S x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq S y
  have hspan :
      Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B) =
        Ideal.map (algebraMap A B) (Ideal.span ({a, b} : Set A)) := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact
          (IsLocalization.mk'_mem_map_algebraMap_iff S B
            (Ideal.span ({a, b} : Set A)) a s).2
            ⟨1, Submonoid.one_mem S, Ideal.subset_span (by simp)⟩
      · exact
          (IsLocalization.mk'_mem_map_algebraMap_iff S B
            (Ideal.span ({a, b} : Set A)) b t).2
            ⟨1, Submonoid.one_mem S, Ideal.subset_span (by simp)⟩
    · refine Ideal.map_le_iff_le_comap.2 ?_
      have ha : algebraMap A B a ∈
          Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B) := by
        exact IsLocalization.mk'_spec' B a s ▸
          (Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B)).mul_mem_left
            (algebraMap A B s) (Ideal.subset_span (by simp))
      have hb : algebraMap A B b ∈
          Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B) := by
        exact IsLocalization.mk'_spec' B b t ▸
          (Ideal.span ({IsLocalization.mk' B a s, IsLocalization.mk' B b t} : Set B)).mul_mem_left
            (algebraMap A B t) (Ideal.subset_span (by simp))
      rw [Ideal.span_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ha
      · exact hb
  have hprincipal :
      (Ideal.map (algebraMap A B) (Ideal.span ({a, b} : Set A))).IsPrincipal :=
    Submodule.IsPrincipal.map_ringHom (algebraMap A B)
      (show (Ideal.span ({a, b} : Set A)).IsPrincipal by infer_instance)
  simpa [hspan] using hprincipal

end

section

-- Proof sketch: prime localizations are local by the owner API `IsLocalization.AtPrime.isLocalRing`;
-- combine that with the generic localized Bezout theorem above and use the canonical
-- valuation-ring owner instance on the canonical local ring `Localization.AtPrime p`.
/-- Every prime localization of a Bezout domain is a valuation ring. -/
theorem valuationRing_localizationAtPrime_of_isBezout
    (A : Type u) [CommRing A] [IsDomain A] [IsBezout A] (p : Ideal A) [p.IsPrime] :
    ValuationRing (Localization.AtPrime p) := by
  letI : IsDomain (Localization.AtPrime p) :=
    IsLocalization.isDomain_of_atPrime (Localization.AtPrime p) p
  letI : IsBezout (Localization.AtPrime p) :=
    isBezout_localization A p.primeCompl (Localization.AtPrime p)
  letI : IsLocalRing (Localization.AtPrime p) :=
    IsLocalization.AtPrime.isLocalRing (Localization.AtPrime p) p
  infer_instance

end
