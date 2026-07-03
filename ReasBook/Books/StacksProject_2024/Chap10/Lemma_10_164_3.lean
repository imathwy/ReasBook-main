import Mathlib
import StacksProject_2024.Chap10.Definition_10_37_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/- Domain triage:
* primary domain: commutative algebra of faithfully flat descent for normal rings;
* sampled owner-style declarations: `IsNormalRing`, `RingHom.FaithfullyFlat`,
  `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective`, and `Localization.localRingHom` together
  with the chapter owner theorem `isNormalRing_of_flat_of_fiber`;
* core/canonical owners: `IsNormalRing` for the target property and `RingHom.FaithfullyFlat` for
  the map property;
* primitive vs. derived API: the primitive inputs are only the ring map `f`, the faithful-flatness
  witness `hff`, and the target normality instance on `S`; the induced lying-over primes,
  localized maps, and local faithful-flatness are canonical derived data and should not become
  extra public structure;
* layer split: this theorem is a source-facing descent statement, not a replacement owner.
-/

-- Proof sketch: unpack `IsNormalRing` primewise. For each `p : PrimeSpectrum R`, use
-- `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` to choose `q : PrimeSpectrum S` above
-- `p`. The induced local map `Localization.AtPrime p.asIdeal → Localization.AtPrime q.asIdeal` is
-- the canonical `Localization.localRingHom`; it is flat by localization and faithfully flat since
-- it is a flat local map. Because `S` is normal, the target localization is a normal domain. This
-- gives that the source localization is a normal domain, so the defining owner predicate
-- `IsNormalRing R` holds.
/-- Helper for Lemma 10.164.3: the induced map on localizations at primes lying over each other is
faithfully flat. -/
lemma faithfullyFlat_localization_atPrime [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat)
    (p : PrimeSpectrum R) (q : PrimeSpectrum S) [q.asIdeal.LiesOver p.asIdeal] :
    (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).FaithfullyFlat := by
  have halg :
      Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) Ideal.LiesOver.over =
        algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Localization.localRingHom_unique _ _ _ _ fun x ↦ by
      -- Both sides are the canonical image of `x` in the target localization.
      trans algebraMap R (Localization.AtPrime q.asIdeal) x
      · exact (IsScalarTower.algebraMap_apply R (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime q.asIdeal) x).symm
      · exact IsScalarTower.algebraMap_apply R S (Localization.AtPrime q.asIdeal) x
  have hflat :
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)).Flat := by
    -- Localization preserves flatness along the canonical local map.
    simpa [halg] using
      (RingHom.Flat.localRingHom hff.flat q.asIdeal p.asIdeal Ideal.LiesOver.over)
  letI : Module.Flat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    (RingHom.flat_algebraMap_iff).mp hflat
  letI : IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal)) := by
    -- The canonical local map between prime localizations is a local hom.
    simpa [halg] using
      (Localization.isLocalHom_localRingHom p.asIdeal q.asIdeal
        (algebraMap R S) Ideal.LiesOver.over)
  haveI : Module.FaithfullyFlat (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact (RingHom.faithfullyFlat_algebraMap_iff).2 inferInstance

/-- Helper for Lemma 10.164.3: faithful flatness contracts the extension of a principal ideal back
to the original principal ideal. -/
lemma mem_span_singleton_of_mem_map_span_singleton
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]
    {a b : A}
    (h : algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span ({b} : Set A))) :
    a ∈ Ideal.span ({b} : Set A) := by
  -- Reduce the statement to the contraction equality for faithfully flat algebras.
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span ({b} : Set A)),
    Ideal.mem_comap]
  exact h

/-- Helper for Lemma 10.164.3: an injective faithfully flat map from a domain to an integrally
closed domain descends integrally closedness. -/
lemma isIntegrallyClosed_of_faithfullyFlat_of_isIntegrallyClosed_target
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B] [Module.FaithfullyFlat A B] [IsIntegrallyClosed B] :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (K := FractionRing A)]
  intro x hx
  have hyφ :
      nonZeroDivisors A ≤ (nonZeroDivisors B).comap (algebraMap A B) :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap A B)
      (FaithfulSMul.algebraMap_injective A B)
  let φ : FractionRing A →+* FractionRing B :=
    IsFractionRing.map (K := FractionRing A) (L := FractionRing B)
      (j := algebraMap A B) (FaithfulSMul.algebraMap_injective A B)
  have hφ_alg (z : A) :
      φ (algebraMap A (FractionRing A) z) =
        algebraMap B (FractionRing B) (algebraMap A B z) :=
    IsLocalization.map_eq (S := FractionRing A) (Q := FractionRing B)
      (M := nonZeroDivisors A) (T := nonZeroDivisors B)
      (g := algebraMap A B) (hy := hyφ) z
  have hcomp :
      (algebraMap B (FractionRing B)).comp (algebraMap A B) =
        φ.comp (algebraMap A (FractionRing A)) := by
    ext z
    exact (hφ_alg z).symm
  have hxB : IsIntegral B (φ x) :=
    IsIntegral.map_of_comp_eq (R := A) (S := FractionRing A) (T := B) (U := FractionRing B)
      (φ := algebraMap A B) (ψ := φ) hcomp hx
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hxB
  obtain ⟨a, b, hb, hxab⟩ := IsFractionRing.div_surjective A x
  have hfrac :
      algebraMap B (FractionRing B) (algebraMap A B a) /
          algebraMap B (FractionRing B) (algebraMap A B b) =
        algebraMap B (FractionRing B) c := by
    -- Map the chosen `a / b` presentation into `Frac(B)` and rewrite via integrally closedness.
    have hfrac' := congrArg φ hxab
    rw [map_div₀, hφ_alg, hφ_alg, ← hc] at hfrac'
    exact hfrac'
  have hb0 : algebraMap B (FractionRing B) (algebraMap A B b) ≠ 0 := by
    exact map_ne_zero_of_mem_nonZeroDivisors (algebraMap B (FractionRing B))
      (FaithfulSMul.algebraMap_injective B (FractionRing B))
      (map_mem_nonZeroDivisors (algebraMap A B) (FaithfulSMul.algebraMap_injective A B) hb)
  have habB :
      algebraMap A B a = c * algebraMap A B b := by
    -- Clear denominators in `Frac(B)` and then use injectivity of `B → Frac(B)`.
    apply (FaithfulSMul.algebraMap_injective B (FractionRing B))
    rw [div_eq_iff hb0] at hfrac
    simpa using hfrac
  have hmemB :
      algebraMap A B a ∈ Ideal.map (algebraMap A B) (Ideal.span ({b} : Set A)) := by
    -- The equality in `B` says exactly that `a` lands in the extended principal ideal `(b)B`.
    simpa [Ideal.map_span] using
      (Ideal.mem_span_singleton'.mpr ⟨c, habB.symm⟩ :
        algebraMap A B a ∈ Ideal.span ({algebraMap A B b} : Set B))
  have hmemA : a ∈ Ideal.span ({b} : Set A) :=
    mem_span_singleton_of_mem_map_span_singleton hmemB
  rcases Ideal.mem_span_singleton.mp hmemA with ⟨d, hd⟩
  refine ⟨d, ?_⟩
  have hbA0 : algebraMap A (FractionRing A) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  -- Reinsert the descended divisibility relation into the original fraction expression.
  calc
    algebraMap A (FractionRing A) d =
        (algebraMap A (FractionRing A) b * algebraMap A (FractionRing A) d) /
          algebraMap A (FractionRing A) b := by
          rw [mul_div_cancel_left₀ _ hbA0]
    _ = algebraMap A (FractionRing A) a / algebraMap A (FractionRing A) b := by
          rw [← map_mul, hd]
    _ = x := hxab

/-- Lemma 10.164.3: a faithfully flat morphism from `R` to a normal ring `S` forces `R` to be a
normal ring. -/
theorem isNormalRing_of_faithfullyFlat (f : R →+* S) (hff : f.FaithfullyFlat) [IsNormalRing S] :
    IsNormalRing R := by
  letI := f.toAlgebra
  haveI : Module.FaithfullyFlat R S :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp <| by
      simpa [RingHom.algebraMap_toAlgebra] using hff
  refine ⟨fun p ↦ ?_⟩
  have hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S)) :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat
  obtain ⟨q, hq⟩ := hsurj p
  letI : q.asIdeal.LiesOver p.asIdeal := ⟨(congrArg PrimeSpectrum.asIdeal hq).symm⟩
  have hffAlg : (algebraMap R S).FaithfullyFlat := by
    simpa [RingHom.algebraMap_toAlgebra] using hff
  have hffLoc :
      (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal)).FaithfullyFlat :=
    faithfullyFlat_localization_atPrime hffAlg p q
  haveI : Module.FaithfullyFlat (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime q.asIdeal) :=
    (RingHom.faithfullyFlat_algebraMap_iff).mp hffLoc
  letI : IsDomain (Localization.AtPrime q.asIdeal) := isDomain_localizationAtPrime q
  letI : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_localizationAtPrime q
  have hinj :
      Function.Injective (algebraMap (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime q.asIdeal)) :=
    hffLoc.injective
  have hdomain : IsDomain (Localization.AtPrime p.asIdeal) :=
    Function.Injective.isDomain _ hinj
  letI : IsDomain (Localization.AtPrime p.asIdeal) := hdomain
  refine ⟨hdomain, ?_⟩
  -- With the localized target already a normal domain, the source localization is integrally
  -- closed by the source proof's faithful-flat descent argument on fractions.
  exact isIntegrallyClosed_of_faithfullyFlat_of_isIntegrallyClosed_target
    (A := Localization.AtPrime p.asIdeal) (B := Localization.AtPrime q.asIdeal)

end
