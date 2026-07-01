import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Module.Flat R S] [Algebra.FinitePresentation R S]

/-
Domain triage:
- primary domain: surjective flat finitely presented algebra maps and their canonical presentation
  as localizations away from an idempotent;
- sampled owner declarations:
  `Ideal.Pure`,
  `Ideal.isIdempotentElem_of_pure`,
  `Ideal.isIdempotentElem_iff_of_fg`,
  `IsLocalization.away_of_isIdempotentElem`,
  `Ideal.quotientKerAlgEquivOfSurjective`;
- best owner abstraction: the kernel ideal of `algebraMap R S`, viewed through the canonical owner
  pipeline "flat quotient => pure ideal => finitely generated idempotent ideal => away
  localization";
- primitive data: the `R`-algebra `S`, the flatness and finite-presentation owner instances, and
  the surjectivity of `algebraMap R S`;
- derived API: the idempotent element cutting out the kernel and the resulting
  `IsLocalization.Away e S`.

This lemma is `source-facing`: it keeps the textbook existence statement, but the proof should
reuse the canonical owner declarations directly rather than introducing any local kernel/idempotent
wrapper.
-/
-- Proof sketch: let `I = RingHom.ker (algebraMap R S)`. Surjectivity identifies `S` with the
-- quotient `R ⧸ I`, so flatness makes `I` a pure ideal. Hence `I` is idempotent, and finite
-- presentation makes it finitely generated. Apply the canonical finitely-generated idempotent-ideal
-- criterion to write `I = (1 - e)` for an idempotent `1 - e`, then use
-- `IsLocalization.away_of_isIdempotentElem` to identify `S` with the localization of `R` away from
-- `e`.
/-- Lemma 10.143.9: if `S` is a surjective, flat, finitely presented `R`-algebra, then there
exists an idempotent `e ∈ R` such that `S` is the localization of `R` away from `e`. -/
theorem exists_idempotent_localizationAway_of_surjective_of_flat_of_finitePresentation
    (hsurj : Function.Surjective (algebraMap R S)) :
    ∃ e : R, IsIdempotentElem e ∧ IsLocalization.Away e S := by
  let I : Ideal R := RingHom.ker (algebraMap R S)
  have hfg : I.FG := by
    simpa [I] using
      Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId R S) hsurj
  have hI : IsIdempotentElem I := by
    let f : R →ₐ[R] S := Algebra.ofId R S
    have hf : Function.Surjective f := by
      simpa [f] using hsurj
    let e : (R ⧸ I) ≃ₐ[R] S := by
      simpa [I, f] using (Ideal.quotientKerAlgEquivOfSurjective hf :
        (R ⧸ RingHom.ker f) ≃ₐ[R] S)
    letI : I.Pure := by
      change Module.Flat R (R ⧸ I)
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    exact Ideal.isIdempotentElem_of_pure I
  obtain ⟨e, he, hker⟩ := (Ideal.isIdempotentElem_iff_of_fg I hfg).mp hI
  refine ⟨1 - e, he.one_sub, ?_⟩
  exact IsLocalization.away_of_isIdempotentElem he.one_sub (hker.trans (by simp)) hsurj

end
