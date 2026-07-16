import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_32_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: commutative algebra of extended ideals and quotient algebra maps under an
  `R`-algebra morphism;
* sampled owner declarations:
  `Ideal.le_comap_map`,
  `Ideal.map_map`,
  `Ideal.quotientMapₐ`,
  `Ideal.IsLocallyNilpotent`;
* best owner abstraction: the induced quotient algebra map is the canonical `Ideal.quotientMapₐ`
  for the extended ideals, with containment supplied from `Ideal.le_comap_map` plus
  functoriality of `Ideal.map`;
* layer: the numbered item is `source-facing`, while the quotient map on extended ideals is only a
  `bridge/view` built directly from the owner quotient construction;
* primitive data: `I`, `f`, and the finite type / finite presentation / flatness hypotheses;
* derived API: the quotient map modulo the extended ideal.
-/

universe u v w

section

variable {R : Type u} {S : Type v} {S' : Type w}
variable [CommRing R] [CommRing S] [CommRing S']
variable [Algebra R S] [Algebra R S']

private theorem extendedIdeal_le_comap_extendedIdeal {I : Ideal R} (f : S →ₐ[R] S') :
    Ideal.map (algebraMap R S) I ≤
      Ideal.comap (f : S →+* S') (Ideal.map (algebraMap R S') I) := by
  simpa [Ideal.map_map] using
    (show Ideal.map (algebraMap R S) I ≤
        Ideal.comap (f : S →+* S')
          (Ideal.map (f : S →+* S') (Ideal.map (algebraMap R S) I)) from
      Ideal.le_comap_map)

-- Proof sketch: Lemma `10.126.9` makes `f` surjective from the surjectivity of the quotient map.
-- By Lemma `10.32.3`, the extended ideals `I S` and `I S'` are locally nilpotent, so every prime
-- of `S` contains `I S`. Localizing at any prime `q ⊆ S`, the induced quotient map remains
-- bijective, and Lemma `10.126.10` yields a neighborhood on which `f` is bijective. Hence every
-- localization `S_q → S'_q` is an isomorphism, and Lemma `10.23.1` then gives injectivity of `f`.
/-- Lemma 10.126.11: let `I ⊆ R` be a locally nilpotent ideal and `f : S →ₐ[R] S'` an
`R`-algebra map. If the induced map `S / I S → S' / I S'` is bijective, `S` is of finite type
over `R`, `S'` is of finite presentation over `R`, and `S'` is flat over `R`, then `f` is
bijective. -/
theorem bijective_of_bijective_mod_ideal_of_locallyNilpotent_of_finiteType_of_finitePresentation_of_flat
    {I : Ideal R} (hI : I.IsLocallyNilpotent) (f : S →ₐ[R] S')
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S'] [Module.Flat R S']
    (hquot :
      Function.Bijective
        (Ideal.quotientMapₐ (Ideal.map (algebraMap R S') I) f
          (extendedIdeal_le_comap_extendedIdeal f))) :
    Function.Bijective f := sorry

end
