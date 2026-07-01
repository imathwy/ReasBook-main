import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling:
* primary domain: localization of `R`-algebra maps at a prime complement and passage to quotients
  by extended ideals;
* sampled owner declarations:
  `IsLocalization.mapₐ`,
  `Ideal.quotientMapₐ`,
  `Ideal.map_le_iff_le_comap`,
  `Localization.awayMapₐ`;
* best owner abstraction:
  the canonical localized quotient comparison algebra map built from `IsLocalization.mapₐ`
  and `Ideal.quotientMapₐ`;
* layer:
  the main existence statement is `source-facing`, while the localized quotient map is a
  `bridge/view` built from the owner localization and quotient constructions;
* primitive data:
  `f`, `I`, `q`, and the finite type / finite presentation / flatness hypotheses;
* derived API:
  the induced quotient algebra map on localizations modulo `I`.
-/

section

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]
variable {S' : Type w} [CommRing S'] [Algebra R S']

variable (f : S →ₐ[R] S') (I : Ideal R) (q : Ideal S) [q.IsPrime]

local notation "Sq" => Localization q.primeCompl
local notation "Sqf" => Localization (Submonoid.map (f : S →+* S') q.primeCompl)

private theorem ideal_map_le_comap_map_of_algHom
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (f : A →ₐ[R] B) (I : Ideal R) :
    Ideal.map (algebraMap R A) I ≤ Ideal.comap f (Ideal.map (algebraMap R B) I) :=
  (Ideal.map_le_iff_le_comap).mp <| by
    calc
      Ideal.map (f : A →+* B) (Ideal.map (algebraMap R A) I) =
          Ideal.map ((f : A →+* B).comp (algebraMap R A)) I := by
            rw [Ideal.map_map]
      _ = Ideal.map (algebraMap R B) I := by
            congr 1
            ext r
            exact f.commutes r
      _ ≤ Ideal.map (algebraMap R B) I := le_rfl

/-- The quotient map modulo `I` induced by the localized map at `q.primeCompl`. -/
noncomputable abbrev localizedQuotientMapModIdealAtPrimeCompl (I : Ideal R) :
    Sq ⧸ Ideal.map (algebraMap R Sq) I →ₐ[R]
      Sqf ⧸ Ideal.map (algebraMap R Sqf) I := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  let localizedMap : Sq →ₐ[R] Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) := by
    let g : Sq →ₐ[Sq] Localization (Algebra.algebraMapSubmonoid S' q.primeCompl) :=
      IsLocalization.mapₐ q.primeCompl Sq Sq
        (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))
        (Algebra.ofId S S')
    exact
      { __ := g.toRingHom
        commutes' := fun r ↦ by
          simpa [IsScalarTower.algebraMap_eq R S Sq,
            IsScalarTower.algebraMap_eq R S
              (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))] using
            g.commutes ((algebraMap R Sq) r) }
  exact
    Ideal.quotientMapₐ
      (Ideal.map (algebraMap R (Localization (Algebra.algebraMapSubmonoid S' q.primeCompl))) I)
      localizedMap
      (ideal_map_le_comap_map_of_algHom localizedMap I)

-- Proof sketch: let `J = RingHom.ker f`. Finite presentation of `S'` and finite type of `S`
-- imply that `J` is finitely generated. Flatness of the localized target over `R` identifies the
-- kernel of `(S_q / I S_q) → (S'_q / I S'_q)` with `J_q / I J_q`; the assumed bijectivity forces
-- this quotient to vanish. Nakayama then gives `J_q = 0`, so `S_q → S'_q` is bijective, and the
-- finite-presentation spreading lemma upgrades this to `S_g → S'_g` for some `g ∉ q`.
/-- Lemma 10.126.10: let `R` be a ring, let `I ⊆ R` be an ideal, let `f : S →ₐ[R] S'` be a
surjective `R`-algebra map, and let `q` be a prime ideal of `S` containing `I S`. If `S` is of
finite type over `R`, `S'` is of finite presentation over `R`, the induced quotient algebra map on
the localizations at `q.primeCompl` modulo `I` is bijective, and the localized target `S'_q` is
flat over `R`,
then there exists `g ∉ q` such that `S_g → S'_g` is bijective. -/
lemma exists_notMem_and_awayMap_bijective_of_localizedQuotient_bijective
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf]
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    ∃ g : S, g ∉ q ∧ Function.Bijective (Localization.awayMapₐ f g) :=
  sorry

end
