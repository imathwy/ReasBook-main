import Mathlib
import StacksProject_2024.Chap10.Lemma_10_20_1_Nakayama_s_lemma
import StacksProject_2024.Chap10.Lemma_10_96_1

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

/-- Helper for Lemma 10.126.10: the kernel ideal of a surjective map from a finite-type algebra to
a finitely presented algebra is finitely generated over the source. -/
private theorem kernel_fg_of_surjective_of_finitePresentation_over_source
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hsurj : Function.Surjective f) :
    (RingHom.ker (f : S →+* S')).FG := by
  letI : Algebra S S' := f.toRingHom.toAlgebra
  have hfp : RingHom.FinitePresentation (f : S →+* S') :=
    RingHom.FinitePresentation.of_comp_finiteType
      (f := algebraMap R S)
      (g := (f : S →+* S'))
      (by
        simpa [RingHom.finitePresentation_algebraMap] using
          (inferInstance : Algebra.FinitePresentation R S'))
      (by
        simpa [RingHom.finiteType_algebraMap] using
          (inferInstance : Algebra.FiniteType R S))
  letI : Algebra.FinitePresentation S S' := hfp
  -- Finite presentation over the source identifies the kernel as a finitely generated ideal.
  simpa using Algebra.FinitePresentation.ker_fG_of_surjective (Algebra.ofId S S') hsurj

/-- Helper for Lemma 10.126.10: the kernel ideal is a finite `S`-module, which is the form needed
when the source proof localizes the kernel and later applies Nakayama. -/
private theorem kernel_finite_of_surjective_of_finitePresentation_over_source
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hsurj : Function.Surjective f) :
    Module.Finite S (RingHom.ker (f : S →+* S')) := by
  -- Package finite generation of the kernel ideal into the finite-module form used later.
  rw [Module.Finite.iff_fg]
  exact kernel_fg_of_surjective_of_finitePresentation_over_source
    (f := f) (R := R) hsurj

/-- Helper for Lemma 10.126.10: the localized kernel of `f` at `q.primeCompl` vanishes once the
comparison modulo `I` is bijective. -/
private theorem localized_kernel_subsingleton_at_prime_compl_of_bijective_quotient
    [Algebra.FiniteType R S] [Algebra.FinitePresentation R S']
    (hIq : Ideal.map (algebraMap R S) I ≤ q)
    (hsurj : Function.Surjective f)
    [Module.Flat R Sqf]
    (hquot : Function.Bijective (localizedQuotientMapModIdealAtPrimeCompl f q I)) :
    Subsingleton (LocalizedModule q.primeCompl (RingHom.ker (f : S →+* S'))) := by
  let J : Ideal S := RingHom.ker (f : S →+* S')
  letI : Algebra S S' := f.toRingHom.toAlgebra
  letI : Module.Finite S J :=
    kernel_finite_of_surjective_of_finitePresentation_over_source (f := f) (R := R) hsurj
  -- Route correction: keep the source proof's single-object route `J_q → S_q → S'_q` and avoid
  -- switching to an unrelated recursion or ad hoc kernel argument.
  have hsub :
      Algebra.algebraMapSubmonoid S' q.primeCompl = Submonoid.map (f : S →+* S') q.primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
  -- The source exact sequence starts from `J = ker(f)` before localization.
  have hExact₀ : Function.Exact J.subtype (Algebra.ofId S S').toLinearMap := by
    simpa [J] using LinearMap.exact_subtype_ker_map ((Algebra.ofId S S').toLinearMap)
  -- TODO: localize the exact sequence `J → S → S'` to `J_q → S_q → S'_q`, identify the quotient
  -- map induced by `S_q → S'_q` with `localizedQuotientMapModIdealAtPrimeCompl f q I`, use
  -- `quotientMapByIdeal_injective_of_exact_of_flat` to deduce `J_q / I J_q = 0`, and then apply
  -- Nakayama over the local ring `Sq` using `hIq`.
  -- Current blocker: the canonical localized codomain for `IsLocalizedModule.map_exact` and the
  -- existing quotient comparison map live on propositionally equal localization submonoids, and
  -- the required `R → Sq → Sqf` tower does not normalize definitionally enough for the quotient
  -- bridge to elaborate without a dedicated coercion-stable lemma.
  sorry

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
  by
  let J : Ideal S := RingHom.ker (f : S →+* S')
  letI : Algebra S S' := f.toRingHom.toAlgebra
  letI : Module.Finite S J := kernel_finite_of_surjective_of_finitePresentation_over_source
    (f := f) (R := R) hsurj
  have hJq :
      Subsingleton (LocalizedModule q.primeCompl J) :=
    localized_kernel_subsingleton_at_prime_compl_of_bijective_quotient
      (f := f) (R := R) (I := I) (q := q) hIq hsurj hquot
  letI : Subsingleton (LocalizedModule q.primeCompl J) := hJq
  obtain ⟨g, hgq, hJaway⟩ := LocalizedModule.exists_subsingleton_away (M := J) q
  have hAwayInj : Function.Injective (Localization.awayMap (f := (f : S →+* S')) g) := by
    rw [Localization.awayMap_injective_iff]
    intro x hx
    obtain ⟨r, hr, hrx⟩ :=
      (LocalizedModule.subsingleton_iff (R := S) (M := J) (S := Submonoid.powers g)).1 hJaway
        ⟨x, hx⟩
    rcases hr with ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    simpa [J, Algebra.smul_def, smul_eq_mul] using congrArg Subtype.val hrx
  have hAwaySurj : Function.Surjective (Localization.awayMap (f := (f : S →+* S')) g) := by
    rw [Localization.awayMap_surjective_iff]
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    exact ⟨y, 0, by simp⟩
  refine ⟨g, hgq, ?_⟩
  -- The algebra-valued away map is bijective exactly when the underlying ring map is.
  simpa using ⟨hAwayInj, hAwaySurj⟩

end
