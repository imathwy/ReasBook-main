import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

/-- Helper for Lemma 10.30.1: localizing `R_a` further away from `u`
can be re-expressed as an away-localization of `R` after multiplying by the
numerator returned by `IsLocalization.Away.sec`. -/
lemma away_of_sec_fst {A : Type u} [CommRing A] (a : A) (u : Localization.Away a) :
    IsLocalization.Away (a * (IsLocalization.Away.sec a u).1) (Localization.Away u) := by
  -- The chosen numerator is associated to `u` in `A_a`, so one more away-localization
  -- clears denominators at the cost of an extra factor of `a`.
  exact .mul_of_associated _ _ u <| IsLocalization.Away.associated_sec_fst a u

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Lemma 10.30.1: once the localized target algebra is known to be finitely
presented over `R_f`, the canonical comparison map `R_f → S_(fg)` is finitely presented
as a ring homomorphism. -/
lemma localizationAwayProductMap_finitePresentation_of_algebra
    (f : R) (g : S)
    (hfp :
      letI : Algebra (Localization.Away f) (Localization.Away ((algebraMap R S f) * g)) :=
        (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
          (Localization.awayMap (algebraMap R S) f)) :
            Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)).toAlgebra
      Algebra.FinitePresentation (Localization.Away f)
        (Localization.Away ((algebraMap R S f) * g))) :
    (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
      (Localization.awayMap (algebraMap R S) f)) :
        Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)).FinitePresentation := by
  -- The target localization carries the algebra structure induced by the comparison map.
  letI : Algebra (Localization.Away f) (Localization.Away ((algebraMap R S f) * g)) :=
    (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
      (Localization.awayMap (algebraMap R S) f)) :
        Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)).toAlgebra
  letI : Algebra.FinitePresentation (Localization.Away f)
      (Localization.Away ((algebraMap R S f) * g)) := hfp
  -- With this algebra structure in place, finite presentation is exactly the algebra-map statement.
  change (algebraMap (Localization.Away f)
    (Localization.Away ((algebraMap R S f) * g))).FinitePresentation
  rw [RingHom.finitePresentation_algebraMap]
  infer_instance

section

variable [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S]

omit [IsDomain S] [FaithfulSMul R S] in
/-- Helper for Lemma 10.30.1: the finite-type hypothesis on `S` is equivalent to finite generation
of the top `R`-subalgebra. -/
lemma top_fg_of_finiteType :
    (⊤ : Subalgebra R S).FG := by
  -- Repackage finite type in the source-proof form needed for the induction on generators.
  let e : (⊤ : Subalgebra R S) ≃ₐ[R] S := Subalgebra.topEquiv
  have htop : Algebra.FiniteType R (⊤ : Subalgebra R S) :=
    Algebra.FiniteType.equiv inferInstance e.symm
  exact (Subalgebra.fg_iff_finiteType (⊤ : Subalgebra R S)).mpr htop

/-- Helper for Lemma 10.30.1: if adjoining no extra generators already gives the whole target,
then every element of `S` comes from `R`. -/
lemma algebraMap_surjective_of_adjoin_empty_eq_top
    (h : Algebra.adjoin R (∅ : Set S) = ⊤) :
    Function.Surjective (algebraMap R S) := by
  intro y
  -- If the empty adjoin is already top, then `y` lies in the bottom subalgebra, hence in the
  -- range of the structure map `R → S`.
  have hy : y ∈ (⊥ : Subalgebra R S) := by
    have hy' : y ∈ Algebra.adjoin R (∅ : Set S) := by
      simpa [h] using (show y ∈ (⊤ : Subalgebra R S) from trivial)
    simpa [Algebra.adjoin_empty] using hy'
  exact Set.mem_range.mp (by simpa [Algebra.mem_bot] using hy)

/-- Helper for Lemma 10.30.1: after splitting off the final generator of a finite set, the same
top-generation statement can be rewritten as a singleton adjoin over the previously generated
subalgebra. -/
lemma adjoin_singleton_eq_top_over_adjoin_finset_of_insert_eq_top
    (s : Finset S) (x : S)
    (h : Algebra.adjoin R ({x} ∪ (↑s : Set S)) = ⊤) :
    Algebra.adjoin (Algebra.adjoin R (↑s : Set S)) ({x} : Set S) = ⊤ := by
  -- Route correction: the insert step needs this exact reassociation lemma before the singleton
  -- branch can be applied over the previously generated subalgebra.
  -- TODO: transport `Algebra.adjoin_insert_adjoin` across the restriction-of-scalars from
  -- `R` to `Algebra.adjoin R (↑s : Set S)` so the target becomes an equality in the larger
  -- base algebra rather than in `R`.
  sorry

/-- Helper for Lemma 10.30.1: once a generated subalgebra is already all of `S`, the localized
finite-presentation statement can be transported across the resulting algebra equivalence. -/
lemma localizationAwayProductMap_finitePresentation_of_generated_top
    {T : Subalgebra R S} (hT : T = ⊤)
    (h :
      ∃ (f : R) (_ : f ≠ 0) (g : T) (_ : g ≠ 0),
        (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
          (Localization.awayMap (algebraMap R T) f)) :
            Localization.Away f →+* Localization.Away ((algebraMap R T f) * g)).FinitePresentation) :
    ∃ (f : R) (_ : f ≠ 0) (g : S) (_ : g ≠ 0),
      (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
        (Localization.awayMap (algebraMap R S) f)) :
          Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)).FinitePresentation := by
  -- Route correction: the final transport from the generated top subalgebra to `S` should be done
  -- by the equivalence `(Subalgebra.equivOfEq _ _ hT).trans Subalgebra.topEquiv`, then by carrying
  -- the localized target across the induced away-map on codomains.
  -- TODO: build the induced bijective away-map on the codomain localization, compose it with the
  -- finite-presentation map supplied by `h`, and rewrite the composite to the canonical
  -- `Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)` map.
  sorry

/-- Helper for Lemma 10.30.1: the insert step in the source-proof induction localizes the
previously generated subalgebra, applies the singleton case to the final generator, and clears the
new denominator. -/
lemma exists_nonzero_localizationAwayProductGeneratedSubalgebra_finitePresentation_of_insert
    (s : Finset S) (x : S)
    (ih :
      ∃ (f : R) (_ : f ≠ 0) (g : Algebra.adjoin R (↑s : Set S)) (_ : g ≠ 0),
        (((IsLocalization.Away.awayToAwayRight
            (algebraMap R (Algebra.adjoin R (↑s : Set S)) f) g).comp
          (Localization.awayMap (algebraMap R (Algebra.adjoin R (↑s : Set S))) f)) :
            Localization.Away f →+*
              Localization.Away ((algebraMap R (Algebra.adjoin R (↑s : Set S)) f) * g)).FinitePresentation) :
    ∃ (f : R) (_ : f ≠ 0) (g : Algebra.adjoin R ({x} ∪ (↑s : Set S))) (_ : g ≠ 0),
      (((IsLocalization.Away.awayToAwayRight
          (algebraMap R (Algebra.adjoin R ({x} ∪ (↑s : Set S))) f) g).comp
        (Localization.awayMap (algebraMap R (Algebra.adjoin R ({x} ∪ (↑s : Set S)))) f)) :
          Localization.Away f →+*
            Localization.Away ((algebraMap R (Algebra.adjoin R ({x} ∪ (↑s : Set S))) f) * g)).FinitePresentation := by
  -- Route correction: this is the source-faithful "`S'` plus one generator" step, so the proof
  -- must pass through the localized subalgebra `Algebra.adjoin R (↑s : Set S)` rather than try to
  -- recurse directly on the ambient algebra `S`.
  -- TODO: rewrite `Algebra.adjoin R (↑(insert x s) : Set S)` as
  -- `Algebra.adjoin (Algebra.adjoin R (↑s : Set S)) ({x} : Set S)`, apply the singleton
  -- localization theorem over the localized base returned by `ih`, and then clear the resulting
  -- denominator using `away_of_sec_fst`.
  sorry

/-- Helper for Lemma 10.30.1: inducting on a finite set of generators is easiest when the target
algebra is the generated subalgebra itself, matching the textbook proof exactly. -/
lemma exists_nonzero_localizationAwayProductGeneratedSubalgebra_finitePresentation_of_finset
    (s : Finset S) :
    ∃ (f : R) (_ : f ≠ 0) (g : Algebra.adjoin R (↑s : Set S)) (_ : g ≠ 0),
      (((IsLocalization.Away.awayToAwayRight
          (algebraMap R (Algebra.adjoin R (↑s : Set S)) f) g).comp
        (Localization.awayMap (algebraMap R (Algebra.adjoin R (↑s : Set S))) f)) :
          Localization.Away f →+*
            Localization.Away ((algebraMap R (Algebra.adjoin R (↑s : Set S)) f) * g)).FinitePresentation := by
  -- Route correction: the induction target is the generated subalgebra `Algebra.adjoin R (↑s)`,
  -- not the ambient algebra `S`, so the empty and insert branches should be proved at that level.
  -- TODO: prove the empty branch by identifying `Algebra.adjoin R ∅` with `⊥` and localizing the
  -- bijective map `R ≃ₐ[R] ⊥`, then use
  -- `exists_nonzero_localizationAwayProductGeneratedSubalgebra_finitePresentation_of_insert`
  -- for the source-faithful insert step.
  sorry

/-- Helper for Lemma 10.30.1: the source-proof induction on a finite generating set produces an
away-localization of `S` that is finitely presented over an away-localization of `R`. -/
lemma exists_nonzero_localizationAwayProductAlgebra_finitePresentation_of_fg_top
    (hfg : (⊤ : Subalgebra R S).FG) :
    ∃ (f : R) (_ : f ≠ 0) (g : S) (_ : g ≠ 0),
      letI : Algebra (Localization.Away f) (Localization.Away ((algebraMap R S f) * g)) :=
        (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
          (Localization.awayMap (algebraMap R S) f)) :
            Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)).toAlgebra
      Algebra.FinitePresentation (Localization.Away f)
        (Localization.Away ((algebraMap R S f) * g)) := by
  rcases hfg with ⟨s, hs⟩
  rcases localizationAwayProductMap_finitePresentation_of_generated_top
      (R := R) (S := S) (T := Algebra.adjoin R (↑s : Set S)) hs
      (exists_nonzero_localizationAwayProductGeneratedSubalgebra_finitePresentation_of_finset
        (R := R) (S := S) s) with ⟨f, hf, g, hg, hfp⟩
  refine ⟨f, hf, g, hg, ?_⟩
  letI : Algebra (Localization.Away f) (Localization.Away ((algebraMap R S f) * g)) :=
    (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) g).comp
      (Localization.awayMap (algebraMap R S) f)) :
        Localization.Away f →+* Localization.Away ((algebraMap R S f) * g)).toAlgebra
  -- After transporting back to `S`, finite presentation is again the algebra-map statement.
  simpa [RingHom.finitePresentation_algebraMap] using hfp

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
  -- The inclusion `R ⊆ S` identifies `R` as a domain, so the source-proof induction is available.
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  -- First convert finite type to a finitely generated top subalgebra and invoke the induction
  -- helper that isolates the source-proof core.
  rcases exists_nonzero_localizationAwayProductAlgebra_finitePresentation_of_fg_top
      (R := R) (S := S) top_fg_of_finiteType with ⟨f, hf, g, hg, hfp⟩
  -- The remaining step is the algebra-to-ring-hom conversion packaged in the helper above.
  exact ⟨f, hf, g, hg,
    localizationAwayProductMap_finitePresentation_of_algebra f g hfp⟩

end

end
