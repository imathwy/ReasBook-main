import Mathlib
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_30_1 (from Chap10) -/
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

/-! ### Lemma_10_30_2 (from Chap10) -/
universe u v

open Set Topology PrimeSpectrum TopologicalSpace
open scoped Set.Notation

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S}
variable {E : Set (PrimeSpectrum S)} {ξ : PrimeSpectrum R}

local notation "Zξ" => closure (Set.singleton ξ : Set (PrimeSpectrum R))
local notation "traceOnClosure" =>
  (((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹' (PrimeSpectrum.comap f '' E)))

/- Layering for this item:
* source-facing: the existence of an open dense subset in the trace of `comap f '' E` on
  `closure {ξ}` for a finite type map;
* core/canonical owner: `PrimeSpectrum.comap`, `IsConstructible`, and the generic-point space
  `closure ({ξ} : Set (PrimeSpectrum R))`;
* bridge/view: the finite-presentation constructible-image theorem
  `PrimeSpectrum.isConstructible_comap_image`, the generic-point package `isGenericPoint_closure`,
  and the Chapter 5 dense-trace criteria
  `IsIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed`
  and `IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed`.
-/

/-- Helper for Lemma 10.30.2: the spectrum of the quotient `R / x` identifies with the closure of
`x` via the quotient map on prime spectra. -/
lemma quotient_range_comap_eq_closure_singleton (x : PrimeSpectrum R) :
    Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk x.asIdeal)) =
      closure ({x} : Set (PrimeSpectrum R)) := by
  -- The quotient-spectrum image is the zero locus of the quotient ideal, which is exactly
  -- `closure {x}`.
  rw [range_comap_of_surjective (R ⧸ x.asIdeal) (Ideal.Quotient.mk x.asIdeal)
      Ideal.Quotient.mk_surjective]
  rw [Ideal.mk_ker]
  rw [PrimeSpectrum.closure_singleton]

/-- Helper for Lemma 10.30.2: a dense open subset of a dense open subspace extends to an open
dense subset of the ambient space, and intersecting back with the ambient open recovers the
original subspace-open set. -/
lemma image_open_dense_of_dense_open_subspace
    {X : Type u} [TopologicalSpace X] {U : Set X} (hU_open : IsOpen U) (hU_dense : Dense U)
    {W : Set U} (hW_open : IsOpen W) (hW_dense : Dense W) :
    ∃ V : Opens X,
      Dense (V : Set X) ∧ (V : Set X) ⊆ U ∧ ((Subtype.val : U → X) ⁻¹' (V : Set X)) = W := by
  obtain ⟨V₀, hV₀_open, hV₀_dense, hV₀_preimage⟩ :=
    exists_open_dense_of_open_dense_subtype (s := U) hU_dense hW_open hW_dense
  let V : Opens X := ⟨V₀ ∩ U, hV₀_open.inter hU_open⟩
  have hU_subset_closure : U ⊆ closure (V₀ ∩ U) := by
    -- Density in the subtype means the image of `W` is dense in `U`.
    rw [Subtype.dense_iff] at hW_dense
    have hW_image : ((↑) : U → X) '' W = U ∩ V₀ := by
      calc
        ((↑) : U → X) '' W = ((↑) : U → X) '' (((↑) : U → X) ⁻¹' V₀) := by
          rw [hV₀_preimage]
        _ = U ∩ V₀ := Subtype.image_preimage_coe U V₀
    simpa [hW_image, Set.inter_comm] using hW_dense
  have hV_dense : Dense (V : Set X) := by
    -- Since `U` is already dense in `X`, density of `V₀ ∩ U` inside `U` makes it dense in `X`.
    intro x
    exact by
      simpa [V, closure_closure, Set.inter_comm] using closure_mono hU_subset_closure (hU_dense x)
  have hV_preimage : ((Subtype.val : U → X) ⁻¹' (V : Set X)) = W := by
    -- Intersecting the ambient open with `U` does not change its trace on the subtype.
    ext x
    simp [V, hV₀_preimage]
  refine ⟨V, hV_dense, ?_, hV_preimage⟩
  -- By construction, the ambient open lies inside `U`.
  intro x hx
  exact hx.2

/-- Helper for Lemma 10.30.2: in the spectrum of a domain, a constructible subset containing the
generic point contains an open dense subset. -/
lemma exists_open_dense_subset_of_constructible_generic_mem
    {A : Type u} [CommRing A] [IsDomain A] {C : Set (PrimeSpectrum A)}
    (hC : IsConstructible C) (hgeneric : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ C) :
    ∃ U : Opens (PrimeSpectrum A), Dense (U : Set (PrimeSpectrum A)) ∧ (U : Set _) ⊆ C := by
  let ξ0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ0 : IsGenericPoint ξ0 (Set.univ : Set (PrimeSpectrum A)) := by
    -- In a domain, the zero prime is the generic point of the whole spectrum.
    simpa [ξ0, PrimeSpectrum.closure_singleton, PrimeSpectrum.zeroLocus_singleton_zero] using
      (isGenericPoint_closure :
        IsGenericPoint ξ0 (closure ({ξ0} : Set (PrimeSpectrum A))))
  let X0 : Set (PrimeSpectrum A) := Set.univ
  have hDenseTrace :
      Dense (((Subtype.val : X0 → PrimeSpectrum A) ⁻¹' C)) := by
    -- The generic-point criterion upgrades membership of `ξ0` to density on the whole-space
    -- subtype.
    simpa using
      (IsGenericPoint.dense_preimage_iff_mem_of_isFiniteUnionOfLocallyClosed
        (hξ := hξ0) hC.isFiniteUnionOfLocallyClosed).2 hgeneric
  obtain ⟨W, hW_dense, hW_subset⟩ :=
    (hξ0.isIrreducible.exists_open_dense_iff_dense_preimage_of_isFiniteUnionOfLocallyClosed
      hC.isFiniteUnionOfLocallyClosed).2 hDenseTrace
  have hX0_open : IsOpen X0 := by
    simpa [X0] using (isOpen_univ : IsOpen (Set.univ : Set (PrimeSpectrum A)))
  have hX0_dense : Dense X0 := by
    simpa [X0] using (dense_univ : Dense (Set.univ : Set (PrimeSpectrum A)))
  obtain ⟨U, hU_dense, -, hU_preimage⟩ :=
    image_open_dense_of_dense_open_subspace
      (U := X0) hX0_open hX0_dense W.2 hW_dense
  refine ⟨U, hU_dense, ?_⟩
  -- Membership in the transported open subset pulls back to `W`, hence to `C`.
  intro x hxU
  have hxPre :
      (⟨x, by simp [X0]⟩ : X0) ∈
        ((Subtype.val : X0 → PrimeSpectrum A) ⁻¹' (U : Set (PrimeSpectrum A))) := by
    simpa [X0] using hxU
  have hxW : (⟨x, by simp [X0]⟩ : X0) ∈ (W : Set X0) := by
    simpa [hU_preimage] using hxPre
  simpa [X0] using hW_subset hxW

/-- Helper for Lemma 10.30.2: in the spectrum of a domain, every basic open defined by a nonzero
element is dense. -/
lemma basicOpen_dense_of_nonzero_of_isDomain
    {A : Type u} [CommRing A] [IsDomain A] (a : A) (ha : a ≠ 0) :
    Dense (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
  let ξ0 : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
  have hξ0_mem : ξ0 ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    -- The generic prime is disjoint from every nonzero basic-open parameter.
    exact (PrimeSpectrum.mem_basicOpen a ξ0).2 <| by simpa [ξ0] using ha
  obtain ⟨U, hU_dense, hU_subset⟩ :=
    exists_open_dense_subset_of_constructible_generic_mem
      (A := A) PrimeSpectrum.isConstructible_basicOpen hξ0_mem
  -- A dense subset of `D(a)` forces `D(a)` itself to be dense.
  exact Dense.mono hU_subset hU_dense

/-- Helper for Lemma 10.30.2: localizing a constructible subset that already contains the generic
point preserves both constructibility and generic-point membership. -/
lemma localized_preimage_constructible_generic_mem
    {B : Type u} [CommRing B] [IsDomain B] (c : B) (hc : c ≠ 0)
    {C : Set (PrimeSpectrum B)} (hC : IsConstructible C)
    (hgeneric : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) ∈ C) :
    letI : IsDomain (Localization.Away c) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away c)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
    IsConstructible
        (PrimeSpectrum.comap (algebraMap B (Localization.Away c)) ⁻¹' C) ∧
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away c)) ∈
        PrimeSpectrum.comap (algebraMap B (Localization.Away c)) ⁻¹' C := by
  letI : IsDomain (Localization.Away c) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away c)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
  constructor
  · -- Constructible sets stay constructible after pulling back along the localization chart.
    exact primeSpectrum_comap_preimage_isConstructible (algebraMap B (Localization.Away c)) hC
  · -- The generic point of the localized domain contracts back to the generic point of `Spec B`.
    have hinj : Function.Injective (algebraMap B (Localization.Away c)) := by
      exact IsLocalization.injective (Localization.Away c)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hc)
    have hgeneric_comap :
        PrimeSpectrum.comap (algebraMap B (Localization.Away c))
            (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away c)) =
          (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum B) := by
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal, Ideal.comap_bot_of_injective _ hinj]
    change PrimeSpectrum.comap (algebraMap B (Localization.Away c))
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away c)) ∈ C
    rw [hgeneric_comap]
    exact hgeneric

/-- Helper for Lemma 10.30.2: contracting `η` along `f` recovers the ideal of `ξ`. -/
lemma quotient_comap_eq_of_comap_eq
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    ξ.asIdeal = Ideal.comap f η.asIdeal := by
  -- This is the ideal-level form of the hypothesis `PrimeSpectrum.comap f η = ξ`.
  simpa [PrimeSpectrum.comap_asIdeal] using (congrArg PrimeSpectrum.asIdeal hηξ).symm

/-- Helper for Lemma 10.30.2: the map `f` descends to the quotient rings at `ξ` and `η`. -/
def quotient_map_of_comap_eq
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    R ⧸ ξ.asIdeal →+* S ⧸ η.asIdeal :=
  Ideal.quotientMap η.asIdeal f
    (le_of_eq (quotient_comap_eq_of_comap_eq (f := f) (ξ := ξ) hηξ))

/-- Helper for Lemma 10.30.2: the descended quotient map commutes with the original map after
precomposing with the quotient map at `ξ`. -/
lemma quotient_map_of_comap_eq_comp_quotient_mk
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ).comp (Ideal.Quotient.mk ξ.asIdeal) =
      (Ideal.Quotient.mk η.asIdeal).comp f := by
  -- Both ring homomorphisms send `r : R` to its class in `S / η`.
  ext r
  rfl

/-- Helper for Lemma 10.30.2: the descended quotient map is injective because its source ideal is
exactly the contracted target ideal. -/
lemma quotient_map_of_comap_eq_injective
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    Function.Injective (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ) := by
  let hηξIdeal : ξ.asIdeal = Ideal.comap f η.asIdeal :=
    quotient_comap_eq_of_comap_eq (f := f) (ξ := ξ) hηξ
  -- Once the contracted ideal agrees with `ξ.asIdeal`, the owner quotient-map criterion applies.
  simpa [quotient_map_of_comap_eq, hηξIdeal] using
    (Ideal.quotientMap_injective' (f := f) (I := η.asIdeal) (J := ξ.asIdeal)
      (h := le_of_eq hηξIdeal.symm))

/-- Helper for Lemma 10.30.2: after choosing a point `η` above `ξ`, the quotient map
`R / ξ → S / η` satisfies the domain and finite-type hypotheses needed to apply
Lemma `10.30.1`. -/
lemma quotient_localization_data_of_comap_eq
    (hf : f.FiniteType) {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    ∃ (a : R ⧸ ξ.asIdeal) (_ : a ≠ 0) (b : S ⧸ η.asIdeal) (_ : b ≠ 0),
      (((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
        (Localization.awayMap fbar a)) :
          Localization.Away a →+* Localization.Away ((fbar a) * b)).FinitePresentation := by
  letI : Algebra R S := f.toAlgebra
  let hηξIdeal : ξ.asIdeal = Ideal.comap f η.asIdeal :=
    quotient_comap_eq_of_comap_eq (f := f) (ξ := ξ) hηξ
  letI : η.asIdeal.LiesOver ξ.asIdeal := by
    -- The chosen point `η` lies over `ξ` exactly because it contracts to `ξ`.
    refine ⟨?_⟩
    exact hηξIdeal
  letI : Algebra (R ⧸ ξ.asIdeal) (S ⧸ η.asIdeal) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq hηξIdeal)
  letI : Algebra.FiniteType R S := by
    -- Reinterpret finite type for the ring map `f` as finite type for the induced algebra.
    rw [← RingHom.finiteType_algebraMap]
    simpa using hf
  letI : IsDomain (R ⧸ ξ.asIdeal) := (Ideal.Quotient.isDomain_iff_prime (I := ξ.asIdeal)).2 ξ.isPrime
  letI : IsDomain (S ⧸ η.asIdeal) := (Ideal.Quotient.isDomain_iff_prime (I := η.asIdeal)).2 η.isPrime
  letI : FaithfulSMul (R ⧸ ξ.asIdeal) (S ⧸ η.asIdeal) := inferInstance
  letI : Algebra.FiniteType (R ⧸ ξ.asIdeal) (S ⧸ η.asIdeal) := inferInstance
  -- Lemma `10.30.1` now applies directly to the quotient-domain map.
  simpa [quotient_map_of_comap_eq, quotient_comap_eq_of_comap_eq] using
    (exists_nonzero_localizationAwayProductMap_finitePresentation
      (R := R ⧸ ξ.asIdeal) (S := S ⧸ η.asIdeal))

/-- Helper for Lemma 10.30.2: the pullback of `E` to `Spec(S / η)` is constructible and contains
the generic point of the quotient domain. -/
lemma quotient_preimage_constructible_generic_mem
    {η : PrimeSpectrum S} (hE : IsConstructible E) (hηE : η ∈ E) :
    IsConstructible (PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E) ∧
      (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (S ⧸ η.asIdeal)) ∈
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E := by
  constructor
  · -- Constructible sets stay constructible after pulling back along any `Spec` map.
    exact primeSpectrum_comap_preimage_isConstructible (Ideal.Quotient.mk η.asIdeal) hE
  · -- The generic point of `Spec(S / η)` maps back to the chosen prime `η`.
    have hgeneric :
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal)
            (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (S ⧸ η.asIdeal)) = η := by
      apply PrimeSpectrum.ext
      rw [PrimeSpectrum.comap_asIdeal, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    change PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal)
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (S ⧸ η.asIdeal)) ∈ E
    rw [hgeneric]
    exact hηE

/-- Helper for Lemma 10.30.2: in the localized finite-presentation chart, the localization map has
trivial kernel, so the zero prime contracts to the zero prime. -/
lemma localized_chart_comap_bot_eq_bot
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} (ha : a ≠ 0) {b : S ⧸ η.asIdeal} (hb : b ≠ 0) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
      ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
        (Localization.awayMap fbar a))
    Ideal.comap g (⊥ : Ideal (Localization.Away ((fbar a) * b))) =
      (⊥ : Ideal (Localization.Away a)) := by
  let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
  let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
    ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
      (Localization.awayMap fbar a))
  letI : IsDomain (Localization.Away a) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away a)
      (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  have hfbar_inj : Function.Injective fbar :=
    quotient_map_of_comap_eq_injective (f := f) (ξ := ξ) hηξ
  have hfa : fbar a ≠ 0 := by
    intro hzero
    exact ha (hfbar_inj <| by simpa using hzero)
  have hab : (fbar a) * b ≠ 0 := mul_ne_zero hfa hb
  letI : IsDomain (Localization.Away ((fbar a) * b)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away ((fbar a) * b))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hab)
  let qmap : R ⧸ ξ.asIdeal →+* Localization.Away ((fbar a) * b) :=
    (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))).comp fbar
  have hqmap_inj : Function.Injective qmap := by
    intro x y hxy
    apply hfbar_inj
    exact (IsLocalization.injective (Localization.Away ((fbar a) * b))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hab)) hxy
  have hqmapa_unit : IsUnit (qmap a) := by
    -- Inverting `(fbar a) * b` also makes `fbar a` invertible in the target localization.
    change IsUnit
      (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b)) (fbar a))
    exact IsLocalization.Away.isUnit_of_dvd (S := Localization.Away ((fbar a) * b))
      (x := (fbar a) * b) (dvd_mul_right _ _)
  letI : IsLocalization.Away (qmap a) (Localization.Away ((fbar a) * b)) :=
    IsLocalization.away_of_isUnit_of_bijective _ hqmapa_unit Function.bijective_id
  have hg_eq :
      g =
        IsLocalization.Away.map
          (Localization.Away a) (Localization.Away ((fbar a) * b)) qmap a := by
    refine (IsLocalization.map_unique
      (M := Submonoid.powers a)
      (T := Submonoid.powers (qmap a))
      (S := Localization.Away a)
      (P := Localization.Away ((fbar a) * b))
      (Q := Localization.Away ((fbar a) * b))
      (g := qmap)
      (hy := by
        rintro y ⟨n, rfl⟩
        exact ⟨n, by simp⟩)
      g ?_).symm
    intro x
    -- Both maps agree on the image of `R / ξ`, so the localization universal property identifies
    -- them.
    change g (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a) x) = qmap x
    change
      (IsLocalization.Away.awayToAwayRight (fbar a) b)
        ((Localization.awayMap fbar a)
          (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a) x)) = qmap x
    have hawayMap_eq :
        (Localization.awayMap fbar a)
          (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a) x) =
            algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a)) (fbar x) := by
      simpa [Localization.awayMap] using
        (IsLocalization.map_eq
          (S := Localization.Away a)
          (Q := Localization.Away (fbar a))
          (g := fbar)
          (hy := by
            rintro y ⟨n, rfl⟩
            exact ⟨n, by simp⟩)
          x)
    rw [hawayMap_eq]
    simpa [qmap] using
      (IsLocalization.Away.awayToAwayRight_eq
        (S := Localization.Away (fbar a))
        (P := Localization.Away ((fbar a) * b))
        (x := fbar a) (y := b) (fbar x))
  have hg_inj : Function.Injective g := by
    rw [hg_eq]
    exact IsLocalization.map_injective_of_injective _ _ _ hqmap_inj
  -- Route correction: instead of unfolding the localization chart directly, identify `g` with the
  -- universal localization map and use injectivity to contract the zero prime.
  exact Ideal.comap_bot_of_injective _ hg_inj

/-- Helper for Lemma 10.30.2: a witness in the localized chart image contracts to a witness in the
quotient-spectrum image. -/
lemma localized_chart_pointwise_to_quotient_image
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} {b : S ⧸ η.asIdeal}
    {xloc : PrimeSpectrum (Localization.Away a)}
    (hxloc :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
        ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
          (Localization.awayMap fbar a))
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
        PrimeSpectrum.comap
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      xloc ∈ PrimeSpectrum.comap g '' Eloc) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    PrimeSpectrum.comap (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a)) xloc ∈
      PrimeSpectrum.comap fbar '' Eη := by
  let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
  let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
    ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
      (Localization.awayMap fbar a))
  let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
    PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
  let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
    PrimeSpectrum.comap
      (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
  change xloc ∈ PrimeSpectrum.comap g '' Eloc at hxloc
  change PrimeSpectrum.comap (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a)) xloc ∈
      PrimeSpectrum.comap fbar '' Eη
  rcases hxloc with ⟨yloc, hyloc, rfl⟩
  refine ⟨PrimeSpectrum.comap
      (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) yloc, hyloc, ?_⟩
  -- Compare the two contractions by rewriting both as a single contraction from the localized
  -- target chart.
  rw [← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply]
  congr 1
  ext r
  -- The localization chart map agrees with the original quotient map on elements from `R / ξ`.
  change (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a * b)))
      (((quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ).comp
          (Ideal.Quotient.mk ξ.asIdeal)) r) =
    (IsLocalization.Away.awayToAwayRight (fbar a) b)
      ((Localization.awayMap fbar a)
        ((algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a))
          ((Ideal.Quotient.mk ξ.asIdeal) r)))
  rw [quotient_map_of_comap_eq_comp_quotient_mk (f := f) (ξ := ξ) hηξ]
  calc
    (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a * b)))
        (((Ideal.Quotient.mk η.asIdeal).comp f) r)
      = (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a * b)))
          ((Ideal.Quotient.mk η.asIdeal) (f r)) := by
          rfl
    _ = (IsLocalization.Away.awayToAwayRight (fbar a) b)
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a))
            (((Ideal.Quotient.mk η.asIdeal).comp f) r)) := by
          simpa using
            (IsLocalization.Away.awayToAwayRight_eq
              (S := Localization.Away (fbar a))
              (P := Localization.Away (fbar a * b))
              (x := fbar a) (y := b) (((Ideal.Quotient.mk η.asIdeal).comp f) r)).symm
    _ = (IsLocalization.Away.awayToAwayRight (fbar a) b)
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a))
            (fbar ((Ideal.Quotient.mk ξ.asIdeal) r))) := by
          exact congrArg
            (fun z : S ⧸ η.asIdeal =>
              (IsLocalization.Away.awayToAwayRight (fbar a) b)
                (algebraMap (S ⧸ η.asIdeal) (Localization.Away (fbar a)) z))
            (show ((Ideal.Quotient.mk η.asIdeal).comp f) r =
                fbar ((Ideal.Quotient.mk ξ.asIdeal) r) by
              rw [← quotient_map_of_comap_eq_comp_quotient_mk
                (f := f) (ξ := ξ) hηξ]
              rfl)
    _ = (IsLocalization.Away.awayToAwayRight (fbar a) b)
          ((Localization.awayMap fbar a)
            ((algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a))
              ((Ideal.Quotient.mk ξ.asIdeal) r))) := by
          congr 1
          symm
          simpa [Localization.awayMap] using
            (IsLocalization.map_eq
              (S := Localization.Away a)
              (Q := Localization.Away (fbar a))
              (g := fbar)
              (hy := by
                rintro x ⟨n, rfl⟩
                exact ⟨n, by simp⟩)
              ((Ideal.Quotient.mk ξ.asIdeal) r))

/-- Helper for Lemma 10.30.2: a witness in the localized chart image descends to the trace of the
quotient-image set on the basic open `D(a)`. -/
lemma localized_chart_homeomorph_pointwise_to_basicOpen_trace
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} {b : S ⧸ η.asIdeal}
    {xloc : PrimeSpectrum (Localization.Away a)}
    (hxloc :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
        ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
          (Localization.awayMap fbar a))
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
        PrimeSpectrum.comap
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      xloc ∈ PrimeSpectrum.comap g '' Eloc) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    let e : PrimeSpectrum (Localization.Away a) ≃ₜ PrimeSpectrum.basicOpen a :=
      primeSpectrum_localizationAway_homeomorph_D a
    e xloc ∈
      ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
        (PrimeSpectrum.comap fbar '' Eη)) := by
  intro fbar Eη e
  -- Rewrite the target point through the canonical localization-basic-open homeomorphism and then
  -- apply the already established localized-chart pointwise transport.
  change (e xloc).1 ∈ PrimeSpectrum.comap fbar '' Eη
  have hxquotient :
      PrimeSpectrum.comap (algebraMap (R ⧸ ξ.asIdeal) (Localization.Away a)) xloc ∈
        PrimeSpectrum.comap fbar '' Eη := by
    simpa using
      localized_chart_pointwise_to_quotient_image
        (f := f) (E := E) (ξ := ξ) (η := η) (a := a) (b := b) (xloc := xloc) hηξ hxloc
  simpa [e, primeSpectrum_localizationAway_homeomorph_D_apply] using hxquotient

/-- Helper for Lemma 10.30.2: transporting a dense open subset of the localized chart across the
homeomorphism `Spec((R / ξ)_a) ≃ D(a)` yields a dense open subset of `D(a)` inside the quotient
trace. -/
lemma localized_chart_dense_open_in_basicOpen_trace
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} {b : S ⧸ η.asIdeal}
    {Wloc : Opens (PrimeSpectrum (Localization.Away a))}
    (hWloc_dense : Dense (Wloc : Set (PrimeSpectrum (Localization.Away a))))
    (hWloc_subset :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let g : Localization.Away a →+* Localization.Away ((fbar a) * b) :=
        ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
          (Localization.awayMap fbar a))
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
        PrimeSpectrum.comap
          (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      (Wloc : Set (PrimeSpectrum (Localization.Away a))) ⊆ PrimeSpectrum.comap g '' Eloc) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    ∃ Wd : Opens (PrimeSpectrum.basicOpen a),
      Dense (Wd : Set (PrimeSpectrum.basicOpen a)) ∧
        (Wd : Set (PrimeSpectrum.basicOpen a)) ⊆
          ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
            (PrimeSpectrum.comap fbar '' Eη)) := by
  intro fbar Eη
  let e : PrimeSpectrum (Localization.Away a) ≃ₜ PrimeSpectrum.basicOpen a :=
    primeSpectrum_localizationAway_homeomorph_D a
  let Wd : Opens (PrimeSpectrum.basicOpen a) :=
    ⟨e '' (Wloc : Set (PrimeSpectrum (Localization.Away a))), e.isOpenMap _ Wloc.2⟩
  have hWd_dense : Dense (Wd : Set (PrimeSpectrum.basicOpen a)) := by
    have hpre :
        e.symm ⁻¹' (Wloc : Set (PrimeSpectrum (Localization.Away a))) =
          (Wd : Set (PrimeSpectrum.basicOpen a)) := by
      ext z
      constructor
      · intro hz
        exact ⟨e.symm z, hz, by simp [e]⟩
      · rintro ⟨w, hw, rfl⟩
        simpa [e] using hw
    -- Density is preserved across the localization-basic-open homeomorphism.
    rw [← hpre]
    exact Dense.preimage hWloc_dense e.symm.isOpenMap
  have hWd_subset :
      (Wd : Set (PrimeSpectrum.basicOpen a)) ⊆
        ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
          (PrimeSpectrum.comap fbar '' Eη)) := by
    intro x hx
    rcases hx with ⟨xloc, hxlocW, rfl⟩
    -- The pointwise adapter turns every localized witness into a witness on `D(a)`.
    exact localized_chart_homeomorph_pointwise_to_basicOpen_trace
      (f := f) (E := E) (ξ := ξ) (η := η) (a := a) (b := b) (xloc := xloc) hηξ
      (hWloc_subset hxlocW)
  exact ⟨Wd, hWd_dense, hWd_subset⟩

/-- Helper for Lemma 10.30.2: a dense open subset of the basic open `D(a)` inside the quotient
trace extends to a dense open subset of the whole quotient spectrum inside the same image. -/
lemma basicOpen_trace_open_dense_to_quotient_image
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {a : R ⧸ ξ.asIdeal} (ha : a ≠ 0)
    {Wd : Opens (PrimeSpectrum.basicOpen a)}
    (hWd_dense : Dense (Wd : Set (PrimeSpectrum.basicOpen a)))
    (hWd_subset :
      let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
      let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
        PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
      (Wd : Set (PrimeSpectrum.basicOpen a)) ⊆
        ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
          (PrimeSpectrum.comap fbar '' Eη))) :
    let fbar := quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ
    let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
      PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
    ∃ W : Opens (PrimeSpectrum (R ⧸ ξ.asIdeal)),
      Dense (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ∧
        (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ⊆
          PrimeSpectrum.comap fbar '' Eη := by
  intro fbar Eη
  have hU_open :
      IsOpen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) :=
    PrimeSpectrum.isOpen_basicOpen
  have hU_dense :
      Dense (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) :=
    basicOpen_dense_of_nonzero_of_isDomain a ha
  obtain ⟨W, hW_dense, hW_subset_basic, hW_preimage⟩ :=
    image_open_dense_of_dense_open_subspace
      (U := (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))))
      hU_open hU_dense Wd.2 hWd_dense
  refine ⟨W, hW_dense, ?_⟩
  intro x hxW
  have hxU : x ∈ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) :=
    hW_subset_basic hxW
  have hxPre :
      (⟨x, hxU⟩ : PrimeSpectrum.basicOpen a) ∈
        ((Subtype.val : PrimeSpectrum.basicOpen a → PrimeSpectrum (R ⧸ ξ.asIdeal)) ⁻¹'
          (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal)))) := by
    simpa using hxW
  have hxWd : (⟨x, hxU⟩ : PrimeSpectrum.basicOpen a) ∈ (Wd : Set (PrimeSpectrum.basicOpen a)) := by
    change (⟨x, hxU⟩ : PrimeSpectrum.basicOpen a) ∈ Wd.carrier
    exact hW_preimage ▸ hxPre
  -- Returning from the dense basic-open chart does not change the image witness.
  simpa using hWd_subset hxWd

/-- Helper for Lemma 10.30.2: a quotient-spectrum witness in the descended image maps to the
trace of `comap f '' E` on `closure {ξ}` under the quotient-spectrum homeomorphism. -/
lemma quotient_homeomorph_trace_pointwise
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {w : PrimeSpectrum (R ⧸ ξ.asIdeal)} {y : PrimeSpectrum (S ⧸ η.asIdeal)}
    (hy :
      y ∈ PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E)
    (hw :
      PrimeSpectrum.comap (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ) y = w) :
    let e : PrimeSpectrum (R ⧸ ξ.asIdeal) ≃ₜ Zξ :=
      (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus ξ.asIdeal).trans
        (Homeomorph.setCongr <| (PrimeSpectrum.closure_singleton ξ).symm)
    e w ∈ traceOnClosure := by
  intro e
  change ((e w : Zξ) : PrimeSpectrum R) ∈ PrimeSpectrum.comap f '' E
  refine ⟨PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) y, hy, ?_⟩
  -- Rewrite the witness through the descended quotient map, then identify the quotient-spectrum
  -- point with its image in `closure {ξ}`.
  change PrimeSpectrum.comap f (PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) y) =
    ((e w : Zξ) : PrimeSpectrum R)
  rw [← PrimeSpectrum.comap_comp_apply]
  rw [← quotient_map_of_comap_eq_comp_quotient_mk (f := f) (ξ := ξ) hηξ]
  rw [PrimeSpectrum.comap_comp_apply, hw]
  change PrimeSpectrum.comap (Ideal.Quotient.mk ξ.asIdeal) w =
    ((Ideal.primeSpectrum_quotient_homeomorph_zeroLocus ξ.asIdeal w :
      V((ξ.asIdeal : Set R))) : PrimeSpectrum R)
  simpa using
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus_apply ξ.asIdeal w).symm

/-- Helper for Lemma 10.30.2: a dense open subset of `Spec(R / ξ)` contained in the quotient
image transports to a dense open subset of `closure {ξ}` contained in the original trace. -/
lemma closure_open_dense_of_quotient_image_subset
    {η : PrimeSpectrum S} (hηξ : PrimeSpectrum.comap f η = ξ)
    {W : Opens (PrimeSpectrum (R ⧸ ξ.asIdeal))}
    (hW_dense : Dense (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))))
    (hW_subset :
      (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ⊆
        PrimeSpectrum.comap (quotient_map_of_comap_eq (f := f) (ξ := ξ) hηξ) ''
          (PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E)) :
    ∃ U : Opens Zξ, Dense (U : Set Zξ) ∧ (U : Set Zξ) ⊆ traceOnClosure := by
  let e : PrimeSpectrum (R ⧸ ξ.asIdeal) ≃ₜ Zξ :=
    (Ideal.primeSpectrum_quotient_homeomorph_zeroLocus ξ.asIdeal).trans
      (Homeomorph.setCongr <| (PrimeSpectrum.closure_singleton ξ).symm)
  let U : Opens Zξ := ⟨e '' (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))), e.isOpenMap _ W.2⟩
  have hU_dense : Dense (U : Set Zξ) := by
    have hpre : e.symm ⁻¹' (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) = (U : Set Zξ) := by
      ext z
      constructor
      · intro hz
        exact ⟨e.symm z, hz, by simp⟩
      · rintro ⟨w, hw, rfl⟩
        simpa using hw
    -- A homeomorphism preserves density by turning the target set into a preimage.
    simpa [hpre] using Dense.preimage hW_dense e.symm.isOpenMap
  refine ⟨U, hU_dense, ?_⟩
  intro z hz
  rcases hz with ⟨w, hwW, rfl⟩
  rcases hW_subset hwW with ⟨y, hy, hw⟩
  -- The quotient-spectrum witness `y` already lands in the original trace after transporting the
  -- target point across the quotient homeomorphism.
  simpa [e] using
    quotient_homeomorph_trace_pointwise (f := f) (E := E) (ξ := ξ) hηξ hy hw

-- Proof sketch: replace `Spec R` by the irreducible closed subset `closure {ξ}` and the source by
-- the closure of a point of `E` above `ξ`, so that `ξ` becomes a generic point. Lemma `10.30.1`
-- gives dense opens on which the finite type map is finitely presented, Chevalley's theorem makes
-- the corresponding image constructible, and the generic-point criterion for constructible subsets
-- then yields an open dense subset of `closure {ξ}` contained in the image.
/-- Lemma 10.30.2: for a finite type ring map `f : R →+* S` and a constructible subset
`E ⊆ Spec(S)`, if `ξ ∈ Spec(R)` lies in the image of `E` under `Spec(S) → Spec(R)`, then the
trace of that image on `closure {ξ}` contains an open dense subset of `closure {ξ}`. -/
lemma exists_open_dense_subset_closure_singleton_of_mem_comap_image_constructible
    (f : R →+* S) (hf : f.FiniteType) (hE : IsConstructible E) (hξ : ξ ∈ comap f '' E) :
    ∃ U : Opens Zξ,
      Dense (U : Set Zξ) ∧
        (U : Set Zξ) ⊆
          ((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹' (PrimeSpectrum.comap f '' E)) := by
  let f₀ : R →+* S := f
  rcases hξ with ⟨η, hηE, hηξ⟩
  letI : IsDomain (R ⧸ ξ.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime (I := ξ.asIdeal)).2 ξ.isPrime
  letI : IsDomain (S ⧸ η.asIdeal) :=
    (Ideal.Quotient.isDomain_iff_prime (I := η.asIdeal)).2 η.isPrime
  let fbar := quotient_map_of_comap_eq (f := f₀) (ξ := ξ) hηξ
  let Eη : Set (PrimeSpectrum (S ⧸ η.asIdeal)) :=
    PrimeSpectrum.comap (Ideal.Quotient.mk η.asIdeal) ⁻¹' E
  have hquotientLoc :=
    quotient_localization_data_of_comap_eq (f := f₀) (ξ := ξ) hf hηξ
  have hquotientE :=
    quotient_preimage_constructible_generic_mem (E := E) hE hηE
  rcases hquotientLoc with ⟨a, ha, b, hb, hfp⟩
  let g :
      Localization.Away a →+* Localization.Away ((fbar a) * b) :=
    ((IsLocalization.Away.awayToAwayRight (fbar a) b).comp
      (Localization.awayMap fbar a))
  let Eloc : Set (PrimeSpectrum (Localization.Away ((fbar a) * b))) :=
    PrimeSpectrum.comap
        (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
  have hquotientTarget :
      ∃ W : Opens (PrimeSpectrum (R ⧸ ξ.asIdeal)),
        Dense (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ∧
          (W : Set (PrimeSpectrum (R ⧸ ξ.asIdeal))) ⊆
            PrimeSpectrum.comap fbar '' Eη := by
    have hfbar_inj : Function.Injective fbar :=
      quotient_map_of_comap_eq_injective (f := f₀) (ξ := ξ) hηξ
    have hfa : fbar a ≠ 0 := by
      -- The localized chart has to stay away from a nonzero element of the quotient domain.
      intro hzero
      exact ha (hfbar_inj <| by simpa using hzero)
    have hab : (fbar a) * b ≠ 0 := mul_ne_zero hfa hb
    letI : IsDomain (Localization.Away a) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.Away a)
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
    letI : IsDomain (Localization.Away ((fbar a) * b)) :=
      IsLocalization.isDomain_of_le_nonZeroDivisors
        (Localization.Away ((fbar a) * b))
        (powers_le_nonZeroDivisors_of_noZeroDivisors hab)
    have hEloc :
        IsConstructible Eloc ∧
          (⟨⊥, Ideal.isPrime_bot⟩ :
              PrimeSpectrum (Localization.Away ((fbar a) * b))) ∈ Eloc := by
      have hEloc' :=
        localized_preimage_constructible_generic_mem
          (B := S ⧸ η.asIdeal) (c := (fbar a) * b) (C := Eη) hab hquotientE.1 hquotientE.2
      -- Pull the quotient constructible set containing the generic point to the localized chart.
      change IsConstructible
          (PrimeSpectrum.comap
            (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη) ∧
            (⟨⊥, Ideal.isPrime_bot⟩ :
                PrimeSpectrum (Localization.Away ((fbar a) * b))) ∈
              PrimeSpectrum.comap
                (algebraMap (S ⧸ η.asIdeal) (Localization.Away ((fbar a) * b))) ⁻¹' Eη
      exact hEloc'
    have hImageConstructible :
        IsConstructible (PrimeSpectrum.comap g '' Eloc) := by
      -- Chevalley on the finite-presentation localized chart gives constructibility of its image.
      simpa [g] using PrimeSpectrum.isConstructible_comap_image hfp hEloc.1
    have hgenericImage :
        (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (Localization.Away a)) ∈
          PrimeSpectrum.comap g '' Eloc := by
      -- The localized generic point of `Eloc` contracts to the generic point of `Spec((R / ξ)_a)`.
      refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ :
        PrimeSpectrum (Localization.Away ((fbar a) * b))), hEloc.2, ?_⟩
      apply PrimeSpectrum.ext
      exact localized_chart_comap_bot_eq_bot
        (f := f₀) (ξ := ξ) hηξ ha hb
    obtain ⟨Wloc, hWloc_dense, hWloc_subset⟩ :=
      exists_open_dense_subset_of_constructible_generic_mem hImageConstructible hgenericImage
    obtain ⟨Wd, hWd_dense, hWd_subset⟩ :=
      localized_chart_dense_open_in_basicOpen_trace
        (f := f₀) (E := E) (ξ := ξ) (η := η) (a := a) (b := b) hηξ hWloc_dense hWloc_subset
    -- Transport the localized dense open to `D(a)`, then extend it to the whole quotient
    -- spectrum using that `D(a)` is dense because `a ≠ 0`.
    exact basicOpen_trace_open_dense_to_quotient_image
      (f := f₀) (E := E) (ξ := ξ) (η := η) (a := a) hηξ ha hWd_dense hWd_subset
  -- Route correction: the direct Chevalley route stops here because mathlib only gives
  -- constructibility of `comap f '' E` for finite-presentation maps. The source-proof reduction
  -- must therefore pass to quotient domains at `ξ` and `η`, use Lemma `10.30.1` on the localized
  -- chart `g : Spec(S_(fbar(a)b)) → Spec(R_a)`, produce `hquotientTarget`, and only then return
  -- from `Spec(R / ξ)` to `closure {ξ}` via
  -- `closure_open_dense_of_quotient_image_subset`, which is now proved above.
  rcases hquotientTarget with ⟨W, hW_dense, hW_subset⟩
  have hfinal :
      ∃ U : Opens Zξ,
        Dense (U : Set Zξ) ∧
          (U : Set Zξ) ⊆
            ((Subtype.val : Zξ → PrimeSpectrum R) ⁻¹' (PrimeSpectrum.comap f₀ '' E)) := by
    -- The quotient-spectrum dense open returns to `closure {ξ}` through the canonical
    -- homeomorphism and lands in the explicit theorem-local trace set.
    simpa [f₀] using
      closure_open_dense_of_quotient_image_subset
        (f := f₀) (E := E) (ξ := ξ) hηξ hW_dense hW_subset
  simpa [f₀] using hfinal

end

/-! ### Lemma_10_30_3 (from Chap10) -/
universe u v w

open scoped TensorProduct
open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

local notation "f" => algebraMap R S

/- Layering for this item:
* source-facing: the TFAE characterizing surjectivity of `Spec S → Spec R` in terms of
  contraction formulas for extended ideals, plus its stability under arbitrary base change;
* core/canonical owner: `PrimeSpectrum.comap (algebraMap R S)` together with the ideal
  operations `Ideal.map`, `Ideal.comap`, and `Ideal.radical`;
* bridge/view: Lemma `10.18.6`, `PrimeSpectrum.mem_range_comap_iff`,
  `PrimeSpectrum.nontrivial_iff_mem_rangeComap`, `Ideal.comap_radical`, and
  `Ideal.radical_eq_sInf`, which translate between the owner map on spectra and the textbook
  contraction criteria.
-/

/-- Helper for Lemma 10.30.3: mapping an ideal or first replacing it by its radical gives the
same radical after extension to `S`. -/
-- The only content is the radical bookkeeping bridge used to pass between the arbitrary-ideal
-- clause and the radical-ideal clause of the source proof.
lemma radical_map_eq_radical_map_radical (I : Ideal R) :
    (I.map f).radical = (I.radical.map f).radical := by
  apply le_antisymm
  · -- Monotonicity of `map` and `radical` gives the easy inclusion.
    exact Ideal.radical_mono (Ideal.map_mono Ideal.le_radical)
  · -- The reverse inclusion is exactly `map_radical_le`, upgraded through radicality.
    exact (Ideal.radical_isRadical _).radical_le_iff.mpr (Ideal.map_radical_le f)

/-- Helper for Lemma 10.30.3: if every extended prime contracts back to itself, then the same
contraction formula holds for every radical ideal. -/
-- This packages the source-proof step that recovers a radical ideal as the intersection of the
-- primes containing it and checks membership prime-by-prime.
lemma prime_contraction_implies_radical_ideal_contraction
    (hprime : ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal) :
    ∀ I : Ideal R, I.IsRadical → (I.map f).comap f = I := by
  intro I hI
  apply le_antisymm
  · intro x hx
    -- Rewrite membership in the radical ideal as membership in every prime above it.
    rw [← hI.radical, Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    have hx_map : algebraMap R S x ∈ I.map f := by
      simpa [Ideal.mem_comap] using hx
    have hx_prime_map : algebraMap R S x ∈ Ideal.map f P :=
      (Ideal.map_mono hP.1) hx_map
    have hx_prime_comap : x ∈ (Ideal.map f P).comap f := by
      simpa [Ideal.mem_comap] using hx_prime_map
    have hP_contract : (Ideal.map f P).comap f = P := hprime ⟨P, hP.2⟩
    simpa [hP_contract] using hx_prime_comap
  · -- Extension followed by contraction always contains the original ideal.
    exact Ideal.le_comap_map

/-- Helper for Lemma 10.30.3: surjectivity of `Spec S → Spec R` is equivalent to the prime-wise
contraction formula `φ⁻¹(pS) = p` for every prime `p`. -/
-- This is the pointwise owner-level image criterion rewritten as a global surjectivity statement.
lemma surjective_iff_forall_prime_contraction :
    Function.Surjective (comap f) ↔
      ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal := by
  constructor
  · intro hsurj p
    exact (PrimeSpectrum.mem_range_comap_iff f).mp (hsurj p)
  · intro hprime p
    exact (PrimeSpectrum.mem_range_comap_iff f).mpr (hprime p)

/-- Lemma 10.30.3: for a ring map `R → S`, the following are equivalent: `Spec S → Spec R` is
surjective, contraction of `√(IS)` is `√I` for every ideal `I`, contraction of `IS` is `I` for
every radical ideal `I`, and contraction of `pS` is `p` for every prime `p` of `R`. -/
-- Proof sketch: the owner object is the canonical spectral map `comap f : Spec S → Spec R`.
-- Use `Ideal.comap_radical` to identify the radical clause with the radical-ideal clause,
-- `Ideal.radical_eq_sInf` to recover a radical ideal as the intersection of primes containing it,
-- and `mem_range_comap_iff` together with Lemma 10.18.6 to identify surjectivity of `comap f`
-- with the prime-ideal contraction condition.
theorem specComap_surjective_tfae :
    List.TFAE
      [ Function.Surjective (comap f),
        ∀ I : Ideal R,
          ((I.map f).radical).comap f = I.radical,
        ∀ I : Ideal R, I.IsRadical → (I.map f).comap f = I,
        ∀ p : PrimeSpectrum R, (p.asIdeal.map f).comap f = p.asIdeal ] := by
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h I hI
      -- Rewrite the radical clause through `comap_radical`, then use radicality of `I`.
      have hrad : ((I.map f).comap f).radical = I := by
        simpa [Ideal.comap_radical, hI.radical] using h I
      exact le_antisymm
        ((hI.radical_le_iff).mp (le_of_eq hrad))
        Ideal.le_comap_map
    · intro h I
      -- Apply the radical-ideal clause to `I.radical` and transport it back to `I`.
      calc
        ((I.map f).radical).comap f = (((I.radical).map f).radical).comap f := by
          rw [radical_map_eq_radical_map_radical]
        _ = (((I.radical).map f).comap f).radical := by
          rw [Ideal.comap_radical]
        _ = I.radical := by
          rw [h I.radical (Ideal.radical_isRadical _), Ideal.radical_idem]
  tfae_have 3 → 4 := by
    intro h p
    -- A prime ideal is radical, so the radical-ideal contraction formula applies directly.
    simpa using h p.asIdeal p.isPrime.isRadical
  tfae_have 4 → 3 := by
    intro h
    -- This is the source-proof intersection-of-primes step, packaged as a reusable helper.
    exact prime_contraction_implies_radical_ideal_contraction h
  tfae_have 1 ↔ 4 := by
    -- Surjectivity is exactly the pointwise image criterion on prime ideals.
    exact surjective_iff_forall_prime_contraction
  tfae_finish

section BaseChange

variable {R' : Type w} [CommRing R'] [Algebra R R']

/-- Helper for Lemma 10.30.3: nontriviality of a fiber ring is preserved after arbitrary base
change along `R → R'`. -/
-- The source proof identifies the new fiber with scalar extension of the old fiber from
-- `κ(p)` to `κ(p')`, and scalar extension over a field preserves nontriviality because the
-- canonical `includeRight` map is injective.
lemma baseChange_fiber_nontrivial (p' : PrimeSpectrum R') :
    Nontrivial ((p'.asIdeal.under R).Fiber S) →
      Nontrivial (p'.asIdeal.Fiber (R' ⊗[R] S)) := by
  intro hfiber
  let p : Ideal R := p'.asIdeal.under R
  let e :
      p'.asIdeal.Fiber (R' ⊗[R] S) ≃ₐ[p'.asIdeal.ResidueField]
        p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  have hcod :
      Nontrivial (p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S)) := by
    -- Scalar extension is injective on the fiber ring because residue-field extensions are
    -- injective and tensoring over a field is flat.
    let j :
        p.Fiber S →ₐ[p.ResidueField]
          p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S) :=
      Algebra.TensorProduct.includeRight
    have hj : Function.Injective j :=
      Algebra.TensorProduct.includeRight_injective
        (A := p'.asIdeal.ResidueField) (B := p.Fiber S)
        (ha := RingHom.injective (algebraMap p.ResidueField p'.asIdeal.ResidueField))
    let _ : Nontrivial (p.Fiber S) := hfiber
    exact hj.nontrivial
  let _ : Nontrivial (p'.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber S)) := hcod
  exact RingHom.domain_nontrivial e.toRingHom

/-- If `Spec S → Spec R` is surjective, then every base change `Spec (R' ⊗[R] S) → Spec R'` is
also surjective. The corresponding contraction formulas for the base-changed map then follow from
`specComap_surjective_tfae`. -/
-- Proof sketch: for `p' : Spec R'` lying over `p : Spec R`, apply Lemma 10.18.6 to reduce
-- surjectivity of `Spec (R' ⊗[R] S) → Spec R'` to nontriviality of the fiber ring over `p'`.
-- Identify that fiber with `(S ⊗[R] κ(p)) ⊗[κ(p)] κ(p')`, which is nontrivial because the first
-- factor is nontrivial by the surjectivity hypothesis and the second map is an extension of
-- fields.
theorem specComap_surjective_stable_under_baseChange
    (h : Function.Surjective (comap f)) :
    Function.Surjective (comap (algebraMap R' (R' ⊗[R] S))) := by
  intro p'
  let p : PrimeSpectrum R := comap (algebraMap R R') p'
  have hp_mem : p ∈ Set.range (comap f) := h p
  have hp_fiber : Nontrivial (p.asIdeal.Fiber S) := by
    exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p).mpr hp_mem
  have hp'_fiber : Nontrivial ((p'.asIdeal.under R).Fiber S) := by
    simpa [p, PrimeSpectrum.comap_asIdeal] using hp_fiber
  have hbase_fiber : Nontrivial (p'.asIdeal.Fiber (R' ⊗[R] S)) :=
    baseChange_fiber_nontrivial (R := R) (S := S) p' hp'_fiber
  exact (PrimeSpectrum.nontrivial_iff_mem_rangeComap p').mp hbase_fiber

end BaseChange

end

/-! ### Lemma_10_30_4 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R] [CommRing S]

/-- Lemma 10.30.4: for a ring map `φ : R →+* S` with `R` a domain, the following are equivalent:
`φ` is injective, `Spec S → Spec R` has dense range, and the generic point `(0)` of `Spec R`
lies in the image. This is the domain specialization of the general dense-range TFAE in
`Lemma_10_30_6`, using that a domain has nilradical `0` and a unique minimal point `(0)`. -/
theorem ringHom_injective_tfae_of_image_contains_dense_set
    (φ : R →+* S) :
    List.TFAE
      [ Function.Injective φ,
        DenseRange (comap φ),
        (⊥ : PrimeSpectrum R) ∈ Set.range (comap φ) ] := by
  have howner := denseRange_comap_tfae_ker_le_nilradical_minimalPrimes φ
  have hinjective : Function.Injective φ ↔ RingHom.ker φ ≤ nilradical R := by
    rw [RingHom.injective_iff_ker_eq_bot]
    simp [le_bot_iff]
  have hminimal :
      (∀ p : PrimeSpectrum R, IsMin p → p ∈ Set.range (comap φ)) ↔
        (⊥ : PrimeSpectrum R) ∈ Set.range (comap φ) := by
    constructor
    · intro h
      exact h ⊥ <| by
        rw [isMin_iff]
        simp [IsDomain.minimalPrimes_eq_singleton_bot R]
    · intro h p hp
      have hp_bot : p = ⊥ := by
        rw [isMin_iff] at hp
        apply PrimeSpectrum.ext
        simpa [IsDomain.minimalPrimes_eq_singleton_bot R] using hp
      simpa [hp_bot] using h
  tfae_have 1 ↔ 2 := by
    exact hinjective.trans (howner.out 0 2)
  tfae_have 2 ↔ 3 := by
    exact (howner.out 2 1).trans hminimal
  tfae_finish

end

/-! ### Lemma_10_30_5 (from Chap10) -/
/- Lemma 10.30.5: for an injective ring homomorphism `f : R →+* S`, every minimal prime ideal
of `R` is the contraction of a prime ideal of `S`. This is exactly the canonical owner theorem
`Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective` (Stacks tag `00FK`). -/
recall Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective

/-! ### Lemma_10_30_6 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.30.6: for a ring map `f : R →+* S`, the following are equivalent: the kernel of `f`
consists of nilpotent elements, every minimal prime ideal of `R` (equivalently every minimal point
of `Spec R`) lies in the image of `Spec(S) → Spec(R)`, and the image of `Spec(S) → Spec(R)` is
dense in `Spec(R)`. -/
-- Proof sketch: the owner abstraction is `DenseRange (comap f)`. Mathlib identifies this both with
-- `RingHom.ker f ≤ nilradical R` via `PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical` and
-- with the minimal-prime condition via `PrimeSpectrum.denseRange_comap_iff_minimalPrimes`;
-- `PrimeSpectrum.isMin_iff` rewrites that owner theorem into the intrinsic minimal-point form.
theorem denseRange_comap_tfae_ker_le_nilradical_minimalPrimes (f : R →+* S) :
    List.TFAE
      [ RingHom.ker f ≤ nilradical R,
        ∀ p : PrimeSpectrum R, IsMin p → p ∈ Set.range (comap f),
        DenseRange (comap f) ] := by
  tfae_have 1 ↔ 3 := (denseRange_comap_iff_ker_le_nilRadical f).symm
  tfae_have 2 ↔ 3 := by
    constructor
    · intro h
      rw [denseRange_comap_iff_minimalPrimes]
      intro I hI
      exact h ⟨I, Ideal.minimalPrimes_isPrime hI⟩ (isMin_iff.mpr hI)
    · intro h p hp
      simpa using ((denseRange_comap_iff_minimalPrimes f).mp h) p.asIdeal (isMin_iff.mp hp)
  tfae_finish

end

/-! ### Lemma_10_30_7 (from Chap10) -/
universe u v

open PrimeSpectrum

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 10.30.7: if a minimal point `p` of `Spec R` lies in the image of `Spec S → Spec R`,
then it is the image of a minimal point of `Spec S`. By `isMin_iff`, this is
equivalent to the source statement about minimal prime ideals. -/
-- Proof sketch: the image hypothesis shows `ker f ≤ p.asIdeal`, so `p.asIdeal` is a minimal
-- prime over `ker f`. The owner lemma `Ideal.exists_minimalPrimes_comap_eq` then produces a
-- minimal prime `q'` of `S` with `comap f q' = p`.
theorem exists_isMin_comap_eq_of_mem_range_comap (f : R →+* S) (p : PrimeSpectrum R)
    (hp : IsMin p) (hp_range : p ∈ Set.range (comap f)) :
    ∃ q : PrimeSpectrum S, IsMin q ∧ comap f q = p := by
  rcases hp_range with ⟨q, hq⟩
  have hp' : p.asIdeal ∈ (RingHom.ker f).minimalPrimes := by
    refine ⟨⟨p.2, ?_⟩, ?_⟩
    · rw [← hq]
      exact Ideal.ker_le_comap f
    intro I hI hIp
    exact (isMin_iff.mp hp).2 ⟨hI.1, bot_le⟩ hIp
  obtain ⟨q', hq', hq'eq⟩ := Ideal.exists_minimalPrimes_comap_eq f p.asIdeal hp'
  exact ⟨⟨q', Ideal.minimalPrimes_isPrime hq'⟩, isMin_iff.mpr hq', PrimeSpectrum.ext hq'eq⟩

end

/-! ### Lemma_10_30_8 (from Chap10) -/
noncomputable section

universe u v

open PrimeSpectrum Set Topology

section

variable {A : Type u} [CommRing A]
variable {B : Type v} [CommRing B] [IsDomain B]
variable [Algebra A B]
variable [IsDomain A]
variable [Algebra (FractionRing A) (FractionRing B)]
variable [IsScalarTower A (FractionRing A) (FractionRing B)]
variable [Algebra.IsAlgebraic (FractionRing A) (FractionRing B)]

local notation "f" => algebraMap A B

-- Proof sketch: `Frac(B)` is algebraic over `Frac(A)`, hence also algebraic over `A` by
-- `IsFractionRing.comap_isAlgebraic_iff`. Since `B` injects into `Frac(B)`, the `A`-algebra `B`
-- is algebraic as well.
omit [IsDomain B] in
private theorem isAlgebraic_of_fractionRing_isAlgebraic :
    Algebra.IsAlgebraic A B := by
  let _ : Algebra.IsAlgebraic A (FractionRing B) :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing B))
  exact
    Algebra.IsAlgebraic.of_injective (IsScalarTower.toAlgHom A B (FractionRing B))
      (IsFractionRing.injective B (FractionRing B))

-- Proof sketch: the closure of the image of `V(J)` under `Spec B → Spec A` is
-- `V(J.comap (algebraMap A B))` by `closure_image_comap_zeroLocus`. The first theorem supplies the
-- contradiction once density forces `J.comap f = ⊥`.
/-
Domain-style triage for Lemma 10.30.8:
* source-facing layer: nonzero ideals of `B` contract nontrivially to `A`, and the corresponding
  closed subsets of `Spec B` have nondense image in `Spec A`.
* sampled canonical owners in this domain:
  `algebraMap_injective_of_field_isFractionRing`,
  `IsFractionRing.comap_isAlgebraic_iff`,
  `Ideal.comap_ne_bot_of_algebraic_mem`,
  `PrimeSpectrum.closure_image_comap_zeroLocus`.
* core owner abstraction: the induced public fraction-field tower
  `[Algebra K L] [IsScalarTower A K L] [Algebra.IsAlgebraic K L]`.
* primitive data: the domain map `A → B`, the induced fraction fields `K = Frac(A)` and
  `L = Frac(B)`, and the nonzero ideal `J`.
* bridge/view: the internal bridge `isAlgebraic_of_fractionRing_isAlgebraic`, upgrading the
  algebraic fraction-field extension to algebraicity of `A → B`.
* derived API: injectivity of `A → B` from
  `algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)`, then the
  ideal/topological consequences from `Ideal.comap_ne_bot_of_algebraic_mem` and
  `PrimeSpectrum.closure_image_comap_zeroLocus`.
-/

/-- Lemma 10.30.8: if the induced fraction-field extension `Frac(B) / Frac(A)` is algebraic, then
every nonzero ideal of `B` has nonzero contraction to `A`. Under the tower hypotheses below,
injectivity of `A → B` is automatic from
`algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)`. -/
theorem ideal_comap_ne_bot_of_ne_bot (J : Ideal B) (hJ : J ≠ ⊥) :
    J.comap f ≠ ⊥ := by
  let _ : Algebra.IsAlgebraic A B := isAlgebraic_of_fractionRing_isAlgebraic
  obtain ⟨x, hxJ, hx0⟩ := (Submodule.ne_bot_iff _).mp hJ
  exact Ideal.comap_ne_bot_of_algebraic_mem hx0 hxJ (Algebra.IsAlgebraic.isAlgebraic x)

/-- If the induced fraction-field extension `Frac(B) / Frac(A)` is algebraic, then the image of
the proper closed subset `V(J)` is not dense in `Spec A`. Under the tower hypotheses below,
injectivity of `A → B` is automatic from
`algebraMap_injective_of_field_isFractionRing A B (FractionRing A) (FractionRing B)`. -/
theorem not_dense_image_zeroLocus_of_ne_bot (J : Ideal B) (hJ : J ≠ ⊥) :
    ¬ Dense (comap f '' zeroLocus J) := by
  intro hDense
  have hclosure :
      closure (comap f '' zeroLocus J) = zeroLocus (J.comap f : Set A) := by
    exact closure_image_comap_zeroLocus f J
  have hzero : zeroLocus (J.comap f : Set A) = univ := by
    rw [← hclosure, dense_iff_closure_eq.mp hDense]
  have hle : J.comap f ≤ nilradical A :=
    zeroLocus_eq_univ_iff _ |>.mp hzero
  have hnil : nilradical A = ⊥ := by
    rw [nilradical_eq_bot_iff]
    infer_instance
  have hbot : J.comap f = ⊥ := by
    apply eq_bot_iff.mpr
    rw [← hnil]
    exact hle
  exact ideal_comap_ne_bot_of_ne_bot J hJ hbot

end
