import Mathlib
import StacksProject_2024.Chap10.Definition_10_153_1
import StacksProject_2024.Chap10.Lemma_10_153_11

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v w

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [StrictHenselianLocalRing R] [StrictHenselianLocalRing S]
variable (φ : R →+* S) [IsLocalHom φ]
variable {n : ℕ}

/-- Helper for Chap10 Lemma 10 153 12: the ordinary residue field of a local ring is equivalent
to the residue field attached to its maximal ideal. -/
noncomputable def maximalIdealResidueFieldEquiv (T : Type*) [CommRing T] [IsLocalRing T] :
    ResidueField T ≃+* (maximalIdeal T).ResidueField :=
  RingEquiv.ofBijective (algebraMap (ResidueField T) (maximalIdeal T).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal T))

/-- Helper for Chap10 Lemma 10 153 12: the maximal-ideal residue field of a strictly henselian
local ring is separably closed. -/
lemma isSepClosed_maximalIdealResidueField (T : Type*) [CommRing T]
    [StrictHenselianLocalRing T] :
    IsSepClosed (maximalIdeal T).ResidueField := by
  -- Proof comment: transport separable splitting across the canonical residue-field equivalence.
  let e := maximalIdealResidueFieldEquiv T
  refine ⟨fun p hp ↦ ?_⟩
  refine Polynomial.Splits.of_splits_map e.symm.toRingHom ?_ ?_
  · simpa using (IsSepClosed.splits_of_separable (p.map e.symm.toRingHom) hp.map)
  · intro a _ha
    refine ⟨e a, ?_⟩
    simp [e]

/-- Helper for Chap10 Lemma 10 153 12: over a strictly henselian local base, the residue-field
map at any prime of an étale algebra lying over the maximal ideal is bijective. -/
lemma bijective_residueFieldMap_of_strictHenselian_etale_prime
    {A : Type w} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (hq : q.under R = maximalIdeal R) :
    Function.Bijective (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hq.symm) := by
  -- Proof comment: the map is a field embedding, and étaleness makes the target residue field a
  -- separable extension of the separably closed source residue field.
  constructor
  · exact RingHom.injective _
  · haveI : q.LiesOver (maximalIdeal R) := ⟨hq.symm⟩
    haveI : Algebra.IsUnramifiedAt R q := inferInstance
    haveI : Algebra.IsSeparable (maximalIdeal R).ResidueField q.ResidueField := inferInstance
    haveI : IsSepClosed (maximalIdeal R).ResidueField := isSepClosed_maximalIdealResidueField R
    simpa using
      (IsSepClosed.algebraMap_surjective (maximalIdeal R).ResidueField q.ResidueField)

/-- Helper for Chap10 Lemma 10 153 12: an `S`-valued point of an `R`-algebra pulls the maximal
ideal of `S` back to a prime of the algebra lying over the maximal ideal of `R`. -/
lemma algHom_comap_maximalIdeal_under_of_localHom
    {A : Type w} [CommRing A] [Algebra R A] :
    letI : Algebra R S := φ.toAlgebra
    ∀ g : A →ₐ[R] S,
      (Ideal.comap (g : A →+* S) (maximalIdeal S)).under R = maximalIdeal R := by
  letI : Algebra R S := φ.toAlgebra
  intro g
  -- Proof comment: pull the maximal ideal back through the composite `R → A → S`, which is `φ`.
  rw [Ideal.under_def, Ideal.comap_comap]
  have hcomp : (g : A →+* S).comp (algebraMap R A) = φ := by
    ext x
    exact g.commutes x
  rw [hcomp]
  exact IsLocalRing.maximalIdeal_comap φ

/-- Helper for Chap10 Lemma 10 153 12: composing an `R`-valued point with a local map to `S`
does not change the pulled-back maximal ideal except through the local map. -/
lemma algHom_comap_maximalIdeal_comp_of_localHom
    {A : Type w} [CommRing A] [Algebra R A] :
    letI : Algebra R S := φ.toAlgebra
    ∀ f : A →ₐ[R] R,
      Ideal.comap ((((Algebra.ofId R S).comp f : A →ₐ[R] S) : A →+* S))
          (maximalIdeal S) =
        Ideal.comap (f : A →+* R) (maximalIdeal R) := by
  letI : Algebra R S := φ.toAlgebra
  intro f
  -- Proof comment: membership is tested by nonunits, and a local map reflects units.
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  exact not_iff_not.mpr (isUnit_map_iff φ (f a))

omit [StrictHenselianLocalRing S] in
/-- Helper for Chap10 Lemma 10 153 12: two `R`-valued points with the same composite to `S`
pull back the maximal ideal of `R` to the same ideal. -/
lemma algHom_comap_maximalIdeal_eq_of_localHom_comp_eq
    {A : Type w} [CommRing A] [Algebra R A] (f g : A →ₐ[R] R) :
    letI : Algebra R S := φ.toAlgebra
    (Algebra.ofId R S).comp f = (Algebra.ofId R S).comp g →
      Ideal.comap (f : A →+* R) (maximalIdeal R) =
        Ideal.comap (g : A →+* R) (maximalIdeal R) := by
  letI : Algebra R S := φ.toAlgebra
  intro hfg
  -- Proof comment: equality after applying `φ` and unit reflection identify the nonunit tests.
  ext a
  rw [Ideal.mem_comap, Ideal.mem_comap]
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
  have happ : φ (f a) = φ (g a) := by
    simpa using AlgHom.congr_fun hfg a
  have hmap : IsUnit (φ (f a)) ↔ IsUnit (φ (g a)) := by
    rw [happ]
  have hunit : IsUnit (f a) ↔ IsUnit (g a) :=
    ((isUnit_map_iff φ (f a)).symm.trans hmap).trans (isUnit_map_iff φ (g a))
  exact not_iff_not.mpr hunit

/-- Helper for Chap10 Lemma 10 153 12: if two `R`-valued points have the same composite to `S`,
then they induce the same map on the common residue field of their pulled-back prime. -/
lemma residueFieldMap_eq_of_localHom_comp_eq
    {A : Type w} [CommRing A] [Algebra R A] (f g : A →ₐ[R] R) :
    letI : Algebra R S := φ.toAlgebra
    (Algebra.ofId R S).comp f = (Algebra.ofId R S).comp g →
    ∀ hq : Ideal.comap (f : A →+* R) (maximalIdeal R) =
      Ideal.comap (g : A →+* R) (maximalIdeal R),
    Ideal.ResidueField.map (Ideal.comap (f : A →+* R) (maximalIdeal R)) (maximalIdeal R)
        (g : A →+* R) hq =
      Ideal.ResidueField.map (Ideal.comap (f : A →+* R) (maximalIdeal R)) (maximalIdeal R)
        (f : A →+* R) rfl := by
  letI : Algebra R S := φ.toAlgebra
  intro hfg hq
  -- Proof comment: compare after the injective residue-field map induced by the local homomorphism.
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro a
  apply RingHom.injective (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) φ
    (IsLocalRing.maximalIdeal_comap φ).symm)
  have happ : φ (f a) = φ (g a) := by
    simpa using AlgHom.congr_fun hfg a
  simp [Ideal.ResidueField.map_algebraMap, happ]

/-- Helper for Chap10 Lemma 10 153 12: the residue-field map induced by an `S`-valued point is
the composite of the local residue map with the inverse of the strict-henselian residue
equivalence at the pulled-back prime. -/
lemma residueFieldMap_eq_localHom_comp_inverse
    {A : Type w} [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    letI : Algebra R S := φ.toAlgebra
    ∀ (g : A →ₐ[R] S) (q : Ideal A) [q.IsPrime],
    (hqR : q.under R = maximalIdeal R) →
    (hqS : q = Ideal.comap (g : A →+* S) (maximalIdeal S)) →
    let e : (maximalIdeal R).ResidueField ≃+* q.ResidueField :=
      RingEquiv.ofBijective _
        (bijective_residueFieldMap_of_strictHenselian_etale_prime (R := R) q hqR)
    Ideal.ResidueField.map q (maximalIdeal S) (g : A →+* S) hqS =
      (Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) φ
        (IsLocalRing.maximalIdeal_comap φ).symm).comp e.symm.toRingHom := by
  letI : Algebra R S := φ.toAlgebra
  intro g q _ hqR hqS
  let e : (maximalIdeal R).ResidueField ≃+* q.ResidueField :=
    RingEquiv.ofBijective _
      (bijective_residueFieldMap_of_strictHenselian_etale_prime (R := R) q hqR)
  -- Proof comment: both maps agree after precomposition with the bijective map from the base
  -- residue field, so extensionality reduces the claim to `map_algebraMap`.
  have hcomp :
      (Ideal.ResidueField.map q (maximalIdeal S) (g : A →+* S) hqS).comp e.toRingHom =
        Ideal.ResidueField.map (maximalIdeal R) (maximalIdeal S) φ
          (IsLocalRing.maximalIdeal_comap φ).symm := by
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro a
    have hφa : (algebraMap R S) a = φ a := rfl
    simpa [e, Ideal.ResidueField.map_algebraMap] using
      congrArg (algebraMap S (maximalIdeal S).ResidueField) hφa
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy :
      (RingEquiv.ofBijective
          (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hqR.symm)
          (bijective_residueFieldMap_of_strictHenselian_etale_prime (R := R) q hqR)).symm
        ((Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hqR.symm) y) = y :=
    e.symm_apply_apply y
  have hy' :
      (RingEquiv.ofBijective
          (Ideal.ResidueField.map (maximalIdeal R) q (algebraMap R A) hqR.symm)
          (bijective_residueFieldMap_of_strictHenselian_etale_prime (R := R) q hqR)).symm
        (e y) = y := by
    simpa [e] using hy
  simpa [hy'] using RingHom.congr_fun hcomp y

/-- Helper for Chap10 Lemma 10 153 12: the inverse residue-field equivalence over a prime lying
above the maximal ideal is compatible with the base residue-field map. -/
lemma residueFieldInverse_comp_baseResidueFieldMap
    {A : Type w} [CommRing A] [Algebra R A] [Algebra.Etale R A]
    (q : Ideal A) [q.IsPrime] (hq : q.under R = maximalIdeal R) :
    ∀ hqTarget : q.under R = (maximalIdeal R).under R,
      let e : (maximalIdeal R).ResidueField ≃+* q.ResidueField :=
        RingEquiv.ofBijective _
          (bijective_residueFieldMap_of_strictHenselian_etale_prime (R := R) q hq)
      e.symm.toRingHom.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal R) (algebraMap R R)
          hqTarget := by
  intro hqTarget
  -- Proof comment: after identifying the lower prime with the maximal ideal, the assertion is
  -- exactly that a ring equivalence followed by its inverse is the identity.
  let e : (maximalIdeal R).ResidueField ≃+* q.ResidueField :=
    RingEquiv.ofBijective _
      (bijective_residueFieldMap_of_strictHenselian_etale_prime (R := R) q hq)
  apply Ideal.ResidueField.ringHom_ext
  apply RingHom.ext
  intro x
  simp only [RingHom.comp_apply]
  rw [Ideal.ResidueField.map_algebraMap]
  rw [Ideal.ResidueField.map_algebraMap]
  have heval :
      (algebraMap A q.ResidueField) ((algebraMap R A) x) =
        e (algebraMap R (maximalIdeal R).ResidueField x) := by
    simp [e, Ideal.ResidueField.map_algebraMap]
  rw [heval]
  exact e.symm_apply_apply (algebraMap R (maximalIdeal R).ResidueField x)

omit [StrictHenselianLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 12: a common zero of the defining polynomials kills the
ideal generated by those polynomials under multivariable evaluation. -/
lemma zeroLocusIdeal_lift_condition
    {T : Type v} [CommRing T] [Algebra R T]
    (P : Fin n → MvPolynomial (Fin n) R) (t : Fin n → T)
    (hzero : ∀ i, MvPolynomial.eval t (MvPolynomial.map (algebraMap R T) (P i)) = 0) :
    ∀ a : MvPolynomial (Fin n) R,
      a ∈ Ideal.span (Set.range P) →
        (MvPolynomial.aeval t : MvPolynomial (Fin n) R →ₐ[R] T) a = 0 := by
  -- Proof comment: it is enough to check the generators `P i`, where the claim is exactly the
  -- zero-locus hypothesis after rewriting `aeval` as mapped evaluation.
  intro a ha
  have hle :
      Ideal.span (Set.range P) ≤
        RingHom.ker
          ((MvPolynomial.aeval t : MvPolynomial (Fin n) R →ₐ[R] T) :
            MvPolynomial (Fin n) R →+* T) := by
    refine Ideal.span_le.mpr ?_
    rintro p ⟨i, rfl⟩
    simpa [RingHom.mem_ker, MvPolynomial.aeval_def, MvPolynomial.eval_map] using hzero i
  exact hle ha

omit [StrictHenselianLocalRing R] in
/-- Helper for Chap10 Lemma 10 153 12: every algebra map out of the quotient by the defining
polynomials recovers a tuple satisfying those equations. -/
lemma quotientAlgHom_zeroLocus
    {T : Type v} [CommRing T] [Algebra R T]
    (P : Fin n → MvPolynomial (Fin n) R)
    (f : (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)) →ₐ[R] T) :
    ∀ i,
      MvPolynomial.eval
          (fun j ↦ f (Ideal.Quotient.mk (Ideal.span (Set.range P)) (MvPolynomial.X j)))
          (MvPolynomial.map (algebraMap R T) (P i)) = 0 := by
  intro i
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range P)
  let t : Fin n → T := fun j ↦ f (Ideal.Quotient.mk I (MvPolynomial.X j))
  -- Proof comment: the quotient map followed by `f` is the evaluator at the recovered tuple.
  have hcomp :
      f.comp (Ideal.Quotient.mkₐ R I) =
        (MvPolynomial.aeval t : MvPolynomial (Fin n) R →ₐ[R] T) := by
    apply MvPolynomial.algHom_ext
    intro j
    simp [t, I]
  have hzero : f (Ideal.Quotient.mk I (P i)) = 0 := by
    have hmem : P i ∈ I := Ideal.subset_span ⟨i, rfl⟩
    have hmk : Ideal.Quotient.mk I (P i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [hmk, map_zero]
  have hp : MvPolynomial.aeval t (P i) = 0 := by
    simpa [I] using
      (congrArg (fun F : MvPolynomial (Fin n) R →ₐ[R] T ↦ F (P i)) hcomp).symm.trans hzero
  simpa [t, I, MvPolynomial.aeval_def, MvPolynomial.eval_map] using hp

/-
Domain-style sampling:
* primary domain: points of étale algebras over strictly henselian local rings;
* sampled owner declarations of the same kind:
  `StrictHenselianLocalRing`,
  `henselian_local_ring_tfae`,
  `etale_retraction_unique_property`,
  `Algebra.Etale.iff_exists_algEquiv_prod`;
* best owner abstraction:
  for `A := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)`, the core owner is the étale
  `R`-algebra `A`; the two polynomial zero loci are only the source-facing presentations of the
  `R`- and `S`-points of that owner algebra;
* primitive data vs. derived API:
  the primitive data are the equations `P i` and the owner hypothesis `[Algebra.Etale R A]`;
  the solution sets are derived from algebra maps out of `A` by the quotient universal property of
  `MvPolynomial.aeval`, not additional primitive structure.

Source/core/bridge triage:
* `source-facing`: the coordinate zero-locus bijection theorem below;
* `core/canonical`: `StrictHenselianLocalRing`, the henselian clause
  `etale_retraction_unique_property`, and the field-level classification
  `Algebra.Etale.iff_exists_algEquiv_prod`;
* `bridge/view`: identifying a common zero of `P` with an `R`-algebra map from the presented
  quotient, and similarly after applying `φ` to coefficients.
-/

-- Proof sketch: for an étale `R`-algebra `A`, the map on point sets `A(R) → A(S)` induced by the
-- local homomorphism `φ : R →+* S` is bijective over strictly henselian local rings. One proves
-- this by applying Lemma `10.153.3`, through the canonical owner clause
-- `etale_retraction_unique_property`, to pass from `A`-points over `R` and `S` to points over the
-- residue fields of `R` and `S`; then `Algebra.Etale.iff_exists_algEquiv_prod` identifies the
-- residue-field base change of `A` with a finite product of copies of the corresponding separably
-- closed residue field.
/-- Owner-level point statement for Lemma 10.153.12: if `φ : R →+* S` is a local homomorphism
between strictly henselian local rings and `A` is an étale `R`-algebra, then composition with `φ`
induces a bijection `A(R) ≃ A(S)`, formalized as a bijection on `R`-algebra maps
`A →ₐ[R] R` and `A →ₐ[R] S`. -/
theorem strictlyHenselian_localHom_bijective_pointMap_of_etale
    (A : Type w) [CommRing A] [Algebra R A] [Algebra.Etale R A] :
    letI : Algebra R S := φ.toAlgebra
    Function.Bijective (fun f : A →ₐ[R] R ↦ (Algebra.ofId R S).comp f) := by
  classical
  letI : Algebra R S := φ.toAlgebra
  constructor
  · intro f g hfg
    -- Proof comment: use the unique henselian lift over `R` for the prime cut out by `f`.
    let q : Ideal A := Ideal.comap (f : A →+* R) (maximalIdeal R)
    have hqUnder : q.under R = maximalIdeal R := by
      dsimp [q]
      rw [Ideal.under_def, Ideal.comap_comap]
      have hcomp : (f : A →+* R).comp (algebraMap R A) = RingHom.id R := by
        ext x
        exact f.commutes x
      rw [hcomp]
      rfl
    let τ : q.ResidueField →+* (maximalIdeal R).ResidueField :=
      Ideal.ResidueField.map q (maximalIdeal R) (f : A →+* R) rfl
    have hqTarget : q.under R = (maximalIdeal R).under R := by
      simpa [Ideal.under_def] using hqUnder
    have hτ :
        τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
          Ideal.ResidueField.map (q.under R) (maximalIdeal R) (algebraMap R R)
            hqTarget := by
      -- Proof comment: both sides are residue maps induced by the same `R`-algebra point.
      apply Ideal.ResidueField.ringHom_ext
      apply RingHom.ext
      intro x
      simp [τ, Ideal.ResidueField.map_algebraMap]
    obtain ⟨f₀, _hf₀, huniq⟩ :=
      existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
        (R := R) (A := A) (S := R) q hqTarget τ hτ
    have hf_prop :
        ∃ hfq : q = Ideal.comap (f : A →+* R) (maximalIdeal R),
          Ideal.ResidueField.map q (maximalIdeal R) (f : A →+* R) hfq = τ := by
      exact ⟨rfl, rfl⟩
    have hqfg :
        Ideal.comap (f : A →+* R) (maximalIdeal R) =
          Ideal.comap (g : A →+* R) (maximalIdeal R) :=
      algHom_comap_maximalIdeal_eq_of_localHom_comp_eq (φ := φ) f g hfg
    have hg_prop :
        ∃ hgq : q = Ideal.comap (g : A →+* R) (maximalIdeal R),
          Ideal.ResidueField.map q (maximalIdeal R) (g : A →+* R) hgq = τ := by
      exact ⟨hqfg, residueFieldMap_eq_of_localHom_comp_eq (φ := φ) f g hfg hqfg⟩
    have hf_eq : f = f₀ := huniq f hf_prop
    have hg_eq : g = f₀ := huniq g hg_prop
    exact hf_eq.trans hg_eq.symm
  · intro g
    -- Proof comment: invert the strict-henselian residue-field map over the prime cut out by `g`.
    let q : Ideal A := Ideal.comap (g : A →+* S) (maximalIdeal S)
    have hqUnder : q.under R = maximalIdeal R :=
      algHom_comap_maximalIdeal_under_of_localHom (φ := φ) g
    let e : (maximalIdeal R).ResidueField ≃+* q.ResidueField :=
      RingEquiv.ofBijective _
        (bijective_residueFieldMap_of_strictHenselian_etale_prime (R := R) q hqUnder)
    let τ : q.ResidueField →+* (maximalIdeal R).ResidueField := e.symm.toRingHom
    have hqTarget : q.under R = (maximalIdeal R).under R := by
      simpa [Ideal.under_def] using hqUnder
    have hτ :
        τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
          Ideal.ResidueField.map (q.under R) (maximalIdeal R) (algebraMap R R)
            hqTarget := by
      -- Proof comment: after rewriting the source prime to `maximalIdeal R`, this is
      -- `e.symm.comp e = id` on the maximal-ideal residue field.
      simpa [τ, e] using
        residueFieldInverse_comp_baseResidueFieldMap (R := R) (A := A) q hqUnder hqTarget
    obtain ⟨f, hf, _huniqR⟩ :=
      existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
        (R := R) (A := A) (S := R) q hqTarget τ hτ
    obtain ⟨hfq, hfτ⟩ := hf
    refine ⟨f, ?_⟩
    let fS : A →ₐ[R] S := (Algebra.ofId R S).comp f
    have hqComp : q = Ideal.comap (fS : A →+* S) (maximalIdeal S) := by
      exact hfq.trans (algHom_comap_maximalIdeal_comp_of_localHom (φ := φ) f).symm
    let τS : q.ResidueField →+* (maximalIdeal S).ResidueField :=
      Ideal.ResidueField.map q (maximalIdeal S) (g : A →+* S) rfl
    have hmaxSUnder : (maximalIdeal S).under R = maximalIdeal R := by
      simpa [Ideal.under_def] using (IsLocalRing.maximalIdeal_comap φ)
    have hqTargetS : q.under R = (maximalIdeal S).under R :=
      hqUnder.trans hmaxSUnder.symm
    have hτS :
        τS.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
          Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S)
            hqTargetS := by
      -- Proof comment: the compatibility condition for `g` is just functoriality on elements
      -- coming from `R`.
      apply Ideal.ResidueField.ringHom_ext
      apply RingHom.ext
      intro x
      have hφx : (algebraMap R S) x = φ x := rfl
      simp [τS, Ideal.ResidueField.map_algebraMap, hφx]
    obtain ⟨g₀, _hg₀, huniqS⟩ :=
      existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
        (R := R) (A := A) (S := S) q hqTargetS τS hτS
    have hg_prop :
        ∃ hgq : q = Ideal.comap (g : A →+* S) (maximalIdeal S),
          Ideal.ResidueField.map q (maximalIdeal S) (g : A →+* S) hgq = τS := by
      exact ⟨rfl, rfl⟩
    have hfS_res :
        Ideal.ResidueField.map q (maximalIdeal S) (fS : A →+* S) hqComp = τS := by
      have hF :=
        residueFieldMap_eq_localHom_comp_inverse (φ := φ) fS q hqUnder hqComp
      have hG :=
        residueFieldMap_eq_localHom_comp_inverse (φ := φ) g q hqUnder rfl
      exact hF.trans hG.symm
    have hfS_prop :
        ∃ hfSq : q = Ideal.comap (fS : A →+* S) (maximalIdeal S),
          Ideal.ResidueField.map q (maximalIdeal S) (fS : A →+* S) hfSq = τS := by
      exact ⟨hqComp, hfS_res⟩
    have hfS_eq : fS = g₀ := huniqS fS hfS_prop
    have hg_eq : g = g₀ := huniqS g hg_prop
    exact hfS_eq.trans hg_eq.symm

-- The coordinate zero-locus statement is the source-facing bridge obtained by identifying common
-- zeros of `P` with `R`- and `S`-points of the étale quotient
-- `R[x_1, ..., x_n] / (P_1, ..., P_n)` via `MvPolynomial.aeval` and `Ideal.Quotient.liftₐ`.
/-- Chap10 Lemma 10 153 12: for a local homomorphism `φ : R →+* S` between strictly
henselian local rings, if `R[x_1, ..., x_n] / (P_1, ..., P_n)` is étale over `R`, then
applying `φ` coordinatewise gives a bijection between the common zero locus of the `P_i` in
`R^n` and the common zero locus of the coefficientwise images `P_i^φ` in `S^n`. -/
@[stacks 04GX]
theorem strictlyHenselian_localHom_bijOn_zeroLocus_of_etale_mvPolynomial_quotient
    (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale R (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P))] :
    Set.BijOn
      (fun r ↦ φ ∘ r)
      {r : Fin n → R | ∀ i, MvPolynomial.eval r (P i) = 0}
      {s : Fin n → S | ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (P i)) = 0} := by
  classical
  letI : Algebra R S := φ.toAlgebra
  let A := MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range P)
  let I : Ideal (MvPolynomial (Fin n) R) := Ideal.span (Set.range P)
  have hpoint :=
    strictlyHenselian_localHom_bijective_pointMap_of_etale
      (φ := φ) (A := A)
  rcases hpoint with ⟨hpoint_inj, hpoint_surj⟩
  refine ⟨?mapsTo, ?injOn, ?surjOn⟩
  · intro r hr i
    -- Proof comment: evaluation commutes with applying the coefficient map `φ`.
    have hφ : φ (MvPolynomial.eval r (P i)) = 0 := by
      rw [hr i, map_zero]
    simpa [Function.comp_def, MvPolynomial.eval_map] using
      (MvPolynomial.eval₂_comp φ r (P i)).symm.trans hφ
  · intro r hr r' hr' hrr'
    -- Proof comment: turn the two zero tuples into quotient points and use owner injectivity.
    have hzeroR :
        ∀ i, MvPolynomial.eval r (MvPolynomial.map (algebraMap R R) (P i)) = 0 := by
      intro i
      simpa using hr i
    have hzeroR' :
        ∀ i, MvPolynomial.eval r' (MvPolynomial.map (algebraMap R R) (P i)) = 0 := by
      intro i
      simpa using hr' i
    let fr : A →ₐ[R] R :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval r)
        (zeroLocusIdeal_lift_condition (P := P) r hzeroR)
    let fr' : A →ₐ[R] R :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval r')
        (zeroLocusIdeal_lift_condition (P := P) r' hzeroR')
    have hfr :
        (Algebra.ofId R S).comp fr = (Algebra.ofId R S).comp fr' := by
      apply Ideal.Quotient.algHom_ext
      apply MvPolynomial.algHom_ext
      intro i
      simpa [fr, fr', I, A, Function.comp_def] using congrFun hrr' i
    have hfr_eq : fr = fr' := hpoint_inj hfr
    funext i
    have happ := AlgHom.congr_fun hfr_eq (Ideal.Quotient.mk I (MvPolynomial.X i))
    simpa [fr, fr', I, A] using happ
  · intro s hs
    -- Proof comment: an `S`-zero gives an `S`-point of the quotient; pull it back to an
    -- `R`-point and then read off its coordinate values.
    have hzeroS :
        ∀ i, MvPolynomial.eval s (MvPolynomial.map (algebraMap R S) (P i)) = 0 := by
      intro i
      simpa using hs i
    let fs : A →ₐ[R] S :=
      Ideal.Quotient.liftₐ I (MvPolynomial.aeval s)
        (zeroLocusIdeal_lift_condition (P := P) s hzeroS)
    obtain ⟨fr, hfr⟩ := hpoint_surj fs
    let r : Fin n → R := fun i ↦ fr (Ideal.Quotient.mk I (MvPolynomial.X i))
    have hr : ∀ i, MvPolynomial.eval r (P i) = 0 := by
      intro i
      have hzero := quotientAlgHom_zeroLocus (P := P) fr i
      simpa [r, I, A] using hzero
    refine ⟨r, hr, ?_⟩
    funext i
    have happ := AlgHom.congr_fun hfr (Ideal.Quotient.mk I (MvPolynomial.X i))
    simpa [r, fs, I, A, Function.comp_def] using happ

end
