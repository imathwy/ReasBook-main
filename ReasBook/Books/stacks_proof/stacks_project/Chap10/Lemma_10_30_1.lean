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

/-- Helper for Chap10 Lemma 10 30 1: a nonzero element of an away-localization has a nonzero
chosen numerator in `IsLocalization.Away.sec`. -/
lemma away_sec_fst_ne_zero {A : Type u} [CommSemiring A] (a : A)
    {u : Localization.Away a} (hu : u ≠ 0) :
    (IsLocalization.Away.sec a u).1 ≠ 0 := by
  -- Reduce the away-specific numerator to the general localization numerator.
  simpa [IsLocalization.Away.sec] using
    (IsLocalization.sec_fst_ne_zero (M := Submonoid.powers a) (S := Localization.Away a) hu)

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Helper for Chap10 Lemma 10 30 1: the map between away-localizations induced by a ring map
sends base-ring elements to their mapped base-ring elements. -/
lemma awayMap_algebraMap_apply {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (a x : A) :
    Localization.awayMap φ a ((algebraMap A (Localization.Away a)) x) =
      algebraMap B (Localization.Away (φ a)) (φ x) := by
  -- Reduce the away-map abbreviation to the standard localization-map computation.
  change (IsLocalization.map (Localization.Away (φ a)) φ
      (show Submonoid.powers a ≤ (Submonoid.powers (φ a)).comap φ by
        rintro y ⟨n, rfl⟩
        exact ⟨n, by simp⟩)) ((algebraMap A (Localization.Away a)) x) = _
  rw [IsLocalization.map_eq]

/-- Helper for Chap10 Lemma 10 30 1: localizing after an away map at an element `u`
is the same as localizing the target ring away from the mapped base denominator times the mapped
chosen numerator of `u`. -/
lemma away_of_awayMap_sec_fst {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A) (u : Localization.Away a) :
    IsLocalization.Away (φ a * φ (IsLocalization.Away.sec a u).1)
      (Localization.Away (Localization.awayMap φ a u)) := by
  -- Map the associatedness between `u` and its chosen numerator through the away map.
  have hassoc : Associated
      (algebraMap B (Localization.Away (φ a)) (φ (IsLocalization.Away.sec a u).1))
      (Localization.awayMap φ a u) := by
    have hmap := (IsLocalization.Away.associated_sec_fst a u).map
      (Localization.awayMap φ a)
    simpa only [awayMap_algebraMap_apply] using hmap
  -- The general `mul_of_associated` API then packages the iterated away-localization.
  exact IsLocalization.Away.mul_of_associated (φ a) (φ (IsLocalization.Away.sec a u).1)
    (Localization.awayMap φ a u) hassoc

/-- Helper for Chap10 Lemma 10 30 1: once the target away-localization is given its natural
`Localization.Away a`-algebra structure, `Localization.awayMap` agrees with the ambient algebra
map on localized elements. -/
lemma awayMap_apply_eq_algebraMap_apply {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A)
    (u : Localization.Away a) :
    letI : Algebra (Localization.Away a) (Localization.Away (φ a)) :=
      (Localization.awayMap φ a).toAlgebra
    Localization.awayMap φ a u =
      algebraMap (Localization.Away a) (Localization.Away (φ a)) u := by
  -- Under the canonical localization algebra, `algebraMap` is definitionally the away-map.
  rfl

/-- Helper for Chap10 Lemma 10 30 1: with the natural localization-algebra structure in place,
the iterated away-localization at the algebra-map image of `u` is also an away-localization at
the mapped product denominator. -/
lemma away_of_algebraMap_sec_fst {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A)
    (u : Localization.Away a) :
    letI : Algebra (Localization.Away a) (Localization.Away (φ a)) :=
      (Localization.awayMap φ a).toAlgebra
    IsLocalization.Away (φ a * φ (IsLocalization.Away.sec a u).1)
      (Localization.Away
        ((algebraMap (Localization.Away a) (Localization.Away (φ a))) u)) := by
  -- In the canonical localization algebra, the displayed denominator is literally the away-map
  -- denominator from the previous helper.
  simpa using away_of_awayMap_sec_fst φ a u

/-- Helper for Chap10 Lemma 10 30 1: the ambient localization at the product denominator is also
an away-localization for the denominator obtained by coercing from a subalgebra. -/
lemma isLocalizationAway_coe_awayProduct {T : Subalgebra R S} (f : R) (g : T) :
    IsLocalization.Away ((((algebraMap R T f) * g : T) : S))
      (Localization.Away ((algebraMap R S f) * (g : S))) := by
  -- The two denominator spellings are propositionally the same after unfolding the subalgebra
  -- coercion and the restricted algebra map.
  simpa using (inferInstance : IsLocalization.Away ((algebraMap R S f) * (g : S))
    (Localization.Away ((algebraMap R S f) * (g : S))))

/-- Helper for Chap10 Lemma 10 30 1: composing a finitely presented ring map with a target
away-localization is again finitely presented. -/
lemma finitePresentation_toLocalizationAway_comp {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (φ : A →+* B) (b : B) (hφ : φ.FinitePresentation) :
    ((algebraMap B (Localization.Away b)).comp φ).FinitePresentation := by
  -- The away-localization map is finitely presented, so finite presentation follows by
  -- stability under composition.
  have hloc : (algebraMap B (Localization.Away b)).FinitePresentation := by
    rw [RingHom.finitePresentation_algebraMap]
    exact IsLocalization.Away.finitePresentation b
  exact RingHom.FinitePresentation.comp hloc hφ

/-- Helper for Chap10 Lemma 10 30 1: an inclusion of subalgebras preserves nonzero elements. -/
lemma subalgebra_inclusion_ne_zero {A : Type u} {B : Type v} [CommSemiring A] [Semiring B]
    [Algebra A B] {T U : Subalgebra A B} (hTU : T ≤ U) {y : T} (hy : y ≠ 0) :
    Subalgebra.inclusion hTU y ≠ 0 := by
  -- Coercing both sides to the ambient algebra reduces the claim to the original nonzero fact.
  intro hzero
  apply hy
  ext
  simpa using congrArg Subtype.val hzero

/-- Helper for Chap10 Lemma 10 30 1: the product denominator used before and after passing to a
larger subalgebra has the expected canonical spelling. -/
lemma subalgebra_inclusion_oldDenominator_mul {T U : Subalgebra R S} (hTU : T ≤ U)
    (f : R) (g d : T) :
    letI : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
    algebraMap T U (((algebraMap R T f) * g) * d) =
      (algebraMap R U f) * (Subalgebra.inclusion hTU g * Subalgebra.inclusion hTU d) := by
  letI : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
  -- Push the comparison to the ambient algebra, where both sides are the same product.
  ext
  simp [RingHom.algebraMap_toAlgebra, mul_assoc]

/-- Helper for Chap10 Lemma 10 30 1: the away map induced by a subalgebra inclusion is injective. -/
lemma awayMap_injective_of_subalgebra_inclusion {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] {T U : Subalgebra A B} (hTU : T ≤ U) (d : T) :
    letI : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
    Function.Injective (Localization.awayMap (algebraMap T U) d) := by
  letI : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
  -- Injectivity after localization follows because the underlying subalgebra inclusion is
  -- already injective; the localization criterion is then solved with the zeroth power.
  rw [Localization.awayMap_injective_iff]
  intro a ha
  refine ⟨0, ?_⟩
  have ha0 : a = 0 := by
    apply Subalgebra.inclusion_injective hTU
    simpa [RingHom.algebraMap_toAlgebra] using ha
  simpa [ha0]

/-- Helper for Chap10 Lemma 10 30 1: the old finite set of generators lies in the subalgebra
generated by that set together with a new singleton. -/
lemma adjoin_le_adjoin_singleton_union {A : Type u} {B : Type v} [CommSemiring A] [Semiring B]
    [Algebra A B] (s : Set B) (x : B) :
    Algebra.adjoin A s ≤ Algebra.adjoin A ({x} ∪ s : Set B) := by
  -- Every old generator is one of the generators of the enlarged union.
  rw [Algebra.adjoin_le_iff]
  intro y hy
  exact Algebra.subset_adjoin (Set.mem_union_right {x} hy)

/-- Helper for Chap10 Lemma 10 30 1: the new singleton generator belongs to the enlarged
generated subalgebra. -/
lemma mem_adjoin_singleton_union_left {A : Type u} {B : Type v} [CommSemiring A] [Semiring B]
    [Algebra A B] (s : Set B) (x : B) :
    x ∈ Algebra.adjoin A ({x} ∪ s : Set B) := by
  -- The left summand of the union supplies the new generator.
  exact Algebra.subset_adjoin (Set.mem_union_left s rfl)

/-- Helper for Chap10 Lemma 10 30 1: in the enlarged generated subalgebra,
the new element generates over the old generated subalgebra. -/
lemma adjoin_singleton_eq_top_of_insertSubalgebra (s : Set S) (x : S) :
    let T : Subalgebra R S := Algebra.adjoin R s
    let U : Subalgebra R S := Algebra.adjoin R ({x} ∪ s : Set S)
    let hTU : T ≤ U := adjoin_le_adjoin_singleton_union (A := R) s x
    @Algebra.adjoin T U _ _ (Subalgebra.inclusion hTU).toAlgebra
      ({(⟨x, mem_adjoin_singleton_union_left (A := R) s x⟩ : U)} : Set U) = ⊤ := by
  intro T U hTU
  letI : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
  let xU : U := ⟨x, mem_adjoin_singleton_union_left (A := R) s x⟩
  let K := @Algebra.adjoin T U _ _ (Subalgebra.inclusion hTU).toAlgebra ({xU} : Set U)
  apply eq_top_iff.mpr
  intro y hy
  change y ∈ K
  -- Induct over the ambient `R`-generators of `U`; the old generators come from `T`, while
  -- the new generator is exactly the singleton used to define `K`.
  exact Algebra.adjoin_induction (s := ({x} ∪ s : Set S))
    (p := fun z hz => (⟨z, hz⟩ : U) ∈ K)
    (fun z hz => by
      rcases hz with hz | hz
      · subst hz
        change xU ∈ K
        exact Algebra.self_mem_adjoin_singleton T xU
      · have hzT : z ∈ T := Algebra.subset_adjoin hz
        have hzK : algebraMap T U ⟨z, hzT⟩ ∈ K :=
          Subalgebra.algebraMap_mem K ⟨z, hzT⟩
        simpa [RingHom.algebraMap_toAlgebra] using hzK)
    (fun r => by
      have hrK : algebraMap T U (algebraMap R T r) ∈ K :=
        Subalgebra.algebraMap_mem K (algebraMap R T r)
      simpa [RingHom.algebraMap_toAlgebra] using hrK)
    (fun z w hz hw hzK hwK => by
      simpa using K.add_mem hzK hwK)
    (fun z w hz hw hzK hwK => by
      simpa using K.mul_mem hzK hwK)
    y.property

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

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
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

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Lemma 10.30.1: after splitting off the final generator of a finite set, the same
top-generation statement can be rewritten as a singleton adjoin over the previously generated
subalgebra. -/
lemma adjoin_singleton_eq_top_over_adjoin_finset_of_insert_eq_top
    (s : Finset S) (x : S)
    (h : Algebra.adjoin R ({x} ∪ (↑s : Set S)) = ⊤) :
    Algebra.adjoin (Algebra.adjoin R (↑s : Set S)) ({x} : Set S) = ⊤ := by
  -- Route correction: the insert step needs this exact reassociation lemma before the singleton
  -- branch can be applied over the previously generated subalgebra.
  -- Restrict scalars back to `R`, where mathlib's adjoin-union theorem identifies this tower
  -- adjoin with adjoining the union of the old finite set and the new singleton.
  apply Subalgebra.restrictScalars_injective R
  rw [Subalgebra.restrictScalars_top]
  rw [← Algebra.adjoin_union_eq_adjoin_adjoin]
  simpa [Set.union_comm] using h

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: if one element generates an algebra, then the corresponding
polynomial evaluation map is surjective. -/
lemma aeval_surjective_of_adjoin_singleton_eq_top
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) :
    Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] B) := by
  -- The range of `aeval x` is exactly the subalgebra generated by `x`, so top-generation gives
  -- surjectivity by the standard range-top criterion for algebra homomorphisms.
  exact
    (AlgHom.range_eq_top _).mp
      ((Algebra.adjoin_singleton_eq_range_aeval A x).symm.trans hgen)

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: singleton generation is preserved after localizing the
base and target away from a base element. -/
lemma localized_adjoin_singleton_eq_top
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (d : A) (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) :
    letI : Algebra (Localization.Away d) (Localization.Away (algebraMap A B d)) :=
      (Localization.awayMap (algebraMap A B) d).toAlgebra
    Algebra.adjoin (Localization.Away d)
      ({algebraMap B (Localization.Away (algebraMap A B d)) x} :
        Set (Localization.Away (algebraMap A B d))) = ⊤ := by
  letI : Algebra (Localization.Away d) (Localization.Away (algebraMap A B d)) :=
    (Localization.awayMap (algebraMap A B) d).toAlgebra
  let K : Subalgebra (Localization.Away d) (Localization.Away (algebraMap A B d)) :=
    Algebra.adjoin (Localization.Away d)
      ({algebraMap B (Localization.Away (algebraMap A B d)) x} :
        Set (Localization.Away (algebraMap A B d)))
  apply eq_top_iff.mpr
  intro y hy
  change y ∈ K
  -- Write the localized target element as a numerator from `B` times an inverse of a power of
  -- the localized denominator.
  obtain ⟨b, m, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (algebraMap A B d)) y
  rcases m with ⟨mval, hmval⟩
  rcases hmval with ⟨n, rfl⟩
  have hbK : algebraMap B (Localization.Away (algebraMap A B d)) b ∈ K := by
    have hb : b ∈ Algebra.adjoin A ({x} : Set B) := by
      simpa [hgen] using (show b ∈ (⊤ : Subalgebra A B) from trivial)
    -- The numerator belongs to the localized generated algebra because `B` was generated by `x`
    -- before localization.
    exact Algebra.adjoin_induction (s := ({x} : Set B))
      (p := fun z hz => algebraMap B (Localization.Away (algebraMap A B d)) z ∈ K)
      (fun z hz => by
        exact Algebra.subset_adjoin (by
          rw [Set.mem_singleton_iff] at hz ⊢
          rw [hz]))
      (fun a => by
        have hscalar : algebraMap (Localization.Away d)
            (Localization.Away (algebraMap A B d))
            (algebraMap A (Localization.Away d) a) ∈ K :=
          Subalgebra.algebraMap_mem K (algebraMap A (Localization.Away d) a)
        simpa only [RingHom.algebraMap_toAlgebra, awayMap_algebraMap_apply] using hscalar)
      (fun z w hz hw hzK hwK => by
        simpa using K.add_mem hzK hwK)
      (fun z w hz hw hzK hwK => by
        simpa using K.mul_mem hzK hwK)
      hb
  have hdenK : IsLocalization.mk' (Localization.Away (algebraMap A B d)) (1 : B)
        (⟨(algebraMap A B d) ^ n, n, rfl⟩ : Submonoid.powers (algebraMap A B d)) ∈ K := by
    let md : Submonoid.powers d := ⟨d ^ n, n, rfl⟩
    have hscalar : algebraMap (Localization.Away d)
        (Localization.Away (algebraMap A B d))
        (IsLocalization.mk' (Localization.Away d) (1 : A) md) ∈ K :=
      Subalgebra.algebraMap_mem K (IsLocalization.mk' (Localization.Away d) (1 : A) md)
    -- The inverse denominator is the image of the corresponding denominator inverse from the
    -- localized base.
    simpa only [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_mk', map_one, md, Subtype.coe_mk, map_pow] using hscalar
  have hmulK : algebraMap B (Localization.Away (algebraMap A B d)) b *
        IsLocalization.mk' (Localization.Away (algebraMap A B d)) (1 : B)
          (⟨(algebraMap A B d) ^ n, n, rfl⟩ : Submonoid.powers (algebraMap A B d)) ∈ K :=
    K.mul_mem hbK hdenK
  -- Reassemble the localized fraction from its numerator and denominator inverse.
  rw [IsLocalization.mk'_eq_mul_mk'_one]
  exact hmulK

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: if every polynomial relation is divisible by a fixed
relation, then the evaluation kernel is the principal ideal generated by that relation. -/
lemma ker_eq_span_of_dvd_relations
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) {q : Polynomial A}
    (hqx : Polynomial.aeval (R := A) x q = 0)
    (hdiv : ∀ p, Polynomial.aeval (R := A) x p = 0 → q ∣ p) :
    RingHom.ker (Polynomial.aeval (R := A) x).toRingHom =
      Ideal.span ({q} : Set (Polynomial A)) := by
  ext p
  constructor
  · intro hp
    -- Membership in the kernel is precisely being a relation, hence divisibility by `q`.
    rw [RingHom.mem_ker] at hp
    exact Ideal.mem_span_singleton.mpr (hdiv p hp)
  · intro hp
    -- Conversely, a multiple of a vanishing relation also vanishes under evaluation.
    rw [RingHom.mem_ker]
    rcases Ideal.mem_span_singleton.mp hp with ⟨r, rfl⟩
    simp [hqx]

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: a monic polynomial relation of minimal `natDegree`
generates the one-variable evaluation kernel. -/
lemma ker_eq_span_of_monic_minimal_natDegree
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B] [Nontrivial B]
    (x : B) {q : Polynomial A}
    (hqmonic : q.Monic)
    (hqx : Polynomial.aeval (R := A) x q = 0)
    (hmin : ∀ p : Polynomial A, p ≠ 0 → Polynomial.aeval (R := A) x p = 0 →
      q.natDegree ≤ p.natDegree) :
    RingHom.ker (Polynomial.aeval (R := A) x).toRingHom =
      Ideal.span ({q} : Set (Polynomial A)) := by
  -- Divide an arbitrary relation by the monic minimal relation; a nonzero remainder would be a
  -- smaller relation, contradicting the chosen minimality.
  apply ker_eq_span_of_dvd_relations x hqx
  intro p hp
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hqmonic]
  by_contra hrem
  have hremRoot : Polynomial.aeval (R := A) x (p %ₘ q) = 0 := by
    simpa [hp] using
      Polynomial.aeval_modByMonic_eq_self_of_root (p := p) (q := q) (x := x) hqx
  have hdegMin : q.natDegree ≤ (p %ₘ q).natDegree :=
    hmin (p %ₘ q) hrem hremRoot
  have hq_ne_one : q ≠ 1 := by
    intro hq1
    have hone : (1 : B) = 0 := by
      simpa [hq1] using hqx
    exact one_ne_zero hone
  have hdegLt : (p %ₘ q).natDegree < q.natDegree :=
    Polynomial.natDegree_modByMonic_lt p hqmonic hq_ne_one
  exact not_lt_of_ge hdegMin hdegLt

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: a surjective one-variable presentation with finitely
generated kernel gives a finitely presented structure map. -/
lemma finitePresentation_of_surjective_aeval_ker_fg
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B)
    (hsurj : Function.Surjective (Polynomial.aeval (R := A) x : Polynomial A →ₐ[A] B))
    (hker : (RingHom.ker (Polynomial.aeval (R := A) x).toRingHom).FG) :
    (algebraMap A B).FinitePresentation := by
  -- Convert the algebra presentation supplied by `aeval` into the ring-hom formulation.
  rw [RingHom.finitePresentation_algebraMap]
  exact Algebra.FinitePresentation.of_surjective (R := A) (A := Polynomial A) (B := B)
    (f := Polynomial.aeval (R := A) x) hsurj hker

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the bottom/principal kernel normal form is enough to prove
finite presentation for a one-variable generated algebra. -/
lemma finitePresentation_of_surjective_aeval_ker_eq_bot_or_span_singleton
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B)
    (hsurj : Function.Surjective (Polynomial.aeval (R := A) x : Polynomial A →ₐ[A] B))
    (hker :
      RingHom.ker (Polynomial.aeval (R := A) x).toRingHom = ⊥ ∨
        ∃ q : Polynomial A,
          RingHom.ker (Polynomial.aeval (R := A) x).toRingHom =
            Ideal.span ({q} : Set (Polynomial A))) :
    (algebraMap A B).FinitePresentation := by
  -- In either normal-form branch, the kernel is finitely generated.
  apply finitePresentation_of_surjective_aeval_ker_fg x hsurj
  rcases hker with hbot | ⟨q, hq⟩
  · rw [hbot]
    exact Submodule.fg_bot
  · rw [hq]
    exact Submodule.fg_span_singleton q

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: localized singleton generation makes the localized
evaluation map surjective. -/
lemma localizedAevalSurjective_of_localizedAdjoinSingletonTop
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) :
    letI : Algebra (Localization.Away a) (Localization.Away (algebraMap A B a)) :=
      (Localization.awayMap (algebraMap A B) a).toAlgebra
    Function.Surjective (Polynomial.aeval (R := Localization.Away a)
      (algebraMap B (Localization.Away (algebraMap A B a)) x) :
        Polynomial (Localization.Away a) →ₐ[Localization.Away a]
          Localization.Away (algebraMap A B a)) := by
  letI : Algebra (Localization.Away a) (Localization.Away (algebraMap A B a)) :=
    (Localization.awayMap (algebraMap A B) a).toAlgebra
  have hgenLoc := localized_adjoin_singleton_eq_top (A := A) (B := B) a x hgen
  -- Localized singleton generation identifies the target as the range of localized evaluation.
  exact aeval_surjective_of_adjoin_singleton_eq_top
    (A := Localization.Away a) (B := Localization.Away (algebraMap A B a))
    (algebraMap B (Localization.Away (algebraMap A B a)) x) hgenLoc

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: a localized bottom/principal kernel normal form proves
finite presentation of the corresponding away map for a one-generator algebra. -/
lemma awayMap_finitePresentation_of_localized_kernel_normal_form
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (a : A) (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hker :
      letI : Algebra (Localization.Away a) (Localization.Away (algebraMap A B a)) :=
        (Localization.awayMap (algebraMap A B) a).toAlgebra
      RingHom.ker (Polynomial.aeval (R := Localization.Away a)
        (algebraMap B (Localization.Away (algebraMap A B a)) x)).toRingHom = ⊥ ∨
        ∃ q : Polynomial (Localization.Away a),
          RingHom.ker (Polynomial.aeval (R := Localization.Away a)
            (algebraMap B (Localization.Away (algebraMap A B a)) x)).toRingHom =
              Ideal.span ({q} : Set (Polynomial (Localization.Away a)))) :
    ((Localization.awayMap (algebraMap A B) a) :
      Localization.Away a →+* Localization.Away (algebraMap A B a)).FinitePresentation := by
  letI : Algebra (Localization.Away a) (Localization.Away (algebraMap A B a)) :=
    (Localization.awayMap (algebraMap A B) a).toAlgebra
  have hsurj :
      Function.Surjective (Polynomial.aeval (R := Localization.Away a)
        (algebraMap B (Localization.Away (algebraMap A B a)) x) :
          Polynomial (Localization.Away a) →ₐ[Localization.Away a]
            Localization.Away (algebraMap A B a)) := by
    -- Use the dedicated localized-surjectivity package instead of re-elaborating it inline.
    exact localizedAevalSurjective_of_localizedAdjoinSingletonTop
      (A := A) (B := B) a x hgen
  -- Apply the kernel normal-form package to the localized `aeval` presentation.
  exact finitePresentation_of_surjective_aeval_ker_eq_bot_or_span_singleton
    (algebraMap B (Localization.Away (algebraMap A B a)) x) hsurj hker

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: a nontrivial one-variable evaluation kernel contains a
minimal-degree nonzero relation. -/
private lemma exists_minimalNatDegreeAevalRelation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B)
    (hker :
      RingHom.ker (Polynomial.aeval (R := A) x).toRingHom ≠ ⊥) :
    ∃ q : Polynomial A, q ≠ 0 ∧ Polynomial.aeval (R := A) x q = 0 ∧
      ∀ p : Polynomial A, p ≠ 0 → Polynomial.aeval (R := A) x p = 0 →
        q.natDegree ≤ p.natDegree := by
  classical
  let I := RingHom.ker (Polynomial.aeval (R := A) x).toRingHom
  rcases (Submodule.ne_bot_iff I).mp hker with ⟨q0, hq0I, hq0ne⟩
  have hq0root : Polynomial.aeval (R := A) x q0 = 0 := by
    rw [RingHom.mem_ker] at hq0I
    exact hq0I
  let P : ℕ → Prop := fun n =>
    ∃ q : Polynomial A, q ≠ 0 ∧ Polynomial.aeval (R := A) x q = 0 ∧ q.natDegree = n
  have hex : ∃ n, P n := ⟨q0.natDegree, q0, hq0ne, hq0root, rfl⟩
  obtain ⟨q, hqne, hqroot, hqdeg⟩ := Nat.find_spec hex
  refine ⟨q, hqne, hqroot, ?_⟩
  intro p hpne hproot
  have hpWitness : P p.natDegree := ⟨p, hpne, hproot, rfl⟩
  calc
    q.natDegree = Nat.find hex := hqdeg
    _ ≤ p.natDegree := Nat.find_min' hex hpWitness

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: any nonzero localized polynomial relation can be cleared
back to a nonzero relation over the original domain without increasing `natDegree`. -/
private lemma clearDenominator_of_localizedAevalRelation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B))
    {u : A} (hu : u ≠ 0) (x : B)
    {p : Polynomial (Localization.Away u)} (hp : p ≠ 0)
    (hroot :
      letI : Algebra (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
        (Localization.awayMap (algebraMap A B) u).toAlgebra
      Polynomial.aeval (R := Localization.Away u)
        (algebraMap B (Localization.Away (algebraMap A B u)) x) p = 0) :
    ∃ q : Polynomial A, q ≠ 0 ∧ Polynomial.aeval (R := A) x q = 0 ∧
      q.natDegree ≤ p.natDegree := by
  letI : IsDomain (Localization.Away u) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away u) (powers_le_nonZeroDivisors_of_noZeroDivisors hu)
  have hmapu : algebraMap A B u ≠ 0 := by
    intro hzero
    exact hu (hinj (by simpa using hzero))
  letI : IsDomain (Localization.Away (algebraMap A B u)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away (algebraMap A B u))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hmapu)
  letI : Algebra (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
    (Localization.awayMap (algebraMap A B) u).toAlgebra
  letI : IsScalarTower A B (Localization.Away (algebraMap A B u)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using
        (awayMap_algebraMap_apply (algebraMap A B) u x).symm
  have hBuInj : Function.Injective (algebraMap B (Localization.Away (algebraMap A B u))) :=
    IsLocalization.injective
      (Localization.Away (algebraMap A B u))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hmapu)
  let q : Polynomial A := IsLocalization.integerNormalization (Submonoid.powers u) p
  have hqLocRoot :
      Polynomial.aeval (R := A)
        (algebraMap B (Localization.Away (algebraMap A B u)) x) q = 0 := by
    -- Clearing coefficients in the localized polynomial preserves the vanishing relation.
    change Polynomial.aeval (R := A)
        (algebraMap B (Localization.Away (algebraMap A B u)) x)
        (IsLocalization.integerNormalization (Submonoid.powers u) p) = 0
    exact IsLocalization.integerNormalization_aeval_eq_zero
      (M := Submonoid.powers u) (R := A)
      (S := Localization.Away u)
      (R' := Localization.Away (algebraMap A B u)) p hroot
  have hqRoot : Polynomial.aeval (R := A) x q = 0 := by
    -- Injectivity of the target localization lets us descend the cleared relation to `B`.
    exact
      (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
        (R := A) (A := B) (B := Localization.Away (algebraMap A B u))
        (x := x) (p := q) hBuInj).mp hqLocRoot
  have hqne : q ≠ 0 := by
    -- Integer normalization of a nonzero localized polynomial stays nonzero over the domain.
    intro hqzero
    have hpzero : p = 0 := by
      exact (IsLocalization.integerNormalization_eq_zero_iff
        (M := Submonoid.powers u) (R := A) (S := Localization.Away u)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hu) p).mp (by simpa [q] using hqzero)
    exact hp hpzero
  have hqSupport : q.support ⊆ p.support := by
    simpa [q] using
      (IsLocalization.integerNormalization_support
        (M := Submonoid.powers u) (R := A) (S := Localization.Away u) p)
  have hqMem : q.natDegree ∈ p.support := by
    exact hqSupport (Polynomial.natDegree_mem_support_of_nonzero hqne)
  refine ⟨q, hqne, hqRoot, ?_⟩
  -- The support inclusion from integer normalization gives the desired `natDegree` control.
  exact Polynomial.le_natDegree_of_mem_supp _ hqMem

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: after inverting the leading coefficient of a minimal
nonzero relation, the localized one-variable evaluation kernel becomes principal. -/
private lemma localizedKernel_eq_span_singleton_of_minimalRelation
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B))
    (x : B) (q : Polynomial A)
    (hq : q ≠ 0)
    (hqx : Polynomial.aeval (R := A) x q = 0)
    (hmin : ∀ p : Polynomial A, p ≠ 0 → Polynomial.aeval (R := A) x p = 0 →
      q.natDegree ≤ p.natDegree) :
    let u := q.leadingCoeff
    letI : Algebra (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
      (Localization.awayMap (algebraMap A B) u).toAlgebra
    ∃ qLoc : Polynomial (Localization.Away u),
      RingHom.ker (Polynomial.aeval (R := Localization.Away u)
        (algebraMap B (Localization.Away (algebraMap A B u)) x)).toRingHom =
          Ideal.span ({qLoc} : Set (Polynomial (Localization.Away u))) := by
  let u : A := q.leadingCoeff
  have hu : u ≠ 0 := by
    -- A nonzero polynomial over a domain has nonzero leading coefficient.
    simpa [u] using Polynomial.leadingCoeff_ne_zero.mpr hq
  letI : IsDomain (Localization.Away u) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away u) (powers_le_nonZeroDivisors_of_noZeroDivisors hu)
  have hmapu : algebraMap A B u ≠ 0 := by
    intro hzero
    exact hu (hinj (by simpa using hzero))
  letI : IsDomain (Localization.Away (algebraMap A B u)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away (algebraMap A B u))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hmapu)
  letI : Algebra (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
    (Localization.awayMap (algebraMap A B) u).toAlgebra
  letI : IsScalarTower A B (Localization.Away (algebraMap A B u)) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower A (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      simpa [RingHom.algebraMap_toAlgebra] using
        (awayMap_algebraMap_apply (algebraMap A B) u x).symm
  let y : Localization.Away (algebraMap A B u) :=
    algebraMap B (Localization.Away (algebraMap A B u)) x
  have hBuInj : Function.Injective (algebraMap B (Localization.Away (algebraMap A B u))) :=
    IsLocalization.injective
      (Localization.Away (algebraMap A B u))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hmapu)
  let qLoc : Polynomial (Localization.Away u) :=
    Polynomial.C (IsLocalization.Away.invSelf u) *
      Polynomial.map (algebraMap A (Localization.Away u)) q
  have hAuInj : Function.Injective (algebraMap A (Localization.Away u)) :=
    IsLocalization.injective
      (Localization.Away u) (powers_le_nonZeroDivisors_of_noZeroDivisors hu)
  have hqLocMonic : qLoc.Monic := by
    -- Multiplying by the canonical inverse of the leading coefficient normalizes the relation.
    refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    calc
      IsLocalization.Away.invSelf u *
          (Polynomial.map (algebraMap A (Localization.Away u)) q).leadingCoeff
          = IsLocalization.Away.invSelf u * algebraMap A (Localization.Away u) q.leadingCoeff := by
              rw [Polynomial.leadingCoeff_map_of_injective hAuInj]
      _ = IsLocalization.Away.invSelf u * algebraMap A (Localization.Away u) u := by
              simp [u]
      _ = 1 := by
              simpa [mul_comm] using IsLocalization.Away.mul_invSelf (S := Localization.Away u) u
  have hqxLoc :
      Polynomial.aeval (R := A) y q = 0 := by
    -- The original minimal relation still vanishes after mapping to the localized target.
    exact
      (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
        (R := A) (A := B) (B := Localization.Away (algebraMap A B u))
        (x := x) (p := q) hBuInj).mpr hqx
  have hqLocRoot :
      Polynomial.aeval (R := Localization.Away u) y qLoc = 0 := by
    -- Evaluate the normalized localized relation by pulling the original root relation upstairs.
    change Polynomial.aeval (R := Localization.Away u) y
        (Polynomial.C (IsLocalization.Away.invSelf (S := Localization.Away u) u) *
          Polynomial.map (algebraMap A (Localization.Away u)) q) = 0
    rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_map_algebraMap]
    simp [hqxLoc]
  have hqLocDeg : qLoc.natDegree = q.natDegree := by
    have hinv : IsLocalization.Away.invSelf (S := Localization.Away u) u ≠ 0 := by
      intro hzero
      have hone : (1 : Localization.Away u) = 0 := by
        have hmul := IsLocalization.Away.mul_invSelf (S := Localization.Away u) u
        simpa [hzero] using hmul.symm
      exact one_ne_zero hone
    -- Scaling by a nonzero constant and mapping into the localization preserve `natDegree`.
    change (Polynomial.C (IsLocalization.Away.invSelf (S := Localization.Away u) u) *
        Polynomial.map (algebraMap A (Localization.Away u)) q).natDegree = q.natDegree
    rw [Polynomial.natDegree_C_mul hinv, Polynomial.natDegree_map_eq_of_injective hAuInj]
  have hminLoc :
      ∀ p : Polynomial (Localization.Away u), p ≠ 0 →
        Polynomial.aeval (R := Localization.Away u) y p = 0 →
          qLoc.natDegree ≤ p.natDegree := by
    intro p hp hproot
    rcases clearDenominator_of_localizedAevalRelation
        (A := A) (B := B) hinj hu x hp hproot with
      ⟨r, hrne, hrroot, hrdeg⟩
    -- Clear denominators on any localized relation and compare degrees with the chosen minimum.
    calc
      qLoc.natDegree = q.natDegree := hqLocDeg
      _ ≤ r.natDegree := hmin r hrne hrroot
      _ ≤ p.natDegree := hrdeg
  refine ⟨qLoc, ?_⟩
  -- The generic minimal-degree kernel computation closes the localized principal ideal claim.
  exact ker_eq_span_of_monic_minimal_natDegree y hqLocMonic hqLocRoot hminLoc

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: a one-generator domain algebra becomes finitely presented
after inverting one nonzero element of the base. -/
lemma exists_nonzero_awayMap_finitePresentation_of_adjoin_singleton_domain
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    [IsDomain A] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B))
    (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) :
    ∃ (u : A) (_ : u ≠ 0),
      ((Localization.awayMap (algebraMap A B) u) :
        Localization.Away u →+*
          Localization.Away (algebraMap A B u)).FinitePresentation := by
  have hker :
      RingHom.ker (Polynomial.aeval (R := A) x).toRingHom = ⊥ ∨
        RingHom.ker (Polynomial.aeval (R := A) x).toRingHom ≠ ⊥ := by
    exact em _
  rcases hker with hker | hker
  · refine ⟨1, one_ne_zero, ?_⟩
    have hkerLoc :
        letI : Algebra (Localization.Away (1 : A))
          (Localization.Away (algebraMap A B (1 : A))) :=
            (Localization.awayMap (algebraMap A B) (1 : A)).toAlgebra
        RingHom.ker (Polynomial.aeval (R := Localization.Away (1 : A))
          (algebraMap B (Localization.Away (algebraMap A B (1 : A))) x)).toRingHom = ⊥ ∨
          ∃ q : Polynomial (Localization.Away (1 : A)),
            RingHom.ker (Polynomial.aeval (R := Localization.Away (1 : A))
              (algebraMap B (Localization.Away (algebraMap A B (1 : A))) x)).toRingHom =
                Ideal.span ({q} : Set (Polynomial (Localization.Away (1 : A)))) := by
      letI : Algebra (Localization.Away (1 : A))
          (Localization.Away (algebraMap A B (1 : A))) :=
        (Localization.awayMap (algebraMap A B) (1 : A)).toAlgebra
      left
      rw [RingHom.ker_eq_bot_iff_eq_zero]
      intro p hp
      by_contra hpne
      rcases clearDenominator_of_localizedAevalRelation
          (A := A) (B := B) hinj (u := (1 : A)) one_ne_zero x hpne hp with
        ⟨q, hqne, hqroot, _⟩
      have hqmem : q ∈ RingHom.ker (Polynomial.aeval (R := A) x).toRingHom := by
        rw [RingHom.mem_ker]
        exact hqroot
      rw [hker] at hqmem
      exact hqne (by simpa using hqmem)
    -- In the injective-kernel branch, localization preserves the zero-kernel normal form.
    exact awayMap_finitePresentation_of_localized_kernel_normal_form
      (A := A) (B := B) 1 x hgen hkerLoc
  · rcases exists_minimalNatDegreeAevalRelation (A := A) (B := B) x hker with
      ⟨q, hqne, hqroot, hmin⟩
    let u : A := q.leadingCoeff
    have hu : u ≠ 0 := by
      -- The chosen minimal relation has nonzero leading coefficient.
      simpa [u] using Polynomial.leadingCoeff_ne_zero.mpr hqne
    refine ⟨u, hu, ?_⟩
    have hkerLoc :
        letI : Algebra (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
          (Localization.awayMap (algebraMap A B) u).toAlgebra
        RingHom.ker (Polynomial.aeval (R := Localization.Away u)
          (algebraMap B (Localization.Away (algebraMap A B u)) x)).toRingHom = ⊥ ∨
          ∃ q : Polynomial (Localization.Away u),
            RingHom.ker (Polynomial.aeval (R := Localization.Away u)
              (algebraMap B (Localization.Away (algebraMap A B u)) x)).toRingHom =
                Ideal.span ({q} : Set (Polynomial (Localization.Away u))) := by
      letI : Algebra (Localization.Away u) (Localization.Away (algebraMap A B u)) :=
        (Localization.awayMap (algebraMap A B) u).toAlgebra
      right
      rcases localizedKernel_eq_span_singleton_of_minimalRelation
          (A := A) (B := B) hinj x q hqne hqroot hmin with
        ⟨qLoc, hqLoc⟩
      exact ⟨qLoc, hqLoc⟩
    -- Localizing at the leading coefficient of the minimal relation gives the principal-kernel
    -- normal form consumed by the finite-presentation package.
    exact awayMap_finitePresentation_of_localized_kernel_normal_form
      (A := A) (B := B) u x hgen hkerLoc

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
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
  rcases h with ⟨f, hf, g, hg, hfp⟩
  have hgS : (g : S) ≠ 0 := by
    intro hzero
    apply hg
    ext
    exact hzero
  refine ⟨f, hf, (g : S), hgS, ?_⟩
  let e : T ≃ₐ[R] S := (Subalgebra.equivOfEq T ⊤ hT).trans Subalgebra.topEquiv
  let H : Submonoid.map e.toRingEquiv.toMonoidHom
      (Submonoid.powers ((algebraMap R T f) * g)) =
    Submonoid.powers ((algebraMap R S f) * (g : S)) := by
    -- The algebra equivalence sends the `T` denominator to the ambient `S` denominator.
    ext x
    simp [e]
  let eLoc : Localization.Away ((algebraMap R T f) * g) ≃+*
      Localization.Away ((algebraMap R S f) * (g : S)) :=
    IsLocalization.ringEquivOfRingEquiv _ _ e.toRingEquiv H
  have hcomp :
      eLoc.toRingHom.comp
          (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
            (Localization.awayMap (algebraMap R T) f)) :
              Localization.Away f →+* Localization.Away ((algebraMap R T f) * g)) =
        (((IsLocalization.Away.awayToAwayRight (algebraMap R S f) (g : S)).comp
          (Localization.awayMap (algebraMap R S) f)) :
            Localization.Away f →+* Localization.Away ((algebraMap R S f) * (g : S))) := by
    -- It remains to identify the transported composite on the source generators.
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    ext x
    simp only [RingHom.comp_apply]
    rw [awayMap_algebraMap_apply]
    rw [IsLocalization.Away.awayToAwayRight_eq]
    have heq := IsLocalization.ringEquivOfRingEquiv_eq
        (S := Localization.Away ((algebraMap R T f) * g))
        (Q := Localization.Away ((algebraMap R S f) * (g : S)))
        (j := e.toRingEquiv) H ((algebraMap R T) x)
    calc
      eLoc.toRingHom
          ((algebraMap T (Localization.Away ((algebraMap R T f) * g)))
            ((algebraMap R T) x))
          = (algebraMap S (Localization.Away ((algebraMap R S f) * (g : S))))
              (e.toRingEquiv ((algebraMap R T) x)) := by
              simpa [eLoc] using heq
      _ = (algebraMap S (Localization.Away ((algebraMap R S f) * (g : S))))
              ((algebraMap R S) x) := by
              simp [e]
      _ = (IsLocalization.Away.awayToAwayRight ((algebraMap R S) f) (g : S))
          ((Localization.awayMap (algebraMap R S) f)
            ((algebraMap R (Localization.Away f)) x)) := by
              rw [awayMap_algebraMap_apply]
              rw [IsLocalization.Away.awayToAwayRight_eq]
  have heLocfp : eLoc.toRingHom.FinitePresentation :=
    RingHom.FinitePresentation.of_bijective eLoc.bijective
  have hfpComp : (eLoc.toRingHom.comp
          (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
            (Localization.awayMap (algebraMap R T) f)) :
              Localization.Away f →+* Localization.Away ((algebraMap R T f) * g))).FinitePresentation :=
    RingHom.FinitePresentation.comp heLocfp hfp
  -- Rewrite the transported composite back to the canonical ambient away-product map.
  rw [hcomp] at hfpComp
  exact hfpComp

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: under the canonical away-localization algebra structure,
the image of an element of `T` in the localized target agrees with its ambient `U`-image. -/
private lemma iteratedAwayAlgebraMapComp_eq
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (a : T) (z : T) :
    letI : Algebra (Localization.Away a) (Localization.Away (algebraMap T U a)) :=
      (Localization.awayMap (algebraMap T U) a).toAlgebra
    algebraMap (Localization.Away a) (Localization.Away (algebraMap T U a))
        ((algebraMap T (Localization.Away a)) z) =
      algebraMap U (Localization.Away (algebraMap T U a)) ((algebraMap T U) z) := by
  letI : Algebra (Localization.Away a) (Localization.Away (algebraMap T U a)) :=
    (Localization.awayMap (algebraMap T U) a).toAlgebra
  -- Under the canonical localization algebra, the first localization map is literally the away
  -- map induced by the subalgebra inclusion.
  simpa [RingHom.algebraMap_toAlgebra] using
    (awayMap_algebraMap_apply (algebraMap T U) a z)

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the second away-map in the insert step sends base
generators to the corresponding generators in the iterated target localization. -/
private lemma stepMap_algebraMap_apply
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (a : T) (u : Localization.Away a)
    (r : R) :
    letI : Algebra (Localization.Away a) (Localization.Away (algebraMap T U a)) :=
      (Localization.awayMap (algebraMap T U) a).toAlgebra
    (Localization.awayMap
      (algebraMap (Localization.Away a) (Localization.Away (algebraMap T U a))) u)
        ((algebraMap (Localization.Away a) (Localization.Away u))
          ((algebraMap T (Localization.Away a)) ((algebraMap R T) r))) =
      algebraMap U
        (Localization.Away
          ((algebraMap (Localization.Away a) (Localization.Away (algebraMap T U a))) u))
        ((algebraMap R U) r) := by
  letI : Algebra (Localization.Away a) (Localization.Away (algebraMap T U a)) :=
    (Localization.awayMap (algebraMap T U) a).toAlgebra
  -- Route correction: normalize the composite on the `R`-generator before transporting it.
  -- First rewrite the second away-map on the displayed localized generator.
  rw [awayMap_algebraMap_apply]
  -- Then collapse the first localized algebra map to the ambient `U`-generator.
  rw [iteratedAwayAlgebraMapComp_eq (R := R) (S := S) (T := T) (U := U)
    (a := a) (z := (algebraMap R T) r)]
  -- Finally, the direct `U`-algebra map to the second localization is definitionally the
  -- composite through the first localized target.
  simp [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq]

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the canonical map `A_a → B_(φ(a)b)` obtained by first
localizing `A` away from `a` and then localizing the target away from `b`. -/
private noncomputable abbrev awayProductComparisonMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (φ : A →+* B) (a : A) (b : B) :
    Localization.Away a →+* Localization.Away (φ a * b) :=
  (IsLocalization.Away.awayToAwayRight (φ a) b).comp (Localization.awayMap φ a)

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: after localizing away from `a`, the further localization
away from `u : Localization.Away a` is the ambient algebra map. -/
private abbrev iteratedAwayMidMap {A : Type u} [CommRing A] (a : A)
    (u : Localization.Away a) :
    Localization.Away a →+* Localization.Away u :=
  algebraMap (Localization.Away a) (Localization.Away u)

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the second away-localization map in the iterated target
model is the canonical away map at `u`. -/
private noncomputable abbrev iteratedAwayStepMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] (u : A) :
    Localization.Away u →+* Localization.Away (algebraMap A B u) :=
  Localization.awayMap (algebraMap A B) u

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the source ring for the second localization in the insert
step, written using the canonical away-map image of `u`. -/
private abbrev iteratedAwayTarget
    {T U : Subalgebra R S} [Algebra T U] (a : T) (u : Localization.Away a) :=
  Localization.Away ((Localization.awayMap (algebraMap T U) a) u)

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the second localization map in the insert step, written
using the explicit away-map of the first away-map so theorem headers do not rely on localized
`Algebra` synthesis. -/
private noncomputable abbrev iteratedAwayInsertStepMap
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (f : R) (g : T) (u : Localization.Away ((algebraMap R T f) * g)) :
    Localization.Away u →+* iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u :=
  Localization.awayMap (Localization.awayMap (algebraMap T U) ((algebraMap R T f) * g)) u

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the identity localization equivalence used in the insert
step transports `U`-generators in the iterated model to the same `U`-generators in the final
away-localization. -/
private lemma iteratedAwayTarget_isLocalizationAway_finalDenominator
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (hTU : T ≤ U)
    (halg : algebraMap T U = Subalgebra.inclusion hTU)
    (f : R) (g d : T)
    (u : Localization.Away ((algebraMap R T f) * g))
    (g' : U)
    (hd : d = (IsLocalization.Away.sec ((algebraMap R T f) * g) u).1)
    (hg' : g' = Subalgebra.inclusion hTU g * Subalgebra.inclusion hTU d) :
    IsLocalization.Away ((algebraMap R U f) * g')
      (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u) := by
  subst hd
  subst hg'
  have hden :
      algebraMap T U
          ((((algebraMap R T f) * g)) * (IsLocalization.Away.sec ((algebraMap R T f) * g) u).1) =
        (algebraMap R U f) *
          (Subalgebra.inclusion hTU g *
            Subalgebra.inclusion hTU (IsLocalization.Away.sec ((algebraMap R T f) * g) u).1) := by
    -- Rewrite the iterated denominator through the canonical subalgebra-inclusion formula.
    ext
    rw [halg]
    simp [IsScalarTower.algebraMap_eq R T U, mul_assoc]
  -- The iterated target localization is exactly the away-localization at the cleared product
  -- denominator.
  rw [← hden]
  simpa [map_mul] using
    away_of_algebraMap_sec_fst (algebraMap T U) ((algebraMap R T f) * g) u

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the identity localization equivalence used in the insert
step transports `U`-generators in the iterated model to the same `U`-generators in the final
away-localization. -/
private lemma iteratedAwayTransport_algebraMap_apply
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (f : R) (g : T) (u : Localization.Away ((algebraMap R T f) * g)) (g' : U)
    [IsLocalization.Away ((algebraMap R U f) * g')
      (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)]
    (H : Submonoid.map (RingEquiv.refl U).toMonoidHom
      (Submonoid.powers ((algebraMap R U f) * g')) =
        Submonoid.powers ((algebraMap R U f) * g'))
    (z : U) :
    (IsLocalization.ringEquivOfRingEquiv
        (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
        (Localization.Away ((algebraMap R U f) * g')) (RingEquiv.refl U) H).toRingHom
      (algebraMap U
        (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
        z) =
      algebraMap U (Localization.Away ((algebraMap R U f) * g')) z := by
  -- Transport only a `U`-generator across the identity equivalence, avoiding mixed localized
  -- spellings in the final comparison.
  simpa using IsLocalization.ringEquivOfRingEquiv_eq
      (S := iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
      (Q := Localization.Away ((algebraMap R U f) * g'))
      (j := RingEquiv.refl U) H z

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: once the old away-product map and the new localized
one-generator map are finitely presented, their iterated composite is finitely presented. -/
private lemma iteratedAwayCompositeFinitePresentation
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (f : R) (g : T) (u : Localization.Away ((algebraMap R T f) * g))
    (hfpOld :
      (awayProductComparisonMap (algebraMap R T) f g).FinitePresentation)
    (hfpStep :
      (iteratedAwayInsertStepMap
        (R := R) (S := S) (T := T) (U := U) f g u).FinitePresentation) :
    ((iteratedAwayInsertStepMap
        (R := R) (S := S) (T := T) (U := U) f g u).comp
      ((iteratedAwayMidMap ((algebraMap R T f) * g) u).comp
        (awayProductComparisonMap (algebraMap R T) f g))).FinitePresentation := by
  have hfpOldLoc :
      ((iteratedAwayMidMap ((algebraMap R T f) * g) u).comp
        (awayProductComparisonMap (algebraMap R T) f g)).FinitePresentation := by
    -- Localizing the old target one more time preserves finite presentation.
    exact finitePresentation_toLocalizationAway_comp
      (awayProductComparisonMap (algebraMap R T) f g) u hfpOld
  -- Finish by composing with the finite-presentation singleton step.
  exact RingHom.FinitePresentation.comp hfpStep hfpOldLoc

/-
  Route correction: this transport lemma does not use the ambient domain/finiteness assumptions,
  so omit them here to keep the downstream transport helper instance-free.
-/
omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: after transporting the iterated localization model to the
canonical away-product localization, the resulting composite agrees with the final away-product
map. -/
private lemma transportedComposite_eq_finalMap
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (f : R) (g : T) (u : Localization.Away ((algebraMap R T f) * g)) (g' : U)
    [IsLocalization.Away ((algebraMap R U f) * g')
      (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)]
    (H : Submonoid.map (RingEquiv.refl U).toMonoidHom
      (Submonoid.powers ((algebraMap R U f) * g')) =
        Submonoid.powers ((algebraMap R U f) * g')) :
    letI :
        Algebra (Localization.Away ((algebraMap R T f) * g))
          (Localization.Away (algebraMap T U ((algebraMap R T f) * g))) :=
      (Localization.awayMap (algebraMap T U) ((algebraMap R T f) * g)).toAlgebra
    let oldMap : Localization.Away f →+* Localization.Away ((algebraMap R T f) * g) :=
      ((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
        (Localization.awayMap (algebraMap R T) f))
    let midMap : Localization.Away ((algebraMap R T f) * g) →+* Localization.Away u :=
      algebraMap (Localization.Away ((algebraMap R T f) * g)) (Localization.Away u)
    let stepMap :
        Localization.Away u →+*
          iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u :=
      Localization.awayMap
        (Localization.awayMap (algebraMap T U) ((algebraMap R T f) * g)) u
    let eLocHom :
        iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u →+*
          Localization.Away ((algebraMap R U f) * g') :=
      (IsLocalization.ringEquivOfRingEquiv
        (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
        (Localization.Away ((algebraMap R U f) * g')) (RingEquiv.refl U) H).toRingHom
    let finalMap : Localization.Away f →+* Localization.Away ((algebraMap R U f) * g') :=
      ((IsLocalization.Away.awayToAwayRight (algebraMap R U f) g').comp
        (Localization.awayMap (algebraMap R U) f))
    eLocHom.comp (stepMap.comp (midMap.comp oldMap)) = finalMap := by
  dsimp
  letI :
      Algebra (Localization.Away ((algebraMap R T f) * g))
        (Localization.Away (algebraMap T U ((algebraMap R T f) * g))) :=
    (Localization.awayMap (algebraMap T U) ((algebraMap R T f) * g)).toAlgebra
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext x
  simp only [RingHom.comp_apply]
  have hStepGenerator :
      (Localization.awayMap
          (Localization.awayMap (algebraMap T U) ((algebraMap R T f) * g)) u)
        ((algebraMap (Localization.Away ((algebraMap R T f) * g)) (Localization.Away u))
          (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
            (Localization.awayMap (algebraMap R T) f))
            ((algebraMap R (Localization.Away f)) x))) =
      algebraMap U
        (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
        ((algebraMap R U) x) := by
    have hGeneratorImage :
        (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
            (Localization.awayMap (algebraMap R T) f))
          ((algebraMap R (Localization.Away f)) x)) =
          algebraMap T (Localization.Away ((algebraMap R T f) * g)) ((algebraMap R T) x) := by
      rw [RingHom.comp_apply]
      rw [awayMap_algebraMap_apply]
      rw [IsLocalization.Away.awayToAwayRight_eq]
    rw [hGeneratorImage]
    simpa using
      stepMap_algebraMap_apply (R := R) (S := S) (T := T) (U := U)
        ((algebraMap R T f) * g) u x
  calc
    (IsLocalization.ringEquivOfRingEquiv
        (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
        (Localization.Away ((algebraMap R U f) * g')) (RingEquiv.refl U) H).toRingHom
      ((Localization.awayMap
          (Localization.awayMap (algebraMap T U) ((algebraMap R T f) * g)) u)
        ((algebraMap (Localization.Away ((algebraMap R T f) * g)) (Localization.Away u))
          (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
            (Localization.awayMap (algebraMap R T) f))
            ((algebraMap R (Localization.Away f)) x)))) =
      (IsLocalization.ringEquivOfRingEquiv
          (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
          (Localization.Away ((algebraMap R U f) * g')) (RingEquiv.refl U) H).toRingHom
        (algebraMap U
          (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
          ((algebraMap R U) x)) := by
            exact congrArg
              ((IsLocalization.ringEquivOfRingEquiv
                (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
                (Localization.Away ((algebraMap R U f) * g')) (RingEquiv.refl U) H).toRingHom)
              hStepGenerator
    _ =
      algebraMap U (Localization.Away ((algebraMap R U f) * g')) ((algebraMap R U) x) := by
            exact iteratedAwayTransport_algebraMap_apply
              (R := R) (S := S) (T := T) (U := U)
              (f := f) (g := g) (u := u) (g' := g') H ((algebraMap R U) x)
    _ =
      ((IsLocalization.Away.awayToAwayRight (algebraMap R U f) g').comp
        (Localization.awayMap (algebraMap R U) f))
          ((algebraMap R (Localization.Away f)) x) := by
            symm
            rw [RingHom.comp_apply]
            rw [awayMap_algebraMap_apply]
            rw [IsLocalization.Away.awayToAwayRight_eq]

omit [IsDomain S] [FaithfulSMul R S] [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: finite presentation on the iterated localization model
transports to the canonical final away-product map after clearing the extra denominator. -/
private lemma transportFinitePresentationToFinalAwayProduct
    {T U : Subalgebra R S} [Algebra T U] [IsScalarTower R T U]
    (f : R) (g : T) (u : Localization.Away ((algebraMap R T f) * g)) (g' : U)
    (hfinalLoc :
      IsLocalization.Away ((algebraMap R U f) * g')
        (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u))
    (hfpTwoStage :
      ((iteratedAwayInsertStepMap
          (R := R) (S := S) (T := T) (U := U) f g u).comp
        ((iteratedAwayMidMap ((algebraMap R T f) * g) u).comp
          (awayProductComparisonMap (algebraMap R T) f g))).FinitePresentation) :
    (awayProductComparisonMap (algebraMap R U) f g').FinitePresentation := by
  letI : IsLocalization.Away ((algebraMap R U f) * g')
      (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u) := hfinalLoc
  let H : Submonoid.map (RingEquiv.refl U).toMonoidHom
      (Submonoid.powers ((algebraMap R U f) * g')) =
        Submonoid.powers ((algebraMap R U f) * g') := by
    -- The comparison equivalence between the two localization models is the identity on `U`.
    simp
  let eLoc :
      iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u ≃+*
        Localization.Away ((algebraMap R U f) * g') :=
    IsLocalization.ringEquivOfRingEquiv
      (iteratedAwayTarget (T := T) (U := U) ((algebraMap R T f) * g) u)
      (Localization.Away ((algebraMap R U f) * g')) (RingEquiv.refl U) H
  have heLocfp :
      eLoc.toRingHom.FinitePresentation := by
    -- Ring equivalences are finitely presented as ring maps.
    exact RingHom.FinitePresentation.of_bijective (f := eLoc.toRingHom) eLoc.bijective
  have hfpTransported :
      (eLoc.toRingHom.comp
        ((iteratedAwayInsertStepMap
            (R := R) (S := S) (T := T) (U := U) f g u).comp
          ((iteratedAwayMidMap ((algebraMap R T f) * g) u).comp
            (awayProductComparisonMap (algebraMap R T) f g)))).FinitePresentation := by
    -- Transport finite presentation across the identity equivalence of localization models.
    exact RingHom.FinitePresentation.comp heLocfp hfpTwoStage
  have hcomp :
      eLoc.toRingHom.comp
          ((iteratedAwayInsertStepMap
              (R := R) (S := S) (T := T) (U := U) f g u).comp
            ((iteratedAwayMidMap ((algebraMap R T f) * g) u).comp
              (awayProductComparisonMap (algebraMap R T) f g))) =
        awayProductComparisonMap (algebraMap R U) f g' := by
    -- Reuse the dedicated transport identity instead of rebuilding it in the main theorem.
    simpa [awayProductComparisonMap, iteratedAwayMidMap, iteratedAwayInsertStepMap] using
      transportedComposite_eq_finalMap
        (R := R) (S := S) (T := T) (U := U)
        (f := f) (g := g) (u := u) (g' := g') H
  -- Rewrite to the canonical final away-product spelling.
  rw [hcomp] at hfpTransported
  exact hfpTransported

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: a one-generator extension of generated subalgebras preserves
the away-product finite-presentation conclusion after multiplying by one further denominator. -/
lemma exists_nonzero_awayProductMap_finitePresentation_of_adjoin_singleton_eq_top
    {T U : Subalgebra R S} (hTU : T ≤ U)
    (f : R) (hf : f ≠ 0) (g : T) (hg : g ≠ 0)
    (hfp :
      (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
        (Localization.awayMap (algebraMap R T) f)) :
          Localization.Away f →+*
            Localization.Away ((algebraMap R T f) * g)).FinitePresentation)
    (x : U)
    (hgen :
      @Algebra.adjoin T U _ _ (Subalgebra.inclusion hTU).toAlgebra
        ({x} : Set U) = ⊤) :
    ∃ (g' : U) (_ : g' ≠ 0),
      (((IsLocalization.Away.awayToAwayRight (algebraMap R U f) g').comp
        (Localization.awayMap (algebraMap R U) f)) :
          Localization.Away f →+*
            Localization.Away ((algebraMap R U f) * g')).FinitePresentation := by
  -- The proof follows the source one-generator step after the old denominator has been inverted:
  -- set `a = f * g` in `T`, apply the generic one-generator localization theorem to
  -- `T_a → U_a`, and then clear the second denominator using `sec`.
  letI : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
  let a : T := (algebraMap R T f) * g
  have hfT : algebraMap R T f ≠ 0 := by
    intro hfTzero
    apply hf
    apply FaithfulSMul.algebraMap_injective R S
    simpa using congrArg Subtype.val hfTzero
  have ha : a ≠ 0 := by
    -- The old product denominator is nonzero in the intermediate domain.
    dsimp [a]
    exact mul_ne_zero hfT hg
  have hmapa : algebraMap T U a ≠ 0 := by
    -- Inclusion of subalgebras preserves nonzero denominators.
    simpa [RingHom.algebraMap_toAlgebra] using subalgebra_inclusion_ne_zero hTU ha
  letI : IsDomain (Localization.Away a) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away a) (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
  letI : IsDomain (Localization.Away (algebraMap T U a)) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors
      (Localization.Away (algebraMap T U a))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hmapa)
  letI : Algebra (Localization.Away a) (Localization.Away (algebraMap T U a)) :=
    (Localization.awayMap (algebraMap T U) a).toAlgebra
  have hinj :
      Function.Injective
        (algebraMap (Localization.Away a)
          (Localization.Away (algebraMap T U a))) := by
    -- The localized inclusion remains injective because the original subalgebra inclusion is.
    simpa [RingHom.algebraMap_toAlgebra] using awayMap_injective_of_subalgebra_inclusion hTU a
  have hgenLoc :
      Algebra.adjoin (Localization.Away a)
        ({algebraMap U (Localization.Away (algebraMap T U a)) x} :
          Set (Localization.Away (algebraMap T U a))) = ⊤ := by
    -- Singleton generation survives localization at the old denominator.
    simpa [a] using localized_adjoin_singleton_eq_top (A := T) (B := U) a x hgen
  rcases exists_nonzero_awayMap_finitePresentation_of_adjoin_singleton_domain
      (A := Localization.Away a) (B := Localization.Away (algebraMap T U a))
      hinj (algebraMap U (Localization.Away (algebraMap T U a)) x) hgenLoc with
    ⟨u, hu, hfpStep⟩
  let d : T := (IsLocalization.Away.sec a u).1
  let g' : U := Subalgebra.inclusion hTU g * Subalgebra.inclusion hTU d
  have hd : d ≠ 0 := by
    -- The second localized denominator has a nonzero chosen numerator in `T`.
    simpa [d] using away_sec_fst_ne_zero a hu
  have hgU : Subalgebra.inclusion hTU g ≠ 0 := by
    -- The old nonzero `g` stays nonzero in the enlarged generated subalgebra.
    exact subalgebra_inclusion_ne_zero hTU hg
  have hdU : Subalgebra.inclusion hTU d ≠ 0 := by
    -- The newly chosen numerator also stays nonzero after inclusion.
    exact subalgebra_inclusion_ne_zero hTU hd
  have hg' : g' ≠ 0 := by
    -- The final denominator is the product of the old and new nonzero target denominators.
    dsimp [g']
    exact mul_ne_zero hgU hdU
  refine ⟨g', hg', ?_⟩
  have hfpOld :
      (awayProductComparisonMap (algebraMap R T) f g).FinitePresentation := by
    -- Repackage the induction hypothesis using the named old denominator `a`.
    simpa [awayProductComparisonMap, a] using hfp
  have hfpStep' :
      (iteratedAwayInsertStepMap
        (R := R) (S := S) (T := T) (U := U) f g u).FinitePresentation := by
    -- The singleton step already gives finite presentation in the canonical iterated spelling.
    simpa [iteratedAwayInsertStepMap, a] using hfpStep
  have hfpTwoStage :
      ((iteratedAwayInsertStepMap
          (R := R) (S := S) (T := T) (U := U) f g u).comp
        ((iteratedAwayMidMap a u).comp
          (awayProductComparisonMap (algebraMap R T) f g))).FinitePresentation := by
    -- Assemble the two-stage localization in a separate helper to avoid repeating the transport
    -- stack inside this main insert-step theorem.
    simpa [a] using
      iteratedAwayCompositeFinitePresentation
        (R := R) (S := S) (T := T) (U := U) (f := f) (g := g) (u := u) hfpOld hfpStep'
  have hfinalLoc :
      IsLocalization.Away ((algebraMap R U f) * g')
        (iteratedAwayTarget (T := T) (U := U) a u) := by
    -- Package the denominator-clearing transport once so the main theorem no longer re-elaborates
    -- the iterated away-localization bridge inline.
    simpa [a] using
      iteratedAwayTarget_isLocalizationAway_finalDenominator
        (R := R) (S := S) hTU (by simpa [RingHom.algebraMap_toAlgebra]) f g d u g' rfl rfl
  -- Route correction: keep the final transport in its own helper so this theorem only assembles
  -- the source-proof ingredients.
  simpa [awayProductComparisonMap, a] using
    transportFinitePresentationToFinalAwayProduct
      (R := R) (S := S) (T := T) (U := U)
      (f := f) (g := g) (u := u) (g' := g') hfinalLoc hfpTwoStage

omit [Algebra.FiniteType R S] in
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
  rcases ih with ⟨f, hf, g, hg, hfp⟩
  let T : Subalgebra R S := Algebra.adjoin R (↑s : Set S)
  let U : Subalgebra R S := Algebra.adjoin R ({x} ∪ (↑s : Set S))
  have hTU : T ≤ U := by
    -- The old generated subalgebra maps canonically into the enlarged one.
    dsimp [T, U]
    exact adjoin_le_adjoin_singleton_union (A := R) (↑s : Set S) x
  let gU : U := Subalgebra.inclusion hTU g
  have hgU : gU ≠ 0 := by
    -- The old denominator remains nonzero after inclusion into the enlarged subalgebra.
    exact subalgebra_inclusion_ne_zero hTU hg
  have hxU : x ∈ U := by
    -- The new generator is available as an element of the enlarged subalgebra.
    dsimp [U]
    exact mem_adjoin_singleton_union_left (A := R) (↑s : Set S) x
  have hgen :
      @Algebra.adjoin T U _ _ (Subalgebra.inclusion hTU).toAlgebra
        ({(⟨x, hxU⟩ : U)} : Set U) = ⊤ := by
    -- The enlarged subalgebra is generated over the old one by the inserted element.
    simpa [T, U] using
      adjoin_singleton_eq_top_of_insertSubalgebra (R := R) (S := S) (↑s : Set S) x
  letI : Algebra T U := (Subalgebra.inclusion hTU).toAlgebra
  have hfpT :
      (((IsLocalization.Away.awayToAwayRight (algebraMap R T f) g).comp
        (Localization.awayMap (algebraMap R T) f)) :
          Localization.Away f →+*
            Localization.Away ((algebraMap R T f) * g)).FinitePresentation := by
    -- Re-express the induction hypothesis using the stable abbreviation `T`.
    simpa [T] using hfp
  rcases exists_nonzero_awayProductMap_finitePresentation_of_adjoin_singleton_eq_top
      (R := R) (S := S) hTU f hf g hg hfpT (⟨x, hxU⟩ : U) hgen with
    ⟨gFinal, hgFinal, hfpFinal⟩
  -- The abstract one-generator helper supplies exactly the final denominator and map.
  exact ⟨f, hf, gFinal, hgFinal, hfpFinal⟩

omit [Algebra.FiniteType R S] in
/-- Helper for Chap10 Lemma 10 30 1: the empty generating-set case identifies
`Algebra.adjoin R ∅` with the image of `R`, so localizing at `1` yields a finitely presented
comparison map. -/
lemma exists_nonzero_localizationAwayProductGeneratedSubalgebra_finitePresentation_of_empty :
    ∃ (f : R) (_ : f ≠ 0)
      (g : Algebra.adjoin R (↑(∅ : Finset S) : Set S)) (_ : g ≠ 0),
      (((IsLocalization.Away.awayToAwayRight
          (algebraMap R (Algebra.adjoin R (↑(∅ : Finset S) : Set S)) f) g).comp
        (Localization.awayMap (algebraMap R (Algebra.adjoin R (↑(∅ : Finset S) : Set S))) f)) :
          Localization.Away f →+*
            Localization.Away
              ((algebraMap R (Algebra.adjoin R (↑(∅ : Finset S) : Set S)) f) * g)).FinitePresentation := by
  -- The empty generated subalgebra is the image of `R`; localizing at `1` transports finite
  -- presentation across bijective localization maps.
  letI : IsDomain R := (FaithfulSMul.algebraMap_injective R S).isDomain
  let T : Subalgebra R S := Algebra.adjoin R (↑(∅ : Finset S) : Set S)
  have hsurj : Function.Surjective (algebraMap R T) := by
    intro y
    have hy : (y : S) ∈ (⊥ : Subalgebra R S) := by
      simpa [T, Algebra.adjoin_empty] using y.property
    rcases Set.mem_range.mp (by simpa [Algebra.mem_bot] using hy) with ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr⟩
  have hinj : Function.Injective (algebraMap R T) := by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective R S
    exact congrArg Subtype.val hab
  refine ⟨1, one_ne_zero, (1 : T), one_ne_zero, ?_⟩
  have hmapinj : Function.Injective (Localization.awayMap (algebraMap R T) (1 : R)) := by
    rw [Localization.awayMap_injective_iff]
    intro a ha
    exact ⟨0, by simpa using hinj (by simpa using ha)⟩
  have hmapsurj : Function.Surjective (Localization.awayMap (algebraMap R T) (1 : R)) := by
    rw [Localization.awayMap_surjective_iff]
    intro a
    rcases hsurj a with ⟨b, rfl⟩
    exact ⟨b, 0, by simp⟩
  have hmapfp : (Localization.awayMap (algebraMap R T) (1 : R)).FinitePresentation :=
    RingHom.FinitePresentation.of_bijective ⟨hmapinj, hmapsurj⟩
  letI : IsLocalization.Away (algebraMap R T (1 : R))
      (Localization.Away ((algebraMap R T (1 : R)) * (1 : T))) := by
    simpa using (inferInstance : IsLocalization.Away
      (((algebraMap R T (1 : R)) * (1 : T)))
      (Localization.Away ((algebraMap R T (1 : R)) * (1 : T))))
  have hrightbij : Function.Bijective
      ((IsLocalization.Away.awayToAwayRight (algebraMap R T (1 : R)) (1 : T)) :
        Localization.Away (algebraMap R T (1 : R)) →+*
          Localization.Away ((algebraMap R T (1 : R)) * (1 : T))) := by
    apply IsLocalization.bijective (Submonoid.powers (algebraMap R T (1 : R)))
    ext x
    simp [IsLocalization.Away.awayToAwayRight_eq]
  have hrightfp :
      (((IsLocalization.Away.awayToAwayRight (algebraMap R T (1 : R)) (1 : T)) :
        Localization.Away (algebraMap R T (1 : R)) →+*
          Localization.Away ((algebraMap R T (1 : R)) * (1 : T)))).FinitePresentation :=
    RingHom.FinitePresentation.of_bijective hrightbij
  exact RingHom.FinitePresentation.comp hrightfp hmapfp

omit [Algebra.FiniteType R S] in
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
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty branch is packaged separately so the finset induction theorem stays lightweight.
      simpa using
        exists_nonzero_localizationAwayProductGeneratedSubalgebra_finitePresentation_of_empty
          (R := R) (S := S)
  | insert x s hx ih =>
      -- The induction step is isolated in the preceding source-facing insert helper.
      have hset : (↑(insert x s) : Set S) = ({x} : Set S) ∪ (↑s : Set S) := by
        ext y
        simp
      rw [hset]
      exact exists_nonzero_localizationAwayProductGeneratedSubalgebra_finitePresentation_of_insert
        (R := R) (S := S) s x ih

omit [Algebra.FiniteType R S] in
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
/-- Chap10 Lemma 10 30 1 (Lemma 10.30.1, 00FG): if `R ⊆ S` is an inclusion of domains and
`R → S` is of finite type,
then there exist nonzero `f ∈ R` and `g ∈ S` such that the canonical map
`R_f → S_(fg)` is of finite presentation. -/
-- Proof sketch: argue by induction on the number of algebra generators of `S` over `R`.
-- In the one-generator case, represent `S` as `R[x] / q`, choose a nonzero relation of minimal
-- degree, and invert its leading coefficient to obtain a monic polynomial presentation. For more
-- generators, first make the subalgebra on `n - 1` generators finitely presented after localizing,
-- then apply the one-generator step to the final generator and combine the two localizations.
@[stacks 00FG]
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
