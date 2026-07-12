import Mathlib.RingTheory.RingHom.EssFiniteType
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Congruence.Hom
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open IsLocalRing

section

namespace CompositionSeries

variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]

/-- Helper for Lemma 10.54.4: the `i`-th successive quotient in a composition series of
submodules. -/
private abbrev factor (s : CompositionSeries (Submodule A M)) (i : Fin s.length) :=
  s i.succ ⧸ (s i.castSucc).comap (s i.succ).subtype

/-- Helper for Lemma 10.54.4: each successive quotient in a composition series is a simple
module. -/
private theorem factor_isSimpleModule (s : CompositionSeries (Submodule A M)) (i : Fin s.length) :
    IsSimpleModule A (s.factor i) := by
  -- The cover relation in the composition series identifies the quotient as a simple module.
  simpa [factor] using
    (covBy_iff_quot_is_simple (CovBy.le (s.step i))).mp (s.step i)

/-- Helper for Lemma 10.54.4: the annihilator of each composition-series factor is maximal. -/
private theorem factor_annihilator_isMaximal (s : CompositionSeries (Submodule A M))
    (i : Fin s.length) : (Module.annihilator A (s.factor i)).IsMaximal := by
  let _ : IsSimpleModule A (s.factor i) := s.factor_isSimpleModule i
  -- Over a commutative ring, the annihilator of a simple module is maximal.
  exact IsSimpleModule.annihilator_isMaximal

/-- Helper for Lemma 10.54.4: each composition-series factor is linearly equivalent to the
quotient of the ring by its annihilator. -/
private theorem factor_isomorphic_quotient_annihilator
    (s : CompositionSeries (Submodule A M)) (i : Fin s.length) :
    Nonempty (s.factor i ≃ₗ[A] A ⧸ Module.annihilator A (s.factor i)) := by
  have hsimple : IsSimpleModule A (s.factor i) := s.factor_isSimpleModule i
  -- Replace the simple factor by the canonical quotient by its annihilator.
  obtain ⟨I, _, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hAnn : Module.annihilator A (s.factor i) = I := by
    rw [e.annihilator_eq, I.annihilator_quotient]
  exact ⟨e.trans <| Submodule.quotEquivOfEq _ _ hAnn.symm⟩

end CompositionSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsArtinianRing S] [IsLocalRing S]

omit [IsArtinianRing S] in
private theorem residue_finite : (residue S).Finite :=
  RingHom.Finite.of_surjective _ residue_surjective

omit [IsArtinianRing S] in
private theorem residue_finiteType : (residue S).FiniteType :=
  RingHom.FiniteType.of_surjective _ residue_surjective

omit [IsArtinianRing S] in
private theorem residue_essFiniteType : (residue S).EssFiniteType :=
  residue_finiteType.essFiniteType

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: every composition-series factor of an Artinian local ring is
linearly equivalent, after restricting scalars along `f`, to the residue field. -/
private theorem compositionSeries_factor_equiv_residue [Algebra R S]
    (s : CompositionSeries (Submodule S S)) (i : Fin s.length) :
    Nonempty ((s.factor i) ≃ₗ[R] ResidueField S) := by
  let J : Ideal S := Module.annihilator S (s.factor i)
  have hJmax : J.IsMaximal := s.factor_annihilator_isMaximal i
  have hJ : J = maximalIdeal S := IsLocalRing.eq_maximalIdeal hJmax
  let e₁ : s.factor i ≃ₗ[S] S ⧸ J :=
    Classical.choice (s.factor_isomorphic_quotient_annihilator i)
  let e₂ : (S ⧸ J) ≃ₐ[R] ResidueField S :=
    { Ideal.quotEquivOfEq hJ with
      commutes' := fun r ↦ rfl }
  exact ⟨(e₁.restrictScalars R).trans e₂.toLinearEquiv⟩

/-- Helper for Lemma 10.54.4: finite generation of the residue field over `R` propagates through
an `S`-composition series of the Artinian local ring `S`. -/
private theorem finite_of_artinianLocal_of_residue_finite (f : R →+* S)
    (h : ((residue S).comp f).Finite) : f.Finite := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R (ResidueField S) := (((residue S).comp f).toAlgebra)
  have hκ : Module.Finite R (ResidueField S) := (RingHom.finite_algebraMap).mp h
  have hFiniteLength : IsFiniteLength S S := (isArtinianRing_iff_isFiniteLength S).mp inferInstance
  obtain ⟨s, hs0, hs1⟩ := isFiniteLength_iff_exists_compositionSeries.mp hFiniteLength
  have hprefix :
      ∀ n : ℕ, ∀ hn : n ≤ s.length,
        Module.Finite R ↥((s ⟨n, Nat.lt_succ_of_le hn⟩).restrictScalars R) := by
    intro n
    induction n with
    | zero =>
        intro hn
        -- The initial stage of the composition series is the zero submodule.
        have hs0R : (s ⟨0, Nat.lt_succ_of_le hn⟩).restrictScalars R = ⊥ := by
          simpa using congrArg (Submodule.restrictScalars R) hs0
        let e0 : ↥((s ⟨0, Nat.lt_succ_of_le hn⟩).restrictScalars R) ≃ₗ[R] ↥(⊥ : Submodule R S) :=
          LinearEquiv.ofEq _ _ hs0R
        exact (Module.Finite.equiv_iff e0).2 inferInstance
    | succ n ih =>
        intro hn
        have hn' : n ≤ s.length := Nat.le_of_succ_le hn
        let i : Fin s.length := ⟨n, Nat.lt_of_succ_le hn⟩
        let P : Submodule R S := (s i.succ).restrictScalars R
        let Q : Submodule R S := (s i.castSucc).restrictScalars R
        let N : Submodule R P := Q.comap P.subtype
        have hQ : Module.Finite R Q := by
          simpa [Q] using ih hn'
        have hN : Module.Finite R N := by
          -- Identify the pulled-back predecessor with the predecessor itself.
          let e₀ := N.equivMapOfInjective P.subtype (Submodule.injective_subtype _)
          have hQP : Q ≤ P := by
            intro x hx
            exact CovBy.le (s.step i) hx
          have hmap : N.map P.subtype = Q := by
            rw [Submodule.map_comap_subtype, inf_of_le_right hQP]
          let e : N ≃ₗ[R] Q := e₀.trans <| LinearEquiv.ofEq _ _ hmap
          exact (Module.Finite.equiv_iff e).2 hQ
        have hfactor : Module.Finite R (s.factor i) := by
          obtain ⟨e⟩ := compositionSeries_factor_equiv_residue (R := R) (S := S) s i
          exact (Module.Finite.equiv_iff e).2 hκ
        have hfactor' : Module.Finite R (P ⧸ N) := by
          simpa [P, Q, N, CompositionSeries.factor] using hfactor
        -- The next stage is an extension of the predecessor by the current simple factor.
        letI : Module.Finite R N := hN
        letI : Module.Finite R (P ⧸ N) := hfactor'
        exact show Module.Finite R P from
          Module.Finite.of_exact (LinearMap.exact_subtype_mkQ N) (Submodule.mkQ_surjective _)
  -- The final stage is the whole ring `S`.
  have hs1R : ((s (Fin.last s.length)).restrictScalars R : Submodule R S) = ⊤ := by
    simpa using congrArg (Submodule.restrictScalars R) hs1
  have hS : Module.Finite R ↥((s (Fin.last s.length)).restrictScalars R) := hprefix s.length le_rfl
  have hS' : Module.Finite R S := by
    let eTop :
        ↥((s (Fin.last s.length)).restrictScalars R) ≃ₗ[R] S :=
      (LinearEquiv.ofEq _ _ hs1R).trans (Submodule.topEquiv : (⊤ : Submodule R S) ≃ₗ[R] S)
    exact (Module.Finite.equiv_iff eTop).1 hS
  exact (RingHom.finite_algebraMap).mpr hS'

-- Proof sketch: the forward implication is stability of finiteness under passage to the residue
-- field via the canonical composition theorem `RingHom.Finite.comp`. For the reverse implication,
-- use that an Artinian local ring has finite length over itself with successive quotients
-- isomorphic to `ResidueField S`, then deduce finite generation over `R` by induction on the
-- filtration length.
/-- Lemma 10.54.4 (1): for a ring map `R → S` with `S` an Artinian local ring, the map is finite
if and only if the induced map to the residue field of `S` is finite. -/
@[stacks 07DT]
theorem finite_iff_finite_residue (f : R →+* S) :
    f.Finite ↔ ((residue S).comp f).Finite := by
  constructor
  · intro hf
    exact residue_finite.comp hf
  · intro h
    -- Route correction: instead of trying to build generators directly, propagate finite
    -- generation along a composition series whose factors are all copies of the residue field.
    exact finite_of_artinianLocal_of_residue_finite (R := R) (S := S) f h

-- Proof sketch: the forward implication is stability of finite type under passage to the residue
-- field via the canonical composition theorem `RingHom.FiniteType.comp`. For the reverse
-- implication, choose lifts in `S` of generators of `ResidueField S`, map a polynomial ring over
-- `R` onto those lifts, and then apply part (1) to show the polynomial algebra maps finitely to
-- `S`, which makes `R → S` finite type.
/-- Lemma 10.54.4 (2): for a ring map `R → S` with `S` an Artinian local ring, the map is of
finite type if and only if the induced map to the residue field of `S` is of finite type. -/
@[stacks 07DT]
theorem finiteType_iff_finiteType_residue (f : R →+* S) :
    f.FiniteType ↔ ((residue S).comp f).FiniteType := by
  constructor
  · intro hf
    exact residue_finiteType.comp hf
  · intro h
    classical
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ResidueField S) := (((residue S).comp f).toAlgebra)
    letI : Algebra.FiniteType R (ResidueField S) := (RingHom.finiteType_algebraMap).mp h
    obtain ⟨n, π, hπsurj⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := ResidueField S)).mp
        inferInstance
    choose x hx using fun i : Fin n ↦ IsLocalRing.residue_surjective (π <| MvPolynomial.X i)
    let φ : MvPolynomial (Fin n) R →ₐ[R] S := MvPolynomial.aeval x
    have hres_ring : (residue S).comp φ.toRingHom = π.toRingHom := by
      -- The lifted polynomial map agrees with the chosen residue-field presentation on
      -- coefficients and variables.
      apply MvPolynomial.ringHom_ext'
      · ext r
        simp [φ, RingHom.algebraMap_toAlgebra]
      · intro i
        simpa [φ, hx i]
    have hφres : ((residue S).comp φ.toRingHom).Finite := by
      rw [hres_ring]
      exact RingHom.Finite.of_surjective _ hπsurj
    have hφ : φ.toRingHom.Finite :=
      (finite_iff_finite_residue (R := MvPolynomial (Fin n) R) (S := S) φ.toRingHom).2 hφres
    have hφcomp :
        φ.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R)) = f := by
      -- The lifted polynomial map extends the original structural map `R → S`.
      ext r
      simp [φ, RingHom.algebraMap_toAlgebra]
    have hcomp :
        (φ.toRingHom.comp (algebraMap R (MvPolynomial (Fin n) R))).FiniteType := by
      exact RingHom.FiniteType.comp hφ.to_finiteType
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    rw [hφcomp] at hcomp
    exact hcomp

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: the restricted residue map is compatible with the chosen
`R`-algebra structure on the residue field. -/
private theorem restricted_residueAlgHom_commutes
    [Algebra R S] [Algebra R (ResidueField S)]
    (hκ : algebraMap R (ResidueField S) = (residue S).comp (algebraMap R S))
    (A : Subalgebra R S) (r : R) :
    ((residue S).comp (algebraMap A S)) (algebraMap R A r) = algebraMap R (ResidueField S) r := by
  -- The subalgebra structure map factors through `S`, so the compatibility is exactly `hκ`.
  simpa [Subalgebra.algebraMap_eq] using
    congrArg (fun g : R →+* ResidueField S ↦ g r) hκ.symm

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: the residue map restricted to a subalgebra of `S`. -/
private noncomputable abbrev restricted_residueAlgHom
    [Algebra R S] [Algebra R (ResidueField S)]
    (hκ : algebraMap R (ResidueField S) = (residue S).comp (algebraMap R S))
    (A : Subalgebra R S) :
    A →ₐ[R] ResidueField S :=
  { toRingHom := (residue S).comp (algebraMap A S)
    commutes' := restricted_residueAlgHom_commutes (R := R) (S := S) hκ A }

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: the restricted residue map on a finite-type subalgebra identifies
the quotient by the contracted maximal ideal with its image in the residue field. -/
private theorem lifted_subalgebra_quotient_equiv
    [Algebra R S] [Algebra R (ResidueField S)]
    (hκ : algebraMap R (ResidueField S) = (residue S).comp (algebraMap R S))
    (A : Subalgebra R S) (B : Subalgebra R (ResidueField S))
    (hB : (restricted_residueAlgHom (R := R) (S := S) hκ A).range = B) :
    ∃ e : (A ⧸ Ideal.comap (algebraMap A S) (maximalIdeal S)) ≃ₐ[R] B,
      ((algebraMap B (ResidueField S)).comp e.toRingHom).comp
          (Ideal.Quotient.mk (Ideal.comap (algebraMap A S) (maximalIdeal S))) =
        (residue S).comp (algebraMap A S) := by
  let ρA : A →ₐ[R] ResidueField S := restricted_residueAlgHom (R := R) (S := S) hκ A
  have hker : RingHom.ker ρA.toRingHom = Ideal.comap (algebraMap A S) (maximalIdeal S) := by
    -- The kernel is exactly the contraction of the maximal ideal along `A ↪ S`.
    ext a
    rw [RingHom.mem_ker]
    change residue S (algebraMap A S a) = 0 ↔ algebraMap A S a ∈ maximalIdeal S
    exact IsLocalRing.residue_eq_zero_iff (algebraMap A S a)
  -- Route correction: apply the first isomorphism theorem only to the small restricted residue
  -- map `ρA`, then rewrite its kernel and range to the textbook objects.
  let e₁ : (A ⧸ Ideal.comap (algebraMap A S) (maximalIdeal S)) ≃ₐ[R] A ⧸ RingHom.ker ρA.toRingHom :=
    Ideal.quotientEquivAlgOfEq R hker.symm
  let e₂ : (A ⧸ RingHom.ker ρA.toRingHom) ≃ₐ[R] ρA.range :=
    Ideal.quotientKerEquivRange (R := R) ρA
  let e₃ : ρA.range ≃ₐ[R] B := Subalgebra.equivOfEq _ _ hB
  let e : (A ⧸ Ideal.comap (algebraMap A S) (maximalIdeal S)) ≃ₐ[R] B :=
    e₁.trans (e₂.trans e₃)
  refine ⟨e, ?_⟩
  -- After composing with the inclusion `B ↪ ResidueField S`, the quotient map recovers `ρA`.
  ext a
  change ↑(e₃ (e₂ (e₁ (Ideal.Quotient.mk _ a)))) = (residue S) ↑a
  rw [show e₁ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk (RingHom.ker ρA.toRingHom) a by
      simpa [e₁] using
        (Ideal.quotientEquivAlgOfEq_mk (R₁ := R) hker.symm a)]
  have hmk_range :
      e₂ (Ideal.Quotient.mk (RingHom.ker ρA.toRingHom) a) =
        ⟨ρA a, AlgHom.mem_range_self ρA a⟩ := by
    change
      Ideal.quotientKerAlgEquivOfSurjective ρA.rangeRestrict_surjective
          ((Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict ρA).symm)
            (Ideal.Quotient.mk (RingHom.ker ρA.toRingHom) a)) =
        ⟨ρA a, AlgHom.mem_range_self ρA a⟩
    have hmk_eq :
        (Ideal.quotientEquivAlgOfEq R (AlgHom.ker_rangeRestrict ρA).symm)
            (Ideal.Quotient.mk (RingHom.ker ρA.toRingHom) a) =
          Ideal.Quotient.mk _ a := by
      rfl
    rw [hmk_eq]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk ρA.rangeRestrict_surjective a
  have hmk : ↑(e₂ (Ideal.Quotient.mk (RingHom.ker ρA.toRingHom) a)) = ρA a := by
    exact congrArg Subtype.val hmk_range
  simpa [hmk, ρA]

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: lift a finite generating set of an essentially finite-type
residue-field witness to a finite-type subalgebra of `S` whose restricted residue map has exactly
the prescribed image. -/
private theorem exists_lifted_finiteType_subalgebra_with_image_eq (f : R →+* S)
    [Algebra R S] [Algebra R (ResidueField S)]
    (hfS : algebraMap R S = f)
    (hfκ : algebraMap R (ResidueField S) = (residue S).comp f)
    (h : ((residue S).comp f).EssFiniteType) :
    ∃ (A : Subalgebra R S) (B : Subalgebra R (ResidueField S)) (M : Submonoid B),
      Algebra.FiniteType R A ∧ IsLocalization M (ResidueField S) ∧
        (restricted_residueAlgHom (R := R) (S := S)
          (by simpa [hfS] using hfκ) A).range = B := by
  classical
  have hκ : algebraMap R (ResidueField S) = (residue S).comp (algebraMap R S) := by
    simpa [hfS] using hfκ
  letI : Algebra.EssFiniteType R (ResidueField S) := by
    rw [← RingHom.essFiniteType_algebraMap]
    simpa [hfκ] using h
  obtain ⟨B, M, hBft, hloc⟩ :=
    (Algebra.essFiniteType_iff_exists_subalgebra (R := R) (S := ResidueField S)).1 inferInstance
  letI : Algebra.FiniteType R B := hBft
  letI : IsLocalization M (ResidueField S) := hloc
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := R) (A := B)
  choose lift hlift using fun x : t ↦ IsLocalRing.residue_surjective ((x : B) : ResidueField S)
  let A : Subalgebra R S := Algebra.adjoin R (Set.range lift)
  have hAft : Algebra.FiniteType R A := by
    -- The lifted generators define `A` as a finite adjoin over `R`.
    simpa [A] using
      (Algebra.FiniteType.adjoin_of_finite (R := R) (t := Set.range lift) (Set.finite_range lift))
  let ρA : A →ₐ[R] ResidueField S := restricted_residueAlgHom (R := R) (S := S) hκ A
  have hρA_mem_B : ∀ a : A, ρA a ∈ B := by
    -- Every adjoined lift maps back into `B`, so the whole restricted residue map lands in `B`.
    intro a
    change residue S (a : S) ∈ B
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ a.2
    · intro s hs
      rcases hs with ⟨x, rfl⟩
      simpa [hlift x] using (show (((x : t) : B) : ResidueField S) ∈ B from ((x : B).2))
    · intro r
      simpa [hκ] using B.algebraMap_mem r
    · intro x y _ _ hx hy
      exact B.add_mem hx hy
    · intro x y _ _ hx hy
      exact B.mul_mem hx hy
  let ρAB : A →ₐ[R] B := ρA.codRestrict B hρA_mem_B
  have hgen : (t : Set B) ⊆ ρAB.range := by
    -- Each chosen generator of `B` is the residue of its selected lift in `A`.
    intro x hx
    let xt : t := ⟨x, hx⟩
    refine (AlgHom.mem_range ρAB).2 ?_
    refine ⟨⟨lift xt, Algebra.subset_adjoin (Set.mem_range_self xt)⟩, ?_⟩
    ext
    simpa [ρAB, ρA, hlift xt, xt]
  have hrange_top : ρAB.range = ⊤ := by
    -- Since the range contains a finite generating set of `B`, it must be all of `B`.
    apply top_unique
    rw [← ht]
    exact Algebra.adjoin_le_iff.mpr hgen
  have hρAB_surj : Function.Surjective ρAB := (AlgHom.range_eq_top ρAB).mp hrange_top
  have hρA_range : ρA.range = B := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨a, rfl⟩
      exact hρA_mem_B a
    · intro y hy
      obtain ⟨a, ha⟩ := hρAB_surj ⟨y, hy⟩
      exact (AlgHom.mem_range ρA).2 ⟨a, congrArg Subtype.val ha⟩
  exact ⟨A, B, M, hAft, hloc, hρA_range⟩

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: an essentially finite-type residue-field witness lifts to a finite-
type subalgebra of `S` whose quotient by the contracted maximal ideal recovers the witness
subalgebra of the residue field. -/
private theorem exists_lifted_finiteType_subalgebra_with_quotient_equiv (f : R →+* S)
    [Algebra R S] [Algebra R (ResidueField S)]
    (hfS : algebraMap R S = f)
    (hfκ : algebraMap R (ResidueField S) = (residue S).comp f)
    (h : ((residue S).comp f).EssFiniteType) :
    ∃ (A : Subalgebra R S) (B : Subalgebra R (ResidueField S)) (M : Submonoid B),
      Algebra.FiniteType R A ∧ IsLocalization M (ResidueField S) ∧
        ∃ e : (A ⧸ Ideal.comap (algebraMap A S) (maximalIdeal S)) ≃ₐ[R] B,
          ((algebraMap B (ResidueField S)).comp e.toRingHom).comp
              (Ideal.Quotient.mk (Ideal.comap (algebraMap A S) (maximalIdeal S))) =
            (residue S).comp (algebraMap A S) := by
  -- First lift the finite-type witness subalgebra from the residue field back into `S`.
  obtain ⟨A, B, M, hAft, hloc, himage⟩ :=
    exists_lifted_finiteType_subalgebra_with_image_eq (R := R) (S := S) f hfS hfκ h
  -- Then the quotient-by-the-contracted-maximal-ideal description is exactly the restricted
  -- first isomorphism theorem for that residue map.
  have hκ : algebraMap R (ResidueField S) = (residue S).comp (algebraMap R S) := by
    simpa [hfS] using hfκ
  obtain ⟨e, he⟩ :=
    lifted_subalgebra_quotient_equiv (R := R) (S := S) hκ A B himage
  exact ⟨A, B, M, hAft, hloc, e, he⟩

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: a subalgebra of a field with a localization witness already has
the ambient field as its fraction ring. -/
private theorem isFractionRing_of_field_localization {K : Type*} [Field K] [Algebra R K]
    (B : Subalgebra R K) (M : Submonoid B) [IsLocalization M K] :
    IsFractionRing B K := by
  -- Express each element of the localization as a quotient of elements of `B`.
  refine IsFractionRing.of_field (R := B) (K := K) fun z ↦ ?_
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj M z
  refine ⟨x, y, ?_⟩
  apply (eq_div_iff (IsLocalization.map_units K y).ne_zero).2
  simpa using hxy

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: the fraction-ring lift of an algebra equivalence commutes with the
canonical maps from the source quotient rings. -/
private theorem fraction_ring_algEquivOfAlgEquiv_comp_algebraMap
    [Algebra R S] [Algebra R (ResidueField S)]
    (A : Subalgebra R S) (B : Subalgebra R (ResidueField S)) (p : Ideal A) [p.IsPrime]
    [IsFractionRing B (ResidueField S)]
    (e : (A ⧸ p) ≃ₐ[R] B) :
    let eκ : p.ResidueField ≃ₐ[R] ResidueField S := IsFractionRing.algEquivOfAlgEquiv e
    eκ.toRingHom.comp (algebraMap (A ⧸ p) p.ResidueField) =
      (algebraMap B (ResidueField S)).comp e.toRingHom := by
  let eκ : p.ResidueField ≃ₐ[R] ResidueField S := IsFractionRing.algEquivOfAlgEquiv e
  -- The fraction-ring equivalence is characterized by its action on quotient classes.
  refine RingHom.ext fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simpa [eκ] using
    IsFractionRing.algEquivOfAlgEquiv_algebraMap
      (R := R) (A := A ⧸ p) (B := B) (K := p.ResidueField) (L := ResidueField S) e
      (Ideal.Quotient.mk p a)

omit [IsArtinianRing S] in
/-- Helper for Lemma 10.54.4: once the lifted quotient `A / p` identifies with a residue-field
subalgebra `B`, fraction-field uniqueness identifies `κ(p)` with the residue field of `S`. -/
private theorem lifted_quotient_residueField_equiv
    [Algebra R S] [Algebra R (ResidueField S)]
    (A : Subalgebra R S) (B : Subalgebra R (ResidueField S)) (M : Submonoid B)
    [IsLocalization M (ResidueField S)]
    (p : Ideal A) [p.IsPrime] (e : (A ⧸ p) ≃ₐ[R] B) :
    ∃ eκ : p.ResidueField ≃ₐ[R] ResidueField S,
      eκ.toRingHom.comp (algebraMap (A ⧸ p) p.ResidueField) =
        (algebraMap B (ResidueField S)).comp e.toRingHom := by
  letI : IsFractionRing B (ResidueField S) :=
    isFractionRing_of_field_localization (R := R) (B := B) (K := ResidueField S) M
  let eκ : p.ResidueField ≃ₐ[R] ResidueField S := IsFractionRing.algEquivOfAlgEquiv e
  -- The localization witness upgrades the quotient equivalence to the residue-field level.
  refine ⟨eκ, ?_⟩
  simpa [eκ] using
    fraction_ring_algEquivOfAlgEquiv_comp_algebraMap
      (R := R) (S := S) A B p e

/-- Helper for Lemma 10.54.4: a local ring is canonically the localization at the complement of
its maximal ideal. -/
private noncomputable abbrev localization_at_maximal_ringEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    Localization.AtPrime (maximalIdeal A) ≃ₐ[A] A := by
  have h_units : (maximalIdeal A).primeCompl ≤ IsUnit.submonoid A := by
    intro x hx
    -- Outside the maximal ideal, a local-ring element is a unit.
    simpa [Ideal.mem_primeCompl_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Classical.not_not] using hx
  letI : IsLocalization (maximalIdeal A).primeCompl A := IsLocalization.self h_units
  exact IsLocalization.algEquiv (maximalIdeal A).primeCompl
    (Localization.AtPrime (maximalIdeal A)) A

/-- Helper for Lemma 10.54.4: the residue field at the maximal ideal agrees with the canonical
local-ring residue field. -/
private noncomputable abbrev maximalIdealResidueFieldEquiv
    (A : Type*) [CommRing A] [IsLocalRing A] :
    (maximalIdeal A).ResidueField ≃+* ResidueField A :=
  (RingEquiv.ofBijective
    (show ResidueField A →+* (maximalIdeal A).ResidueField from
      algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField)
    (Ideal.bijective_algebraMap_quotient_residueField (maximalIdeal A))).symm

/-- Helper for Lemma 10.54.4: the maximal-ideal residue-field identification sends the quotient
class of `a` to the usual residue of `a`. -/
private theorem maximalIdealResidueFieldEquiv_apply_algebraMap
    (A : Type*) [CommRing A] [IsLocalRing A] (a : A) :
    maximalIdealResidueFieldEquiv A (algebraMap A (maximalIdeal A).ResidueField a) =
      residue A a := by
  rw [show algebraMap A (maximalIdeal A).ResidueField a =
      (show ResidueField A →+* (maximalIdeal A).ResidueField from
        algebraMap (A ⧸ maximalIdeal A) (maximalIdeal A).ResidueField) (residue A a) by rfl]
  exact (maximalIdealResidueFieldEquiv A).apply_symm_apply (residue A a)

-- Proof sketch: the forward implication is stability of essential finite type under composition,
-- applied to the essentially finite type residue map. For the reverse implication, present
-- `ResidueField S` as a localization of a finite type `R`-algebra, lift the chosen generators to
-- `S`, form the induced finite type subalgebra `A ⊆ S`, and apply part (1) to the local map
-- `A_(A ∩ maximalIdeal S) → S`.
/-- Lemma 10.54.4 (3): for a ring map `R → S` with `S` an Artinian local ring, the map is
essentially of finite type if and only if the induced map to the residue field of `S` is
essentially of finite type. -/
@[stacks 07DT]
theorem essFiniteType_iff_essFiniteType_residue (f : R →+* S) :
    f.EssFiniteType ↔ ((residue S).comp f).EssFiniteType := by
  constructor
  · intro hf
    -- The residue map is essentially finite type, so composition preserves the property.
    exact RingHom.EssFiniteType.comp hf residue_essFiniteType
  · intro h
    classical
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R (ResidueField S) := (((residue S).comp f).toAlgebra)
    have hfS : algebraMap R S = f := rfl
    have hfκ : algebraMap R (ResidueField S) = (residue S).comp f := rfl
    obtain ⟨A, B, M, hAft, hloc, e, he⟩ :=
      exists_lifted_finiteType_subalgebra_with_quotient_equiv
        (R := R) (S := S) f hfS hfκ h
    let p : Ideal A := Ideal.comap (algebraMap A S) (maximalIdeal S)
    haveI : p.IsPrime := by
      -- The contracted maximal ideal is prime.
      dsimp [p]
      infer_instance
    have he' :
        ((algebraMap B (ResidueField S)).comp e.toRingHom).comp (Ideal.Quotient.mk p) =
          (residue S).comp (algebraMap A S) := by
      simpa [p] using he
    obtain ⟨eκ, heκ⟩ :=
      lifted_quotient_residueField_equiv
        (R := R) (S := S) A B M (p := p) (by simpa [p] using e)
    let ψ₀ : Localization.AtPrime p →+* Localization.AtPrime (maximalIdeal S) :=
      Localization.localRingHom p (maximalIdeal S) (algebraMap A S) rfl
    letI : IsLocalHom (localization_at_maximal_ringEquiv S).toRingHom :=
      Function.Surjective.isLocalHom _ (localization_at_maximal_ringEquiv S).surjective
    let ψ : Localization.AtPrime p →+* S :=
      (localization_at_maximal_ringEquiv S).toRingHom.comp ψ₀
    letI : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
    have hψcomp : ψ.comp (algebraMap A (Localization.AtPrime p)) = algebraMap A S := by
      -- The local map extends the inclusion `A ↪ S` after identifying `S_m` with `S`.
      ext a
      change
        localization_at_maximal_ringEquiv S
            (ψ₀ (algebraMap A (Localization.AtPrime p) a)) =
          algebraMap A S a
      rw [Localization.localRingHom_to_map]
      simpa [ψ₀] using (localization_at_maximal_ringEquiv S).commutes (algebraMap A S a)
    have heκ_apply :
        ∀ a : A, eκ (algebraMap A p.ResidueField a) = residue S (algebraMap A S a) := by
      intro a
      -- Compare both sides on the quotient class of `a`.
      calc
        eκ (algebraMap A p.ResidueField a)
            = eκ (algebraMap (A ⧸ p) p.ResidueField (Ideal.Quotient.mk p a)) := by
                rw [Ideal.algebraMap_quotient_residueField_mk]
        _ = algebraMap B (ResidueField S) (e (Ideal.Quotient.mk p a)) := by
              exact congrArg (fun g : A ⧸ p →+* ResidueField S ↦ g (Ideal.Quotient.mk p a)) heκ
        _ = residue S (algebraMap A S a) := by
              exact congrArg (fun g : A →+* ResidueField S ↦ g a) he'
    have hresidue_map : ResidueField.map ψ = eκ.toRingHom := by
      -- Route correction: identify the residue-field map by checking it on `A`.
      apply Ideal.ResidueField.ringHom_ext
      ext a
      change
        ResidueField.map ψ (residue (Localization.AtPrime p) (algebraMap A (Localization.AtPrime p) a)) =
          eκ (algebraMap A p.ResidueField a)
      rw [IsLocalRing.ResidueField.map_residue]
      rw [show ψ (algebraMap A (Localization.AtPrime p) a) = algebraMap A S a by
          exact congrArg (fun g : A →+* S ↦ g a) hψcomp]
      exact (heκ_apply a).symm
    have hψ_residue_finite : ((residue S).comp ψ).Finite := by
      -- The residue-field map of `ψ` is an isomorphism, so the composite residue map is finite.
      rw [← IsLocalRing.ResidueField.map_comp_residue ψ, hresidue_map]
      exact RingHom.Finite.comp
        (RingHom.Finite.of_surjective _ eκ.surjective)
        (residue_finite (S := Localization.AtPrime p))
    have hψ_finite : ψ.Finite :=
      (finite_iff_finite_residue (R := Localization.AtPrime p) (S := S) ψ).2 hψ_residue_finite
    have hA_loc_ess :
        (algebraMap A (Localization.AtPrime p)).EssFiniteType := by
      -- Localizations are essentially finite type over the source ring.
      rw [RingHom.essFiniteType_algebraMap]
      exact Algebra.EssFiniteType.of_isLocalization
        (R := A) (S := Localization.AtPrime p) p.primeCompl
    have hAS_ess : (algebraMap A S).EssFiniteType := by
      -- The map `A → S` factors through the finite local map `ψ`.
      rw [← hψcomp]
      exact RingHom.EssFiniteType.comp hA_loc_ess hψ_finite.to_finiteType.essFiniteType
    have hfinal : (f.comp (RingHom.id R)).EssFiniteType := by
      -- Compose the finite-type map `R → A` with the essentially finite-type map `A → S`.
      have hRA : (algebraMap R A).FiniteType := RingHom.finiteType_algebraMap.mpr hAft
      have hcomp :
          ((algebraMap A S).comp (algebraMap R A)).EssFiniteType :=
        RingHom.EssFiniteType.comp hRA.essFiniteType hAS_ess
      simpa [hfS, Subalgebra.algebraMap_eq] using hcomp
    simpa using RingHom.EssFiniteType.of_comp (RingHom.id R) hfinal

end
