import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_136_1_Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped TensorProduct
open Polynomial

universe u

namespace Polynomial

section

variable {A : Type u} [CommRing A]

/-- Helper for Chap10 Lemma 10 136 14: the one-variable presentation map for an adjoining-root
quotient is surjective. -/
private lemma adjoinRoot_unitAlgHom_surjective (P : A[X]) :
    Function.Surjective (((AdjoinRoot.mkₐ P).comp (MvPolynomial.pUnitAlgEquiv A).toAlgHom) :
      MvPolynomial Unit A →ₐ[A] AdjoinRoot P) := by
  let e : MvPolynomial Unit A ≃ₐ[A] A[X] := MvPolynomial.pUnitAlgEquiv A
  intro x
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective x
  refine ⟨e.symm p, ?_⟩
  change AdjoinRoot.mk P (e (e.symm p)) = x
  rw [AlgEquiv.apply_symm_apply]
  exact hp

/-- Helper for Chap10 Lemma 10 136 14: the transported single relation cuts out the same
principal ideal as the original adjoining-root relation. -/
private lemma mem_span_adjoinRoot_unit_relation_iff (P : A[X]) (x : MvPolynomial Unit A) :
    x ∈ Ideal.span ({(MvPolynomial.pUnitAlgEquiv A).symm P} : Set (MvPolynomial Unit A)) ↔
      (MvPolynomial.pUnitAlgEquiv A) x ∈ Ideal.span ({P} : Set A[X]) := by
  let e : MvPolynomial Unit A ≃ₐ[A] A[X] := MvPolynomial.pUnitAlgEquiv A
  have hmap : Ideal.map (e : MvPolynomial Unit A →+* A[X])
      (Ideal.span ({e.symm P} : Set (MvPolynomial Unit A))) = Ideal.span ({P} : Set A[X]) := by
    rw [Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z ↦ Ideal.span ({z} : Set A[X])) (AlgEquiv.apply_symm_apply e P)
  constructor
  · intro hx
    have hxmap : e x ∈ Ideal.map (e : MvPolynomial Unit A →+* A[X])
        (Ideal.span ({e.symm P} : Set (MvPolynomial Unit A))) :=
      Ideal.mem_map_of_mem _ hx
    simpa [hmap] using hxmap
  · intro hx
    have hxcomap : x ∈ Ideal.comap (e : MvPolynomial Unit A →+* A[X])
        (Ideal.span ({P} : Set A[X])) := hx
    have hcomap : Ideal.comap (e : MvPolynomial Unit A →+* A[X])
        (Ideal.map (e : MvPolynomial Unit A →+* A[X])
          (Ideal.span ({e.symm P} : Set (MvPolynomial Unit A)))) =
        Ideal.span ({e.symm P} : Set (MvPolynomial Unit A)) :=
      Ideal.comap_map_of_bijective (e : MvPolynomial Unit A →+* A[X]) e.bijective
    rw [← hmap] at hxcomap
    rwa [hcomap] at hxcomap

/-- Helper for Chap10 Lemma 10 136 14: the kernel of the one-variable presentation map is the
span of the transported adjoining-root relation. -/
private lemma adjoinRoot_unitAlgHom_ker (P : A[X]) :
    RingHom.ker ((((AdjoinRoot.mkₐ P).comp (MvPolynomial.pUnitAlgEquiv A).toAlgHom) :
      MvPolynomial Unit A →ₐ[A] AdjoinRoot P).toRingHom) =
      Ideal.span ({(MvPolynomial.pUnitAlgEquiv A).symm P} : Set (MvPolynomial Unit A)) := by
  ext x
  rw [RingHom.mem_ker]
  change AdjoinRoot.mk P ((MvPolynomial.pUnitAlgEquiv A) x) = 0 ↔
    x ∈ Ideal.span ({(MvPolynomial.pUnitAlgEquiv A).symm P} : Set (MvPolynomial Unit A))
  rw [AdjoinRoot.mk_eq_zero, ← Ideal.mem_span_singleton]
  exact (mem_span_adjoinRoot_unit_relation_iff P x).symm

/-- Helper for Chap10 Lemma 10 136 14: the one-variable presentation relation has the expected
kernel for the adjoining-root quotient. -/
private lemma adjoinRootPresentation_span_range_relation_eq_ker (P : A[X]) :
    Ideal.span (Set.range (fun _ : Unit ↦
      ((MvPolynomial.pUnitAlgEquiv A).symm P : MvPolynomial Unit A))) =
    (Algebra.Generators.ofAlgHom
      ((AdjoinRoot.mkₐ P).comp (MvPolynomial.pUnitAlgEquiv A).toAlgHom)
      (adjoinRoot_unitAlgHom_surjective P)).ker := by
  simp only [Set.range_const]
  rw [Algebra.Generators.ker_eq_ker_aeval_val]
  let f : MvPolynomial Unit A →ₐ[A] AdjoinRoot P :=
    (AdjoinRoot.mkₐ P).comp (MvPolynomial.pUnitAlgEquiv A).toAlgHom
  change Ideal.span ({(MvPolynomial.pUnitAlgEquiv A).symm P} : Set (MvPolynomial Unit A)) =
    RingHom.ker (MvPolynomial.aeval (f ∘ MvPolynomial.X)).toRingHom
  have hf : MvPolynomial.aeval (f ∘ MvPolynomial.X) = f := by
    ext i
    simp [f]
  rw [hf]
  exact (adjoinRoot_unitAlgHom_ker P).symm

/-- Helper for Chap10 Lemma 10 136 14: adjoining a root has a one-generator, one-relation
presentation. -/
private noncomputable def adjoinRootPresentation (P : A[X]) :
    Algebra.Presentation A (AdjoinRoot P) Unit Unit where
  toGenerators := Algebra.Generators.ofAlgHom
    ((AdjoinRoot.mkₐ P).comp (MvPolynomial.pUnitAlgEquiv A).toAlgHom)
    (adjoinRoot_unitAlgHom_surjective P)
  relation _ := (MvPolynomial.pUnitAlgEquiv A).symm P
  span_range_relation_eq_ker := adjoinRootPresentation_span_range_relation_eq_ker P

/-- Helper for Chap10 Lemma 10 136 14: a field is a global complete intersection over itself. -/
private lemma field_isGlobalCompleteIntersection (K : Type u) [Field K] :
    IsGlobalCompleteIntersection K K := by
  let Pempty : Algebra.Presentation K K PEmpty.{1} PEmpty.{1} := Algebra.Presentation.id K
  let e : Fin 0 ≃ PEmpty.{1} := Equiv.equivPEmpty (Fin 0)
  let P : Algebra.Presentation K K (Fin 0) (Fin 0) := Pempty.reindex e e
  refine ⟨Or.inr ⟨0, 0, P, ?_⟩⟩
  simpa [P, Pempty, e, Algebra.Presentation.dimension] using ringKrullDim_eq_zero_of_field K

/-- Helper for Chap10 Lemma 10 136 14: the identity-map fiber is a local complete intersection. -/
private lemma tensorProduct_right_self_isLocalCompleteIntersection
    {K : Type u} [Field K] [Algebra A K] :
    IsLocalCompleteIntersection K (K ⊗[A] A) := by
  let e : K ⊗[A] A ≃ₐ[K] K := Algebra.TensorProduct.rid A K K
  have hK : IsGlobalCompleteIntersection K K := field_isGlobalCompleteIntersection K
  letI : IsGlobalCompleteIntersection K (K ⊗[A] A) :=
    IsGlobalCompleteIntersection.of_algEquiv hK e.symm
  infer_instance

/-- Helper for Chap10 Lemma 10 136 14: a finite algebra with a one-generator, one-relation
presentation over a field is a global complete intersection. -/
private lemma isGlobalCompleteIntersection_of_unitPresentation_finite
    {K S : Type u} [Field K] [CommRing S] [Algebra K S] [Module.Finite K S]
    (P : Algebra.Presentation K S Unit Unit) :
    IsGlobalCompleteIntersection K S := by
  by_cases hsub : Subsingleton S
  · letI : Subsingleton S := hsub
    infer_instance
  · letI : Nontrivial S := not_subsingleton_iff_nontrivial.mp hsub
    letI : Algebra.FiniteType K S := Module.Finite.finiteType S
    let Pfin : Algebra.Presentation K S (Fin 1) (Fin 1) := P.reindex finOneEquiv finOneEquiv
    have hdim : Pfin.dimension = 0 := by
      calc
        Pfin.dimension = P.dimension := by
          simpa [Pfin] using P.dimension_reindex finOneEquiv finOneEquiv
        _ = 0 := by
          simp [Algebra.Presentation.dimension]
    have hle : Ring.KrullDimLE 0 S :=
      (Module.finite_iff_krullDimLE_zero K S).mp inferInstance
    have hkrull : ringKrullDim S = 0 := ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle
    refine ⟨Or.inr ⟨1, 1, Pfin, ?_⟩⟩
    simpa [hdim] using hkrull

/-- Helper for Chap10 Lemma 10 136 14: every residue-field fiber of a monic adjoining-root
extension is a local complete intersection. -/
private lemma adjoinRoot_fiber_isLocalCompleteIntersection {P : A[X]} (hP : P.Monic)
    (q : PrimeSpectrum A) :
    IsLocalCompleteIntersection q.asIdeal.ResidueField (q.asIdeal.Fiber (AdjoinRoot P)) := by
  let K := q.asIdeal.ResidueField
  letI : Module.Finite A (AdjoinRoot P) := hP.finite_adjoinRoot
  let Pbase : Algebra.Presentation K (q.asIdeal.Fiber (AdjoinRoot P)) Unit Unit :=
    (adjoinRootPresentation P).baseChange K
  have hfinite : Module.Finite K (q.asIdeal.Fiber (AdjoinRoot P)) := inferInstance
  letI : Module.Finite K (q.asIdeal.Fiber (AdjoinRoot P)) := hfinite
  letI : IsGlobalCompleteIntersection K (q.asIdeal.Fiber (AdjoinRoot P)) :=
    isGlobalCompleteIntersection_of_unitPresentation_finite Pbase
  infer_instance

/-- Helper for Chap10 Lemma 10 136 14: the identity algebra map has an empty square
presentation. -/
private noncomputable def identitySquarePresentation (A : Type u) [CommRing A] :
    Algebra.Presentation A A (Fin 0) (Fin 0) :=
  let Pempty : Algebra.Presentation A A PEmpty.{1} PEmpty.{1} := Algebra.Presentation.id A
  let e : Fin 0 ≃ PEmpty.{1} := Equiv.equivPEmpty (Fin 0)
  Pempty.reindex e e

/-- Helper for Chap10 Lemma 10 136 14: a monic adjoining-root extension has a square
presentation. -/
private noncomputable def monicAdjoinRoot_squarePresentation (P : A[X]) :
    Algebra.Presentation A (AdjoinRoot P) (Fin 1) (Fin 1) :=
  (adjoinRootPresentation P).reindex finOneEquiv finOneEquiv

/-- Helper for Chap10 Lemma 10 136 14: a finite algebra with a square presentation has global
complete-intersection fibers. -/
private lemma fiber_isGlobalCompleteIntersection_of_squarePresentation_finite
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    {n : ℕ} (P : Algebra.Presentation R S (Fin n) (Fin n)) (p : PrimeSpectrum R) :
    IsGlobalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
  let K := p.asIdeal.ResidueField
  by_cases hsub : Subsingleton (p.asIdeal.Fiber S)
  · letI : Subsingleton (p.asIdeal.Fiber S) := hsub
    infer_instance
  · letI : Nontrivial (p.asIdeal.Fiber S) := not_subsingleton_iff_nontrivial.mp hsub
    have hfinite : Module.Finite K (p.asIdeal.Fiber S) := inferInstance
    letI : Module.Finite K (p.asIdeal.Fiber S) := hfinite
    letI : Algebra.FiniteType K (p.asIdeal.Fiber S) :=
      Module.Finite.finiteType (p.asIdeal.Fiber S)
    let Pbase : Algebra.Presentation K (p.asIdeal.Fiber S) (Fin n) (Fin n) := P.baseChange K
    have hdim : Pbase.dimension = 0 := by
      simp [Algebra.Presentation.dimension]
    have hle : Ring.KrullDimLE 0 (p.asIdeal.Fiber S) :=
      (Module.finite_iff_krullDimLE_zero K (p.asIdeal.Fiber S)).mp inferInstance
    have hkrull : ringKrullDim (p.asIdeal.Fiber S) = 0 :=
      ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hle
    refine ⟨Or.inr ⟨n, n, Pbase, ?_⟩⟩
    simpa [hdim] using hkrull

/-- Helper for Chap10 Lemma 10 136 14: a finite free algebra with a square presentation is
syntomic. -/
private lemma syntomic_of_squarePresentation_free
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S]
    {n : ℕ} (P : Algebra.Presentation R S (Fin n) (Fin n)) :
    (algebraMap R S).Syntomic := by
  refine ⟨?_, ?_, ?_⟩
  · rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_projective
  · rw [RingHom.finitePresentation_algebraMap]
    exact P.finitePresentation_of_isFinite
  · rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap]
    intro p
    letI : IsGlobalCompleteIntersection p.asIdeal.ResidueField (p.asIdeal.Fiber S) :=
      fiber_isGlobalCompleteIntersection_of_squarePresentation_finite P p
    infer_instance

/-- Helper for Chap10 Lemma 10 136 14: adjoining one root of a monic polynomial is syntomic. -/
private lemma monicAdjoinRoot_syntomic [Nontrivial A] {P : A[X]} (hP : P.Monic) :
    (algebraMap A (AdjoinRoot P)).Syntomic := by
  -- The one-root extension is free, hence flat, and has the standard finite presentation.
  refine ⟨?_, ?_, ?_⟩
  · rw [RingHom.flat_algebraMap_iff]
    letI : Module.Free A (AdjoinRoot P) := hP.free_adjoinRoot
    exact Module.Flat.of_projective
  · rw [RingHom.finitePresentation_algebraMap]
    exact AdjoinRoot.finitePresentation P
  · -- Each residue-field fiber is again an `AdjoinRoot`, hence a local complete intersection.
    rw [RingHom.HasLocalCompleteIntersectionFibers, toAlgebra_algebraMap]
    intro q
    exact adjoinRoot_fiber_isLocalCompleteIntersection hP q

/-- Helper for Chap10 Lemma 10 136 14: adjoining one root of a monic polynomial is faithfully
flat. -/
private lemma monicAdjoinRoot_faithfullyFlat [Nontrivial A] {P : A[X]} (hP : P.Monic)
    (hP_nonunit : ¬ IsUnit P) :
    (algebraMap A (AdjoinRoot P)).FaithfullyFlat := by
  -- A nonzero monic quotient is a nontrivial free module, hence faithfully flat.
  rw [RingHom.faithfullyFlat_algebraMap_iff]
  letI : Module.Free A (AdjoinRoot P) := hP.free_adjoinRoot
  have hnontrivial : Nontrivial (AdjoinRoot P) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    simpa using hP_nonunit
  letI : Nontrivial (AdjoinRoot P) := hnontrivial
  infer_instance

/-- Helper for Chap10 Lemma 10 136 14: the finite-free splitting extension from mathlib's
`Monic.exists_splits_map` can be chosen syntomic and faithfully flat. -/
private lemma Monic.exists_syntomic_finiteFree_faithfullyFlat_splits_map
    [Nontrivial A] {P : A[X]} (hP : P.Monic) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A')
      (n : ℕ) (_ : Algebra.Presentation A A' (Fin n) (Fin n))
      (_ : (algebraMap A A').Syntomic)
      (_ : Module.Free A A') (_ : Module.Finite A A')
      (_ : (algebraMap A A').FaithfullyFlat) (_ : Nontrivial A'),
      (P.map (algebraMap A A')).Splits := by
  -- Follow mathlib's strong induction on the degree, adding syntomic and faithful-flat data to
  -- the usual finite-free splitting tower.
  induction hn : P.natDegree using Nat.strong_induction_on generalizing A with
  | h n IH =>
    by_cases hpu : IsUnit P
    · -- The unit monic polynomial is `1`, so the identity extension already splits it.
      obtain rfl := hP.eq_one_of_isUnit hpu
      let Pid := identitySquarePresentation A
      have hSynId : (algebraMap A A).Syntomic :=
        syntomic_of_squarePresentation_free Pid
      refine ⟨A, inferInstance, inferInstance, 0, Pid, hSynId, inferInstance, inferInstance, ?_,
        inferInstance, ?_⟩
      · simpa using
          (RingHom.FaithfullyFlat.of_bijective (f := RingHom.id A) Function.bijective_id)
      · simp
    -- Adjoin one root, split off the corresponding linear factor, and recurse on the monic
    -- quotient of smaller degree.
    obtain ⟨q, hq⟩ : X - C (AdjoinRoot.root P) ∣ P.map (algebraMap _ _) := by
      simp [dvd_iff_isRoot, -AdjoinRoot.algebraMap_eq]
    have hqm : q.Monic := .of_mul_monic_left (monic_X_sub_C (.root _)) (hq ▸ hP.map _)
    letI : Module.Free A (AdjoinRoot P) := hP.free_adjoinRoot
    letI : Module.Finite A (AdjoinRoot P) := hP.finite_adjoinRoot
    have hAR_nontrivial : Nontrivial (AdjoinRoot P) := by
      refine Ideal.Quotient.nontrivial_iff.mpr ?_
      simpa using hpu
    letI : Nontrivial (AdjoinRoot P) := hAR_nontrivial
    have hq_degree_lt : q.natDegree < n := by
      rw [← hn, ← hP.natDegree_map (algebraMap A (AdjoinRoot P)), hq,
        Monic.natDegree_mul (monic_X_sub_C _) hqm]
      simp
    obtain ⟨S, hSring, hSalg, m, Pstep, hSynS, hFreeS, hFiniteS, hffS, hNontrivS, hSplitS⟩ :=
      IH _ hq_degree_lt hqm rfl
    algebraize [(algebraMap (AdjoinRoot P) S).comp (algebraMap A (AdjoinRoot P))]
    have hcompAlg :
        (algebraMap (AdjoinRoot P) S).comp (algebraMap A (AdjoinRoot P)) =
          algebraMap A S :=
      IsScalarTower.algebraMap_eq A (AdjoinRoot P) S
    -- Compose the one-root stage with the recursive syntomic stage, and compose the finite-free
    -- and faithfully-flat module data through the same tower.
    let Proot := monicAdjoinRoot_squarePresentation P
    let Pcomp₀ : Algebra.Presentation A S (Fin m ⊕ Fin 1) (Fin m ⊕ Fin 1) :=
      Pstep.comp Proot
    let Pcomp : Algebra.Presentation A S (Fin (m + 1)) (Fin (m + 1)) :=
      Pcomp₀.reindex finSumFinEquiv.symm finSumFinEquiv.symm
    have hFree : Module.Free A S := Module.Free.trans (R := A) (S := AdjoinRoot P) (M := S)
    have hFinite : Module.Finite A S := Module.Finite.trans (R := A) (AdjoinRoot P) S
    have hSyn : (algebraMap A S).Syntomic := syntomic_of_squarePresentation_free Pcomp
    have hffRoot : (algebraMap A (AdjoinRoot P)).FaithfullyFlat :=
      monicAdjoinRoot_faithfullyFlat hP hpu
    have hff : (algebraMap A S).FaithfullyFlat := by
      simpa [← hcompAlg] using RingHom.FaithfullyFlat.stableUnderComposition _ _ hffRoot hffS
    refine ⟨S, hSring, inferInstance, m + 1, Pcomp, hSyn, hFree, hFinite, hff, hNontrivS, ?_⟩
    -- Finally transport the recursive splitting statement across the polynomial map composition.
    rw [← hcompAlg, ← Polynomial.map_map, hq, Polynomial.map_mul]
    have hSplitLinear : ((X - C (AdjoinRoot.root P)).map (algebraMap (AdjoinRoot P) S)).Splits := by
      simp
    exact .mul hSplitLinear hSplitS

/- Domain-style sampling:
* primary domain: splitting monic polynomials after finite flat base change in commutative algebra;
* sampled owner declarations:
  `Polynomial.Monic.exists_splits_map`,
  `Polynomial.Splits`,
  `Polynomial.Splits.eq_prod_roots_of_monic`,
  `RingHom.Syntomic`;
* best owner abstraction:
  the extension itself remains source-facing existential data, while the splitting conclusion
  should use the canonical owner `Polynomial.Splits`; the explicit linear-factor product is
  derived API from that owner for monic polynomials;
* primitive vs. derived:
  primitive data are the extension ring `A'` and its syntomic / finite free / faithfully flat
  structure over `A`; a chosen family of roots indexed by `Fin P.natDegree` is derived packaging
  and should not be primitive public output.
-/

-- Proof sketch: base change the universal elementary-symmetric factorization ring of Example
-- `10.136.8` along the map sending the elementary-symmetric coefficients to the coefficients of
-- `P`. The resulting algebra is finite free and faithfully flat by base change, and it is
-- syntomic by Lemma `10.136.13`. Its tautological roots show that
-- `P.map (algebraMap A A')` splits; the explicit linear-factor product is then derived from the
-- canonical owner lemma `Polynomial.Splits.eq_prod_roots_of_monic`.
/-- Chap10 Lemma 10 136 14: a monic polynomial over `A` splits after a syntomic finite free
faithfully flat extension of `A`. -/
@[stacks 03HS]
theorem exists_syntomic_finiteFree_faithfullyFlat_split_extension_of_monic
    (P : A[X]) (hP : P.Monic) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : (algebraMap A A').Syntomic)
      (_ : Module.Free A A') (_ : Module.Finite A A')
      (_ : (algebraMap A A').FaithfullyFlat),
      (P.map (algebraMap A A')).Splits := by
  -- If the base is the zero ring, the identity extension is enough because every mapped
  -- polynomial is zero and `0` splits by convention.
  by_cases hsub : Subsingleton A
  · letI : Subsingleton A := hsub
    refine ⟨A, inferInstance, inferInstance, ?_, inferInstance, inferInstance, ?_, ?_⟩
    · exact syntomic_of_squarePresentation_free (identitySquarePresentation A)
    · simpa using
        (RingHom.FaithfullyFlat.of_bijective (f := RingHom.id A) Function.bijective_id)
    · have hzero : P.map (algebraMap A A) = 0 := by
        ext n
        exact Subsingleton.elim _ _
      rw [hzero]
      exact Polynomial.Splits.zero
  · -- Otherwise use the strengthened splitting-tower induction and forget only the auxiliary
    -- nontriviality witness in its output.
    letI : Nontrivial A := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨A', hA'comm, hA'alg, _n, _Ppres, hSyn, hFree, hFinite, hff, _hNontriv, hsplit⟩ :=
      hP.exists_syntomic_finiteFree_faithfullyFlat_splits_map
    exact ⟨A', hA'comm, hA'alg, hSyn, hFree, hFinite, hff, hsplit⟩

end

end Polynomial
