import Mathlib
import StacksProject_2024.Chap10.Lemma_10_112_7

-- Acyclic support for the inequality part of Lemma 10.113.1.

noncomputable section

universe u v

open PrimeSpectrum
open scoped TensorProduct

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S]

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: private bridge from an injective domain map to the
natural-number transcendence degree of the induced fraction-field extension. -/
private noncomputable abbrev fractionRingTrdeg
    (hinj : Function.Injective (algebraMap R S)) : ℕ :=
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  Cardinal.toNat (trdeg (FractionRing R) (FractionRing S))

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the local fraction-field transcendence bridge unfolds by
installing the faithful scalar action supplied by injectivity. -/
private lemma fractionRingTrdeg_eq_cardinalToNat_trdeg
    (hinj : Function.Injective (algebraMap R S)) :
    Algebra.fractionRingTrdeg (R := R) (S := S) hinj =
      let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
      Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  -- The bridge only installs the faithful scalar action needed for the fraction-field algebra.
  rfl

end

end Algebra

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
  [Algebra R S] [Algebra (FractionRing R) (FractionRing S)]
  [IsScalarTower R (FractionRing R) (FractionRing S)]

/-- Helper for Lemma 10.113.1: two successive height/residue-field inequalities combine by
canceling the intermediate height term. -/
private lemma towerStep_primeHeightResidueFieldTrdeg_le
    {heightR heightT heightS genericRT genericTS residueRT residueTS : ℕ}
    (hRT : heightT + residueRT ≤ heightR + genericRT)
    (hTS : heightS + residueTS ≤ heightT + genericTS) :
    heightS + (residueRT + residueTS) ≤ heightR + (genericRT + genericTS) := by
  -- Add the two tower-step inequalities and cancel the middle height contribution.
  omega

/-- Helper for Lemma 10.113.1: an essentially finite type field extension has finite
transcendence degree. -/
private lemma trdeg_lt_aleph0_of_essFiniteType_field
    {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L] :
    Algebra.trdeg K L < Cardinal.aleph0 := by
  -- Choose finitely many field generators and bound the transcendence degree by that finite set.
  obtain ⟨t, ht⟩ := IntermediateField.fg_top K L
  have ht_alg : Algebra.IsAlgebraic (Algebra.adjoin K (t : Set L)) L := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, ht, Algebra.isAlgebraic_iff_isIntegral]
    exact Algebra.isIntegral_of_surjective IntermediateField.topEquiv.surjective
  exact
    lt_of_le_of_lt
      (Algebra.IsAlgebraic.trdeg_le_cardinalMk K (t : Set L))
      (by simpa using t.finite_toSet.lt_aleph0)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the private generic fraction-field transcendence term is
additive across finite-type towers of domains. -/
private lemma fractionRingTrdeg_tower_eq
    {T : Type v} {U : Type v}
    [CommRing T] [CommRing U] [IsDomain T] [IsDomain U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    [Algebra.FiniteType R T] [Algebra.FiniteType T U]
    (hinjRT : Function.Injective (algebraMap R T))
    (hinjTU : Function.Injective (algebraMap T U))
    (hinjRU : Function.Injective (algebraMap R U)) :
    Algebra.fractionRingTrdeg (R := R) (S := U) hinjRU =
      Algebra.fractionRingTrdeg (R := R) (S := T) hinjRT +
        Algebra.fractionRingTrdeg (R := T) (S := U) hinjTU := by
  -- Install the faithful scalar actions needed to use the canonical fraction-field algebra maps.
  let _ : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr hinjRT
  let _ : FaithfulSMul T U := (faithfulSMul_iff_algebraMap_injective T U).mpr hinjTU
  let _ : FaithfulSMul R U := (faithfulSMul_iff_algebraMap_injective R U).mpr hinjRU
  letI : Algebra.EssFiniteType R (FractionRing T) := Algebra.EssFiniteType.comp R T (FractionRing T)
  letI : Algebra.EssFiniteType T (FractionRing U) := Algebra.EssFiniteType.comp T U (FractionRing U)
  letI : Algebra.EssFiniteType R (FractionRing U) := Algebra.EssFiniteType.comp R T (FractionRing U)
  letI : Algebra.EssFiniteType (FractionRing R) (FractionRing T) :=
    Algebra.EssFiniteType.of_comp R (FractionRing R) (FractionRing T)
  letI : Algebra.EssFiniteType (FractionRing T) (FractionRing U) :=
    Algebra.EssFiniteType.of_comp T (FractionRing T) (FractionRing U)
  have hRT_lt :
      Algebra.trdeg (FractionRing R) (FractionRing T) < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field (K := FractionRing R) (L := FractionRing T)
  have hTU_lt :
      Algebra.trdeg (FractionRing T) (FractionRing U) < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field (K := FractionRing T) (L := FractionRing U)
  -- Convert cardinal-valued additivity for fraction fields into the nat-valued private term.
  dsimp [Algebra.fractionRingTrdeg]
  rw [← trdeg_add_eq (R := FractionRing R) (S := FractionRing T) (A := FractionRing U)]
  exact Cardinal.toNat_add hRT_lt hTU_lt

omit [IsDomain R] in
/-- Helper for Lemma 10.113.1: contracting a prime first to an intermediate stage and then to
the base ring agrees with direct contraction to the base. -/
private lemma comap_under_eq_under_in_tower
    {T : Type*} {U : Type*}
    [CommRing T] [CommRing U] [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    (q : PrimeSpectrum U) :
    let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
    qT.asIdeal.under R = q.asIdeal.under R := by
  let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
  ext r
  -- Both contractions test whether the image of `r` lands in `q`, and the scalar tower identifies
  -- the two images in `U`.
  change algebraMap T U (algebraMap R T r) ∈ q.asIdeal ↔ algebraMap R U r ∈ q.asIdeal
  rw [IsScalarTower.algebraMap_apply R T U r]

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: equal base primes give the same residue-field
transcendence-degree term for a fixed lying-over target prime. -/
private lemma residueFieldTrdeg_toNat_eq_of_base_eq
    {A : Type*} [CommRing A] [Algebra R A]
    {p p' : Ideal R} [p.IsPrime] [p'.IsPrime]
    {P : Ideal A} [P.IsPrime] [P.LiesOver p] [P.LiesOver p'] (hp : p = p') :
    Cardinal.toNat (Algebra.trdeg p.ResidueField P.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p'.ResidueField P.ResidueField) := by
  -- After replacing the base prime, proof irrelevance identifies the two residue-field algebra
  -- structures used in the transcendence-degree term.
  cases hp
  rfl

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: with an explicit base prime, residue-field
transcendence degree is additive across a finite-type tower. -/
private lemma residueFieldTrdeg_tower_eq_of_liesOver
    {T : Type v} {U : Type v}
    [CommRing T] [CommRing U] [IsDomain T] [IsDomain U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    [Algebra.FiniteType R T] [Algebra.FiniteType T U]
    {p : Ideal R} [p.IsPrime] (q : PrimeSpectrum U)
    [hmid : (PrimeSpectrum.comap (algebraMap T U) q).asIdeal.LiesOver p]
    [htop : q.asIdeal.LiesOver (PrimeSpectrum.comap (algebraMap T U) q).asIdeal]
    [hcomp : q.asIdeal.LiesOver p] :
    let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
    Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p.ResidueField qT.asIdeal.ResidueField) +
        Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
  let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
  -- Install the finite-type residue-field extensions and the field-map faithful scalar actions
  -- explicitly, avoiding the previous inference-heavy tower search.
  letI : Algebra.EssFiniteType p.ResidueField qT.asIdeal.ResidueField := inferInstance
  letI : Algebra.EssFiniteType qT.asIdeal.ResidueField q.asIdeal.ResidueField := inferInstance
  letI : FaithfulSMul p.ResidueField qT.asIdeal.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective p.ResidueField qT.asIdeal.ResidueField).mpr
      (RingHom.injective (algebraMap p.ResidueField qT.asIdeal.ResidueField))
  letI : FaithfulSMul qT.asIdeal.ResidueField q.asIdeal.ResidueField :=
    (faithfulSMul_iff_algebraMap_injective qT.asIdeal.ResidueField q.asIdeal.ResidueField).mpr
      (RingHom.injective (algebraMap qT.asIdeal.ResidueField q.asIdeal.ResidueField))
  have hbase_lt :
      Algebra.trdeg p.ResidueField qT.asIdeal.ResidueField < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field
      (K := p.ResidueField) (L := qT.asIdeal.ResidueField)
  have htop_lt :
      Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField < Cardinal.aleph0 :=
    trdeg_lt_aleph0_of_essFiniteType_field
      (K := qT.asIdeal.ResidueField) (L := q.asIdeal.ResidueField)
  have hsum :
      Algebra.trdeg p.ResidueField qT.asIdeal.ResidueField +
          Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField =
        Algebra.trdeg p.ResidueField q.asIdeal.ResidueField :=
    trdeg_add_eq
      (R := p.ResidueField) (S := qT.asIdeal.ResidueField)
      (A := q.asIdeal.ResidueField)
  -- Convert cardinal additivity to the natural-number form used by the dimension inequality.
  rw [← hsum, Cardinal.toNat_add hbase_lt htop_lt]

omit [IsDomain R] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: residue-field transcendence degree is additive in a
finite-type tower after contracting the top prime through the intermediate stage. -/
private lemma residueFieldTrdeg_tower_eq
    {T : Type v} {U : Type v}
    [CommRing T] [CommRing U] [IsDomain T] [IsDomain U]
    [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
    [Algebra.FiniteType R T] [Algebra.FiniteType T U]
    (q : PrimeSpectrum U) :
    let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
        Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
  let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T U) q
  let pT : Ideal R := qT.asIdeal.under R
  let p : Ideal R := q.asIdeal.under R
  letI : pT.IsPrime := by
    dsimp [pT]
    infer_instance
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  have hp : pT = p := by
    -- Normalize the two contractions of the top prime to the same ideal of the base ring.
    simpa [pT, p, qT] using
      comap_under_eq_under_in_tower (R := R) (T := T) (U := U) q
  letI : qT.asIdeal.LiesOver pT := ⟨rfl⟩
  letI : q.asIdeal.LiesOver qT.asIdeal := ⟨rfl⟩
  letI : q.asIdeal.LiesOver pT := Ideal.LiesOver.trans q.asIdeal qT.asIdeal pT
  letI : q.asIdeal.LiesOver p := ⟨rfl⟩
  have hbaseTop :
      Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg pT.ResidueField q.asIdeal.ResidueField) := by
    -- Move the top residue-field extension from the direct contraction to the staged contraction.
    exact
      (residueFieldTrdeg_toNat_eq_of_base_eq
        (R := R) (A := U) (p := pT) (p' := p) (P := q.asIdeal) hp).symm
  have htower :
      Cardinal.toNat (Algebra.trdeg pT.ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg pT.ResidueField qT.asIdeal.ResidueField) +
          Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
    -- Apply the no-search tower additivity helper at the staged base prime.
    simpa [qT] using
      residueFieldTrdeg_tower_eq_of_liesOver (R := R) (T := T) (U := U) (p := pT) q
  -- Transport the direct base prime to the staged base prime, then split the tower.
  calc
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
      = Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
          rfl
    _ = Cardinal.toNat (Algebra.trdeg pT.ResidueField q.asIdeal.ResidueField) := hbaseTop
    _ = Cardinal.toNat (Algebra.trdeg pT.ResidueField qT.asIdeal.ResidueField) +
          Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := htower
    _ = Cardinal.toNat
            (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
          Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
            rfl

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Lemma 10.113.1: the structure map into a finite adjoin stage is injective when
the ambient map is injective. -/
private lemma adjoinFinset_algebraMap_injective
    (hinj : Function.Injective (algebraMap R S)) (s : Finset S) :
    Function.Injective (algebraMap R (Algebra.adjoin R (s : Set S))) := by
  -- Compare two stage elements after applying the inclusion into the ambient algebra `S`.
  intro x y hxy
  apply hinj
  change (((algebraMap R (Algebra.adjoin R (s : Set S)) x :
      Algebra.adjoin R (s : Set S)) : S)) =
    (((algebraMap R (Algebra.adjoin R (s : Set S)) y :
      Algebra.adjoin R (s : Set S)) : S))
  simpa using congrArg (fun z : Algebra.adjoin R (s : Set S) ↦ (z : S)) hxy

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Lemma 10.113.1: a finite adjoin stage is finite type over the source ring. -/
private lemma adjoinFinset_finiteType (s : Finset S) :
    Algebra.FiniteType R (Algebra.adjoin R (s : Set S)) := by
  let T : Subalgebra R S := Algebra.adjoin R (s : Set S)
  have hfg : T.FG := by
    -- The stage is generated by exactly the finite set used in its definition.
    exact Subalgebra.fg_def.2 ⟨(s : Set S), s.finite_toSet, rfl⟩
  have hfgTop : (⊤ : Subalgebra R T).FG := (Subalgebra.fg_top T).2 hfg
  have hftTop : Algebra.FiniteType R (⊤ : Subalgebra R T) :=
    (Subalgebra.fg_iff_finiteType (⊤ : Subalgebra R T)).mp hfgTop
  -- Transfer finite type across the canonical equivalence from the top subalgebra to the stage.
  exact Algebra.FiniteType.equiv hftTop Subalgebra.topEquiv

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Lemma 10.113.1: finite adjoin stages over a Noetherian source are Noetherian. -/
private lemma adjoinFinset_isNoetherianRing [IsNoetherianRing R] (s : Finset S) :
    IsNoetherianRing (Algebra.adjoin R (s : Set S)) := by
  let T : Subalgebra R S := Algebra.adjoin R (s : Set S)
  have hfg : T.FG := by
    -- The displayed finite set itself presents the subalgebra as a finite adjoin.
    exact Subalgebra.fg_def.2 ⟨(s : Set S), s.finite_toSet, rfl⟩
  exact isNoetherianRing_of_fg hfg

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: a finite adjoin stage is contained in the stage obtained
by inserting one more generator. -/
private lemma adjoinFinset_le_insert_adjoinFinset [DecidableEq S] (t : Finset S) (x : S) :
    Algebra.adjoin R (t : Set S) ≤
      Algebra.adjoin R (((insert x t : Finset S) : Set S)) := by
  -- The old generating set is a subset of the inserted generating set, so monotonicity of adjoin
  -- gives the inclusion of stages.
  have hsubset : (t : Set S) ⊆ (((insert x t : Finset S) : Set S)) := by
    intro y hy
    exact Finset.mem_insert_of_mem hy
  exact Algebra.adjoin_mono hsubset

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the inserted generator belongs to the inserted finite
adjoin stage. -/
private lemma insertedElement_mem_adjoinFinsetStage [DecidableEq S] (t : Finset S) (x : S) :
    x ∈ Algebra.adjoin R (((insert x t : Finset S) : Set S)) := by
  -- The new element is one of the displayed generators of the inserted stage.
  have hxmem : x ∈ (((insert x t : Finset S) : Set S)) := by
    simp
  exact Algebra.subset_adjoin hxmem

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: after adjoining one new element to a finite stage, the
new stage is generated over the previous stage by that single inserted element. -/
private lemma adjoinSingleton_eq_top_over_adjoinFinsetStage
    [DecidableEq S]
    (t : Finset S) (x : S) :
    let T : Subalgebra R S := Algebra.adjoin R (t : Set S)
    let A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
    let hTA : T ≤ A := adjoinFinset_le_insert_adjoinFinset (R := R) (S := S) t x
    letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
    letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
    let xA : A := ⟨x, insertedElement_mem_adjoinFinsetStage (R := R) (S := S) t x⟩
    Algebra.adjoin T ({xA} : Set A) = ⊤ := by
  classical
  dsimp
  set T : Subalgebra R S := Algebra.adjoin R (t : Set S)
  set A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
  have hTA : T ≤ A := by
    -- Reuse the named inclusion of finite adjoin stages in the local abbreviations.
    simpa [T, A] using adjoinFinset_le_insert_adjoinFinset (R := R) (S := S) t x
  letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
  letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
  have hxA_mem : x ∈ A := by
    -- Package the inserted generator as an element of the new stage.
    simpa [A] using insertedElement_mem_adjoinFinsetStage (R := R) (S := S) t x
  let xA : A := ⟨x, hxA_mem⟩
  apply top_unique
  intro y hy
  clear hy
  -- It is enough to check that every generator of the inserted stage lies in the singleton
  -- adjoin over the old stage, and then close under the algebra operations.
  refine Algebra.adjoin_induction
    (s := (((insert x t : Finset S) : Set S)))
    (p := fun z hz => ∀ hzA : z ∈ A, (⟨z, hzA⟩ : A) ∈ Algebra.adjoin T ({xA} : Set A))
    ?_ ?_ ?_ ?_ y.2 y.2
  · intro z hz hzA
    rcases Finset.mem_insert.mp hz with rfl | hzt
    · -- The new generator is exactly the chosen singleton generator over `T`.
      change xA ∈ Algebra.adjoin T ({xA} : Set A)
      have hxmem : xA ∈ ({xA} : Set A) := by
        simp
      exact Algebra.subset_adjoin hxmem
    · -- Old generators already come from the previous stage through the inclusion `T → A`.
      have hzT : z ∈ T := by
        dsimp [T]
        have hztSet : z ∈ (t : Set S) := hzt
        exact Algebra.subset_adjoin hztSet
      change algebraMap T A ⟨z, hzT⟩ ∈ Algebra.adjoin T ({xA} : Set A)
      exact Subalgebra.algebraMap_mem _ _
  · intro r hrA
    -- Scalars from `R` lie in the previous stage and hence in the singleton adjoin over it.
    change algebraMap T A (algebraMap R T r) ∈ Algebra.adjoin T ({xA} : Set A)
    exact Subalgebra.algebraMap_mem _ _
  · intro z w hz hw hz_mem hw_mem hzwA
    -- The singleton adjoin is closed under addition.
    have hzA : z ∈ A := by
      simpa [A] using hz
    have hwA : w ∈ A := by
      simpa [A] using hw
    simpa using Subalgebra.add_mem _ (hz_mem hzA) (hw_mem hwA)
  · intro z w hz hw hz_mem hw_mem hzwA
    -- The singleton adjoin is closed under multiplication.
    have hzA : z ∈ A := by
      simpa [A] using hz
    have hwA : w ∈ A := by
      simpa [A] using hw
    simpa using Subalgebra.mul_mem _ (hz_mem hzA) (hw_mem hwA)

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: a finite type algebra is generated by a finite adjoin
stage. -/
private lemma existsFinset_adjoin_eq_top_of_finiteType [Algebra.FiniteType R S] :
    ∃ s : Finset S, Algebra.adjoin R (s : Set S) = ⊤ := by
  -- Extract a finite generating set from the finite-type structure and convert it to a `Finset`.
  obtain ⟨t, htfinite, htTop⟩ := Subalgebra.fg_def.1
    (show (⊤ : Subalgebra R S).FG from (inferInstance : Algebra.FiniteType R S).out)
  refine ⟨htfinite.toFinset, ?_⟩
  simpa [htfinite.coe_toFinset] using htTop

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: a finite adjoin stage equal to the whole algebra gives
finite type over the source. -/
private lemma finiteType_of_adjoin_finset_eq_top
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    Algebra.FiniteType R S := by
  -- The displayed finite adjoin stage is all of `S`, so it is a finite generating set for `S`.
  have hfg : (⊤ : Subalgebra R S).FG := by
    rw [← hs]
    exact Subalgebra.fg_def.2 ⟨(s : Set S), s.finite_toSet, rfl⟩
  exact ⟨hfg⟩

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: if a finite adjoin stage is the whole algebra, then the
stage inclusion is surjective. -/
private lemma adjoinStage_algebraMap_surjective
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    Function.Surjective (algebraMap (Algebra.adjoin R (s : Set S)) S) := by
  intro y
  refine ⟨⟨y, ?_⟩, rfl⟩
  -- The equality with `⊤` says exactly that every element of `S` belongs to the stage.
  simpa [hs] using (show y ∈ (⊤ : Subalgebra R S) from trivial)

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: if a finite adjoin stage is the whole algebra, then the
stage inclusion is bijective. -/
private lemma adjoinStage_algebraMap_bijective
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    Function.Bijective (algebraMap (Algebra.adjoin R (s : Set S)) S) := by
  -- The inclusion of a subalgebra is injective, and the preceding helper gives surjectivity.
  constructor
  · intro x y hxy
    exact Subtype.ext hxy
  · exact adjoinStage_algebraMap_surjective (R := R) (S := S) hs

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: if a map is surjective on stalks at a lying-over pair,
then the induced residue-field algebra map is bijective. -/
private lemma bijective_algebraMap_residueField_of_surjectiveOnStalks
    {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] [q.LiesOver p]
    (hsurj : (algebraMap R S).SurjectiveOnStalks) :
    Function.Bijective (algebraMap p.ResidueField q.ResidueField) := by
  have hmap :
      Ideal.ResidueField.map p q (algebraMap R S) (Ideal.over_def q p) =
        algebraMap p.ResidueField q.ResidueField := by
    -- Compare the explicit residue-field map with the default algebra map out of `κ(p)`.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext a
    simp only [RingHom.comp_apply]
    rw [Ideal.ResidueField.map_algebraMap]
    calc
      algebraMap S q.ResidueField (algebraMap R S a) = algebraMap R q.ResidueField a := by
        rw [IsScalarTower.algebraMap_apply R S q.ResidueField a]
      _ = algebraMap p.ResidueField q.ResidueField (algebraMap R p.ResidueField a) := by
        rw [IsScalarTower.algebraMap_apply R p.ResidueField q.ResidueField a]
  -- Surjectivity on stalks upgrades the owner residue-field map to a bijection.
  simpa [hmap] using hsurj.residueFieldMap_bijective p q (Ideal.over_def q p)

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: in the empty-generator stage, the bottom subalgebra is
identified with the base ring, so the residue-field contribution is zero. -/
private lemma adjoinEmpty_primeHeightResidueFieldTrdeg_eq
    [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R S))
    (q : PrimeSpectrum (Algebra.adjoin R (∅ : Set S))) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) := by
  have hmapSurj : Function.Surjective (algebraMap R (Algebra.adjoin R (∅ : Set S))) := by
    intro y
    have hybot : (y : S) ∈ (⊥ : Subalgebra R S) := by
      simpa [Algebra.adjoin_empty] using y.2
    rcases Algebra.mem_bot.mp hybot with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    exact Subtype.ext hr
  have hsurj :
      (algebraMap R (Algebra.adjoin R (∅ : Set S))).SurjectiveOnStalks := by
    -- The bottom-stage structure map is surjective, hence surjective on stalks.
    exact RingHom.surjectiveOnStalks_of_surjective hmapSurj
  have hheight :
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) =
        ENat.toNat (Ideal.primeHeight q.asIdeal) := by
    have hmapInj :
        Function.Injective (Algebra.ofId R (Algebra.adjoin R (∅ : Set S))) := by
      intro x y hxy
      apply hinj
      change (((algebraMap R (Algebra.adjoin R (∅ : Set S)) x :
          Algebra.adjoin R (∅ : Set S)) : S)) =
        (((algebraMap R (Algebra.adjoin R (∅ : Set S)) y :
          Algebra.adjoin R (∅ : Set S)) : S))
      simpa using congrArg (fun z : Algebra.adjoin R (∅ : Set S) ↦ (z : S)) hxy
    let eStage : R ≃ₐ[R] Algebra.adjoin R (∅ : Set S) :=
      AlgEquiv.ofBijective (Algebra.ofId R (Algebra.adjoin R (∅ : Set S)))
        ⟨hmapInj, hmapSurj⟩
    -- Build the equivalence from the actual structure map, so the height computation is a direct
    -- contraction statement for `q.under R`.
    have hcomap :
        Ideal.comap eStage.toRingEquiv q.asIdeal =
          q.asIdeal.under R := by
      ext r
      rfl
    have hheight_eq :
        (q.asIdeal.under R).height = q.asIdeal.height := by
      have h := RingEquiv.height_comap eStage.toRingEquiv q.asIdeal
      rwa [hcomap] at h
    have hprimeHeight_eq :
        Ideal.primeHeight (q.asIdeal.under R) = Ideal.primeHeight q.asIdeal := by
      simpa [Ideal.height_eq_primeHeight] using hheight_eq
    exact congrArg ENat.toNat hprimeHeight_eq
  have hbij :
      Function.Bijective
        (algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) :=
    bijective_algebraMap_residueField_of_surjectiveOnStalks
      (R := R) (S := Algebra.adjoin R (∅ : Set S))
      (p := q.asIdeal.under R) (q := q.asIdeal) hsurj
  have htrdegZero :
      Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField = 0 := by
    let eResidue :
        (q.asIdeal.under R).ResidueField ≃ₐ[(q.asIdeal.under R).ResidueField]
          q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective
        (Algebra.ofId (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
        hbij
    let _ :
        Algebra.IsAlgebraic (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_injective eResidue.symm.toAlgHom eResidue.symm.injective
    exact trdeg_eq_zero
      (R := (q.asIdeal.under R).ResidueField) (A := q.asIdeal.ResidueField)
  -- With the residue-field term zero, the equality reduces to the transported height equality.
  have htrdegToNat :
      Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) = 0 := by
    simpa [htrdegZero]
  omega

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the empty `Finset` adjoin stage has
the same height/residue-field contribution as the base ring. -/
private lemma adjoinFinsetEmpty_primeHeightResidueFieldTrdeg_eq
    [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R S))
    (q : PrimeSpectrum (Algebra.adjoin R (((∅ : Finset S) : Set S)))) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) := by
  have hmapSurj :
      Function.Surjective (algebraMap R (Algebra.adjoin R (((∅ : Finset S) : Set S)))) := by
    intro y
    have hybot : (y : S) ∈ (⊥ : Subalgebra R S) := by
      -- The empty `Finset` stage is the bottom subalgebra.
      have hEmpty :
          Algebra.adjoin R (((∅ : Finset S) : Set S)) = (⊥ : Subalgebra R S) := by
        rw [show (((∅ : Finset S) : Set S)) = (∅ : Set S) by
          ext z
          simp]
        exact Algebra.adjoin_empty R S
      simpa [hEmpty] using y.2
    rcases Algebra.mem_bot.mp hybot with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    exact Subtype.ext hr
  have hsurj :
      (algebraMap R (Algebra.adjoin R (((∅ : Finset S) : Set S)))).SurjectiveOnStalks := by
    -- Surjectivity of the empty-stage structure map passes to all stalks.
    exact RingHom.surjectiveOnStalks_of_surjective hmapSurj
  have hheight :
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) =
        ENat.toNat (Ideal.primeHeight q.asIdeal) := by
    have hmapInj :
        Function.Injective (Algebra.ofId R (Algebra.adjoin R (((∅ : Finset S) : Set S)))) := by
      intro x y hxy
      apply hinj
      change (((algebraMap R (Algebra.adjoin R (((∅ : Finset S) : Set S))) x :
          Algebra.adjoin R (((∅ : Finset S) : Set S))) : S)) =
        (((algebraMap R (Algebra.adjoin R (((∅ : Finset S) : Set S))) y :
          Algebra.adjoin R (((∅ : Finset S) : Set S))) : S))
      simpa using
        congrArg (fun z : Algebra.adjoin R (((∅ : Finset S) : Set S)) ↦ (z : S)) hxy
    let eStage : R ≃ₐ[R] Algebra.adjoin R (((∅ : Finset S) : Set S)) :=
      AlgEquiv.ofBijective (Algebra.ofId R (Algebra.adjoin R (((∅ : Finset S) : Set S))))
        ⟨hmapInj, hmapSurj⟩
    have hcomap :
        Ideal.comap eStage.toRingEquiv q.asIdeal =
          q.asIdeal.under R := by
      ext r
      rfl
    have hheight_eq :
        (q.asIdeal.under R).height = q.asIdeal.height := by
      have h := RingEquiv.height_comap eStage.toRingEquiv q.asIdeal
      rwa [hcomap] at h
    have hprimeHeight_eq :
        Ideal.primeHeight (q.asIdeal.under R) = Ideal.primeHeight q.asIdeal := by
      simpa [Ideal.height_eq_primeHeight] using hheight_eq
    exact congrArg ENat.toNat hprimeHeight_eq
  have hbij :
      Function.Bijective
        (algebraMap (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) :=
    bijective_algebraMap_residueField_of_surjectiveOnStalks
      (R := R) (S := Algebra.adjoin R (((∅ : Finset S) : Set S)))
      (p := q.asIdeal.under R) (q := q.asIdeal) hsurj
  have htrdegZero :
      Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField = 0 := by
    let eResidue :
        (q.asIdeal.under R).ResidueField ≃ₐ[(q.asIdeal.under R).ResidueField]
          q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective
        (Algebra.ofId (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
        hbij
    let _ :
        Algebra.IsAlgebraic (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_injective eResidue.symm.toAlgHom eResidue.symm.injective
    exact trdeg_eq_zero
      (R := (q.asIdeal.under R).ResidueField) (A := q.asIdeal.ResidueField)
  have htrdegToNat :
      Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) = 0 := by
    simpa [htrdegZero]
  -- With a trivial residue-field extension, the base-stage equality is just height transport.
  omega

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the empty finite-adjoin stage has zero generic
fraction-field transcendence degree over the base. -/
private lemma adjoinEmpty_fractionRingTrdeg_eq_zero
    (hinj : Function.Injective (algebraMap R S)) :
    Algebra.fractionRingTrdeg
        (R := R) (S := Algebra.adjoin R (((∅ : Finset S) : Set S)))
        (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj ∅) = 0 := by
  let A : Subalgebra R S := Algebra.adjoin R (((∅ : Finset S) : Set S))
  let hRA : Function.Injective (algebraMap R A) :=
    adjoinFinset_algebraMap_injective (R := R) (S := S) hinj ∅
  let _ : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hRA
  have hEmpty : A = (⊥ : Subalgebra R S) := by
    simpa [A] using Algebra.adjoin_empty R S
  let eBot : A ≃ₐ[R] (⊥ : Subalgebra R S) :=
    Subalgebra.equivOfEq A (⊥ : Subalgebra R S) hEmpty
  let e : A ≃ₐ[R] R := eBot.trans (Algebra.botEquivOfInjective hinj)
  let eFrac : FractionRing A ≃ₐ[FractionRing R] FractionRing R :=
    IsFractionRing.fieldEquivOfAlgEquiv (FractionRing R) (FractionRing A) (FractionRing R) e
  have htrdeg : Algebra.trdeg (FractionRing R) (FractionRing A) = 0 := by
    -- The fraction field of the empty stage is algebraic because it is equivalent to `Frac(R)`.
    let _ : Algebra.IsAlgebraic (FractionRing R) (FractionRing A) :=
      Algebra.IsAlgebraic.of_injective eFrac.toAlgHom eFrac.injective
    exact trdeg_eq_zero (R := FractionRing R) (A := FractionRing A)
  -- Unfold the private generic term once and use the zero transcendence-degree computation.
  simpa [Algebra.fractionRingTrdeg, A, hRA] using congrArg Cardinal.toNat htrdeg

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the prime transported along a terminal adjoin-stage
equivalence is the ordinary contraction of the ambient prime to that stage. -/
private lemma adjoinStage_comap_asIdeal_eq_under
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    (PrimeSpectrum.comap eStage.toRingHom q).asIdeal = q.asIdeal.under A := by
  -- Unfold the stage equivalence only to compare the two contraction maps pointwise.
  dsimp
  ext x
  rfl

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: contracting the terminal-stage prime further to the base
recovers direct contraction of the ambient prime. -/
private lemma adjoinStage_comap_under_eq_under
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    qA.asIdeal.under R = q.asIdeal.under R := by
  -- Once the transported prime is normalized to the stage contraction, contractions compose in
  -- the scalar tower `R ⟶ A ⟶ S`.
  dsimp
  ext r
  change
    (algebraMap (Algebra.adjoin R (s : Set S)) S
        (algebraMap R (Algebra.adjoin R (s : Set S)) r)) ∈ q.asIdeal ↔
      algebraMap R S r ∈ q.asIdeal
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (s : Set S)) S r]

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the contracted source prime has the same height after
transporting through a terminal finite adjoin stage. -/
private lemma adjoinStage_under_height_eq
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    (qA.asIdeal.under R).height = (q.asIdeal.under R).height := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  -- Move the existing contraction equality to the non-dependent `height` layer.
  have hunder : qA.asIdeal.under R = q.asIdeal.under R := by
    simpa [A, eStage, qA] using
      adjoinStage_comap_under_eq_under (R := R) (S := S) hs q
  exact congrArg Ideal.height hunder

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the natural-number height of the contracted source prime is
unchanged after terminal finite-adjoin transport. -/
private lemma adjoinStage_under_primeHeight_toNat_eq
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  -- Convert the non-dependent height equality back to prime heights for the two prime ideals.
  have hheight :
      (qA.asIdeal.under R).height = (q.asIdeal.under R).height := by
    simpa [A, eStage, qA] using
      adjoinStage_under_height_eq (R := R) (S := S) hs q
  have hprimeHeight :
      Ideal.primeHeight (qA.asIdeal.under R) =
        Ideal.primeHeight (q.asIdeal.under R) := by
    simpa [Ideal.height_eq_primeHeight] using hheight
  exact congrArg ENat.toNat hprimeHeight

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: terminal finite-adjoin transport preserves the
residue-field transcendence-degree term. -/
private lemma adjoinStage_residueFieldTrdeg_toNat_eq
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    Cardinal.toNat
        (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) =
      Cardinal.toNat
        (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  let pA : Ideal R := qA.asIdeal.under R
  let p : Ideal R := q.asIdeal.under R
  letI : pA.IsPrime := by
    dsimp [pA]
    infer_instance
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  change
    Cardinal.toNat (Algebra.trdeg pA.ResidueField qA.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField)
  have hqA_under : pA = p := by
    simpa [A, eStage, qA] using
      adjoinStage_comap_under_eq_under (R := R) (S := S) hs q
  have hq_lies : q.asIdeal.LiesOver qA.asIdeal := by
    refine ⟨?_⟩
    exact (by
      simpa [A, eStage, qA] using
        (adjoinStage_comap_asIdeal_eq_under (R := R) (S := S) hs q).symm)
  letI : q.asIdeal.LiesOver qA.asIdeal := hq_lies
  letI : qA.asIdeal.LiesOver pA := ⟨rfl⟩
  letI : q.asIdeal.LiesOver pA :=
    Ideal.LiesOver.trans q.asIdeal qA.asIdeal pA
  have hsurjStage : Function.Surjective (algebraMap A S) :=
    adjoinStage_algebraMap_surjective (R := R) (S := S) hs
  have hsurjStalks : (algebraMap A S).SurjectiveOnStalks :=
    RingHom.surjectiveOnStalks_of_surjective hsurjStage
  have hbij :
      Function.Bijective (algebraMap qA.asIdeal.ResidueField q.asIdeal.ResidueField) :=
    bijective_algebraMap_residueField_of_surjectiveOnStalks
      (R := A) (S := S) (p := qA.asIdeal) (q := q.asIdeal) hsurjStalks
  let eResidue :
      qA.asIdeal.ResidueField ≃ₐ[qA.asIdeal.ResidueField] q.asIdeal.ResidueField :=
    AlgEquiv.ofBijective (Algebra.ofId qA.asIdeal.ResidueField q.asIdeal.ResidueField) hbij
  have hstage :
      Cardinal.toNat
          (Algebra.trdeg pA.ResidueField qA.asIdeal.ResidueField) =
        Cardinal.toNat
          (Algebra.trdeg pA.ResidueField q.asIdeal.ResidueField) := by
    -- The stage and ambient residue fields are isomorphic over the stage residue field, hence
    -- also over the contracted base residue field.
    simpa using
      congrArg Cardinal.toNat
        (AlgEquiv.trdeg_eq
          (AlgEquiv.restrictScalars pA.ResidueField eResidue))
  -- Finally rewrite the contracted base prime from the transported stage back to the ambient one.
  calc
    Cardinal.toNat (Algebra.trdeg pA.ResidueField qA.asIdeal.ResidueField)
        = Cardinal.toNat (Algebra.trdeg pA.ResidueField q.asIdeal.ResidueField) := hstage
    _ = Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
          subst p
          rfl

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: after identifying a finite adjoin stage with the ambient
algebra, the transported prime has the same prime height. -/
private lemma adjoinStage_primeHeight_eq
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    Ideal.primeHeight qA.asIdeal = Ideal.primeHeight q.asIdeal := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  -- The stage equivalence identifies the two prime ideals, so their heights agree.
  have hheight_eq : qA.asIdeal.height = q.asIdeal.height :=
    RingEquiv.height_comap eStage.toRingEquiv q.asIdeal
  simpa [Ideal.height_eq_primeHeight] using hheight_eq

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: after identifying a finite adjoin stage with the ambient
algebra, the transported prime has the same natural-number prime height. -/
private lemma adjoinStage_primeHeight_toNat_eq
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    ENat.toNat (Ideal.primeHeight qA.asIdeal) =
      ENat.toNat (Ideal.primeHeight q.asIdeal) := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  -- Apply `toNat` to the stronger height equality proved above.
  have hheight_prime :
      Ideal.primeHeight qA.asIdeal = Ideal.primeHeight q.asIdeal := by
    simpa [A, eStage, qA] using
      adjoinStage_primeHeight_eq (R := R) (S := S) hs q
  exact congrArg ENat.toNat hheight_prime

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: terminal finite-adjoin transport preserves the full
left side of the dimension inequality. -/
private lemma adjoinStage_leftSide_eq
    {s : Finset S} (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
    let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
    let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
    ENat.toNat (Ideal.primeHeight qA.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  have hheight :
      ENat.toNat (Ideal.primeHeight qA.asIdeal) =
        ENat.toNat (Ideal.primeHeight q.asIdeal) := by
    -- Transport the target-prime height through the terminal stage equivalence.
    simpa [A, eStage, qA] using
      adjoinStage_primeHeight_toNat_eq (R := R) (S := S) hs q
  have hresidue :
      Cardinal.toNat
          (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) =
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
    -- Transport the residue-field term through the same terminal stage equivalence.
    simpa [A, eStage, qA] using
      adjoinStage_residueFieldTrdeg_toNat_eq (R := R) (S := S) hs q
  -- Combine the two transported summands into the left side used by the final inequality.
  dsimp only
  rw [hheight, hresidue]

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: terminal finite-adjoin transport preserves the
fraction-field transcendence-degree term. -/
private lemma adjoinStage_fractionRingTrdeg_eq_cardinalToNat_trdeg
    (hinj : Function.Injective (algebraMap R S)) {s : Finset S}
    (hs : Algebra.adjoin R (s : Set S) = ⊤) :
    Algebra.fractionRingTrdeg
        (R := R) (S := Algebra.adjoin R (s : Set S))
        (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj s) =
      Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let hRA : Function.Injective (algebraMap R A) :=
    adjoinFinset_algebraMap_injective (R := R) (S := S) hinj s
  let _ : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hRA
  let _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hinj
  have hAS_inj : Function.Injective (algebraMap A S) := by
    -- The terminal-stage map is the inclusion of a subalgebra into the ambient algebra.
    intro x y hxy
    exact Subtype.ext hxy
  have hAS_surj : Function.Surjective (algebraMap A S) := by
    -- The equality with `⊤` says every ambient element is represented by the stage.
    intro y
    refine ⟨⟨y, ?_⟩, rfl⟩
    simpa [A, hs] using (show y ∈ (⊤ : Subalgebra R S) from trivial)
  have hAS_bij : Function.Bijective (algebraMap A S) := ⟨hAS_inj, hAS_surj⟩
  let eStage : A ≃ₐ[R] S :=
    AlgEquiv.ofBijective ((Algebra.ofId A S).restrictScalars R) hAS_bij
  let eFrac : FractionRing A ≃ₐ[FractionRing R] FractionRing S :=
    IsFractionRing.fieldEquivOfAlgEquiv
      (FractionRing R) (FractionRing A) (FractionRing S) eStage
  have htrdeg :
      Algebra.trdeg (FractionRing R) (FractionRing A) =
        Algebra.trdeg (FractionRing R) (FractionRing S) := by
    -- The stage and ambient fraction fields are equivalent over `Frac(R)`.
    exact AlgEquiv.trdeg_eq eFrac
  -- Unfold the private generic term once, then transport trdeg through the fraction-field
  -- equivalence above.
  calc
    Algebra.fractionRingTrdeg (R := R) (S := Algebra.adjoin R (s : Set S))
        (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj s)
        = Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing A)) := by
            simp [A, Algebra.fractionRingTrdeg]
    _ = Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
          exact congrArg Cardinal.toNat htrdeg

omit [IsDomain R] [IsDomain S] [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: after coercing to `WithBot ℕ∞`,
the natural-number prime height of a Noetherian prime is the Krull dimension of its
localization. -/
private lemma primeHeightNatCast_eq_ringKrullDim_localizationAtPrime
    {A : Type*} [CommRing A] [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] :
    (((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) =
      ringKrullDim (Localization.AtPrime p) := by
  -- Rewrite local dimension as height and use Noetherian finiteness to recover `toNat`.
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
    Ideal.height_eq_primeHeight]
  exact_mod_cast ENat.coe_toNat (Ideal.primeHeight_ne_top p)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: a nonzero prime of a one-variable
polynomial ring over a field gives an algebraic quotient over the coefficient field. -/
private lemma polynomialQuotient_isAlgebraic_of_ne_bot
    {k : Type*} [Field k] (Q : Ideal (Polynomial k)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Algebra.IsAlgebraic k (Polynomial k ⧸ Q) := by
  let g₀ : Polynomial k := Submodule.IsPrincipal.generator Q
  have hg₀_ne : g₀ ≠ 0 := by
    intro hg₀
    exact hQ ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero Q).2 hg₀)
  let g : Polynomial k := g₀ * Polynomial.C (Polynomial.leadingCoeff g₀)⁻¹
  have hg_monic : g.Monic := by
    -- Scale the principal generator by the inverse leading coefficient to get a monic relation.
    simpa [g] using Polynomial.monic_mul_leadingCoeff_inv hg₀_ne
  have hg_mem : g ∈ Q := by
    -- The monic relation stays in the ideal because it is a scalar multiple of its generator.
    simpa [g] using Q.mul_mem_right (Polynomial.C (Polynomial.leadingCoeff g₀)⁻¹)
      (Submodule.IsPrincipal.generator_mem Q)
  have hIntegralHom : (algebraMap k (Polynomial k ⧸ Q)).IsIntegral := by
    -- A monic polynomial in the kernel makes the quotient integral over the field.
    simpa using
      (Polynomial.Monic.quotient_isIntegral (S := k) (I := Q) hg_monic hg_mem)
  letI : Algebra.IsIntegral k (Polynomial k ⧸ Q) :=
    (algebraMap_isIntegral_iff (R := k) (A := Polynomial k ⧸ Q)).mp hIntegralHom
  infer_instance

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: a polynomial ring in one variable
over a field has Krull dimension one. -/
private lemma polynomialRingKrullDim_eq_one
    {k : Type*} [Field k] :
    ringKrullDim (Polynomial k) = 1 := by
  -- The general polynomial-dimension formula specializes to `0 + 1` over a field.
  simpa [ringKrullDim_eq_zero_of_field] using
    (Polynomial.ringKrullDim_of_isNoetherianRing (R := k))

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: localizing `k[X]` at `(0)` gives its
fraction field, hence a zero-dimensional local ring. -/
private lemma polynomialRingKrullDim_localizationAtPrime_bot_eq_zero
    {k : Type*} [Field k] :
    ringKrullDim (Localization.AtPrime (⊥ : Ideal (Polynomial k))) = 0 := by
  letI : IsFractionRing (Polynomial k) (Localization.AtPrime (⊥ : Ideal (Polynomial k))) := by
    delta IsFractionRing
    simpa [Ideal.primeCompl_bot] using
      (inferInstance :
        IsLocalization ((⊥ : Ideal (Polynomial k)).primeCompl)
          (Localization.AtPrime (⊥ : Ideal (Polynomial k))))
  let e : FractionRing (Polynomial k) ≃ₐ[Polynomial k]
      Localization.AtPrime (⊥ : Ideal (Polynomial k)) :=
    FractionRing.algEquiv (Polynomial k) (Localization.AtPrime (⊥ : Ideal (Polynomial k)))
  -- Transport Krull dimension to the fraction field.
  rw [← ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
  exact ringKrullDim_eq_zero_of_field (FractionRing (Polynomial k))

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: every nonzero prime of `k[X]` is
maximal. -/
private lemma polynomialPrime_isMaximal_of_ne_bot
    {k : Type*} [Field k] (Q : Ideal (Polynomial k)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Q.IsMaximal := by
  have hdim : ringKrullDim (Polynomial k) = 1 :=
    polynomialRingKrullDim_eq_one (k := k)
  have hdim' : Ring.KrullDimLE 1 (Polynomial k) :=
    Ring.krullDimLE_iff.mpr (by simpa [hdim])
  letI : Ring.DimensionLEOne (Polynomial k) := by
    refine ⟨fun {p} hp hprime ↦ ?_⟩
    exact Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim' p hp hprime
  -- In a one-dimensional domain, a nonzero prime is maximal.
  exact Ring.DimensionLEOne.maximalOfPrime hQ inferInstance

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: localizing `k[X]` at a nonzero prime
has Krull dimension one. -/
private lemma polynomialRingKrullDim_localizationAtPrime_eq_one_of_ne_bot
    {k : Type*} [Field k] (Q : Ideal (Polynomial k)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    ringKrullDim (Localization.AtPrime Q) = 1 := by
  letI : Q.IsMaximal := polynomialPrime_isMaximal_of_ne_bot (Q := Q) hQ
  letI : Q.LiesOver (⊥ : Ideal k) := by
    refine ⟨?_⟩
    simpa [Ideal.under_def] using
      (Ideal.eq_bot_of_prime (I := Ideal.comap Polynomial.C Q)).symm
  have hbot_height : (⊥ : Ideal k).height = 0 := by
    have hbot_primeHeight : (⊥ : Ideal k).primeHeight = 0 := by
      rw [Ideal.primeHeight_eq_zero_iff, IsDomain.minimalPrimes_eq_singleton_bot]
      simp
    simpa [Ideal.height_eq_primeHeight] using hbot_primeHeight
  have hQ_height : Q.height = 1 := by
    -- The polynomial height-jump formula computes the height over the zero prime of the field.
    calc
      Q.height = (⊥ : Ideal k).height + 1 := by
        simpa using (Polynomial.height_eq_height_add_one (p := (⊥ : Ideal k)) (P := Q))
      _ = 1 := by simp [hbot_height]
  simpa [hQ_height] using
    (IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q))

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the transported polynomial-fiber
height branch is `0` at the generic point and `1` at a nonzero prime. -/
private lemma polynomialTransport_branch_ringKrullDim_values
    {k : Type*} [Field k] (Q : PrimeSpectrum (Polynomial k)) :
    ringKrullDim (Localization.AtPrime Q.asIdeal) =
      if Q.asIdeal = ⊥ then 0 else 1 := by
  by_cases hQ : Q.asIdeal = ⊥
  · have hQbot : Q = (⊥ : PrimeSpectrum (Polynomial k)) := by
      apply PrimeSpectrum.ext
      simpa using hQ
    subst hQbot
    -- The generic branch localizes to the fraction field of `k[X]`.
    simpa using polynomialRingKrullDim_localizationAtPrime_bot_eq_zero (k := k)
  · -- The closed branch is the localization at a maximal ideal of the one-dimensional ring.
    simpa [hQ] using
      polynomialRingKrullDim_localizationAtPrime_eq_one_of_ne_bot (Q := Q.asIdeal) hQ

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the transported polynomial-fiber
residue-field transcendence branch is `1` at the generic point and `0` at a nonzero prime. -/
private lemma polynomialTransport_branch_trdeg_values
    {k : Type*} [Field k] (Q : PrimeSpectrum (Polynomial k)) :
    Cardinal.toNat (Algebra.trdeg k Q.asIdeal.ResidueField) =
      if Q.asIdeal = ⊥ then 1 else 0 := by
  by_cases hQ : Q.asIdeal = ⊥
  · have hQbot : Q = ⊥ := by
      apply PrimeSpectrum.ext
      simpa using hQ
    subst hQbot
    let S := Polynomial k
    let e0 : FractionRing S ≃ₐ[S] ((⊥ : Ideal S).ResidueField) := by
      let e : S ≃ₐ[S] S ⧸ (⊥ : Ideal S) := (AlgEquiv.quotientBot S S).symm
      letI : IsFractionRing S ((⊥ : Ideal S).ResidueField) := by
        refine IsFractionRing.of_ringEquiv_left e.toRingEquiv ?_
        intro x
        change algebraMap S ((⊥ : Ideal S).ResidueField) x =
          algebraMap (S ⧸ (⊥ : Ideal S)) ((⊥ : Ideal S).ResidueField)
            (Ideal.Quotient.mk _ x)
        symm
        rfl
      exact FractionRing.algEquiv S ((⊥ : Ideal S).ResidueField)
    let e : FractionRing S ≃ₐ[k] ((⊥ : Ideal S).ResidueField) :=
      AlgEquiv.restrictScalars k e0
    have hAlgFrac : Algebra.IsAlgebraic S (FractionRing S) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := S) (K := FractionRing S)
          (C := FractionRing S)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing S) (FractionRing S))
    have htrdegFrac : Algebra.trdeg k (FractionRing S) = Algebra.trdeg k S := by
      -- Split `k -> k[X] -> Frac(k[X])` and kill the relative algebraic top extension.
      have hsplit := trdeg_add_eq (R := k) (S := S) (A := FractionRing S)
      have hzero : Algebra.trdeg S (FractionRing S) = 0 :=
        trdeg_eq_zero (R := S) (A := FractionRing S)
      simpa [hzero] using hsplit.symm
    calc
      Cardinal.toNat (Algebra.trdeg k ((⊥ : Ideal S).ResidueField))
          = Cardinal.toNat (Algebra.trdeg k (FractionRing S)) := by
              simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq (R := k) e).symm
      _ = Cardinal.toNat (Algebra.trdeg k S) := by rw [htrdegFrac]
      _ = 1 := by
        simpa [S] using congrArg Cardinal.toNat (Polynomial.trdeg_of_isDomain (R := k))
      _ = if (⊥ : Ideal S) = ⊥ then 1 else 0 := by simp
  · have hQmax : Q.asIdeal.IsMaximal :=
      polynomialPrime_isMaximal_of_ne_bot (Q := Q.asIdeal) hQ
    letI : Q.asIdeal.IsMaximal := hQmax
    let eQuot : (Polynomial k ⧸ Q.asIdeal) ≃ₐ[k] Q.asIdeal.ResidueField :=
      AlgEquiv.ofBijective
        (IsScalarTower.toAlgHom k (Polynomial k ⧸ Q.asIdeal) Q.asIdeal.ResidueField)
        (Ideal.bijective_algebraMap_quotient_residueField Q.asIdeal)
    letI : Algebra.IsAlgebraic k (Polynomial k ⧸ Q.asIdeal) :=
      polynomialQuotient_isAlgebraic_of_ne_bot (Q := Q.asIdeal) hQ
    letI : Algebra.IsAlgebraic k Q.asIdeal.ResidueField :=
      Algebra.IsAlgebraic.of_injective eQuot.symm.toAlgHom eQuot.symm.injective
    -- The closed branch is algebraic over `k`, so its transcendence degree is zero.
    simpa [hQ, trdeg_eq_zero (R := k) (A := Q.asIdeal.ResidueField)]

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: complementary polynomial branch
values add to one after the height and residue-field terms have been normalized. -/
private lemma polynomialBranch_values_sum_eq_one
    {base height residue : ℕ} {genericBranch : Prop} [Decidable genericBranch]
    (hheight : height = base + (if genericBranch then 0 else 1))
    (hresidue : residue = if genericBranch then 1 else 0) :
    height + residue = base + 1 := by
  -- Once the branch values are exposed, the generic and closed cases are pure arithmetic.
  by_cases hbranch : genericBranch
  · simp [hbranch] at hheight hresidue
    omega
  · simp [hbranch] at hheight hresidue
    omega

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the fiber prime attached to `q`
contracts back to `q` along the canonical map from the source to the fiber ring. -/
private theorem fiberPrime_contracts_to_source_prime
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    PrimeSpectrum.comap (algebraMap B ((q.asIdeal.under A).Fiber B)) (fiberPrimeAt A B q) = q := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  have hleft :
      ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q)) = q := by
    -- The definition of `fiberPrimeAt` uses the forward equivalence, so the inverse recovers `q`.
    simpa [p, fiberPrimeAt] using
      congrArg Subtype.val
        ((PrimeSpectrum.preimageEquivFiber A B p).symm_apply_apply ⟨q, rfl⟩)
  -- Unfold the contraction map in the fiber equivalence and apply the inverse law.
  calc
    PrimeSpectrum.comap (algebraMap B (p.asIdeal.Fiber B)) (fiberPrimeAt A B q)
        = ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q)) := by
            change PrimeSpectrum.comap Algebra.TensorProduct.includeRight.toRingHom
                (fiberPrimeAt A B q) =
              ↑((PrimeSpectrum.preimageEquivFiber A B p).symm (fiberPrimeAt A B q))
            rfl
    _ = q := hleft

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the fiber prime attached to `q`
contracts back to `q.asIdeal` on underlying ideals. -/
private theorem fiberPrime_comap_asIdeal
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    Ideal.comap (algebraMap B ((q.asIdeal.under A).Fiber B)) (fiberPrimeAt A B q).asIdeal =
      q.asIdeal := by
  -- Pass from the prime-spectrum contraction statement to underlying ideals.
  simpa using congrArg PrimeSpectrum.asIdeal
    (fiberPrime_contracts_to_source_prime (A := A) (B := B) q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the residue field at the fiber prime is
canonically identified with the residue field at the original prime. -/
private noncomputable def fiberPrime_residueField_equiv_source
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    (fiberPrimeAt A B q).asIdeal.ResidueField ≃ₐ[B] q.asIdeal.ResidueField := by
  let hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt A B q).asIdeal
          (Algebra.ofId B ((q.asIdeal.under A).Fiber B))
          (fiberPrime_comap_asIdeal (A := A) (B := B) q).symm) := by
    -- The residue-field base-change map is surjective on stalks, hence bijective on residue fields.
    simpa using
      RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        ((Ideal.surjectiveOnStalks_residueField (R := A) (q.asIdeal.under A)).baseChange')
        q.asIdeal (fiberPrimeAt A B q).asIdeal
        (fiberPrime_comap_asIdeal (A := A) (B := B) q).symm
  -- Package the bijective residue-field map as an algebra equivalence.
  exact
    (AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ q.asIdeal (fiberPrimeAt A B q).asIdeal
      (Algebra.ofId B ((q.asIdeal.under A).Fiber B))
      (fiberPrime_comap_asIdeal (A := A) (B := B) q).symm)
      hbij).symm

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: localizing corresponding primes along an
algebra equivalence gives an algebra equivalence of the local rings. -/
private noncomputable def localizationAtPrime_algEquiv_of_algEquiv
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    Localization.AtPrime (PrimeSpectrum.comap e.toRingHom q).asIdeal ≃ₐ[R]
      Localization.AtPrime q.asIdeal :=
  -- Transport the source prime by `e` and invoke the canonical localization comparison.
  Localization.localAlgEquiv
    (I := (PrimeSpectrum.comap e.toRingHom q).asIdeal)
    (J := q.asIdeal)
    e
    (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: an algebra equivalence identifies the
residue fields of corresponding prime ideals. -/
private noncomputable def residueField_algEquiv_of_algEquiv
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (q : PrimeSpectrum B) :
    (PrimeSpectrum.comap e.toRingHom q).asIdeal.ResidueField ≃ₐ[R] q.asIdeal.ResidueField := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap e.toRingHom q
  have hbij :
      Function.Bijective
        (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal e.toAlgHom
          (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)) := by
    -- A surjective equivalence is surjective on stalks, hence bijective on residue fields.
    simpa [p] using
      RingHom.SurjectiveOnStalks.residueFieldMap_bijective
        (RingHom.surjectiveOnStalks_of_surjective e.surjective)
        p.asIdeal q.asIdeal
        (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q)
  -- Package the canonical bijection as the required residue-field algebra equivalence.
  exact
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ p.asIdeal q.asIdeal e.toAlgHom
        (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) q))
      hbij

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: rewrite the residue-field transport to a
literal source ideal owner. -/
private noncomputable def residueField_algEquiv_of_algEquiv_of_comap_asIdeal_eq
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (Q : PrimeSpectrum B) (I : Ideal A) [I.IsPrime]
    (hI : Ideal.comap e.toRingHom Q.asIdeal = I) :
    I.ResidueField ≃ₐ[R] Q.asIdeal.ResidueField := by
  let J : Ideal A := Ideal.comap e.toRingHom Q.asIdeal
  let eSource : I.ResidueField ≃ₐ[R] J.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ I J (AlgHom.id R A) hI.symm)
      ((RingHom.surjectiveOnStalks_of_surjective (fun x ↦ ⟨x, rfl⟩)).residueFieldMap_bijective
        I J hI.symm)
  -- First rewrite the source residue field, then transport along the algebra equivalence.
  exact eSource.trans (residueField_algEquiv_of_algEquiv (R := R) e Q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the fiber of `A[X]` over a prime `p` is
canonically the polynomial ring `κ(p)[X]`. -/
private noncomputable def polynomial_fiber_algEquiv_residueField_polynomial
    {A : Type*} [CommRing A] (p : Ideal A) [p.IsPrime] :
    p.Fiber (Polynomial A) ≃ₐ[p.ResidueField] Polynomial p.ResidueField := by
  let eQuot :
      p.Fiber (Polynomial A) ≃ₐ[p.ResidueField]
        Polynomial p.ResidueField ⧸
          ((RingHom.ker (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A)).map
            (Polynomial.mapRingHom (algebraMap A p.ResidueField))) :=
    Polynomial.fiberEquivQuotient
      (f := (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A))
      (by intro x; exact ⟨x, rfl⟩)
      p
  have hker :
      ((RingHom.ker (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A)).map
        (Polynomial.mapRingHom (algebraMap A p.ResidueField))) = ⊥ := by
    -- The identity presentation has zero kernel, so the quotient kernel disappears.
    have hker0 :
        RingHom.ker (AlgHom.id A (Polynomial A) : Polynomial A →ₐ[A] Polynomial A) =
          (⊥ : Ideal (Polynomial A)) := by
      ext f
      simp [RingHom.mem_ker]
    rw [hker0, Ideal.map_bot]
  -- Use the library fiber quotient, then collapse the quotient by zero.
  exact eQuot.trans ((Ideal.quotientEquivAlgOfEq _ hker).trans (AlgEquiv.quotientBot _ _))

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: transport `fiberPrimeAt` for `A[X]` to
a literal prime of `κ(q ∩ A)[X]`. -/
private noncomputable def fiberPrime_polynomial_transport
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    PrimeSpectrum (Polynomial ((q.asIdeal.under A).ResidueField)) := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  -- Comap the original fiber prime along the inverse polynomial-fiber equivalence.
  exact PrimeSpectrum.comap
    ((polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).symm.toRingHom)
    (fiberPrimeAt A (Polynomial A) q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: transporting the polynomial fiber prime
back along the forward equivalence recovers the original fiber prime. -/
private lemma comap_polynomial_fiber_transport_eq_fiberPrimeAt
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    PrimeSpectrum.comap
        (polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).toRingHom
        (fiberPrime_polynomial_transport (A := A) q) =
      fiberPrimeAt A (Polynomial A) q := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  -- The transported prime was defined by the inverse equivalence, so comapping back cancels it.
  apply PrimeSpectrum.ext
  change
      Ideal.comap
        (polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).toRingHom
        (fiberPrime_polynomial_transport (A := A) q).asIdeal =
      (fiberPrimeAt A (Polynomial A) q).asIdeal
  simpa [fiberPrime_polynomial_transport] using
    (Ideal.comap_of_equiv (I := (fiberPrimeAt A (Polynomial A) q).asIdeal)
      (polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).toRingEquiv)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: after transporting the polynomial fiber
to `κ(p)[X]`, the fiber local ring becomes the localization at the transported prime. -/
private lemma ringKrullDim_fiberLocalRingAt_polynomial_eq_ringKrullDim_localization_transport
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    ringKrullDim (fiberLocalRingAt A (Polynomial A) q) =
      ringKrullDim (Localization.AtPrime (fiberPrime_polynomial_transport (A := A) q).asIdeal) := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let eκ : p.Fiber (Polynomial A) ≃ₐ[p.ResidueField] Polynomial p.ResidueField :=
    polynomial_fiber_algEquiv_residueField_polynomial (A := A) p
  let qκ : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let eLoc :
      Localization.AtPrime qκ.asIdeal ≃ₐ[p.ResidueField]
        Localization.AtPrime (PrimeSpectrum.comap eκ.toRingHom qκ).asIdeal :=
    (localizationAtPrime_algEquiv_of_algEquiv (R := p.ResidueField) eκ qκ).symm
  have hqκ : PrimeSpectrum.comap eκ.toRingHom qκ = fiberPrimeAt A (Polynomial A) q := by
    -- Reuse the prime-transport bridge rather than unfolding the transported prime again.
    simpa [p, qκ] using comap_polynomial_fiber_transport_eq_fiberPrimeAt (A := A) q
  have hdim :
      ringKrullDim (Localization.AtPrime (PrimeSpectrum.comap eκ.toRingHom qκ).asIdeal) =
        ringKrullDim (Localization.AtPrime qκ.asIdeal) := by
    exact (ringKrullDim_eq_of_ringEquiv eLoc.toRingEquiv).symm
  rw [hqκ] at hdim
  -- Unfold the owner fiber local ring only after the prime transport has been named.
  simpa [fiberLocalRingAt, p, qκ] using hdim

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: record the explicit
`κ(q ∩ A)`-algebra structure on the residue field of the source fiber prime. -/
private noncomputable abbrev fiberPrime_residueField_baseAlgebra
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  (((fiberPrime_residueField_equiv_source (A := A) (B := B) q).symm.toRingHom).comp
    (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) rfl)).toAlgebra

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: record the explicit base-field algebra
structure on the residue field of the transported polynomial prime. -/
private noncomputable abbrev fiberPrime_polynomial_transport_residueField_baseAlgebra
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    Algebra p.ResidueField (fiberPrime_polynomial_transport (A := A) q).asIdeal.ResidueField :=
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := inferInstance
  (((algebraMap (Polynomial p.ResidueField)
      (fiberPrime_polynomial_transport (A := A) q).asIdeal.ResidueField)).comp
    Polynomial.C).toAlgebra

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the explicit source-side residue-field
equivalence commutes with the contracted residue-field scalar map. -/
private lemma fiberPrime_residueField_equiv_source_commutes
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B)
    (x : (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    let _ : Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := B) q
    fiberPrime_residueField_equiv_source (A := A) (B := B) q
        (algebraMap p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField x) =
      algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField x := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  -- Unfold the explicit scalar structure and cancel the inverse equivalence.
  change
    fiberPrime_residueField_equiv_source (A := A) (B := B) q
        ((((fiberPrime_residueField_equiv_source (A := A) (B := B) q).symm.toRingHom).comp
          (Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) rfl)) x) =
      algebraMap p.asIdeal.ResidueField q.asIdeal.ResidueField x
  simpa [RingHom.comp_apply] using
    (fiberPrime_residueField_equiv_source (A := A) (B := B) q).apply_symm_apply
      ((Ideal.ResidueField.map p.asIdeal q.asIdeal (algebraMap A B) rfl) x)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: composing the default fiber-prime scalar
map with the canonical map back to `κ(q)` recovers the usual residue-field map. -/
private lemma fiberPrime_polynomial_source_default_comp_commutes
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).toRingHom.comp
        ((algebraMap (p.Fiber (Polynomial A))
            (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
          (algebraMap p.ResidueField (p.Fiber (Polynomial A)))) =
      Ideal.ResidueField.map p q.asIdeal (algebraMap A (Polynomial A)) rfl := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  -- Compare the two maps from `κ(p)` on residue classes coming from `A`.
  apply Ideal.ResidueField.ringHom_ext (I := p)
  ext a
  simp only [RingHom.comp_apply]
  have hbase :
      (algebraMap p.ResidueField (p.Fiber (Polynomial A))) ((algebraMap A p.ResidueField) a) =
        ((Algebra.TensorProduct.includeRight : Polynomial A →ₐ[A] p.Fiber (Polynomial A)).toRingHom.comp
          Polynomial.C) a := by
    simpa [RingHom.comp_apply] using
      congrArg (fun f : A →+* p.Fiber (Polynomial A) => f a)
        (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := A) (A := p.ResidueField) (B := Polynomial A))
  rw [hbase, RingHom.comp_apply]
  have hright_apply :
      (algebraMap (p.Fiber (Polynomial A))
          (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField)
        ((Algebra.TensorProduct.includeRight : Polynomial A →ₐ[A] p.Fiber (Polynomial A)).toRingHom
          (Polynomial.C a)) =
      algebraMap (Polynomial A) (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        (Polynomial.C a) := by
    simpa [RingHom.comp_apply] using
      congrArg
        (fun f : Polynomial A →+* (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField =>
          f (Polynomial.C a))
        (AlgHom.comp_algebraMap_of_tower (R := Polynomial A)
          (f := IsScalarTower.toAlgHom (Polynomial A)
            (p.Fiber (Polynomial A))
            (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField))
  rw [hright_apply]
  -- The fiber-prime residue equivalence is `Polynomial A`-linear.
  calc
    (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).toRingHom
        ((algebraMap (Polynomial A) (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField)
          (Polynomial.C a))
      = algebraMap (Polynomial A) q.asIdeal.ResidueField (Polynomial.C a) := by
          simpa using
            (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).commutes
              (Polynomial.C a)
    _ = (Ideal.ResidueField.map p q.asIdeal (algebraMap A (Polynomial A)) rfl)
          ((algebraMap A p.ResidueField) a) := by
          symm
          exact
            Ideal.ResidueField.map_algebraMap p q.asIdeal (algebraMap A (Polynomial A)) rfl a

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the explicit source algebra structure
on the fiber-prime residue field agrees with the default scalar map inherited from the fiber. -/
private lemma fiberPrime_polynomial_source_baseAlgebra_eq_default
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    algebraMap p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField =
      ((algebraMap (p.Fiber (Polynomial A))
          (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))) := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let _ : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  -- Compare after applying the canonical equivalence back to `κ(q)`.
  apply Ideal.ResidueField.ringHom_ext (I := p)
  ext a
  apply (fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q).injective
  calc
    fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q
        (((algebraMap p.ResidueField
              (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
            (algebraMap A p.ResidueField)) a)
      = algebraMap p.ResidueField q.asIdeal.ResidueField (algebraMap A p.ResidueField a) := by
          simpa [RingHom.comp_apply] using
            (fiberPrime_residueField_equiv_source_commutes (A := A) (B := Polynomial A) q
              (algebraMap A p.ResidueField a))
    _ =
        fiberPrime_residueField_equiv_source (A := A) (B := Polynomial A) q
          ((((algebraMap (p.Fiber (Polynomial A))
                (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
              (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).comp
            (algebraMap A p.ResidueField)) a) := by
          symm
          simpa [RingHom.comp_apply] using
            congrArg
              (fun f : p.ResidueField →+* q.asIdeal.ResidueField =>
                f (algebraMap A p.ResidueField a))
              (fiberPrime_polynomial_source_default_comp_commutes (A := A) q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: source fiber-prime residue fields carry
the same `κ(q ∩ A)`-algebra structure from the default and explicit scalar maps. -/
private noncomputable def fiberPrime_polynomial_source_default_residueField_id_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    let defaultAlg : Algebra p.ResidueField RF :=
      ((algebraMap (p.Fiber (Polynomial A)) RF).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
    let explicitAlg : Algebra p.ResidueField RF :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    @AlgEquiv p.ResidueField RF RF _ _ _ explicitAlg defaultAlg := by
  let p : Ideal A := q.asIdeal.under A
  letI : p.IsPrime := by
    dsimp [p]
    infer_instance
  let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
  let defaultAlg : Algebra p.ResidueField RF :=
    ((algebraMap (p.Fiber (Polynomial A)) RF).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let explicitAlg : Algebra p.ResidueField RF :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  -- The scalar-map equality packages as the identity algebra equivalence.
  exact
    @AlgEquiv.ofRingEquiv p.ResidueField RF RF _ _ _ explicitAlg defaultAlg
      (f := RingEquiv.refl _)
      (fun x ↦
        DFunLike.congr_fun (fiberPrime_polynomial_source_baseAlgebra_eq_default (A := A) q) x)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the local-ring residue-field owner on
the transported polynomial residue field agrees with the literal polynomial-ring owner. -/
private noncomputable def transported_polynomial_residueField_id_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let defaultAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    let explicitAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
        Polynomial.C).toAlgebra
    @AlgEquiv p.ResidueField Q.asIdeal.ResidueField Q.asIdeal.ResidueField
      _ _ _ defaultAlg explicitAlg := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let defaultAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let explicitAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
      Polynomial.C).toAlgebra
  -- Check scalar compatibility after applying the local-ring residue map.
  exact
    @AlgEquiv.ofRingEquiv p.ResidueField Q.asIdeal.ResidueField Q.asIdeal.ResidueField
      _ _ _ defaultAlg explicitAlg (f := RingEquiv.refl _)
      (fun x ↦ by
        change
          IsLocalRing.residue (Localization.AtPrime Q.asIdeal)
              (algebraMap p.ResidueField (Localization.AtPrime Q.asIdeal) x) =
            IsLocalRing.residue (Localization.AtPrime Q.asIdeal)
              (algebraMap (Polynomial p.ResidueField) (Localization.AtPrime Q.asIdeal)
                (Polynomial.C x))
        simpa using congrArg
          (IsLocalRing.residue (Localization.AtPrime Q.asIdeal))
          ((IsScalarTower.algebraMap_apply p.ResidueField
            (Polynomial p.ResidueField)
            (Localization.AtPrime Q.asIdeal) x).symm))

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the transported polynomial fiber prime
has the same source ideal as the original fiber prime after comapping along the fiber equivalence. -/
private lemma comap_polynomial_fiber_transport_asIdeal_eq_fiberPrimeAt
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    Ideal.comap
        (polynomial_fiber_algEquiv_residueField_polynomial (A := A) p).toRingHom
        (fiberPrime_polynomial_transport (A := A) q).asIdeal =
      (fiberPrimeAt A (Polynomial A) q).asIdeal := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  -- Take underlying ideals in the already proved prime-spectrum transport identity.
  simpa [p] using
    congrArg PrimeSpectrum.asIdeal
      (comap_polynomial_fiber_transport_eq_fiberPrimeAt (A := A) q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: residue-field transport along an
algebra equivalence respects the scalar maps coming from an ambient base ring. -/
private lemma residueFieldAlgEquivOfComapWithAmbientScalars_commutes
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (Q : PrimeSpectrum B) (I : Ideal A) [I.IsPrime]
    (hI : Ideal.comap e.toRingHom Q.asIdeal = I) (x : R) :
    (residueField_algEquiv_of_algEquiv_of_comap_asIdeal_eq
        (R := R) e Q I hI)
      (algebraMap A I.ResidueField (algebraMap R A x)) =
    algebraMap B Q.asIdeal.ResidueField (algebraMap R B x) := by
  -- Both sides are residue classes of the same scalar after transporting through `e`.
  let J : Ideal A := Ideal.comap e.toRingHom Q.asIdeal
  let eSource : I.ResidueField ≃ₐ[R] J.ResidueField :=
    AlgEquiv.ofBijective
      (Ideal.ResidueField.mapₐ I J (AlgHom.id R A) hI.symm)
      ((RingHom.surjectiveOnStalks_of_surjective (fun y ↦ ⟨y, rfl⟩)).residueFieldMap_bijective
        I J hI.symm)
  let eTarget : J.ResidueField ≃ₐ[R] Q.asIdeal.ResidueField :=
    residueField_algEquiv_of_algEquiv (R := R) e Q
  change
    (eSource.trans eTarget) (algebraMap A I.ResidueField (algebraMap R A x)) =
      algebraMap B Q.asIdeal.ResidueField (algebraMap R B x)
  rw [AlgEquiv.trans_apply]
  have hsource :
      eSource (algebraMap A I.ResidueField (algebraMap R A x)) =
        algebraMap A J.ResidueField (algebraMap R A x) := by
    -- The source-changing residue-field map is induced by the identity on the ambient algebra.
    simpa [eSource] using
      Ideal.ResidueField.map_algebraMap I J (AlgHom.id R A) hI.symm (algebraMap R A x)
  rw [hsource]
  have htarget :
      eTarget (algebraMap A J.ResidueField (algebraMap R A x)) =
        algebraMap B Q.asIdeal.ResidueField (e (algebraMap R A x)) := by
    -- The target residue-field map is induced by `e`, so it sends residue classes functorially.
    simpa [J, eTarget] using
      Ideal.ResidueField.map_algebraMap J Q.asIdeal e.toAlgHom
        (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) Q) (algebraMap R A x)
  rw [htarget]
  -- Finally use that `e` is an `R`-algebra equivalence.
  rw [e.commutes x]

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: residue-field transport along an
algebra equivalence with the scalar structures inherited from ambient scalar maps. -/
private noncomputable def residueFieldAlgEquivOfComapWithAmbientScalars
    {R : Type*} [CommRing R]
    {A : Type*} [CommRing A] [Algebra R A]
    {B : Type*} [CommRing B] [Algebra R B]
    (e : A ≃ₐ[R] B) (Q : PrimeSpectrum B) (I : Ideal A) [I.IsPrime]
    (hI : Ideal.comap e.toRingHom Q.asIdeal = I) :
    let sourceAlg : Algebra R I.ResidueField :=
      ((algebraMap A I.ResidueField).comp (algebraMap R A)).toAlgebra
    let targetAlg : Algebra R Q.asIdeal.ResidueField :=
      ((algebraMap B Q.asIdeal.ResidueField).comp (algebraMap R B)).toAlgebra
    @AlgEquiv R I.ResidueField Q.asIdeal.ResidueField _ _ _ sourceAlg targetAlg :=
  @AlgEquiv.ofRingEquiv R I.ResidueField Q.asIdeal.ResidueField _ _ _
    (((algebraMap A I.ResidueField).comp (algebraMap R A)).toAlgebra)
    (((algebraMap B Q.asIdeal.ResidueField).comp (algebraMap R B)).toAlgebra)
    (f :=
      (residueField_algEquiv_of_algEquiv_of_comap_asIdeal_eq
        (R := R) e Q I hI).toRingEquiv)
    (residueFieldAlgEquivOfComapWithAmbientScalars_commutes (R := R) e Q I hI)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: normalize the local-ring owner on the
source fiber-prime residue field to the fiber-composite owner. -/
private noncomputable def fiberPrime_polynomial_source_local_residueField_id_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    let localAlg : Algebra p.ResidueField RF :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime (fiberPrimeAt A (Polynomial A) q).asIdeal)
    let defaultAlg : Algebra p.ResidueField RF :=
      ((algebraMap (p.Fiber (Polynomial A)) RF).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
    @AlgEquiv p.ResidueField RF RF _ _ _ localAlg defaultAlg := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
  exact
    @AlgEquiv.ofRingEquiv p.ResidueField RF RF _ _ _
      (IsLocalRing.ResidueField.algebra
        (Localization.AtPrime (fiberPrimeAt A (Polynomial A) q).asIdeal))
      (((algebraMap (p.Fiber (Polynomial A)) RF).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra)
      (f := RingEquiv.refl _)
      (fun x ↦ by
        -- The explicit owner terms make this the identity algebra-linearity check.
        rfl)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the polynomial-fiber equivalence
identifies the source fiber-prime residue field with the transported residue field. -/
private noncomputable def fiberPrime_polynomial_transport_default_residueField_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let sourceAlg : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
      ((algebraMap (p.Fiber (Polynomial A))
          (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
    let targetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    @AlgEquiv p.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      Q.asIdeal.ResidueField
      _ _ _ sourceAlg targetAlg :=
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let sourceAlg : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    ((algebraMap (p.Fiber (Polynomial A))
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let targetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let explicitTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
      Polynomial.C).toAlgebra
  -- Route correction: avoid the failed source local-ring owner comparison by using ambient
  -- scalar maps for the residue-field transport, then normalize only the target owner.
  let eTransport :
      @AlgEquiv p.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        Q.asIdeal.ResidueField
        _ _ _ sourceAlg explicitTargetAlg :=
    residueFieldAlgEquivOfComapWithAmbientScalars
      (R := p.ResidueField)
      (e := polynomial_fiber_algEquiv_residueField_polynomial (A := A) p)
      (Q := Q)
      (I := (fiberPrimeAt A (Polynomial A) q).asIdeal)
      (comap_polynomial_fiber_transport_asIdeal_eq_fiberPrimeAt (A := A) q)
  @AlgEquiv.ofRingEquiv p.ResidueField
    (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    Q.asIdeal.ResidueField
    _ _ _ sourceAlg targetAlg
    (f := eTransport.toRingEquiv)
    (fun x ↦ by
      -- The target owner comparison is the residue of the scalar-tower equality in `κ(Q)`.
      have htransport :
          eTransport.toRingEquiv
              (algebraMap p.ResidueField
                (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField x) =
            ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
              Polynomial.C) x := by
        exact eTransport.commutes x
      rw [htransport]
      change
        IsLocalRing.residue (Localization.AtPrime Q.asIdeal)
            (algebraMap (Polynomial p.ResidueField) (Localization.AtPrime Q.asIdeal)
              (Polynomial.C x)) =
          IsLocalRing.residue (Localization.AtPrime Q.asIdeal)
            (algebraMap p.ResidueField (Localization.AtPrime Q.asIdeal) x)
      simpa using congrArg
        (IsLocalRing.residue (Localization.AtPrime Q.asIdeal))
        (IsScalarTower.algebraMap_apply p.ResidueField
          (Polynomial p.ResidueField)
          (Localization.AtPrime Q.asIdeal) x))

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the source fiber-prime residue field is
canonically identified with `κ(q)` over the contracted residue field. -/
private noncomputable def fiberPrime_residueField_algEquiv_base
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (q : PrimeSpectrum B) :
    let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
    let _ : Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := B) q
    (fiberPrimeAt A B q).asIdeal.ResidueField ≃ₐ[
      (PrimeSpectrum.comap (algebraMap A B) q).asIdeal.ResidueField] q.asIdeal.ResidueField := by
  let p : PrimeSpectrum A := PrimeSpectrum.comap (algebraMap A B) q
  let _ : Algebra p.asIdeal.ResidueField (fiberPrimeAt A B q).asIdeal.ResidueField :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := B) q
  -- Repackage the existing ring equivalence with the explicit scalar-compatibility lemma.
  exact
    AlgEquiv.ofRingEquiv
      (f := (fiberPrime_residueField_equiv_source (A := A) (B := B) q).toRingEquiv)
      (fiberPrime_residueField_equiv_source_commutes (A := A) (B := B) q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: in the polynomial case, freeze the
source-side residue-field comparison as a literal `κ(q ∩ A)`-algebra equivalence. -/
private noncomputable def fiberPrime_polynomial_source_residueField_algEquiv
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let sourceAlg : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    let targetAlg : Algebra p.ResidueField q.asIdeal.ResidueField := inferInstance
    @AlgEquiv p.ResidueField
      q.asIdeal.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      _ _ _ targetAlg sourceAlg := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let sourceAlg : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  let targetAlg : Algebra p.ResidueField q.asIdeal.ResidueField := inferInstance
  let _ : Algebra p.ResidueField (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField := sourceAlg
  let _ : Algebra p.ResidueField q.asIdeal.ResidueField := targetAlg
  let e :
      @AlgEquiv p.ResidueField
        (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
        q.asIdeal.ResidueField
        _ _ _ sourceAlg targetAlg :=
    fiberPrime_residueField_algEquiv_base (A := A) (B := Polynomial A) q
  -- Reverse the canonical comparison so it transports `κ(q)` to the fiber-prime residue field.
  exact
    @AlgEquiv.ofRingEquiv p.ResidueField
      q.asIdeal.ResidueField
      (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
      _ _ _ targetAlg sourceAlg e.toRingEquiv.symm
      (fun x ↦ by
        simpa using e.symm.commutes x)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the original polynomial-prime residue
field and the source fiber-prime residue field have the same transcendence degree. -/
private lemma polynomial_source_residueFieldTrdeg_eq_sourceFiber
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    let sourceAlg : Algebra p.ResidueField RF :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (@Algebra.trdeg _ _ _ _ sourceAlg) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
  let sourceAlg : Algebra p.ResidueField RF :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  let eSource :
      @AlgEquiv p.ResidueField q.asIdeal.ResidueField RF
        _ _ _ inferInstance sourceAlg :=
    fiberPrime_polynomial_source_residueField_algEquiv (A := A) q
  -- Transport transcendence degree through the source fiber-prime residue-field equivalence.
  exact congrArg Cardinal.toNat (@AlgEquiv.trdeg_eq _ _ _ _ inferInstance _ _ sourceAlg eSource)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: changing the source fiber-prime
residue-field owner from the explicit source map to the fiber-composite map preserves trdeg. -/
private lemma polynomial_sourceFiberTrdeg_eq_defaultFiberTrdeg
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    let sourceAlg : Algebra p.ResidueField RF :=
      fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
    let defaultSourceAlg : Algebra p.ResidueField RF :=
      ((algebraMap (p.Fiber (Polynomial A)) RF).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
    Cardinal.toNat (@Algebra.trdeg _ _ _ _ sourceAlg) =
      Cardinal.toNat (@Algebra.trdeg _ _ _ _ defaultSourceAlg) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
  let sourceAlg : Algebra p.ResidueField RF :=
    fiberPrime_residueField_baseAlgebra (A := A) (B := Polynomial A) q
  let defaultSourceAlg : Algebra p.ResidueField RF :=
    ((algebraMap (p.Fiber (Polynomial A)) RF).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let eSourceOwner :
      @AlgEquiv p.ResidueField RF RF
        _ _ _ sourceAlg defaultSourceAlg :=
    fiberPrime_polynomial_source_default_residueField_id_algEquiv (A := A) q
  -- The identity equivalence records the owner change on the source fiber-prime residue field.
  exact congrArg Cardinal.toNat
    (@AlgEquiv.trdeg_eq _ _ _ _ sourceAlg _ _ defaultSourceAlg eSourceOwner)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: polynomial fiber transport preserves
the residue-field transcendence degree with default source and target owners. -/
private lemma polynomial_defaultFiberTrdeg_eq_transportLocalTrdeg
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
    let defaultSourceAlg : Algebra p.ResidueField RF :=
      ((algebraMap (p.Fiber (Polynomial A)) RF).comp
        (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
    let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    Cardinal.toNat (@Algebra.trdeg _ _ _ _ defaultSourceAlg) =
      Cardinal.toNat (@Algebra.trdeg _ _ _ _ defaultTargetAlg) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let RF := (fiberPrimeAt A (Polynomial A) q).asIdeal.ResidueField
  let defaultSourceAlg : Algebra p.ResidueField RF :=
    ((algebraMap (p.Fiber (Polynomial A)) RF).comp
      (algebraMap p.ResidueField (p.Fiber (Polynomial A)))).toAlgebra
  let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let eTransport :
      @AlgEquiv p.ResidueField RF Q.asIdeal.ResidueField
        _ _ _ defaultSourceAlg defaultTargetAlg :=
    fiberPrime_polynomial_transport_default_residueField_algEquiv (A := A) q
  -- Apply trdeg invariance to the owner-stable polynomial fiber residue-field transport.
  exact congrArg Cardinal.toNat
    (@AlgEquiv.trdeg_eq _ _ _ _ defaultSourceAlg _ _ defaultTargetAlg eTransport)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: changing the transported target owner
from the local-ring owner to the explicit polynomial owner preserves trdeg. -/
private lemma polynomial_transportLocalTrdeg_eq_explicitTrdeg
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let targetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
        Polynomial.C).toAlgebra
    let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    Cardinal.toNat (@Algebra.trdeg _ _ _ _ defaultTargetAlg) =
      Cardinal.toNat (@Algebra.trdeg _ _ _ _ targetAlg) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let targetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    ((algebraMap (Polynomial p.ResidueField) Q.asIdeal.ResidueField).comp
      Polynomial.C).toAlgebra
  let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let eTargetOwner :
      @AlgEquiv p.ResidueField Q.asIdeal.ResidueField Q.asIdeal.ResidueField
        _ _ _ defaultTargetAlg targetAlg :=
    transported_polynomial_residueField_id_algEquiv (A := A) q
  -- The target owner comparison is an identity equivalence on the residue field.
  exact congrArg Cardinal.toNat
    (@AlgEquiv.trdeg_eq _ _ _ _ defaultTargetAlg _ _ targetAlg eTargetOwner)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the residue-field transcendence
degree is invariant under the polynomial fiber-prime transport. -/
private lemma polynomial_source_residueFieldTrdeg_eq_transport
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    let _ : Algebra p.ResidueField Q.asIdeal.ResidueField := defaultTargetAlg
    Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg p.ResidueField Q.asIdeal.ResidueField) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let _ : Algebra p.ResidueField Q.asIdeal.ResidueField := defaultTargetAlg
  -- Chain the three cached trdeg-invariance steps across source and fiber owners.
  exact
    (polynomial_source_residueFieldTrdeg_eq_sourceFiber (A := A) q).trans
      ((polynomial_sourceFiberTrdeg_eq_defaultFiberTrdeg (A := A) q).trans
        (by
          simpa [p, Q, defaultTargetAlg] using
            polynomial_defaultFiberTrdeg_eq_transportLocalTrdeg (A := A) q))

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the transported prime has the expected
polynomial trdeg branch value with its default residue-field owner. -/
private lemma polynomial_transportTrdeg_eq_branch
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
      IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
    let _ : Algebra p.ResidueField Q.asIdeal.ResidueField := defaultTargetAlg
    Cardinal.toNat (Algebra.trdeg p.ResidueField Q.asIdeal.ResidueField) =
      if Q.asIdeal = ⊥ then 1 else 0 := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let _ : Algebra p.ResidueField Q.asIdeal.ResidueField := defaultTargetAlg
  -- This is the field-polynomial branch computation for the transported prime.
  simpa [Q, defaultTargetAlg] using polynomialTransport_branch_trdeg_values (Q := Q)

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: in the polynomial branch, the
residue-field transcendence-degree term is read off from the transported prime. -/
private lemma polynomial_source_residueFieldTrdeg_eq_branch
    {A : Type*} [CommRing A] (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
      if Q.asIdeal = ⊥ then 1 else 0 := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  let defaultTargetAlg : Algebra p.ResidueField Q.asIdeal.ResidueField :=
    IsLocalRing.ResidueField.algebra (Localization.AtPrime Q.asIdeal)
  let _ : Algebra p.ResidueField Q.asIdeal.ResidueField := defaultTargetAlg
  have htransport :
      Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField Q.asIdeal.ResidueField) := by
    -- First move from the source residue field to the transported polynomial-fiber prime.
    simpa [p, Q] using polynomial_source_residueFieldTrdeg_eq_transport (A := A) q
  have hbranch :
      Cardinal.toNat (Algebra.trdeg p.ResidueField Q.asIdeal.ResidueField) =
        if Q.asIdeal = ⊥ then 1 else 0 := by
    -- The transported prime is a prime of the polynomial ring over the residue field.
    simpa [p, Q] using polynomial_transportTrdeg_eq_branch (A := A) q
  exact htransport.trans hbranch

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: in the polynomial branch, the height
term is the contracted height plus the transported fiber-local branch dimension. -/
private lemma polynomial_height_eq_under_add_branch_dim
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : PrimeSpectrum (Polynomial A)) :
    let p : Ideal A := q.asIdeal.under A
    let _ : p.IsPrime := inferInstance
    let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
      fiberPrime_polynomial_transport (A := A) q
    ENat.toNat (Ideal.primeHeight q.asIdeal) =
      ENat.toNat (Ideal.primeHeight p) + (if Q.asIdeal = ⊥ then 0 else 1) := by
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  have hdim :
      (((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) =
        ((((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) +
          (if Q.asIdeal = ⊥ then 0 else 1)) := by
    calc
      (((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞)
          = ringKrullDim (Localization.AtPrime q.asIdeal) := by
              simpa using
                primeHeightNatCast_eq_ringKrullDim_localizationAtPrime (p := q.asIdeal)
      _ =
          ringKrullDim (Localization.AtPrime p) +
            ringKrullDim (fiberLocalRingAt A (Polynomial A) q) := by
              simpa using
                ringKrullDim_localizationAtPrime_eq_ringKrullDim_localizationAtPrime_under_add_ringKrullDim_fiberLocalRingAt_of_hasGoingDown
                  (R := A) (S := Polynomial A) q
      _ =
          ringKrullDim (Localization.AtPrime p) +
            ringKrullDim (Localization.AtPrime Q.asIdeal) := by
              rw [ringKrullDim_fiberLocalRingAt_polynomial_eq_ringKrullDim_localization_transport
                (A := A) q]
      _ =
          (((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) +
            (if Q.asIdeal = ⊥ then 0 else 1) := by
              rw [primeHeightNatCast_eq_ringKrullDim_localizationAtPrime (p := p)]
              rw [polynomialTransport_branch_ringKrullDim_values (Q := Q)]
  have hsum :
      ((((ENat.toNat (Ideal.primeHeight p) : ℕ) : ℕ∞) : WithBot ℕ∞) +
          (if Q.asIdeal = ⊥ then 0 else 1)) =
        (((ENat.toNat (Ideal.primeHeight p) + (if Q.asIdeal = ⊥ then 0 else 1) : ℕ) : ℕ∞) :
          WithBot ℕ∞) := by
    by_cases hQ : Q.asIdeal = ⊥
    · simp [hQ]
    · simp [hQ]
  -- Convert the normalized `WithBot ℕ∞` equality back to the intended natural-number equality.
  exact_mod_cast (hdim.trans hsum)

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the polynomial source case has total
fiber contribution one. -/
private lemma polynomialBranch_primeHeight_add_residueFieldTrdeg_eq_under_add_one
    {A : Type v} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (q : PrimeSpectrum (Polynomial A)) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
  -- Route correction: the field-polynomial branch arithmetic and branch values are now isolated;
  -- the remaining work is only the owner-stable transport from the canonical fiber prime of
  -- `A[X]` to the transported prime of `κ(q ∩ A)[X]`.
  let p : Ideal A := q.asIdeal.under A
  let _ : p.IsPrime := inferInstance
  let Q : PrimeSpectrum (Polynomial p.ResidueField) :=
    fiberPrime_polynomial_transport (A := A) q
  have hheight :
      ENat.toNat (Ideal.primeHeight q.asIdeal) =
        ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) +
          (if Q.asIdeal = ⊥ then 0 else 1) := by
    -- The height side is Lemma 10.112.7 plus the fiber-local-ring transport to `κ(p)[X]`.
    simpa [p, Q] using polynomial_height_eq_under_add_branch_dim (A := A) q
  have hresidue :
      Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
        if Q.asIdeal = ⊥ then 1 else 0 := by
    -- The residue-field side is invariant under the owner-normalizing algebra-equivalence chain.
    simpa [p, Q] using polynomial_source_residueFieldTrdeg_eq_branch (A := A) q
  -- The two complementary polynomial branch values add to one.
  exact polynomialBranch_values_sum_eq_one hheight hresidue

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: if one element generates the algebra,
then the evaluation map from the polynomial algebra at that element is surjective. -/
private lemma singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) :
    Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] B) := by
  -- The range of `aeval x` is exactly the singleton adjoin generated by `x`.
  exact
    (AlgHom.range_eq_top _).mp
      ((Algebra.adjoin_singleton_eq_range_aeval A x).symm.trans hx)

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: contracting a prime through the
one-generator evaluation presentation and then to the source equals direct contraction. -/
private lemma singleGenerator_comap_under_eq
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    q'.asIdeal.under A = q.asIdeal.under A := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  ext a
  -- Constants in `A[X]` evaluate to the corresponding scalar in `B`.
  change Polynomial.C a ∈ Ideal.comap φ.toRingHom q.asIdeal ↔ algebraMap A B a ∈ q.asIdeal
  rw [Ideal.mem_comap]
  simp [φ]

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the residue-field map induced by a
surjective one-generator presentation is bijective at corresponding primes. -/
private lemma singleGenerator_residueFieldMap_bijective_of_surjective_aeval
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    Function.Bijective (Ideal.ResidueField.map q'.asIdeal q.asIdeal φ rfl) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  have hsurj : Function.Surjective φ :=
    singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  -- Surjectivity passes to stalks and hence to residue fields.
  exact (RingHom.surjectiveOnStalks_of_surjective hsurj).residueFieldMap_bijective _ _ rfl

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the residue-field transcendence term
is unchanged after transporting the target prime back to the polynomial presentation. -/
private lemma singleGenerator_residueFieldTrdeg_eq_comap_of_surjective_aeval
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
    let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
      Cardinal.toNat (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  let p : Ideal A := q'.asIdeal.under A
  letI : q'.asIdeal.LiesOver p := ⟨rfl⟩
  have hp : p = q.asIdeal.under A := by
    -- The polynomial antecedent and the original prime have the same contraction to `A`.
    simpa [p, q'] using singleGenerator_comap_under_eq (A := A) (B := B) x q
  letI : q.asIdeal.LiesOver p := by
    refine ⟨?_⟩
    exact hp
  let f : q'.asIdeal.ResidueField →+* q.asIdeal.ResidueField :=
    Ideal.ResidueField.map q'.asIdeal q.asIdeal φ.toRingHom rfl
  have hf_base :
      f.comp (algebraMap p.ResidueField q'.asIdeal.ResidueField) =
        algebraMap p.ResidueField q.asIdeal.ResidueField := by
    -- Compare the two residue-field maps on representatives coming from the coefficient ring.
    apply Ideal.ResidueField.ringHom_ext (I := p)
    ext a
    calc
      f (algebraMap p.ResidueField q'.asIdeal.ResidueField
          (algebraMap A p.ResidueField a))
          = f (algebraMap A q'.asIdeal.ResidueField a) := by
              rw [IsScalarTower.algebraMap_apply A p.ResidueField
                q'.asIdeal.ResidueField a]
      _ = f (algebraMap (Polynomial A) q'.asIdeal.ResidueField (Polynomial.C a)) := by
              rw [IsScalarTower.algebraMap_apply A (Polynomial A) q'.asIdeal.ResidueField a,
                Polynomial.algebraMap_eq]
      _ = algebraMap B q.asIdeal.ResidueField (φ (Polynomial.C a)) := by
              rw [Ideal.ResidueField.map_algebraMap]
              rfl
      _ = algebraMap B q.asIdeal.ResidueField (algebraMap A B a) := by
              simp [φ]
      _ = algebraMap A q.asIdeal.ResidueField a := by
              rw [IsScalarTower.algebraMap_apply A B q.asIdeal.ResidueField a]
      _ = algebraMap p.ResidueField q.asIdeal.ResidueField
            (algebraMap A p.ResidueField a) := by
              rw [IsScalarTower.algebraMap_apply A p.ResidueField q.asIdeal.ResidueField a]
  let fAlg : q'.asIdeal.ResidueField →ₐ[p.ResidueField] q.asIdeal.ResidueField :=
    { f with
      commutes' := fun r ↦ DFunLike.congr_fun hf_base r }
  let e : q'.asIdeal.ResidueField ≃ₐ[p.ResidueField] q.asIdeal.ResidueField :=
    AlgEquiv.ofBijective fAlg
      (singleGenerator_residueFieldMap_bijective_of_surjective_aeval
        (A := A) (B := B) x hx q)
  have htarget :
      Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q'.asIdeal.ResidueField) := by
    -- Transport transcendence degree across the residue-field algebra equivalence.
    simpa using congrArg Cardinal.toNat (AlgEquiv.trdeg_eq e).symm
  have hleftBase :
      Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := by
    -- Replace the direct contraction by the polynomial-side contraction.
    exact
      (residueFieldTrdeg_toNat_eq_of_base_eq
        (R := A) (A := B) (p := p) (p' := q.asIdeal.under A) (P := q.asIdeal) hp).symm
  -- Assemble the base-prime replacement and the residue-field equivalence.
  calc
    Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.asIdeal.ResidueField) := hleftBase
    _ = Cardinal.toNat (Algebra.trdeg p.ResidueField q'.asIdeal.ResidueField) := htarget
    _ = Cardinal.toNat
          (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
          rfl

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: in the zero-kernel branch of the
one-generator presentation, the generic fraction-field transcendence degree is one. -/
private lemma singleGenerator_fractionRingTrdeg_eq_one_of_ker_eq_bot
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) :
    RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] B).toRingHom = ⊥ →
      Algebra.fractionRingTrdeg hinj = 1 := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  intro hker
  let _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hφ_surj : Function.Surjective φ :=
    singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
  have hφ_inj : Function.Injective φ := by
    -- The zero-kernel branch makes the polynomial presentation an isomorphism.
    rw [RingHom.injective_iff_ker_eq_bot]
    simpa [φ] using hker
  let e : Polynomial A ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  let eFrac : FractionRing (Polynomial A) ≃ₐ[A] FractionRing B :=
    IsFractionRing.algEquivOfAlgEquiv e
  let _ : FaithfulSMul A (Polynomial A) :=
    (faithfulSMul_iff_algebraMap_injective A (Polynomial A)).mpr (by
      simpa using (Polynomial.C_injective (R := A)))
  let _ : FaithfulSMul (Polynomial A) (FractionRing (Polynomial A)) :=
    (faithfulSMul_iff_algebraMap_injective (Polynomial A)
      (FractionRing (Polynomial A))).mpr
      (IsFractionRing.injective (Polynomial A) (FractionRing (Polynomial A)))
  let _ : FaithfulSMul A (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective A (FractionRing A)).mpr
      (IsFractionRing.injective A (FractionRing A))
  have hfracPoly :
      Algebra.trdeg (Polynomial A) (FractionRing (Polynomial A)) = 0 := by
    let _ : Algebra.IsAlgebraic (Polynomial A) (FractionRing (Polynomial A)) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := Polynomial A)
          (K := FractionRing (Polynomial A)) (C := FractionRing (Polynomial A))).mpr
          (inferInstance :
            Algebra.IsAlgebraic (FractionRing (Polynomial A))
              (FractionRing (Polynomial A)))
    -- Passing from a domain to its fraction field adds no transcendence.
    simpa using
      (trdeg_eq_zero :
        Algebra.trdeg (Polynomial A) (FractionRing (Polynomial A)) = 0)
  have hpolyFrac :
      Algebra.trdeg A (FractionRing (Polynomial A)) = 1 := by
    -- Compute `Frac(A[X])` over `A` by the tower `A -> A[X] -> Frac(A[X])`.
    have hsum := trdeg_add_eq (R := A) (S := Polynomial A)
      (A := FractionRing (Polynomial A))
    rw [Polynomial.trdeg_of_isDomain, hfracPoly] at hsum
    simpa using hsum.symm
  have hAFracA :
      Algebra.trdeg A (FractionRing A) = 0 := by
    let _ : Algebra.IsAlgebraic A (FractionRing A) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing A) = 0)
  have hAFracB :
      Algebra.trdeg A (FractionRing B) = 1 := by
    -- Transport the polynomial computation across the one-generator presentation.
    calc
      Algebra.trdeg A (FractionRing B)
          = Algebra.trdeg A (FractionRing (Polynomial A)) := by
              simpa using (AlgEquiv.trdeg_eq (R := A) eFrac).symm
      _ = 1 := hpolyFrac
  have hFrac :
      Algebra.trdeg (FractionRing A) (FractionRing B) = 1 := by
    -- Algebraic base change from `A` to `Frac(A)` does not change the generic term.
    have hsum := trdeg_add_eq (R := A) (S := FractionRing A) (A := FractionRing B)
    rw [hAFracA, hAFracB] at hsum
    simpa using hsum
  change Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 1
  simpa [hFrac] using rfl

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: in the nonzero-kernel branch of the
one-generator presentation, the generic fraction-field transcendence degree is zero. -/
private lemma singleGenerator_fractionRingTrdeg_eq_zero_of_ker_ne_bot
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) :
    RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] B).toRingHom ≠ ⊥ →
      Algebra.fractionRingTrdeg hinj = 0 := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  intro hker
  let _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  let _ : FaithfulSMul A (FractionRing A) :=
    (faithfulSMul_iff_algebraMap_injective A (FractionRing A)).mpr
      (IsFractionRing.injective A (FractionRing A))
  have hxAlg : IsAlgebraic A x := by
    -- A nonzero kernel gives a nontrivial polynomial relation for `x`.
    rw [isAlgebraic_iff_not_injective]
    intro hφ_inj
    apply hker
    rw [RingHom.injective_iff_ker_eq_bot] at hφ_inj
    simpa [φ] using hφ_inj
  have hBAlg : Algebra.IsAlgebraic A B := by
    -- Since `B = A[x]`, algebraicity of the generator makes all of `B` algebraic.
    refine Algebra.isAlgebraic_iff.2 ?_
    rw [← hx]
    refine (Algebra.isAlgebraic_adjoin_iff (R := A) (s := ({x} : Set B))).2 ?_
    intro y hy
    simpa [Set.mem_singleton_iff.mp hy] using hxAlg
  have hAFracB :
      Algebra.trdeg A (FractionRing B) = 0 := by
    let _ : Algebra.IsAlgebraic A B := hBAlg
    let _ : Algebra.IsAlgebraic B (FractionRing B) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := B) (K := FractionRing B)
          (C := FractionRing B)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing B) (FractionRing B))
    let _ : Algebra.IsAlgebraic A (FractionRing B) :=
      Algebra.IsAlgebraic.trans (R := A) (S := B) (A := FractionRing B)
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing B) = 0)
  have hAFracA :
      Algebra.trdeg A (FractionRing A) = 0 := by
    let _ : Algebra.IsAlgebraic A (FractionRing A) := by
      exact
        (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := FractionRing A)
          (C := FractionRing A)).mpr
          (inferInstance : Algebra.IsAlgebraic (FractionRing A) (FractionRing A))
    simpa using
      (trdeg_eq_zero : Algebra.trdeg A (FractionRing A) = 0)
  have hFrac :
      Algebra.trdeg (FractionRing A) (FractionRing B) = 0 := by
    -- The algebraic top extension forces the fraction-field generic term to vanish.
    have hsum := trdeg_add_eq (R := A) (S := FractionRing A) (A := FractionRing B)
    rw [hAFracA, hAFracB] at hsum
    simpa using hsum
  change Cardinal.toNat (Algebra.trdeg (FractionRing A) (FractionRing B)) = 0
  simpa [hFrac] using rfl

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: in the nonzero-kernel quotient case,
the target prime height is at most one less than the height of its polynomial antecedent. -/
private lemma singleGenerator_quotientCase_primeHeight_succ_le_comap_primeHeight
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤) (q : PrimeSpectrum B) :
    RingHom.ker (Polynomial.aeval x : Polynomial A →ₐ[A] B).toRingHom ≠ ⊥ →
      ENat.toNat (Ideal.primeHeight q.asIdeal) + 1 ≤
        ENat.toNat
          (Ideal.primeHeight
            (PrimeSpectrum.comap
              (Polynomial.aeval x : Polynomial A →ₐ[A] B).toRingHom q).asIdeal) := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  letI : Algebra.FiniteType A B := by
    -- Singleton generation supplies the finite-type target instance needed for Noetherian heights.
    have hfgTop : (⊤ : Subalgebra A B).FG :=
      Subalgebra.fg_def.2 ⟨({x} : Set B), Set.finite_singleton x, hx⟩
    exact ⟨hfgTop⟩
  letI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  let L := Localization.AtPrime q'.asIdeal
  let K : Ideal L := Ideal.map (algebraMap (Polynomial A) L) n
  intro hn
  let e :
      Localization.AtPrime q.asIdeal ≃ₐ[A] (L ⧸ K) :=
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    let hφ_surj : Function.Surjective φ :=
      singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
    let hφloc_surj : Function.Surjective φloc := by
      -- Localizing a surjective map at corresponding primes stays surjective on the local rings.
      simpa [φloc, Localization.localAlgHom] using
        (RingHom.surjectiveOnStalks_of_surjective hφ_surj).localRingHom_surjective
          q'.asIdeal q.asIdeal rfl
    let hprimeCompl :
        Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
      -- The localized source and target use the corresponding prime complements.
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        simpa [q', Ideal.mem_comap] using hg
      · intro hf
        rcases hφ_surj f with ⟨g, rfl⟩
        exact ⟨g, by simpa [q', Ideal.mem_comap] using hf, rfl⟩
    let hker :
        RingHom.ker φloc.toRingHom = K := by
      -- The kernel of the localized map is exactly the localization of the original kernel.
      dsimp [φloc, K, n]
      simpa [Localization.localAlgHom, Localization.localRingHom] using
        (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
          φ.toRingHom hprimeCompl)
    -- Repackage the localized surjection as the quotient by its kernel, then rewrite that kernel to
    -- the literal localized ideal `K`.
    (Ideal.quotientKerAlgEquivOfSurjective hφloc_surj).symm.trans
      (Ideal.quotientEquivAlgOfEq A hker)
  have hdrop :
      ringKrullDim (L ⧸ K) + 1 ≤ ringKrullDim L := by
    let φloc : L →ₐ[A] Localization.AtPrime q.asIdeal :=
      Localization.localAlgHom q'.asIdeal q.asIdeal φ rfl
    have hprimeCompl :
        Submonoid.map φ.toRingHom q'.asIdeal.primeCompl = q.asIdeal.primeCompl := by
      -- The local source and target are localized at the corresponding primes of `aeval x`.
      ext f
      constructor
      · rintro ⟨g, hg, rfl⟩
        simpa [q', Ideal.mem_comap] using hg
      · intro hf
        have hφ_surj : Function.Surjective φ :=
          singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
        rcases hφ_surj f with ⟨g, rfl⟩
        exact ⟨g, by simpa [q', Ideal.mem_comap] using hf, rfl⟩
    have hker :
        RingHom.ker φloc.toRingHom = K := by
      -- Localization turns `ker φ` into the localized ideal `K`.
      dsimp [φloc, K, n]
      simpa [Localization.localAlgHom, Localization.localRingHom] using
        (IsLocalization.ker_map (S := L) (Q := Localization.AtPrime q.asIdeal)
          φ.toRingHom hprimeCompl)
    have hK_prime : K.IsPrime := by
      -- The kernel of a map to the domain `B_q` is prime, hence so is `K`.
      rw [← hker]
      exact RingHom.ker_isPrime φloc.toRingHom
    have hK_ne_bot : K ≠ ⊥ := by
      -- The localization map is injective on the domain `A[X]`, so a nonzero kernel element stays
      -- nonzero after localization.
      have hL_inj : Function.Injective (algebraMap (Polynomial A) L) :=
        IsLocalization.injective L q'.asIdeal.primeCompl_le_nonZeroDivisors
      exact (Ideal.map_eq_bot_iff_of_injective hL_inj).not.mpr hn
    let P : PrimeSpectrum (Localization.AtPrime q'.asIdeal) := ⟨K, hK_prime⟩
    let _ : Nonempty (PrimeSpectrum (Localization.AtPrime q'.asIdeal)) := ⟨P⟩
    have hP_bot : (⊥ : PrimeSpectrum (Localization.AtPrime q'.asIdeal)) < P := by
      change (⊥ : Ideal (Localization.AtPrime q'.asIdeal)) < K
      exact bot_lt_iff_ne_bot.mpr hK_ne_bot
    have hheight_pos : 1 ≤ Order.height P := by
      -- Strictly lying over the zero prime means the height is positive, i.e. at least one.
      simpa [Order.one_le_iff_pos] using Order.height_pos_of_bot_lt hP_bot
    have hquot :
        ringKrullDim (L ⧸ K) = Order.coheight P := by
      -- Quotient Krull dimension is the coheight of the corresponding prime.
      rw [ringKrullDim_quotient]
      have hzero : PrimeSpectrum.zeroLocus (K : Set L) = Set.Ici P := by
        ext r
        change K ≤ r.asIdeal ↔ P ≤ r
        rfl
      rw [hzero]
      exact (Order.coheight_eq_krullDim_Ici P).symm
    have hsum :
        (((Order.coheight P + 1 : ℕ∞)) : WithBot ℕ∞) ≤
          (((Order.height P + Order.coheight P : ℕ∞)) : WithBot ℕ∞) := by
      -- A nonzero prime has positive height, so its height-plus-coheight term dominates
      -- `coheight + 1`.
      exact_mod_cast
        (show Order.coheight P + 1 ≤ Order.height P + Order.coheight P by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hheight_pos (Order.coheight P))
    have hdim :
        (((Order.height P + Order.coheight P : ℕ∞)) : WithBot ℕ∞) ≤ ringKrullDim L := by
      -- The ambient Krull dimension dominates the height-plus-coheight of every prime.
      rw [ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
      exact WithBot.coe_le_coe.mpr
        (le_iSup (fun r : PrimeSpectrum L ↦ Order.height r + Order.coheight r) P)
    calc
      ringKrullDim (L ⧸ K) + 1
          = (((Order.coheight P + 1 : ℕ∞)) : WithBot ℕ∞) := by
              rw [hquot]
              simp
      _ ≤ (((Order.height P + Order.coheight P : ℕ∞)) : WithBot ℕ∞) := hsum
      _ ≤ ringKrullDim L := hdim
  have hlocal :
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1 ≤
        ringKrullDim (Localization.AtPrime q'.asIdeal) := by
    -- Transport the quotient-side local dimension drop back to `B_q`.
    calc
      ringKrullDim (Localization.AtPrime q.asIdeal) + 1
          = ringKrullDim (L ⧸ K) + 1 := by
              rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv]
      _ ≤ ringKrullDim L := hdrop
      _ = ringKrullDim (Localization.AtPrime q'.asIdeal) := by
            rfl
  have hheight :
      ((((ENat.toNat (Ideal.primeHeight q.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) + 1) ≤
        (((ENat.toNat (Ideal.primeHeight q'.asIdeal) : ℕ) : ℕ∞) : WithBot ℕ∞) := by
    -- Rewrite both local dimensions as prime heights.
    rw [primeHeightNatCast_eq_ringKrullDim_localizationAtPrime (p := q.asIdeal)]
    rw [primeHeightNatCast_eq_ringKrullDim_localizationAtPrime (p := q'.asIdeal)]
    simpa [L] using hlocal
  -- Convert the cast inequality back to natural numbers.
  exact_mod_cast hheight

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the dimension inequality for a
single-generator extension. -/
private lemma singleGenerator_primeHeightResidueFieldTrdeg_le
    {A : Type v} {B : Type v} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
    [IsNoetherianRing A] [Algebra A B]
    (x : B) (hx : Algebra.adjoin A ({x} : Set B) = ⊤)
    (hinj : Function.Injective (algebraMap A B)) (q : PrimeSpectrum B) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) +
        Algebra.fractionRingTrdeg hinj := by
  let φ : Polynomial A →ₐ[A] B := Polynomial.aeval x
  let n : Ideal (Polynomial A) := RingHom.ker φ.toRingHom
  let q' : PrimeSpectrum (Polynomial A) := PrimeSpectrum.comap φ.toRingHom q
  by_cases hker : n = ⊥
  · have hgeneric :
        Algebra.fractionRingTrdeg hinj = 1 :=
      singleGenerator_fractionRingTrdeg_eq_one_of_ker_eq_bot
        (A := A) (B := B) x hx hinj hker
    have hφ_surj : Function.Surjective φ :=
      singleGenerator_aeval_surjective_of_adjoin_singleton_eq_top (A := A) x hx
    have hφ_inj : Function.Injective φ := by
      rw [RingHom.injective_iff_ker_eq_bot]
      simpa [φ, n] using hker
    let e : Polynomial A ≃ₐ[A] B := AlgEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
    have hheight :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) =
          ENat.toNat (Ideal.primeHeight q.asIdeal) := by
      -- The zero-kernel presentation identifies the polynomial antecedent prime with `q`.
      have hheight_eq : q'.asIdeal.height = q.asIdeal.height := by
        simpa only [q', e] using
          (RingEquiv.height_comap e.toRingEquiv q.asIdeal)
      exact congrArg ENat.toNat (by
        simpa [Ideal.height_eq_primeHeight] using hheight_eq)
    have hres :
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          Cardinal.toNat
            (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) :=
      singleGenerator_residueFieldTrdeg_eq_comap_of_surjective_aeval
        (A := A) (B := B) x hx q
    have hunder : q'.asIdeal.under A = q.asIdeal.under A :=
      singleGenerator_comap_under_eq (A := A) (B := B) x q
    have hpoly :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) =
          ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 :=
      polynomialBranch_primeHeight_add_residueFieldTrdeg_eq_under_add_one (A := A) q'
    apply le_of_eq
    -- Transport the left side to the polynomial presentation and consume the polynomial normal
    -- form; the generic term is `1` in this branch.
    calc
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField)
        = ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) := by
                rw [← hheight, hres]
      _ = ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 := hpoly
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
            have hunderHeight :
                ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) =
                  ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) := by
              have hheight_under :
                  (q'.asIdeal.under A).height = (q.asIdeal.under A).height :=
                congrArg Ideal.height hunder
              exact congrArg ENat.toNat (by
                simpa [Ideal.height_eq_primeHeight] using hheight_under)
            rw [hunderHeight]
      _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) +
            Algebra.fractionRingTrdeg hinj := by simpa [hgeneric]
  · have hgeneric :
        Algebra.fractionRingTrdeg hinj = 0 :=
      singleGenerator_fractionRingTrdeg_eq_zero_of_ker_ne_bot
        (A := A) (B := B) x hx hinj hker
    have hres :
        Cardinal.toNat (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          Cardinal.toNat
            (Algebra.trdeg (q'.asIdeal.under A).ResidueField q'.asIdeal.ResidueField) :=
      singleGenerator_residueFieldTrdeg_eq_comap_of_surjective_aeval
        (A := A) (B := B) x hx q
    have hheight :
        ENat.toNat (Ideal.primeHeight q.asIdeal) + 1 ≤
          ENat.toNat (Ideal.primeHeight q'.asIdeal) :=
      singleGenerator_quotientCase_primeHeight_succ_le_comap_primeHeight
        (A := A) (B := B) x hx q hker
    have hpoly :
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) =
          ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
      -- The nonzero-kernel branch uses the same polynomial normal form after residue transport.
      calc
        ENat.toNat (Ideal.primeHeight q'.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField)
          = ENat.toNat (Ideal.primeHeight q'.asIdeal) +
              Cardinal.toNat
                (Algebra.trdeg (q'.asIdeal.under A).ResidueField
                  q'.asIdeal.ResidueField) := by rw [hres]
        _ = ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) + 1 :=
              polynomialBranch_primeHeight_add_residueFieldTrdeg_eq_under_add_one (A := A) q'
        _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) + 1 := by
              have hunder : q'.asIdeal.under A = q.asIdeal.under A :=
                singleGenerator_comap_under_eq (A := A) (B := B) x q
              have hunderHeight :
                  ENat.toNat (Ideal.primeHeight (q'.asIdeal.under A)) =
                    ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) := by
                have hheight_under :
                    (q'.asIdeal.under A).height = (q.asIdeal.under A).height :=
                  congrArg Ideal.height hunder
                exact congrArg ENat.toNat (by
                  simpa [Ideal.height_eq_primeHeight] using hheight_under)
              rw [hunderHeight]
    have hgoal :
        ENat.toNat (Ideal.primeHeight q.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under A).ResidueField q.asIdeal.ResidueField) ≤
          ENat.toNat (Ideal.primeHeight (q.asIdeal.under A)) := by
      omega
    simpa [hgeneric] using hgoal

omit [Algebra (FractionRing R) (FractionRing S)]
    [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: adjoining finitely many generators one
at a time gives the finite-stage dimension inequality. -/
private theorem adjoinFinset_primeHeightResidueFieldTrdeg_le
    [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R S)) (s : Finset S) :
    ∀ q : PrimeSpectrum (Algebra.adjoin R (s : Set S)),
      ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
        ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
          Algebra.fractionRingTrdeg
            (R := R) (S := Algebra.adjoin R (s : Set S))
            (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj s) := by
  classical
  -- Induct on the displayed finite generating set; the insert step is the isolated
  -- one-generator inequality over the previous finite stage.
  induction s using Finset.induction_on with
  | empty =>
      intro q
      have hbase :
          ENat.toNat (Ideal.primeHeight q.asIdeal) +
              Cardinal.toNat
                (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
            ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) := by
        -- The empty `Finset` stage is the bottom subalgebra over the base.
        exact adjoinFinsetEmpty_primeHeightResidueFieldTrdeg_eq (R := R) (S := S) hinj q
      have hgeneric :=
        adjoinEmpty_fractionRingTrdeg_eq_zero (R := R) (S := S) hinj
      -- The empty stage is identified with the source ring, and its generic contribution is zero.
      omega
  | @insert x t hxnotin ih =>
      set T : Subalgebra R S := Algebra.adjoin R (t : Set S)
      set A : Subalgebra R S := Algebra.adjoin R (((insert x t : Finset S) : Set S))
      have hTA : T ≤ A := by
        -- The old finite stage embeds in the stage with the inserted generator.
        simpa [T, A] using adjoinFinset_le_insert_adjoinFinset (R := R) (S := S) t x
      letI : Algebra T A := (Subalgebra.inclusion hTA).toAlgebra
      letI : IsScalarTower R T A := IsScalarTower.of_algebraMap_eq' rfl
      letI : IsNoetherianRing T := by
        simpa [T] using adjoinFinset_isNoetherianRing (R := R) (S := S) t
      letI : Algebra.FiniteType R T := by
        simpa [T] using adjoinFinset_finiteType (R := R) (S := S) t
      have hTA_inj : Function.Injective (algebraMap T A) :=
        Subalgebra.inclusion_injective hTA
      have hxA_mem : x ∈ A := by
        -- Package the newly inserted ambient element as an element of the inserted stage.
        simpa [A] using insertedElement_mem_adjoinFinsetStage (R := R) (S := S) t x
      let xA : A := ⟨x, hxA_mem⟩
      have hxA : Algebra.adjoin T ({xA} : Set A) = ⊤ := by
        -- The inserted stage is generated over the old stage by this single element.
        simpa [T, A, hTA, xA, hxA_mem] using
          adjoinSingleton_eq_top_over_adjoinFinsetStage (R := R) (S := S) t x
      letI : Algebra.FiniteType T A := by
        -- Convert the singleton generation statement into the finite-type instance needed for
        -- residue-field and fraction-field tower additivity.
        have hfgTop : (⊤ : Subalgebra T A).FG :=
          Subalgebra.fg_def.2 ⟨({xA} : Set A), Set.finite_singleton xA, hxA⟩
        have hftTop : Algebra.FiniteType T (⊤ : Subalgebra T A) :=
          (Subalgebra.fg_iff_finiteType (R := T) (A := A) (⊤ : Subalgebra T A)).mp hfgTop
        exact Algebra.FiniteType.equiv hftTop Subalgebra.topEquiv
      intro q
      let qT : PrimeSpectrum T := PrimeSpectrum.comap (algebraMap T A) q
      have hRT :
          ENat.toNat (Ideal.primeHeight qT.asIdeal) +
              Cardinal.toNat
                (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) ≤
            ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              Algebra.fractionRingTrdeg
                (R := R) (S := T)
                (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj t) := by
        -- Apply the induction hypothesis to the contraction of `q` on the previous stage.
        simpa [T, qT] using ih qT
      have hTS :
          ENat.toNat (Ideal.primeHeight q.asIdeal) +
              Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) ≤
            ENat.toNat (Ideal.primeHeight qT.asIdeal) +
              Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj := by
        -- The inserted generator contributes through the one-generator inequality over `T`.
        simpa [qT, xA] using
          singleGenerator_primeHeightResidueFieldTrdeg_le
            (A := T) (B := A) xA hxA hTA_inj q
      have hres :
          Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) =
            Cardinal.toNat
                (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
              Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField) := by
        -- Split the residue-field extension through the intermediate finite stage.
        simpa [qT] using residueFieldTrdeg_tower_eq (R := R) (T := T) (U := A) q
      have hfrac :
          Algebra.fractionRingTrdeg
              (R := R) (S := A)
              (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj (insert x t)) =
            Algebra.fractionRingTrdeg
                (R := R) (S := T)
                (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj t) +
              Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj := by
        -- Split the generic fraction-field transcendence degree along the same tower.
        simpa [T, A] using
          fractionRingTrdeg_tower_eq
            (R := R) (T := T) (U := A)
            (hinjRT := adjoinFinset_algebraMap_injective (R := R) (S := S) hinj t)
            (hinjTU := hTA_inj)
            (hinjRU := adjoinFinset_algebraMap_injective (R := R) (S := S) hinj (insert x t))
      have hunder : qT.asIdeal.under R = q.asIdeal.under R := by
        -- Contracting through the previous stage and then to the base is direct contraction.
        exact comap_under_eq_under_in_tower (R := R) (T := T) (U := A) q
      have hunderHeight :
          ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) =
            ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) := by
        -- Rewrite the dependent prime-height expression by substituting the contracted ideal.
        cases hunder
        rfl
      have hstep :
          ENat.toNat (Ideal.primeHeight q.asIdeal) +
              (Cardinal.toNat
                  (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
                Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField)) ≤
            ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              (Algebra.fractionRingTrdeg
                  (R := R) (S := T)
                  (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj t) +
                Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj) :=
        towerStep_primeHeightResidueFieldTrdeg_le hRT hTS
      -- Reassemble the two tower decompositions into the desired inserted-stage inequality.
      calc
        ENat.toNat (Ideal.primeHeight q.asIdeal) +
            Cardinal.toNat
              (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
          =
            ENat.toNat (Ideal.primeHeight q.asIdeal) +
              (Cardinal.toNat
                  (Algebra.trdeg (qT.asIdeal.under R).ResidueField qT.asIdeal.ResidueField) +
                Cardinal.toNat (Algebra.trdeg qT.asIdeal.ResidueField q.asIdeal.ResidueField)) := by
                  rw [hres]
        _ ≤ ENat.toNat (Ideal.primeHeight (qT.asIdeal.under R)) +
              (Algebra.fractionRingTrdeg
                  (R := R) (S := T)
                  (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj t) +
                Algebra.fractionRingTrdeg (R := T) (S := A) hTA_inj) := hstep
        _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
              Algebra.fractionRingTrdeg
                (R := R) (S := A)
                (adjoinFinset_algebraMap_injective (R := R) (S := S) hinj (insert x t)) := by
                  rw [hunderHeight, ← hfrac]

/-- Chap10 Lemma 10 113 1 DimensionInequality: explicit finite-adjoin version of the owner-form
dimension inequality. -/
private theorem primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_fractionRing_trdeg_of_adjoin_eq_top
    [IsNoetherianRing R]
    (hinj : Function.Injective (algebraMap R S)) {s : Finset S}
    (hs : Algebra.adjoin R (s : Set S) = ⊤) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  -- Route correction: importing `stacks_project.Chap10.Lemma_10_113_1` as the predecessor owner
  -- was tested and is currently blocked because that aggregate source module itself does not
  -- compile. The remaining dependency-closed obligation is therefore still the finite-adjoin
  -- dimension inequality, not just a terminal rewrite.
  let A : Subalgebra R S := Algebra.adjoin R (s : Set S)
  let eStage : A ≃ₐ[R] S := (Subalgebra.equivOfEq A ⊤ hs).trans Subalgebra.topEquiv
  let qA : PrimeSpectrum A := PrimeSpectrum.comap eStage.toRingHom q
  let hRA : Function.Injective (algebraMap R A) :=
    adjoinFinset_algebraMap_injective (R := R) (S := S) hinj s
  have hleft :
      ENat.toNat (Ideal.primeHeight qA.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) =
        ENat.toNat (Ideal.primeHeight q.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) := by
    -- The terminal-stage equivalence has already absorbed the height and residue-field transports.
    simpa [A, eStage, qA] using
      adjoinStage_leftSide_eq (R := R) (S := S) hs q
  have hunderHeightStage :
      ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) =
        ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) := by
    -- The base-height term is now normalized by a standalone transport helper.
    simpa [A, eStage, qA] using
      adjoinStage_under_primeHeight_toNat_eq (R := R) (S := S) hs q
  have hfracStage :
      Algebra.fractionRingTrdeg
          (R := R) (S := A) hRA =
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
    -- The terminal-stage equality also identifies the generic fraction-field contribution.
    simpa [A, hRA] using
      adjoinStage_fractionRingTrdeg_eq_cardinalToNat_trdeg
        (R := R) (S := S) hinj hs
  have hstage :
      ENat.toNat (Ideal.primeHeight qA.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) ≤
        ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) +
          Algebra.fractionRingTrdeg (R := R) (S := A) hRA := by
    -- The finite-stage induction is now the only input needed before the terminal transports.
    simpa [A, qA, hRA] using
      adjoinFinset_primeHeightResidueFieldTrdeg_le (R := R) (S := S) hinj s qA
  -- Apply the finite-stage inequality and then rewrite the three terminal transport terms.
  calc
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField)
      = ENat.toNat (Ideal.primeHeight qA.asIdeal) +
          Cardinal.toNat
            (Algebra.trdeg (qA.asIdeal.under R).ResidueField qA.asIdeal.ResidueField) := hleft.symm
    _ ≤ ENat.toNat (Ideal.primeHeight (qA.asIdeal.under R)) +
          Algebra.fractionRingTrdeg (R := R) (S := A) hRA := hstage
    _ = ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
            rw [hunderHeightStage, hfracStage]

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the owner-form finite-type dimension inequality follows
from the explicit finite-adjoin-stage theorem by choosing finite generators. -/
private theorem finiteType_primeHeight_add_residueFieldTrdeg_le_under_add_fractionRing_trdeg
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  -- Choose a finite generating stage for the finite-type algebra and consume the explicit
  -- finite-adjoin theorem. This fixes the previous reversed dependency direction.
  obtain ⟨s, hs⟩ := existsFinset_adjoin_eq_top_of_finiteType (R := R) (S := S)
  exact
    primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_fractionRing_trdeg_of_adjoin_eq_top
      (R := R) (S := S) hinj hs q

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the prime-spectrum owner form of the finite-type
dimension inequality, with the source prime represented as the contraction of `q`. -/
private theorem primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_fractionRing_trdeg_of_finiteType
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (q : PrimeSpectrum S) :
    ENat.toNat (Ideal.primeHeight q.asIdeal) +
        Cardinal.toNat
          (Algebra.trdeg (q.asIdeal.under R).ResidueField q.asIdeal.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight (q.asIdeal.under R)) +
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  -- Reduce the finite-type source to a chosen finite adjoin stage; the remaining blocker is now
  -- the explicit finite-stage induction and terminal transport lemma above.
  obtain ⟨s, hs⟩ := existsFinset_adjoin_eq_top_of_finiteType (R := R) (S := S)
  exact
    primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_fractionRing_trdeg_of_adjoin_eq_top
      (R := R) (S := S) hinj hs q

omit [IsDomain R] [IsDomain S] [IsScalarTower R (FractionRing R) (FractionRing S)] in
/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: transport the owner-form inequality from the contracted
source prime `q.under R` to any explicitly supplied lying-over prime `p`. -/
private lemma primeHeight_add_residueFieldTrdeg_le_of_under_bound
    {p : Ideal R} [p.IsPrime] {q : Ideal S} [q.IsPrime] (hq : q.LiesOver p)
    (hunder :
      ENat.toNat (Ideal.primeHeight q) +
          Cardinal.toNat (Algebra.trdeg (q.under R).ResidueField q.ResidueField) ≤
        ENat.toNat (Ideal.primeHeight (q.under R)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S))) :
    ENat.toNat (Ideal.primeHeight q) +
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight p) +
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  -- Replace the explicitly named base prime by the contraction supplied by the lies-over witness.
  have hp : p = q.under R := by
    simpa using hq.over
  subst p
  simpa using hunder

/-- Helper for Chap10 Lemma 10 113 1 DimensionInequality: the finite-type dimension inequality
comparing prime height, residue-field transcendence degree, and the concrete fraction-field
transcendence degree. -/
theorem primeHeight_add_residueFieldTrdeg_le_primeHeight_add_fractionRing_trdeg_of_finiteType
    [IsNoetherianRing R] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S)) (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] (hq : q.LiesOver p) :
    ENat.toNat (Ideal.primeHeight q) +
        Cardinal.toNat (Algebra.trdeg p.ResidueField q.ResidueField) ≤
      ENat.toNat (Ideal.primeHeight p) +
        Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
  -- First apply the owner-form inequality at the prime spectrum point attached to `q`.
  have hunder :
      ENat.toNat (Ideal.primeHeight q) +
          Cardinal.toNat (Algebra.trdeg (q.under R).ResidueField q.ResidueField) ≤
        ENat.toNat (Ideal.primeHeight (q.under R)) +
          Cardinal.toNat (Algebra.trdeg (FractionRing R) (FractionRing S)) := by
    simpa using
      primeHeight_add_residueFieldTrdeg_le_primeHeight_under_add_fractionRing_trdeg_of_finiteType
        (R := R) (S := S) hinj (⟨q, inferInstance⟩ : PrimeSpectrum S)
  -- Then use the lies-over proof to identify the contracted source prime with the supplied `p`.
  exact primeHeight_add_residueFieldTrdeg_le_of_under_bound (R := R) (S := S) hq hunder

end
