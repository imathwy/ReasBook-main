import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_154_2
import stacks_proof.stacks_project.Chap10.Lemma_10_155_6
import stacks_proof.stacks_project.Chap10.Lemma_10_155_10
import stacks_proof.stacks_project.Chap10.Lemma_10_137_2
import stacks_proof.stacks_project.Chap10.Definition_10_137_10
import stacks_proof.stacks_project.Chap15.Definition_15_107_6
import stacks_proof.stacks_project.Chap15.Lemma_15_51_11

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u v

section

/-
Domain-style sampling:
- primary domain: local commutative algebra of henselizations, strict henselizations, minimal
  primes, and smoothness at the closed point;
- sampled owner declarations of the same kind:
  `branchNumber`,
  `geometricBranchNumber`,
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`;
- best owner abstraction: the source-facing branch-count equalities should stay expressed in terms
  of the chapter owners `branchNumber` / `geometricBranchNumber` with the source-facing smoothness
  hypothesis `Algebra.SmoothAtPrime A B (closedPoint B)`, while henselization and strict
  henselization remain primitive ambient data through `IsHenselizationOf` and
  `IsStrictHenselizationOf`;
- primitive data: a local homomorphism `A → B` of local rings, a chosen henselization or strict
  henselization on each side, the source-facing closed-point smoothness hypothesis, and in clause
  `(2)` the purely inseparable residue-field extension;
- derived API: the equalities comparing the branch and geometric-branch counts.

Source/core/bridge triage:
- `source-facing`: the two branch-count invariance statements below;
- `core/canonical`: `branchNumber`, `geometricBranchNumber`, `IsHenselizationOf`,
  `IsStrictHenselizationOf`, and the canonical local smoothness owner `IsSmoothAt`;
- `bridge/view`: `Algebra.smoothAtPrime_iff_isSmoothAt`, which justifies keeping
  `Algebra.SmoothAtPrime` as the source-facing hypothesis rather than introducing a parallel local
  reformulation.
-/

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A]
variable [CommRing B] [IsLocalRing B]
variable [Algebra A B] [IsLocalHom (algebraMap A B)]

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- Helper for Lemma 15.107.8: in a local target ring, smoothness at the closed point upgrades to
global smoothness because the witnessing localization is taken away from a unit. -/
lemma smooth_of_smoothAtPrime_closedPoint
    (hsmooth : Algebra.SmoothAtPrime A B (closedPoint B)) :
    Algebra.Smooth A B := by
  rcases hsmooth with ⟨g, hg, hsmoothAway⟩
  have hg_not_mem_maximal : g ∉ maximalIdeal B := by
    simpa [closedPoint_asIdeal_eq_maximalIdeal] using hg
  have hg_unit : IsUnit g := by
    -- In a local ring, an element outside the maximal ideal is a unit.
    by_contra hg_nonunit
    exact hg_not_mem_maximal <| by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hg_nonunit
  let e : Localization.Away g ≃ₐ[A] B :=
    (AlgEquiv.restrictScalars A <|
      (IsLocalization.atUnit B (Localization.Away g) g hg_unit).symm)
  let _ : Algebra.Smooth A (Localization.Away g) := hsmoothAway
  -- Transport the smooth away-localization model back across the at-unit equivalence.
  exact Algebra.Smooth.of_equiv e

omit [IsLocalRing A] in
/-- Helper for Lemma 15.107.8: contraction of a minimal prime along a faithfully flat algebra map
is again a minimal prime. -/
lemma comap_mem_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) {Q : Ideal S}
    (hQ : Q ∈ minimalPrimes S) :
    Ideal.comap (algebraMap R S) Q ∈ minimalPrimes R := by
  have hflat : (algebraMap R S).Flat := hff.flat
  let _ : Module.Flat R S := RingHom.flat_algebraMap_iff.mp hflat
  change Ideal.comap (algebraMap R S) Q ∈ (⊥ : Ideal R).minimalPrimes
  have hQ' : Q ∈ (⊥ : Ideal S).minimalPrimes := by
    simpa [minimalPrimes] using hQ
  have hQ_prime : Q.IsPrime := Ideal.minimalPrimes_isPrime hQ'
  let _ : Q.IsPrime := hQ_prime
  have hcomap_prime : (Ideal.comap (algebraMap R S) Q).IsPrime := by
    simpa using Ideal.comap_isPrime (algebraMap R S) Q
  -- Going down for the flat map shows that no smaller prime can contract to the same ideal.
  refine ⟨⟨hcomap_prime, bot_le⟩, ?_⟩
  intro J hJ hJ_le
  by_cases hQJ : Ideal.comap (algebraMap R S) Q = J
  · exact hQJ.le
  · let _ : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
    let _ : J.IsPrime := hJ.1
    let _ : Q.IsPrime := hQ_prime
    let _ : Q.LiesOver (Ideal.comap (algebraMap R S) Q) := ⟨rfl⟩
    have hJ_lt_Q :
        J < Ideal.comap (algebraMap R S) Q :=
      lt_of_le_of_ne hJ_le (Ne.symm hQJ)
    -- The resulting smaller prime below `Q` contradicts minimality of `Q`.
    obtain ⟨Q', hQ'_lt, hQ'_prime, _⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt (R := R) (S := S) (Q := Q) hJ_lt_Q
    have hQ_le_Q' : Q ≤ Q' :=
      hQ.2 ⟨hQ'_prime, bot_le⟩ hQ'_lt.le
    exact (hQ'_lt.not_ge hQ_le_Q').elim

omit [IsLocalRing A] in
/-- Helper for Lemma 15.107.8: contraction along a faithfully flat algebra map is surjective on
minimal primes. -/
lemma surjOn_minimalPrimes_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (hff : (algebraMap R S).FaithfullyFlat) :
    Set.SurjOn (Ideal.comap (algebraMap R S)) (minimalPrimes S) (minimalPrimes R) := by
  intro q hq
  have hinj : Function.Injective (algebraMap R S) := hff.injective
  have hker : RingHom.ker (algebraMap R S) = ⊥ := by
    ext x
    constructor
    · intro hx
      have hx0 : x = 0 := hinj <| by simpa using hx
      simpa [hx0]
    · intro hx
      have hx0 : x = 0 := by simpa using hx
      simpa [hx0]
  have hq' : q ∈ (⊥ : Ideal R).minimalPrimes := by
    simpa [minimalPrimes] using hq
  have hqker : q ∈ (RingHom.ker (algebraMap R S)).minimalPrimes := by
    refine ⟨⟨Ideal.minimalPrimes_isPrime hq', ?_⟩, ?_⟩
    · simpa [hker]
    · intro I hI hIq
      exact hq'.2 ⟨hI.1, by simpa [hker] using hI.2⟩ hIq
  -- Injectivity identifies `q` with a minimal prime over the kernel.
  obtain ⟨Q, hQ, hQq⟩ :=
    Ideal.exists_minimalPrimes_comap_eq (algebraMap R S) q hqker
  refine ⟨Q, ?_⟩
  constructor
  · simpa [minimalPrimes] using hQ
  · simpa using hQq

omit [IsLocalRing A] in
/-- Helper for Lemma 15.107.8: a surjective local homomorphism induces a bijection on residue
fields. -/
lemma residueField_bijective_of_surjective_localHom
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    [Nontrivial S] (f : R →+* S) (hf_surj : Function.Surjective f) [IsLocalHom f] :
    Function.Bijective (ResidueField.map f) := by
  constructor
  · -- The source residue field is a field, so its map into a nontrivial target is injective.
    exact RingHom.injective (ResidueField.map f)
  · -- Lift a target residue class through the surjective local map and compare residues.
    intro z
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective z
    obtain ⟨r, rfl⟩ := hf_surj s
    refine ⟨residue R r, ?_⟩
    simpa using IsLocalRing.ResidueField.map_residue f r

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- Helper for Lemma 15.107.8: a local `R`-algebra endomorphism of a chosen henselization is the
identity. -/
lemma henselization_endomorphism_eq_id
    {R Rh : Type u} [CommRing R] [IsLocalRing R]
    [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    (f : Rh →ₐ[R] Rh) (hf : IsLocalHom (f : Rh →+* Rh)) :
    f = AlgHom.id R Rh := by
  rcases
      existsUnique_algHom_between_henselizations_of_localHom
        (R := R) (S := R) (Rh := Rh) (Sh := Rh) with
    ⟨g, hg_local, hg_unique⟩
  have hid_local : IsLocalHom (((AlgHom.id R Rh : Rh →ₐ[R] Rh) : Rh →+* Rh)) := by
    -- The identity map is local because it is the structural self-map.
    simpa using (show IsLocalHom (algebraMap Rh Rh) by infer_instance)
  -- Uniqueness among local endomorphisms forces the chosen map to be the identity.
  calc
    f = g := hg_unique f hf
    _ = AlgHom.id R Rh := (hg_unique (AlgHom.id R Rh) hid_local).symm

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- Helper for Lemma 15.107.8: a local endomorphism of a chosen strict henselization that is
trivial on the chosen residue-field model is the identity. -/
lemma strict_henselization_endomorphism_eq_id
    {R Rsh Ksep : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [Field Ksep] [Algebra (ResidueField R) Ksep]
    (ι : ResidueField Rsh ≃+* Ksep)
    (hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep)
    (f : Rsh →ₐ[R] Rsh) (hf_local : IsLocalHom (f : Rsh →+* Rsh))
    (hf_res :
      (ι.toRingHom.comp (residue Rsh)).comp (f : Rsh →+* Rsh) =
        ι.toRingHom.comp (residue Rsh)) :
    f = AlgHom.id R Rsh := by
  have hid_compat :
      (RingHom.id Ksep).comp (algebraMap (ResidueField R) Ksep) =
        (algebraMap (ResidueField R) Ksep).comp
          (ResidueField.map (algebraMap R R)) := by
    -- For the identity base map, the residue-field compatibility is tautological.
    ext x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    simp
  rcases
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (R := R) (S := R) (Rsh := Rsh) (Ssh := Rsh)
        ι hι ι hι (RingHom.id Ksep) hid_compat with
    ⟨g, hg, huniq⟩
  have hid_local : IsLocalHom (((AlgHom.id R Rsh : Rsh →ₐ[R] Rsh) : Rsh →+* Rsh)) := by
    -- The structural identity map is local.
    simpa using (show IsLocalHom (algebraMap Rsh Rsh) by infer_instance)
  have hid_res :
      (ι.toRingHom.comp (residue Rsh)).comp ((AlgHom.id R Rsh : Rsh →ₐ[R] Rsh) : Rsh →+* Rsh) =
        ι.toRingHom.comp (residue Rsh) := by
    -- The identity leaves the chosen residue-field comparison unchanged.
    ext x
    rfl
  -- Uniqueness with the fixed residue-field model eliminates nontrivial endomorphisms.
  calc
    f = g := huniq f ⟨hf_local, hf_res⟩
    _ = AlgHom.id R Rsh := (huniq (AlgHom.id R Rsh) ⟨hid_local, hid_res⟩).symm

/-- Helper for Lemma 15.107.8: a henselization of the closed-point localization is also a
henselization of the original local ring. -/
lemma closedPoint_henselization_isHenselizationOf
    {R R0h : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing R0h]
    [Algebra (Localization.AtPrime (closedPoint R).asIdeal) R0h]
    [Algebra R R0h]
    [IsScalarTower R (Localization.AtPrime (closedPoint R).asIdeal) R0h]
    [IsHenselizationOf (Localization.AtPrime (closedPoint R).asIdeal) R0h] :
    IsHenselizationOf R R0h := by
  let R0 := Localization.AtPrime (closedPoint R).asIdeal
  let e : R0 ≃ₐ[R] R := localizationAtClosedPoint_algEquiv_self R
  have hR0_surj : Function.Surjective (algebraMap R R0) := by
    intro x
    refine ⟨e x, ?_⟩
    simpa using (e.symm.commutes (e x)).symm
  letI : IsLocalHom (algebraMap R R0) := Function.Surjective.isLocalHom _ hR0_surj
  have hlocal_R0h : IsLocalHom (algebraMap R R0h) := by
    -- The structural map `R → R0h` factors through the local closed-point localization map.
    let _ : IsLocalHom (algebraMap R0 R0h) := IsHenselizationOf.toIsLocalHom
    simpa [R0, IsScalarTower.algebraMap_eq R R0 R0h] using
      (RingHom.isLocalHom_comp (algebraMap R0 R0h) (algebraMap R R0) :
        IsLocalHom ((algebraMap R0 R0h).comp (algebraMap R R0)))
  refine
    { toHenselianLocalRing := inferInstance
      toIsLocalHom := hlocal_R0h
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_
      residueField_bijective := ?_ }
  · -- The localization map is etale because it is bijective, so composition preserves ind-etale.
    have hR0_bij : Function.Bijective (algebraMap R R0) := by
      constructor
      · intro x y hxy
        simpa using congrArg e hxy
      · exact hR0_surj
    have hR0_colim : (algebraMap R R0).IsFilteredColimitOfEtale := by
      let _ : Algebra R (ULift.{u} R0) := ULift.algebra
      let uliftMap : ULift.{u} R →+* ULift.{u} R0 :=
        { toFun := fun x ↦ ⟨algebraMap R R0 x.down⟩
          map_one' := by ext; simp
          map_mul' := fun _ _ ↦ by ext; simp
          map_zero' := by ext; simp
          map_add' := fun _ _ ↦ by ext; simp }
      let _ : Algebra (ULift.{u} R) (ULift.{u} R0) := uliftMap.toAlgebra
      have hEtale :
          CommRingCat.etale (CommRingCat.ofHom uliftMap) := by
        -- A bijective ring map is etale, hence already lies in the ind-etale closure.
        dsimp [CommRingCat.etale]
        refine RingHom.Etale.of_bijective ?_
        constructor
        · intro x y hxy
          apply ULift.ext
          exact hR0_bij.1 <| by
            simpa [uliftMap] using congrArg ULift.down hxy
        · intro z
          obtain ⟨x, hx⟩ := hR0_bij.2 z.down
          refine ⟨⟨x⟩, ?_⟩
          apply ULift.ext
          simpa [uliftMap] using hx
      dsimp [RingHom.IsFilteredColimitOfEtale]
      exact CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale) _ hEtale
    have hcomp :
        algebraMap R R0h = (algebraMap R0 R0h).comp (algebraMap R R0) := by
      ext r
      simp [R0, IsScalarTower.algebraMap_eq R R0 R0h]
    exact hcomp ▸
      RingHom.isFilteredColimitOfEtale_comp
        (algebraMap R R0)
        (algebraMap R0 R0h)
        hR0_colim
        IsHenselizationOf.isFilteredColimitOfEtale
  · -- The maximal ideal first localizes to the maximal ideal of `R0`, then maps to that of `R0h`.
    calc
      Ideal.map (algebraMap R R0h) (maximalIdeal R) =
          Ideal.map (algebraMap R0 R0h) (Ideal.map (algebraMap R R0) (maximalIdeal R)) := by
            simpa [R0, IsScalarTower.algebraMap_eq R R0 R0h] using
              (Ideal.map_map (I := maximalIdeal R) (f := algebraMap R R0)
                (g := algebraMap R0 R0h)).symm
      _ = Ideal.map (algebraMap R0 R0h) (maximalIdeal R0) := by
            congr 1
            simpa [R0, closedPoint_asIdeal_eq_maximalIdeal] using
              (IsLocalization.AtPrime.map_eq_maximalIdeal (closedPoint R).asIdeal R0)
      _ = maximalIdeal R0h := IsHenselizationOf.map_maximalIdeal
  · -- The residue-field map is a composite of two bijections.
    have hR0_residue :
        Function.Bijective (ResidueField.map (algebraMap R R0)) :=
      residueField_bijective_of_surjective_localHom
        (f := algebraMap R R0) hR0_surj
    have hcomp :
        (ResidueField.map (algebraMap R0 R0h)).comp (ResidueField.map (algebraMap R R0)) =
          ResidueField.map (algebraMap R R0h) := by
      ext x
      simp [R0, IsScalarTower.algebraMap_eq R R0 R0h]
    let _ : IsLocalHom (algebraMap R R0h) := hlocal_R0h
    exact hcomp.symm ▸
      IsHenselizationOf.residueField_bijective.comp hR0_residue

/-- Helper for Lemma 15.107.8: a chosen henselization of a local ring is canonically equivalent
to any chosen henselization of the localization at the closed point. -/
lemma chosen_henselization_equiv_closedPoint_henselization
    {R Rh R0h : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
    [CommRing R0h]
    [Algebra (Localization.AtPrime (closedPoint R).asIdeal) R0h]
    [Algebra R R0h]
    [IsScalarTower R (Localization.AtPrime (closedPoint R).asIdeal) R0h]
    [IsHenselizationOf (Localization.AtPrime (closedPoint R).asIdeal) R0h] :
    Nonempty (Rh ≃ₐ[R] R0h) := by
  letI : IsHenselizationOf R R0h :=
    closedPoint_henselization_isHenselizationOf (R := R) (R0h := R0h)
  let _ : IsScalarTower R R Rh := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower R R R0h := IsScalarTower.of_algebraMap_eq' rfl
  let f : Rh →ₐ[R] R0h := henselizationMap (R := R) (S := R) (Rh := Rh) (Sh := R0h)
  let g : R0h →ₐ[R] Rh := henselizationMap (R := R) (S := R) (Rh := R0h) (Sh := Rh)
  have hf_local : IsLocalHom (f : Rh →+* R0h) := by
    -- The canonical comparison between the two chosen henselizations is local.
    simpa [f] using
      (henselizationMap_isLocalHom (R := R) (S := R) (Rh := Rh) (Sh := R0h) :
        IsLocalHom ((henselizationMap (R := R) (S := R) (Rh := Rh) (Sh := R0h) :
          Rh →ₐ[R] R0h).toRingHom))
  have hg_local : IsLocalHom (g : R0h →+* Rh) := by
    -- The reverse canonical comparison is local for the same reason.
    simpa [g] using
      (henselizationMap_isLocalHom (R := R) (S := R) (Rh := R0h) (Sh := Rh) :
        IsLocalHom ((henselizationMap (R := R) (S := R) (Rh := R0h) (Sh := Rh) :
          R0h →ₐ[R] Rh).toRingHom))
  have hgf_local : IsLocalHom ((g.comp f : Rh →ₐ[R] Rh).toRingHom) := by
    -- Both canonical comparison maps are local, so their composite is again local.
    let _ : IsLocalHom (f : Rh →+* R0h) := hf_local
    let _ : IsLocalHom (g : R0h →+* Rh) := hg_local
    simpa [f, g] using
      (RingHom.isLocalHom_comp (g : R0h →+* Rh) (f : Rh →+* R0h) :
        IsLocalHom ((g : R0h →+* Rh).comp (f : Rh →+* R0h)))
  have hfg_local : IsLocalHom ((f.comp g : R0h →ₐ[R] R0h).toRingHom) := by
    -- The same argument applies in the opposite direction.
    let _ : IsLocalHom (f : Rh →+* R0h) := hf_local
    let _ : IsLocalHom (g : R0h →+* Rh) := hg_local
    simpa [f, g] using
      (RingHom.isLocalHom_comp (f : Rh →+* R0h) (g : R0h →+* Rh) :
        IsLocalHom ((f : Rh →+* R0h).comp (g : R0h →+* Rh)))
  have hgf : g.comp f = AlgHom.id R Rh :=
    henselization_endomorphism_eq_id (R := R) (Rh := Rh) (f := g.comp f) hgf_local
  have hfg : f.comp g = AlgHom.id R R0h :=
    henselization_endomorphism_eq_id (R := R) (Rh := R0h) (f := f.comp g) hfg_local
  have hf_injective : Function.Injective f := by
    -- A left inverse immediately makes the chosen-to-closed-point map injective.
    intro x y hxy
    calc
      x = g (f x) := by
        symm
        exact DFunLike.congr_fun hgf x
      _ = g (f y) := by rw [hxy]
      _ = y := DFunLike.congr_fun hgf y
  have hf_surjective : Function.Surjective f := by
    -- A right inverse provides a canonical preimage of every closed-point henselization point.
    intro y
    refine ⟨g y, ?_⟩
    exact DFunLike.congr_fun hfg y
  exact ⟨AlgEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩⟩

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- Helper for Lemma 15.107.8: a strict henselization of the closed-point localization is also a
strict henselization of the original local ring. -/
lemma closedPoint_strictHenselization_isStrictHenselizationOf
    {R R0sh : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing R0sh]
    [Algebra (Localization.AtPrime (closedPoint R).asIdeal) R0sh]
    [Algebra R R0sh]
    [IsScalarTower R (Localization.AtPrime (closedPoint R).asIdeal) R0sh]
    [IsStrictHenselizationOf (Localization.AtPrime (closedPoint R).asIdeal) R0sh] :
    IsStrictHenselizationOf R R0sh := by
  let R0 := Localization.AtPrime (closedPoint R).asIdeal
  let e : R0 ≃ₐ[R] R := localizationAtClosedPoint_algEquiv_self R
  have hR0_surj : Function.Surjective (algebraMap R R0) := by
    intro x
    refine ⟨e x, ?_⟩
    simpa using (e.symm.commutes (e x)).symm
  letI : IsLocalHom (algebraMap R R0) := Function.Surjective.isLocalHom _ hR0_surj
  have hlocal_R0sh : IsLocalHom (algebraMap R R0sh) := by
    -- The structural map `R → R0sh` factors through the local closed-point localization map.
    let _ : IsLocalHom (algebraMap R0 R0sh) := IsStrictHenselizationOf.toIsLocalHom
    simpa [R0, IsScalarTower.algebraMap_eq R R0 R0sh] using
      (RingHom.isLocalHom_comp (algebraMap R0 R0sh) (algebraMap R R0) :
        IsLocalHom ((algebraMap R0 R0sh).comp (algebraMap R R0)))
  refine
    { toStrictHenselianLocalRing := inferInstance
      toIsLocalHom := hlocal_R0sh
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_ }
  · -- The closed-point localization map is etale because it is bijective, so composition keeps
    -- the ind-etale presentation of the chosen strict henselization.
    have hR0_bij : Function.Bijective (algebraMap R R0) := by
      constructor
      · intro x y hxy
        simpa using congrArg e hxy
      · exact hR0_surj
    have hR0_colim : (algebraMap R R0).IsFilteredColimitOfEtale := by
      let uliftMap : ULift.{u} R →+* ULift.{u} R0 :=
        { toFun := fun x ↦ ⟨algebraMap R R0 x.down⟩
          map_one' := by ext; simp
          map_mul' := fun _ _ ↦ by ext; simp
          map_zero' := by ext; simp
          map_add' := fun _ _ ↦ by ext; simp }
      let _ : Algebra (ULift.{u} R) (ULift.{u} R0) := uliftMap.toAlgebra
      have hEtale :
          CommRingCat.etale (CommRingCat.ofHom uliftMap) := by
        -- A bijective ring map is etale, hence already in the ind-etale closure.
        dsimp [CommRingCat.etale]
        refine RingHom.Etale.of_bijective ?_
        constructor
        · intro x y hxy
          apply ULift.ext
          exact hR0_bij.1 <| by
            simpa [uliftMap] using congrArg ULift.down hxy
        · intro z
          obtain ⟨x, hx⟩ := hR0_bij.2 z.down
          refine ⟨⟨x⟩, ?_⟩
          apply ULift.ext
          simpa [uliftMap] using hx
      dsimp [RingHom.IsFilteredColimitOfEtale]
      exact CategoryTheory.MorphismProperty.le_ind (P := CommRingCat.etale) _ hEtale
    have hcomp :
        algebraMap R R0sh = (algebraMap R0 R0sh).comp (algebraMap R R0) := by
      ext r
      simp [R0, IsScalarTower.algebraMap_eq R R0 R0sh]
    exact hcomp ▸
      RingHom.isFilteredColimitOfEtale_comp
        (algebraMap R R0)
        (algebraMap R0 R0sh)
        hR0_colim
        IsStrictHenselizationOf.isFilteredColimitOfEtale
  · -- The maximal ideal first localizes to the maximal ideal of `R0`, then maps to that of
    -- `R0sh`, exactly as in the ordinary henselization bridge.
    calc
      Ideal.map (algebraMap R R0sh) (maximalIdeal R) =
          Ideal.map (algebraMap R0 R0sh) (Ideal.map (algebraMap R R0) (maximalIdeal R)) := by
            simpa [R0, IsScalarTower.algebraMap_eq R R0 R0sh] using
              (Ideal.map_map (I := maximalIdeal R) (f := algebraMap R R0)
                (g := algebraMap R0 R0sh)).symm
      _ = Ideal.map (algebraMap R0 R0sh) (maximalIdeal R0) := by
            congr 1
            simpa [R0, closedPoint_asIdeal_eq_maximalIdeal] using
              (IsLocalization.AtPrime.map_eq_maximalIdeal (closedPoint R).asIdeal R0)
      _ = maximalIdeal R0sh := IsStrictHenselizationOf.map_maximalIdeal

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] in
/-- Helper for Lemma 15.107.8: if a local map sends the source maximal ideal onto the target
maximal ideal, then its closed fiber is a field. -/
lemma closedFiber_isField_of_map_maximalIdeal
    {R : Type u} {S : Type v}
    [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S]
    [Algebra R S]
    (hmap : Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S) :
    IsField (Ideal.Fiber (maximalIdeal R) S) := by
  let e : Ideal.Fiber (maximalIdeal R) S ≃+* S ⧸ maximalIdeal S :=
    (closedFiberQuotAlgEquiv :
        Ideal.Fiber (maximalIdeal R) S ≃ₐ[R]
          S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R)).toRingEquiv.trans <|
      Ideal.quotEquivOfEq hmap
  letI : Field (S ⧸ maximalIdeal S) := Ideal.Quotient.field (maximalIdeal S)
  -- The quotient by the maximal ideal is a field, and the closed fiber is canonically equivalent
  -- to that quotient.
  exact e.toMulEquiv.isField (Field.toIsField _)

/-- Helper for Lemma 15.107.8: the residue field of a strict henselization is algebraic over the
base residue field at the closed point. -/
lemma strict_henselization_closedPoint_residueField_isAlgebraic
    {R Rsh : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh] :
    Algebra.IsAlgebraic (ResidueField R) (ResidueField Rsh) := by
  -- TODO: the intended closed-point specialization exists upstream, but every dependency-closed
  -- owner currently available in this workspace (`15.45.13` and `15.105.17`) fails under
  -- `lake lean` before this file is checked. Re-plan around that earlier broken owner chain.
  sorry

/-- Helper for Lemma 15.107.8: the residue field of a strict henselization is separably closed. -/
lemma strict_henselization_closedPoint_residueField_isSepClosed
    {R Rsh : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh] :
    IsSepClosed (ResidueField Rsh) := by
  -- This is built into the strict henselian structure on the chosen strict henselization.
  infer_instance

/-- Helper for Lemma 15.107.8: once the closed-point residue field of a strict henselization is
known to be algebraic over the base residue field, it is automatically a separable closure. -/
lemma strict_henselization_closedPoint_residueField_isSepClosure
    {R Rsh : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh] :
    IsSepClosure (ResidueField R) (ResidueField Rsh) := by
  -- TODO: the remaining missing input is the separability of `ResidueField R → ResidueField Rsh`.
  -- The helper above supplies only algebraicity, while `IsSepClosure` also needs separability.
  -- Re-plan around an earlier stable owner for the closed-point residue-field separability bridge.
  sorry

/-- Helper for Lemma 15.107.8: a chosen strict henselization of a local ring is canonically
equivalent to any chosen strict henselization of the localization at the closed point once both
residue fields are compared with the same separable-closure model. -/
lemma chosen_strictHenselization_equiv_closedPoint_strictHenselization
    {R Rsh R0sh Ksep : Type u}
    [CommRing R] [IsLocalRing R]
    [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]
    [Field Ksep] [Algebra (ResidueField R) Ksep] [IsSepClosure (ResidueField R) Ksep]
    [CommRing R0sh]
    [Algebra (Localization.AtPrime (closedPoint R).asIdeal) R0sh]
    [Algebra R R0sh]
    [IsLocalHom (algebraMap R R0sh)]
    [IsScalarTower R (Localization.AtPrime (closedPoint R).asIdeal) R0sh]
    [IsStrictHenselizationOf (Localization.AtPrime (closedPoint R).asIdeal) R0sh]
    (ι0 : ResidueField R0sh ≃+* Ksep)
    (hι0 :
      ι0.toRingHom.comp (ResidueField.map (algebraMap R R0sh)) =
        algebraMap (ResidueField R) Ksep) :
    Nonempty (Rsh ≃ₐ[R] R0sh) := by
  letI : IsStrictHenselizationOf R R0sh :=
    closedPoint_strictHenselization_isStrictHenselizationOf (R := R) (R0sh := R0sh)
  let _ : IsSepClosure (ResidueField R) (ResidueField Rsh) :=
    strict_henselization_closedPoint_residueField_isSepClosure (R := R) (Rsh := Rsh)
  let ι : ResidueField Rsh ≃+* Ksep :=
    (IsSepClosure.equiv (ResidueField R) (ResidueField Rsh) Ksep).toRingEquiv
  have hι :
      ι.toRingHom.comp (ResidueField.map (algebraMap R Rsh)) =
        algebraMap (ResidueField R) Ksep := by
    -- Both residue-field identifications land in the same separable-closure model.
    ext x
    exact (IsSepClosure.equiv (ResidueField R) (ResidueField Rsh) Ksep).commutes x
  have hid_compat :
      (RingHom.id Ksep).comp (algebraMap (ResidueField R) Ksep) =
        (algebraMap (ResidueField R) Ksep).comp
          (ResidueField.map (algebraMap R R)) := by
    -- Over the identity base map, residue-field compatibility is tautological.
    ext x
    simp
  rcases
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (R := R) (S := R) (Rsh := Rsh) (Ssh := R0sh)
        ι hι ι0 hι0 (RingHom.id Ksep) hid_compat with
    ⟨f, hf, huniq_f⟩
  rcases
      existsUnique_algHom_between_strictHenselizations_of_residueFieldMap
        (R := R) (S := R) (Rsh := R0sh) (Ssh := Rsh)
        ι0 hι0 ι hι (RingHom.id Ksep) hid_compat with
    ⟨g, hg, huniq_g⟩
  have hgf_local :
      IsLocalHom (((g.comp f : Rsh →ₐ[R] Rsh) : Rsh →+* Rsh)) := by
    -- The two comparison maps are local, hence so is their composite.
    let _ : IsLocalHom (f : Rsh →+* R0sh) := hf.1
    let _ : IsLocalHom (g : R0sh →+* Rsh) := hg.1
    simpa using
      (RingHom.isLocalHom_comp
        (g : R0sh →+* Rsh)
        (f : Rsh →+* R0sh))
  have hgf_res :
      (ι.toRingHom.comp (residue Rsh)).comp
          ((g.comp f : Rsh →ₐ[R] Rsh) : Rsh →+* Rsh) =
        ι.toRingHom.comp (residue Rsh) := by
    -- Compose the two residue-field compatibility relations from the uniqueness theorem.
    have hg_comp :
        (((ι.toRingHom.comp (residue Rsh)).comp
          (g : R0sh →+* Rsh)).comp
            (f : Rsh →+* R0sh)) =
          ((ι0.toRingHom.comp (residue R0sh)).comp
            (f : Rsh →+* R0sh)) := by
      exact congrArg (fun ψ ↦ ψ.comp (f : Rsh →+* R0sh)) hg.2
    calc
      (ι.toRingHom.comp (residue Rsh)).comp
          ((g.comp f : Rsh →ₐ[R] Rsh) : Rsh →+* Rsh) =
        ((ι.toRingHom.comp (residue Rsh)).comp
          (g : R0sh →+* Rsh)).comp
            (f : Rsh →+* R0sh) := by
              rfl
      _ = ((ι0.toRingHom.comp (residue R0sh)).comp
          (f : Rsh →+* R0sh)) := hg_comp
      _ = ι.toRingHom.comp (residue Rsh) := by
            simpa using hf.2
  have hfg_local :
      IsLocalHom (((f.comp g : R0sh →ₐ[R] R0sh) : R0sh →+* R0sh)) := by
    -- The reverse composite is local for the same reason.
    let _ : IsLocalHom (f : Rsh →+* R0sh) := hf.1
    let _ : IsLocalHom (g : R0sh →+* Rsh) := hg.1
    simpa using
      (RingHom.isLocalHom_comp
        (f : Rsh →+* R0sh)
        (g : R0sh →+* Rsh))
  have hfg_res :
      (ι0.toRingHom.comp (residue R0sh)).comp
          ((f.comp g : R0sh →ₐ[R] R0sh) : R0sh →+* R0sh) =
        ι0.toRingHom.comp (residue R0sh) := by
    -- The same residue-field composition argument applies on the closed-point side.
    have hf_comp :
        (((ι0.toRingHom.comp (residue R0sh)).comp
          (f : Rsh →+* R0sh)).comp
            (g : R0sh →+* Rsh)) =
          ((ι.toRingHom.comp (residue Rsh)).comp
            (g : R0sh →+* Rsh)) := by
      exact congrArg (fun ψ ↦ ψ.comp (g : R0sh →+* Rsh)) hf.2
    calc
      (ι0.toRingHom.comp (residue R0sh)).comp
          ((f.comp g : R0sh →ₐ[R] R0sh) : R0sh →+* R0sh) =
        ((ι0.toRingHom.comp (residue R0sh)).comp
          (f : Rsh →+* R0sh)).comp
            (g : R0sh →+* Rsh) := by
              rfl
      _ = ((ι.toRingHom.comp (residue Rsh)).comp
          (g : R0sh →+* Rsh)) := hf_comp
      _ = ι0.toRingHom.comp (residue R0sh) := by
            simpa using hg.2
  have hgf :
      g.comp f = AlgHom.id R Rsh := by
    -- Uniqueness over the chosen separable-closure model forces the source composite to be
    -- the identity.
    exact
      strict_henselization_endomorphism_eq_id
        (R := R) (Rsh := Rsh) (Ksep := Ksep)
        ι hι (g.comp f) hgf_local hgf_res
  have hfg :
      f.comp g = AlgHom.id R R0sh := by
    -- The same argument shows the closed-point composite is also the identity.
    exact
      strict_henselization_endomorphism_eq_id
        (R := R) (Rsh := R0sh) (Ksep := Ksep)
        ι0 hι0 (f.comp g) hfg_local hfg_res
  have hf_injective : Function.Injective (f : Rsh →+* R0sh) := by
    -- The explicit left inverse `g` gives injectivity.
    intro x y hxy
    calc
      x = g (f x) := by
        symm
        exact DFunLike.congr_fun hgf x
      _ = g (f y) := by exact congrArg g hxy
      _ = y := DFunLike.congr_fun hgf y
  have hf_surjective : Function.Surjective (f : Rsh →+* R0sh) := by
    -- The explicit right inverse `g` gives surjectivity.
    intro y
    refine ⟨g y, ?_⟩
    exact DFunLike.congr_fun hfg y
  exact ⟨AlgEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩⟩

section StrictHenselization

variable {Ash : Type u} {Bsh : Type v}
variable [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
variable [CommRing Bsh] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]

-- Proof sketch: pass to chosen strict henselizations of `A` and `B`, use that the smooth local
-- map remains flat after strict henselization, and compare minimal primes by going down and the
-- domain criterion after quotienting by a minimal prime of `A`.
/-- Lemma 15.107.8 (1): if `A → B` is a local homomorphism of local rings whose closed point is
smooth over `A`, then the number of geometric branches of `A`, computed from a chosen strict
henselization `Ash`, equals the number of geometric branches of `B`, computed from a chosen strict
henselization `Bsh`. -/
@[stacks 0DQ1]
theorem geometricBranchNumber_eq_of_smoothAtPrime_closedPoint
    (hsmooth : Algebra.SmoothAtPrime A B (closedPoint B)) :
    geometricBranchNumber A Ash = geometricBranchNumber B Bsh :=
  -- Route correction: do not force the chosen strict henselizations into the closed-point owner
  -- hypotheses. The next step is to compare them with auxiliary strict henselizations of the
  -- closed-point localizations, then apply Lemma `10.155.12` on those genuine owners.
  -- TODO: the faithfully-flat minimal-prime package is now available locally. The remaining work
  -- is the source-faithful strict-henselization comparison route: choose a common separable-closure
  -- residue-field target to define the canonical map `Ash → Bsh`, prove that comparison is
  -- faithfully flat, and then show each quotient over a minimal prime of `Ash` is a domain.
  sorry

end StrictHenselization

section Henselization

variable {Ah : Type u} {Bh : Type v}
variable [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
variable [CommRing Bh] [Algebra B Bh] [IsHenselizationOf B Bh]

-- Proof sketch: repeat the strict-henselization argument with ordinary henselizations. The purely
-- inseparable residue-field extension is used after normalizing the reduced domain quotient of `A`
-- to force the relevant tensor product with the henselization of `B` to stay local.
/-- Lemma 15.107.8 (2): if `A → B` is a local homomorphism of local rings whose closed point is
smooth over `A` and whose induced residue-field extension is purely inseparable, then the number
of branches of `A`, computed from a chosen henselization `Ah`, equals the number of branches of
`B`, computed from a chosen henselization `Bh`. -/
@[stacks 0DQ1]
theorem branchNumber_eq_of_smoothAtPrime_closedPoint_of_purelyInseparable
    (hsmooth : Algebra.SmoothAtPrime A B (closedPoint B))
    (hκ : IsPurelyInseparable (ResidueField A) (ResidueField B)) :
    branchNumber A Ah = branchNumber B Bh :=
  -- Route correction: the ordinary henselization comparison must also pass through auxiliary
  -- closed-point-localization owners, rather than by transporting `Ah` and `Bh` directly into the
  -- hypotheses of Lemma `10.155.8`.
  -- TODO: the generic faithfully-flat/minimal-prime descent step is isolated above. The remaining
  -- blocker is the closed-point comparison `Ah → Bh`: transport the chosen henselizations to the
  -- closed-point localization owners needed by Lemma `10.155.8`, prove the comparison is
  -- faithfully flat, and then run the normalization-plus-locality argument using `hκ`.
  sorry

end Henselization

end
