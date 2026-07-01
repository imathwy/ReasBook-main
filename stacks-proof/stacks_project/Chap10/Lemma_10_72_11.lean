import Mathlib
import stacks_project.Chap10.Definition_10_72_1
import stacks_project.Chap10.Lemma_10_63_13
import stacks_project.Chap10.Lemma_10_63_15
import stacks_project.Chap10.Lemma_10_63_16
import stacks_project.Chap10.Lemma_10_63_18
import stacks_project.Chap10.Lemma_10_72_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing
open LocalizedModule
open scoped ENat

section

variable {R : Type u} {S : Type v} {N : Type w}
variable [CommRing R] [CommRing S] [IsLocalRing R] [IsNoetherianRing R] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
variable [Module.Finite S N]

/-- Helper for Lemma 10.72.11: a prime ideal lies in the range of the localization comap exactly
when it is disjoint from the localization submonoid. -/
private lemma mem_range_comap_iff_disjoint_of_isPrime_for_entry {A : Type*} [CommRing A]
    (T : Submonoid A) {p : Ideal A} (hp : p.IsPrime) :
    p ∈ Set.range (Ideal.comap (algebraMap A (Localization T))) ↔
      Disjoint (T : Set A) (p : Set A) := by
  constructor
  · rintro ⟨J, rfl⟩
    rw [IsLocalization.disjoint_comap_iff T (Localization T)]
    simpa using hp.ne_top
  · intro hpT
    exact ⟨Ideal.map (algebraMap A (Localization T)) p,
      IsLocalization.comap_map_of_isPrime_disjoint T (Localization T) hp hpT⟩

/-- Helper for Lemma 10.72.11: the maximal ideal of a Noetherian local ring cannot generate a
nonzero finite module. -/
private lemma maximalIdeal_smul_top_ne_top_for_entry {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Nontrivial M] :
    maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ := by
  -- This is the Jacobson-ideal form of Nakayama for the maximal ideal.
  simpa [ne_comm] using
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (maximalIdeal_le_jacobson (Module.annihilator A M)))

/-- Helper for Lemma 10.72.11: over a Noetherian local ring, depth zero is equivalent to the
absence of a regular element in the maximal ideal. -/
private lemma moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_entry {A : Type*} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] :
    moduleDepth A M = 0 ↔ ¬ ∃ x ∈ maximalIdeal A, IsSMulRegular M x := by
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry (A := A) (M := M)
  rw [show moduleDepth A M = sSup (Ideal.regularSequenceLengths (maximalIdeal A) M) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) M hsmul]
  constructor
  · intro hdepth hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    -- A regular element in the maximal ideal contributes a regular sequence of length one.
    have hge : (1 : ℕ∞) ≤ sSup (Ideal.regularSequenceLengths (maximalIdeal A) M) := by
      refine le_sSup ?_
      refine ⟨[x], ?_, ?_, by simp⟩
      · exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
          (by
            intro r hr
            simpa [List.mem_singleton.mp hr] using hx)
          ((RingTheory.Sequence.isWeaklyRegular_singleton_iff M x).2 hxreg)
      · simpa using hx
    exact (ENat.one_le_iff_ne_zero.1 hge) hdepth
  · intro hno
    apply le_antisymm
    · refine sSup_le ?_
      intro d hd
      rcases hd with ⟨rs, hreg, hmem, rfl⟩
      cases rs with
      | nil =>
          simp
      | cons x xs =>
          exfalso
          have hx : x ∈ maximalIdeal A := hmem (Ideal.subset_span (by simp))
          have hxreg : IsSMulRegular M x :=
            ((RingTheory.Sequence.isRegular_cons_iff M x xs).1 hreg).1
          exact hno ⟨x, hx, hxreg⟩
    · exact bot_le

/-- Helper for Lemma 10.72.11: if the source depth is nonzero, the maximal ideal contains a
regular element. -/
private lemma exists_mem_maximalIdeal_isSMulRegular_of_moduleDepth_ne_zero_for_entry {A : Type*}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Nontrivial M] (hdepth : moduleDepth A M ≠ 0) :
    ∃ x ∈ maximalIdeal A, IsSMulRegular M x := by
  by_contra hno
  exact hdepth ((moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_entry (A := A) (M := M)).2 hno)

/-- Helper for Lemma 10.72.11: a finite subsingleton module over a Noetherian local ring has
infinite depth. -/
private theorem moduleDepth_eq_top_of_subsingleton {A : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Subsingleton M] :
    moduleDepth A M = ⊤ := by
  -- A subsingleton module has `⊤ = ⊥`, so the maximal ideal already generates the whole module.
  have htop_eq_bot : (⊤ : Submodule A M) = ⊥ := by
    ext m
    simp [Subsingleton.elim m 0]
  have hsmul_bot : maximalIdeal A • (⊥ : Submodule A M) = ⊥ := by
    ext m
    simp
  have hsmul_top : maximalIdeal A • (⊤ : Submodule A M) = ⊤ := by
    rw [htop_eq_bot, hsmul_bot, ← htop_eq_bot]
  change Ideal.depth (maximalIdeal A) M = ⊤
  simpa using Ideal.depth_eq_top_of_smul_top (maximalIdeal A) M hsmul_top

/-- Helper for Lemma 10.72.11: an `M`-regular element in the maximal ideal forces positive local
depth. -/
private lemma one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular M x) :
    (1 : ℕ∞) ≤ moduleDepth A M := by
  -- The singleton list `[x]` contributes a regular sequence of length one.
  have hsingleton_reg : RingTheory.Sequence.IsRegular M [x] := by
    exact RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal M
      (by
        intro r hr
        simpa [List.mem_singleton.mp hr] using hx)
      ((RingTheory.Sequence.isWeaklyRegular_singleton_iff M x).2 hreg)
  have hsingleton_mem : Ideal.ofList [x] ≤ maximalIdeal A := by
    simpa using (Ideal.span_singleton_le_iff_mem (I := maximalIdeal A) (x := x)).2 hx
  have hsmul :
      maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry (A := A) (M := M)
  rw [show moduleDepth A M = sSup (Ideal.regularSequenceLengths (maximalIdeal A) M) from
    Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) M hsmul]
  refine le_sSup ?_
  exact ⟨[x], hsingleton_reg, hsingleton_mem, by simp⟩

/-- Helper for Lemma 10.72.11: over a Noetherian local ring, an associated closed point forces the
module depth to vanish. -/
private lemma moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hmax : maximalIdeal A ∈ associatedPrimes A M) :
    moduleDepth A M = 0 := by
  by_cases hsub : Subsingleton M
  · letI : Subsingleton M := hsub
    exact False.elim ((not_isAssociatedPrime_of_subsingleton : ¬ IsAssociatedPrime (maximalIdeal A) M)
      hmax)
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
    rw [moduleDepth_eq_zero_iff_no_maximalIdeal_regular_for_entry (A := A) (M := M)]
    intro hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    have hx_not_union :
        x ∉ ⋃ p ∈ associatedPrimes A M, (p : Set A) := by
      simpa [Set.mem_compl_iff, biUnion_associatedPrimes_eq_compl_regular A M] using hxreg
    exact hx_not_union <|
      Set.mem_iUnion.2 ⟨maximalIdeal A, Set.mem_iUnion.2 ⟨hmax, hx⟩⟩

/-- Helper for Lemma 10.72.11: over a Noetherian local ring, depth zero forces the maximal ideal
to be an associated prime. -/
private lemma maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
    {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hdepth : moduleDepth A M = 0) :
    maximalIdeal A ∈ associatedPrimes A M := by
  -- Route correction: rebuild the depth-zero bridge directly from the regular-element criterion.
  have htop :
      maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ := by
    intro htop
    rw [show moduleDepth A M = ⊤ from
          Ideal.depth_eq_top_of_smul_top (maximalIdeal A) M htop] at hdepth
    simp at hdepth
  have hnontrivial : Nontrivial M := by
    by_contra hsub
    letI : Subsingleton M := not_nontrivial_iff_subsingleton.mp hsub
    exact htop <| by
      ext m
      simp [Subsingleton.elim m 0]
  have hno_regular : ¬ ∃ x ∈ maximalIdeal A, IsSMulRegular M x := by
    intro hreg
    rcases hreg with ⟨x, hx, hxreg⟩
    have hdepth_pos : (1 : ℕ∞) ≤ moduleDepth A M :=
      one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular
        (A := A) (M := M) hx hxreg
    exact (ENat.one_le_iff_ne_zero.1 hdepth_pos) hdepth
  by_contra hmax
  have hforall :
      ∀ q ∈ associatedPrimes A M, ¬ maximalIdeal A ≤ q := by
    intro q hq hmq
    have hq_le : q ≤ maximalIdeal A := IsLocalRing.le_maximalIdeal hq.1.ne_top
    have hq_eq : q = maximalIdeal A := le_antisymm hq_le hmq
    exact hmax (hq_eq ▸ hq)
  exact hno_regular <|
    (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
      (R := A) (M := M) (I := maximalIdeal A)).2 hforall

/-- Helper for Lemma 10.72.11: the target maximal ideals of a finite algebra over a local ring all
lie over the source maximal ideal. -/
private lemma comap_maximalIdeal_eq_of_finite (m : MaximalSpectrum S) [Module.Finite R S] :
    Ideal.comap (algebraMap R S) m.asIdeal = maximalIdeal R := by
  -- Finite algebras are integral, so maximal ideals contract to maximal ideals.
  have hcomap_max : (Ideal.comap (algebraMap R S) m.asIdeal).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m.asIdeal
  exact IsLocalRing.eq_maximalIdeal hcomap_max

/-- Helper for Lemma 10.72.11: localizing an associated prime makes the localized maximal ideal
associated. -/
private theorem maximalIdeal_mem_associatedPrimes_atPrime_of_mem
    {X : Type w} [AddCommGroup X] [Module S X] [IsNoetherianRing S]
    {q : Ideal S} [q.IsPrime]
    (hq : q ∈ associatedPrimes S X) :
    maximalIdeal (Localization.AtPrime q) ∈
      associatedPrimes (Localization.AtPrime q) (LocalizedModule.AtPrime q X) := by
  -- Route correction: use the earlier owner/textbook bridge for localization at a prime, then
  -- return to the owner `associatedPrimes` API on both sides.
  have hq_text : q ∈ associatedPrimesOfModule S X := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq
  have hq_loc_text :
      maximalIdeal (Localization.AtPrime q) ∈
        associatedPrimesOfModule (Localization.AtPrime q) (LocalizedModule.AtPrime q X) :=
    mem_associatedPrimesOfModule_atPrime_of_mem_associatedPrimesOfModule hq_text
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq_loc_text

/-- Helper for Lemma 10.72.11: if the localized maximal ideal is associated, then the underlying
prime was already associated before localizing. -/
private theorem mem_associatedPrimes_of_maximalIdeal_mem_atPrime
    {X : Type w} [AddCommGroup X] [Module S X] [Module.Finite S X] [IsNoetherianRing S]
    {q : Ideal S} [q.IsPrime]
    (hq :
      maximalIdeal (Localization.AtPrime q) ∈
        associatedPrimes (Localization.AtPrime q) (LocalizedModule.AtPrime q X)) :
    q ∈ associatedPrimes S X := by
  -- Descend from the localized owner statement to the textbook one, then use the finite-generation
  -- hypothesis on `q` coming from Noetherianity to contract back to `S`.
  have hq_text :
      maximalIdeal (Localization.AtPrime q) ∈
        associatedPrimesOfModule (Localization.AtPrime q) (LocalizedModule.AtPrime q X) := by
    simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq
  have hq_source_text : q ∈ associatedPrimesOfModule S X :=
    mem_associatedPrimesOfModule_of_mem_associatedPrimesOfModule_atPrime_of_fg
      hq_text (Ideal.fg_of_isNoetherianRing q)
  simpa [associatedPrimesOfModule_eq_associatedPrimes] using hq_source_text

/-- Helper for Lemma 10.72.11: mapping a regular sequence along an algebra map preserves
regularity on the restricted-scalar module. -/
private theorem isRegular_map_algebraMap_iff_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (rs : List A) :
    RingTheory.Sequence.IsRegular M (rs.map (algebraMap A B)) ↔
      RingTheory.Sequence.IsRegular M rs := by
  -- The identity map on `M` intertwines the two scalar actions through `algebraMap A B`.
  exact
    (AddEquiv.refl M).isRegular_congr <|
      List.forall₂_map_left_iff.mpr <|
        List.forall₂_same.mpr fun r _ => algebraMap_smul B r

/-- Helper for Lemma 10.72.11: under a surjective local map, a list in the target maximal ideal
lifts to a list in the source maximal ideal with the same image. -/
private theorem exists_preimage_list_in_maximalIdeal_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    (hsurj : Function.Surjective (algebraMap A B)) (rs : List B)
    (hI : Ideal.ofList rs ≤ maximalIdeal B) :
    ∃ rs' : List A,
      rs'.map (algebraMap A B) = rs ∧ Ideal.ofList rs' ≤ maximalIdeal A := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  induction rs with
  | nil =>
      -- The empty list already lies in the source maximal ideal.
      have hnil : Ideal.ofList ([] : List A) ≤ maximalIdeal A := by
        simpa using (bot_le : (⊥ : Ideal A) ≤ maximalIdeal A)
      exact ⟨[], rfl, hnil⟩
  | cons s rs ih =>
      -- Lift the head entry from the target maximal ideal, then recurse on the tail.
      have hs_mem : s ∈ maximalIdeal B := by
        exact hI (Ideal.subset_span (by simp))
      have hs_map : s ∈ Ideal.map (algebraMap A B) (maximalIdeal A) := by
        simpa [hmap] using hs_mem
      rcases (Ideal.mem_map_iff_of_surjective (f := algebraMap A B) hsurj).1 hs_map with
        ⟨r, hr, hrs⟩
      have htail_aux : Ideal.ofList rs ≤ Ideal.ofList (s :: rs) := by
        rw [Ideal.ofList_cons]
        exact le_sup_of_le_right le_rfl
      have htail : Ideal.ofList rs ≤ maximalIdeal B := htail_aux.trans hI
      rcases ih htail with ⟨rs', hrs', hI'⟩
      have hr_le : Ideal.span ({r} : Set A) ≤ maximalIdeal A := by
        refine Ideal.span_le.mpr ?_
        intro x hx
        simp at hx
        simpa [hx] using hr
      have hcons : Ideal.ofList (r :: rs') ≤ maximalIdeal A := by
        rw [Ideal.ofList_cons]
        exact sup_le hr_le hI'
      exact ⟨r :: rs', by simp [hrs, hrs'], hcons⟩

/-- Helper for Lemma 10.72.11: an `R`-regular element remains regular after localizing at a
maximal ideal of the finite target algebra. -/
private theorem localizedModule_atPrime_isSMulRegular_of_isSMulRegular
    [Module.Finite R S] (m : MaximalSpectrum S) {f : R}
    (hf : f ∈ maximalIdeal R) (hreg : IsSMulRegular N f) :
    IsSMulRegular (LocalizedModule.AtPrime m.asIdeal N)
      (algebraMap R (Localization.AtPrime m.asIdeal) f) := by
  -- First reinterpret `f` as the corresponding `S`-scalar, then localize the regular action
  -- along `S → S_m`.
  have hregS : IsSMulRegular N (algebraMap R S f) :=
    (isSMulRegular_algebraMap_iff S).2 hreg
  -- The source maximal-ideal hypothesis is only needed later to keep the source proof route;
  -- the regularity transport itself is pure localization.
  have _hf_unused : f ∈ maximalIdeal R := hf
  simpa [DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S (Localization.AtPrime m.asIdeal)) f]
    using
      (IsSMulRegular.of_isLocalizedModule
        (R := S)
        (S := Localization.AtPrime m.asIdeal)
        (p := m.asIdeal.primeCompl)
        (K := N)
        (M := LocalizedModule.AtPrime m.asIdeal N)
        (f := LocalizedModule.mkLinearMap m.asIdeal.primeCompl N)
        hregS)

/-- Helper for Lemma 10.72.11: a linear equivalence preserves the set of regular-sequence lengths
in a fixed ideal. -/
private theorem regularSequenceLengths_eq_of_linearEquiv
    {A : Type*} [CommRing A] {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] (I : Ideal A) (e : N₁ ≃ₗ[A] N₂) :
    Ideal.regularSequenceLengths I N₁ = Ideal.regularSequenceLengths I N₂ := by
  -- Transport each regular sequence across the equivalence and then reverse the argument.
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).1 hreg, hI, rfl⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    exact ⟨rs, (e.isRegular_congr rs).2 hreg, hI, rfl⟩

/-- Helper for Lemma 10.72.11: ideal depth is invariant under a linear equivalence of finite
modules. -/
private theorem idealDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] {N₁ : Type*} [AddCommGroup N₁] [Module A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₁] [Module.Finite A N₂]
    (I : Ideal A) (e : N₁ ≃ₗ[A] N₂) :
    Ideal.depth I N₁ = Ideal.depth I N₂ := by
  -- Compare the two depth branches by mapping `I • ⊤` along the equivalence.
  have htop :
      I • (⊤ : Submodule A N₁) = ⊤ ↔ I • (⊤ : Submodule A N₂) = ⊤ := by
    constructor
    · intro h
      have hmap := congrArg (Submodule.map e.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.surjective] using hmap
    · intro h
      have hmap := congrArg (Submodule.map e.symm.toLinearMap) h
      simpa [Submodule.map_smul'', LinearMap.range_eq_top.2 e.symm.surjective] using hmap
  by_cases hN₁ : I • (⊤ : Submodule A N₁) = ⊤
  · rw [Ideal.depth_eq_top_of_smul_top I N₁ hN₁,
      Ideal.depth_eq_top_of_smul_top I N₂ (htop.mp hN₁)]
  · rw [Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N₁ hN₁,
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top I N₂ (mt htop.mpr hN₁),
      regularSequenceLengths_eq_of_linearEquiv I e]

/-- Helper for Lemma 10.72.11: linear equivalences preserve module depth over a local ring. -/
private theorem moduleDepth_eq_of_linearEquiv
    {A : Type*} [CommRing A] [IsLocalRing A]
    {N₁ : Type*} [AddCommGroup N₁] [Module A N₁] [Module.Finite A N₁]
    {N₂ : Type*} [AddCommGroup N₂] [Module A N₂] [Module.Finite A N₂]
    (e : N₁ ≃ₗ[A] N₂) :
    moduleDepth A N₁ = moduleDepth A N₂ := by
  -- Specialize ideal-depth invariance to the maximal ideal of the local ring.
  simpa [moduleDepth] using idealDepth_eq_of_linearEquiv (maximalIdeal A) e

/-- Helper for Lemma 10.72.11: restricting scalars identifies the `S`-submodule
`(algebraMap R S f)N` with the `R`-submodule `fN`. -/
private lemma smul_top_eq_algebraMap_principal_restrictScalars
    [Module.Finite R S] (f : R) :
    (((Ideal.span ({algebraMap R S f} : Set S) : Ideal S) •
        (⊤ : Submodule S N)).restrictScalars R) =
      ((Ideal.span ({f} : Set R) : Ideal R) • (⊤ : Submodule R N)) := by
  -- Rewrite the target ideal as the image of the source principal ideal, then restrict scalars.
  calc
    (((Ideal.span ({algebraMap R S f} : Set S) : Ideal S) •
        (⊤ : Submodule S N)).restrictScalars R)
        = ((Ideal.map (algebraMap R S) (Ideal.span ({f} : Set R)) : Ideal S) •
            (⊤ : Submodule S N)).restrictScalars R := by
            congr 2
            simpa [Set.image_singleton] using
              (Ideal.map_span (f := algebraMap R S) ({f} : Set R)).symm
    _ = ((Ideal.span ({f} : Set R) : Ideal R) • (⊤ : Submodule R N)) := by
          simpa using
            (Ideal.smul_restrictScalars
              (R := R) (S := S) (M := N) (Ideal.span ({f} : Set R))
              (⊤ : Submodule S N))

/-- Helper for Lemma 10.72.11: quotienting by `f` over the restricted `R`-action agrees with
quotienting by `algebraMap R S f` over the `S`-action. -/
private noncomputable def quotSMulTop_algebraMap_restrictScalars_equiv
    [Module.Finite R S] (f : R) :
    QuotSMulTop (algebraMap R S f) N ≃ₗ[R] QuotSMulTop f N := by
  -- Compare the same quotient first as an `S`-quotient and then as an `R`-quotient after
  -- restricting scalars; the principal submodule agrees by the explicit principal-ideal rewrite.
  let P : Submodule S N := (Ideal.span ({algebraMap R S f} : Set S) : Ideal S) • ⊤
  let e₀ : QuotSMulTop (algebraMap R S f) N ≃ₗ[R] N ⧸ P.restrictScalars R :=
    (((Submodule.quotEquivOfEq _ _ (by
        simpa [P] using
          (Submodule.ideal_span_singleton_smul (algebraMap R S f) (⊤ : Submodule S N)).symm)
      ).restrictScalars R)).trans (Submodule.Quotient.restrictScalarsEquiv R P).symm
  have hsmul :
      P.restrictScalars R = (Ideal.span ({f} : Set R) : Ideal R) • (⊤ : Submodule R N) := by
    simpa [P] using
      smul_top_eq_algebraMap_principal_restrictScalars (R := R) (S := S) (N := N) f
  let e₁ :
      (N ⧸ P.restrictScalars R) ≃ₗ[R] QuotSMulTop f N :=
    (Submodule.quotEquivOfEq _ _ hsmul).trans
      (Submodule.quotEquivOfEq _ _ (by
        simpa using (Submodule.ideal_span_singleton_smul f (⊤ : Submodule R N)).symm)).symm
  exact e₀.trans e₁

/-- Helper for Lemma 10.72.11: localizing the quotient by `f` agrees with quotienting the
localized module by the localized scalar. -/
private noncomputable def localizedModule_atPrime_quotSMulTop_equiv
    [Module.Finite R S] (m : MaximalSpectrum S) (f : R) :
    LocalizedModule.AtPrime m.asIdeal (QuotSMulTop (algebraMap R S f) N) ≃ₗ[Localization.AtPrime m.asIdeal]
      QuotSMulTop (algebraMap R (Localization.AtPrime m.asIdeal) f)
        (LocalizedModule.AtPrime m.asIdeal N) := by
  -- This is the same three-map tensor/quotient comparison as in Lemma 10.72.10, now with the
  -- localized `S`-algebra and the source scalar `f`.
  let e₁ :=
    LocalizedModule.equivTensorProduct
      (R := S) m.asIdeal.primeCompl (QuotSMulTop (algebraMap R S f) N)
  let e₂ := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop
    (R := S) (r := algebraMap R S f) (M := N) (Localization.AtPrime m.asIdeal)).symm
  let e₃ := QuotSMulTop.congr
    (algebraMap S (Localization.AtPrime m.asIdeal) (algebraMap R S f))
    (LocalizedModule.equivTensorProduct (R := S) m.asIdeal.primeCompl N).symm
  simpa [DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S (Localization.AtPrime m.asIdeal)) f]
    using e₁.trans (e₂.trans e₃)

/-- Helper for Lemma 10.72.11: under a surjective local map, the regular-sequence lengths in the
two maximal ideals agree on the same module. -/
private theorem regularSequenceLengths_maximalIdeal_eq_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    (hsurj : Function.Surjective (algebraMap A B)) :
    Ideal.regularSequenceLengths (maximalIdeal A) M =
      Ideal.regularSequenceLengths (maximalIdeal B) M := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  ext d
  constructor
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Push a source regular sequence into the target maximal ideal.
    have hreg' : RingTheory.Sequence.IsRegular M (rs.map (algebraMap A B)) :=
      (isRegular_map_algebraMap_iff_for_entry (A := A) (B := B) (M := M) rs).2 hreg
    have hI' : Ideal.ofList (rs.map (algebraMap A B)) ≤ maximalIdeal B := by
      simpa [Ideal.map_ofList, hmap] using Ideal.map_mono (f := algebraMap A B) hI
    exact ⟨rs.map (algebraMap A B), hreg', hI', by simp⟩
  · rintro ⟨rs, hreg, hI, rfl⟩
    -- Pull a target regular sequence back through the surjective map.
    rcases exists_preimage_list_in_maximalIdeal_of_surjective_for_entry
        (A := A) (B := B) hsurj rs hI with
      ⟨rs', hrs', hI'⟩
    have hreg_map : RingTheory.Sequence.IsRegular M (rs'.map (algebraMap A B)) := by
      simpa [hrs'] using hreg
    have hreg' : RingTheory.Sequence.IsRegular M rs' :=
      (isRegular_map_algebraMap_iff_for_entry (A := A) (B := B) (M := M) rs').1 hreg_map
    have hlen_nat : rs'.length = rs.length := by
      simpa using congrArg List.length hrs'
    exact ⟨rs', hreg', hI', by exact_mod_cast hlen_nat.symm⟩

/-- Helper for Lemma 10.72.11: restricting scalars along a surjective local map does not change
module depth. -/
private theorem moduleDepth_eq_of_surjective_for_entry
    {A : Type*} {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    {M : Type*} [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
    [Module.Finite A M] [Module.Finite B M]
    (hsurj : Function.Surjective (algebraMap A B)) :
    moduleDepth A M = moduleDepth B M := by
  have hmap :
      Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A B) hsurj
  have hsmul :
      (maximalIdeal B • (⊤ : Submodule B M)).restrictScalars A =
        maximalIdeal A • (⊤ : Submodule A M) := by
    -- The target maximal ideal is the image of the source maximal ideal under the surjective map.
    simpa [hmap] using
      (Ideal.smul_restrictScalars (R := A) (S := B) (M := M) (maximalIdeal A)
        (⊤ : Submodule B M))
  have htop :
      maximalIdeal A • (⊤ : Submodule A M) = ⊤ ↔
        maximalIdeal B • (⊤ : Submodule B M) = ⊤ := by
    constructor
    · intro hA
      have hA' : (maximalIdeal B • (⊤ : Submodule B M)).restrictScalars A = ⊤ := by
        rw [hsmul, hA]
      exact
        (Submodule.restrictScalars_eq_top_iff (S := A)
          (p := maximalIdeal B • (⊤ : Submodule B M))).mp hA'
    · intro hB
      have hB' :
          (maximalIdeal B • (⊤ : Submodule B M)).restrictScalars A = ⊤ := by
        rw [hB, Submodule.restrictScalars_top]
      simpa [hsmul] using hB'
  by_cases hA : maximalIdeal A • (⊤ : Submodule A M) = ⊤
  · -- In the `⊤` branch, both depths are infinite.
    rw [show moduleDepth A M = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal A) M hA,
      show moduleDepth B M = ⊤ from Ideal.depth_eq_top_of_smul_top (maximalIdeal B) M (htop.mp hA)]
  · -- Otherwise, both depths are the supremum of regular-sequence lengths, which agree.
    have hB : maximalIdeal B • (⊤ : Submodule B M) ≠ ⊤ := mt htop.mpr hA
    rw [show moduleDepth A M = sSup (Ideal.regularSequenceLengths (maximalIdeal A) M) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) M hA,
      show moduleDepth B M = sSup (Ideal.regularSequenceLengths (maximalIdeal B) M) from
          Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal B) M hB,
      regularSequenceLengths_maximalIdeal_eq_of_surjective_for_entry
        (A := A) (B := B) (M := M) hsurj]

/-- Helper for Lemma 10.72.11: membership in the maximal ideal survives the canonical lift
`A → ULift A`. -/
private lemma mem_maximalIdeal_ulift_of_mem
    {A : Type v} [CommRing A] [IsLocalRing A] [IsLocalRing (ULift.{w} A)] {x : A}
    (hx : x ∈ maximalIdeal A) :
    algebraMap A (ULift.{w} A) x ∈ maximalIdeal (ULift.{w} A) := by
  let hsurj : Function.Surjective (algebraMap A (ULift.{w} A)) :=
    fun y ↦ ⟨y.down, by cases y; rfl⟩
  -- The maximal ideal of the lift is the image of the maximal ideal of `A`.
  have hmap :
      Ideal.map (algebraMap A (ULift.{w} A)) (maximalIdeal A) =
        maximalIdeal (ULift.{w} A) :=
    IsLocalRing.map_maximalIdeal_of_surjective (algebraMap A (ULift.{w} A)) hsurj
  have hx_map :
      algebraMap A (ULift.{w} A) x ∈
        Ideal.map (algebraMap A (ULift.{w} A)) (maximalIdeal A) :=
    Ideal.mem_map_of_mem (algebraMap A (ULift.{w} A)) hx
  simpa [hmap] using hx_map

/-- Helper for Lemma 10.72.11: in separate universes, quotienting by a maximal-ideal
nonzerodivisor lowers local depth by at most one. -/
private lemma moduleDepth_quotSMulTop_le_sub_one_of_mem_maximalIdeal_local_poly
    {A : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M] [Nontrivial M] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular M x) :
    moduleDepth A (QuotSMulTop x M) ≤ moduleDepth A M - 1 := by
  letI : Nontrivial (QuotSMulTop x M) :=
    nontrivial_quotSMulTop_of_mem_maximalIdeal (R := A) (L := M) hx
  -- Rewrite both depths as suprema of regular-sequence lengths and prepend `x`.
  have hquot_smul :
      maximalIdeal A • (⊤ : Submodule A (QuotSMulTop x M)) ≠ ⊤ := by
    simpa using maximalIdeal_smul_top_ne_top_for_entry (A := A) (M := QuotSMulTop x M)
  have hmodule_smul :
      maximalIdeal A • (⊤ : Submodule A M) ≠ ⊤ :=
    maximalIdeal_smul_top_ne_top_for_entry (A := A) (M := M)
  have hfiniteDepth : moduleDepth A M < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top (R := A) (I := maximalIdeal A) (M := M) hmodule_smul
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hfiniteDepth)
  have hdepth : moduleDepth A M = n := by
    simpa using hn.symm
  rw [show moduleDepth A (QuotSMulTop x M) =
      sSup (Ideal.regularSequenceLengths (maximalIdeal A) (QuotSMulTop x M)) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) (QuotSMulTop x M)
        hquot_smul]
  refine sSup_le ?_
  intro d hd
  rcases hd with ⟨ys, hysreg, hysmem, rfl⟩
  have hcons_reg : RingTheory.Sequence.IsRegular M ([x] ++ ys) := by
    have hfull : RingTheory.Sequence.IsRegular M (x :: ys) := by
      exact RingTheory.Sequence.IsRegular.cons hreg hysreg
    simpa using hfull
  have hcons_mem : Ideal.ofList ([x] ++ ys) ≤ maximalIdeal A := by
    refine Ideal.span_le.mpr ?_
    intro r hr
    rcases (by simpa [List.mem_append] using hr : r = x ∨ r ∈ ys) with rfl | hyr
    · exact hx
    · exact hysmem (Ideal.subset_span hyr)
  have hcons_le : ((([x] ++ ys).length : ℕ∞) ≤ moduleDepth A M) := by
    rw [show moduleDepth A M = sSup (Ideal.regularSequenceLengths (maximalIdeal A) M) from
      Ideal.depth_eq_sSup_lengths_of_smul_top_ne_top (maximalIdeal A) M hmodule_smul]
    refine le_sSup ?_
    exact ⟨[x] ++ ys, hcons_reg, hcons_mem, rfl⟩
  have hcons_le_nat : ([x] ++ ys).length ≤ n := by
    rw [hdepth] at hcons_le
    exact_mod_cast hcons_le
  have hys_le_nat : ys.length ≤ n - 1 := by
    have hsucc_le : ys.length + 1 ≤ n := by
      simpa using hcons_le_nat
    omega
  rw [hdepth]
  exact_mod_cast hys_le_nat

/-- Helper for Lemma 10.72.11: separate-universe copy of Lemma `10.72.7 (1)` for local rings. -/
private theorem moduleDepth_quotSMulTop_eq_sub_one_of_regular_local_poly
    {A : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {M : Type w} [AddCommGroup M] [Module A M] [Module.Finite A M] {x : A}
    (hx : x ∈ maximalIdeal A) (hreg : IsSMulRegular M x) :
    moduleDepth A (QuotSMulTop x M) = moduleDepth A M - 1 := by
  by_cases hM : Subsingleton M
  · letI : Subsingleton M := hM
    letI : Subsingleton (QuotSMulTop x M) := by infer_instance
    -- In the zero-module branch, both depths are `⊤`.
    have hdepth_M : moduleDepth A M = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (A := A) (M := M)
    have hdepth_quot : moduleDepth A (QuotSMulTop x M) = ⊤ :=
      moduleDepth_eq_top_of_subsingleton (A := A) (M := QuotSMulTop x M)
    simpa [hdepth_M, hdepth_quot]
  · letI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    -- TODO: complete the common-universe lift `(ULift A, ULift M)` by packaging the missing
    -- quotient-side `A`/`ULift A` scalar-tower and finite-module bridges. The remaining blocker is
    -- a stable equivalence
    -- `QuotSMulTop (algebraMap A (ULift A) x) (ULift M) ≃ₗ[A] QuotSMulTop x M`
    -- compatible with `moduleDepth_eq_of_surjective_for_entry`, so that Lemma `10.72.7` can be
    -- applied on the lifted side and descended back to `(A, M)`.
    sorry

/-- Helper for Lemma 10.72.11: after localizing at a maximal ideal, quotienting by a regular
source element lowers depth by one. -/
private theorem moduleDepth_localized_quotSMulTop_eq_sub_one_of_regular
    [Module.Finite R S] (m : MaximalSpectrum S) {f : R}
    (hf : f ∈ maximalIdeal R) (hreg : IsSMulRegular N f) :
    moduleDepth (Localization.AtPrime m.asIdeal)
      (LocalizedModule.AtPrime m.asIdeal (QuotSMulTop (algebraMap R S f) N)) =
        moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N) - 1 := by
  -- Route correction: use the new separate-universe local depth-drop theorem after transporting
  -- the quotient through the localization equivalence.
  have hfS : algebraMap R S f ∈ m.asIdeal := by
    rw [← Ideal.mem_comap]
    simpa [comap_maximalIdeal_eq_of_finite (R := R) (S := S) (m := m)] using hf
  have hf_loc :
      algebraMap R (Localization.AtPrime m.asIdeal) f ∈
        maximalIdeal (Localization.AtPrime m.asIdeal) := by
    simpa [DFunLike.congr_fun (IsScalarTower.algebraMap_eq R S (Localization.AtPrime m.asIdeal)) f]
      using
        (IsLocalization.AtPrime.to_map_mem_maximal_iff
          (Localization.AtPrime m.asIdeal) m.asIdeal (algebraMap R S f)).2 hfS
  have hreg_loc :
      IsSMulRegular (LocalizedModule.AtPrime m.asIdeal N)
        (algebraMap R (Localization.AtPrime m.asIdeal) f) :=
    localizedModule_atPrime_isSMulRegular_of_isSMulRegular
      (R := R) (S := S) (N := N) m hf hreg
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
    IsLocalization.isNoetherianRing
      m.asIdeal.primeCompl
      (Localization.AtPrime m.asIdeal)
      inferInstance
  calc
    moduleDepth (Localization.AtPrime m.asIdeal)
        (LocalizedModule.AtPrime m.asIdeal (QuotSMulTop (algebraMap R S f) N)) =
      moduleDepth (Localization.AtPrime m.asIdeal)
        (QuotSMulTop (algebraMap R (Localization.AtPrime m.asIdeal) f)
          (LocalizedModule.AtPrime m.asIdeal N)) := by
            simpa using
              moduleDepth_eq_of_linearEquiv
                (A := Localization.AtPrime m.asIdeal)
                (localizedModule_atPrime_quotSMulTop_equiv (R := R) (S := S) (N := N) m f)
    _ =
      moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N) - 1 := by
        exact moduleDepth_quotSMulTop_eq_sub_one_of_regular_local_poly
          (A := Localization.AtPrime m.asIdeal)
          (M := LocalizedModule.AtPrime m.asIdeal N)
          hf_loc
          hreg_loc

/-- Helper for Lemma 10.72.11: a finite algebra over the local ring `R` has only finitely many
maximal ideals. -/
private theorem finite_maximalSpectrum_of_finite_algebra [Module.Finite R S] :
    Finite (MaximalSpectrum S) := by
  -- View the finite map as quasi-finite so that the finite fiber over `maximalIdeal R` controls
  -- all maximal ideals of `S`.
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  letI : Algebra.QuasiFinite R S :=
    (RingHom.quasiFinite_algebraMap : (algebraMap R S).QuasiFinite ↔ Algebra.QuasiFinite R S).mp <|
      RingHom.QuasiFinite.of_finite <| RingHom.finite_algebraMap.mpr inferInstance
  have hprimesOver : ((maximalIdeal R).primesOver S).Finite :=
    Algebra.QuasiFinite.finite_primesOver (R := R) (S := S) (maximalIdeal R)
  have hmax : { J : Ideal S | J.IsMaximal }.Finite := by
    -- Every maximal ideal of `S` lies over the unique maximal ideal of the local ring `R`.
    refine hprimesOver.subset ?_
    intro J hJ
    letI : J.IsMaximal := hJ
    refine ⟨hJ.isPrime, ?_⟩
    have hcomap : maximalIdeal R = Ideal.comap (algebraMap R S) J :=
      (IsLocalRing.eq_maximalIdeal <|
        Ideal.isMaximal_comap_of_isIntegral_of_isMaximal J
      ).symm
    letI : J.LiesOver (maximalIdeal R) := ⟨by simpa [Ideal.under_def] using hcomap⟩
    exact inferInstance
  exact (MaximalSpectrum.equivSubtype S).finite_iff.mpr hmax

/-- Helper for Lemma 10.72.11: if the infimum of the localized depths is a natural number, then
that minimum is attained at some maximal ideal of `S`. -/
private theorem depth_iInf_attained_at_maximalIdeal_of_finite_algebra
    [Module.Finite R S] {N' : Type w}
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] {n : ℕ}
    (hdepth :
      (⨅ m : MaximalSpectrum S,
        moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N')) = n) :
    ∃ m : MaximalSpectrum S,
      moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N') = n := by
  letI : Finite (MaximalSpectrum S) := finite_maximalSpectrum_of_finite_algebra (R := R) (S := S)
  have hnonempty : Nonempty (MaximalSpectrum S) := by
    -- If there were no maximal ideals, the indexed infimum would be `⊤`, contradicting
    -- the hypothesis that it is the natural number `n`.
    by_contra hempty
    letI : IsEmpty (MaximalSpectrum S) := not_nonempty_iff.mp hempty
    simpa [iInf_of_empty] using hdepth
  -- `ℕ∞` infima with a nonempty index set are attained, so specialize that owner theorem here.
  obtain ⟨m, hm⟩ := ENat.exists_eq_iInf
    (fun m : MaximalSpectrum S ↦
      moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N'))
  refine ⟨m, ?_⟩
  simpa [hdepth] using hm

/-- Helper for Lemma 10.72.11: a nontrivial finite module over the finite target algebra has at
least one maximal localization of finite depth. -/
private theorem exists_maximalIdeal_with_finite_localized_depth_of_nontrivial
    [Module.Finite R S] [Nontrivial N] :
    ∃ m : MaximalSpectrum S,
      moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N) ≠ ⊤ := by
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  obtain ⟨q, hq_assoc⟩ := associatedPrimes.nonempty S N
  obtain ⟨mI, hmI_max, hqm⟩ := Ideal.exists_le_maximal q hq_assoc.1.ne_top
  let m : MaximalSpectrum S := ⟨mI, hmI_max⟩
  have hq_range :
      q ∈ Set.range (Ideal.comap (algebraMap S (Localization.AtPrime m.asIdeal))) := by
    rw [mem_range_comap_iff_disjoint_of_isPrime_for_entry m.asIdeal.primeCompl hq_assoc.1]
    exact Set.disjoint_left.2 fun x hxcomp hxq ↦ hxcomp (hqm hxq)
  have hq_loc_assoc : q ∈ associatedPrimes S (LocalizedModule.AtPrime m.asIdeal N) := by
    rw [← associatedPrimes_inter_localization_range_eq
      (S := m.asIdeal.primeCompl) (R := S) (M := N)]
    exact ⟨hq_assoc, hq_range⟩
  letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
    IsLocalization.isNoetherianRing
      m.asIdeal.primeCompl
      (Localization.AtPrime m.asIdeal)
      inferInstance
  have hnontrivial_loc : Nontrivial (LocalizedModule.AtPrime m.asIdeal N) := by
    by_contra hsub
    letI : Subsingleton (LocalizedModule.AtPrime m.asIdeal N) :=
      not_nontrivial_iff_subsingleton.mp hsub
    exact (not_isAssociatedPrime_of_subsingleton hq_loc_assoc)
  have hfinite_loc :
      moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N) < ⊤ := by
    simpa [moduleDepth] using
      Ideal.depth_lt_top_of_smul_top_ne_top
        (R := Localization.AtPrime m.asIdeal)
        (I := maximalIdeal (Localization.AtPrime m.asIdeal))
        (M := LocalizedModule.AtPrime m.asIdeal N)
        (maximalIdeal_smul_top_ne_top_for_entry
          (A := Localization.AtPrime m.asIdeal)
          (M := LocalizedModule.AtPrime m.asIdeal N))
  exact ⟨m, ne_of_lt hfinite_loc⟩

/-- Helper for Lemma 10.72.11: once the infimum of the maximal-local depths is the natural number
`n`, the source depth is exactly `n`. -/
private theorem moduleDepth_eq_of_iInf_localizedModule_eq_nat
    [Module.Finite R S] {N' : Type w}
    [AddCommGroup N'] [Module S N'] [Module R N'] [IsScalarTower R S N']
    [Module.Finite S N'] {n : ℕ}
    (hdepth :
      (⨅ m : MaximalSpectrum S,
        moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N')) = n) :
    letI : Module.Finite R N' := Module.Finite.trans S N'
    moduleDepth R N' = n := by
  letI : Module.Finite R N' := Module.Finite.trans S N'
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  let depthLoc : MaximalSpectrum S → ℕ∞ := fun m ↦
    moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N')
  induction n generalizing N' with
  | zero =>
      -- The attained zero-depth localization contracts an associated maximal ideal back to `R`.
      obtain ⟨m, hm⟩ :=
        depth_iInf_attained_at_maximalIdeal_of_finite_algebra
          (R := R) (S := S) (N' := N') (n := 0) hdepth
      letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
        IsLocalization.isNoetherianRing
          m.asIdeal.primeCompl
          (Localization.AtPrime m.asIdeal)
          inferInstance
      have hloc_assoc :
          maximalIdeal (Localization.AtPrime m.asIdeal) ∈
            associatedPrimes (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal N') :=
        maximalIdeal_mem_associatedPrimes_of_moduleDepth_eq_zero
          (A := Localization.AtPrime m.asIdeal)
          (M := LocalizedModule.AtPrime m.asIdeal N')
          hm
      have hsource_assoc : m.asIdeal ∈ associatedPrimes S N' :=
        mem_associatedPrimes_of_maximalIdeal_mem_atPrime
          (S := S) (X := N') (q := m.asIdeal) hloc_assoc
      have hmax_assoc :
          maximalIdeal R ∈ associatedPrimes R N' := by
        rw [← associatedPrimes_restrictScalars_eq_image_comap
          (R := R) (S := S) (M := N')]
        exact ⟨m.asIdeal, hsource_assoc,
          comap_maximalIdeal_eq_of_finite (R := R) (S := S) (m := m)⟩
      exact
        moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes
          (A := R) (M := N') hmax_assoc
  | succ n ih =>
      have hnontrivial : Nontrivial N' := by
        by_contra hsub
        letI : Subsingleton N' := not_nontrivial_iff_subsingleton.mp hsub
        have hlocal_top : ∀ m : MaximalSpectrum S, depthLoc m = ⊤ := by
          intro m
          letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
            IsLocalization.isNoetherianRing
              m.asIdeal.primeCompl
              (Localization.AtPrime m.asIdeal)
              inferInstance
          letI : Subsingleton (LocalizedModule.AtPrime m.asIdeal N') := by infer_instance
          exact
            moduleDepth_eq_top_of_subsingleton
              (A := Localization.AtPrime m.asIdeal)
              (M := LocalizedModule.AtPrime m.asIdeal N')
        have hdepth_top : ((n + 1 : ℕ) : ℕ∞) = ⊤ := by
          simpa [depthLoc, hlocal_top] using hdepth.symm
        have hnot_top : ¬ (((n + 1 : ℕ) : ℕ∞) = ⊤) :=
          ENat.coe_ne_top (n + 1)
        exact hnot_top hdepth_top
      letI : Nontrivial N' := hnontrivial
      -- Positive localized depth everywhere rules out `maximalIdeal R` as an associated prime.
      have hmax_not_assoc : maximalIdeal R ∉ associatedPrimes R N' := by
        intro hmax
        rw [← associatedPrimes_restrictScalars_eq_image_comap
          (R := R) (S := S) (M := N')] at hmax
        rcases hmax with ⟨q, hq_assoc, hq_comap⟩
        letI : q.IsPrime := (AssociatedPrimes.mem_iff.mp hq_assoc).isPrime
        have hq_comap_max : (Ideal.comap (algebraMap R S) q).IsMaximal := by
          simpa [hq_comap] using (inferInstance : (maximalIdeal R).IsMaximal)
        letI : q.IsMaximal :=
          Ideal.isMaximal_of_isIntegral_of_isMaximal_comap
            (R := R) (S := S) q hq_comap_max
        let m : MaximalSpectrum S := ⟨q, inferInstance⟩
        letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
          IsLocalization.isNoetherianRing
            m.asIdeal.primeCompl
            (Localization.AtPrime m.asIdeal)
            inferInstance
        have hloc_assoc :
            maximalIdeal (Localization.AtPrime m.asIdeal) ∈
              associatedPrimes (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal N') :=
          maximalIdeal_mem_associatedPrimes_atPrime_of_mem
            (S := S) (X := N') (q := q) hq_assoc
        have hloc_zero :
            moduleDepth (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal N') = 0 :=
          moduleDepth_eq_zero_of_maximalIdeal_mem_associatedPrimes
            (A := Localization.AtPrime m.asIdeal)
            (M := LocalizedModule.AtPrime m.asIdeal N')
            hloc_assoc
        have hlocal_pos :
            ((n + 1 : ℕ) : ℕ∞) ≤ depthLoc m := by
          simpa [depthLoc, hdepth] using (iInf_le depthLoc m)
        have hnat_pos : ¬ (((n + 1 : ℕ) : ℕ∞) ≤ 0) := by
          exact not_le_of_gt (by exact_mod_cast Nat.succ_pos n)
        exact hnat_pos (by simpa [depthLoc, hloc_zero] using hlocal_pos)
      have hforall :
          ∀ q ∈ associatedPrimes R N', ¬ maximalIdeal R ≤ q := by
        intro q hq hmq
        have hq_le : q ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hq.1.ne_top
        exact hmax_not_assoc (show maximalIdeal R ∈ associatedPrimes R N' from
          Eq.ndrec hq (by rw [le_antisymm hq_le hmq]))
      -- Choose the regular element from `maximalIdeal R` and quotient by its image in `S`.
      obtain ⟨f, hf, hreg⟩ :=
        (exists_mem_isSMulRegular_iff_forall_not_le_associatedPrimes
          (R := R) (M := N') (I := maximalIdeal R)).2 hforall
      let Q := QuotSMulTop (algebraMap R S f) N'
      obtain ⟨m₀, hm₀⟩ :=
        depth_iInf_attained_at_maximalIdeal_of_finite_algebra
          (R := R) (S := S) (N' := N') (n := n + 1) hdepth
      have hdepth_Q_ge :
          ∀ m : MaximalSpectrum S,
            (n : ℕ∞) ≤
              moduleDepth (Localization.AtPrime m.asIdeal)
                (LocalizedModule.AtPrime m.asIdeal Q) := by
        intro m
        have hlocal_ge :
            ((n + 1 : ℕ) : ℕ∞) ≤ depthLoc m := by
          simpa [depthLoc, hdepth] using (iInf_le depthLoc m)
        -- Each localized depth drops by exactly one after quotienting by the chosen regular
        -- element.
        calc
          (n : ℕ∞) = ((n + 1 : ℕ∞) - 1) := by
            exact_mod_cast Nat.succ_sub_one n
          _ ≤ depthLoc m - 1 := by
            exact tsub_le_tsub_right hlocal_ge 1
          _ =
            moduleDepth (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal Q) := by
                simpa [depthLoc, Q] using
                  (moduleDepth_localized_quotSMulTop_eq_sub_one_of_regular
                    (R := R) (S := S) (N := N') m hf hreg).symm
      have hdepth_Q_at_m₀ :
          moduleDepth (Localization.AtPrime m₀.asIdeal)
            (LocalizedModule.AtPrime m₀.asIdeal Q) = n := by
        calc
          moduleDepth (Localization.AtPrime m₀.asIdeal)
              (LocalizedModule.AtPrime m₀.asIdeal Q)
              = depthLoc m₀ - 1 := by
                  simpa [depthLoc, Q] using
                    (moduleDepth_localized_quotSMulTop_eq_sub_one_of_regular
                      (R := R) (S := S) (N := N') m₀ hf hreg)
          _ = n := by
              simpa [depthLoc, hm₀] using
                (show (((n + 1 : ℕ) : ℕ∞) - 1) = (n : ℕ∞) by
                  exact_mod_cast Nat.succ_sub_one n)
      have hdepth_Q :
          (⨅ m : MaximalSpectrum S,
            moduleDepth (Localization.AtPrime m.asIdeal)
              (LocalizedModule.AtPrime m.asIdeal Q)) = n := by
        refine le_antisymm ?_ ?_
        · simpa [hdepth_Q_at_m₀] using
            (iInf_le
              (fun m : MaximalSpectrum S ↦
                moduleDepth (Localization.AtPrime m.asIdeal)
                  (LocalizedModule.AtPrime m.asIdeal Q))
              m₀)
        · exact le_iInf hdepth_Q_ge
      have hsource_Q : moduleDepth R Q = n := by
        letI : Module.Finite R Q := Module.Finite.trans S Q
        exact ih (N' := Q) hdepth_Q
      have hsource_drop :
          moduleDepth R Q = moduleDepth R N' - 1 := by
        calc
          moduleDepth R Q = moduleDepth R (QuotSMulTop f N') := by
            simpa [Q] using
              moduleDepth_eq_of_linearEquiv
                (A := R)
                (quotSMulTop_algebraMap_restrictScalars_equiv
                  (R := R) (S := S) (N := N') f)
          _ = moduleDepth R N' - 1 := by
              simpa using
                (moduleDepth_quotSMulTop_eq_sub_one_of_regular_local_poly
                  (A := R) (M := N') hf hreg)
      have hone :
          (1 : ℕ∞) ≤ moduleDepth R N' :=
        one_le_moduleDepth_of_mem_maximalIdeal_of_isSMulRegular
          (A := R) (M := N') hf hreg
      -- Convert the quotient-depth computation back to the source depth.
      calc
        moduleDepth R N' = moduleDepth R Q + 1 := by
          rw [hsource_drop]
          exact (tsub_add_cancel_of_le hone).symm
        _ = n + 1 := by simpa [hsource_Q]

/- Domain-style sampling:
* primary domain: local depth for finite modules under a finite ring map, compared across maximal
  localizations of the target ring;
* sampled owner declarations of the same kind:
  `moduleDepth`,
  `Module.Finite`,
  `MaximalSpectrum`,
  `Localization.AtPrime`;
* best owner abstraction: the chapter owner surface for local depth is `moduleDepth`, the finite
  algebra hypothesis is the canonical owner instance `[Module.Finite R S]`, and the canonical
  index type for maximal ideals is `MaximalSpectrum S`;
* source/core/bridge triage:
  `source-facing`: the equality between the depth over the source local ring and the infimum of
    the depths at maximal localizations of the finite target algebra;
  `core/canonical`: `moduleDepth` and `MaximalSpectrum`;
  `bridge/view`: the maximal localizations `Localization.AtPrime m.asIdeal` and localized modules
    `LocalizedModule.AtPrime m.asIdeal N`.

Primitive data are only the local ring `R`, the finite `R`-algebra `S`, the finite `S`-module
`N`, and the family of maximal localizations indexed by `MaximalSpectrum S`. The old surface
spelled this family through `PrimeSpectrum S` together with an `IsMaximal` witness and unfolded
local depth back to `Ideal.depth (maximalIdeal _)`; both are derived API and should be replaced by
the owner abstractions here. The finiteness of `N` over `R` is derived from the owner instance
`[Module.Finite R S]` together with `[Module.Finite S N]`, so it should not remain a primitive
public assumption either.
-/
-- Proof sketch: for each maximal ideal `𝔪ᵢ` of `S`, compare `depth_{𝔪}(N)` with the local depth of
-- `N_{𝔪ᵢ}`. The case where one localized depth is `0` is detected by associated primes after
-- localization and contraction. For positive minimum depth, choose an element of `maximalIdeal R`
-- that is `N`-regular, use the finite-map comparison to see it stays regular at every maximal
-- localization of `S`, apply the depth-drop lemma after quotienting by this element, and conclude
-- by induction on the minimum localized depth.
/-- Lemma 10.72.11: for a finite ring map `R → S` from a Noetherian local ring `R` and a finite
`S`-module `N`, the depth of `N` over `R` with respect to the maximal ideal equals the minimum of
the depths of the localizations `N_𝔪` over the local rings `S_𝔪`, as `𝔪` ranges over the maximal
ideals of `S`. -/
theorem depth_eq_sInf_depth_localizedModule_at_maximalIdeals_of_finite
    [Module.Finite R S] :
    letI : Module.Finite R N := Module.Finite.trans S N
    (⨅ m : MaximalSpectrum S,
      moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N)) =
      moduleDepth R N := by
  letI : Module.Finite R N := Module.Finite.trans S N
  let depthLoc : MaximalSpectrum S → ℕ∞ := fun m ↦
    moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N)
  by_cases hsub : Subsingleton N
  · letI : Subsingleton N := hsub
    have hlocal_top :
        ∀ m : MaximalSpectrum S, depthLoc m = ⊤ := by
      intro m
      letI : IsNoetherianRing (Localization.AtPrime m.asIdeal) :=
        IsLocalization.isNoetherianRing
          m.asIdeal.primeCompl
          (Localization.AtPrime m.asIdeal)
          (IsNoetherianRing.of_finite R S)
      letI : Subsingleton (LocalizedModule.AtPrime m.asIdeal N) := by infer_instance
      exact
        moduleDepth_eq_top_of_subsingleton
          (A := Localization.AtPrime m.asIdeal)
          (M := LocalizedModule.AtPrime m.asIdeal N)
    simp [depthLoc, hlocal_top, moduleDepth_eq_top_of_subsingleton (A := R) (M := N)]
  · letI : Nontrivial N := not_subsingleton_iff_nontrivial.mp hsub
    -- Rule out the `⊤` branch by a finite-depth localization, then reduce to the induction
    -- theorem on the natural-number value of the infimum.
    have hiInf_ne_top : (⨅ m : MaximalSpectrum S, depthLoc m) ≠ ⊤ := by
      rcases exists_maximalIdeal_with_finite_localized_depth_of_nontrivial
        (R := R) (S := S) (N := N) with ⟨m, hm⟩
      intro htop
      have hlocal_top : depthLoc m = ⊤ := by
        exact top_unique (by simpa [depthLoc, htop] using (iInf_le depthLoc m))
      exact hm hlocal_top
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hiInf_ne_top
    have hsource :
        moduleDepth R N = n :=
      moduleDepth_eq_of_iInf_localizedModule_eq_nat
        (R := R) (S := S) (N' := N) (n := n) (by simpa [depthLoc] using hn.symm)
    calc
      (⨅ m : MaximalSpectrum S,
        moduleDepth (Localization.AtPrime m.asIdeal) (LocalizedModule.AtPrime m.asIdeal N))
          = n := by simpa [depthLoc] using hn.symm
      _ = moduleDepth R N := hsource.symm

end
