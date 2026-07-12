import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap15.Lemma_15_11_6
import StacksProject_2024.Chap15.Lemma_15_12_1
import StacksProject_2024.Chap15.Lemma_15_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PrimeSpectrum
open RingPairCat
open scoped PrimeSpectrum

universe u

noncomputable section

section

variable {A : Type u} [CommRing A]
variable [RingPairCat.henselianPairInclusion.IsRightAdjoint]

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: extending two ideals along any algebra map preserves equality of
their zero loci in prime spectra. -/
private theorem zeroLocus_map_eq_of_zeroLocus_eq (I J : Ideal A)
    (hV : V((I : Set A)) = V((J : Set A)))
    {B : Type u} [CommRing B] [Algebra A B] :
    V((Ideal.map (algebraMap A B) I : Set B)) = V((Ideal.map (algebraMap A B) J : Set B)) := by
  -- Proof comment: compare membership pointwise after contracting prime ideals along `A → B`.
  ext q
  constructor
  · intro hq
    have hIq : I ≤ Ideal.comap (algebraMap A B) q.asIdeal := by
      exact Ideal.map_le_iff_le_comap.mp <|
        (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) I : Set B)).mp hq
    have hqI :
        PrimeSpectrum.comap (algebraMap A B) q ∈ V((I : Set A)) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
        (I : Set A)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hIq
    have hqJ :
        PrimeSpectrum.comap (algebraMap A B) q ∈ V((J : Set A)) := by
      simpa [hV] using hqI
    exact (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) J : Set B)).mpr <|
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
            (J : Set A)).mp hqJ
  · intro hq
    have hJq : J ≤ Ideal.comap (algebraMap A B) q.asIdeal := by
      exact Ideal.map_le_iff_le_comap.mp <|
        (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) J : Set B)).mp hq
    have hqJ :
        PrimeSpectrum.comap (algebraMap A B) q ∈ V((J : Set A)) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
        (J : Set A)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hJq
    have hqI :
        PrimeSpectrum.comap (algebraMap A B) q ∈ V((I : Set A)) := by
      simpa [hV] using hqJ
    exact (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) I : Set B)).mpr <|
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
            (I : Set A)).mp hqI

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: a surjective ring map with nilpotent kernel elements induces a
bijection on idempotents. -/
private theorem bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hsurj : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Function.Bijective f.idempotentMap := by
  constructor
  · intro e₁ e₂ h
    apply Subtype.ext
    -- Proof comment: unique lifting across the nilpotent kernel identifies equal target
    -- idempotents with equal source lifts.
    obtain ⟨e, -, huniq⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker (f e₁.1) (hsurj _) (e₁.2.map f)
    exact (huniq _ ⟨e₁.2, rfl⟩).trans
      (huniq _ ⟨e₂.2, by simpa using (congrArg Subtype.val h).symm⟩).symm
  · intro e
    -- Proof comment: surjectivity supplies a lift, and the same lifting lemma makes it
    -- idempotent.
    obtain ⟨e', he', -⟩ :=
      existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker e.1 (hsurj _) e.2
    refine ⟨⟨e', he'.1⟩, ?_⟩
    exact Subtype.ext he'.2

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: the quotient map from `B ⧸ K` to `B ⧸ √K` is surjective. -/
private theorem radicalQuotientFactor_surjective {B : Type u} [CommRing B] (K : Ideal B) :
    Function.Surjective (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  -- Proof comment: every class modulo `√K` is represented by the same element modulo `K`.
  exact ⟨Ideal.Quotient.mk K y, rfl⟩

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: every element in the kernel of `B ⧸ K → B ⧸ √K` is nilpotent. -/
private theorem radicalQuotientFactor_ker_nilpotent_elements
    {B : Type u} [CommRing B] (K : Ideal B) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)),
      IsNilpotent x := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  change Ideal.Quotient.mk K.radical y = 0 at hx
  have hy : y ∈ K.radical := Ideal.Quotient.eq_zero_iff_mem.mp hx
  rcases Ideal.mem_radical_iff.mp hy with ⟨n, hn⟩
  -- Proof comment: membership in the radical means a power lands back in `K`, so the class is
  -- nilpotent in `B ⧸ K`.
  refine ⟨n, ?_⟩
  change Ideal.Quotient.mk K (y ^ n) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: the factor map `B ⧸ K → B ⧸ √K` induces a bijection on
idempotents. -/
private theorem radicalQuotientFactor_bijective_idempotentMap
    {B : Type u} [CommRing B] (K : Ideal B) :
    Function.Bijective
      (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)).idempotentMap := by
  -- Proof comment: apply the nilpotent-kernel idempotent-lifting theorem to the radical factor.
  exact bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical))
    (radicalQuotientFactor_surjective K)
    (radicalQuotientFactor_ker_nilpotent_elements K)

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: composing with a bijection preserves bijectivity. -/
private theorem bijective_iff_bijective_comp
    {α β γ : Type u} (f : α → β) (g : β → γ) (hg : Function.Bijective g) :
    Function.Bijective f ↔ Function.Bijective (g ∘ f) := by
  constructor
  · intro hf
    exact hg.comp hf
  · intro hgf
    constructor
    · intro x y hxy
      exact hgf.1 (by simpa [Function.comp, hxy])
    · intro z
      obtain ⟨x, hx⟩ := hgf.2 (g z)
      exact ⟨x, hg.1 <| by simpa [Function.comp] using hx⟩

/-- Helper for Lemma 15.12.6: bijectivity of the quotient idempotent map depends only on the
radical of the ideal. -/
private theorem bijective_idempotentMap_iff_of_radical_eq
    {B : Type u} [CommRing B] (K L : Ideal B) (hKL : K.radical = L.radical) :
    Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
      Function.Bijective (Ideal.Quotient.mk L).idempotentMap := by
  have hK :
      Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
        Function.Bijective (Ideal.Quotient.mk K.radical).idempotentMap := by
    let φ : B ⧸ K →+* B ⧸ K.radical :=
      Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)
    have hφ : Function.Bijective φ.idempotentMap :=
      radicalQuotientFactor_bijective_idempotentMap K
    have hcomp :
        φ.idempotentMap ∘ (Ideal.Quotient.mk K).idempotentMap =
          (Ideal.Quotient.mk K.radical).idempotentMap := by
      funext e
      rfl
    -- Proof comment: passing from `B ⧸ K` to `B ⧸ √K` does not change idempotents.
    simpa [φ, hcomp] using
      (bijective_iff_bijective_comp
        (Ideal.Quotient.mk K).idempotentMap φ.idempotentMap hφ)
  have hL :
      Function.Bijective (Ideal.Quotient.mk L).idempotentMap ↔
        Function.Bijective (Ideal.Quotient.mk L.radical).idempotentMap := by
    let φ : B ⧸ L →+* B ⧸ L.radical :=
      Ideal.Quotient.factor (Ideal.le_radical : L ≤ L.radical)
    have hφ : Function.Bijective φ.idempotentMap :=
      radicalQuotientFactor_bijective_idempotentMap L
    have hcomp :
        φ.idempotentMap ∘ (Ideal.Quotient.mk L).idempotentMap =
          (Ideal.Quotient.mk L.radical).idempotentMap := by
      funext e
      rfl
    -- Proof comment: the same reduced-quotient comparison works for `L`.
    simpa [φ, hcomp] using
      (bijective_iff_bijective_comp
        (Ideal.Quotient.mk L).idempotentMap φ.idempotentMap hφ)
  rw [hK, hL, hKL]

/-- Helper for Lemma 15.12.6: the integral idempotent-lifting criterion depends only on the
closed subset `V(I)`. -/
private theorem hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq_local (I J : Ideal A)
    (hV : V((I : Set A)) = V((J : Set A))) :
    Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A) I ↔
      Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := A) J := by
  -- Proof comment: for every integral `A`-algebra `B`, the mapped ideals have the same zero
  -- locus, hence the same radical. Passing to the common reduced quotient preserves idempotents,
  -- so the Chapter 15 idempotent-lifting predicate is unchanged.
  constructor
  · intro h B _ _ _
    let K : Ideal B := Ideal.map (algebraMap A B) I
    let L : Ideal B := Ideal.map (algebraMap A B) J
    have hKL : K.radical = L.radical := by
      exact PrimeSpectrum.zeroLocus_eq_iff.mp <|
        zeroLocus_map_eq_of_zeroLocus_eq I J hV
    have hK : Function.Bijective (Ideal.Quotient.mk K).idempotentMap := by
      simpa [K] using (h (B := B))
    exact (bijective_idempotentMap_iff_of_radical_eq K L hKL).mp hK
  · intro h B _ _ _
    let K : Ideal B := Ideal.map (algebraMap A B) I
    let L : Ideal B := Ideal.map (algebraMap A B) J
    have hKL : K.radical = L.radical := by
      exact PrimeSpectrum.zeroLocus_eq_iff.mp <|
        zeroLocus_map_eq_of_zeroLocus_eq I J hV
    have hL : Function.Bijective (Ideal.Quotient.mk L).idempotentMap := by
      simpa [L] using (h (B := B))
    exact (bijective_idempotentMap_iff_of_radical_eq K L hKL).mpr hL

/-- Helper for Lemma 15.12.6: henselianity of `(A, I)` depends only on the closed subset
`V(I) ⊆ Spec A`. -/
private theorem henselianRing_iff_of_zeroLocus_eq_local (I J : Ideal A)
    (hV : V((I : Set A)) = V((J : Set A))) :
    HenselianRing A I ↔ HenselianRing A J := by
  let Q : Ideal A → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal A → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (K : Ideal A) : List Prop :=
    [HenselianRing A K, K.HasEtaleLiftProperty, Q K, P K, K.SatisfiesGabberRootCriterion]
  have hTfaeI : List.TFAE (T I) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion I
  have hI : HenselianRing A I ↔ P I := by
    -- Proof comment: isolate the `0 ↔ 3` branch of the Chapter 15 equivalence for `I`.
    simpa [T] using hTfaeI.out 0 3
  have hIJ : P I ↔ P J :=
    hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq_local I J hV
  have hTfaeJ : List.TFAE (T J) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion J
  have hJ : HenselianRing A J ↔ P J := by
    -- Proof comment: the same TFAE branch converts back for `J`.
    simpa [T] using hTfaeJ.out 0 3
  exact (hI.trans hIJ).trans hJ.symm

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: a morphism of ring pairs is determined by its underlying ring
homomorphism. -/
private theorem ringPair_hom_ext {X Y : RingPairCat.{u}} {f g : X ⟶ Y}
    (hfg : RingPairCat.ringHom f = RingPairCat.ringHom g) :
    f = g := by
  -- Proof comment: this is exactly the extensionality lemma already established for `RingPairCat`.
  exact RingPairCat.hom_ext hfg

omit [RingPairCat.henselianPairInclusion.IsRightAdjoint] in
/-- Helper for Lemma 15.12.6: the quotient maps attached to a ring hom respecting ideals form the
commutative square needed for a morphism of ring pairs. -/
private theorem ringPair_toIdealPair_hom_square {X : RingPairCat.{u}}
    {B : Type u} [CommRing B] [Algebra X.ring B] (J : Ideal B)
    (hXJ : X.ideal ≤ Ideal.comap (algebraMap X.ring B) J) :
    CommRingCat.ofHom (algebraMap X.ring B) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal) ≫
        CommRingCat.ofHom (Ideal.quotientMap J (algebraMap X.ring B) hXJ) := by
  -- Proof comment: after unpacking `X`, this reduces to the canonical square from
  -- `pairOfIdealMap`; it is the transport needed to turn a ring hom plus an ideal inclusion into
  -- a morphism of ring pairs.
  ext a
  rfl

/-- Helper for Lemma 15.12.6: a ring hom out of a ring pair that carries the distinguished ideal
into `J` induces a canonical morphism of ring pairs into `(B, J)`. -/
private abbrev ringPairToIdealPairMap {X : RingPairCat.{u}}
    {B : Type u} [CommRing B] [Algebra X.ring B] (J : Ideal B)
    (hXJ : X.ideal ≤ Ideal.comap (algebraMap X.ring B) J) :
    X ⟶ pairOfIdeal J :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom (algebraMap X.ring B))
      (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap X.ring B) hXJ))
      (ringPair_toIdealPair_hom_square (X := X) J hXJ)

/-- Helper for Lemma 15.12.6: maps from `(A, I)` into a henselian target pair factor uniquely
through the chosen henselization ring of `(A, I)`. -/
private theorem existsUnique_henselizationRingHom_of_henselian_target (I : Ideal A)
    {B : Type u} [CommRing B] [Algebra A B] (K : Ideal B)
    (hK : HenselianRing B K) (hIK : I ≤ Ideal.comap (algebraMap A B) K) :
    ∃! g : henselizationRing (pairOfIdeal I) →+* B,
      g.comp (toHenselization (pairOfIdeal I)) = algebraMap A B := by
  -- Proof comment: the source route uses the adjunction `henselization ⊣ henselianPairInclusion`
  -- and the unit identity `Adjunction.homEquiv_unit`. The remaining work is to package a raw ring
  -- hom `g` together with `g ∘ toHenselization = algebraMap` as a morphism of ring pairs out of
  -- the henselization pair, then apply `ringPair_hom_ext`.
  let adj := Adjunction.ofIsRightAdjoint henselianPairInclusion
  let target : HenselianPairCat.{u} := ⟨pairOfIdeal K, hK⟩
  let pairMap : pairOfIdeal I ⟶ henselianPairInclusion.obj target :=
    pairOfIdealMap I K hIK
  let comparison : henselization (pairOfIdeal I) ⟶ target :=
    (adj.homEquiv (pairOfIdeal I) target).symm pairMap
  have hcomparison :
      adj.homEquiv (pairOfIdeal I) target comparison = pairMap := by
    exact Equiv.apply_symm_apply (adj.homEquiv (pairOfIdeal I) target) pairMap
  refine ⟨RingPairCat.ringHom comparison.hom, ?_, ?_⟩
  · -- Proof comment: read the adjunction unit identity on underlying rings.
    have hunit :
        pairMap = (adj.unit.app (pairOfIdeal I)) ≫ comparison.hom := by
      calc
        pairMap = adj.homEquiv (pairOfIdeal I) target comparison := hcomparison.symm
        _ = (adj.unit.app (pairOfIdeal I)) ≫ comparison.hom :=
          adj.homEquiv_unit (X := pairOfIdeal I) (Y := target) (f := comparison)
    have hunitRing := congrArg
      (fun k :
          pairOfIdeal I ⟶ henselianPairInclusion.obj target ↦
            RingPairCat.ringHom k) hunit
    simpa [pairMap, RingPairCat.toHenselization, RingPairCat.ringHom] using
      hunitRing.symm
  · intro g hg
    -- Proof comment: package `g` as a morphism of henselian pairs and compare its adjoint
    -- transpose with the original map `(A, I) → (B, K)`.
    letI : Algebra (henselizationRing (pairOfIdeal I)) B := g.toAlgebra
    have hmap :
        henselizationIdeal (pairOfIdeal I) ≤ Ideal.comap g K := by
      rw [henselizationIdeal_eq_map (X := pairOfIdeal I), Ideal.map_le_iff_le_comap,
        Ideal.comap_comap]
      simpa [hg] using hIK
    let liftedPairMap :
        henselizationPair (pairOfIdeal I) ⟶ henselianPairInclusion.obj target :=
      ringPairToIdealPairMap (X := henselizationPair (pairOfIdeal I)) K hmap
    let lifted : henselization (pairOfIdeal I) ⟶ target :=
      ObjectProperty.homMk liftedPairMap
    have hpair :
        (adj.unit.app (pairOfIdeal I)) ≫ liftedPairMap = pairMap := by
      -- Proof comment: both pair morphisms restrict to the same ring map `A → B`, namely `g`
      -- after the henselization unit, so pair extensionality identifies them.
      apply RingPairCat.hom_ext
      simpa [pairMap, liftedPairMap, RingPairCat.toHenselization, RingPairCat.ringHom] using hg
    have htranspose :
        adj.homEquiv (pairOfIdeal I) target lifted = pairMap := by
      exact (adj.homEquiv_unit (X := pairOfIdeal I) (Y := target) (f := lifted)).trans hpair
    have hlifted : lifted = comparison := by
      apply (adj.homEquiv (pairOfIdeal I) target).injective
      calc
        adj.homEquiv (pairOfIdeal I) target lifted = pairMap := htranspose
        _ = adj.homEquiv (pairOfIdeal I) target comparison := hcomparison.symm
    exact congrArg RingPairCat.ringHom <|
      congrArg (fun k : henselization (pairOfIdeal I) ⟶ target ↦ k.hom) hlifted

/-- Helper for Lemma 15.12.6: after extending ideals to any `A`-algebra, equal zero loci should
still give equivalent henselian conditions. -/
private theorem henselianRing_map_iff_of_zeroLocus_eq (I J : Ideal A)
    (hV : V((I : Set A)) = V((J : Set A)))
    {B : Type u} [CommRing B] [Algebra A B] :
    HenselianRing B (Ideal.map (algebraMap A B) I) ↔
      HenselianRing B (Ideal.map (algebraMap A B) J) := by
  -- Proof comment: specialize the Chapter 15 zero-locus invariance theorem after base change to
  -- the `A`-algebra `B`.
  exact henselianRing_iff_of_zeroLocus_eq_local
    (Ideal.map (algebraMap A B) I) (Ideal.map (algebraMap A B) J)
    (zeroLocus_map_eq_of_zeroLocus_eq I J hV)

-- Proof sketch: Lemma `15.11.7` shows that `V(I) = V(J)` makes `(A, I)` henselian exactly when
-- `(A, J)` is henselian. Applying the universal property of the left adjoint from Lemma `15.12.1`
-- to the two henselization pairs gives unique `A`-algebra maps in both directions, and the same
-- uniqueness forces the composites to be identities.
/-- Lemma 15.12.6: if two ideals of `A` have the same zero locus in `Spec A`, then the chosen
pair-henselization functor yields canonically isomorphic `A`-algebras for the pairs `(A, I)` and
`(A, J)`. -/
@[stacks 0F0L]
theorem henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq (I J : Ideal A)
    (hV : V((I : Set A)) = V((J : Set A))) :
    ∃! e : henselizationRing (pairOfIdeal I) ≃ₐ[A] henselizationRing (pairOfIdeal J),
      e.toRingHom.comp
        (toHenselization (pairOfIdeal I)) =
      toHenselization (pairOfIdeal J) := by
  -- Proof comment: source-faithful route.
  -- 1. Use `henselianRing_map_iff_of_zeroLocus_eq` to show `(A_J^h, I A_J^h)` and
  --    `(A_I^h, J A_I^h)` are henselian.
  -- 2. Apply `existsUnique_henselizationRingHom_of_henselian_target` in both directions.
  -- 3. Use the same uniqueness on the self-targets to force the composites to be identities.
  -- 4. Upgrade the forward map to an `A`-algebra equivalence by `AlgEquiv.ofBijective`, and
  --    deduce uniqueness from uniqueness of the underlying ring hom.
  let toI := toHenselization (pairOfIdeal I)
  let toJ := toHenselization (pairOfIdeal J)
  have hPairI :
      HenselianRing (henselizationRing (pairOfIdeal I)) (henselizationIdeal (pairOfIdeal I)) := by
    change HenselianRing (henselizationPair (pairOfIdeal I)).ring
      (henselizationPair (pairOfIdeal I)).ideal
    exact (henselization (pairOfIdeal I)).property
  have hPairJ :
      HenselianRing (henselizationRing (pairOfIdeal J)) (henselizationIdeal (pairOfIdeal J)) := by
    change HenselianRing (henselizationPair (pairOfIdeal J)).ring
      (henselizationPair (pairOfIdeal J)).ideal
    exact (henselization (pairOfIdeal J)).property
  have hHensI :
      HenselianRing (henselizationRing (pairOfIdeal I)) (Ideal.map toI I) := by
    -- Proof comment: the distinguished ideal of the henselization is the image of the source
    -- ideal, so the chosen henselization pair is henselian for `I A_I^h`.
    simpa [toI, henselizationIdeal_eq_map (X := pairOfIdeal I)] using hPairI
  have hHensJ :
      HenselianRing (henselizationRing (pairOfIdeal J)) (Ideal.map toJ J) := by
    -- Proof comment: the same identification gives the henselianity of `(A_J^h, J A_J^h)`.
    simpa [toJ, henselizationIdeal_eq_map (X := pairOfIdeal J)] using hPairJ
  have hHensJI :
      HenselianRing (henselizationRing (pairOfIdeal J)) (Ideal.map toJ I) := by
    -- Proof comment: equal zero loci let us replace `J A_J^h` by `I A_J^h`.
    exact (henselianRing_map_iff_of_zeroLocus_eq I J hV).mpr hHensJ
  have hHensIJ :
      HenselianRing (henselizationRing (pairOfIdeal I)) (Ideal.map toI J) := by
    -- Proof comment: symmetrically replace `I A_I^h` by `J A_I^h`.
    exact (henselianRing_map_iff_of_zeroLocus_eq I J hV).mp hHensI
  obtain ⟨f, hf_comp, hf_unique⟩ :=
    existsUnique_henselizationRingHom_of_henselian_target (I := I)
      (B := henselizationRing (pairOfIdeal J)) (K := Ideal.map toJ I)
      hHensJI Ideal.le_comap_map
  obtain ⟨g, hg_comp, hg_unique⟩ :=
    existsUnique_henselizationRingHom_of_henselian_target (I := J)
      (B := henselizationRing (pairOfIdeal I)) (K := Ideal.map toI J)
      hHensIJ Ideal.le_comap_map
  have hgf_id : g.comp f = RingHom.id _ := by
    obtain ⟨u, hu_comp, hu_unique⟩ :=
      existsUnique_henselizationRingHom_of_henselian_target (I := I)
        (B := henselizationRing (pairOfIdeal I)) (K := Ideal.map toI I)
        hHensI Ideal.le_comap_map
    have hcomp :
        (g.comp f).comp toI = algebraMap A (henselizationRing (pairOfIdeal I)) := by
      -- Proof comment: the composite still agrees with the unit map on `A` because each factor
      -- does.
      simpa [toI, toJ, RingHom.comp_assoc, hf_comp] using hg_comp
    have hid :
        (RingHom.id (henselizationRing (pairOfIdeal I))).comp toI =
          algebraMap A (henselizationRing (pairOfIdeal I)) := by
      rfl
    calc
      g.comp f = u := hu_unique _ hcomp
      _ = RingHom.id _ := hu_unique _ hid |> Eq.symm
  have hfg_id : f.comp g = RingHom.id _ := by
    obtain ⟨u, hu_comp, hu_unique⟩ :=
      existsUnique_henselizationRingHom_of_henselian_target (I := J)
        (B := henselizationRing (pairOfIdeal J)) (K := Ideal.map toJ J)
        hHensJ Ideal.le_comap_map
    have hcomp :
        (f.comp g).comp toJ = algebraMap A (henselizationRing (pairOfIdeal J)) := by
      -- Proof comment: the reverse composite satisfies the same unit equation on `A`.
      simpa [toI, toJ, RingHom.comp_assoc, hg_comp] using hf_comp
    have hid :
        (RingHom.id (henselizationRing (pairOfIdeal J))).comp toJ =
          algebraMap A (henselizationRing (pairOfIdeal J)) := by
      rfl
    calc
      f.comp g = u := hu_unique _ hcomp
      _ = RingHom.id _ := hu_unique _ hid |> Eq.symm
  have hleft : Function.LeftInverse g f := by
    intro x
    exact congrArg (fun h : henselizationRing (pairOfIdeal I) →+*
        henselizationRing (pairOfIdeal I) ↦ h x) hgf_id
  have hright : Function.RightInverse g f := by
    intro y
    exact congrArg (fun h : henselizationRing (pairOfIdeal J) →+*
        henselizationRing (pairOfIdeal J) ↦ h y) hfg_id
  let fAlg : henselizationRing (pairOfIdeal I) →ₐ[A] henselizationRing (pairOfIdeal J) :=
    { toRingHom := f
      commutes' := by
        intro a
        exact congrArg (fun h : A →+* henselizationRing (pairOfIdeal J) ↦ h a) hf_comp }
  let e : henselizationRing (pairOfIdeal I) ≃ₐ[A] henselizationRing (pairOfIdeal J) :=
    AlgEquiv.ofBijective fAlg ⟨hleft.injective, hright.surjective⟩
  refine ⟨e, ?_, ?_⟩
  · -- Proof comment: the algebra equivalence is built from the unique comparison map `f`.
    simpa [e, fAlg] using hf_comp
  · intro e' he'
    -- Proof comment: uniqueness of the underlying ring hom from the universal property forces
    -- the entire `A`-algebra equivalence.
    ext x
    have hring : e'.toRingHom = f := by
      exact hf_unique e'.toRingHom <| by simpa [toI, toJ] using he'
    simpa [e, fAlg] using congrArg
      (fun h : henselizationRing (pairOfIdeal I) →+*
          henselizationRing (pairOfIdeal J) ↦ h x) hring

end
