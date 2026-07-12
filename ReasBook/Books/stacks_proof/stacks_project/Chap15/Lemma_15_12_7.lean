import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap15.IdempotentLifting
import StacksProject_2024.Chap15.Lemma_15_12_1
import StacksProject_2024.Chap15.Lemma_15_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PrimeSpectrum
open RingPairCat
open scoped PrimeSpectrum
open scoped TensorProduct

universe u

noncomputable section

section

attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (J : Ideal B)

/- Domain-style sampling for Lemma 15.12.7:
- primary domain: pair henselization and its canonical base-change comparison map along a morphism
  of ring pairs;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `RingPairCat.henselizationRingMap`,
  `RingPairCat.toHenselization_naturality`,
  `RingPairCat.pairOfIdealMap`;
- owner abstraction: the core owner is the pair-henselization adjunction for
  `henselianPairInclusion`, already supplied by Lemma `15.12.1`;
- primitive data: a map of pairs `(A, I) → (B, J)` and the chosen henselization rings attached to
  that adjunction;
- derived API: the induced map on henselization rings, the tensor-product comparison map, and the
  bijectivity/algebra-equivalence statements.

Source/core/bridge triage:
- `source-facing`: the canonical comparison map `A^h ⊗[A] B → B^h` and its bijectivity under the
  hypotheses of Lemma 15.12.7;
- `core/canonical`: `henselianPairInclusion` together with its chosen left adjoint from
  `henselianPairInclusion_isRightAdjoint`;
- `bridge/view`: the tensor-product comparison map derived from the source pair morphism and the
  adjunction unit naturality. -/

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- The henselization ring of `(B, J)` inherits its `A`-algebra structure by composition with the
map `A → B`. -/
instance pairOfIdeal_henselizationRing_comp_algebra :
    Algebra A (henselizationRing (pairOfIdeal J)) :=
  (RingHom.comp (toHenselization (pairOfIdeal J)) (algebraMap A B)).toAlgebra

/-- The composed `A`- and `B`-algebra structures on the henselization ring of `(B, J)` form a
scalar tower. -/
instance pairOfIdeal_henselizationRing_isScalarTower :
    IsScalarTower A B (henselizationRing (pairOfIdeal J)) := by
  -- The `A`-algebra structure was defined as the composite `A → B → B^h`.
  refine IsScalarTower.of_algebraMap_eq' ?_
  rfl

-- Proof sketch: apply naturality of the adjunction unit for pair henselization to the morphism
-- `(A, I) → (B, J)`; on underlying rings this says the induced henselization map commutes with
-- the original `A`-algebra maps.
/-- The induced map on henselization rings is compatible with the `A`-algebra structures coming
from the original map `A → B`. -/
lemma henselizationRingMap_commutes (hIJ : I ≤ Ideal.comap (algebraMap A B) J) (a : A) :
    henselizationRingMap (pairOfIdealMap I J hIJ)
        (algebraMap A (henselizationRing (pairOfIdeal I)) a) =
      algebraMap A (henselizationRing (pairOfIdeal J)) a := by
  -- Naturality of `toHenselization` identifies the two composites `A → B → B^h`.
  have hNat := toHenselization_naturality (pairOfIdealMap I J hIJ)
  simpa [RingHom.comp_apply, pairOfIdeal_henselizationRing_comp_algebra] using
    (congrArg (fun φ : A →+* henselizationRing (pairOfIdeal J) ↦ φ a) hNat).symm

/-- The comparison map `A^h ⊗[A] B → B^h` induced by the map of pairs `(A, I) → (B, J)`. -/
abbrev henselizationBaseChangeComparison (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    (henselizationRing (pairOfIdeal I) ⊗[A] B) →ₐ[A] henselizationRing (pairOfIdeal J) :=
  Algebra.TensorProduct.productMap
    { toRingHom := henselizationRingMap (pairOfIdealMap I J hIJ)
      commutes' := henselizationRingMap_commutes I J hIJ }
    ((Algebra.ofId B (henselizationRing (pairOfIdeal J))).restrictScalars A)

/-- Helper for Lemma 15.12.7: on the tensor product `A^h ⊗[A] B`, the extension of the
henselization ideal `I^h` along the left factor agrees with the extension of `IB` along the
right factor. -/
lemma tensor_base_change_targetIdeal_eq_mappedIdeal :
    Ideal.map
        (algebraMap (henselizationRing (pairOfIdeal I))
          (henselizationRing (pairOfIdeal I) ⊗[A] B))
        (henselizationIdeal (pairOfIdeal I)) =
      Ideal.map
        (algebraMap B (henselizationRing (pairOfIdeal I) ⊗[A] B))
        (Ideal.map (algebraMap A B) I) := by
  -- Proof comment: rewrite `I^h` as the image of `I`, then identify the two composites
  -- `A → A^h → A^h ⊗[A] B` and `A → B → A^h ⊗[A] B` through tensor-product functoriality.
  rw [henselizationIdeal_eq_map (pairOfIdeal I), Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  exact congrArg
    (fun φ : A →+* (henselizationRing (pairOfIdeal I) ⊗[A] B) ↦ φ a)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
      (Algebra.TensorProduct.includeLeft : henselizationRing (pairOfIdeal I) →ₐ[A]
          henselizationRing (pairOfIdeal I) ⊗[A] B).toRingHom.comp
        (algebraMap A (henselizationRing (pairOfIdeal I))) =
      ((Algebra.TensorProduct.includeRight : B →ₐ[A]
          henselizationRing (pairOfIdeal I) ⊗[A] B).toRingHom.comp
        (algebraMap A B)))

/-- Helper for Lemma 15.12.7: in the mapped-ideal case, the comparison map is the identity on the
right tensor factor `B`. -/
lemma henselizationBaseChangeComparison_includeRight
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (b : B) :
    henselizationBaseChangeComparison I J hIJ
        (algebraMap B (henselizationRing (pairOfIdeal I) ⊗[A] B) b) =
      algebraMap B (henselizationRing (pairOfIdeal J)) b := by
  -- Proof comment: expand the comparison on the pure tensor `1 ⊗ b`; the second
  -- component of `productMap` is the canonical `B`-algebra map into `B^h`.
  change
    henselizationBaseChangeComparison I J hIJ
        ((1 : henselizationRing (pairOfIdeal I)) ⊗ₜ[A] b) =
      algebraMap B (henselizationRing (pairOfIdeal J)) b
  rw [henselizationBaseChangeComparison, Algebra.TensorProduct.productMap_apply_tmul]
  simp

/-- Helper for Lemma 15.12.7: in the mapped-ideal case, the comparison map is the identity on the
right tensor factor `B`. -/
lemma henselizationBaseChangeComparison_mappedIdeal_includeRight (b : B) :
    henselizationBaseChangeComparison I (Ideal.map (algebraMap A B) I) Ideal.le_comap_map
        (algebraMap B (henselizationRing (pairOfIdeal I) ⊗[A] B) b) =
      algebraMap B (henselizationRing (pairOfIdeal (Ideal.map (algebraMap A B) I))) b := by
  -- Proof comment: this is the general right-factor computation specialized to `J = I B`.
  exact henselizationBaseChangeComparison_includeRight
    (I := I) (J := Ideal.map (algebraMap A B) I) Ideal.le_comap_map b

/-- Helper for Lemma 15.12.7: in the mapped-ideal case, the comparison map restricts on the
right tensor factor to the canonical henselization map `B → (IB)^h`. -/
lemma henselizationBaseChangeComparison_mappedIdeal_comp_algebraMap :
    (henselizationBaseChangeComparison
        I (Ideal.map (algebraMap A B) I) Ideal.le_comap_map).toRingHom.comp
      (algebraMap B (henselizationRing (pairOfIdeal I) ⊗[A] B)) =
    algebraMap B (henselizationRing (pairOfIdeal (Ideal.map (algebraMap A B) I))) := by
  -- Proof comment: extensionality on `B` reduces this to the pure-tensor computation above.
  ext b
  exact henselizationBaseChangeComparison_mappedIdeal_includeRight (I := I) (A := A) (B := B) b

/-- Helper for Lemma 15.12.7: on the left tensor factor, the comparison map is the induced map on
henselization rings. -/
lemma henselizationBaseChangeComparison_includeLeft
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (x : henselizationRing (pairOfIdeal I)) :
    henselizationBaseChangeComparison I J hIJ
        (algebraMap (henselizationRing (pairOfIdeal I))
          (henselizationRing (pairOfIdeal I) ⊗[A] B) x) =
      henselizationRingMap (pairOfIdealMap I J hIJ) x := by
  -- Proof comment: expand the comparison on the pure tensor `x ⊗ 1`; the left component of
  -- `productMap` is the induced map on henselization rings.
  change henselizationBaseChangeComparison I J hIJ
      (x ⊗ₜ[A] (1 : B)) = henselizationRingMap (pairOfIdealMap I J hIJ) x
  rw [henselizationBaseChangeComparison, Algebra.TensorProduct.productMap_apply_tmul]
  simp

/-- Helper for Lemma 15.12.7: in the mapped-ideal case, the comparison map restricts on the
left tensor factor to the induced map `A^h → (IB)^h`. -/
lemma henselizationBaseChangeComparison_mappedIdeal_comp_includeLeft :
    (henselizationBaseChangeComparison
        I (Ideal.map (algebraMap A B) I) Ideal.le_comap_map).toRingHom.comp
      (algebraMap (henselizationRing (pairOfIdeal I))
        (henselizationRing (pairOfIdeal I) ⊗[A] B)) =
    henselizationRingMap
      (pairOfIdealMap I (Ideal.map (algebraMap A B) I) Ideal.le_comap_map) := by
  -- Proof comment: extensionality on `A^h` reduces this to the pure-tensor computation above.
  ext x
  exact henselizationBaseChangeComparison_includeLeft
    (I := I) (J := Ideal.map (algebraMap A B) I) Ideal.le_comap_map x

/-- Helper for Lemma 15.12.7: a ring hom carrying the distinguished ideal of a ring pair into a
target ideal induces the corresponding morphism of ring pairs. -/
lemma ringPair_toIdealPair_hom_square {X : RingPairCat.{u}}
    {C : Type u} [CommRing C] [Algebra X.ring C] (K : Ideal C)
    (hXK : X.ideal ≤ Ideal.comap (algebraMap X.ring C) K) :
    CommRingCat.ofHom (algebraMap X.ring C) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk K) =
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal) ≫
        CommRingCat.ofHom (Ideal.quotientMap K (algebraMap X.ring C) hXK) := by
  -- Proof comment: `Ideal.quotientMap` is defined so that both composites are the same quotient
  -- map on representatives.
  ext x
  rfl

/-- Helper for Lemma 15.12.7: package a ring hom together with ideal containment as a morphism of
ring pairs into `(C, K)`. -/
abbrev ringPairToIdealPairMap {X : RingPairCat.{u}}
    {C : Type u} [CommRing C] [Algebra X.ring C] (K : Ideal C)
    (hXK : X.ideal ≤ Ideal.comap (algebraMap X.ring C) K) :
    X ⟶ pairOfIdeal K :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom (algebraMap X.ring C))
      (CommRingCat.ofHom (Ideal.quotientMap K (algebraMap X.ring C) hXK))
      (ringPair_toIdealPair_hom_square (K := K) hXK)

/-- Helper for Lemma 15.12.7: maps from the chosen henselization ring into a henselian target pair
are uniquely determined by their restriction to the original ring. -/
lemma existsUnique_henselizationRingHom_of_henselian_target
    (K : Ideal B) (hK : HenselianRing B K)
    (hIK : I ≤ Ideal.comap (algebraMap A B) K) :
    ∃! g : henselizationRing (pairOfIdeal I) →+* B,
      g.comp (toHenselization (pairOfIdeal I)) = algebraMap A B := by
  -- Proof comment: this is the same universal property used in the source proof.
  -- We transpose the pair map `(A, I) → (B, K)` across the henselization adjunction and then read
  -- the resulting uniqueness statement on underlying ring homomorphisms.
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
  · -- Proof comment: the adjunction unit identity says the transpose extends `A → B`.
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

/-- Helper for Lemma 15.12.7: extending ideals along a `B`-algebra map preserves equality of
their zero loci in prime spectra. -/
private theorem zeroLocus_map_eq_of_zeroLocus_eq_same_ring
    {R : Type u} [CommRing R] (K L : Ideal R)
    (hV : V((K : Set R)) = V((L : Set R)))
    {C : Type u} [CommRing C] [Algebra R C] :
    V((Ideal.map (algebraMap R C) K : Set C)) =
      V((Ideal.map (algebraMap R C) L : Set C)) := by
  -- Proof comment: compare membership pointwise after contracting prime ideals along `B → C`.
  ext q
  constructor
  · intro hq
    have hKq : K ≤ Ideal.comap (algebraMap R C) q.asIdeal := by
      exact Ideal.map_le_iff_le_comap.mp <|
        (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap R C) K : Set C)).mp hq
    have hqK :
        PrimeSpectrum.comap (algebraMap R C) q ∈ V((K : Set R)) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap R C) q)
        (K : Set R)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hKq
    have hqL :
        PrimeSpectrum.comap (algebraMap R C) q ∈ V((L : Set R)) := by
      simpa [hV] using hqK
    exact (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap R C) L : Set C)).mpr <|
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap R C) q)
            (L : Set R)).mp hqL
  · intro hq
    have hLq : L ≤ Ideal.comap (algebraMap R C) q.asIdeal := by
      exact Ideal.map_le_iff_le_comap.mp <|
        (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap R C) L : Set C)).mp hq
    have hqL :
        PrimeSpectrum.comap (algebraMap R C) q ∈ V((L : Set R)) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap R C) q)
        (L : Set R)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hLq
    have hqK :
        PrimeSpectrum.comap (algebraMap R C) q ∈ V((K : Set R)) := by
      simpa [hV] using hqL
    exact (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap R C) K : Set C)).mpr <|
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap R C) q)
            (K : Set R)).mp hqK

/-- Helper for Lemma 15.12.7: a surjective ring hom with nilpotent kernel elements induces a
bijection on idempotents. -/
private theorem bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] (f : R →+* S)
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

/-- Helper for Lemma 15.12.7: the quotient map from `C ⧸ K` to `C ⧸ √K` is surjective. -/
private theorem radicalQuotientFactor_surjective {C : Type u} [CommRing C] (K : Ideal C) :
    Function.Surjective (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  -- Proof comment: every class modulo `√K` is represented by the same element modulo `K`.
  exact ⟨Ideal.Quotient.mk K y, rfl⟩

/-- Helper for Lemma 15.12.7: every element in the kernel of `C ⧸ K → C ⧸ √K` is nilpotent. -/
private theorem radicalQuotientFactor_ker_nilpotent_elements
    {C : Type u} [CommRing C] (K : Ideal C) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)),
      IsNilpotent x := by
  intro x hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [RingHom.mem_ker] at hx
  change Ideal.Quotient.mk K.radical y = 0 at hx
  have hy : y ∈ K.radical := Ideal.Quotient.eq_zero_iff_mem.mp hx
  rcases Ideal.mem_radical_iff.mp hy with ⟨n, hn⟩
  -- Proof comment: membership in the radical means a power lands back in `K`, so the class is
  -- nilpotent in `C ⧸ K`.
  refine ⟨n, ?_⟩
  change Ideal.Quotient.mk K (y ^ n) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

/-- Helper for Lemma 15.12.7: the factor map `C ⧸ K → C ⧸ √K` induces a bijection on
idempotents. -/
private theorem radicalQuotientFactor_bijective_idempotentMap
    {C : Type u} [CommRing C] (K : Ideal C) :
    Function.Bijective
      (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)).idempotentMap := by
  -- Proof comment: apply the nilpotent-kernel idempotent-lifting theorem to the radical factor.
  exact bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    (Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical))
    (radicalQuotientFactor_surjective K)
    (radicalQuotientFactor_ker_nilpotent_elements K)

/-- Helper for Lemma 15.12.7: composing with a bijection preserves bijectivity. -/
private theorem bijective_iff_bijective_comp
    {α β γ : Type u} (f : α → β) (g : β → γ) (hg : Function.Bijective g) :
    Function.Bijective f ↔ Function.Bijective (g ∘ f) := by
  constructor
  · intro hf
    exact hg.comp hf
  · intro hgf
    constructor
    · intro x y hxy
      exact hgf.1 (by simp [Function.comp, hxy])
    · intro z
      obtain ⟨x, hx⟩ := hgf.2 (g z)
      exact ⟨x, hg.1 <| by simpa [Function.comp] using hx⟩

/-- Helper for Lemma 15.12.7: bijectivity of the quotient idempotent map depends only on the
radical of the ideal. -/
private theorem bijective_idempotentMap_iff_of_radical_eq
    {C : Type u} [CommRing C] (K L : Ideal C) (hKL : K.radical = L.radical) :
    Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
      Function.Bijective (Ideal.Quotient.mk L).idempotentMap := by
  have hK :
      Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
        Function.Bijective (Ideal.Quotient.mk K.radical).idempotentMap := by
    let φ : C ⧸ K →+* C ⧸ K.radical :=
      Ideal.Quotient.factor (Ideal.le_radical : K ≤ K.radical)
    have hφ : Function.Bijective φ.idempotentMap :=
      radicalQuotientFactor_bijective_idempotentMap K
    have hcomp :
        φ.idempotentMap ∘ (Ideal.Quotient.mk K).idempotentMap =
          (Ideal.Quotient.mk K.radical).idempotentMap := by
      funext e
      rfl
    -- Proof comment: passing from `C ⧸ K` to `C ⧸ √K` does not change idempotents.
    simpa [φ, hcomp] using
      (bijective_iff_bijective_comp
        (Ideal.Quotient.mk K).idempotentMap φ.idempotentMap hφ)
  have hL :
      Function.Bijective (Ideal.Quotient.mk L).idempotentMap ↔
        Function.Bijective (Ideal.Quotient.mk L.radical).idempotentMap := by
    let φ : C ⧸ L →+* C ⧸ L.radical :=
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

/-- Helper for Lemma 15.12.7: the integral idempotent-lifting criterion depends only on the
closed subset cut out inside `Spec B`. -/
private theorem hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq_same_ring
    {R : Type u} [CommRing R] (K L : Ideal R)
    (hV : V((K : Set R)) = V((L : Set R))) :
    Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := R) K ↔
      Ideal.HasIntegralAlgebraIdempotentLifting.{u, u} (A := R) L := by
  constructor
  · intro h C _ _ _
    let K' : Ideal C := Ideal.map (algebraMap R C) K
    let L' : Ideal C := Ideal.map (algebraMap R C) L
    have hKL : K'.radical = L'.radical := by
      exact PrimeSpectrum.zeroLocus_eq_iff.mp <|
        zeroLocus_map_eq_of_zeroLocus_eq_same_ring K L hV
    have hK : Function.Bijective (Ideal.Quotient.mk K').idempotentMap := by
      simpa [K'] using (h (B := C))
    exact (bijective_idempotentMap_iff_of_radical_eq K' L' hKL).mp hK
  · intro h C _ _ _
    let K' : Ideal C := Ideal.map (algebraMap R C) K
    let L' : Ideal C := Ideal.map (algebraMap R C) L
    have hKL : K'.radical = L'.radical := by
      exact PrimeSpectrum.zeroLocus_eq_iff.mp <|
        zeroLocus_map_eq_of_zeroLocus_eq_same_ring K L hV
    have hL : Function.Bijective (Ideal.Quotient.mk L').idempotentMap := by
      simpa [L'] using (h (B := C))
    exact (bijective_idempotentMap_iff_of_radical_eq K' L' hKL).mpr hL

/-- Helper for Lemma 15.12.7: after extending along any `B`-algebra, henselianity depends only on
the common zero locus inside `Spec B`. -/
private theorem henselianRing_map_iff_of_zeroLocus_eq_same_ring (K L : Ideal B)
    (hV : V((K : Set B)) = V((L : Set B)))
    {C : Type u} [CommRing C] [Algebra B C] :
    HenselianRing C (Ideal.map (algebraMap B C) K) ↔
      HenselianRing C (Ideal.map (algebraMap B C) L) := by
  -- Proof comment: convert henselianity to the Chapter 15 integral idempotent-lifting criterion,
  -- move across the common zero locus, and convert back.
  let Q : Ideal C → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal C → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (M : Ideal C) : List Prop :=
    [HenselianRing C M, M.HasEtaleLiftProperty, Q M, P M, M.SatisfiesGabberRootCriterion]
  have hTfaeK : List.TFAE (T (Ideal.map (algebraMap B C) K)) := by
    simpa [T, Q, P] using
      henselianRing_tfae_etaleLift_idempotents_gabberCriterion (Ideal.map (algebraMap B C) K)
  have hK :
      HenselianRing C (Ideal.map (algebraMap B C) K) ↔
        P (Ideal.map (algebraMap B C) K) := by
    simpa [T] using hTfaeK.out 0 3
  have hKL :
      P (Ideal.map (algebraMap B C) K) ↔
        P (Ideal.map (algebraMap B C) L) := by
    exact hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq_same_ring
      (R := C)
      (Ideal.map (algebraMap B C) K)
      (Ideal.map (algebraMap B C) L)
      (zeroLocus_map_eq_of_zeroLocus_eq_same_ring K L hV)
  have hTfaeL : List.TFAE (T (Ideal.map (algebraMap B C) L)) := by
    simpa [T, Q, P] using
      henselianRing_tfae_etaleLift_idempotents_gabberCriterion (Ideal.map (algebraMap B C) L)
  have hL :
      HenselianRing C (Ideal.map (algebraMap B C) L) ↔
        P (Ideal.map (algebraMap B C) L) := by
    simpa [T] using hTfaeL.out 0 3
  exact (hK.trans hKL).trans hL.symm

/-- Helper for Lemma 15.12.7: integral base change of a henselian pair is henselian when both
rings live in the same universe. -/
private theorem ideal_map_henselianRing_of_isIntegral_local
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (K : Ideal R) [HenselianRing R K] [Algebra.IsIntegral R S] :
    HenselianRing S (Ideal.map (algebraMap R S) K) := by
  -- Proof comment: transport the integral idempotent-lifting criterion along the integral base
  -- change `R → S`, then recover henselianity from the Chapter 15 TFAE.
  let J : Ideal S := Ideal.map (algebraMap R S) K
  let Qsrc : Ideal R → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let Psrc : Ideal R → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let Qtgt : Ideal S → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let Ptgt : Ideal S → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  have hTfaeSource :
      List.TFAE [HenselianRing R K, K.HasEtaleLiftProperty, Qsrc K, Psrc K,
        K.SatisfiesGabberRootCriterion] := by
    simpa [Qsrc, Psrc] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion K
  have hSourceIff : HenselianRing R K ↔ Psrc K := by
    simpa using hTfaeSource.out 0 3
  have hSource : Psrc K :=
    hSourceIff.mp inferInstance
  have hTarget : Ptgt J := by
    intro C _ _ hC
    let _ : Algebra R C := ((algebraMap S C).comp (algebraMap R S)).toAlgebra
    let _ : IsScalarTower R S C := IsScalarTower.of_algebraMap_eq' rfl
    let _ : Algebra.IsIntegral R C := Algebra.IsIntegral.trans S
    let JS : Ideal C := Ideal.map (algebraMap S C) J
    let JR : Ideal C := Ideal.map (algebraMap R C) K
    have hMap : JS = JR := by
      simp [JS, JR, J, Ideal.map_map, IsScalarTower.algebraMap_eq R S C]
    let e : (C ⧸ JS) ≃+* (C ⧸ JR) := Ideal.quotEquivOfEq hMap
    have heBij : Function.Bijective (RingHom.idempotentMap e.toRingHom) := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        exact e.injective (congrArg Subtype.val hxy)
      · intro y
        refine ⟨RingHom.idempotentMap e.symm.toRingHom y, ?_⟩
        apply Subtype.ext
        simp [RingHom.idempotentMap]
    have hComm :
        RingHom.idempotentMap e.toRingHom ∘ (Ideal.Quotient.mk JS).idempotentMap =
          (Ideal.Quotient.mk JR).idempotentMap := by
      funext x
      apply Subtype.ext
      change e ((Ideal.Quotient.mk JS) x.1) = (Ideal.Quotient.mk JR) x.1
      rw [Ideal.quotEquivOfEq_mk]
    have hSourceC : Function.Bijective (Ideal.Quotient.mk JR).idempotentMap := by
      simpa [JR] using hSource (B := C)
    have hComp :
        Function.Bijective
          (RingHom.idempotentMap e.toRingHom ∘ (Ideal.Quotient.mk JS).idempotentMap) := by
      rw [hComm]
      exact hSourceC
    have hJS : Function.Bijective (Ideal.Quotient.mk JS).idempotentMap := by
      constructor
      · intro x y hxy
        apply hComp.1
        simp [Function.comp, hxy]
      · intro z
        obtain ⟨w, hw⟩ := hComp.2 (RingHom.idempotentMap e.toRingHom z)
        refine ⟨w, ?_⟩
        exact heBij.1 <| by simpa [Function.comp] using hw
    simpa [JS] using hJS
  have hTfaeTarget :
      List.TFAE [HenselianRing S J, J.HasEtaleLiftProperty, Qtgt J, Ptgt J,
        J.SatisfiesGabberRootCriterion] := by
    simpa [Qtgt, Ptgt] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion J
  have hTargetIff : HenselianRing S J ↔ Ptgt J := by
    simpa using hTfaeTarget.out 0 3
  exact hTargetIff.mpr hTarget

/-- Helper for Lemma 15.12.7: the mapped-ideal tensor target
`(A^h ⊗[A] B, I^h(A^h ⊗[A] B))` is henselian under the integral hypothesis. -/
lemma tensor_base_change_henselian_pair [Algebra.IsIntegral A B] :
    HenselianRing
      (henselizationRing (pairOfIdeal I) ⊗[A] B)
      (Ideal.map
        (algebraMap (henselizationRing (pairOfIdeal I))
          (henselizationRing (pairOfIdeal I) ⊗[A] B))
        (henselizationIdeal (pairOfIdeal I))) := by
  -- Proof comment: apply Lemma `15.11.8` to the henselization pair `(A^h, I^h)`.
  -- The only extra input is that `A^h → A^h ⊗[A] B` is integral, which follows from stability of
  -- integrality under base change.
  let R := henselizationRing (pairOfIdeal I)
  let T := R ⊗[A] B
  let K := henselizationIdeal (pairOfIdeal I)
  have hRingHomInt : (algebraMap R T).IsIntegral := by
    have hAB : (algebraMap A B).IsIntegral := algebraMap_isIntegral_iff.mpr inferInstance
    exact RingHom.isIntegral_isStableUnderBaseChange A B R T hAB
  let _ : Algebra.IsIntegral R T := algebraMap_isIntegral_iff.mp hRingHomInt
  have hPair :
      HenselianRing R K := by
    change HenselianRing (henselizationPair (pairOfIdeal I)).ring
      (henselizationPair (pairOfIdeal I)).ideal
    exact (henselization (pairOfIdeal I)).property
  -- The imported integral-base-change theorem gives henselianity for the mapped ideal.
  simpa [R, T, K] using
    (ideal_map_henselianRing_of_isIntegral_local
      (R := R) (S := T) (K := K))

/-- Helper for Lemma 15.12.7: when `J = IB`, the canonical base-change comparison map is
bijective. -/
lemma henselizationBaseChangeComparison_bijective_mappedIdeal
    [Algebra.IsIntegral A B] :
    Function.Bijective
      (henselizationBaseChangeComparison
        I (Ideal.map (algebraMap A B) I) Ideal.le_comap_map) := by
  let K : Ideal B := Ideal.map (algebraMap A B) I
  let T : Type u := henselizationRing (pairOfIdeal I) ⊗[A] B
  let f :=
    henselizationBaseChangeComparison I K Ideal.le_comap_map
  have hT :
      HenselianRing T (Ideal.map (algebraMap B T) K) := by
    -- Proof comment: the tensor target is henselian for the left-factor ideal, and that ideal is
    -- exactly the image of `IB` on the right tensor factor.
    simpa [K, T, tensor_base_change_targetIdeal_eq_mappedIdeal (I := I) (A := A) (B := B)] using
      (tensor_base_change_henselian_pair (A := A) (B := B) (I := I))
  obtain ⟨g, hg_comp, hg_unique⟩ :=
    existsUnique_henselizationRingHom_of_henselian_target
      (A := B) (I := K) (B := T) (K := Ideal.map (algebraMap B T) K) hT
      Ideal.le_comap_map
  have hg_left :
      g.comp (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map)) =
        algebraMap (henselizationRing (pairOfIdeal I)) T := by
    have hIK :
        I ≤ Ideal.comap (algebraMap A T) (Ideal.map (algebraMap B T) K) := by
      intro x hx
      change algebraMap A T x ∈ Ideal.map (algebraMap B T) K
      rw [IsScalarTower.algebraMap_eq A B T]
      exact Ideal.mem_map_of_mem (algebraMap B T) <|
        Ideal.mem_map_of_mem (algebraMap A B) hx
    obtain ⟨u, hu_comp, hu_unique⟩ :=
      existsUnique_henselizationRingHom_of_henselian_target
        (A := A) (I := I) (B := T) (K := Ideal.map (algebraMap B T) K) hT hIK
    have hu :
        (g.comp (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map))).comp
            (toHenselization (pairOfIdeal I)) =
          algebraMap A T := by
      calc
        (g.comp (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map))).comp
            (toHenselization (pairOfIdeal I)) =
            g.comp
              ((henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map)).comp
                (toHenselization (pairOfIdeal I))) := by
              rw [RingHom.comp_assoc]
        _ = g.comp ((toHenselization (pairOfIdeal K)).comp (algebraMap A B)) := by
          congr 1
          simpa [RingPairCat.ringHom] using
            (toHenselization_naturality (pairOfIdealMap I K Ideal.le_comap_map)).symm
        _ = (g.comp (toHenselization (pairOfIdeal K))).comp (algebraMap A B) := by
          rw [RingHom.comp_assoc]
        _ = (algebraMap B T).comp (algebraMap A B) := by
          rw [hg_comp]
        _ = algebraMap A T := by
          rw [IsScalarTower.algebraMap_eq A B T]
    have hu_id : u = algebraMap (henselizationRing (pairOfIdeal I)) T := by
      exact (hu_unique _ rfl).symm
    calc
      g.comp (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map)) = u :=
        hu_unique _ hu
      _ = algebraMap (henselizationRing (pairOfIdeal I)) T := hu_id
  have hfg_id : f.toRingHom.comp g = RingHom.id _ := by
    have hPairK :
        HenselianRing (henselizationRing (pairOfIdeal K)) (henselizationIdeal (pairOfIdeal K)) := by
      change HenselianRing (henselizationPair (pairOfIdeal K)).ring
        (henselizationPair (pairOfIdeal K)).ideal
      exact (henselization (pairOfIdeal K)).property
    have hSelf :
        HenselianRing (henselizationRing (pairOfIdeal K))
          (Ideal.map (algebraMap B (henselizationRing (pairOfIdeal K))) K) := by
      -- Proof comment: the chosen henselization pair is henselian, with ideal equal to the image
      -- of `K`.
      simpa [henselizationIdeal_eq_map (X := pairOfIdeal K)] using hPairK
    obtain ⟨u, hu_comp, hu_unique⟩ :=
      existsUnique_henselizationRingHom_of_henselian_target
        (A := B) (I := K)
        (B := henselizationRing (pairOfIdeal K))
        (K := Ideal.map (algebraMap B (henselizationRing (pairOfIdeal K))) K)
        hSelf Ideal.le_comap_map
    have hcomp :
        (f.toRingHom.comp g).comp (toHenselization (pairOfIdeal K)) =
          algebraMap B (henselizationRing (pairOfIdeal K)) := by
      calc
        (f.toRingHom.comp g).comp (toHenselization (pairOfIdeal K)) =
            f.toRingHom.comp (g.comp (toHenselization (pairOfIdeal K))) := by
              rw [RingHom.comp_assoc]
        _ = f.toRingHom.comp (algebraMap B T) := by
          rw [hg_comp]
        _ = algebraMap B (henselizationRing (pairOfIdeal K)) := by
          simpa [f, K, T] using
            henselizationBaseChangeComparison_mappedIdeal_comp_algebraMap
              (A := A) (B := B) (I := I)
    have hid :
        (RingHom.id (henselizationRing (pairOfIdeal K))).comp
            (toHenselization (pairOfIdeal K)) =
          algebraMap B (henselizationRing (pairOfIdeal K)) := by
      rfl
    calc
      f.toRingHom.comp g = u := hu_unique _ hcomp
      _ = RingHom.id _ := (hu_unique _ hid).symm
  have hgf_id : g.comp f.toRingHom = RingHom.id _ := by
    have hright :
        (g.comp f.toRingHom).comp (algebraMap B T) = algebraMap B T := by
      calc
        (g.comp f.toRingHom).comp (algebraMap B T) =
            g.comp (f.toRingHom.comp (algebraMap B T)) := by
              rw [RingHom.comp_assoc]
        _ = g.comp (algebraMap B (henselizationRing (pairOfIdeal K))) := by
          rw [henselizationBaseChangeComparison_mappedIdeal_comp_algebraMap
            (A := A) (B := B) (I := I)]
        _ = algebraMap B T := hg_comp
    have hleft :
        (g.comp f.toRingHom).comp
            (algebraMap (henselizationRing (pairOfIdeal I)) T) =
          algebraMap (henselizationRing (pairOfIdeal I)) T := by
      calc
        (g.comp f.toRingHom).comp
            (algebraMap (henselizationRing (pairOfIdeal I)) T) =
            g.comp
              (f.toRingHom.comp
                (algebraMap (henselizationRing (pairOfIdeal I)) T)) := by
              rw [RingHom.comp_assoc]
        _ = g.comp
            (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map)) := by
          rw [henselizationBaseChangeComparison_mappedIdeal_comp_includeLeft
            (A := A) (B := B) (I := I)]
        _ = algebraMap (henselizationRing (pairOfIdeal I)) T := hg_left
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · ext x
      exact congrArg (fun h : henselizationRing (pairOfIdeal I) →+* T ↦ h x) hleft
    · ext b
      exact congrArg (fun h : B →+* T ↦ h b) hright
  have hleftInv : Function.LeftInverse g f := by
    intro x
    exact congrArg
      (fun h : T →+* T ↦ h x)
      hgf_id
  have hrightInv : Function.RightInverse g f := by
    intro y
    exact congrArg
      (fun h : henselizationRing (pairOfIdeal K) →+*
          henselizationRing (pairOfIdeal K) ↦ h y)
      hfg_id
  exact ⟨hleftInv.injective, hrightInv.surjective⟩

/-- Helper for Lemma 15.12.7: equal zero loci in `Spec B` should induce a canonical `B`-algebra
equivalence between the corresponding chosen henselization rings. -/
lemma henselizationRing_algEquiv_of_zeroLocus_eq_same_ring
    (K L : Ideal B) (hV : V((K : Set B)) = V((L : Set B))) :
    ∃! e : henselizationRing (pairOfIdeal K) ≃ₐ[B] henselizationRing (pairOfIdeal L),
      e.toRingHom.comp (toHenselization (pairOfIdeal K)) =
        toHenselization (pairOfIdeal L) := by
  -- Proof comment: replay Lemma `15.12.6` inside the fixed base ring `B`.
  -- Equal zero loci make the two mapped henselian conditions equivalent after any `B`-algebra
  -- extension, so the same universal-property argument produces inverse comparison maps.
  let toK := toHenselization (pairOfIdeal K)
  let toL := toHenselization (pairOfIdeal L)
  have hPairK :
      HenselianRing (henselizationRing (pairOfIdeal K)) (henselizationIdeal (pairOfIdeal K)) := by
    change HenselianRing (henselizationPair (pairOfIdeal K)).ring
      (henselizationPair (pairOfIdeal K)).ideal
    exact (henselization (pairOfIdeal K)).property
  have hPairL :
      HenselianRing (henselizationRing (pairOfIdeal L)) (henselizationIdeal (pairOfIdeal L)) := by
    change HenselianRing (henselizationPair (pairOfIdeal L)).ring
      (henselizationPair (pairOfIdeal L)).ideal
    exact (henselization (pairOfIdeal L)).property
  have hHensK :
      HenselianRing (henselizationRing (pairOfIdeal K)) (Ideal.map toK K) := by
    -- Proof comment: identify the distinguished ideal of the henselization with the image of `K`.
    simpa [toK, henselizationIdeal_eq_map (X := pairOfIdeal K)] using hPairK
  have hHensL :
      HenselianRing (henselizationRing (pairOfIdeal L)) (Ideal.map toL L) := by
    -- Proof comment: the same identification gives the henselianity of `(B_L^h, L B_L^h)`.
    simpa [toL, henselizationIdeal_eq_map (X := pairOfIdeal L)] using hPairL
  have hHensLK :
      HenselianRing (henselizationRing (pairOfIdeal L)) (Ideal.map toL K) := by
    -- Proof comment: equal zero loci let us replace `L B_L^h` by `K B_L^h`.
    exact (henselianRing_map_iff_of_zeroLocus_eq_same_ring K L hV).mpr hHensL
  have hHensKL :
      HenselianRing (henselizationRing (pairOfIdeal K)) (Ideal.map toK L) := by
    -- Proof comment: symmetrically replace `K B_K^h` by `L B_K^h`.
    exact (henselianRing_map_iff_of_zeroLocus_eq_same_ring K L hV).mp hHensK
  obtain ⟨f, hf_comp, hf_unique⟩ :=
    existsUnique_henselizationRingHom_of_henselian_target
      (A := B) (I := K)
      (B := henselizationRing (pairOfIdeal L))
      (K := Ideal.map toL K)
      hHensLK Ideal.le_comap_map
  obtain ⟨g, hg_comp, hg_unique⟩ :=
    existsUnique_henselizationRingHom_of_henselian_target
      (A := B) (I := L)
      (B := henselizationRing (pairOfIdeal K))
      (K := Ideal.map toK L)
      hHensKL Ideal.le_comap_map
  have hgf_id : g.comp f = RingHom.id _ := by
    obtain ⟨u, hu_comp, hu_unique⟩ :=
      existsUnique_henselizationRingHom_of_henselian_target
        (A := B) (I := K)
        (B := henselizationRing (pairOfIdeal K))
        (K := Ideal.map toK K)
        hHensK Ideal.le_comap_map
    have hcomp :
        (g.comp f).comp toK = algebraMap B (henselizationRing (pairOfIdeal K)) := by
      -- Proof comment: the composite still agrees with the unit map on `B`.
      simpa [toK, toL, RingHom.comp_assoc, hf_comp] using hg_comp
    have hid :
        (RingHom.id (henselizationRing (pairOfIdeal K))).comp toK =
          algebraMap B (henselizationRing (pairOfIdeal K)) := by
      rfl
    calc
      g.comp f = u := hu_unique _ hcomp
      _ = RingHom.id _ := hu_unique _ hid |> Eq.symm
  have hfg_id : f.comp g = RingHom.id _ := by
    obtain ⟨u, hu_comp, hu_unique⟩ :=
      existsUnique_henselizationRingHom_of_henselian_target
        (A := B) (I := L)
        (B := henselizationRing (pairOfIdeal L))
        (K := Ideal.map toL L)
        hHensL Ideal.le_comap_map
    have hcomp :
        (f.comp g).comp toL = algebraMap B (henselizationRing (pairOfIdeal L)) := by
      -- Proof comment: the reverse composite satisfies the same unit equation on `B`.
      simpa [toK, toL, RingHom.comp_assoc, hg_comp] using hf_comp
    have hid :
        (RingHom.id (henselizationRing (pairOfIdeal L))).comp toL =
          algebraMap B (henselizationRing (pairOfIdeal L)) := by
      rfl
    calc
      f.comp g = u := hu_unique _ hcomp
      _ = RingHom.id _ := hu_unique _ hid |> Eq.symm
  have hleft : Function.LeftInverse g f := by
    intro x
    exact congrArg (fun h : henselizationRing (pairOfIdeal K) →+*
        henselizationRing (pairOfIdeal K) ↦ h x) hgf_id
  have hright : Function.RightInverse g f := by
    intro y
    exact congrArg (fun h : henselizationRing (pairOfIdeal L) →+*
        henselizationRing (pairOfIdeal L) ↦ h y) hfg_id
  let fAlg : henselizationRing (pairOfIdeal K) →ₐ[B] henselizationRing (pairOfIdeal L) :=
    { toRingHom := f
      commutes' := by
        intro b
        exact congrArg (fun h : B →+* henselizationRing (pairOfIdeal L) ↦ h b) hf_comp }
  let e : henselizationRing (pairOfIdeal K) ≃ₐ[B] henselizationRing (pairOfIdeal L) :=
    AlgEquiv.ofBijective fAlg ⟨hleft.injective, hright.surjective⟩
  refine ⟨e, ?_, ?_⟩
  · -- Proof comment: the algebra equivalence is built from the unique comparison map `f`.
    simpa [e, fAlg] using hf_comp
  · intro e' he'
    -- Proof comment: uniqueness of the underlying ring hom forces the whole `B`-algebra
    -- equivalence.
    ext x
    have hring : e'.toRingHom = f := by
      exact hf_unique e'.toRingHom <| by simpa [toK, toL] using he'
    simpa [e, fAlg] using congrArg
      (fun h : henselizationRing (pairOfIdeal K) →+*
          henselizationRing (pairOfIdeal L) ↦ h x) hring

-- Proof sketch: use Lemma `15.12.6` to replace `J` by `IB`, then prove the mapped-ideal case by
-- constructing the inverse through the henselian tensor target supplied by Lemma `15.11.8`.
/-- Lemma 15.12.7: for a map of pairs `(A, I) → (B, J)` with `V(J) = V(IB)` and integral ring map
`A → B`, the canonical comparison map `A^h ⊗[A] B → B^h` on chosen pair-henselization rings is
bijective. -/
@[stacks 0DYE]
theorem henselizationBaseChangeComparison_bijective_of_isIntegral
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    Function.Bijective (henselizationBaseChangeComparison I J hIJ) := by
  let K : Ideal B := Ideal.map (algebraMap A B) I
  obtain ⟨e, he_comp, -⟩ :=
    henselizationRing_algEquiv_of_zeroLocus_eq_same_ring
      (B := B) (K := K) (L := J) hV.symm
  let f₀ := henselizationBaseChangeComparison I K Ideal.le_comap_map
  let f :=
    henselizationBaseChangeComparison I J hIJ
  have he_right :
      e.toRingHom.comp (algebraMap B (henselizationRing (pairOfIdeal K))) =
        algebraMap B (henselizationRing (pairOfIdeal J)) := by
    simpa [K] using he_comp
  have he_left :
      e.toRingHom.comp
          (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map)) =
        henselizationRingMap (pairOfIdealMap I J hIJ) := by
    have hPairJ :
        HenselianRing (henselizationRing (pairOfIdeal J)) (henselizationIdeal (pairOfIdeal J)) := by
      change HenselianRing (henselizationPair (pairOfIdeal J)).ring
        (henselizationPair (pairOfIdeal J)).ideal
      exact (henselization (pairOfIdeal J)).property
    have hTarget :
        HenselianRing (henselizationRing (pairOfIdeal J))
          (Ideal.map (algebraMap B (henselizationRing (pairOfIdeal J))) J) := by
      -- Proof comment: the chosen henselization pair of `(B, J)` is henselian, and its ideal is
      -- the image of `J`.
      simpa [henselizationIdeal_eq_map (X := pairOfIdeal J)] using hPairJ
    have hIJ_target :
        I ≤ Ideal.comap
            (algebraMap A (henselizationRing (pairOfIdeal J)))
            (Ideal.map (algebraMap B (henselizationRing (pairOfIdeal J))) J) := by
      intro x hx
      change
        algebraMap B (henselizationRing (pairOfIdeal J)) (algebraMap A B x) ∈
          Ideal.map (algebraMap B (henselizationRing (pairOfIdeal J))) J
      exact Ideal.mem_map_of_mem _ (hIJ hx)
    obtain ⟨u, hu_comp, hu_unique⟩ :=
      existsUnique_henselizationRingHom_of_henselian_target
        (A := A) (I := I)
        (B := henselizationRing (pairOfIdeal J))
        (K := Ideal.map (algebraMap B (henselizationRing (pairOfIdeal J))) J)
        hTarget hIJ_target
    have hu :
        (e.toRingHom.comp
            (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map))).comp
            (toHenselization (pairOfIdeal I)) =
          algebraMap A (henselizationRing (pairOfIdeal J)) := by
      calc
        (e.toRingHom.comp
            (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map))).comp
            (toHenselization (pairOfIdeal I)) =
            e.toRingHom.comp
              ((henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map)).comp
                (toHenselization (pairOfIdeal I))) := by
              rw [RingHom.comp_assoc]
        _ = e.toRingHom.comp
            ((toHenselization (pairOfIdeal K)).comp (algebraMap A B)) := by
          congr 1
          simpa [RingPairCat.ringHom] using
            (toHenselization_naturality (pairOfIdealMap I K Ideal.le_comap_map)).symm
        _ = (e.toRingHom.comp (toHenselization (pairOfIdeal K))).comp (algebraMap A B) := by
          rw [RingHom.comp_assoc]
        _ = (toHenselization (pairOfIdeal J)).comp (algebraMap A B) := by
          rw [he_comp]
        _ = algebraMap A (henselizationRing (pairOfIdeal J)) := by
          rfl
    have hu' :
        (henselizationRingMap (pairOfIdealMap I J hIJ)).comp
            (toHenselization (pairOfIdeal I)) =
          algebraMap A (henselizationRing (pairOfIdeal J)) := by
      simpa [RingPairCat.ringHom, pairOfIdeal_henselizationRing_comp_algebra] using
        (toHenselization_naturality (pairOfIdealMap I J hIJ)).symm
    calc
      e.toRingHom.comp
          (henselizationRingMap (pairOfIdealMap I K Ideal.le_comap_map)) = u := hu_unique _ hu
      _ = henselizationRingMap (pairOfIdealMap I J hIJ) := hu_unique _ hu' |> Eq.symm
  have hcomp :
      (e.toAlgHom.restrictScalars A).comp f₀ = f := by
    apply Algebra.TensorProduct.ext
    · ext x
      change
        e.toRingHom (f₀ (algebraMap (henselizationRing (pairOfIdeal I))
          (henselizationRing (pairOfIdeal I) ⊗[A] B) x)) =
          f (algebraMap (henselizationRing (pairOfIdeal I))
            (henselizationRing (pairOfIdeal I) ⊗[A] B) x)
      rw [henselizationBaseChangeComparison_includeLeft
          (I := I) (J := K) Ideal.le_comap_map,
        henselizationBaseChangeComparison_includeLeft]
      exact congrArg
        (fun h : henselizationRing (pairOfIdeal I) →+*
            henselizationRing (pairOfIdeal J) ↦ h x)
        he_left
    · ext b
      change
        e.toRingHom (f₀ (algebraMap B (henselizationRing (pairOfIdeal I) ⊗[A] B) b)) =
          f (algebraMap B (henselizationRing (pairOfIdeal I) ⊗[A] B) b)
      rw [henselizationBaseChangeComparison_mappedIdeal_includeRight,
        henselizationBaseChangeComparison_includeRight]
      exact congrArg
        (fun h : B →+* henselizationRing (pairOfIdeal J) ↦ h b)
        he_right
  have hf₀ :
      Function.Bijective f₀ :=
    henselizationBaseChangeComparison_bijective_mappedIdeal (A := A) (B := B) (I := I)
  have he : Function.Bijective (e.toAlgHom.restrictScalars A) :=
    e.bijective
  have hf : Function.Bijective f := by
    rw [← hcomp]
    exact he.comp hf₀
  simpa [f] using hf

/-- The canonical algebra equivalence induced by Lemma 15.12.7. -/
noncomputable def henselizationBaseChangeAlgEquiv_of_isIntegral
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    (henselizationRing (pairOfIdeal I) ⊗[A] B) ≃ₐ[A] henselizationRing (pairOfIdeal J) :=
  AlgEquiv.ofBijective (henselizationBaseChangeComparison I J hIJ)
    (henselizationBaseChangeComparison_bijective_of_isIntegral I J hIJ hV)

/-- The algebra equivalence of Lemma 15.12.7 is the canonical comparison map equipped with its
inverse. -/
theorem henselizationBaseChangeAlgEquiv_of_isIntegral_toAlgHom
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    (henselizationBaseChangeAlgEquiv_of_isIntegral I J hIJ hV).toAlgHom =
      henselizationBaseChangeComparison I J hIJ := rfl

end
