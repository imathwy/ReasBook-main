import Mathlib
import StacksProject_2024.Chap15.Lemma_15_11_6

-- Helper declarations for Lemma 15.12.6.

universe u v

section

open PrimeSpectrum

variable {A : Type u} [CommRing A]

namespace Ideal

/-- Helper for Lemma 15.12.6: extending two ideals along an algebra map preserves equality of
their prime-spectrum zero loci. -/
private theorem zeroLocus_map_eq_of_zeroLocus_eq (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A))
    {B : Type v} [CommRing B] [Algebra A B] :
    zeroLocus (Ideal.map (algebraMap A B) I : Set B) =
      zeroLocus (Ideal.map (algebraMap A B) J : Set B) := by
  -- Proof comment: compare membership pointwise after contracting prime ideals along `A → B`.
  ext q
  constructor
  · intro hq
    have hIq : I ≤ Ideal.comap (algebraMap A B) q.asIdeal := by
      exact Ideal.map_le_iff_le_comap.mp <|
        (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) I : Set B)).mp hq
    have hqI :
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (I : Set A) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
        (I : Set A)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hIq
    have hqJ :
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (J : Set A) := by
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
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (J : Set A) := by
      exact (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
        (J : Set A)).mpr <| by
          simpa [PrimeSpectrum.comap_asIdeal] using hJq
    have hqI :
        PrimeSpectrum.comap (algebraMap A B) q ∈ zeroLocus (I : Set A) := by
      simpa [hV] using hqJ
    exact (PrimeSpectrum.mem_zeroLocus q (Ideal.map (algebraMap A B) I : Set B)).mpr <|
      Ideal.map_le_iff_le_comap.mpr <| by
        simpa [PrimeSpectrum.comap_asIdeal] using
          (PrimeSpectrum.mem_zeroLocus (PrimeSpectrum.comap (algebraMap A B) q)
            (I : Set A)).mp hqI

/-- Helper for Lemma 15.12.6: a surjective ring map with nilpotent kernel elements induces a
bijection on idempotents. -/
private theorem bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] (f : R →+* S)
    (hsurj : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Function.Bijective f.idempotentMap := by
  constructor
  · intro e₁ e₂ h
    apply Subtype.ext
    -- Proof comment: unique lifting across the nilpotent kernel identifies equal target
    -- idempotents with equal source lifts.
    obtain ⟨e, he, huniq⟩ :=
      RingHom.existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker (f e₁.1) (hsurj _) (e₁.2.map f)
    exact (huniq _ ⟨e₁.2, rfl⟩).trans
      (huniq _ ⟨e₂.2, by simpa using (congrArg Subtype.val h).symm⟩).symm
  · intro e
    -- Proof comment: surjectivity supplies a lift, and the same lifting lemma makes it
    -- idempotent.
    obtain ⟨e', he', -⟩ :=
      RingHom.existsUnique_isIdempotentElem_eq_of_ker_isNilpotent
        f hker e.1 (hsurj _) e.2
    refine ⟨⟨e', he'.1⟩, ?_⟩
    exact Subtype.ext he'.2

/-- Helper for Lemma 15.12.6: the quotient map from `B ⧸ K` to `B ⧸ √K` is surjective. -/
private theorem radicalQuotientFactor_surjective {B : Type v} [CommRing B] (K : Ideal B) :
    Function.Surjective (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical) := by
  intro z
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  -- Proof comment: every class modulo `√K` is represented by the same element modulo `K`.
  exact ⟨Ideal.Quotient.mk K y, rfl⟩

/-- Helper for Lemma 15.12.6: every element in the kernel of `B ⧸ K → B ⧸ √K` is nilpotent. -/
private theorem radicalQuotientFactor_ker_nilpotent_elements
    {B : Type v} [CommRing B] (K : Ideal B) :
    ∀ x ∈ RingHom.ker (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical),
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

/-- Helper for Lemma 15.12.6: the factor map `B ⧸ K → B ⧸ √K` induces a bijection on
idempotents. -/
private theorem radicalQuotientFactor_bijective_idempotentMap
    {B : Type v} [CommRing B] (K : Ideal B) :
    Function.Bijective
      (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical).idempotentMap := by
  -- Proof comment: apply the nilpotent-kernel idempotent-lifting theorem to the radical factor.
  exact bijective_idempotentMap_of_surjective_of_nilpotent_kernel_elements
    (Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical)
    (radicalQuotientFactor_surjective K)
    (radicalQuotientFactor_ker_nilpotent_elements K)

/-- Helper for Lemma 15.12.6: composing with a bijection preserves bijectivity. -/
private theorem bijective_iff_bijective_comp
    {α : Type u} {β : Type v} {γ : Type max u v}
    (f : α → β) (g : β → γ) (hg : Function.Bijective g) :
    Function.Bijective f ↔ Function.Bijective (g ∘ f) := by
  constructor
  · intro hf
    exact hg.comp hf
  · intro hgf
    constructor
    · intro x y hxy
      exact hgf.1 hxy
    · intro z
      obtain ⟨y, rfl⟩ := hg.2 z
      obtain ⟨x, rfl⟩ := hgf.2 y
      exact ⟨x, rfl⟩

/-- Helper for Lemma 15.12.6: bijectivity of the quotient idempotent map depends only on the
radical of the ideal. -/
private theorem bijective_idempotentMap_iff_of_radical_eq
    {B : Type v} [CommRing B] (K L : Ideal B) (hKL : K.radical = L.radical) :
    Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
      Function.Bijective (Ideal.Quotient.mk L).idempotentMap := by
  have hK :
      Function.Bijective (Ideal.Quotient.mk K).idempotentMap ↔
        Function.Bijective (Ideal.Quotient.mk K.radical).idempotentMap := by
    let φ : B ⧸ K →+* B ⧸ K.radical :=
      Ideal.Quotient.factor (I := K) (J := K.radical) Ideal.le_radical
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
      Ideal.Quotient.factor (I := L) (J := L.radical) Ideal.le_radical
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
theorem hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq_local (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
    I.HasIntegralAlgebraIdempotentLifting ↔ J.HasIntegralAlgebraIdempotentLifting := by
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
      simpa [K] using h (B := B)
    exact (bijective_idempotentMap_iff_of_radical_eq K L hKL).mp hK
  · intro h B _ _ _
    let K : Ideal B := Ideal.map (algebraMap A B) I
    let L : Ideal B := Ideal.map (algebraMap A B) J
    have hKL : K.radical = L.radical := by
      exact PrimeSpectrum.zeroLocus_eq_iff.mp <|
        zeroLocus_map_eq_of_zeroLocus_eq I J hV
    have hL : Function.Bijective (Ideal.Quotient.mk L).idempotentMap := by
      simpa [L] using h (B := B)
    exact (bijective_idempotentMap_iff_of_radical_eq K L hKL).mpr hL

end Ideal

-- Proof sketch: convert henselianity to the Chapter 15 integral idempotent-lifting criterion by
-- the `0 ↔ 3` branch of the TFAE, use the previous theorem to move across equal zero loci, and
-- convert back.
/-- Helper for Lemma 15.12.6: henselianity of `(A, I)` depends only on the closed subset
`V(I) ⊆ Spec A`. -/
theorem henselianRing_iff_of_zeroLocus_eq_local (I J : Ideal A)
    (hV : zeroLocus (I : Set A) = zeroLocus (J : Set A)) :
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
    Ideal.hasIntegralAlgebraIdempotentLifting_iff_of_zeroLocus_eq_local I J hV
  have hTfaeJ : List.TFAE (T J) := by
    simpa [T, Q, P] using henselianRing_tfae_etaleLift_idempotents_gabberCriterion J
  have hJ : HenselianRing A J ↔ P J := by
    -- Proof comment: the same TFAE branch converts back for `J`.
    simpa [T] using hTfaeJ.out 0 3
  exact (hI.trans hIJ).trans hJ.symm

end
