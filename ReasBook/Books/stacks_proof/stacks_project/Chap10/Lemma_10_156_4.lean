import Mathlib
import StacksProject_2024.Chap10.Lemma_10_156_2
import StacksProject_2024.Chap10.Lemma_10_155_2

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

section

variable {R Rsh : Type u} [CommRing R] [IsLocalRing R]
variable [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

omit [IsLocalRing R] [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh] in
/-- Helper for Chap10 Lemma 10 156 4: separable closedness of fields transports backwards
through a ring equivalence. -/
private theorem isSepClosed_of_ringEquiv
    {k K : Type u} [Field k] [Field K] [IsSepClosed K] (e : k ≃+* K) :
    IsSepClosed k := by
  -- Proof comment: split after mapping to the separably closed field, then pull the roots back
  -- across the equivalence.
  refine ⟨fun p hp ↦ ?_⟩
  refine Polynomial.Splits.of_splits_map e.toRingHom ?_ ?_
  · exact IsSepClosed.splits_of_separable (p.map e.toRingHom) hp.map
  · intro a _
    exact ⟨e.symm a, by simp⟩

namespace StrictHenselianLocalRing

/-- Helper for Chap10 Lemma 10 156 4: a quotient of a strict henselian local ring by a proper
ideal is again strict henselian. -/
theorem quotient {A : Type u} [CommRing A] [IsLocalRing A] [StrictHenselianLocalRing A]
    (I : Ideal A) (hI : I ≠ ⊤) : StrictHenselianLocalRing (A ⧸ I) := by
  let _ : IsLocalRing (A ⧸ I) := IsLocalRing.quotient I hI
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  let _ : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  let e : ResidueField A ≃+* ResidueField (A ⧸ I) :=
    RingEquiv.ofBijective (ResidueField.map q) (residueField_map_quotient_mk_bijective I hI)
  -- Proof comment: henselianity descends by the quotient theorem, and the residue field is
  -- unchanged up to the quotient residue-field equivalence.
  refine { toHenselianLocalRing := HenselianLocalRing.quotient I hI, toIsSepClosed := ?_ }
  exact isSepClosed_of_ringEquiv e.symm

end StrictHenselianLocalRing

/- Domain-style sampling:
- primary domain: local commutative algebra of strict henselizations and quotients by ideals inside
  the closed point;
- sampled owner declarations: `StrictHenselianLocalRing`, `IsStrictHenselizationOf`,
  `RingHom.IsFilteredColimitOfEtale`, and `IsLocalRing.quotient`;
- best owner abstraction: the quotient theorem should stay source-facing as an
  `IsStrictHenselizationOf` statement, while the local-ring quotient fact is reused from the
  upstream Chapter 10 owner rather than duplicated locally;
- primitive data: the strict henselization owner on `R → Rsh` and the properness hypothesis
  `I ≠ ⊤`;
- derived API: the local-ring structure on `R ⧸ I`.
-/

-- Proof sketch: combine the quotient local-ring lemma from `Lemma 10.156.2` with the strict
-- analogue of the henselization quotient construction. The quotient of a strict henselization
-- remains henselian local with separably closed residue field, and the filtered-colimit-of-étale
-- and maximal-ideal conditions descend through the quotient by `Ideal.map (algebraMap R Rsh) I`.
/-- Chap10 Lemma 10 156 4: if `Rsh` is a strict henselization of the local ring `R` and `I` is a
proper ideal of `R`, then the quotient `Rsh ⧸ Ideal.map (algebraMap R Rsh) I` is a strict
henselization of the quotient ring `R ⧸ I`. -/
@[stacks 05WS]
theorem strictHenselization_quotient_isStrictHenselizationOf_quotient
    (I : Ideal R) (hI : I ≠ ⊤) :
    let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
    IsStrictHenselizationOf (R ⧸ I) (Rsh ⧸ Ideal.map (algebraMap R Rsh) I) := by
  let _ : IsLocalRing (R ⧸ I) := IsLocalRing.quotient I hI
  let J : Ideal Rsh := Ideal.map (algebraMap R Rsh) I
  have hImax : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hJle : J ≤ maximalIdeal Rsh := by
    -- Proof comment: the image of `I` lands in the image of the source maximal ideal, which is
    -- the target maximal ideal for a strict henselization.
    calc
      J = Ideal.map (algebraMap R Rsh) I := rfl
      _ ≤ Ideal.map (algebraMap R Rsh) (maximalIdeal R) := Ideal.map_mono hImax
      _ = maximalIdeal Rsh := IsStrictHenselizationOf.map_maximalIdeal (R := R) (S := Rsh)
  have hJ : J ≠ ⊤ := by
    -- Proof comment: if the image ideal were top, the target maximal ideal would also be top.
    intro htop
    have htop_le : (⊤ : Ideal Rsh) ≤ maximalIdeal Rsh := by
      simpa [htop] using hJle
    have hmax_top : maximalIdeal Rsh = ⊤ := le_antisymm le_top htop_le
    exact (IsLocalRing.maximalIdeal.isMaximal Rsh).ne_top hmax_top
  let _ : IsLocalRing (Rsh ⧸ J) := IsLocalRing.quotient J hJ
  let _ : StrictHenselianLocalRing (Rsh ⧸ J) := StrictHenselianLocalRing.quotient J hJ
  let q : R ⧸ I →+* Rsh ⧸ J :=
    Ideal.quotientMap J (algebraMap R Rsh) Ideal.le_comap_map
  have hqLocal : IsLocalHom q :=
    quotientMap_isLocalHom_of_le_of_ne_top
      (A := R) (B := Rsh) (I := I) (J := J) Ideal.le_comap_map hJ
  let _ : IsLocalHom q := hqLocal
  let _ : IsLocalHom (algebraMap (R ⧸ I) (Rsh ⧸ J)) := by
    simpa [q] using hqLocal
  change IsStrictHenselizationOf (R ⧸ I) (Rsh ⧸ J)
  refine
    { toStrictHenselianLocalRing := ?_
      toIsLocalHom := ?_
      isFilteredColimitOfEtale := ?_
      map_maximalIdeal := ?_ }
  · -- Proof comment: strict henselianity of the target quotient is the helper above.
    infer_instance
  · -- Proof comment: the quotient map is local, and it is the installed quotient algebra map.
    infer_instance
  · -- Proof comment: ind-etaleness descends by base change along `R → R ⧸ I`.
    exact RingHom.IsFilteredColimitOfEtale.quotient I
      (IsStrictHenselizationOf.isFilteredColimitOfEtale (R := R) (S := Rsh))
  · -- Proof comment: normalize both quotient maximal ideals as images, then use the strict
    -- henselization maximal-ideal equality upstairs.
    change Ideal.map q (maximalIdeal (R ⧸ I)) = maximalIdeal (Rsh ⧸ J)
    calc
      Ideal.map q (maximalIdeal (R ⧸ I))
          = Ideal.map q (Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R)) := by
            rw [maximalIdeal_quotient_eq_map (A := R) I hI]
      _ = Ideal.map (q.comp (Ideal.Quotient.mk I)) (maximalIdeal R) := by
            rw [Ideal.map_map]
      _ = Ideal.map ((Ideal.Quotient.mk J).comp (algebraMap R Rsh)) (maximalIdeal R) := by
            congr 1
      _ = Ideal.map (Ideal.Quotient.mk J)
            (Ideal.map (algebraMap R Rsh) (maximalIdeal R)) := by
            rw [Ideal.map_map]
      _ = Ideal.map (Ideal.Quotient.mk J) (maximalIdeal Rsh) := by
            rw [IsStrictHenselizationOf.map_maximalIdeal (R := R) (S := Rsh)]
      _ = maximalIdeal (Rsh ⧸ J) := maximalIdeal_quotient_eq_map (A := Rsh) J hJ

end
