import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_153_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open IsLocalRing Polynomial
open scoped TensorProduct

section SimpleRootBridge

variable (T : Type w) [CommRing T] [HenselianLocalRing T]

/-- Helper for Chap10 Lemma 10 153 11: henselian local rings lift simple roots from the residue
field, in the exact clause shape exposed by mathlib's `HenselianLocalRing.TFAE`. -/
lemma henselianLocalRing_liftsSimpleRootsFromResidueField :
    ∀ f : T[X], f.Monic → ∀ a0 : ResidueField T,
      aeval a0 f = 0 →
      aeval a0 (f.derivative) ≠ 0 →
      ∃ a : T, f.IsRoot a ∧ residue T a = a0 := by
  -- Proof comment: take the `HenselianLocalRing → simple-root lifting` projection from
  -- mathlib's canonical TFAE; this is the verified prefix of the missing owner bridge.
  exact ((HenselianLocalRing.TFAE T).out 0 1).mp (show HenselianLocalRing T from inferInstance)

end SimpleRootBridge

section

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommRing R] [CommRing A] [CommRing S]
variable [Algebra R A] [Algebra R S] [HenselianLocalRing S]

/-- Helper for Chap10 Lemma 10 153 11: a retraction prime on the base-change tensor product
pulls back along the right tensor factor to the prime of the induced `R`-algebra map. -/
lemma algHomComapOfBaseChangeRetraction
    (q : Ideal A) (Q : Ideal (S ⊗[R] A)) (ρ : S ⊗[R] A →ₐ[S] S)
    (hQright :
      Q.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom = q)
    (hQρ : Q = Ideal.comap (ρ : S ⊗[R] A →+* S) (maximalIdeal S)) :
    q = Ideal.comap (((ρ.restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)) : A →ₐ[R] S).toRingHom
      (maximalIdeal S) := by
  -- Proof comment: pull the retraction's comap identity through the right tensor inclusion.
  rw [← hQright, hQρ]
  simp [Ideal.comap_comap, AlgHom.comp_toRingHom]

/-- Helper for Chap10 Lemma 10 153 11: an `S`-algebra retraction of the base change has
maximal-ideal pullback equal to `maximalIdeal S` along the left tensor inclusion. -/
lemma baseChangeRetraction_comap_includeLeft
    (ρ : S ⊗[R] A →ₐ[S] S)
    (hρleft : ρ.comp (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A) =
      AlgHom.id S S) :
    Ideal.comap (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A).toRingHom
      (Ideal.comap (ρ : S ⊗[R] A →+* S) (maximalIdeal S)) = maximalIdeal S := by
  -- Proof comment: compose the two ideal pullbacks and replace the composite by the identity.
  rw [Ideal.comap_comap]
  simpa [AlgHom.comp_toRingHom] using
    congrArg (fun φ : S →ₐ[S] S => Ideal.comap (φ : S →+* S) (maximalIdeal S)) hρleft

omit [HenselianLocalRing S] in
/-- Helper for Chap10 Lemma 10 153 11: an `S`-algebra map out of the base-change tensor product
is automatically the identity after precomposition with the left tensor factor. -/
lemma baseChangeRetraction_comp_includeLeft
    (ρ : S ⊗[R] A →ₐ[S] S) :
    ρ.comp (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A) =
      AlgHom.id S S := by
  -- Proof comment: the left inclusion is the structure map for the `S`-algebra tensor product,
  -- so `S`-algebra homomorphisms preserve it by definition.
  ext

/-- Helper for Chap10 Lemma 10 153 11: the residue-field point of `A` defined by `τ` respects
the base `R`, so it is an `R`-algebra point. -/
lemma baseChangeResiduePoint_commutes
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)
    (r : R) :
    τ (algebraMap A q.ResidueField (algebraMap R A r)) =
      algebraMap S (maximalIdeal S).ResidueField (algebraMap R S r) := by
  -- Proof comment: evaluate the compatibility hypothesis on the residue class of `r`.
  have happ := congrArg
    (fun f : (q.under R).ResidueField →+* (maximalIdeal S).ResidueField =>
      f (algebraMap R (q.under R).ResidueField r)) hτ
  simpa [Ideal.ResidueField.map_algebraMap, RingHom.comp_apply] using happ

/-- Helper for Chap10 Lemma 10 153 11: the residue-field point of `A` obtained from `τ`. -/
noncomputable def baseChangeResiduePoint
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    A →ₐ[R] (maximalIdeal S).ResidueField where
  toRingHom := τ.comp (algebraMap A q.ResidueField)
  commutes' := baseChangeResiduePoint_commutes (q := q) hq τ hτ

/-- Helper for Chap10 Lemma 10 153 11: the induced `S`-algebra point of the base change
`S ⊗[R] A` with values in the residue field of `S`. -/
noncomputable def baseChangeResiduePointMap
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    S ⊗[R] A →ₐ[S] (maximalIdeal S).ResidueField :=
  Algebra.TensorProduct.lift (Algebra.ofId S (maximalIdeal S).ResidueField)
    (baseChangeResiduePoint (q := q) hq τ hτ) (fun _ _ => Commute.all _ _)

/-- Helper for Chap10 Lemma 10 153 11: the prime of `S ⊗[R] A` cut out by the residue-field
point determined by `τ`. -/
noncomputable abbrev baseChangeResiduePrime
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    Ideal (S ⊗[R] A) :=
  RingHom.ker (baseChangeResiduePointMap (q := q) hq τ hτ).toRingHom

/-- Helper for Chap10 Lemma 10 153 11: the base-change residue point restricts to the residue map
on the left tensor factor. -/
lemma baseChangeResiduePointMap_comp_includeLeft
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    (baseChangeResiduePointMap (q := q) hq τ hτ).comp
      (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A) =
      Algebra.ofId S (maximalIdeal S).ResidueField := by
  -- Proof comment: this is the left computation rule for the tensor-product universal map.
  simp [baseChangeResiduePointMap]

/-- Helper for Chap10 Lemma 10 153 11: the base-change residue point restricts to the selected
residue point of `A` on the right tensor factor. -/
lemma baseChangeResiduePointMap_comp_includeRight
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ((baseChangeResiduePointMap (q := q) hq τ hτ).restrictScalars R).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) =
      baseChangeResiduePoint (q := q) hq τ hτ := by
  -- Proof comment: this is the right computation rule for the tensor-product universal map.
  simp [baseChangeResiduePointMap]

/-- Helper for Chap10 Lemma 10 153 11: the base-change residue point is surjective because the
left residue map `S → κ(maximalIdeal S)` is surjective. -/
lemma baseChangeResiduePointMap_surjective
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    Function.Surjective (baseChangeResiduePointMap (q := q) hq τ hτ) := by
  intro y
  obtain ⟨s, hs⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal S) y
  refine ⟨(Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A) s, ?_⟩
  -- Proof comment: lift a residue-field representative from `S` through the left inclusion.
  have hx :
      (baseChangeResiduePointMap (q := q) hq τ hτ)
        ((Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A) s) =
        algebraMap S (maximalIdeal S).ResidueField s := by
    simpa using congrFun (congrArg DFunLike.coe
      (baseChangeResiduePointMap_comp_includeLeft (q := q) hq τ hτ)) s
  exact hx.trans hs

/-- Helper for Chap10 Lemma 10 153 11: the base-change residue prime contracts to
`maximalIdeal S` along the left tensor factor. -/
lemma baseChangeResiduePrime_comap_includeLeft
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    Ideal.comap (algebraMap S (S ⊗[R] A)) (baseChangeResiduePrime (q := q) hq τ hτ) =
      maximalIdeal S := by
  ext x
  have hx :
      (baseChangeResiduePointMap (q := q) hq τ hτ) (algebraMap S (S ⊗[R] A) x) =
        algebraMap S (maximalIdeal S).ResidueField x := by
    have h := congrFun (congrArg DFunLike.coe
      (baseChangeResiduePointMap_comp_includeLeft (q := q) hq τ hτ)) x
    simpa using h
  -- Proof comment: membership in the kernel is exactly vanishing in the residue field.
  change (baseChangeResiduePointMap (q := q) hq τ hτ) (algebraMap S (S ⊗[R] A) x) = 0 ↔
    x ∈ maximalIdeal S
  rw [hx]
  exact Ideal.algebraMap_residueField_eq_zero

/-- Helper for Chap10 Lemma 10 153 11: the base-change residue prime contracts to `q` along the
right tensor factor. -/
lemma baseChangeResiduePrime_comap_includeRight
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    Ideal.comap (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toRingHom
      (baseChangeResiduePrime (q := q) hq τ hτ) = q := by
  ext x
  have hx :
      (baseChangeResiduePointMap (q := q) hq τ hτ)
        ((Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) x) =
        τ (algebraMap A q.ResidueField x) := by
    simpa [baseChangeResiduePoint] using congrFun (congrArg DFunLike.coe
      (baseChangeResiduePointMap_comp_includeRight (q := q) hq τ hτ)) x
  -- Proof comment: `τ` is injective as a map of fields, so the kernel is exactly `q`.
  change (baseChangeResiduePointMap (q := q) hq τ hτ)
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) x) = 0 ↔ x ∈ q
  rw [hx]
  constructor
  · intro h
    have hz : τ (algebraMap A q.ResidueField x) = τ 0 := by
      simpa using h
    exact Ideal.algebraMap_residueField_eq_zero.mp (τ.injective hz)
  · intro hxq
    simpa [Ideal.algebraMap_residueField_eq_zero.mpr hxq]

/-- Helper for Chap10 Lemma 10 153 11: the residue-field map from `κ(maximalIdeal S)` to the
base-change residue prime is bijective. -/
lemma baseChangeResiduePrime_residueFieldMap_bijective
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    letI : (baseChangeResiduePrime (q := q) hq τ hτ).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective
        (baseChangeResiduePointMap (q := q) hq τ hτ).toRingHom
        (baseChangeResiduePointMap_surjective (q := q) hq τ hτ)).isPrime
    Function.Bijective
      (Ideal.ResidueField.map (maximalIdeal S) (baseChangeResiduePrime (q := q) hq τ hτ)
        (algebraMap S (S ⊗[R] A))
        (by
          simpa [baseChangeResiduePrime] using
            (baseChangeResiduePrime_comap_includeLeft (q := q) hq τ hτ).symm)) := by
  letI : (baseChangeResiduePrime (q := q) hq τ hτ).IsPrime :=
    (RingHom.ker_isMaximal_of_surjective
      (baseChangeResiduePointMap (q := q) hq τ hτ).toRingHom
      (baseChangeResiduePointMap_surjective (q := q) hq τ hτ)).isPrime
  constructor
  · exact RingHom.injective _
  · intro y
    have hQmax : (baseChangeResiduePrime (q := q) hq τ hτ).IsMaximal := by
      dsimp [baseChangeResiduePrime]
      exact RingHom.ker_isMaximal_of_surjective
        (baseChangeResiduePointMap (q := q) hq τ hτ).toRingHom
        (baseChangeResiduePointMap_surjective (q := q) hq τ hτ)
    obtain ⟨x, rfl⟩ :=
      Ideal.algebraMap_residueField_surjective (baseChangeResiduePrime (q := q) hq τ hτ) y
    obtain ⟨s, hs⟩ :=
      Ideal.algebraMap_residueField_surjective (maximalIdeal S)
        ((baseChangeResiduePointMap (q := q) hq τ hτ) x)
    refine ⟨algebraMap S (maximalIdeal S).ResidueField s, ?_⟩
    -- Proof comment: compare representatives after pushing the equality into the kernel prime.
    rw [Ideal.ResidueField.map_algebraMap]
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
    dsimp [baseChangeResiduePrime]
    rw [RingHom.mem_ker, map_sub]
    have hsx :
        (baseChangeResiduePointMap (q := q) hq τ hτ) (s ⊗ₜ[R] (1 : A)) =
          algebraMap S (maximalIdeal S).ResidueField s := by
      have h := congrFun (congrArg DFunLike.coe
        (baseChangeResiduePointMap_comp_includeLeft (q := q) hq τ hτ)) s
      simpa [Algebra.TensorProduct.includeLeft_apply] using h
    simpa [hsx, hs]

/-- Helper for Chap10 Lemma 10 153 11: any retraction cutting out the base-change residue prime
induces the prescribed residue-field map on the right tensor factor. -/
lemma baseChangeRetraction_residue_includeRight
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq)
    (ρ : S ⊗[R] A →ₐ[S] S)
    (hρQ :
      baseChangeResiduePrime (q := q) hq τ hτ =
        Ideal.comap (ρ : S ⊗[R] A →+* S) (maximalIdeal S))
    (x : A) :
    algebraMap S (maximalIdeal S).ResidueField
        (ρ ((Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) x)) =
      τ (algebraMap A q.ResidueField x) := by
  letI : (baseChangeResiduePrime (q := q) hq τ hτ).IsPrime :=
    (RingHom.ker_isMaximal_of_surjective
      (baseChangeResiduePointMap (q := q) hq τ hτ).toRingHom
      (baseChangeResiduePointMap_surjective (q := q) hq τ hτ)).isPrime
  let k : (maximalIdeal S).ResidueField →+* (baseChangeResiduePrime (q := q) hq τ hτ).ResidueField :=
    Ideal.ResidueField.map (maximalIdeal S) (baseChangeResiduePrime (q := q) hq τ hτ)
      (algebraMap S (S ⊗[R] A))
      (by
        simpa [baseChangeResiduePrime] using
          (baseChangeResiduePrime_comap_includeLeft (q := q) hq τ hτ).symm)
  have hk_inj : Function.Injective k :=
    (baseChangeResiduePrime_residueFieldMap_bijective (q := q) hq τ hτ).1
  apply hk_inj
  let y : S ⊗[R] A := (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) x
  have hleft_image :
      k (algebraMap S (maximalIdeal S).ResidueField (ρ y)) =
        algebraMap (S ⊗[R] A) (baseChangeResiduePrime (q := q) hq τ hτ).ResidueField y := by
    rw [Ideal.ResidueField.map_algebraMap]
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
    -- Proof comment: the retraction identifies `y` with its left tensor representative modulo
    -- the prime it cuts out.
    rw [hρQ, Ideal.mem_comap, map_sub]
    have hleft :
        ρ ((Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A) (ρ y)) = ρ y := by
      simpa using congrFun (congrArg DFunLike.coe (baseChangeRetraction_comp_includeLeft ρ))
        (ρ y)
    have hleft_tmul : ρ ((ρ y) ⊗ₜ[R] (1 : A)) = ρ y := by
      simpa [Algebra.TensorProduct.includeLeft_apply] using hleft
    have hleft_tmul_x :
        ρ ((ρ ((Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) x)) ⊗ₜ[R] (1 : A)) =
          ρ ((Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) x) := by
      simpa [y] using hleft_tmul
    simpa [hleft_tmul] using (show (0 : S) ∈ maximalIdeal S from zero_mem _)
  have hright_image :
      k (τ (algebraMap A q.ResidueField x)) =
        algebraMap (S ⊗[R] A) (baseChangeResiduePrime (q := q) hq τ hτ).ResidueField y := by
    obtain ⟨s, hs⟩ :=
      Ideal.algebraMap_residueField_surjective (maximalIdeal S)
        (τ (algebraMap A q.ResidueField x))
    rw [← hs, Ideal.ResidueField.map_algebraMap]
    rw [← sub_eq_zero, ← map_sub, Ideal.algebraMap_residueField_eq_zero]
    dsimp [baseChangeResiduePrime]
    rw [RingHom.mem_ker, map_sub]
    have hsx :
        (baseChangeResiduePointMap (q := q) hq τ hτ) (s ⊗ₜ[R] (1 : A)) =
          algebraMap S (maximalIdeal S).ResidueField s := by
      have h := congrFun (congrArg DFunLike.coe
        (baseChangeResiduePointMap_comp_includeLeft (q := q) hq τ hτ)) s
      simpa [Algebra.TensorProduct.includeLeft_apply] using h
    have hy :
        (baseChangeResiduePointMap (q := q) hq τ hτ) y =
          τ (algebraMap A q.ResidueField x) := by
      simpa [y, baseChangeResiduePoint] using congrFun (congrArg DFunLike.coe
        (baseChangeResiduePointMap_comp_includeRight (q := q) hq τ hτ)) x
    simpa [hsx, hy, hs]
  exact hleft_image.trans hright_image.symm

variable [Algebra.Etale R A]

omit [HenselianLocalRing S] in
/-- Helper for Chap10 Lemma 10 153 11: base-changing the étale algebra `A` from `R` to `S`
makes the tensor product `S ⊗[R] A` an étale `S`-algebra. -/
lemma tensorProduct_baseChange_etale :
    Algebra.Etale S (S ⊗[R] A) := by
  -- Proof comment: this is exactly the canonical base-change instance for étale algebras.
  infer_instance

/-- Helper for Chap10 Lemma 10 153 11: a henselian local ring satisfies the generic unique
retraction criterion for étale neighborhoods with unchanged residue field. -/
lemma etaleRetractionUniqueProperty_of_henselianLocal
    (T : Type w) [CommRing T] [HenselianLocalRing T] :
    @etale_retraction_unique_property.{w, v} T _ _ := by
  -- Route correction: reuse the earlier TFAE owner clause instead of reconstructing the
  -- standard-etale localization proof inside this item.
  -- Proof comment: clause `0 → 7` of Lemma 10.153.3 is exactly the unique étale-retraction
  -- property for a henselian local ring.
  have hT : HenselianLocalRing T := inferInstance
  exact ((henselian_local_ring_tfae (R := T)).out 0 7).mp hT

/-- Helper for Chap10 Lemma 10 153 11: the generic henselian criterion still needed by this
entry, stated for an arbitrary etale algebra over the henselian local base. -/
lemma existsUnique_etaleRetraction_of_henselianLocal
    (B : Type*) [CommRing B] [Algebra S B] [Algebra.Etale S B]
    (Q : Ideal B) [Q.IsPrime]
    (hQ : maximalIdeal S = Ideal.comap (algebraMap S B) Q)
    (hκ :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal S) Q (algebraMap S B) hQ)) :
    ∃! ρ : B →ₐ[S] S, Q = Ideal.comap (ρ : B →+* S) (maximalIdeal S) := by
  -- Proof comment: package the prime as a `PrimeSpectrum` point, since the owner criterion is
  -- formulated for points rather than bare ideals.
  let q : PrimeSpectrum B := ⟨Q, inferInstance⟩
  have hκa :
      Function.Bijective
        (Ideal.ResidueField.mapₐ (maximalIdeal S) q.asIdeal (Algebra.ofId S B) hQ) := by
    -- Proof comment: the residue-field map in this file is the same map as the algebra-hom
    -- version used by the TFAE criterion.
    simpa [q, Ideal.ResidueField.mapₐ] using hκ
  have hprop : @etale_retraction_unique_property S _ _ :=
    etaleRetractionUniqueProperty_of_henselianLocal (T := S)
  -- Proof comment: apply the owner criterion and unfold the `PrimeSpectrum` package.
  simpa [q] using hprop (S := B) q hQ hκa

/-- Helper for Chap10 Lemma 10 153 11: the remaining owner-level henselian input, specialized to
the base-change prime constructed from the residue-field point `τ`. -/
lemma existsUnique_baseChangeRetraction_of_henselianLocal
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! ρ : S ⊗[R] A →ₐ[S] S,
      baseChangeResiduePrime (q := q) hq τ hτ =
        Ideal.comap (ρ : S ⊗[R] A →+* S) (maximalIdeal S) := by
  -- Route correction: the earlier owner theorem now supplies the generic etale-neighborhood
  -- criterion, so the tensor-specific statement only has to verify the prime and residue map
  -- side conditions.
  -- Proof comment: install the canonical etale structure on the base change and the prime
  -- structure on the kernel prime, then feed the generic criterion the two verified tensor-prime
  -- side conditions.
  letI : Algebra.Etale S (S ⊗[R] A) := tensorProduct_baseChange_etale
  letI : (baseChangeResiduePrime (q := q) hq τ hτ).IsPrime :=
    (RingHom.ker_isMaximal_of_surjective
      (baseChangeResiduePointMap (q := q) hq τ hτ).toRingHom
      (baseChangeResiduePointMap_surjective (q := q) hq τ hτ)).isPrime
  have hQ :
      maximalIdeal S =
        Ideal.comap (algebraMap S (S ⊗[R] A)) (baseChangeResiduePrime (q := q) hq τ hτ) := by
    simpa [baseChangeResiduePrime] using
      (baseChangeResiduePrime_comap_includeLeft (q := q) hq τ hτ).symm
  have hκ :
      Function.Bijective
        (Ideal.ResidueField.map (maximalIdeal S) (baseChangeResiduePrime (q := q) hq τ hτ)
          (algebraMap S (S ⊗[R] A)) hQ) := by
    simpa [hQ] using
      baseChangeResiduePrime_residueFieldMap_bijective (q := q) hq τ hτ
  exact existsUnique_etaleRetraction_of_henselianLocal
    (B := S ⊗[R] A) (Q := baseChangeResiduePrime (q := q) hq τ hτ) hQ hκ

/- Domain-style sampling:
- primary domain: henselian local rings, étale neighborhoods, and residue-field controlled lifts
  of points to henselian local targets;
- sampled owner declarations in the surrounding chapter/domain:
  `HenselianLocalRing`,
  `etale_retraction_unique_property`,
  `RingHom.IsFilteredColimitOfEtale`,
  `existsUnique_algHom_of_filteredColimitOfEtale_of_henselianLocal_of_residueFieldMap`;
- best owner abstraction:
  the core owner is the henselian étale-retraction criterion
  `etale_retraction_unique_property`, while the present file is `source-facing`, recording the
  textbook étale-algebra specialization before the later ind-étale generalization of
  Lemma `10.154.6`;
- primitive data vs. derived API:
  the primitive source-facing inputs are the étale `R`-algebra `A`, the chosen prime `q`, and the
  compatible residue-field map `τ`;
  the derived API is the unique `R`-algebra map `A → S` inducing that residue-field map.

Source/core/bridge triage:
- `source-facing`: the present étale lifting theorem;
- `core/canonical`: `HenselianLocalRing S` together with `etale_retraction_unique_property S`;
- `bridge/view`: the passage from the chosen prime and residue-field map on `A` to the unique
  `R`-algebra point of `A` valued in the henselian local ring `S`.
-/

-- Proof sketch: base change the étale `R`-algebra `A` along `R → S` to obtain the étale
-- `S`-algebra `A ⊗[R] S`. The prime `q` together with the chosen residue-field map `τ` determines
-- a prime of `A ⊗[R] S` over `maximalIdeal S` whose residue field is the same as that of `S`.
-- Apply the unique étale-neighborhood retraction characterization of henselian local rings from
-- Lemma `10.153.3` to get a unique `S`-algebra retraction `A ⊗[R] S → S`, then compose it with
-- the canonical map `A → A ⊗[R] S`.
/-- Source-facing algebra-map form for Chap10 Lemma 10 153 11: let `R → S` be a ring map with
`S` henselian local. If `R → A` is étale,
`q` is a prime of `A` whose contraction is the contraction of `maximalIdeal S`, and
`τ : κ(q) → S / maximalIdeal S` is compatible with the induced map from the common residue field
`κ(q ∩ R)`, then there exists a unique `R`-algebra map `f : A → S` whose inverse image of
`maximalIdeal S` is `q` and which induces `τ` on residue fields. -/
lemma existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := by
  -- Proof comment: cut out a prime of the base change using the chosen residue-field point `τ`,
  -- then apply the isolated henselian retraction criterion for that base-change prime.
  letI : (baseChangeResiduePrime (q := q) hq τ hτ).IsPrime :=
    (RingHom.ker_isMaximal_of_surjective
      (baseChangeResiduePointMap (q := q) hq τ hτ).toRingHom
      (baseChangeResiduePointMap_surjective (q := q) hq τ hτ)).isPrime
  -- Proof comment: the base-change retraction comes from the imported henselian
  -- etale-neighborhood criterion, and then its restriction to the right tensor factor gives the
  -- required `R`-algebra map.
  obtain ⟨ρ, hρQ, hρuniq⟩ :=
    existsUnique_baseChangeRetraction_of_henselianLocal (q := q) hq τ hτ
  let f : A →ₐ[R] S :=
    (ρ.restrictScalars R).comp (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
  refine ⟨f, ?_, ?_⟩
  · have hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S) := by
      exact algHomComapOfBaseChangeRetraction (q := q)
        (Q := baseChangeResiduePrime (q := q) hq τ hτ) ρ
        (baseChangeResiduePrime_comap_includeRight (q := q) hq τ hτ)
        hρQ
    refine ⟨hfq, ?_⟩
    -- Proof comment: compute the induced residue map on algebra generators of `A`.
    apply Ideal.ResidueField.ringHom_ext
    apply RingHom.ext
    intro x
    simpa [f, Ideal.ResidueField.map_algebraMap] using
      baseChangeRetraction_residue_includeRight (q := q) hq τ hτ ρ hρQ x
  · intro g hg
    obtain ⟨hgq, hgτ⟩ := hg
    let ρg : S ⊗[R] A →ₐ[S] S :=
      Algebra.TensorProduct.lift (AlgHom.id S S) g (fun _ _ => Commute.all _ _)
    let χg : S ⊗[R] A →ₐ[S] (maximalIdeal S).ResidueField :=
      (Algebra.ofId S (maximalIdeal S).ResidueField).comp ρg
    have hχg : χg = baseChangeResiduePointMap (q := q) hq τ hτ := by
      apply Algebra.TensorProduct.ext
      · have hχleft :
            χg.comp (Algebra.TensorProduct.includeLeft : S →ₐ[S] S ⊗[R] A) =
              Algebra.ofId S (maximalIdeal S).ResidueField := by
          simpa [χg, AlgHom.comp_assoc] using
            congrArg (fun φ : S →ₐ[S] S =>
              (Algebra.ofId S (maximalIdeal S).ResidueField).comp φ)
              (baseChangeRetraction_comp_includeLeft ρg)
        exact hχleft.trans (baseChangeResiduePointMap_comp_includeLeft (q := q) hq τ hτ).symm
      · ext x
        have hx := congrFun (congrArg DFunLike.coe hgτ) (algebraMap A q.ResidueField x)
        have hright := congrFun (congrArg DFunLike.coe
          (baseChangeResiduePointMap_comp_includeRight (q := q) hq τ hτ)) x
        simpa [χg, ρg, baseChangeResiduePoint, Ideal.ResidueField.map_algebraMap] using
          hx.trans hright.symm
    have hρgQ :
        baseChangeResiduePrime (q := q) hq τ hτ =
          Ideal.comap (ρg : S ⊗[R] A →+* S) (maximalIdeal S) := by
      ext z
      -- Proof comment: the competing map has the same residue-field point, hence the same kernel.
      change (baseChangeResiduePointMap (q := q) hq τ hτ) z = 0 ↔ ρg z ∈ maximalIdeal S
      rw [← hχg]
      exact Ideal.algebraMap_residueField_eq_zero
    have hρg_eq : ρg = ρ := hρuniq ρg hρgQ
    -- Proof comment: equality of retractions restricts along the right tensor factor to equality
    -- of the original `R`-algebra maps.
    apply AlgHom.ext
    intro x
    have happ := congrFun (congrArg DFunLike.coe hρg_eq)
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) x)
    simpa [f, ρg] using happ

/-- Chap10 Lemma 10 153 11: let `R → S` be a ring map with `S` henselian local. If `R → A` is
étale, `q` is a prime of `A` whose contraction is the contraction of `maximalIdeal S`, and
`τ : κ(q) → S / maximalIdeal S` is compatible with the induced map from the common residue field
`κ(q ∩ R)`, then there exists a unique `R`-algebra map `f : A → S` whose inverse image of
`maximalIdeal S` is `q` and which induces `τ` on residue fields. -/
@[stacks 08HQ]
lemma existsUnique_retraction_of_etale_henselianLocal
    (q : Ideal A) [q.IsPrime]
    (hq : q.under R = (maximalIdeal S).under R)
    (τ : q.ResidueField →+* (maximalIdeal S).ResidueField)
    (hτ :
      τ.comp (Ideal.ResidueField.map (q.under R) q (algebraMap R A) rfl) =
        Ideal.ResidueField.map (q.under R) (maximalIdeal S) (algebraMap R S) hq) :
    ∃! f : A →ₐ[R] S,
      ∃ hfq : q = Ideal.comap (f : A →+* S) (maximalIdeal S),
        Ideal.ResidueField.map q (maximalIdeal S) (f : A →+* S) hfq = τ := by
  -- Proof comment: this planned declaration name is the same source-facing lifting theorem.
  exact existsUnique_algHom_of_etale_of_henselianLocal_of_residueFieldMap (q := q) hq τ hτ

end
