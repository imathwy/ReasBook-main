import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_10_165_1 (from Chap10) -/
open scoped TensorProduct

universe u v w

section

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/- Domain triage:
- `source-facing`: the four-way field-extension criterion for normality in Lemma `10.165.1`;
- `core/canonical`: the ring-level owner `IsNormalRing` together with the tensor base-change
  objects `k' ⊗[k] A`;
- `bridge/view`: the pairwise clause projections extracted from the `List.TFAE`.

The theorem below should remain the source-facing TFAE. The individual implications among its
clauses are derived API and should be named once here, then reused downstream instead of rebuilding
the same proposition list locally.
-/
-- Proof sketch: `(1) → (2) → (3)` and `(1) → (4)` are immediate. For `(4) → (3)`, embed any
-- finite purely inseparable extension into the chosen perfect closure and descend normality along
-- the induced faithfully flat base-change map. For `(2) → (1)`, write an arbitrary field
-- extension as a directed colimit of finitely generated subextensions and apply stability of
-- normality under filtered colimits. For `(3) → (2)`, replace a finitely generated extension by a
-- finite purely inseparable extension that becomes separable over a finite purely inseparable
-- extension of the base, then use ascent along smooth algebras, localization, and faithful-flat
-- descent.
/-- Lemma 10.165.1: for a commutative `k`-algebra `A`, the following are equivalent: every base
change `k' ⊗[k] A` to a field extension `k' / k` is a normal ring, it suffices to check this for
finitely generated field extensions, it suffices to check this for finite purely inseparable field
extensions, and it suffices to check it after base change to the chosen model
`perfectClosure k (AlgebraicClosure k)` of `k^{perf}`. -/
theorem isNormalRing_tensorProduct_tfae_essFiniteType_finitePurelyInseparable_perfectClosure :
    List.TFAE [
      ∀ (k' : Type w) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type w) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
        IsNormalRing (k' ⊗[k] A),
      ∀ (k' : Type w) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A),
      IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)
    ] := sorry

/-- Lemma 10.165.1, clauses `(1) ↔ (3)`: it is enough to test normality of all tensor base
changes `k' ⊗[k] A` on finite purely inseparable field extensions `k' / k`. -/
theorem forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable :
    (∀ (k' : Type w) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A)) ↔
      ∀ (k' : Type w) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] A) := by
  let l : List Prop := [
    ∀ (k' : Type w) [Field k'] [Algebra k k'], IsNormalRing (k' ⊗[k] A),
    ∀ (k' : Type w) [Field k'] [Algebra k k'] [Algebra.EssFiniteType k k'],
      IsNormalRing (k' ⊗[k] A),
    ∀ (k' : Type w) [Field k'] [Algebra k k'] [FiniteDimensional k k']
      [IsPurelyInseparable k k'],
      IsNormalRing (k' ⊗[k] A),
    IsNormalRing (perfectClosure k (AlgebraicClosure k) ⊗[k] A)
  ]
  have htfae : List.TFAE l := by
    simpa [l] using
      isNormalRing_tensorProduct_tfae_essFiniteType_finitePurelyInseparable_perfectClosure
  simpa [l] using htfae.out 0 2 (by simp [l]) (by simp [l])

end

/-! ### Definition_10_165_2 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

/-- Definition 10.165.2: a commutative `k`-algebra `R` is geometrically normal over `k` if for
every field extension `K / k`, the base change `K ⊗[k] R` is a normal ring. By Lemma 10.165.1,
this is equivalent to the other usual tests for geometric normality. -/
class IsGeometricallyNormal (k : Type u) (R : Type v) [Field k] [CommRing R] [Algebra k R] :
    Prop where
  /-- Every scalar extension of a geometrically normal algebra to a field is a normal ring. -/
  isNormalRing_baseChange (K : Type (max u v)) [Field K] [Algebra k K] :
    IsNormalRing (K ⊗[k] R)

section

variable (k : Type u) [Field k]

/-- The ground field is geometrically normal over itself. -/
instance : IsGeometricallyNormal k k := by
  refine ⟨?_⟩
  intro K _ _
  let e : K ⊗[k] k ≃ₐ[k] K := TensorProduct.rid k k K
  letI : IsDomain (K ⊗[k] k) := Function.Injective.isDomain e.toRingHom e.injective
  letI : IsIntegrallyClosed (K ⊗[k] k) := IsIntegrallyClosed.of_equiv e.symm.toRingEquiv
  infer_instance

end

end Algebra

/-! ### Lemma_10_165_3 (from Chap10) -/
universe u v w x

namespace Algebra

variable {k : Type u} [Field k]
variable {A : Type v} [CommRing A] [Algebra k A]
variable {B : Type w} [CommRing B] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- Lemma 10.165.3: a localization of a geometrically normal `k`-algebra is geometrically normal. -/
-- Proof sketch: for any field extension `K/k`, the scalar extension `K ⊗[k] B` is a localization
-- of `K ⊗[k] A`; since normality is checked on prime localizations, localizing a normal ring
-- remains normal.
theorem IsGeometricallyNormal.of_isLocalization (S : Submonoid A) [IsLocalization S B]
    [IsGeometricallyNormal k A] : IsGeometricallyNormal k B := by
  refine { isNormalRing_baseChange := ?_ }
  intro K instK instKA
  letI := instK
  letI := instKA
  haveI : IsNormalRing K := by infer_instance
  letI : IsNormalRing (TensorProduct k A K) := by infer_instance
  let e₀ : TensorProduct k A K ≃ₐ[k] TensorProduct k K A := Algebra.TensorProduct.comm k A K
  let f₀ : TensorProduct k K A →+* TensorProduct k A K := e₀.symm.toRingHom
  have hf₀ : RingHom.FaithfullyFlat f₀ := by
    let hbij : Function.Bijective f₀ := e₀.symm.bijective
    exact RingHom.FaithfullyFlat.of_bijective hbij
  letI : IsNormalRing (TensorProduct k K A) := isNormalRing_of_faithfullyFlat f₀ hf₀
  letI : Algebra A (TensorProduct k K A) := Algebra.TensorProduct.rightAlgebra
  letI : IsLocalization (Algebra.algebraMapSubmonoid (TensorProduct k K A) S)
      (TensorProduct A (TensorProduct k K A) B) := by
    infer_instance
  letI : IsNormalRing (TensorProduct A (TensorProduct k K A) B) :=
    isNormalRing_of_isLocalization (Algebra.algebraMapSubmonoid (TensorProduct k K A) S)
  let e : TensorProduct A (TensorProduct k K A) B ≃ₐ[K] TensorProduct k K B :=
    Algebra.IsPushout.cancelBaseChangeAlg k K A (TensorProduct k K A) B
  letI : CommRing (TensorProduct k K B) := inferInstance
  letI : CommRing (TensorProduct A (TensorProduct k K A) B) := inferInstance
  let f : TensorProduct k K B →+* TensorProduct A (TensorProduct k K A) B := e.symm.toRingHom
  have hf : RingHom.FaithfullyFlat f := by
    let hbij : Function.Bijective f := e.symm.bijective
    exact RingHom.FaithfullyFlat.of_bijective hbij
  exact isNormalRing_of_faithfullyFlat f hf

end Algebra

/-! ### Lemma_10_165_4 (from Chap10) -/
open scoped TensorProduct

universe u v

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable [IsSeparableOver k K]

/- Domain triage:
- `source-facing`: the field-extension corollary that a Stacks-separable extension is
  geometrically normal over its base field.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyNormal`.
- `bridge/view`: the sampled owner-level bridges are
  `isReduced_tensorProduct_of_geometricallyReduced`,
  `isNormalRing_tensorProduct_tfae_essFiniteType_finitePurelyInseparable_perfectClosure`,
  `IsArtinianRing.equivPi`,
  and `isNormalRing_of_faithfullyFlat`.

Primitive data are only the field extension `K / k` together with the chapter owner
`IsSeparableOver k K`. Geometric reducedness, the finite purely inseparable normality test, and
the Artinian product decomposition are derived API. The file remains a thin source-facing
corollary rather than an algebraic-only specialization or a parallel wrapper.
-/
-- Proof sketch: by Lemma `10.165.1`, it suffices to prove normality after every finite purely
-- inseparable base change `k' / k`. Since `K / k` is separable in the Stacks Project sense,
-- every tensor product `k' ⊗[k] K` is reduced. For finite `k' / k`, commute the tensor factors to
-- view this ring as a finite `K`-algebra, hence an Artinian reduced ring; `IsArtinianRing.equivPi`
-- identifies it with a finite product of fields, which is normal, and faithful-flat descent along
-- the resulting ring equivalences transports normality back.
/-- Lemma 10.165.4: a field extension that is separable in the sense of Definition `10.42.1 (2)`
is geometrically normal over the base field. -/
theorem isGeometricallyNormal_of_isSeparableOver :
    IsGeometricallyNormal k K := by
  refine ⟨?_⟩
  have hfinite :
      ∀ (k' : Type (max u v)) [Field k'] [Algebra k k'] [FiniteDimensional k k']
        [IsPurelyInseparable k k'],
        IsNormalRing (k' ⊗[k] K) := by
    intro k' _ _ _ _
    have hred : IsReduced (k' ⊗[k] K) :=
      isReduced_tensorProduct_of_geometricallyReduced
    let e : k' ⊗[k] K ≃ₐ[k] K ⊗[k] k' := Algebra.TensorProduct.comm k k' K
    letI : IsReduced (K ⊗[k] k') := isReduced_of_injective e.symm.toRingHom e.symm.injective
    letI : IsArtinianRing (K ⊗[k] k') := IsArtinianRing.of_finite K (K ⊗[k] k')
    letI :
        ∀ I : MaximalSpectrum (K ⊗[k] k'), IsNormalRing ((K ⊗[k] k') ⧸ I.asIdeal) :=
      fun I ↦ by
        letI : Field ((K ⊗[k] k') ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
        infer_instance
    letI : CommRing (∀ I : MaximalSpectrum (K ⊗[k] k'), (K ⊗[k] k') ⧸ I.asIdeal) :=
      inferInstance
    letI : IsNormalRing (∀ I : MaximalSpectrum (K ⊗[k] k'), (K ⊗[k] k') ⧸ I.asIdeal) :=
      isNormalRing_pi
    let f : K ⊗[k] k' →+* ∀ I : MaximalSpectrum (K ⊗[k] k'), (K ⊗[k] k') ⧸ I.asIdeal :=
      IsArtinianRing.equivPi (K ⊗[k] k')
    have hbij : Function.Bijective f := (IsArtinianRing.equivPi (K ⊗[k] k')).bijective
    have hf : RingHom.FaithfullyFlat f := by
      exact RingHom.FaithfullyFlat.of_bijective hbij
    letI : IsNormalRing (K ⊗[k] k') := isNormalRing_of_faithfullyFlat f hf
    let f' : k' ⊗[k] K →+* K ⊗[k] k' := e.toRingHom
    have hbij' : Function.Bijective f' := e.bijective
    have hf' : RingHom.FaithfullyFlat f' := by
      exact RingHom.FaithfullyFlat.of_bijective hbij'
    exact isNormalRing_of_faithfullyFlat f' hf'
  intro k' _ _
  have hall :
      ∀ (L : Type (max u v)) [Field L] [Algebra k L], IsNormalRing (L ⊗[k] K) :=
    (forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable.{u, v, max u v}).2 hfinite
  exact hall k'

@[instance low] instance : IsGeometricallyNormal k K :=
  isGeometricallyNormal_of_isSeparableOver

end

end Algebra

/-! ### Lemma_10_165_5 (from Chap10) -/
open scoped TensorProduct
open Algebra

universe u v w x

/-
Domain triage:
- `source-facing`: normality of the tensor product with one geometrically normal factor.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyNormal`.
- `bridge/view`: the tensor-product normality statement is derived API yielding an
  `IsNormalRing` instance; there is no extra wrapper object.

Sampled declarations in this domain:
- `Algebra.IsGeometricallyNormal` from `Definition_10_165_2`,
- `isReduced_tensorProduct_of_geometricallyReduced` from `Lemma_10_43_5`,
- `IsGeometricallyNormal.of_isLocalization` from `Lemma_10_165_3`.

Primitive data are only the field `k`, the two `k`-algebras `A` and `B`, and the hypotheses
`[IsGeometricallyNormal k A]` and `[IsNormalRing B]`. Normality of `A ⊗[k] B` is derived API and
should not be duplicated by a parallel local instance wrapper.
-/
section

variable {k : Type u} {A : Type v} {B : Type w}
variable [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
variable [IsGeometricallyNormal k A] [IsNormalRing B]

/-- Lemma 10.165.5: if `A` is geometrically normal over the field `k` and `B` is a normal
`k`-algebra, then `A ⊗[k] B` is a normal ring. -/
-- Proof sketch: localize at a prime of `A ⊗[k] B` and reduce to the case where both factors are
-- domains. Approximate `B` by finite type normal `k`-subalgebras, reduce by filtered colimits to
-- finite type, and then embed the tensor product into the intersections `Frac(A) ⊗[k] B` and
-- `A ⊗[k] Frac(B)`. The geometric normality of `A` makes the first overring normal after passing
-- through finitely generated subextensions of `Frac(A)`, so integral elements over `A ⊗[k] B`
-- already lie in the tensor product itself.
@[instance]
theorem isNormalRing_tensorProduct_of_isGeometricallyNormal :
    IsNormalRing (A ⊗[k] B) := sorry

end

/-! ### Lemma_10_165_6 (from Chap10) -/
open scoped TensorProduct

universe u v w

namespace Algebra

section

variable {k : Type u} {k' : Type v} {A : Type v}
variable [Field k] [Field k'] [CommRing A]
variable [Algebra k k'] [Algebra k' A] [Algebra k A] [IsScalarTower k k' A]
variable [Algebra.IsSeparable k k']

/-- Helper for Lemma 10.165.6: normality transports across ring equivalences. -/
theorem isNormalRing_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) [IsNormalRing R] : IsNormalRing S := by
  refine ⟨fun p ↦ ?_⟩
  let q : PrimeSpectrum R := PrimeSpectrum.comap e.toRingHom p
  let eLoc : Localization.AtPrime q.asIdeal ≃+* Localization.AtPrime p.asIdeal :=
    Localization.localRingEquiv _ _ e (PrimeSpectrum.comap_asIdeal (f := e.toRingHom) p)
  have hDomain : IsDomain (Localization.AtPrime q.asIdeal) := isDomain_localizationAtPrime q
  have hIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_localizationAtPrime q
  refine ⟨?_, ?_⟩
  · exact Function.Injective.isDomain eLoc.symm.toRingHom eLoc.symm.injective
  · exact IsIntegrallyClosed.of_equiv eLoc

/-- Helper for Lemma 10.165.6: geometric normality supplies normality for tensor products with
field extensions in any universe after transporting across `ULift.algEquiv`. -/
theorem isNormalRing_tensorProduct_of_geometricallyNormal_any_universe
    [IsGeometricallyNormal k A] (K : Type (max u v)) [Field K] [Algebra k K] :
    IsNormalRing (K ⊗[k] A) := by
  -- This helper is the owner field of geometric normality, restated for later reuse.
  simpa using IsGeometricallyNormal.isNormalRing_baseChange (k := k) (R := A) K

/-- Helper for Lemma 10.165.6: an algebra equivalence over the base field preserves geometric
normality. -/
theorem IsGeometricallyNormal.of_algEquiv {B : Type v} [CommRing B] [Algebra k B]
    [IsGeometricallyNormal k A] (e : A ≃ₐ[k] B) : IsGeometricallyNormal k B := by
  refine { isNormalRing_baseChange := ?_ }
  intro K _ _
  -- Tensor the given algebra equivalence with the arbitrary field extension.
  let eK : K ⊗[k] A ≃ₐ[K] K ⊗[k] B :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[K] K) e
  -- The source tensor product is normal by geometric normality of `A`.
  letI : IsNormalRing (K ⊗[k] A) :=
    isNormalRing_tensorProduct_of_geometricallyNormal_any_universe (k := k) (A := A) K
  -- Transport normality across the base-changed algebra equivalence.
  exact isNormalRing_of_ringEquiv eK.toRingEquiv

/-- Helper for Lemma 10.165.6: a separable algebraic field extension is geometrically normal over
the base field. -/
lemma isGeometricallyNormal_field_of_isSeparable_local :
    IsGeometricallyNormal k k' := by
  exact isGeometricallyNormal_of_isSeparableOver (k := k) (K := k')

/-- Helper for Lemma 10.165.6: if the intermediate field extension `k' / k` is geometrically
normal and `A` is geometrically normal over `k'`, then `A` is geometrically normal over `k`. -/
lemma isGeometricallyNormal_restrictScalars_of_geometricallyNormal_base
    [IsGeometricallyNormal k k'] [IsGeometricallyNormal k' A] :
    IsGeometricallyNormal k A := by
  refine ⟨?_⟩
  -- Route correction: use the finite purely inseparable test from the source proof, then rewrite
  -- the test ring via the standard `commRight` plus `cancelBaseChange` tensor comparison.
  let hfinite :
      ∀ (L : Type (max u v)) [Field L] [Algebra k L] [FiniteDimensional k L]
        [IsPurelyInseparable k L], IsNormalRing (L ⊗[k] A) := by
    intro L _ _ _ _
    -- The intermediate tensor product `L ⊗[k] k'` is normal because `k'` is geometrically normal
    -- over `k`.
    letI : IsNormalRing (L ⊗[k] k') :=
      isNormalRing_tensorProduct_of_geometricallyNormal_any_universe (k := k) (A := k') L
    letI : IsNormalRing (k' ⊗[k] L) :=
      isNormalRing_of_ringEquiv (Algebra.TensorProduct.comm k L k').toRingEquiv
    -- Tensor this normal ring with the geometrically normal `k'`-algebra `A`.
    letI : IsNormalRing (A ⊗[k'] (k' ⊗[k] L)) :=
      isNormalRing_tensorProduct_of_isGeometricallyNormal (k := k') (A := A)
        (B := k' ⊗[k] L)
    let e : A ⊗[k'] (k' ⊗[k] L) ≃+* L ⊗[k] A :=
      ((Algebra.TensorProduct.cancelBaseChange k k' A A L).toRingEquiv).trans <|
        (Algebra.TensorProduct.comm k A L).toRingEquiv
    -- Transport normality across the comparison to recover the original test ring.
    exact isNormalRing_of_ringEquiv (R := A ⊗[k'] (k' ⊗[k] L)) (S := L ⊗[k] A) e
  -- The finite purely inseparable criterion is exactly Lemma `10.165.1`.
  exact (forall_isNormalRing_tensorProduct_iff_finitePurelyInseparable
    (k := k) (A := A)).2 hfinite

/-- Helper for Lemma 10.165.6: after base change from `k` to `k'`, the resulting algebra
`k' ⊗[k] A` is geometrically normal over `k'` whenever `A` is geometrically normal over `k`. -/
lemma isGeometricallyNormal_tensor_baseChange [IsGeometricallyNormal k A] :
    IsGeometricallyNormal k' (k' ⊗[k] A) := by
  refine { isNormalRing_baseChange := ?_ }
  intro K _ _
  -- Equip `K` with the composite `k`-algebra structure so the source proof can compare the two
  -- tensor products by the canonical base-change cancellation isomorphism.
  letI : Algebra k K := ((algebraMap k' K).comp (algebraMap k k')).toAlgebra
  letI : IsScalarTower k k' K := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsNormalRing (ULift.{u} K ⊗[k] A) :=
    isNormalRing_tensorProduct_of_geometricallyNormal_any_universe (k := k) (A := A)
      (ULift.{u} K)
  let eLift : ULift.{u} K ⊗[k] A ≃+* K ⊗[k] A :=
    (Algebra.TensorProduct.congr (ULift.algEquiv (R := k) (A := K))
      (AlgEquiv.refl : A ≃ₐ[k] A)).toRingEquiv
  letI : IsNormalRing (K ⊗[k] A) := isNormalRing_of_ringEquiv eLift
  let e : K ⊗[k'] (k' ⊗[k] A) ≃+* K ⊗[k] A :=
    (Algebra.TensorProduct.cancelBaseChange k k' K K A).toRingEquiv
  -- The comparison isomorphism turns the base-changed test ring into the original one.
  exact isNormalRing_of_ringEquiv e.symm

/-- Helper for Lemma 10.165.6: the source proof uses the right-ordered base change
`A ⊗[k] k'`, so commute the standard base change once and transport geometric normality there. -/
lemma isGeometricallyNormal_tensor_baseChange_commRight [IsGeometricallyNormal k A] :
    letI : Algebra k' (A ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
    IsGeometricallyNormal k' (A ⊗[k] k') := by
  letI : IsGeometricallyNormal k' (k' ⊗[k] A) :=
    isGeometricallyNormal_tensor_baseChange (k := k) (k' := k') (A := A)
  letI : Algebra k' (A ⊗[k] k') := Algebra.TensorProduct.rightAlgebra
  -- Proof comment: `commRight` rewrites the usual base change into the tensor order used by the
  -- source diagonal-localization argument.
  exact IsGeometricallyNormal.of_algEquiv
    (k := k') (A := k' ⊗[k] A) (B := A ⊗[k] k')
    (Algebra.TensorProduct.commRight k k' A)

/-- Helper for Lemma 10.165.6: the same right-ordered tensor product is geometrically normal
over `k'` when viewed through the left tensor factor. -/
lemma isGeometricallyNormal_tensor_baseChange_left [IsGeometricallyNormal k A] :
    IsGeometricallyNormal k' (A ⊗[k] k') := by
  sorry

/-- Helper for Lemma 10.165.6: geometric normality of `k' ⊗[k'] A` collapses back to `A` through
the standard left-unital tensor equivalence. -/
lemma isGeometricallyNormal_of_tensorProduct_lid :
    IsGeometricallyNormal k' (k' ⊗[k'] A) → IsGeometricallyNormal k' A := by
  intro h
  letI : IsGeometricallyNormal k' (k' ⊗[k'] A) := h
  -- The tensor product over the same field is canonically just `A`.
  exact IsGeometricallyNormal.of_algEquiv
    (k := k') (A := k' ⊗[k'] A) (B := A)
    (Algebra.TensorProduct.lid k' A)

/-- Helper for Lemma 10.165.6: tensoring a `k'`-algebra map `Q → k'` on the right fixes the
canonical right tensor inclusion. -/
theorem tensor_right_map_includeRight_comp_local {Q : Type w} [CommRing Q]
    [Algebra k' Q] (φ : Q →ₐ[k'] k') :
    (letI : Algebra (Q ⊗[k'] A) (k' ⊗[k'] A) :=
      (Algebra.TensorProduct.map φ (AlgHom.id k' A)).toAlgebra
    (algebraMap (Q ⊗[k'] A) (k' ⊗[k'] A)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) := by
  ext x
  -- Proof comment: both composites send `x` to the pure tensor `1 ⊗ₜ x`.
  change Algebra.TensorProduct.map φ (AlgHom.id k' A) (1 ⊗ₜ[k'] x) = 1 ⊗ₜ[k'] x
  simp

/-- Helper for Lemma 10.165.6: once the right-tensored diagonal map is aligned, tensor-product
localization gives the localized target over the same denominator set. -/
theorem tensor_right_isLocalization_local {Q : Type w} [CommRing Q]
    [Algebra k' Q] [Algebra Q k'] [IsScalarTower k' Q k']
    (M : Submonoid Q) [IsLocalization M k']
    [Algebra A (Q ⊗[k'] A)] [Algebra A (k' ⊗[k'] A)]
    [Algebra (Q ⊗[k'] A) (k' ⊗[k'] A)]
    [IsScalarTower Q (Q ⊗[k'] A) (k' ⊗[k'] A)]
    (hcompat : (algebraMap (Q ⊗[k'] A) (k' ⊗[k'] A)).comp
        Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    IsLocalization (Algebra.algebraMapSubmonoid (Q ⊗[k'] A) M) (k' ⊗[k'] A) := by
  -- Proof comment: this is exactly `tensorProduct_tensorProduct` after the compatibility square
  -- has been normalized into the right tensor order.
  exact IsLocalization.tensorProduct_tensorProduct k' A M k' hcompat

section DiagonalRight

/-- Helper for Lemma 10.165.6: the diagonal tensor source ring appearing in the localization
descent step. -/
abbrev diagonal_tensor_source := ((k' ⊗[k] k') ⊗[k'] A)

/-- Helper for Lemma 10.165.6: the right-tensored target ring appearing after diagonal
multiplication. -/
abbrev diagonal_tensor_target := (k' ⊗[k'] A)

/-- Helper for Lemma 10.165.6: the diagonal multiplication map also respects the left-factor
`k'`-algebra structure on `k' ⊗[k] k'`. -/
theorem diagonal_lmul_left_commutes (x : k') :
    (TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k')
        (algebraMap k' (k' ⊗[k] k') x) =
      algebraMap k' k' x := by
  -- Proof comment: rewrite the scalar action through the left tensor inclusion and apply the
  -- standard computation rule for `lmul'`.
  change ((TensorProduct.lmul' k).comp Algebra.TensorProduct.includeLeft) x = x
  simpa using congr($(TensorProduct.lmul'_comp_includeLeft (R := k) (S := k')) x)

/-- Helper for Lemma 10.165.6: package the diagonal multiplication map as a `k'`-algebra map for
the default left-factor algebra structure on `k' ⊗[k] k'`. -/
def diagonal_lmul_leftAlgHom : (k' ⊗[k] k') →ₐ[k'] k' :=
  { __ := (TensorProduct.lmul' k : k' ⊗[k] k' →ₐ[k] k').toRingHom
    commutes' := diagonal_lmul_left_commutes }

/-- Helper for Lemma 10.165.6: the left-factor packaged diagonal map gives the scalar-tower
identity needed to tensor the localization on the right by `A`. -/
lemma diagonal_lmul_left_tower_eq :
    algebraMap k' k' =
      (diagonal_lmul_leftAlgHom.toRingHom).comp
        (algebraMap k' (k' ⊗[k] k')) := by
  -- Proof comment: this is exactly the scalar-compatibility identity of
  -- `diagonal_lmul_leftAlgHom`, rewritten as a tower equality.
  ext x
  simpa using (diagonal_lmul_left_commutes (k := k) (k' := k') x).symm

/-- Helper for Lemma 10.165.6: after packaging the diagonal map as an `Algebra` structure on
`k'`, the same scalar-tower identity is expressed with the ambient `algebraMap`. -/
lemma diagonal_lmul_left_tower_eq_toAlgebra :
    letI : Algebra (k' ⊗[k] k') k' := diagonal_lmul_leftAlgHom.toAlgebra
    algebraMap k' k' =
      (algebraMap (k' ⊗[k] k') k').comp (algebraMap k' (k' ⊗[k] k')) := by
  letI : Algebra (k' ⊗[k] k') k' := diagonal_lmul_leftAlgHom.toAlgebra
  -- Proof comment: the packaged `algebraMap` is definitionally the same diagonal ring map.
  simpa [RingHom.algebraMap_toAlgebra] using
    (diagonal_lmul_left_tower_eq (k := k) (k' := k'))

/-- Helper for Lemma 10.165.6: the localization witness from Lemma `10.43.8` can be rewritten for
the packaged diagonal `Algebra` structure on `k'`. -/
lemma diagonal_lmul_left_isLocalizationMap_toAlgebra
    (M : Submonoid (k' ⊗[k] k'))
    (hM : M.IsLocalizationMap (TensorProduct.lmul' k)) :
    letI : Algebra (k' ⊗[k] k') k' := diagonal_lmul_leftAlgHom.toAlgebra
    M.IsLocalizationMap (algebraMap (k' ⊗[k] k') k') := by
  letI : Algebra (k' ⊗[k] k') k' := diagonal_lmul_leftAlgHom.toAlgebra
  -- Proof comment: `toAlgebra` keeps the same underlying ring map, so the localization witness
  -- transfers without changing denominators.
  simpa [diagonal_lmul_leftAlgHom, RingHom.algebraMap_toAlgebra] using hM

/-- Helper for Lemma 10.165.6: commute the diagonal source so the `k' ⊗[k] k'` factor sits on the
right, where the standard base-change cancellation can be applied. -/
def diagonal_tensor_source_algEquiv_assoc :
    ((k' ⊗[k] k') ⊗[k'] A) ≃ₐ[k'] A ⊗[k'] (k' ⊗[k] k') :=
  -- Proof comment: first commute the outer tensor product over `k'`; this is the tensor order
  -- needed to invoke the canonical base-change cancellation equivalence next.
  Algebra.TensorProduct.comm k' (k' ⊗[k] k') A

/-- Helper for Lemma 10.165.6: after freezing the right-factor `k'`-algebra structure on
`A ⊗[k] k'`, base-change cancellation rewrites `A ⊗[k'] (k' ⊗[k] k')` to `A ⊗[k] k'`. -/
def diagonal_tensor_source_algEquiv_cancelBaseChange :
    (A ⊗[k'] (k' ⊗[k] k')) ≃ₐ[k'] (A ⊗[k] k') :=
  -- Proof comment: this is the canonical cancellation isomorphism, now with the target
  -- `k'`-algebra structure given by the left tensor factor, which is the canonical algebra
  -- structure produced by `cancelBaseChange`.
  Algebra.TensorProduct.cancelBaseChange k k' k' A k'

/-- Helper for Lemma 10.165.6: the diagonal source
`((k' ⊗[k] k') ⊗[k'] A)` identifies with the right-ordered base change `A ⊗[k] k'`. -/
def diagonal_tensor_source_algEquiv_to_baseChangeRight :
    ((k' ⊗[k] k') ⊗[k'] A) ≃ₐ[k'] (A ⊗[k] k') :=
  -- Proof comment: the source proof first commutes the outer tensor product and then cancels the
  -- duplicated base field `k'`.
  (diagonal_tensor_source_algEquiv_assoc (k := k) (k' := k') (A := A)).trans
    (diagonal_tensor_source_algEquiv_cancelBaseChange (k := k) (k' := k') (A := A))

/-- Helper for Lemma 10.165.6: once `A ⊗[k] k'` is known geometrically normal over `k'`, the
same holds for the diagonal source via the canonical comparison equivalence. -/
lemma diagonal_tensor_source_geometricallyNormal [IsGeometricallyNormal k A] :
    IsGeometricallyNormal k' ((k' ⊗[k] k') ⊗[k'] A) := by
  letI : IsGeometricallyNormal k' (A ⊗[k] k') :=
    isGeometricallyNormal_tensor_baseChange_left (k := k) (k' := k') (A := A)
  -- Proof comment: the diagonal source is geometrically normal because the comparison
  -- equivalence rewrites it to the source-faithful right-ordered base-change ring `A ⊗[k] k'`.
  exact IsGeometricallyNormal.of_algEquiv
    (k := k') (A := A ⊗[k] k') (B := ((k' ⊗[k] k') ⊗[k'] A))
    (diagonal_tensor_source_algEquiv_to_baseChangeRight (k := k) (k' := k') (A := A)).symm

/-- Helper for Lemma 10.165.6: tensoring the diagonal multiplication map on the right by `A`
produces the source-to-target algebra map used in the localization descent. -/
def diagonal_tensor_source_to_lidTensorAlgHom :
    ((k' ⊗[k] k') ⊗[k'] A) →ₐ[k'] (k' ⊗[k'] A) :=
  -- Proof comment: tensor the packaged diagonal multiplication map with the identity on `A`.
  Algebra.TensorProduct.map diagonal_lmul_leftAlgHom (AlgHom.id k' A)

/-- Helper for Lemma 10.165.6: the exact diagonal `Q := k' ⊗[k] k'`-algebra structure on the
target `k' ⊗[k'] A` obtained by composing diagonal multiplication with the left tensor inclusion. -/
def diagonal_tensor_target_qAlgHom :
    (k' ⊗[k] k') →ₐ[k'] (k' ⊗[k'] A) :=
  -- Proof comment: this packages the fixed target `Q`-action once, so later scalar-tower and
  -- localization lemmas can reference a stable algebra map instead of repeatedly unfolding the
  -- same composite.
  (Algebra.TensorProduct.includeLeft : k' →ₐ[k'] (k' ⊗[k'] A)).comp diagonal_lmul_leftAlgHom

/-- Helper for Lemma 10.165.6: the right-tensored diagonal map carries the canonical left tensor
inclusion to the target algebra map determined by `diagonal_lmul_leftAlgHom`. -/
lemma diagonal_tensor_source_to_lidTensor_comp_includeLeft :
    letI : Algebra (k' ⊗[k] k') (k' ⊗[k'] A) :=
      diagonal_tensor_target_qAlgHom.toAlgebra
    diagonal_tensor_source_to_lidTensorAlgHom.toRingHom.comp
        (Algebra.TensorProduct.includeLeft :
          (k' ⊗[k] k') →ₐ[k'] ((k' ⊗[k] k') ⊗[k'] A)).toRingHom =
      algebraMap (k' ⊗[k] k') (k' ⊗[k'] A) := by
  letI : Algebra (k' ⊗[k] k') (k' ⊗[k'] A) :=
    diagonal_tensor_target_qAlgHom.toAlgebra
  -- Proof comment: `map_comp_includeLeft` rewrites the source composite, and the target side is
  -- exactly the algebra map for the chosen `Q`-action on `k' ⊗[k'] A`.
  change (diagonal_tensor_source_to_lidTensorAlgHom.comp
      (Algebra.TensorProduct.includeLeft :
        (k' ⊗[k] k') →ₐ[k'] ((k' ⊗[k] k') ⊗[k'] A))).toRingHom =
    algebraMap (k' ⊗[k] k') (k' ⊗[k'] A)
  rw [show diagonal_tensor_source_to_lidTensorAlgHom.comp
      (Algebra.TensorProduct.includeLeft :
        (k' ⊗[k] k') →ₐ[k'] ((k' ⊗[k] k') ⊗[k'] A)) =
      diagonal_tensor_target_qAlgHom by
        simpa [diagonal_tensor_source_to_lidTensorAlgHom, diagonal_tensor_target_qAlgHom] using
          (Algebra.TensorProduct.map_comp_includeLeft
            diagonal_lmul_leftAlgHom (AlgHom.id k' A))]
  rw [RingHom.algebraMap_toAlgebra]

/-- Helper for Lemma 10.165.6: the right-tensored diagonal map also fixes the canonical right
tensor inclusion from `A`. -/
lemma diagonal_tensor_source_to_lidTensor_comp_includeRight :
    letI : Algebra (((k' ⊗[k] k') ⊗[k'] A)) (k' ⊗[k'] A) :=
      diagonal_tensor_source_to_lidTensorAlgHom.toAlgebra
    (algebraMap (((k' ⊗[k] k') ⊗[k'] A)) (k' ⊗[k'] A)).comp
        (Algebra.TensorProduct.includeRight :
          A →ₐ[k'] ((k' ⊗[k] k') ⊗[k'] A)).toRingHom =
      (Algebra.TensorProduct.includeRight :
        A →ₐ[k'] (k' ⊗[k'] A)).toRingHom := by
  letI : Algebra (((k' ⊗[k] k') ⊗[k'] A)) (k' ⊗[k'] A) :=
    diagonal_tensor_source_to_lidTensorAlgHom.toAlgebra
  -- Proof comment: specialize the generic tensor-right compatibility theorem to the diagonal
  -- multiplication map tensored with the identity on `A`.
  simpa [diagonal_tensor_source_to_lidTensorAlgHom] using
    (tensor_right_map_includeRight_comp_local (k' := k') (A := A)
      (Q := k' ⊗[k] k') diagonal_lmul_leftAlgHom)

/-- Helper for Lemma 10.165.6: after freezing the diagonal `Q := k' ⊗[k] k'`-action on source and
target, tensor-product localization turns the diagonal map into the exact localization needed in
the forward implication. -/
lemma diagonal_tensor_source_localization_packaged
    (M : Submonoid (k' ⊗[k] k'))
    (hM : M.IsLocalizationMap (TensorProduct.lmul' k)) :
    letI : Algebra (((k' ⊗[k] k') ⊗[k'] A)) (k' ⊗[k'] A) :=
      diagonal_tensor_source_to_lidTensorAlgHom.toAlgebra
    IsLocalization
      (Algebra.algebraMapSubmonoid (diagonal_tensor_source (k := k) (k' := k') (A := A)) M)
      (diagonal_tensor_target (k' := k') (A := A)) := by
  sorry

end DiagonalRight

/- Domain triage:
- `source-facing`: invariance of geometric normality under a separable algebraic extension of the
  ground field.
- `core/canonical`: the owner abstraction is `Algebra.IsGeometricallyNormal`.
- `bridge/view`: the sampled owner-style declarations are:
  `Definition_10_165_2` for the owner predicate itself,
  `IsGeometricallyNormal.of_isLocalization` from Lemma `10.165.3`,
  `isNormalRing_tensorProduct_of_isGeometricallyNormal` from Lemma `10.165.5`,
  and the parallel owner-level separable-base-change theorem
  `isGeometricallyReduced_iff_of_isSeparable` from Lemma `10.43.9`.

Primitive data are only the field-extension hypotheses and the ambient `k'`-algebra `A`.
Geometric normality stays in the owner class, and the localization/tensor-product normality facts
remain derived API rather than primitive fields of a parallel wrapper.
-/
/-- Lemma 10.165.6: for a separable algebraic field extension `k' / k`, a `k'`-algebra `A` is
geometrically normal over `k` if and only if it is geometrically normal over `k'`. -/
-- Proof sketch: for `→`, every field extension of `k'` is in particular a field extension of `k`,
-- so the required normality statement is immediate from the owner definition. For `←`, any field
-- extension of `k` can be tensored with `k'`; separability makes the intermediate tensor product
-- geometrically normal over the larger field, and Lemmas `10.165.5` and `10.165.3` provide the
-- tensor-product and localization steps needed to descend normality back to the original
-- base-changed ring.
theorem isGeometricallyNormal_iff_of_isSeparable :
    IsGeometricallyNormal k A ↔ IsGeometricallyNormal k' A := by
  constructor
  · intro h
    letI : IsGeometricallyNormal k A := h
    obtain ⟨M, hM⟩ := exists_submonoid_tensorProduct_self_isLocalization (k := k) (K := k')
    letI : IsGeometricallyNormal k' (diagonal_tensor_source (k := k) (k' := k') (A := A)) :=
      diagonal_tensor_source_geometricallyNormal (k := k) (k' := k') (A := A)
    letI : Algebra (((k' ⊗[k] k') ⊗[k'] A)) (k' ⊗[k'] A) :=
      diagonal_tensor_source_to_lidTensorAlgHom.toAlgebra
    letI :
        IsLocalization
          (Algebra.algebraMapSubmonoid (diagonal_tensor_source (k := k) (k' := k') (A := A)) M)
          (diagonal_tensor_target (k' := k') (A := A)) :=
      diagonal_tensor_source_localization_packaged (k := k) (k' := k') (A := A) M hM
    let htarget : IsGeometricallyNormal k' (diagonal_tensor_target (k' := k') (A := A)) :=
      IsGeometricallyNormal.of_isLocalization
        (k := k')
        (A := diagonal_tensor_source (k := k) (k' := k') (A := A))
        (B := diagonal_tensor_target (k' := k') (A := A))
        (Algebra.algebraMapSubmonoid (diagonal_tensor_source (k := k) (k' := k') (A := A)) M)
    -- Proof comment: the source proof localizes the geometrically normal diagonal source and then
    -- collapses `k' ⊗[k'] A` back to `A` via the left-unital tensor equivalence.
    exact isGeometricallyNormal_of_tensorProduct_lid (k' := k') (A := A) htarget
  · intro h
    letI : IsGeometricallyNormal k' A := h
    letI : IsGeometricallyNormal k k' :=
      isGeometricallyNormal_field_of_isSeparable_local (k := k) (k' := k')
    exact isGeometricallyNormal_restrictScalars_of_geometricallyNormal_base
      (k := k) (k' := k') (A := A)

end

end Algebra
