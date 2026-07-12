import Mathlib
import StacksProject_2024.Chap10.Definition_10_165_2
import StacksProject_2024.Chap10.Lemma_10_37_15
import StacksProject_2024.Chap10.Lemma_10_43_5
import StacksProject_2024.Chap10.Lemma_10_43_6
import StacksProject_2024.Chap10.Lemma_10_164_3
import StacksProject_2024.Chap10.Lemma_10_165_1

-- Declarations for this item will be appended below by the statement pipeline.

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
