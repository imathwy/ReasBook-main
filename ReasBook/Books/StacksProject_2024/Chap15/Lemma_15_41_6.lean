import Mathlib
import stacks_project.Chap10.Lemma_10_44_2
import stacks_project.Chap10.Lemma_10_44_4
import stacks_project.Chap10.Lemma_10_158_11
import stacks_project.Chap15.Lemma_15_41_3_Regular_maps_and_base_change
import stacks_project.Chap15.Lemma_15_41_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace Algebra

universe u v

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/- Domain triage:
- primary domain: regular ring maps and separability of field extensions in commutative algebra;
- sampled owner declarations of the same kind:
  `IsRegularRingMap`,
  `IsSeparableOver`,
  `isSeparableOver_iff_isGeometricallyReduced`,
  `isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable`,
  `RingHom.IsFilteredColimitOfSmooth`,
  `RingHom.IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers`;
- best owner abstraction: the main statement is source-facing, while the canonical owners are
  `IsRegularRingMap k K` on the regularity side and `IsSeparableOver k K` on the field-extension
  side;
- primitive data: only the field extension `k → K`;
- derived API: the regular-base-change owner theorem
  `RingHom.IsRegularRingMap.baseChange_of_essFiniteType`, the zero-prime fiber equivalence over a
  field from the residue-field / tensor-product owner API, the reduced-fiber owner theorem
  `RingHom.IsRegularRingMap.isReduced_fiber`, the geometric-reducedness bridge from
  `Lemma_10_44_4`, and the filtered-colimit-of-smooth presentation supplied by
  `Lemma_10_158_11`.

Layering:
- `isRegularRingMap_iff_isSeparableOver` is `source-facing`;
- `IsRegularRingMap` and `IsSeparableOver` are the `core/canonical` owners;
- `isSeparableOver_iff_isGeometricallyReduced`,
  `isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable`, and
  the derived regular-map consequences
  `RingHom.IsRegularRingMap.baseChange_of_essFiniteType`, together with the residue-field / fiber
  equivalence for the unique prime of a field and `(algebraMap k K).IsFilteredColimitOfSmooth`, are
  `bridge/view` theorems used to move between the source-facing owner statement and the finite
  purely inseparable / filtered-colimit characterizations already available earlier in the chapter.
-/

-- Proof sketch: if `k → K` is regular, then after any finite purely inseparable field extension
-- `L / k`, the base-changed map `L → L ⊗[k] K` is still regular by the canonical base-change
-- theorem `15.41.3`. Over the unique prime of the field `L`, the fiber of this map is canonically
-- `L ⊗[k] K` itself via the standard residue-field equivalence and `TensorProduct.lid`; the fiber
-- is reduced by the owner theorem `RingHom.IsRegularRingMap.isReduced_fiber`.
-- `Lemma_10_44_4` upgrades this family of reduced tensor base changes to geometric reducedness,
-- and `Lemma_10_44_2` then identifies that with Stacks-separability.
-- Conversely, if `K / k` is separable in the Stacks Project sense, then `Lemma_10_158_11`
-- provides the canonical smooth-presentation bridge for `K`, and
-- `RingHom.IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers` upgrades that bridge
-- to regularity of the structure map.
/-- Lemma 15.41.6: for a field extension `K / k`, the structure map `k → K` is a regular ring map
if and only if `K / k` is separable in the Stacks Project sense. -/
theorem isRegularRingMap_iff_isSeparableOver :
    (algebraMap k K).IsRegularRingMap ↔ IsSeparableOver k K := by
  constructor
  · intro hreg
    have hgred : IsGeometricallyReduced k K := by
      refine isGeometricallyReduced_iff_isReduced_tensorProduct_finitePurelyInseparable.2 ?_
      intro L _ _ _ _
      let _ : Algebra.EssFiniteType k L := inferInstance
      let T : Type (max u v) := TensorProduct k L K
      have hbase : RingHom.IsRegularRingMap (algebraMap L T) := by
        simpa [T] using
          (RingHom.IsRegularRingMap.baseChange_of_essFiniteType hreg :
            RingHom.IsRegularRingMap (algebraMap L (TensorProduct k L K)))
      let _ : RingHom.IsRegularRingMap (algebraMap L T) := hbase
      let _ : Algebra L T := (algebraMap L T).toAlgebra
      let p : PrimeSpectrum L := ⟨⊥, Ideal.isPrime_bot⟩
      let φ : L →ₐ[L] p.asIdeal.ResidueField := IsScalarTower.toAlgHom L L p.asIdeal.ResidueField
      have hφ : Function.Bijective φ := by
        constructor
        · exact RingHom.injective _
        · simpa [p] using Ideal.algebraMap_residueField_surjective (⊥ : Ideal L)
      let eκ : p.asIdeal.ResidueField ≃ₐ[L] L := (AlgEquiv.ofBijective φ hφ).symm
      let e : p.asIdeal.Fiber T ≃ₐ[L] T :=
        (Algebra.TensorProduct.congr eκ
          (AlgEquiv.refl : T ≃ₐ[L] T)).trans
          (Algebra.TensorProduct.lid L T)
      have hregT : RingHom.IsRegularRingMap (algebraMap L T) := hbase
      have hredFiber : IsReduced (p.asIdeal.Fiber T) := by
        simpa using hregT.isReduced_fiber p
      exact isReduced_of_injective e.symm.toRingHom e.symm.injective
    exact isSeparableOver_iff_isGeometricallyReduced.2 hgred
  · intro hsep
    letI : IsSeparableOver k K := hsep
    sorry

end

end Algebra
