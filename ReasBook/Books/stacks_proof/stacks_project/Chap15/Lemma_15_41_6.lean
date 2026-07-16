import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_44_2
import stacks_proof.stacks_project.Chap10.Lemma_10_44_4
import stacks_proof.stacks_project.Chap10.Lemma_10_158_11
import stacks_proof.stacks_project.Chap15.Definition_15_41_1_Field
import stacks_proof.stacks_project.Chap15.Lemma_15_41_3_Regular_maps_and_base_change
import stacks_proof.stacks_project.Chap15.Lemma_15_41_5

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
/-- Helper for Lemma 15.41.6: after installing the explicit `k`-algebra structure coming from
`algebraMap k K`, every field fiber `κ(p) ⊗[k] K` is Noetherian because it is canonically
equivalent to the field `K`. -/
lemma algebraMap_field_fiber_isNoetherianRing (p : PrimeSpectrum k) :
    let _ : Algebra k K := (algebraMap k K).toAlgebra
    IsNoetherianRing (p.asIdeal.Fiber K) := by
  letI : Algebra k K := (algebraMap k K).toAlgebra
  let eκ := Algebra.residueField_algEquiv_self_of_field_prime (k := k) p
  let _ : Algebra p.asIdeal.ResidueField k := eκ.toRingHom.toAlgebra
  let _ : Algebra p.asIdeal.ResidueField K :=
    ((algebraMap k K).comp (algebraMap p.asIdeal.ResidueField k)).toAlgebra
  let _ : IsScalarTower p.asIdeal.ResidueField k K := IsScalarTower.of_algebraMap_eq' rfl
  let e : p.asIdeal.Fiber K ≃ₐ[p.asIdeal.ResidueField] K :=
    Algebra.field_fiber_algEquiv (k := k) (A := K) p
  -- Transport Noetherianity across the canonical equivalence between the field fiber and `K`.
  exact isNoetherianRing_of_ringEquiv K e.symm.toRingEquiv

/-- Helper for Lemma 15.41.6: a directed smooth family of `k`-subalgebras with supremum `⊤`
packages directly into the categorical owner `RingHom.IsFilteredColimitOfSmooth`. -/
lemma algebraMap_isFilteredColimitOfSmooth_of_directed_smooth_subalgebra_family
    {ι : Type (max u v)} [Nonempty ι] (S : ι → Subalgebra k K) (hdir : Directed (· ≤ ·) S)
    (hsmooth : ∀ i, Smooth k ↥(S i)) (hSup : iSup S = (⊤ : Subalgebra k K)) :
    (algebraMap k K).IsFilteredColimitOfSmooth := by
  -- Route correction: the source-faithful proof does run through a filtered diagram of subalgebra
  -- stages, but the canonical `Under`-presentation has to be built at the common universe
  -- `max u v`. The naive unlifted `Under (CommRingCat.of k)` route fails because
  -- `CommRingCat.mkUnder` requires the base and stage carriers to live in the same universe.
  -- TODO for Lemma 15.41.6: repackage the stage family in `Under (CommRingCat.of (ULift.{v} k))`
  -- using `RingHom.ulift` on the stage maps and `Subalgebra.iSupLift` after transporting the
  -- target cocone to a genuine `(ULift.{v} k)`-algebra. The remaining blocker is a reusable
  -- same-universe bridge identifying the lifted stage cocone with the original subalgebra union.
  sorry

/-- Helper for Lemma 15.41.6: a separable field extension is a filtered colimit of smooth
subalgebras, expressed in the owner form expected by Lemma `15.41.5`. -/
lemma algebraMap_isFilteredColimitOfSmooth_of_isSeparableOver [IsSeparableOver k K] :
    (algebraMap k K).IsFilteredColimitOfSmooth := by
  -- Use the directed smooth-subalgebra presentation from Lemma `10.158.11`, then invoke the
  -- explicit categorical bridge proved just above.
  obtain ⟨ι, S, hdir, hsmooth, hSup⟩ :=
    exists_directed_smooth_subalgebra_family (k := k) (K := K)
  let T : Option ι → Subalgebra k K
    | none => ⊥
    | some i => S i
  have hsmooth_bot : Smooth k ↥((⊥ : Subalgebra k K)) := by
    -- The bottom subalgebra is canonically isomorphic to `k`, so its structure map is smooth.
    rw [← RingHom.smooth_algebraMap]
    simpa [RingHom.algebraMap_toAlgebra] using
      (RingHom.Smooth.of_bijective (Algebra.botEquiv k K).symm.bijective :
        (Algebra.botEquiv k K).symm.toRingHom.Smooth)
  have hdirT : Directed (· ≤ ·) T := by
    intro a b
    cases a with
    | none =>
        refine ⟨b, ?_, le_rfl⟩
        cases b with
        | none => exact le_rfl
        | some j => exact bot_le
    | some i =>
        cases b with
        | none => exact ⟨some i, le_rfl, bot_le⟩
        | some j =>
            rcases hdir i j with ⟨l, hil, hjl⟩
            exact ⟨some l, hil, hjl⟩
  have hsmoothT : ∀ a, Smooth k ↥(T a) := by
    intro a
    cases a with
    | none => simpa [T] using hsmooth_bot
    | some i => simpa [T] using hsmooth i
  have hSupT : iSup T = (⊤ : Subalgebra k K) := by
    apply le_antisymm le_top
    calc
      (⊤ : Subalgebra k K) = iSup S := hSup.symm
      _ ≤ iSup T := by
        refine iSup_le ?_
        intro i
        exact le_iSup T (some i)
  exact algebraMap_isFilteredColimitOfSmooth_of_directed_smooth_subalgebra_family
    (k := k) (K := K) T hdirT hsmoothT hSupT

/-- Lemma 15.41.6: for a field extension `K / k`, the structure map `k → K` is a regular ring map
if and only if `K / k` is separable in the Stacks Project sense. -/
@[stacks 07EQ]
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
    have hcolim : (algebraMap k K).IsFilteredColimitOfSmooth :=
      algebraMap_isFilteredColimitOfSmooth_of_isSeparableOver (k := k) (K := K)
    have hfiber_noetherian :
        let _ : Algebra k K := (algebraMap k K).toAlgebra
        ∀ p : PrimeSpectrum k, IsNoetherianRing (p.asIdeal.Fiber K) := by
      intro hK
      letI : Algebra k K := hK
      -- The regularity criterion from Lemma `15.41.5` reduces the field case to the unique
      -- Noetherianity statement for each fiber.
      intro p
      let eκ := Algebra.residueField_algEquiv_self_of_field_prime (k := k) p
      let _ : Algebra p.asIdeal.ResidueField k := eκ.toRingHom.toAlgebra
      let _ : Algebra p.asIdeal.ResidueField K :=
        ((algebraMap k K).comp (algebraMap p.asIdeal.ResidueField k)).toAlgebra
      let _ : IsScalarTower p.asIdeal.ResidueField k K := IsScalarTower.of_algebraMap_eq' rfl
      let e : p.asIdeal.Fiber K ≃ₐ[p.asIdeal.ResidueField] K :=
        Algebra.field_fiber_algEquiv (k := k) (A := K) p
      exact isNoetherianRing_of_ringEquiv K e.symm.toRingEquiv
    exact
      RingHom.IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers
        (f := algebraMap k K) hcolim hfiber_noetherian

end

end Algebra
