import Mathlib
import Mathlib.Data.List.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_41_1 (from Chap15) -/
namespace Algebra

universe u v

/-- Definition 15.41.1: a ring map `R → S` is regular if it is flat and for every prime
`p ⊂ R` the fiber ring `p.asIdeal.Fiber S = S ⊗[R] κ(p)` is geometrically regular over the
residue field `κ(p)`. In this project, `IsGeometricallyRegular` already packages the
Noetherianity required in the textbook definition of the fibers. -/
class IsRegularRingMap (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    Prop extends Module.Flat R S where
  /-- Every fiber ring of a regular ring map is geometrically regular over the corresponding
  residue field. -/
  isGeometricallyRegular_fiber :
    ∀ p : PrimeSpectrum R, IsGeometricallyRegular p.asIdeal.ResidueField (p.asIdeal.Fiber S)

section

variable (R : Type u) [CommRing R]

-- Proof sketch: the identity map is flat, and for each prime `p` the fiber of `R → R` over `p`
-- identifies with the residue field `κ(p)`, which is geometrically regular over itself by the
-- canonical field instance from `Lemma 10.166.5`.
/-- The identity map of a commutative ring is a regular ring map. -/
instance : IsRegularRingMap R R := sorry

end

end Algebra

/-! ### Lemma_15_41_2_Regular_is_a_local_property (from Chap15) -/
namespace RingHom.IsRegularRingMap

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {f : R →+* S} [IsNoetherianRing S]

def AtPrimes (f : R →+* S) : Prop :=
  ∀ q : PrimeSpectrum S,
    (Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl).IsRegularRingMap

def AtMaximals (f : R →+* S) : Prop :=
  ∀ m : MaximalSpectrum S,
    Ideal.IsMaximal (m.asIdeal.comap f) →
      (Localization.localRingHom (m.asIdeal.comap f) m.asIdeal f rfl).IsRegularRingMap

/- Domain sampling pass:
* primary domain: regular ring maps and their local-fiber behavior in commutative algebra;
* sampled owner declarations:
  - `RingHom.IsRegularRingMap f` from `Definition_15_41_1`, the source-facing owner for
    regularity of the ring hom `f`;
  - `Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl`, the canonical owner for the
    induced map `R_(q ∩ R) → S_q`;
  - `flat_iff_flat_localizedModule_atPrime_over_under` from `Lemma_10_39_18`, the canonical
    prime-local flatness criterion for a ring hom after viewing `S` as an `R`-algebra through `f`;
  - `flat_iff_flat_localizedModule_atMaximal_over_under` from `Lemma_10_39_18`, the corresponding
    maximal-local flatness criterion;
  - `IsGeometricallyRegular k A` from `Definition_10_166_2`, the canonical owner for
    geometric regularity of a field algebra.

Source/core/bridge triage:
* `source-facing`: `isRegularRingMap_local_tfae`, the textbook local-property statement for the
  ring map `f`;
* `core/canonical`: `RingHom.IsRegularRingMap f`;
* `bridge/view`: the canonical localized ring hom
  `Localization.localRingHom (q.asIdeal.comap f) q.asIdeal f rfl`, together with the corresponding
  prime-local and maximal-local clauses `AtPrimes f` and `AtMaximals f`.

Primitive data already belong to the owner abstractions `RingHom.IsRegularRingMap f` and
`IsGeometricallyRegular`. This file should therefore keep only the source-facing `TFAE` on the
regular-map owner itself, without a parallel algebra-only wrapper or private clause packaging.
-/

-- Proof sketch: clause `(1)` localizes to clause `(2)`. Conversely, recover flatness of `f`
-- from `flat_iff_flat_localizedModule_atPrime_over_under`, and recover the fiberwise
-- geometric-regularity clause of `RingHom.IsRegularRingMap f` by checking it on all prime
-- localizations of the Noetherian fiber rings. Clause `(3)` is the maximal-ideal version of the
-- same local test, using `flat_iff_flat_localizedModule_atMaximal_over_under` for the flatness
-- part.
/-- Lemma 15.41.2 (Regular is a local property): for a ring map `f : R →+* S` with `S`
Noetherian, the following are equivalent: `f` is regular; for every prime ideal `q ⊂ S`, the
localized map `R_(q ∩ R) → S_q` is regular; and for every maximal ideal `m ⊂ S` whose contraction
to `R` is maximal, the localized map `R_(m ∩ R) → S_m` is regular. -/
theorem isRegularRingMap_local_tfae :
    ([ f.IsRegularRingMap, AtPrimes f, AtMaximals f ] : List Prop).TFAE := sorry

end

end RingHom.IsRegularRingMap

/-! ### Lemma_15_41_3_Regular_maps_and_base_change (from Chap15) -/
open scoped TensorProduct

namespace RingHom.IsRegularRingMap

universe u v w

section

variable {R : Type u} {R' : Type v} {Λ : Type w}
variable [CommRing R] [CommRing R'] [CommRing Λ]
variable [Algebra R Λ] [Algebra R R']
variable [Algebra.EssFiniteType R R']

/- Domain triage:
- primary domain: regular ring maps and tensor-product base change in commutative algebra;
- sampled owner declarations of the same kind:
  `RingHom.IsRegularRingMap`,
  `Algebra.IsGeometricallyRegular`,
  `Algebra.EssFiniteType`;
- best owner abstraction: the regularity datum already lives on the ring hom
  `algebraMap R Λ : R →+* Λ`, so the source-facing tensor-product statement should be exposed as a
  theorem in the owner namespace `RingHom.IsRegularRingMap` rather than through a parallel
  algebra-only wrapper namespace;
- primitive data: the algebra structures `R → Λ` and `R → R'`, together with
  `[Algebra.EssFiniteType R R']` and a proof `h : (algebraMap R Λ).IsRegularRingMap`;
- derived API: the regularity of the canonical base-change map
  `(algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap`, exposed by the exact owner theorem below with
  its essentially-finite-type hypothesis kept visible on the theorem surface.

Layering:
- `baseChange_of_essFiniteType` is `source-facing`;
- the core/canonical owner is `RingHom.IsRegularRingMap`;
- there is no additional bridge/view layer beyond the canonical tensor-product base change.
-/

-- Proof sketch: flatness is preserved by tensor base change along `R → R'`. For each prime
-- `p' : Spec R'`, compare the fiber of `R' → R' ⊗[R] Λ` over `p'` with the base change of the
-- fiber of `R → Λ` over the image prime in `R`, then use geometric regularity of fibers together
-- with the essentially-finite-type hypothesis on `R → R'`.
/-- Lemma 15.41.3 (Regular maps and base change): the base change of a regular ring map along a
essentially finite type ring map is again a regular ring map. -/
theorem baseChange_of_essFiniteType (h : (algebraMap R Λ).IsRegularRingMap) :
    (algebraMap R' (R' ⊗[R] Λ)).IsRegularRingMap := sorry

end

end RingHom.IsRegularRingMap

/-! ### Lemma_15_41_4_Composition_of_regular_maps (from Chap15) -/
namespace RingHom.IsRegularRingMap

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable {f : A →+* B} {g : B →+* C}

/- Domain triage:
- primary domain: regular ring maps and composition through fiberwise geometric regularity in
  commutative algebra;
- sampled owner declarations of the same kind:
  `IsRegularRingMap`,
  `IsGeometricallyRegular`,
  `baseChange_of_essFiniteType`,
  `isRegularLocalRing_of_flat_localHom_of_regular_closedFiber`;
- best owner abstraction: `IsRegularRingMap` on composable ring homomorphisms
  `f : A →+* B` and `g : B →+* C`, with `IsGeometricallyRegular` supplying the canonical owner on
  each fiber over a residue field;
- primitive data: the ring homs `f` and `g`, regularity of `f` and `g`, and the Noetherianity
  hypothesis on the fibers `p.asIdeal.Fiber C` of the composite `g.comp f`;
- derived API: field-valued base change of regular maps and the local regularity criterion for flat
  local maps with regular closed fiber.

Layering:
- `comp_of_noetherianFibers` is `source-facing`;
- the core/canonical owners are `IsRegularRingMap` and `IsGeometricallyRegular`;
- the Noetherian-fiber hypothesis is auxiliary input, not a new owner-level wrapper.
-/

-- Proof sketch: for each prime `p : PrimeSpectrum A` and each finite purely inseparable extension
-- `κ(p) ⊂ k`, base change along `A → k` using
-- `baseChange_of_essFiniteType` to reduce to the case where the
-- source is the field `k`. Then `k ⊗[A] B` is regular because `A → B` is regular, and
-- `k ⊗[A] C` is Noetherian by the fiber hypothesis. The induced map `k ⊗[A] B → k ⊗[A] C` is
-- regular because `B → C` is regular, so Lemma `10.112.8` upgrades regularity of the source and
-- of the fibers to regularity of `k ⊗[A] C`, which is exactly the geometric regularity needed for
-- `A → C`.
/-- Lemma 15.41.4 (Composition of regular maps): let `f : A →+* B` and `g : B →+* C` be regular
ring maps. If every fiber ring `p.asIdeal.Fiber C = C ⊗[A] κ(p)` of `g.comp f : A →+* C` is
Noetherian, then `g.comp f` is a regular ring map. -/
theorem comp_of_noetherianFibers (hf : f.IsRegularRingMap) (hg : g.IsRegularRingMap)
    (hfiber_noetherian :
      let _ : Algebra A C := (g.comp f).toAlgebra
      ∀ p : PrimeSpectrum A, IsNoetherianRing (p.asIdeal.Fiber C)) :
    (g.comp f).IsRegularRingMap := by
  let _ : Algebra A B := f.toAlgebra
  let _ : Algebra B C := g.toAlgebra
  let _ : Algebra A C := (g.comp f).toAlgebra
  sorry

end

end RingHom.IsRegularRingMap

/-! ### Lemma_15_41_5 (from Chap15) -/
universe u v

namespace RingHom

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S]
variable {f : R →+* S}

/- Domain sampling pass:
* primary domain: regular ring maps and filtered colimits of smooth commutative algebras;
* sampled owner declarations:
  - `RingHom.IsFilteredColimitOfSmooth` from `Lemma_10_147_5`, the source-facing owner for the
    intrinsic hypothesis that a ring map `R →+* S` is a filtered colimit of smooth `R`-algebras;
  - `RingHom.IsRegularRingMap` from `Definition_15_41_1`, the source-facing owner for regularity;
  - `Algebra.isGeometricallyRegular_of_smooth` from `Lemma_10_166_4`, the canonical smooth-to-
    geometric-regularity owner used on field-valued fibers;
  - the inherited `RingHom.Flat` data inside `RingHom.IsRegularRingMap` from
    `Definition_15_41_1`, showing that flatness is primitive owner data rather than a separate
    local wrapper.

Source/core/bridge triage:
* `source-facing`: `isRegularRingMap_of_noetherianFibers`;
* `core/canonical`: `RingHom.IsFilteredColimitOfSmooth` together with
  `RingHom.IsRegularRingMap`, both owned by the ring hom `f`;
* `bridge/view`: any chosen directed-system presentation of the codomain of `f`, together with
  the hidden same-universe presentation inside `RingHom.IsFilteredColimitOfSmooth`.

Primitive data for the hypothesis are only that the ring map `f` is a filtered colimit of smooth
`R`-algebras. A chosen indexing type, stage family, and direct-limit model are auxiliary
presentation data already packaged by `RingHom.IsFilteredColimitOfSmooth`, so they should not
remain the main public API here.
-/

-- Proof sketch: choose a filtered diagram of smooth `R`-algebras presenting `f`. Lemma `10.39.3`
-- gives flatness of `f`. For a prime `p ⊂ R` and a finite purely inseparable extension
-- `κ(p) ⊂ k`, Lemma `10.137.3` identifies `k ⊗[R] S` with the filtered colimit of the corresponding
-- smooth `k`-algebras, hence of regular local rings by Lemma `10.140.3`; the Noetherianity
-- hypothesis on the fibers then lets Lemma `10.106.8` promote those colimit local rings to
-- regular ones, giving geometric regularity of every fiber and therefore regularity of `f`.
/-- Lemma 15.41.5: if a ring map `f : R →+* S` is a filtered colimit of smooth `R`-algebras and
every fiber ring `p.asIdeal.Fiber S = κ(p) ⊗[R] S` is Noetherian, then `f` is regular. -/
theorem IsFilteredColimitOfSmooth.isRegularRingMap_of_noetherianFibers
    (hcolim : f.IsFilteredColimitOfSmooth)
    (hfiber_noetherian :
      let _ : Algebra R S := f.toAlgebra
      ∀ p : PrimeSpectrum R, IsNoetherianRing (p.asIdeal.Fiber S)) :
    f.IsRegularRingMap := by
  let _ : Algebra R S := f.toAlgebra
  sorry

end

end RingHom

/-! ### Lemma_15_41_6 (from Chap15) -/
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

/-! ### Lemma_15_41_7 (from Chap15) -/
namespace RingHom.IsRegularRingMap

universe u v w

section

variable {A : Type u} {B : Type v} {C : Type w}
variable [CommRing A] [CommRing B] [CommRing C]
variable {f : A →+* B} {g : B →+* C}

/- Domain triage:
- primary domain: regular ring maps and faithfully flat descent of fiberwise geometric regularity
  in commutative algebra;
- sampled owner declarations of the same kind:
  `IsRegularRingMap`,
  `RingHom.FaithfullyFlat`,
  `RingHom.IsRegularRingMap.comp_of_noetherianFibers`,
  `RingHom.faithfullyFlat_algebraMap_iff`,
  `isGeometricallyRegular_of_faithfullyFlat`;
- best owner abstraction: the source-facing theorem should be stated for explicit composable ring
  homomorphisms `f : A →+* B` and `g : B →+* C`, with `IsRegularRingMap` and
  `RingHom.FaithfullyFlat` as the canonical owners on those morphisms;
- primitive data: the composable maps `f` and `g`, regularity of `g.comp f`, and faithful
  flatness of `g`;
- derived API: the `algebraMap`/tower specialization is only a bridge/view of this owner-level
  theorem, and the algebra/module faithful-flat bridge `faithfullyFlat_algebraMap_iff` remains
  auxiliary.

Layering:
- `of_comp_of_faithfullyFlat` is `source-facing`;
- the core/canonical owners are `IsRegularRingMap` and `RingHom.FaithfullyFlat`;
- the `algebraMap`/tower specialization and the module-faithful-flat bridge are `bridge/view`
  only.
-/

-- Proof sketch: first use Lemma `10.39.10` together with faithful flatness of `g` to descend
-- flatness from `g.comp f` to `f`. For each `p : Spec A`, base change `g` to `κ(p)`; the induced
-- map on the fibers of `f` and `g.comp f` stays faithfully flat. Since the fiber of `g.comp f`
-- over `p` is geometrically regular, Lemma `10.166.3` descends geometric regularity to the fiber
-- of `f` over `p`.
/-- Lemma 15.41.7: if `g.comp f : A →+* C` is a regular ring map and `g : B →+* C` is faithfully
flat, then `f : A →+* B` is a regular ring map. -/
theorem of_comp_of_faithfullyFlat (hgf : (g.comp f).IsRegularRingMap) (hg : g.FaithfullyFlat) :
    f.IsRegularRingMap := by
  sorry

end

end RingHom.IsRegularRingMap
