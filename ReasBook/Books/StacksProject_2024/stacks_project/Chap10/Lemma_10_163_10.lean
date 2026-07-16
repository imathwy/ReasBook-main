import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_110_7
import StacksProject_2024.stacks_project.Chap10.Lemma_10_166_4
import StacksProject_2024.stacks_project.Chap15.Lemma_15_42_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Smooth R S] [IsRegularRing R]

/- Domain-style sampling pass:
* primary domain: commutative algebra of smooth algebras, regular ring maps, and regular rings;
* sampled owner declarations:
  `IsRegularRing`,
  `RingHom.IsRegularRingMap`,
  `Algebra.isGeometricallyRegular_of_smooth`,
  `Algebra.isRegularRing_of_regularRingMap`;
* best owner abstraction: the source-facing statement here remains the smooth-specialized ascent
  theorem, but its canonical proof owner is `RingHom.IsRegularRingMap (algebraMap R S)`; smoothness supplies
  the flatness and geometrically regular fibers needed for that owner, and regularity of `S` is
  then derived API from `Algebra.isRegularRing_of_regularRingMap`.

Primitive data vs. derived API:
* primitive public inputs: `[Algebra.Smooth R S]` and `[IsRegularRing R]`;
* derived API: the regular-map owner on `R → S`, obtained by base-changing smoothness to every
  fiber and applying geometric-regularity ascent over the residue fields.

Source/core/bridge triage:
* `source-facing`: `isRegularRing_of_smooth`;
* `core/canonical`: `RingHom.IsRegularRingMap (algebraMap R S)` and `IsRegularRing S`;
* `bridge/view`: `Algebra.Smooth.baseChange` on the fibers and
  `Algebra.isGeometricallyRegular_of_smooth`.
-/
-- Proof sketch: package the smooth map `R → S` as a regular ring map. Flatness is already a
-- canonical consequence of smoothness, and for each prime `p ⊂ R` the fiber `κ(𝔭) ⊗[R] S` is
-- smooth over `κ(𝔭)` by base change, hence geometrically regular over `κ(𝔭)` by Lemma
-- `10.166.4`. The canonical regular-map ascent theorem then yields `IsRegularRing S`.
/-- Lemma 10.163.10: if `R → S` is smooth and `R` is a regular ring, then `S` is a regular ring. -/
theorem isRegularRing_of_smooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Smooth R S] [IsRegularRing R] :
    IsRegularRing S := by
  letI : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let _ : RingHom.IsRegularRingMap (algebraMap R S) := by
    exact
      { toFlat := RingHom.flat_algebraMap_iff.mpr inferInstance
        isGeometricallyRegular_fiber := fun p ↦ by
          letI : Algebra.Smooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := inferInstance
          letI :
              Algebra.IsGeometricallyRegular p.asIdeal.ResidueField p.asIdeal.ResidueField :=
            inferInstance
          infer_instance }
  exact Algebra.isRegularRing_of_regularRingMap R

end
