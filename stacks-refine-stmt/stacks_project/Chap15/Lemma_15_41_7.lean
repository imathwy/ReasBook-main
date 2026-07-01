import stacks_project.Chap10.Lemma_10_39_10
import stacks_project.Chap10.Lemma_10_166_3
import stacks_project.Chap15.Definition_15_41_1

-- Declarations for this item will be appended below by the statement pipeline.

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
