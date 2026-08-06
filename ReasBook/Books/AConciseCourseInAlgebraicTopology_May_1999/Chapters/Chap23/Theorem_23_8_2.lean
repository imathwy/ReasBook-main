import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_8_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_7_1

noncomputable section

open scoped Topology

universe u v

-- The canonical Chapter 23 owner for principal `G`-bundles, their isomorphism classes, and
-- pullback is `Theorem_23_7_1`; this file only adds the universal-bundle classifying map and the
-- source-facing statements of Theorem 23.8.2.

section UniversalPrincipalBundle

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {Y : Type v} [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- The classifying assignment `[B, Y /[G]] → PG(B)` induced by the universal principal bundle
`Y → Y /[G]`. -/
def universalPrincipalBundleClassifyingMap
    (hY : IsPrincipalBundleMap G (Quotient.mk'' : Y → Y /[G]))
    (B : Type v) [TopologicalSpace B] :
    continuousMapHomotopyClasses B (Y /[G]) → PrincipalGBundle.classes G B :=
  PrincipalGBundle.pullbackOnHomotopyClasses
    (Quotient.mk'' : Y → Y /[G])

/-- Evaluating the universal classifying map on a representative `f : C(B, Y /[G])` yields the
class of the pullback bundle `f^*Y`. -/
@[simp] theorem universalPrincipalBundleClassifyingMap_mk
    (hY : IsPrincipalBundleMap G (Quotient.mk'' : Y → Y /[G]))
    {B : Type v} [TopologicalSpace B] (f : C(B, Y /[G])) :
    universalPrincipalBundleClassifyingMap hY B ⟦f⟧ =
      PrincipalGBundle.classOf ((orbitPrincipalGBundle hY).pullback f) := by
  exact PrincipalGBundle.pullbackOnHomotopyClasses_mk
    (Quotient.mk'' : Y → Y /[G]) f

/-- Theorem 23.8.2 (1): for the universal principal bundle `Y → Y /[G]`, the classification map
`[B, Y /[G]] → PG(B)` given by `f ↦ f^*Y` is natural with respect to pullback along maps of
bases. -/
theorem universalPrincipalBundleClassifyingMap_natural
    (hY : IsPrincipalBundleMap G (Quotient.mk'' : Y → Y /[G]))
    {B : Type v} [TopologicalSpace B] {B' : Type v} [TopologicalSpace B'] (g : C(B', B)) :
    (PrincipalGBundle.pullbackOnClasses g :
      PrincipalGBundle.classes G B → PrincipalGBundle.classes G B') ∘
      universalPrincipalBundleClassifyingMap hY B =
    universalPrincipalBundleClassifyingMap hY B' ∘
      continuousMapHomotopyClassesPrecompose g := by
  funext c
  refine Quotient.inductionOn c ?_
  intro f
  rcases PrincipalGBundle.pullbackIso_comp (orbitPrincipalGBundle hY) f g with ⟨e⟩
  simp only [Function.comp_apply, universalPrincipalBundleClassifyingMap_mk,
    PrincipalGBundle.pullbackOnClasses_classOf]
  exact PrincipalGBundle.classOf_eq_of_iso e

/-- Companion to Theorem 23.8.2 (1): iterated pullback of the universal principal bundle is
isomorphic to pullback along the composite map. -/
theorem universalPrincipalBundle_pullbackIso_comp
    (hY : IsPrincipalBundleMap G (Quotient.mk'' : Y → Y /[G]))
    {B : Type v} [TopologicalSpace B] {B' : Type v} [TopologicalSpace B']
    (f : C(B, Y /[G])) (g : C(B', B)) :
    Nonempty
      (PrincipalGBundle.Iso
        (((orbitPrincipalGBundle hY).pullback f).pullback g)
        ((orbitPrincipalGBundle hY).pullback (f.comp g))) :=
  PrincipalGBundle.pullbackIso_comp (orbitPrincipalGBundle hY) f g

/-- Theorem 23.8.2 (2): if `Y` is contractible and `Y → Y /[G]` is a principal `G`-bundle, then
the assignment `f ↦ f^*Y` induces a bijection `[B, Y /[G]] → PG(B)`. -/
theorem universalPrincipalBundle_classifying_bijective
    [ContractibleSpace Y] {B : Type v} [TopologicalSpace B]
    (hY : IsPrincipalBundleMap G (Quotient.mk'' : Y → Y /[G])) :
    Function.Bijective (universalPrincipalBundleClassifyingMap hY B) := sorry

end UniversalPrincipalBundle
