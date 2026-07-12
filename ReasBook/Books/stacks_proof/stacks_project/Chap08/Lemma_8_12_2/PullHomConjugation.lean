import StacksProject_2024.Chap08.Lemma_8_12_2.PullHomConjugationPair

open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology.Cover

universe uC uD uS vC vD vS

namespace CategoryTheory

section

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}
variable (u : C ⥤ D)

/-- Helper for Chap08 Lemma 8 12 2: strictifying target components conjugates source
`pullHom` along a composite restriction to the corresponding target `pullHom`. -/
theorem pullbackProjection_targetRestrictionIso_pullHom_conjugation
    (p : S ⥤ D) [p.IsFibered] {U V W : C}
    (a : V ⟶ U) (k : W ⟶ V) (b : W ⟶ U)
    (hk : k ≫ a = b) (hkTarget : u.map k ≫ u.map a = u.map b)
    (X Y : (CategoricalPullback.π₁ u p).Fiber U)
    (φ :
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
        a.op.toLoc).toFunctor.obj X ⟶
      ((canonicalFiberPseudofunctor (CategoricalPullback.π₁ u p)).map
        a.op.toLoc).toFunctor.obj Y) :
    (pullbackProjection_targetRestrictionIso u p b X).inv ≫
        (pullbackProjection_targetFiberFunctor u p W).map
          (Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ k b b hk hk) ≫
        (pullbackProjection_targetRestrictionIso u p b Y).hom =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        ((pullbackProjection_targetRestrictionIso u p a X).inv ≫
          (pullbackProjection_targetFiberFunctor u p V).map φ ≫
          (pullbackProjection_targetRestrictionIso u p a Y).hom)
        (u.map k) (u.map b) (u.map b) hkTarget hkTarget := by
  exact
    pullbackProjection_targetRestrictionIso_pullHom_conjugation_pair u p a a k b b
      hk hk hkTarget hkTarget X Y φ


end

end CategoryTheory
