import Mathlib
import StacksProject_2024.Chap29.Definition_29_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` found the scheme-side finite-presentation owner
-- `AlgebraicGeometry.LocallyOfFinitePresentation`; local Section 29.21 provides the
-- source-facing morphism class `Scheme.Hom.FinitePresentation`. Local Chapter 32 precedent
-- represents directed inverse limits of schemes by `D : OrderDual I ⥤ Scheme`, a cone `c`,
-- and a proof `hc : IsLimit c`, with stage base change expressed by `Over.pullback`.

/-- Lemma 32.10.1 (1): let `S = lim_i S_i` be a directed inverse limit of quasi-compact
quasi-separated schemes with affine transition morphisms. Every finitely presented scheme over
`S` descends, after passing to some stage `i`, to a finitely presented scheme over `S_i`;
the original object is isomorphic over `S` to the base change of that stage object. -/
@[stacks 01ZM]
theorem exists_finitePresentation_stage_of_finitePresentation_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X : Over c.pt) (hX : Scheme.Hom.FinitePresentation X.hom) :
    ∃ (i : I) (Xi : Over (D.obj i)),
      Scheme.Hom.FinitePresentation Xi.hom ∧
        Nonempty ((Over.pullback (c.π.app i)).obj Xi ≅ X) := sorry

/-- Lemma 32.10.1 (2): in the same directed inverse-limit setup, a morphism over `S`
between the base changes of two finitely presented stage objects descends, after passing to
some later stage `i' ≥ i`, to a morphism between the corresponding stagewise base changes.
The equality in the conclusion compares the two base-change descriptions over `S` using the
canonical pullback-composition isomorphism and the cone relation
`S ⟶ S_i = (S ⟶ S_i') ≫ (S_i' ⟶ S_i)`. -/
@[stacks 01ZM]
theorem exists_ge_morphism_stageBaseChange_of_limitBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (Xi Yi : Over (D.obj i))
    (hXi : Scheme.Hom.FinitePresentation Xi.hom)
    (hYi : Scheme.Hom.FinitePresentation Yi.hom)
    (φ : (Over.pullback (c.π.app i)).obj Xi ⟶ (Over.pullback (c.π.app i)).obj Yi) :
    ∃ (i' : I) (hii' : i ≤ i')
      (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
      (φi' : (Over.pullback (D.map (homOfLE hii'))).obj Xi ⟶
        (Over.pullback (D.map (homOfLE hii'))).obj Yi),
      (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app Xi ≫
          (Over.pullback (c.π.app i')).map φi' ≫
        (Over.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app Yi =
        eqToHom (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Xi)
          (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
            (c.π.app i) hcomp)) ≫
          φ ≫
        eqToHom (Eq.symm (congrArg (fun F : Over (D.obj i) ⥤ Over c.pt ↦ F.obj Yi)
          (Over.pullback.congr_simp (c.π.app i' ≫ D.map (homOfLE hii'))
            (c.π.app i) hcomp))) := sorry

/-- Lemma 32.10.1 (3): in the same directed inverse-limit setup, if two morphisms between
finitely presented stage objects become equal after base change to `S`, then after passing to
some later stage `i' ≥ i` their base changes to `S_i'` are already equal. -/
@[stacks 01ZM]
theorem exists_ge_eq_stageBaseChange_of_eq_limitBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (Xi Yi : Over (D.obj i))
    (hXi : Scheme.Hom.FinitePresentation Xi.hom)
    (hYi : Scheme.Hom.FinitePresentation Yi.hom)
    (φ ψ : Xi ⟶ Yi)
    (hφψ : (Over.pullback (c.π.app i)).map φ =
      (Over.pullback (c.π.app i)).map ψ) :
    ∃ (i' : I) (hii' : i ≤ i'),
      (Over.pullback (D.map (homOfLE hii'))).map φ =
        (Over.pullback (D.map (homOfLE hii'))).map ψ := sorry

end AlgebraicGeometry
