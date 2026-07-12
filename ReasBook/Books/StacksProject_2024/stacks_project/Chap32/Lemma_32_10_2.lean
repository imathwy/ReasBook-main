import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical sheaf-module owner
-- `SheafOfModules.IsFinitePresentation`. Local Chapter 32 precedent represents directed inverse
-- limits of schemes by `D : OrderDual I ⥤ Scheme`, a cone `c`, and `hc : IsLimit c`, and uses
-- `Scheme.Modules.pullback` for inverse image of `\mathcal O`-modules.

/-- Lemma 32.10.2 (1): let `S = lim_i S_i` be a directed inverse limit of quasi-compact
quasi-separated schemes with affine transition morphisms. Every finitely presented
`\mathcal O_S`-module descends, after passing to some stage `i`, to a finitely presented
`\mathcal O_{S_i}`-module whose pullback along `S ⟶ S_i` is isomorphic to the original module. -/
@[stacks 01ZR]
theorem exists_finitePresentation_module_stage_of_limit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (ℱ : c.pt.Modules) [ℱ.IsFinitePresentation] :
    ∃ (i : I) (ℱi : (D.obj i).Modules),
      ℱi.IsFinitePresentation ∧
        Nonempty ((Scheme.Modules.pullback (c.π.app i)).obj ℱi ≅ ℱ) := sorry

/-- Lemma 32.10.2 (2): in the same directed inverse-limit setup, a morphism over `S`
between the pullbacks of two finitely presented modules from a stage `S_i` descends, after
passing to some later stage `i' >= i`, to a morphism between the corresponding pullbacks to
`S_{i'}`. The equality compares the two pullback descriptions over `S` through the canonical
pullback-composition isomorphism and the cone relation
`S ⟶ S_i = (S ⟶ S_i') ≫ (S_i' ⟶ S_i)`. -/
@[stacks 01ZR]
theorem exists_ge_module_morphism_stageBaseChange_of_limitBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (ℱi 𝒢i : (D.obj i).Modules)
    [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
    (φ : (Scheme.Modules.pullback (c.π.app i)).obj ℱi ⟶
      (Scheme.Modules.pullback (c.π.app i)).obj 𝒢i) :
    ∃ (i' : I) (hii' : i ≤ i')
      (hcomp : c.π.app i' ≫ D.map (homOfLE hii') = c.π.app i)
      (φi' : (Scheme.Modules.pullback (D.map (homOfLE hii'))).obj ℱi ⟶
        (Scheme.Modules.pullback (D.map (homOfLE hii'))).obj 𝒢i),
      (Scheme.Modules.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).inv.app ℱi ≫
          (Scheme.Modules.pullback (c.π.app i')).map φi' ≫
        (Scheme.Modules.pullbackComp (c.π.app i') (D.map (homOfLE hii'))).hom.app 𝒢i =
        (Scheme.Modules.pullbackCongr hcomp).hom.app ℱi ≫ φ ≫
          (Scheme.Modules.pullbackCongr hcomp).inv.app 𝒢i := sorry

/-- Lemma 32.10.2 (3): in the same directed inverse-limit setup, if two morphisms between
finitely presented modules on a stage `S_i` become equal after pullback to the limit scheme `S`,
then after passing to some later stage `i' >= i` their pullbacks to `S_{i'}` are already equal. -/
@[stacks 01ZR]
theorem exists_ge_module_eq_stageBaseChange_of_eq_limitBaseChange
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i : I) (ℱi 𝒢i : (D.obj i).Modules)
    [ℱi.IsFinitePresentation] [𝒢i.IsFinitePresentation]
    (φ ψ : ℱi ⟶ 𝒢i)
    (hφψ : (Scheme.Modules.pullback (c.π.app i)).map φ =
      (Scheme.Modules.pullback (c.π.app i)).map ψ) :
    ∃ (i' : I) (hii' : i ≤ i'),
      (Scheme.Modules.pullback (D.map (homOfLE hii'))).map φ =
        (Scheme.Modules.pullback (D.map (homOfLE hii'))).map ψ := sorry

end AlgebraicGeometry
