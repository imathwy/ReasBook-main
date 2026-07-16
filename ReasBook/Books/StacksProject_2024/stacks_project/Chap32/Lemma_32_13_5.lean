import StacksProject_2024.stacks_project.Chap29.Definition_29_5_5
import StacksProject_2024.stacks_project.Chap32.Lemma_32_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: the semantic-search MCP tool was unavailable in this environment. Local
-- Chapter 29 support precedent fixes the literal scheme-theoretic support owner as
-- `Scheme.Modules.IsSchemeTheoreticSupport`, and local Chapter 32 precedent represents
-- Situation 32.8.1 base changes by `pullback.snd f0 (pullback.fst y0 ...)`.

/-- Pullback of a finite-type scheme module is finite type, used only to elaborate
`IsSchemeTheoreticSupport` for the base-changed modules below. -/
local instance instSchemeModulePullbackIsFiniteType
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsFiniteType] :
    ((Scheme.Modules.pullback f).obj F).IsFiniteType := sorry

/-- Pullback of a quasi-coherent scheme module is quasi-coherent, used only to elaborate
`IsSchemeTheoreticSupport` for the base-changed modules below. -/
local instance instSchemeModulePullbackIsQuasicoherent
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj F).IsQuasicoherent := sorry

/-- Lemma 32.13.5: in the notation and assumptions of Situation 32.8.1, let `F0` be a
finite-type quasi-coherent `𝒪_X0`-module and let its pullbacks to the limit base change and to
the stage base changes be denoted by `F` and `F_i`. If `f0` is locally of finite type and a
scheme-theoretic support of `F` is proper over the limit `Y`, then for some stage `i >= i0` a
scheme-theoretic support of `F_i` is proper over `Y_i`. -/
@[stacks 081G]
theorem exists_isProper_schemeTheoreticSupport_stagePullback_of_isProper_limitPullback
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i0 : I)
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (X0 Y0 : Scheme.{u}) (x0 : X0 ⟶ D.obj i0) (y0 : Y0 ⟶ D.obj i0)
    (f0 : X0 ⟶ Y0) (hf0 : f0 ≫ y0 = x0)
    [CompactSpace (D.obj i0)] [QuasiSeparatedSpace (D.obj i0)]
    [CompactSpace X0] [QuasiSeparatedSpace X0]
    [CompactSpace Y0] [QuasiSeparatedSpace Y0]
    (F0 : X0.Modules) [F0.IsQuasicoherent] [F0.IsFiniteType]
    (hft : LocallyOfFiniteType f0)
    (Z : (pullback f0 (pullback.fst y0 (c.π.app i0))).IdealSheafData)
    (hZ : Scheme.Modules.IsSchemeTheoreticSupport
      ((Scheme.Modules.pullback (pullback.fst f0 (pullback.fst y0 (c.π.app i0)))).obj F0) Z)
    (hZproper : IsProper (Z.subschemeι ≫
      pullback.snd f0 (pullback.fst y0 (c.π.app i0)))) :
    ∃ (i : I) (hi0i : i0 ≤ i),
      ∃ Zi : (pullback f0 (pullback.fst y0 (D.map (homOfLE hi0i)))).IdealSheafData,
        Scheme.Modules.IsSchemeTheoreticSupport
          ((Scheme.Modules.pullback
            (pullback.fst f0 (pullback.fst y0 (D.map (homOfLE hi0i))))).obj F0) Zi ∧
        IsProper (Zi.subschemeι ≫
          pullback.snd f0 (pullback.fst y0 (D.map (homOfLE hi0i)))) := sorry

end AlgebraicGeometry
