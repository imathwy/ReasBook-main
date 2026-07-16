import Mathlib
import StacksProject_2024.stacks_project.Chap28.Definition_28_26_1
import StacksProject_2024.stacks_project.Chap32.Situation_32_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

section

/- Semantic recall: `lean_leansearch` found the canonical scheme-module pullback API
`Scheme.Modules.pullback`; the local Chapter 28 owner for ampleness is
`Scheme.Modules.IsAmple`, with explicit invertible-module interfaces for pullbacks. -/

/-- Lemma 32.4.15: in Situation 32.4.5, let `\mathcal L_0` be an invertible sheaf of
modules on the distinguished stage `S_0`. If its pullback to the limit scheme `S` is ample, then
after passing to some stage `S_i` over `S_0`, the pullback `\mathcal L_i` is ample. -/
@[stacks 09MT]
theorem exists_stage_isAmple_pullback_of_isAmple_limit_pullback
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace ↥(D.obj j)]
    [∀ j, QuasiSeparatedSpace ↥(D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
    (i₀ : I) (ℒ₀ : (D.obj i₀).Modules) [Scheme.Modules.Invertible ℒ₀]
    [hℒ : Scheme.Modules.Invertible ((Scheme.Modules.pullback (c.π.app i₀)).obj ℒ₀)]
    [@Scheme.Modules.IsAmple c.pt ((Scheme.Modules.pullback (c.π.app i₀)).obj ℒ₀) hℒ] :
    ∃ (i : I) (hi : i₀ ≤ i),
      ∃ hℒi : Scheme.Modules.Invertible
          ((Scheme.Modules.pullback (D.map (homOfLE hi))).obj ℒ₀),
        @Scheme.Modules.IsAmple (D.obj i)
          ((Scheme.Modules.pullback (D.map (homOfLE hi))).obj ℒ₀) hℒi := sorry

end

end AlgebraicGeometry
