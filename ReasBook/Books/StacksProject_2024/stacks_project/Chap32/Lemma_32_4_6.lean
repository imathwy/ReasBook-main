import Mathlib
import StacksProject_2024.stacks_project.Chap32.Lemma_32_4_1
import StacksProject_2024.stacks_project.Chap32.Lemma_32_4_2
import StacksProject_2024.stacks_project.Chap32.Lemma_32_4_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ i, CompactSpace ↥(D.obj i)]
variable [∀ i, QuasiSeparatedSpace ↥(D.obj i)]
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable [∀ {i i' : I} (hii' : i ≤ i'), IsAffineHom (D.map (homOfLE hii'))]

-- Semantic recall: `lean_leansearch` found `specializes_iff_mem_closure` for the topology
-- relation `x ⤳ y`; local Chapter 32 precedent supplies the point-set and topological-space
-- limit statements as Lemma 32.4.1 and Lemma 32.4.2, while Lemma 32.4.4 supplies the closure
-- limit input behind the finite-stage specialization detection.

/-- Lemma 32.4.6 (1): in Situation 32.4.5, the underlying set of
`S = lim_i S_i` is the inverse limit of the underlying sets of the stages. -/
@[stacks 01YY]
theorem bijectiveToUnderlyingSetSections_of_situation_32_4_5 :
    Function.Bijective
      (fun x : c.pt ↦
        (⟨fun i ↦ (c.π.app i) x,
          fun {i j} f ↦ limitPointProjectionCompatible_of_directedAffineTransition D c f x⟩ :
          (D ⋙ Scheme.forget).sections)) := sorry

/-- Lemma 32.4.6 (2): in Situation 32.4.5, the underlying topological space of
`S = lim_i S_i` is the inverse limit of the underlying topological spaces of the stages. -/
@[stacks 01YY]
def isLimit_forgetToTop_mapCone_of_situation_32_4_5 :
    IsLimit (Scheme.forgetToTop.mapCone c) :=
  isLimit_forgetToTop_mapCone_of_directedAffineTransition D c hc

/-- The topological limit witness in Situation 32.4.5 has the expected projection
factorization property. -/
@[stacks 01YY]
theorem isLimit_forgetToTop_mapCone_of_situation_32_4_5_fac
    (s : Cone (D ⋙ Scheme.forgetToTop)) (i : OrderDual I) :
    (isLimit_forgetToTop_mapCone_of_situation_32_4_5 D c hc).lift s ≫
      (Scheme.forgetToTop.mapCone c).π.app i = s.π.app i := sorry

/-- Lemma 32.4.6 (3): in Situation 32.4.5, if `s'` is not a specialization of `s`
in `S = lim_i S_i`, then at some stage the image of `s'` is not a specialization of the image
of `s`. -/
@[stacks 01YY]
theorem exists_stage_not_specializes_of_not_specializes
    (s s' : c.pt) (h : ¬ s ⤳ s') :
    ∃ i : I, ¬ ((c.π.app i) s ⤳ (c.π.app i) s') := sorry

end

end AlgebraicGeometry
