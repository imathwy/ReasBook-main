import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Module.Injective
import Mathlib.Tactic.TFAE
import StacksProject_2024.Chap12.Lemma_12_27_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Abelian
open CategoryTheory.Abelian.Ext
open Module
open ModuleCat
open ShortComplex

universe u

namespace CategoryTheory

attribute [local instance] CategoryTheory.HasExt.standard

section

variable (R : Type u) [Ring R]
variable (J : ModuleCat.{u} R)

-- Domain-style sampling:
-- * primary domain: injective `R`-modules, Baer's criterion, and degree-one `Ext` in `ModuleCat R`.
-- * inspected owner declarations: `CategoryTheory.injective_iff_ext_one_eq_zero`,
--   `Module.Baer.iff_injective`, and
--   `Ext.contravariant_sequence_exact₁`.
-- * best owner abstraction: the canonical owners are `Injective J` on `ModuleCat R`,
--   `Module.Baer R J`, and the `Ext` connecting morphism attached to the quotient short exact
--   sequence; the local file should specialize those owners directly rather than introduce a
--   parallel quotient-module or connecting-map wrapper.
-- * owner choice: the `Ext¹`-vanishing criterion is already owned by the chapter-12 theorem
--   `CategoryTheory.injective_iff_ext_one_eq_zero`, whose implicit source object specializes
--   directly to `ModuleCat R`; this file should use that owner rather than the local
--   module-category wrapper from the same chapter.
-- * layer: `source-facing`; the lemma is the ideal-quotient specialization of the general
--   injective-via-`Ext` criterion, compared with the source's Baer condition.
-- * primitive data: the ring `R`, the module object `J : ModuleCat R`, and an ideal `I : Ideal R`.
-- * bridge/view: the source quotient `R ⧸ I` and its short exact sequence
--   `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0` are already canonical in `ModuleCat R`, built from `I.mkQ` and
--   `LinearMap.exact_subtype_mkQ I`, so the proof should use that owner directly rather than
--   introduce a parallel local short-complex wrapper.
-- * derived API: the degree-one group `Ext (ModuleCat.of R (R ⧸ I)) J 1` and the connecting map
--   from `Hom_R(I, J)`, with the degree-zero comparison handled by the primitive owner
--   `Ext.mk₀`/`Ext.homEquiv₀` rather than the linearized wrapper API.

/-- Lemma 15.55.4: for an `R`-module `J`, the following are equivalent: `J` is injective,
`Ext^1_R(R/I, J)` is trivial for every ideal `I ⊆ R`, and every `R`-linear map `I → J` extends to
an `R`-linear map `R → J` (equivalently, `J` satisfies Baer's criterion). -/
-- Proof sketch: `(1) ↔ (3)` is Baer's criterion via
-- `Module.Baer.iff_injective` and `Module.injective_iff_injective_object`. For `(1) → (2)`,
-- apply the owner theorem `CategoryTheory.injective_iff_ext_one_eq_zero`.
-- For `(2) → (3)`,
-- apply the contravariant long exact `Ext` sequence to the canonical quotient short exact sequence
-- `0 ⟶ I ⟶ R ⟶ R ⧸ I ⟶ 0`: if `Ext¹_R(R/I, J) = 0`, then every class in
-- `Ext⁰_R(I, J) = Hom_R(I, J)` lies in the image of `Hom_R(R, J)`.
theorem injective_tfae_extOneFromIdealQuotient_eq_zero_baer :
    List.TFAE
      [ Injective J
      , ∀ I : Ideal R, ∀ e : Ext (ModuleCat.of R (R ⧸ I)) J 1, e = 0
      , Module.Baer R J
      ] := by
  tfae_have 1 ↔ 3 := by
    simpa [Module.injective_iff_injective_object R J] using
      (show Module.Injective R J ↔ Module.Baer R J from Baer.iff_injective.symm)
  tfae_have 1 → 2 := by
    intro hJ I e
    exact ((injective_iff_ext_one_eq_zero J).1 hJ) e
  tfae_have 2 → 3 := by
    intro hExt I g
    let S :=
      moduleCatMk I.subtype I.mkQ
        (LinearMap.exact_subtype_mkQ I).linearMap_comp_eq_zero
    have hS : S.ShortExact := by
      refine ModuleCat.shortComplex_shortExact S ?_ ?_ ?_
      · simpa [S] using LinearMap.exact_subtype_mkQ I
      · exact Subtype.coe_injective
      · simpa [S] using I.mkQ_surjective
    let gHom : S.X₁ ⟶ J := by
      simpa [S] using (ModuleCat.ofHom g)
    let gExt : Ext S.X₁ J 0 := Ext.mk₀ gHom
    have hgExt : hS.extClass.comp gExt (show 1 + 0 = 1 by simp) = 0 := hExt I _
    obtain ⟨g'Ext, hg'Ext⟩ := contravariant_sequence_exact₁ hS J gExt (by simp) hgExt
    obtain ⟨g'Hom, rfl⟩ := homEquiv₀.symm.surjective g'Ext
    have hg'Hom : S.f ≫ g'Hom = gHom := by
      apply homEquiv₀.symm.injective
      simpa [Ext.homEquiv₀_symm_apply, gExt, Ext.mk₀_comp_mk₀] using hg'Ext
    let g' : ModuleCat.of R R ⟶ J := by
      simpa [S] using g'Hom
    have hg' : g'.hom.comp I.subtype = g := by
      exact ModuleCat.hom_ext_iff.mp <| by
        simpa [S, g'] using hg'Hom
    refine ⟨g'.hom, ?_⟩
    intro x hx
    simpa using LinearMap.congr_fun hg' ⟨x, hx⟩
  tfae_finish

end

end CategoryTheory
