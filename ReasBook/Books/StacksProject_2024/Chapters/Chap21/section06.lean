import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_6_1 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u v

section

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable (𝒪 : Sheaf J CommRingCat.{max u v})
variable [IsLocallyRingedSite J 𝒪]
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v})]

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [SymmetricCategory (ringedSiteModuleCategory J 𝒪)]

-- Proof sketch: an invertible `\mathcal O`-module defines an `\mathcal O^*`-torsor of local
-- generators, and Lemma `21.4.3` identifies isomorphism classes of `\mathcal O^*`-torsors with
-- `H^1(C, \mathcal O^*)`. The locally ringed hypothesis guarantees local triviality of invertible
-- modules, while Lemma `21.4.2` identifies the trivial torsor with the neutral Picard class; the
-- inverse map is obtained by reconstructing an invertible module from an `\mathcal O^*`-torsor.
/-- Lemma 21.6.1: for a locally ringed site `(\mathcal C, \mathcal O)`, the first cohomology
group of the units sheaf `\mathcal O^*` is canonically isomorphic, as an abelian group, to the
Picard group `\mathrm{Pic}(\mathcal O)`. -/
theorem ringedSiteUnitsSheaf_H1_equiv_picardGroup :
    Nonempty (((ringedSiteUnitsAddSheaf 𝒪).H 1) ≃+
      ringedSitePicardGroup J 𝒪) := sorry

end
