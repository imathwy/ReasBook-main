import Mathlib
import StacksProject_2024.Chap18.Lemma_18_28_8
import StacksProject_2024.Chap18.Lemma_18_30_4
import StacksProject_2024.Chap13.Lemma_13_35_7
import StacksProject_2024.Chap13.Remark_13_35_5
import StacksProject_2024.Chap21.Lemma_21_52_1

open CategoryTheory
open CategoryTheory.IsGrothendieckAbelian

noncomputable section

universe u w

attribute [local instance] HasDerivedCategory.standard

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable {𝒪 : Sheaf J CommRingCat.{u}}

local notation "Mod" => SheafOfModules (ringSheaf J 𝒪)
local notation "DMod" => DerivedCategory Mod

-- Proof sketch: apply `compactObject_isRetract_of_finiteCoproductComplex_of_generatingSet` to the
-- set of modules `j_{U!}\mathcal O_U` with `U` quasi-compact. Use Lemma `18.28.8` and the
-- quasi-compact covering hypothesis to obtain the generating epimorphism condition, and use the
-- identification `Hom(j_{U!}\mathcal O_U, -) = \Gamma(U, -)` together with Lemma `7.17.7` as
-- packaged in Lemma `18.30.4` to prove that each such generator is compact.
/-- Lemma 21.52.2: if every object of the ringed site admits a covering by quasi-compact objects,
then every compact object of `D(\mathcal O)` is a retract of an object represented by a bounded
complex whose terms are finite direct sums of modules `j_{U!}\mathcal O_U` with `U`
quasi-compact. -/
theorem compactObject_isRetract_of_finite_quasiCompact_extensionByZeroStructureComplex
    [IsGrothendieckAbelian.{w} Mod]
    (hcover : ∀ W : C, ∃ S : J.Cover W, ∀ I : S.Arrow, J.QuasiCompactObject I.Y)
    {K : DMod} (hK : IsCompactObject K) :
    ∃ (P : CochainComplex Mod ℤ) (a b : ℤ),
      P.IsStrictlyGE a ∧
        P.IsStrictlyLE b ∧
          (∀ i : Set.Icc a b,
            CategoryTheory.additiveClosure
              (fun ℱ : Mod ↦ ∃ U : C, J.QuasiCompactObject U ∧
                ℱ = localizedStructureModuleExtensionByZero 𝒪 U)
              (P.X i.1)) ∧
            Nonempty (Retract K (DerivedCategory.Q.obj P)) := sorry

end

end SheafOfModules.RingedSite
