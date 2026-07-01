import Mathlib
import stacks_project.Chap21.Example_21_48_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat]
variable [J.WEqualsLocallyBijective AddCommGrpCat]
variable [∀ U : C, (J.over U).HasSheafCompose
  (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat]
variable [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => RingedSiteModules J 𝒪
local notation "Cpx" => CochainComplex Mod ℤ

section

variable [MonoidalCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]

-- Proof sketch: write the coevaluation and evaluation of the chosen left dual degreewise. The
-- triangle identities induce left duals between `G.X n` and `F.X n`, so Lemma `18.29.2`
-- applied on each localized ringed site shows that every term of `F` becomes locally a direct
-- summand of a finite free module. As in the module-complex argument of More on Algebra,
-- Lemma `15.73.2`, the coevaluation has only finitely many nonzero homogeneous components after
-- passing to a cover, which yields local boundedness and hence local strict perfectness.
/-- Lemma 21.48.3: if a complex `\mathcal F^\bullet` of `\mathcal O`-modules on a ringed site has
a left dual in the monoidal category of complexes of `\mathcal O`-modules, then
`\mathcal F^\bullet` is locally strictly perfect, i.e. every object `U` admits a covering on
whose members the restricted complex is strictly perfect. -/
theorem exactPairing_isLocallyStrictlyPerfect
    {F G : Cpx} (hpair : ExactPairing G F) :
    CochainComplex.IsLocallyStrictlyPerfect F := sorry

section

variable [BraidedCategory (CochainComplex (RingedSiteModules J 𝒪) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSiteModules J 𝒪) ℤ)]

/-- The canonical uniqueness isomorphism from a chosen left dual of `F^\bullet` to the internal-Hom
object `\mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O)` produced in Example `21.48.2`
once `F^\bullet` is known to be locally strictly perfect. -/
noncomputable def exactPairing_leftDualIso_internalHomToUnit
    {F G : Cpx} (hpair : ExactPairing G F) :
    G ≅ (ihom F).obj (𝟙_ Cpx) :=
  leftDualIso hpair
    (ringedSiteModuleComplexDualExactPairing
      (exactPairing_isLocallyStrictlyPerfect hpair))

end

end

end

end SheafOfModules.RingedSite
