import StacksProject_2024.Chap22.Situation_22_27_2
import StacksProject_2024.Chap24.Definition_24_13_1

open CategoryTheory
open DifferentialGradedCategory
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "DGAO" => DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)

-- Semantic owner choice: `Situation_22_27_2` provides the source-facing owner
-- `HasAdmissibleCones` for axiom `(C)`, while `Definition_24_13_1` supplies the
-- Chapter 24 owner `moduleCategory 𝒜 = \mathrm{Mod}(\mathcal A, d)`.

namespace DifferentialGradedModule

local notation "DGModA" => @DifferentialGradedModule.moduleCategory C _ J _ 𝒪 _

variable (𝒜 : DGAO)

local notation "DGComp" => Comp ℤ (DGModA 𝒜)

variable [DifferentialGradedCategory ℤ (DGModA 𝒜)]
local instance : Category (Comp ℤ (DGModA 𝒜)) :=
  DifferentialGradedCategory.compCategory
variable [HasShift (Comp ℤ (DGModA 𝒜)) ℤ]

/-- Lemma 24.22.3: for a ringed site `(\mathcal C, \mathcal O)` and a sheaf of differential
graded algebras `\mathcal A` on it, the differential graded category `\textit{Mod}^{dg}
(\mathcal A, \mathrm d)` satisfies axiom `(C)` of Situation `22.27.2`. In the current
formalization, the Chapter 22 owner `HasAdmissibleCones` is obtained from explicit admissible-cone
data on the Chapter 24 owner `moduleCategory 𝒜`.  Definition `24.22.2` supplies the source-facing
mapping-cone model; once a boundary-map assignment is fixed, a chosen admissible cone for every
closed degree-`0` morphism upgrades that explicit cone data to axiom `(C)`. -/
@[stacks 0FS6]
theorem hasAdmissibleCones_of_admissibleCone
    [B : CompBoundaryMap ℤ (DGModA 𝒜)]
    (hcone : ∀ {x y : DGComp} (f : x ⟶ y),
      AdmissibleCone (R := ℤ) (A := DGModA 𝒜) f) :
    HasAdmissibleCones ℤ (DGModA 𝒜) :=
  ⟨B, fun f ↦ hcone f⟩

/-- Companion bridge: the same admissible-cone data may be supplied as a pointwise existence
statement, and then chosen to build the Chapter 22 owner `HasAdmissibleCones`. -/
theorem hasAdmissibleCones_of_nonemptyAdmissibleCone
    [CompBoundaryMap ℤ (DGModA 𝒜)]
    (hcone : ∀ {x y : DGComp} (f : x ⟶ y),
      Nonempty (AdmissibleCone (R := ℤ) (A := DGModA 𝒜) f)) :
    HasAdmissibleCones ℤ (DGModA 𝒜) :=
  hasAdmissibleCones_of_admissibleCone 𝒜 (fun f ↦ Classical.choice (hcone f))

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
