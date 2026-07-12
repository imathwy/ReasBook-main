import StacksProject_2024.Chap31.Definition_31_21_1
import StacksProject_2024.Chap31.Lemma_31_20_3

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: the reusable owners here are the scheme-level ideal-sheaf predicates from
-- `Definition_31_21_1` together with the implication ladder already publicized in
-- `Lemma_31_20_3`. This file keeps the Stacks-tagged consequences as thin projections from the
-- quasi-regular case instead of duplicating separate proof routes for each regularity notion.

section

variable {X : Scheme.{u}}
local notation "ModX" => RingedSpace.Modules X.toRingedSpace
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
variable (I : Subobject 𝒪X)
local notation "ℐ" => (Subobject.underlying.obj I : ModX)

/-- A quasi-regular ideal sheaf on a scheme is both finite type and quasi-coherent. -/
theorem quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent
    (hI : IsQuasiRegularIdealSheaf I) :
    ℐ.IsFiniteType ∧ ℐ.IsQuasicoherent := by
  sorry

/-- Lemma 31.20.6 (1): a regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
theorem regularIdealSheaf_isFiniteType (hI : IsRegularIdealSheaf I) :
    ℐ.IsFiniteType := by
  have hI' : IsQuasiRegularIdealSheaf I := by
    exact RingedSpace.h1RegularIdealSheaf_isQuasiRegularIdealSheaf I <|
      RingedSpace.koszulRegularIdealSheaf_isH1RegularIdealSheaf I <|
        RingedSpace.regularIdealSheaf_isKoszulRegularIdealSheaf I hI
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI').1

/-- Lemma 31.20.6 (2): a regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
theorem regularIdealSheaf_isQuasicoherent (hI : IsRegularIdealSheaf I) :
    ℐ.IsQuasicoherent := by
  have hI' : IsQuasiRegularIdealSheaf I := by
    exact RingedSpace.h1RegularIdealSheaf_isQuasiRegularIdealSheaf I <|
      RingedSpace.koszulRegularIdealSheaf_isH1RegularIdealSheaf I <|
        RingedSpace.regularIdealSheaf_isKoszulRegularIdealSheaf I hI
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI').2

/-- Lemma 31.20.6 (3): a Koszul-regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
theorem koszulRegularIdealSheaf_isFiniteType (hI : IsKoszulRegularIdealSheaf I) :
    ℐ.IsFiniteType := by
  have hI' : IsQuasiRegularIdealSheaf I := by
    exact RingedSpace.h1RegularIdealSheaf_isQuasiRegularIdealSheaf I <|
      RingedSpace.koszulRegularIdealSheaf_isH1RegularIdealSheaf I hI
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI').1

/-- Lemma 31.20.6 (4): a Koszul-regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
theorem koszulRegularIdealSheaf_isQuasicoherent (hI : IsKoszulRegularIdealSheaf I) :
    ℐ.IsQuasicoherent := by
  have hI' : IsQuasiRegularIdealSheaf I := by
    exact RingedSpace.h1RegularIdealSheaf_isQuasiRegularIdealSheaf I <|
      RingedSpace.koszulRegularIdealSheaf_isH1RegularIdealSheaf I hI
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI').2

/-- Lemma 31.20.6 (5): an `H_1`-regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
theorem h1RegularIdealSheaf_isFiniteType (hI : IsH1RegularIdealSheaf I) :
    ℐ.IsFiniteType := by
  have hI' : IsQuasiRegularIdealSheaf I := by
    exact RingedSpace.h1RegularIdealSheaf_isQuasiRegularIdealSheaf I hI
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI').1

/-- Lemma 31.20.6 (6): an `H_1`-regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
theorem h1RegularIdealSheaf_isQuasicoherent (hI : IsH1RegularIdealSheaf I) :
    ℐ.IsQuasicoherent := by
  have hI' : IsQuasiRegularIdealSheaf I := by
    exact RingedSpace.h1RegularIdealSheaf_isQuasiRegularIdealSheaf I hI
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI').2

/-- Lemma 31.20.6 (7): a quasi-regular sheaf of ideals on a scheme is of finite type. -/
@[stacks 063F]
theorem quasiRegularIdealSheaf_isFiniteType (hI : IsQuasiRegularIdealSheaf I) :
    ℐ.IsFiniteType := by
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI).1

/-- Lemma 31.20.6 (8): a quasi-regular sheaf of ideals on a scheme is quasi-coherent. -/
@[stacks 063F]
theorem quasiRegularIdealSheaf_isQuasicoherent (hI : IsQuasiRegularIdealSheaf I) :
    ℐ.IsQuasicoherent := by
  exact (quasiRegularIdealSheaf_isFiniteType_and_isQuasicoherent I hI).2

end

end AlgebraicGeometry
