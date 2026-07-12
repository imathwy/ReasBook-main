import StacksProject_2024.Chap31.Definition_31_12_1

open CategoryTheory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ 𝒢 : X.Modules)

#check (ihom ℱ).obj 𝒢

end

end AlgebraicGeometry.Scheme.Modules
