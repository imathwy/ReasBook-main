import Serre.Chap15.Exercise_15_15_1_2
import Serre.Chap15.Definition_15_15_3_1
import Serre.Chap15.Theorem_15_15_2_2

noncomputable section

universe u

namespace Representation

open scoped Representation TensorProduct

section ScalarExtensionCompatibility

variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]

variable (A : Type u) [CommRing A] [IsLocalRing A] [HenselianLocalRing A]
  [IsDomain A] [IsDiscreteValuationRing A] [Algebra A K] [IsFractionRing A K]

local notation "k" => IsLocalRing.ResidueField A
local notation:max "P_k(" G ")" => finiteProjectiveGroupAlgebraGrothendieckGroup k G
local notation:max "R_K(" G ")" => finiteRepGrothendieckGroup K G
local notation:max "R_k(" G ")" => finiteRepGrothendieckGroup k G
local notation "d" => decompositionHom A K G

local notation "e" => projectiveGrothendieckScalarExtensionHom (A := A) (K := K) (G := G)

/-- Exercise 15-15.3-2: Serre's scalar-extension homomorphism intertwines the tensor-product
action of `d x ∈ R_k(G)` on `P_k(G)` with multiplication by `x ∈ R_K(G)`. -/
theorem projectiveGrothendieckScalarExtensionHom_smul
    (x : R_K(G)) (y : P_k(G)) :
    e (d x • y) = x * e y := by
  sorry

end ScalarExtensionCompatibility

end Representation
