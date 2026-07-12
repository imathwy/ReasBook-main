import Mathlib
import StacksProject_2024.Chap18.Definition_18_32_1.UnitIsoTensorUnit
import StacksProject_2024.Chap18.RingedSiteModuleCategory

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ

/-- Transport the left Leibniz term for a sheaf-valued cochain differential graded algebra to
degree `n + m + 1`. -/
theorem differentialGradedAlgebra_leftLeibniz_index (n m : ℤ) :
    (n + 1) + m = n + m + 1 := by
  omega

/-- Transport the right Leibniz term for a sheaf-valued cochain differential graded algebra to
degree `n + m + 1`. -/
theorem differentialGradedAlgebra_rightLeibniz_index (n m : ℤ) :
    n + (m + 1) = n + m + 1 := by
  omega

/-- Definition 24.12.1 (1): a sheaf of differential graded `\mathcal O`-algebras on a ringed
site `(\mathcal C, \mathcal O)` is a cochain complex of `\mathcal O`-modules equipped with
degreewise multiplication, a unit, and the graded Leibniz rule. -/
structure DifferentialGradedAlgebra where
  /-- The underlying cochain complex of `\mathcal O`-modules. -/
  toComplex : CpxO
  /-- The degreewise multiplication map `\mathcal A^n \otimes \mathcal A^m \to
  \mathcal A^{n + m}`. -/
  mul : ∀ n m : ℤ, toComplex.X n ⊗ toComplex.X m ⟶ toComplex.X (n + m)
  /-- The unit section `1 \in \mathcal A^0`, expressed as a morphism from the unit
  `\mathcal O`-module. -/
  one : unitModule J 𝒪 ⟶ toComplex.X 0
  /-- Associativity of the multiplication. -/
  mul_assoc :
    ∀ n m k : ℤ,
      (α_ (toComplex.X n) (toComplex.X m) (toComplex.X k)).hom ≫
          (toComplex.X n ◁ mul m k) ≫
          mul n (m + k) =
        (mul n m ▷ toComplex.X k) ≫
          mul (n + m) k ≫
          eqToHom (congrArg toComplex.X (Int.add_assoc n m k))
  /-- The left unit law. -/
  one_mul :
    ∀ n : ℤ,
      (unitIsoTensorUnit.hom ▷ toComplex.X n) ≫
          (λ_ (toComplex.X n)).hom =
        (one ▷ toComplex.X n) ≫
          mul 0 n ≫
          eqToHom (congrArg toComplex.X (zero_add n))
  /-- The right unit law. -/
  mul_one :
    ∀ n : ℤ,
      (toComplex.X n ◁ unitIsoTensorUnit.hom) ≫
          (ρ_ (toComplex.X n)).hom =
        (toComplex.X n ◁ one) ≫
          mul n 0 ≫
          eqToHom (congrArg toComplex.X (add_zero n))
  /-- Compatibility of the differential with multiplication (the graded Leibniz rule). -/
  d_mul :
    ∀ n m : ℤ,
      mul n m ≫ toComplex.d (n + m) (n + m + 1) =
        ((toComplex.d n (n + 1)) ▷ toComplex.X m) ≫
          mul (n + 1) m ≫
          eqToHom
            (congrArg toComplex.X
              (differentialGradedAlgebra_leftLeibniz_index n m)) +
        n.negOnePow •
          ((toComplex.X n ◁ toComplex.d m (m + 1)) ≫
            mul n (m + 1) ≫
            eqToHom
              (congrArg toComplex.X
                (differentialGradedAlgebra_rightLeibniz_index n m)))

local notation "DGAO" => @DifferentialGradedAlgebra C _ J _ 𝒪 _

/-- The underlying cochain complex of a bundled differential graded algebra. -/
instance instCoeOutDifferentialGradedAlgebra :
    CoeOut DGAO CpxO where
  coe 𝒜 := 𝒜.toComplex

namespace DifferentialGradedAlgebra

/-- A homomorphism of sheaves of differential graded `\mathcal O`-algebras is a morphism of the
underlying cochain complexes that preserves the unit and multiplication. -/
@[ext] structure Hom
    (A B : DGAO) where
  /-- The underlying morphism of cochain complexes of `\mathcal O`-modules. -/
  hom : A.toComplex ⟶ B.toComplex
  /-- The degree-zero component preserves the unit section. -/
  comm_one :
    A.one ≫ hom.f 0 = B.one
  /-- Compatibility with the multiplication maps in each pair of degrees. -/
  comm_mul :
    ∀ n m : ℤ,
      A.mul n m ≫ hom.f (n + m) =
        ((hom.f n) ▷ A.toComplex.X m) ≫
          (B.toComplex.X n ◁ hom.f m) ≫
          B.mul n m

/-- A differential graded algebra homomorphism carries its underlying morphism of cochain
complexes. -/
instance instCoeOutHom
    {A B : DGAO} :
    CoeOut (Hom A B) (A.toComplex ⟶ B.toComplex) where
  coe f := f.hom

end DifferentialGradedAlgebra

end

end SheafOfModules.RingedSite
