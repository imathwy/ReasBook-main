import StacksProject_2024.Chap24.Definition_24_13_1

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open HomologicalComplex
open scoped SheafOfModules.RingedSite.DifferentialGradedModule

noncomputable section

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

universe u v

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [HasFiniteBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]

local notation "ModO" => ringedSiteModuleCategory J 𝒪
local notation "CpxO" => CochainComplex ModO ℤ
/-- Tensoring sheaves of modules on the right by a fixed module is additive. -/
local instance tensorRightAdditive (M : ModO) : (tensorRight M).Additive :=
  show (tensorRight M).Additive from tensorRight_additive M

namespace DifferentialGradedModule

/-- The canonical degree equality identifying `(n + 1) + m` with `n + m + 1`. -/
private theorem succAdd_eq_addSucc (n m : ℤ) : (n + 1) + m = n + m + 1 :=
  ((Int.add_assoc n 1 m).trans
      (congrArg (fun t : ℤ ↦ n + t) (Int.add_comm 1 m))).trans
    (Int.add_assoc n m 1).symm

/-- The degree-`n` term of the source-faithful cone underlying `C(f)`. -/
private def coneTerm
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (n : ℤ) : ModO :=
  L.toComplex.X n ⊞ K.toComplex.X (n + 1)

section

variable {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}

private abbrev coneTerm' (n : ℤ) : ModO :=
  coneTerm (𝒜 := 𝒜) (K := K) (L := L) n

/-- The canonical mapping-cone degree identifies with the textbook order
`L^n \oplus K^{n + 1}` after swapping the canonical biproduct factors. -/
private noncomputable def mappingConeTextbookXIso
    (f : K ⟶ L) (n : ℤ) :
    (CochainComplex.mappingCone f.toCochainMap).X n ≅ coneTerm' n :=
  homotopyCofiber.XIsoBiprod f.toCochainMap n (n + 1) rfl ≪≫
    biprod.braiding (K.toComplex.X (n + 1)) (L.toComplex.X n)

/-- The differential on the source-faithful cone underlying `C(f)`, written in the textbook order
`L^n \oplus K^{n + 1}`. -/
private noncomputable def coneDiff
    (f : K ⟶ L) (n : ℤ) :
    coneTerm' n ⟶ coneTerm' (n + 1) :=
  (mappingConeTextbookXIso f n).inv ≫
    (CochainComplex.mappingCone f.toCochainMap).d n (n + 1) ≫
    (mappingConeTextbookXIso f (n + 1)).hom

private abbrev coneDiff' (f : K ⟶ L) (n : ℤ) : coneTerm' n ⟶ coneTerm' (n + 1) :=
  coneDiff (𝒜 := 𝒜) (K := K) (L := L) f n

/-- The textbook cone differential squares to zero. -/
private theorem coneDiff_sq
    (f : K ⟶ L) :
    ∀ n : ℤ, coneDiff' f n ≫ coneDiff' f (n + 1) = 0 := by
  sorry

/-- The underlying cochain complex of the source-faithful cone `C(f)`. -/
private noncomputable def coneComplex
    (f : K ⟶ L) : CpxO :=
  CochainComplex.of coneTerm' (coneDiff' f) (coneDiff_sq f)

/-- The direct-sum `\mathcal A`-action on the textbook cone term
`L^n \oplus K^{n + 1}`. -/
private noncomputable def coneSmul
    (n m : ℤ) :
    (coneTerm' n ⊗ 𝒜.toComplex.X m) ⟶ coneTerm' (n + m) :=
  ((tensorRight (𝒜.toComplex.X m)).mapBiprod (L.toComplex.X n) (K.toComplex.X (n + 1))).hom ≫
    biprod.map
      (L.smul n m)
      (K.smul (n + 1) m ≫
        eqToHom (congrArg (fun t : ℤ ↦ K.toComplex.X t) (succAdd_eq_addSucc n m)))

private abbrev coneSmul' (n m : ℤ) : (coneTerm' n ⊗ 𝒜.toComplex.X m) ⟶ coneTerm' (n + m) :=
  coneSmul (𝒜 := 𝒜) (K := K) (L := L) n m

/-- The cone action is associative because it is the direct sum of the actions on `L` and `K`. -/
private theorem cone_smul_assoc
    (n m k : ℤ) :
    (α_ (coneTerm' n) (𝒜.toComplex.X m) (𝒜.toComplex.X k)).hom ≫
        (coneTerm' n ◁ 𝒜.mul m k) ≫
        coneSmul' n (m + k) =
      (coneSmul' n m ▷ 𝒜.toComplex.X k) ≫
        coneSmul' (n + m) k ≫
        eqToHom (congrArg coneTerm' (Int.add_assoc n m k)) := by
  sorry

/-- The unit section of `\mathcal A^0` acts as the identity on each cone degree. -/
private theorem cone_one_smul
    (n : ℤ) :
    (coneTerm' n ◁ unitIsoTensorUnit.hom) ≫
        (ρ_ (coneTerm' n)).hom =
      (coneTerm' n ◁ 𝒜.one) ≫
        coneSmul' n 0 ≫
        eqToHom (congrArg coneTerm' (add_zero n)) := by
  sorry

/-- The cone differential satisfies the Leibniz rule with respect to the direct-sum action. -/
private theorem cone_d_smul
    (f : K ⟶ L) (n m : ℤ) :
    coneSmul' n m ≫ coneDiff' f (n + m) =
      (coneDiff' f n ▷ 𝒜.toComplex.X m) ≫
        coneSmul' (n + 1) m ≫
        eqToHom
          (congrArg coneTerm'
            (differentialGradedAlgebra_leftLeibniz_index n m)) +
      n.negOnePow •
        ((coneTerm' n ◁ 𝒜.toComplex.d m (m + 1)) ≫
          coneSmul' n (m + 1) ≫
          eqToHom
            (congrArg coneTerm'
              (differentialGradedAlgebra_rightLeibniz_index n m))) := by
  sorry

/-- Definition 24.22.2: for a homomorphism `f : \mathcal K \to \mathcal L` of differential graded
`\mathcal A`-modules on a ringed site, the cone `C(f)` is the differential graded
`\mathcal A`-module whose underlying cochain complex has degree-`n` term
`\mathcal L^n \oplus \mathcal K^{n + 1}`, differential given by the matrix
`[[d_\mathcal L, f], [0, -d_\mathcal K]]`, and `\mathcal A`-action given by the direct sum of the
actions on `\mathcal L` and `\mathcal K`. -/
@[stacks 0FS5]
noncomputable def cone
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (f : K ⟶ L) : Mod(𝒜, d) where
  toComplex := coneComplex f
  smul := coneSmul
  smul_assoc := cone_smul_assoc
  one_smul := cone_one_smul
  d_smul := by
    simpa [coneComplex] using cone_d_smul f

/-- The degree-`n` term of `cone f` is `L^n \oplus K^{n + 1}`. -/
@[simp] theorem cone_X
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (f : K ⟶ L) (n : ℤ) :
    (cone f).toComplex.X n = (L.toComplex.X n ⊞ K.toComplex.X (n + 1)) :=
  rfl

/-- The source-facing cone evaluates in degree `n` to `L^n \oplus K^{n + 1}`. -/
@[simp] theorem cone_apply
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (f : K ⟶ L) (n : ℤ) :
    cone f n = (L n ⊞ K (n + 1)) :=
  rfl

/-- The differential on `cone f`, written in the ordered biproduct
`L^n \oplus K^{n + 1}` as a block matrix. -/
private theorem cone_d_desc_lift
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (f : K ⟶ L) (n : ℤ) :
    (cone f).toComplex.d n (n + 1) =
      biprod.desc
        (L.toComplex.d n (n + 1) ≫ biprod.inl)
        (biprod.lift
          (f.toCochainMap.f (n + 1))
          (-K.toComplex.d (n + 1) ((n + 1) + 1))) :=
  sorry

/-- The differential on `cone f` is the textbook matrix
`\begin{pmatrix} d_\mathcal L & f \\ 0 & -d_\mathcal K \end{pmatrix}` in the ordered biproduct
`L^n \oplus K^{n + 1}`. -/
theorem cone_d
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (f : K ⟶ L) (n : ℤ) :
    (cone f).toComplex.d n (n + 1) =
      Biprod.ofComponents
        (L.toComplex.d n (n + 1))
        0
        (f.toCochainMap.f (n + 1))
        (-K.toComplex.d (n + 1) ((n + 1) + 1)) := by
  sorry

/-- Bridge/view: in each degree, the source-facing cone term is canonically isomorphic to the
corresponding term of the canonical cochain-complex mapping cone. -/
noncomputable def coneXIsoMappingConeX
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (f : K ⟶ L) (n : ℤ) :
    (cone f).toComplex.X n ≅ (CochainComplex.mappingCone f.toCochainMap).X n :=
  (mappingConeTextbookXIso f n ≪≫ eqToIso (cone_X f n).symm).symm

/-- Bridge/view: the underlying cochain complex of `cone f` is canonically isomorphic to the
canonical mapping cone of the underlying cochain map. -/
noncomputable def coneToMappingCone
    {𝒜 : DifferentialGradedAlgebra (C := C) (J := J) (𝒪 := 𝒪)} {K L : Mod(𝒜, d)}
    (f : K ⟶ L) :
    (cone f).toComplex ≅ CochainComplex.mappingCone f.toCochainMap :=
  HomologicalComplex.Hom.isoOfComponents
    (coneXIsoMappingConeX f)
    (fun i j hij ↦ by
      sorry)

end

end DifferentialGradedModule

end

end SheafOfModules.RingedSite
