import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
import StacksProject_2024.Chap13.Definition_13_34_1

open CategoryTheory
open CategoryTheory.Limits
open Opposite

noncomputable section

universe u v w

/-- A source-facing owner for the category of differential graded modules over a fixed
differential graded algebra, exposing the quasi-isomorphisms, admissible epimorphisms, and dual
shifts `Aᵛ⟦k⟧` used in the definition of property `(I)`. -/
structure DGModuleContext where
  /-- The category `Mod_(A, d)` of differential graded modules over a fixed differential graded
  algebra. -/
  moduleCat : Type u
  /-- The categorical structure on differential graded modules. -/
  instCategory : Category.{v} moduleCat
  /-- The abelian structure on differential graded modules. -/
  instAbelian : @Abelian moduleCat instCategory
  /-- The quasi-isomorphisms of differential graded modules. -/
  quasiIso : @MorphismProperty moduleCat instCategory.toCategoryStruct
  /-- The admissible epimorphisms of differential graded modules. -/
  admissibleEpi : @MorphismProperty moduleCat instCategory.toCategoryStruct
  /-- The shifted dual modules `Aᵛ⟦k⟧`. -/
  dualShift : ℤ → moduleCat

attribute [instance] DGModuleContext.instCategory
attribute [instance] DGModuleContext.instAbelian

namespace DGModuleContext

/-- An object is a product of dual shifts if it is isomorphic to a chosen product of objects
`Aᵛ⟦k⟧`. -/
def IsProductOfDualShifts.{u_1, v_1} (𝒜 : DGModuleContext.{u_1, v_1}) (X : 𝒜.moduleCat) : Prop :=
  ∃ (ι : Type u_1) (degree : ι → ℤ) (hι : HasProduct (fun i ↦ 𝒜.dualShift (degree i))),
    let _ := hι
    Nonempty (X ≅ ∏ᶜ fun i ↦ 𝒜.dualShift (degree i))

/-- A filtration exhibiting property `(I)` on a differential graded module, encoded by the inverse
system of quotients `I / F_i I` together with short exact transition sequences whose kernels are
products of the dual shifts `Aᵛ⟦k⟧`. -/
structure PropertyIFiltration (𝒜 : DGModuleContext) (I : 𝒜.moduleCat) where
  /-- The inverse system of quotient stages `I / F_i I`. -/
  tower : SequentialInverseSystem 𝒜.moduleCat
  /-- The initial quotient stage is `I / F_0 I = 0`. -/
  towerZero : IsZero (tower.obj (op 0))
  /-- The inverse system of quotient stages admits a limit. -/
  hasLimit : HasLimit tower
  /-- The original module identifies with the inverse limit of its quotient tower. -/
  limitIso : let _ := hasLimit; I ≅ limit tower
  /-- The successive kernels `F_i I / F_{i + 1} I`. -/
  piece : ℕ → 𝒜.moduleCat
  /-- The inclusion of each successive kernel into the next quotient stage. -/
  inclusion : ∀ i : ℕ, piece i ⟶ tower.obj (op (i + 1))
  /-- Each successive kernel maps to zero in the previous quotient stage. -/
  zero_comp :
    ∀ i : ℕ, inclusion i ≫ tower.transitionMap (Nat.le_succ i) = 0
  /-- Each transition quotient sequence is short exact. -/
  shortExact :
    ∀ i : ℕ,
      (ShortComplex.mk (inclusion i) (tower.transitionMap (Nat.le_succ i))
        (zero_comp i)).ShortExact
  /-- Each transition map is an admissible epimorphism. -/
  admissible :
    ∀ i : ℕ, 𝒜.admissibleEpi (tower.transitionMap (Nat.le_succ i))
  /-- Each successive kernel is a product of dual shifts `Aᵛ⟦k⟧`. -/
  pieceProduct : ∀ i : ℕ, IsProductOfDualShifts 𝒜 (piece i)

/-- A chosen property `(I)` filtration provides the needed limit instance for its quotient tower.
-/
instance instHasLimitPropertyIFiltration
    {𝒜 : DGModuleContext} {I : 𝒜.moduleCat}
    (F : PropertyIFiltration 𝒜 I) :
    HasLimit F.tower :=
  F.hasLimit

/-- The chosen comparison isomorphism identifying a module with the inverse limit of the quotient
tower coming from a property `(I)` filtration. -/
abbrev PropertyIFiltration.limitComparison
    {𝒜 : DGModuleContext} {I : 𝒜.moduleCat}
    (F : PropertyIFiltration 𝒜 I) :
    I ≅ limit F.tower :=
  F.limitIso

/-- A differential graded module has property `(I)` if it admits a filtration whose quotient tower
is inverse-limit complete, whose transition maps are admissible epimorphisms, and whose
successive kernels are products of the dual shifts `Aᵛ⟦k⟧`. -/
def HasPropertyI (𝒜 : DGModuleContext) (I : 𝒜.moduleCat) : Prop :=
  Nonempty (PropertyIFiltration 𝒜 I)

/-- A chosen property `(I)` filtration exhibits property `(I)` on the underlying differential
graded module. -/
theorem PropertyIFiltration.hasPropertyI
    {𝒜 : DGModuleContext} {I : 𝒜.moduleCat}
    (F : PropertyIFiltration 𝒜 I) :
    HasPropertyI 𝒜 I :=
  ⟨F⟩

namespace HasPropertyI

/-- A property `(I)` hypothesis can be discharged by working with an arbitrary chosen witnessing
filtration. This keeps `HasPropertyI` as the source-facing public owner while providing the bridge
to the explicit filtration API used by nearby Chapter 22 lemmas. -/
theorem elim
    {𝒜 : DGModuleContext} {I : 𝒜.moduleCat} {P : Prop}
    (hI : HasPropertyI 𝒜 I)
    (hP : PropertyIFiltration 𝒜 I → P) :
    P := by
  rcases hI with ⟨F⟩
  exact hP F

end HasPropertyI

end DGModuleContext

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat A) ℤ

/-- The degree-`n` cokernel `Coker(d_M)` of the differential graded `A`-module `M`. This is the
source's cokernel of the differential in degree `n`. -/
abbrev differentialCokernel (M : DGMod) (n : ℤ) : ModuleCat A :=
  cokernel (M.d (n - 1) n)

/-- The map on differential cokernels induced by a morphism of differential graded `A`-modules. -/
abbrev differentialCokernelMap {M I : DGMod} (ι : M ⟶ I) (n : ℤ) :
    differentialCokernel M n ⟶ differentialCokernel I n :=
  cokernel.map (M.d (n - 1) n) (I.d (n - 1) n) (ι.f (n - 1)) (ι.f n)
    (by simpa using ι.comm (n - 1) n)

@[reassoc, simp]
theorem π_differentialCokernelMap {M I : DGMod} (ι : M ⟶ I) (n : ℤ) :
    cokernel.π (M.d (n - 1) n) ≫ differentialCokernelMap ι n =
      ι.f n ≫ cokernel.π (I.d (n - 1) n) := by
  simp [differentialCokernelMap]

/-- A differential graded `A`-module is a product of shifts of a fixed dual object `Aᵛ` if it is
isomorphic to a chosen product of objects `Aᵛ⟦k⟧`. -/
def IsProductOfDualShifts (Avee P : DGMod) : Prop :=
  ∃ (ι : Type u) (degree : ι → ℤ) (hι : HasProduct (fun i ↦ (Avee⟦degree i⟧ : DGMod))),
    let _ := hι
    Nonempty (P ≅ ∏ᶜ fun i ↦ (Avee⟦degree i⟧ : DGMod))

/-- The induced maps `Coker(d_M) ⟶ Coker(d_I)` are monomorphisms in every degree. -/
def MonoOnDifferentialCokernels {M I : DGMod} (ι : M ⟶ I) : Prop :=
  ∀ n : ℤ, Mono (differentialCokernelMap ι n)

end

end CochainComplex
