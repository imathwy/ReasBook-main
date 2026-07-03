import Mathlib
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_15_15_2_2 (from Chap15) -/
noncomputable section

universe u v

namespace Representation

open scoped Pointwise Representation
open CategoryTheory

/-
Domain-style sampling for this item:
* source-facing owners already present upstream: `StableLattice`,
  `StableLattice.reductionRepresentation`, and `finiteRepGrothendieckGroup`.
* core/canonical bundled owner for finite-dimensional representations: `FDRep.of`.
* source-facing declarations in this file: independence of the reduction class from the chosen
  stable lattice, and the induced Grothendieck-group map `decompositionHom`.

Primitive data vs derived API:
* primitive data belongs to the owners `StableLattice` and `finiteRepGrothendieckGroup`;
* derived API here is the canonical rebundling `FDRep.of L.reductionRepresentation`
  and the quotient lift `decompositionHom`.
-/

section ReductionFiniteRep

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {K : Type v} [Field K] [Algebra A K]
variable {G : Type u} [Group G]
variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

namespace StableLattice

-- Proof sketch: a stable lattice is finitely generated over `A`, hence its quotient by
-- `𝔪_A L` is finitely generated over the residue field `A ⧸ 𝔪_A`.
/-- The reduction modulo the maximal ideal of a stable lattice is finite-dimensional over the
residue field. -/
theorem reduction_finite {ρ : Representation K G E} (L : StableLattice A ρ) :
    Module.Finite (IsLocalRing.ResidueField A)
      L.reduction := by
  let M : Type _ := L.toSubmodule ⧸ L.maximalIdealSubmodule
  letI : Module (IsLocalRing.ResidueField A) M := inferInstance
  letI : IsScalarTower A (IsLocalRing.ResidueField A) M :=
    IsScalarTower.of_algebraMap_smul fun a x ↦ by
      refine Quotient.inductionOn' x ?_
      intro y
      rfl
  letI : Module.Finite (IsLocalRing.ResidueField A) M := by
    -- First view the quotient defining the reduction as an `A`-finite module.
    dsimp [M]
    letI : Module.Finite A L.toSubmodule := by
      infer_instance
    letI : Module.Finite A (L.toSubmodule ⧸ L.maximalIdealSubmodule) :=
      Module.Finite.quotient A L.maximalIdealSubmodule
    -- Then pass from `A` to its residue field via the quotient scalar action.
    exact Module.Finite.of_restrictScalars_finite A (IsLocalRing.ResidueField A)
      (L.toSubmodule ⧸ L.maximalIdealSubmodule)
  let e : M ≃ₗ[IsLocalRing.ResidueField A] L.reduction :=
    { toFun := id
      invFun := id
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        -- Compare the canonical quotient action with the public residue-field action on
        -- represented classes.
        change (Submodule.Quotient.mk (a • y) : L.reduction) =
          (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a :
              IsLocalRing.ResidueField A) •
            (Submodule.Quotient.mk y : L.reduction)
        symm
        exact StableLattice.reduction_smul_mk (L := L) a y }
  -- Finally transport finiteness across the identity equivalence between the two quotient owners.
  exact Module.Finite.equiv e

instance {ρ : Representation K G E} (L : StableLattice A ρ) :
    Module.Finite (IsLocalRing.ResidueField A) L.reduction :=
  reduction_finite L

end StableLattice

end ReductionFiniteRep

section FDRepRestrictScalars

variable {A : Type u} [CommRing A]
variable {K : Type v} [Field K] [Algebra A K]
variable {G : Type v} [Group G]

namespace FDRep

/-- Restrict scalars on the underlying module of a finite-dimensional `K[G]`-representation along
`A → K`. -/
instance instModuleRestrictScalars (V : FDRep K G) : Module A V.V :=
  Module.compHom V.V (algebraMap A K)

/-- The ambient `A`- and `K`-actions on a finite-dimensional `K[G]`-representation form a scalar
tower. -/
instance instIsScalarTowerRestrictScalars (V : FDRep K G) : IsScalarTower A K V.V :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

end FDRep

end FDRepRestrictScalars

section ReductionGrothendieckClass

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable {G : Type u} [Group G]
variable {E : Type u} [AddCommGroup E] [Module A E] [Module K E] [IsScalarTower A K E]

local notation "k" => IsLocalRing.ResidueField A

namespace StableLattice

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: multiplication by a field unit acts `A`-linearly on the
ambient module. -/
abbrev mulByUnitLinear (a : Kˣ) : E →ₗ[A] E :=
  ((Algebra.lsmul A K E).toLinearMap (a : K)).restrictScalars A

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: multiplication by a field unit is injective on the ambient
module. -/
theorem mulByUnitLinear_injective (a : Kˣ) :
    Function.Injective (mulByUnitLinear (A := A) (K := K) (E := E) a) := by
  -- Apply the inverse unit on both sides to cancel the homothety.
  intro x y h
  have h' := congrArg (fun z => ((↑a⁻¹ : K) • z)) h
  simpa [mulByUnitLinear, smul_smul] using h'

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the image of a stable lattice under multiplication by a field
unit is exactly the homothetic lattice. -/
theorem toSubmodule_map_mulByUnitLinear
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    L.toSubmodule.map (mulByUnitLinear (A := A) (K := K) (E := E) a) = (a • L).toSubmodule := by
  -- Both sides are described by the same witnesses upstairs in `E`.
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: multiplication by a field unit identifies a lattice with its
homothetic copy as an `A`-submodule. -/
noncomputable def toSubmoduleEquivSmul
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    L.toSubmodule ≃ₗ[A] (a • L).toSubmodule :=
  (Submodule.equivMapOfInjective (mulByUnitLinear (A := A) (K := K) (E := E) a)
      (mulByUnitLinear_injective (A := A) (K := K) (E := E) a) L.toSubmodule).trans
    (LinearEquiv.ofEq _ _ (toSubmodule_map_mulByUnitLinear (A := A) (K := K) (ρ := ρ) L a))

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the maximal-ideal multiple `𝔪_A L` is carried to the
maximal-ideal multiple of the homothetic lattice. -/
theorem maximalIdealSubmodule_map_toSubmoduleEquivSmul
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    L.maximalIdealSubmodule.map
        ((toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a).toLinearMap) =
      (a • L).maximalIdealSubmodule := by
  -- Transport `𝔪_A • ⊤` through the linear equivalence and use surjectivity on the top submodule.
  rw [StableLattice.maximalIdealSubmodule, StableLattice.maximalIdealSubmodule,
    Submodule.map_smul'']
  have htop : (⊤ : Submodule A L.toSubmodule).map
      ((toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a).toLinearMap) = ⊤ := by
    rw [Submodule.map_top]
    exact
      LinearMap.range_eq_top.2
        (toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a).surjective
  simp [htop]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the underlying `A`-module quotient defining the reduction is
unchanged by homothety of the lattice. -/
noncomputable def reductionEquivSmulA
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    L.reduction ≃ₗ[A] (a • L).reduction :=
  Submodule.Quotient.equiv L.maximalIdealSubmodule (a • L).maximalIdealSubmodule
    (toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a)
    (maximalIdealSubmodule_map_toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: on represented quotient classes, the homothety comparison map
is induced by multiplication by the chosen unit upstairs. -/
theorem reductionEquivSmulA_apply_mk
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) (x : L.toSubmodule) :
    reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a) x) := by
  -- Unfold the quotient equivalence and evaluate it on a represented class.
  simp [reductionEquivSmulA, Submodule.Quotient.equiv_apply]

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the reduction modulo `𝔪_A` is unchanged, as a `k`-vector
space, when the lattice is rescaled by a field unit. -/
noncomputable def reductionEquivSmul
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    L.reduction ≃ₗ[k] (a • L).reduction := by
  -- Start from the `A`-linear quotient equivalence and then check residue-field linearity on
  -- represented scalars and represented quotient classes.
  refine
    { toFun := reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a
      invFun := (reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a).symm
      left_inv := (reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a).left_inv
      right_inv := (reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a).right_inv
      map_add' := (reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a).map_add
      map_smul' := ?_ }
  intro c x
  refine Quotient.inductionOn' c ?_
  intro b
  refine Quotient.inductionOn' x ?_
  intro y
  -- Reduce the scalar action to an `A`-scalar on representatives and transport it through the
  -- quotient comparison map.
  change
    (reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a)
        ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) b : k) •
          (Submodule.Quotient.mk y : L.reduction)) = _
  rw [StableLattice.reduction_smul_mk (L := L) b y]
  rw [reductionEquivSmulA_apply_mk]
  calc
    (Submodule.Quotient.mk
        ((toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a) (b • y)) :
          (a • L).reduction) =
        Submodule.Quotient.mk
          (b • (toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a) y) := by
            simp
    _ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) b : k) •
          (Submodule.Quotient.mk
            ((toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a) y) :
              (a • L).reduction) := by
          rw [StableLattice.reduction_smul_mk (L := a • L)]
    _ = (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) b : k) •
          (reductionEquivSmulA (A := A) (K := K) (ρ := ρ) L a
            (Submodule.Quotient.mk y)) := by
          rw [reductionEquivSmulA_apply_mk]

end StableLattice

namespace StableLattice

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the `k`-linear reduction equivalence associated to a homothety
acts on represented quotient classes by the induced lattice homothety upstairs. -/
@[simp] theorem reductionEquivSmul_apply_mk
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) (x : L.toSubmodule) :
    reductionEquivSmul (A := A) (K := K) (ρ := ρ) L a (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a) x) := by
  -- The `k`-linear equivalence is defined using the same quotient map as `reductionEquivSmulA`.
  exact reductionEquivSmulA_apply_mk (A := A) (K := K) (ρ := ρ) L a x

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the lattice homothety equivalence sends each lattice point to
its scalar multiple in the ambient module. -/
@[simp] theorem toSubmoduleEquivSmul_apply_coe
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) (y : L.toSubmodule) :
    ((toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a y : (a • L).toSubmodule) : E) =
      (a : K) • (y : E) := by
  have h :=
    Submodule.coe_equivMapOfInjective_apply
      (StableLattice.mulByUnitLinear (A := A) (K := K) (E := E) a)
      (StableLattice.mulByUnitLinear_injective (A := A) (K := K) (E := E) a)
      L.toSubmodule y
  simpa [StableLattice.toSubmoduleEquivSmul, StableLattice.mulByUnitLinear] using h

omit [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the homothety equivalence on lattices commutes with the
restricted `G`-action upstairs. -/
theorem toSubmoduleEquivSmul_comm
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) (g : G)
    (y : L.toSubmodule) :
    toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a (L.toRepresentation g y) =
      (a • L).toRepresentation g
        (toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a y) := by
  -- Compare both subtype elements after forgetting down to the ambient module `E`.
  ext1
  rw [StableLattice.toSubmoduleEquivSmul_apply_coe,
    StableLattice.toRepresentation_apply_coe,
    StableLattice.toRepresentation_apply_coe,
    StableLattice.toSubmoduleEquivSmul_apply_coe]
  exact ((ρ g).map_smul (a : K) (y : E)).symm

/-- Helper for Theorem 15-15.2-2: the reduction representations of homothetic stable lattices are
isomorphic as `k[G]`-representations. -/
noncomputable def reductionRepresentationEquivOfSmul
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    L.reductionRepresentation.Equiv (a • L).reductionRepresentation :=
  Representation.Equiv.mk
    (StableLattice.reductionEquivSmul (A := A) (K := K) (ρ := ρ) L a) fun g ↦ by
      apply LinearMap.ext
      intro x
      rcases Submodule.Quotient.mk_surjective L.maximalIdealSubmodule x with ⟨y, rfl⟩
      -- Evaluate the intertwining identity on represented quotient classes and compare the two
      -- ambient vectors upstairs in `E`.
      rw [LinearMap.comp_apply, LinearMap.comp_apply,
        StableLattice.reductionRepresentation_apply_mk]
      change
        StableLattice.reductionEquivSmul (A := A) (K := K) (ρ := ρ) L a
            (Submodule.Quotient.mk ((L.toRepresentation g) y)) =
          ((a • L).reductionRepresentation g)
            (StableLattice.reductionEquivSmul (A := A) (K := K) (ρ := ρ) L a
              (Submodule.Quotient.mk y))
      rw [StableLattice.reductionEquivSmul_apply_mk,
        StableLattice.reductionEquivSmul_apply_mk,
        StableLattice.toSubmoduleEquivSmul_comm (A := A) (K := K) (ρ := ρ) L a g y]
      exact
        (StableLattice.reductionRepresentation_apply_mk
          (L := a • L) g
          ((StableLattice.toSubmoduleEquivSmul (A := A) (K := K) (ρ := ρ) L a) y)).symm

/-- Helper for Theorem 15-15.2-2: after bundling the reductions as finite-dimensional
representations, homothetic stable lattices become isomorphic in `FDRep k G`. -/
theorem reductionRepresentationEquivSmul
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    Nonempty (FDRep.of L.reductionRepresentation ≅ FDRep.of (a • L).reductionRepresentation) := by
  -- Rebundle the representation equivalence through the canonical `FDRep` owner.
  exact ⟨Representation.Equiv.toFDRepIso
    (StableLattice.reductionRepresentationEquivOfSmul (A := A) (K := K) (ρ := ρ) L a)⟩

/-- Helper for Theorem 15-15.2-2: rescaling a stable lattice by a field unit does not change the
Grothendieck class of its reduction. -/
theorem reduction_grothendieckClass_eq_of_smul
    (ρ : Representation K G E) (L : StableLattice A ρ) (a : Kˣ) :
    [FDRep.of L.reductionRepresentation]₀ = [FDRep.of (a • L).reductionRepresentation]₀ := by
  -- Transport the class equality across the bundled isomorphism from the previous helper.
  exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G)
    (reductionRepresentationEquivSmul (A := A) (K := K) (ρ := ρ) L a)

omit [IsLocalRing A] in
/-- Helper for Theorem 15-15.2-2: after clearing finitely many denominator coordinates, some
homothetic copy of one stable lattice is contained in the other. -/
theorem exists_smul_le_of_lattices
    (ρ : Representation K G E) (L₁ L₂ : StableLattice A ρ) :
    ∃ a : Kˣ, (a • L₂).toSubmodule ≤ L₁.toSubmodule := by
  classical
  let b₁ : Module.Basis (Module.Free.ChooseBasisIndex A L₁.toSubmodule) A L₁.toSubmodule :=
    Module.Free.chooseBasis A L₁.toSubmodule
  let e₁ : Module.Basis (Module.Free.ChooseBasisIndex A L₁.toSubmodule) K E :=
    b₁.extendOfIsLattice K
  let b₂ : Module.Basis (Module.Free.ChooseBasisIndex A L₂.toSubmodule) A L₂.toSubmodule :=
    Module.Free.chooseBasis A L₂.toSubmodule
  let coeff :
      Module.Free.ChooseBasisIndex A L₂.toSubmodule ×
          Module.Free.ChooseBasisIndex A L₁.toSubmodule → K :=
    fun ij ↦ e₁.repr ((b₂ ij.1 : L₂.toSubmodule) : E) ij.2
  -- Clear the finitely many coefficient denominators that describe the basis of `L₂`
  -- in the `K`-basis induced from `L₁`.
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors A) coeff
  let a : Kˣ := (IsLocalization.map_units K d).unit
  refine ⟨a, ?_⟩
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  let yL₂ : L₂.toSubmodule := ⟨y, hy⟩
  change (algebraMap A K d) • (yL₂ : E) ∈ L₁.toSubmodule
  have hbasis_mem (i : Module.Free.ChooseBasisIndex A L₂.toSubmodule) :
      (algebraMap A K d) • ((b₂ i : L₂.toSubmodule) : E) ∈ L₁.toSubmodule := by
    let c : Module.Free.ChooseBasisIndex A L₁.toSubmodule → A :=
      fun j ↦ Classical.choose (hd (i, j))
    let z : L₁.toSubmodule := ∑ j, c j • b₁ j
    -- Reassemble the cleared coefficients along the `A`-basis of `L₁`.
    have hz : ((z : L₁.toSubmodule) : E) = (algebraMap A K d) • ((b₂ i : L₂.toSubmodule) : E) := by
      calc
        ((z : L₁.toSubmodule) : E)
            = ∑ j, (algebraMap A K (c j)) • (((b₁ j : L₁.toSubmodule) : E)) := by
                simp [z, c]
        _ = ∑ j, e₁.repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))) j • e₁ j := by
              apply Finset.sum_congr rfl
              intro j _
              have hc : algebraMap A K (c j) =
                  e₁.repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))) j := by
                calc
                  algebraMap A K (c j) = (algebraMap A K d) * coeff (i, j) := by
                    simpa [c, Algebra.smul_def] using (Classical.choose_spec (hd (i, j)))
                  _ = e₁.repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))) j := by
                    simpa [coeff, Algebra.smul_def] using
                      ((congrArg (fun f => f j)
                        (LinearEquiv.map_smul e₁.repr (algebraMap A K d)
                          (((b₂ i : L₂.toSubmodule) : E)))).symm)
              simpa [e₁, Module.Basis.extendOfIsLattice_apply] using
                congrArg (fun t => t • (((b₁ j : L₁.toSubmodule) : E))) hc
        _ = (algebraMap A K d) • ((b₂ i : L₂.toSubmodule) : E) := by
              simpa [e₁, Module.Basis.extendOfIsLattice_apply] using
                (e₁.sum_repr ((algebraMap A K d) • (((b₂ i : L₂.toSubmodule) : E))))
    exact hz ▸ z.property
  have hy_expand_sub : (∑ i, (b₂.repr yL₂ i : A) • b₂ i : L₂.toSubmodule) = yL₂ := by
    simpa using b₂.sum_repr yL₂
  -- Expand `y` in the `A`-basis of `L₂` and use the basiswise containment just proved.
  rw [← hy_expand_sub]
  change (algebraMap A K d) •
        (((∑ i, (b₂.repr yL₂ i : A) • b₂ i : L₂.toSubmodule) : L₂.toSubmodule) : E) ∈
      L₁.toSubmodule
  simp_rw [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ ?_
  intro i _
  simpa [smul_smul, mul_comm] using
    L₁.toSubmodule.smul_mem (b₂.repr yL₂ i) (hbasis_mem i)

/-- Helper for Theorem 15-15.2-2: if one stable lattice is contained in another, then some power
of the maximal ideal sends the larger lattice into the smaller one. -/
theorem exists_maximalIdeal_pow_le_of_le
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    ∃ n : ℕ, (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ≤ L₂.toSubmodule := by
  classical
  by_cases hsub : Subsingleton L₁.toSubmodule
  · -- If the larger lattice is trivial, then both lattices are zero and the claim is immediate.
    have hL₁bot : L₁.toSubmodule = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      exact congrArg Subtype.val (hsub.elim ⟨x, hx⟩ 0)
    have hL₂bot : L₂.toSubmodule = ⊥ := by
      apply le_antisymm
      · exact h21.trans hL₁bot.le
      · exact bot_le
    use 0
    simp [hL₁bot, hL₂bot, Ideal.one_eq_top]
  · -- First clear denominators in the reverse inclusion `L₁ → L₂`.
    obtain ⟨a, ha⟩ := exists_smul_le_of_lattices (A := A) (K := K) (ρ := ρ) L₂ L₁
    obtain ⟨x, y, hy, hfrac⟩ := IsFractionRing.div_surjective A (a : K)
    have hy0 : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
    have hy0K : (algebraMap A K y : K) ≠ 0 := by
      exact IsFractionRing.to_map_eq_zero_iff.not.mpr hy0
    have hx0K : (algebraMap A K x : K) ≠ 0 := by
      intro hx0
      apply Units.ne_zero a
      rw [← hfrac, hx0, zero_div]
    have hx0 : x ≠ 0 := by
      exact IsFractionRing.to_map_eq_zero_iff.not.mp hx0K
    have hx_le : x • L₁.toSubmodule ≤ L₂.toSubmodule := by
      intro w hw
      rcases hw with ⟨z, hz, rfl⟩
      -- Rewrite the homothety scalar as `x / y` and clear the denominator by the
      -- `A`-submodule structure on `L₂`.
      have hz' : ((algebraMap A K x / algebraMap A K y : K) • z) ∈ L₂.toSubmodule := by
        have hsmul_mem : ((algebraMap A K x / algebraMap A K y : K) • z) ∈
            (a • L₁).toSubmodule := by
          rw [hfrac]
          exact ⟨z, hz, rfl⟩
        exact ha hsmul_mem
      have hyhz' : (y : A) • ((algebraMap A K x / algebraMap A K y : K) • z) ∈
          L₂.toSubmodule := by
        exact L₂.toSubmodule.smul_mem y hz'
      have hyhz'' :
          (((algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y)) : K) • z ∈
            L₂.toSubmodule := by
        have hs :
            (y : A) • ((algebraMap A K x / algebraMap A K y : K) • z) =
              (((algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y)) : K) • z := by
          calc
            (y : A) • ((algebraMap A K x / algebraMap A K y : K) • z) =
                ((y • (algebraMap A K x / algebraMap A K y : K)) • z) := by
                  symm
                  exact smul_assoc y (algebraMap A K x / algebraMap A K y : K) z
            _ =
                (((algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y)) : K) • z := by
                  rw [Algebra.smul_def, mul_smul]
        simpa [hs] using hyhz'
      have hmul :
          (algebraMap A K y : K) * (algebraMap A K x / algebraMap A K y) =
            algebraMap A K x := by
        field_simp [hy0K]
      simpa [hmul] using hyhz''
    -- In a DVR, the principal ideal `(x)` is a power of the maximal ideal.
    have hspan_le : (Ideal.span {x} : Ideal A) • L₁.toSubmodule ≤ L₂.toSubmodule := by
      simpa [Submodule.ideal_span_singleton_smul] using hx_le
    obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal A
      (inferInstance : (IsLocalRing.maximalIdeal A).IsPrincipal)
      (Ideal.span {x})
      (mt Ideal.span_singleton_eq_bot.mp hx0)
    use n
    simpa [hn] using hspan_le

end StableLattice

/-- Helper for Theorem 15-15.2-2: repackage a finite-dimensional `k[G]`-module as an object of
`FDRep k G` using `Representation.ofModule'`. -/
abbrev fdRepOfModule
    (M : Type u) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M] : FDRep k G :=
  FDRep.of (@Representation.ofModule' k G inferInstance inferInstance M
    inferInstance inferInstance inferInstance inferInstance)

/-- Helper for Theorem 15-15.2-2: in `R₀[k](G)`, the class of a finite-dimensional `k[G]`-module
viewed through `Representation.ofModule'` splits as the sum of the classes of any submodule and
its quotient. -/
theorem finiteRepGrothendieckClass_ofModule_eq_submodule_add_quotient
    (M : Type u) [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    [Module (MonoidAlgebra k G) M] [IsScalarTower k (MonoidAlgebra k G) M]
    (N : Submodule (MonoidAlgebra k G) M)
    [FiniteDimensional k N] [FiniteDimensional k (M ⧸ N)] :
    let X₁ : FDRep k G := fdRepOfModule N
    let X₂ : FDRep k G := fdRepOfModule M
    let X₃ : FDRep k G := fdRepOfModule (M ⧸ N)
    [X₂]₀ = [X₁]₀ + [X₃]₀ := by
  dsimp
  -- Build the canonical short complex `0 → N → M → M ⧸ N → 0` in `FDRep k G`.
  let X₁ : FDRep k G := fdRepOfModule N
  let X₂ : FDRep k G := fdRepOfModule M
  let X₃ : FDRep k G := fdRepOfModule (M ⧸ N)
  let fRep :
      ((CategoryTheory.forget₂ (FDRep k G) (Rep k G)).obj X₁ ⟶
        (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).obj X₂) :=
    Rep.ofHom ⟨N.subtype.restrictScalars k, fun g => by
      ext x
      rfl⟩
  let gRep :
      ((CategoryTheory.forget₂ (FDRep k G) (Rep k G)).obj X₂ ⟶
        (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).obj X₃) :=
    Rep.ofHom ⟨N.mkQ.restrictScalars k, fun g => by
      ext x
      rfl⟩
  let f : X₁ ⟶ X₂ := (FDRep.forget₂HomLinearEquiv X₁ X₂) fRep
  let g : X₂ ⟶ X₃ := (FDRep.forget₂HomLinearEquiv X₂ X₃) gRep
  have hf : (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).map f = fRep := by
    change (FDRep.forget₂HomLinearEquiv X₁ X₂).symm
        ((FDRep.forget₂HomLinearEquiv X₁ X₂) fRep) = fRep
    exact (FDRep.forget₂HomLinearEquiv X₁ X₂).left_inv fRep
  have hg : (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).map g = gRep := by
    change (FDRep.forget₂HomLinearEquiv X₂ X₃).symm
        ((FDRep.forget₂HomLinearEquiv X₂ X₃) gRep) = gRep
    exact (FDRep.forget₂HomLinearEquiv X₂ X₃).left_inv gRep
  let S : ShortComplex (FDRep k G) := ShortComplex.mk f g (by
    apply (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).map_injective
    rw [Functor.map_comp, hf, hg]
    ext x
    change N.mkQ (N.subtype x) = 0
    simp)
  let SRep : ShortComplex (Rep k G) := ShortComplex.mk fRep gRep (by
    ext x
    change N.mkQ (N.subtype x) = 0
    simp)
  have hMod : (SRep.map (CategoryTheory.forget₂ (Rep k G) (ModuleCat k))).ShortExact := by
    -- Forgetting to `ModuleCat k` turns the sequence into the standard quotient exact sequence.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · rw [ShortComplex.moduleCat_exact_iff]
      intro x hx
      refine ⟨⟨x, ?_⟩, rfl⟩
      change N.mkQ x = 0 at hx
      simpa using hx
    · rw [ModuleCat.mono_iff_injective]
      intro x y hxy
      exact Subtype.ext hxy
    · rw [ModuleCat.epi_iff_surjective]
      intro x
      obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective N x
      exact ⟨y, rfl⟩
  have hRep' : SRep.ShortExact := by
    -- Reflect exactness from `ModuleCat k` back to `Rep k G`.
    apply (CategoryTheory.ShortExact.shortExact_map_iff
      (S := SRep) (F := CategoryTheory.forget₂ (Rep k G) (ModuleCat k))).1
    simpa using hMod
  have hRep : (S.map (CategoryTheory.forget₂ (FDRep k G) (Rep k G))).ShortExact := by
    -- The `Rep`-image of the bundled short complex is definitionally the same sequence.
    simpa [S, SRep, hf, hg] using hRep'
  have hS : S.ShortExact := by
    -- Reflect exactness, mono, and epi back to `FDRep k G`.
    refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
    · exact
        ((S.exact_map_iff_of_faithful (CategoryTheory.forget₂ (FDRep k G) (Rep k G))).1
          hRep.exact)
    · exact (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).mono_of_mono_map hRep.mono_f
    · exact (CategoryTheory.forget₂ (FDRep k G) (Rep k G)).epi_of_epi_map hRep.epi_g
  -- Apply the defining Grothendieck relation to the canonical short exact sequence.
  have hrelation :=
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G) S hS
  simpa [S, X₁, X₂, X₃] using hrelation

namespace StableLattice

local notation "𝔪" => IsLocalRing.maximalIdeal A

/-- Helper for Theorem 15-15.2-2: the induction-step lattice
`(𝔪_A ^ n) • L₁ + L₂` is again a stable lattice. -/
noncomputable def maximalIdealPowSupStableLattice
    (ρ : Representation K G E) (L₁ L₂ : StableLattice A ρ) (n : ℕ) :
    StableLattice A ρ :=
  { toSubmodule := (𝔪 ^ n) • L₁.toSubmodule ⊔ L₂.toSubmodule
    apply_mem_toSubmodule := by
      intro g x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
      -- Each summand is preserved by the ambient `G`-action, so their sum stays in the supremum.
      have hy' : ((Representation.restrictScalars A ρ) g) y ∈ (𝔪 ^ n) • L₁.toSubmodule := by
        -- Stability of the ideal multiple follows by expanding membership in `𝔪 ^ n • L₁`.
        refine Submodule.smul_induction_on hy ?_ ?_
        · intro a ha w hw
          simpa [Representation.restrictScalars_apply] using
            Submodule.smul_mem_smul ha (L₁.apply_mem_toSubmodule g hw)
        · intro y' z' hy'' hz''
          simpa [Representation.restrictScalars_apply, map_add] using add_mem hy'' hz''
      have hz' : ((Representation.restrictScalars A ρ) g) z ∈ L₂.toSubmodule :=
        L₂.apply_mem_toSubmodule g hz
      simpa [Representation.restrictScalars_apply, map_add] using
        add_mem (Submodule.mem_sup_left hy') (Submodule.mem_sup_right hz')
    isLattice := by
      -- The new lattice contains `L₂`, and it is finitely generated as a supremum of finitely
      -- generated submodules.
      have hmFG : (𝔪 : Ideal A).FG := by
        rw [← Ideal.span_singleton_generator 𝔪]
        exact Submodule.fg_span (Set.finite_singleton _)
      have hfgIdeal : (𝔪 ^ n).FG := by
        exact Ideal.FG.pow (n := n) hmFG
      have hfgSmul : ((𝔪 ^ n) • L₁.toSubmodule).FG :=
        Submodule.FG.smul hfgIdeal (Submodule.IsLattice.fg (A := K) (M := L₁.toSubmodule))
      exact
        Submodule.IsLattice.of_le_of_isLattice_of_fg K le_sup_right
          (Submodule.FG.sup hfgSmul (Submodule.IsLattice.fg (A := K) (M := L₂.toSubmodule))) }

/-- Helper for Theorem 15-15.2-2: the induction-step lattice has the expected underlying
submodule. -/
@[simp] theorem maximalIdealPowSupStableLattice_toSubmodule
    (ρ : Representation K G E) (L₁ L₂ : StableLattice A ρ) (n : ℕ) :
    (maximalIdealPowSupStableLattice (A := A) (K := K) (ρ := ρ) L₁ L₂ n).toSubmodule =
      (𝔪 ^ n) • L₁.toSubmodule ⊔ L₂.toSubmodule :=
  rfl

/-- Helper for Theorem 15-15.2-2: if `L₂ ≤ L₁`, then the induction-step lattice also lies in
`L₁`. -/
theorem maximalIdealPowSupStableLattice_le_left
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ} {n : ℕ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    (maximalIdealPowSupStableLattice (A := A) (K := K) (ρ := ρ) L₁ L₂ n).toSubmodule ≤
      L₁.toSubmodule := by
  -- Each summand of `(𝔪 ^ n) • L₁ + L₂` already lies in `L₁`.
  rw [maximalIdealPowSupStableLattice_toSubmodule]
  refine sup_le ?_ h21
  exact Submodule.smul_le.2 fun a ha x hx ↦ L₁.toSubmodule.smul_mem a hx

/-- Helper for Theorem 15-15.2-2: under the power bound
`𝔪_A ^ (n + 1) • L₁ ≤ L₂`, multiplying the induction-step lattice by `𝔪_A` lands inside `L₂`. -/
theorem maximalIdealPowSupStableLattice_maximalIdeal_le
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ} {n : ℕ}
    (hpow : (𝔪 ^ (n + 1)) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    𝔪 •
        (maximalIdealPowSupStableLattice (A := A) (K := K) (ρ := ρ) L₁ L₂ n).toSubmodule ≤
      L₂.toSubmodule := by
  -- Distribute `𝔪` across the defining supremum and use the assumed `(n + 1)`-power bound on
  -- the first summand.
  rw [maximalIdealPowSupStableLattice_toSubmodule, Submodule.smul_sup]
  refine sup_le ?_ ?_
  · have hpow' : (𝔪 * 𝔪 ^ n) • L₁.toSubmodule ≤ L₂.toSubmodule := by
      simpa [pow_succ, mul_comm] using hpow
    have hsmul : (𝔪 * 𝔪 ^ n) • L₁.toSubmodule = 𝔪 • 𝔪 ^ n • L₁.toSubmodule := by
      simpa using (Submodule.mul_smul (I := 𝔪) (J := 𝔪 ^ n) (N := L₁.toSubmodule))
    -- Rewrite the iterated submodule scalar action into ideal multiplication.
    simpa [hsmul] using hpow'
  · exact Submodule.smul_le.2 fun a ha x hx ↦ L₂.toSubmodule.smul_mem a hx

end StableLattice

/-- Helper for Theorem 15-15.2-2: in the nested case `𝔪_A • L₁ ≤ L₂ ≤ L₁`, the maximal-ideal
submodule of `L₁` already lies in the image of the inclusion `L₂ ↪ L₁`. -/
theorem maximalIdealSubmodule_le_nested_range
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    L₁.maximalIdealSubmodule ≤ LinearMap.range (Submodule.inclusion h21) := by
  -- Every generator of `𝔪_A L₁` already lands in `L₂`, so it is represented by the nested
  -- inclusion `L₂ ↪ L₁`.
  intro x hx
  rw [StableLattice.maximalIdealSubmodule] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    -- Use the assumed containment `𝔪_A L₁ ≤ L₂` on a pure generator `a • y`.
    refine ⟨⟨a • y, h𝔪 ?_⟩, ?_⟩
    · exact Submodule.smul_mem_smul ha y.property
    · ext
      rfl
  · intro y z hy hz
    -- The inclusion range is a submodule, hence closed under addition.
    exact add_mem hy hz

/-- Helper for Theorem 15-15.2-2: in the nested case `𝔪_A • L₁ ≤ L₂ ≤ L₁`, quotienting
`L₁ / 𝔪_A L₁` by the image of `L₂` recovers `L₁ / L₂`. -/
noncomputable abbrev reduction_quotient_by_nested_image_equiv
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    (L₁.reduction ⧸ Submodule.map L₁.maximalIdealSubmodule.mkQ
      (LinearMap.range (Submodule.inclusion h21))) ≃ₗ[A]
      (L₁.toSubmodule ⧸ LinearMap.range (Submodule.inclusion h21)) :=
  -- Apply Noether's third isomorphism theorem inside the lattice `L₁`.
  Submodule.quotientQuotientEquivQuotient
    L₁.maximalIdealSubmodule
    (LinearMap.range (Submodule.inclusion h21))
    (maximalIdealSubmodule_le_nested_range
      (A := A) (K := K) (G := G) (ρ := ρ) (L₁ := L₁) (L₂ := L₂) h21 h𝔪)

/-- Helper for Theorem 15-15.2-2: in the same nested case, the maximal-ideal submodule of `L₂`
lies in the image of the inclusion `(𝔪_A • L₁) ↪ L₂`. -/
theorem maximalIdealSubmodule_le_maximalIdeal_range
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    L₂.maximalIdealSubmodule ≤ LinearMap.range (Submodule.inclusion h𝔪) := by
  -- Every generator of `𝔪_A L₂` is also in `𝔪_A L₁`, so it comes from the nested maximal-ideal
  -- inclusion `(𝔪_A • L₁) ↪ L₂`.
  intro x hx
  rw [StableLattice.maximalIdealSubmodule] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    -- The ambient inclusion `L₂ ≤ L₁` upgrades the generator `a • y` to a point of `𝔪_A L₁`.
    refine ⟨⟨a • y, ?_⟩, ?_⟩
    · exact Submodule.smul_mem_smul ha (h21 y.property)
    · ext
      rfl
  · intro y z hy hz
    -- Again, the range of a linear map is an additive submodule.
    exact add_mem hy hz

/-- Helper for Theorem 15-15.2-2: in the nested case `𝔪_A • L₁ ≤ L₂ ≤ L₁`, quotienting
`L₂ / 𝔪_A L₂` by the image of `𝔪_A • L₁` recovers `L₂ / (𝔪_A • L₁)`. -/
noncomputable abbrev reduction_quotient_by_maximalIdeal_image_equiv
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    (L₂.reduction ⧸ Submodule.map L₂.maximalIdealSubmodule.mkQ
      (LinearMap.range (Submodule.inclusion h𝔪))) ≃ₗ[A]
      (L₂.toSubmodule ⧸ LinearMap.range (Submodule.inclusion h𝔪)) :=
  -- Apply the same third-isomorphism theorem inside the smaller lattice `L₂`.
  Submodule.quotientQuotientEquivQuotient
    L₂.maximalIdealSubmodule
    (LinearMap.range (Submodule.inclusion h𝔪))
    (maximalIdealSubmodule_le_maximalIdeal_range
      (A := A) (K := K) (G := G) (ρ := ρ) (L₁ := L₁) (L₂ := L₂) h21 h𝔪)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the maximal-ideal submodule of the smaller lattice maps into
the maximal-ideal submodule of the larger lattice under the nested inclusion. -/
theorem maximalIdealSubmodule_le_comap_inclusion
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    L₂.maximalIdealSubmodule ≤
      Submodule.comap (Submodule.inclusion h21) L₁.maximalIdealSubmodule := by
  -- Rewrite membership in `𝔪_A • ⊤` by generators and transport each generator across the
  -- lattice inclusion.
  intro x hx
  change (Submodule.inclusion h21 x : L₁.toSubmodule) ∈ L₁.maximalIdealSubmodule
  rw [StableLattice.maximalIdealSubmodule] at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    exact Submodule.smul_mem_smul ha
      (show (Submodule.inclusion h21 y : L₁.toSubmodule) ∈ ⊤ by trivial)
  · intro y z hy hz
    exact add_mem hy hz

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the nested inclusion `L₂ ⊆ L₁` induces the canonical map on
reductions modulo `𝔪_A`. -/
noncomputable def reductionNestedMapA
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    L₂.reduction →ₗ[A] L₁.reduction :=
  Submodule.mapQ L₂.maximalIdealSubmodule L₁.maximalIdealSubmodule
    (Submodule.inclusion h21)
    (maximalIdealSubmodule_le_comap_inclusion
      (A := A) (K := K) (G := G) (ρ := ρ) h21)

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: on represented quotient classes, the nested reduction map is
the obvious quotient class of the inclusion `L₂ ↪ L₁`. -/
@[simp] theorem reductionNestedMapA_apply_mk
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) (x : L₂.toSubmodule) :
    reductionNestedMapA (A := A) (K := K) (ρ := ρ) h21 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion h21 x) := by
  -- This is just the defining formula of `Submodule.mapQ` on quotient representatives.
  rfl

omit [IsDomain A] [IsDiscreteValuationRing A] [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: a point of `𝔪_A L` inside the subtype lattice also lies in the
ambient ideal multiple `𝔪_A • L`. -/
theorem coe_mem_maximalIdealSubmodule
    (ρ : Representation K G E) {L : StableLattice A ρ}
    {x : L.toSubmodule} (hx : x ∈ L.maximalIdealSubmodule) :
    ((x : L.toSubmodule) : E) ∈ (IsLocalRing.maximalIdeal A) • L.toSubmodule := by
  -- Expand membership in `𝔪_A • ⊤` inside the subtype and forget back to the ambient module.
  rw [StableLattice.maximalIdealSubmodule] at hx
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    exact Submodule.smul_mem_smul ha y.property
  · intro y z hy hz
    exact add_mem hy hz

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: multiplying a lattice vector by a generator of `𝔪_A` lands in
the nested lattice `L₂` once `𝔪_A L₁ ≤ L₂`. -/
theorem mul_generator_mem_nested_lattice
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule)
    (x : L₁.toSubmodule) :
    (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) • (x : E)) ∈ L₂.toSubmodule := by
  -- The chosen generator lies in `𝔪_A`, so its multiple lies in `𝔪_A L₁`, hence in `L₂`.
  exact h𝔪 <|
    Submodule.smul_mem_smul
      (Submodule.IsPrincipal.generator_mem (IsLocalRing.maximalIdeal A))
      x.property

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: addition is preserved by multiplication with a fixed generator
of `𝔪_A` when viewed as a map `L₁ → L₂`. -/
theorem mulGeneratorToNestedLattice_map_add
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule)
    (x y : L₁.toSubmodule) :
    (⟨Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) • ((x + y : L₁.toSubmodule) : E),
        mul_generator_mem_nested_lattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 (x + y)⟩ :
      L₂.toSubmodule) =
      ⟨Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) • (x : E),
        mul_generator_mem_nested_lattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x⟩ +
      ⟨Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) • (y : E),
        mul_generator_mem_nested_lattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 y⟩ := by
  -- Forget to `E`, where the claim is the distributivity of scalar multiplication.
  ext
  simp [smul_add]

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: scalar multiplication in `A` commutes with multiplication by the
chosen generator of `𝔪_A` on nested lattices. -/
theorem mulGeneratorToNestedLattice_map_smul
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule)
    (a : A) (x : L₁.toSubmodule) :
    (⟨Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) • ((a • x : L₁.toSubmodule) : E),
        mul_generator_mem_nested_lattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 (a • x)⟩ :
      L₂.toSubmodule) =
      a •
        (⟨Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) • (x : E),
            mul_generator_mem_nested_lattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x⟩ :
          L₂.toSubmodule) := by
  -- Forget again to the ambient module `E` and commute the two `A`-scalars.
  ext
  simp [smul_smul, mul_comm]

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: multiplication by a chosen generator of `𝔪_A` defines an
`A`-linear map from `L₁` to the nested lattice `L₂`. -/
noncomputable def mulGeneratorToNestedLattice
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    L₁.toSubmodule →ₗ[A] L₂.toSubmodule :=
  { toFun := fun x ↦
      ⟨Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) • (x : E),
        mul_generator_mem_nested_lattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x⟩
    map_add' := mulGeneratorToNestedLattice_map_add
      (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
    map_smul' := mulGeneratorToNestedLattice_map_smul
      (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 }

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the generator-multiplication map kills the maximal-ideal
submodule of `L₁`, so it descends to reductions. -/
theorem maximalIdealSubmodule_le_ker_mulGeneratorToNestedLattice
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    L₁.maximalIdealSubmodule ≤
      LinearMap.ker
        (L₂.maximalIdealSubmodule.mkQ.comp
          (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪)) := by
  -- An element of `𝔪_A L₁` becomes a generator multiple of something already in `L₂`, hence lies
  -- in `𝔪_A L₂`.
  intro x hx
  simp only [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  rw [StableLattice.maximalIdealSubmodule]
  rw [Submodule.mem_smul_top_iff (IsLocalRing.maximalIdeal A) (N := L₂.toSubmodule)]
  exact Submodule.smul_mem_smul
    (Submodule.IsPrincipal.generator_mem (IsLocalRing.maximalIdeal A))
    (h𝔪 <| coe_mem_maximalIdealSubmodule (A := A) (K := K) (G := G) (ρ := ρ) hx)

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: multiplication by a generator of `𝔪_A` descends to the map
from `L₁ / 𝔪_A L₁` to `L₂ / 𝔪_A L₂`. -/
noncomputable def reductionGeneratorMapA
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    L₁.reduction →ₗ[A] L₂.reduction :=
  Submodule.liftQ L₁.maximalIdealSubmodule
    (L₂.maximalIdealSubmodule.mkQ.comp
      (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪))
    (maximalIdealSubmodule_le_ker_mulGeneratorToNestedLattice
      (A := A) (K := K) (G := G) (ρ := ρ) h𝔪)

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: on represented quotient classes, the generator map is exactly
the quotient class of the multiplied representative. -/
@[simp] theorem reductionGeneratorMapA_apply_mk
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule)
    (x : L₁.toSubmodule) :
    reductionGeneratorMapA (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x) := by
  -- This is the defining formula of the quotient lift on a represented class.
  rfl

omit [IsFractionRing A K] in
/-- Helper for Theorem 15-15.2-2: the descended generator map is linear over the residue field. -/
theorem reductionGeneratorMapA_smul_mk
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule)
    (a : A) (y : L₁.toSubmodule) :
    reductionGeneratorMapA (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
        (Submodule.Quotient.mk y : L₁.reduction)) =
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : IsLocalRing.ResidueField A) •
        reductionGeneratorMapA (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
          (Submodule.Quotient.mk y) := by
  -- This is the representative-level scalar formula for the descended generator map.
  simp [reductionGeneratorMapA, mulGeneratorToNestedLattice]

/-- Helper for Theorem 15-15.2-2: the nested reduction map is residue-field linear and
`G`-equivariant, so it is the canonical morphism `\bar E₂ → \bar E₁` in LinearRepresentations_Serre_1977's exact sequence. -/
noncomputable def reductionNestedMap
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) :
    L₂.reductionRepresentation.IntertwiningMap L₁.reductionRepresentation := by
  let f : L₂.reduction →ₗ[k] L₁.reduction :=
    { toFun := reductionNestedMapA (A := A) (K := K) (ρ := ρ) h21
      map_add' := (reductionNestedMapA (A := A) (K := K) (ρ := ρ) h21).map_add
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        -- Reduce the residue-field linearity claim to represented quotient classes.
        change
          reductionNestedMapA (A := A) (K := K) (ρ := ρ) h21
              ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : k) •
                (Submodule.Quotient.mk y : L₂.reduction)) = _
        rw [StableLattice.reduction_smul_mk (L := L₂) a y]
        rw [reductionNestedMapA_apply_mk]
        change
          (Submodule.Quotient.mk ((Submodule.inclusion h21) (a • y)) : L₁.reduction) =
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : k) •
              ((reductionNestedMapA (A := A) (K := K) (ρ := ρ) h21)
                (Submodule.Quotient.mk y))
        rw [reductionNestedMapA_apply_mk]
        rw [StableLattice.reduction_smul_mk (L := L₁) a ((Submodule.inclusion h21) y)]
        simpa using
          congrArg (fun z : L₁.toSubmodule =>
            (Submodule.Quotient.mk z : L₁.reduction))
            ((Submodule.inclusion h21).map_smul a y) }
  -- Compare both sides on represented quotient classes to prove equivariance.
  exact f.intertwiningMap_of_isIntertwiningMap
    L₂.reductionRepresentation L₁.reductionRepresentation fun g x ↦ by
      refine Quotient.inductionOn' x ?_
      intro y
      change
        reductionNestedMapA (A := A) (K := K) (ρ := ρ) h21
            (Submodule.Quotient.mk ((L₂.toRepresentation g) y)) =
          (L₁.reductionRepresentation g)
            (reductionNestedMapA (A := A) (K := K) (ρ := ρ) h21
              (Submodule.Quotient.mk y))
      rw [reductionNestedMapA_apply_mk,
        reductionNestedMapA_apply_mk,
        StableLattice.reductionRepresentation_apply_mk]
      rfl

/-- Helper for Theorem 15-15.2-2: on represented quotient classes, the bundled nested map is
still just the class of the lattice inclusion `L₂ ↪ L₁`. -/
@[simp] theorem reductionNestedMap_apply_mk
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule) (x : L₂.toSubmodule) :
    reductionNestedMap (A := A) (K := K) (G := G) (ρ := ρ) h21
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (Submodule.inclusion h21 x) := by
  -- The bundled map is defined from the same underlying quotient map as `reductionNestedMapA`.
  rfl

/-- Helper for Theorem 15-15.2-2: multiplication by the chosen generator of `𝔪_A` commutes with
the restricted `G`-action on the nested lattices. -/
theorem mulGeneratorToNestedLattice_comm
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule)
    (g : G) (x : L₁.toSubmodule) :
    mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
        (L₁.toRepresentation g x) =
      L₂.toRepresentation g
        (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x) := by
  -- Forget to the ambient module `E`, where this is the `A`-linearity of `ρ g`.
  ext
  simp [mulGeneratorToNestedLattice, StableLattice.toRepresentation_apply_coe,
    map_smul]

/-- Helper for Theorem 15-15.2-2: the generator-descended map is residue-field linear and
`G`-equivariant, hence gives LinearRepresentations_Serre_1977's morphism `\bar E₁ → \bar E₂`. -/
noncomputable def reductionGeneratorMap
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    L₁.reductionRepresentation.IntertwiningMap L₂.reductionRepresentation := by
  let f : L₁.reduction →ₗ[k] L₂.reduction :=
    { toFun := reductionGeneratorMapA (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
      map_add' := (reductionGeneratorMapA (A := A) (K := K) (G := G) (ρ := ρ) h𝔪).map_add
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        -- The residue-field scalar action is already computed on representatives.
        exact reductionGeneratorMapA_smul_mk
          (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 a y }
  -- Check equivariance on represented quotient classes, where the generator map is explicit.
  exact f.intertwiningMap_of_isIntertwiningMap
    L₁.reductionRepresentation L₂.reductionRepresentation fun g x ↦ by
      refine Quotient.inductionOn' x ?_
      intro y
      change
        reductionGeneratorMapA (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
            (Submodule.Quotient.mk ((L₁.toRepresentation g) y)) =
          (L₂.reductionRepresentation g)
            (reductionGeneratorMapA (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
              (Submodule.Quotient.mk y))
      rw [reductionGeneratorMapA_apply_mk,
        reductionGeneratorMapA_apply_mk,
        StableLattice.reductionRepresentation_apply_mk,
        mulGeneratorToNestedLattice_comm (A := A) (K := K) (G := G) (ρ := ρ) h𝔪]

/-- Helper for Theorem 15-15.2-2: on represented quotient classes, the bundled generator map is
the quotient class of the generator-multiplication map upstairs. -/
@[simp] theorem reductionGeneratorMap_apply_mk
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule)
    (x : L₁.toSubmodule) :
    reductionGeneratorMap (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x) := by
  -- The bundled generator map has the same underlying quotient map as `reductionGeneratorMapA`.
  rfl

/-- Helper for Theorem 15-15.2-2: a surjective intertwining map contributes the usual
Grothendieck-group decomposition by its kernel. -/
theorem finiteRepGrothendieckClass_eq_kernel_add_target_of_surjective_intertwining
    {V W : Type u}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    [FiniteDimensional k V] [FiniteDimensional k W]
    (f : IntertwiningMap ρ σ)
    (hf : Function.Surjective f.toLinearMap) :
    [FDRep.of ρ]₀ = [FDRep.of (V := ↥f.ker.toSubmodule) f.ker.toRepresentation]₀ + [FDRep.of σ]₀ := by
  letI : Module.Finite k ↥f.ker.toSubmodule := by
    infer_instance
  let K' : FDRep k G := FDRep.of (V := ↥f.ker.toSubmodule) f.ker.toRepresentation
  let fRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ) ⟶
        (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of σ)) :=
    Rep.ofHom f
  let iRep :
      ((forget₂ (FDRep k G) (Rep k G)).obj K' ⟶
        (forget₂ (FDRep k G) (Rep k G)).obj (FDRep.of ρ)) :=
    Rep.ofHom <|
      f.ker.toSubmodule.subtype.intertwiningMap_of_isIntertwiningMap
        f.ker.toRepresentation ρ (fun g x ↦ rfl)
  let i : K' ⟶ FDRep.of ρ := (FDRep.forget₂HomLinearEquiv K' (FDRep.of ρ)) iRep
  let g : FDRep.of ρ ⟶ FDRep.of σ := (FDRep.forget₂HomLinearEquiv (FDRep.of ρ) (FDRep.of σ)) fRep
  let T : ShortComplex (FDRep k G) := ShortComplex.mk i g (by
    -- The kernel inclusion followed by the quotient map is zero by construction.
    apply (forget₂ (FDRep k G) (Rep k G)).map_injective
    ext x
    change f.toLinearMap (f.ker.toSubmodule.subtype x) = 0
    exact x.property)
  let TRep : ShortComplex (Rep k G) := ShortComplex.mk iRep fRep (by
    ext x
    change f.toLinearMap (f.ker.toSubmodule.subtype x) = 0
    exact x.property)
  have hRepMap : ((TRep.map (forget₂ (Rep k G) (ModuleCat k))).ShortExact) := by
    -- Forgetting to `ModuleCat k` gives the concrete short exact sequence `0 → ker(f) → ρ → σ → 0`.
    simpa [TRep, K', fRep, iRep] using
      (LinearMap.shortExact_shortComplexKer (f := f.toLinearMap) hf)
  have hRepShort : TRep.ShortExact := by
    -- Reflect module-level exactness back to `Rep k G`.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := TRep) (F := forget₂ (Rep k G) (ModuleCat k))).1 hRepMap
  have hRep : ((T.map (forget₂ (FDRep k G) (Rep k G))).ShortExact) := by
    -- The `Rep` short complex is definitionally the image of the `FDRep` short complex.
    simpa [T, TRep, K', i, g, fRep, iRep] using hRepShort
  have hT : T.ShortExact := by
    -- Reflect short exactness one last time to `FDRep k G`.
    exact
      (CategoryTheory.ShortExact.shortExact_map_iff
        (S := T) (F := forget₂ (FDRep k G) (Rep k G))).1 hRep
  -- The defining Grothendieck relation for this short exact sequence gives the claimed class split.
  simpa [T, K'] using
    finiteRepGrothendieckClass_middle_eq_left_add_right (L := k) (G := G) T hT

/-- Helper for Theorem 15-15.2-2: multiplication by a generator of the maximal ideal is
injective on the ambient `K`-vector space. -/
theorem maximalIdeal_generator_smul_injective
    : Function.Injective fun x : E ↦
        ((algebraMap A K (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)) : K) • x) := by
  let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
  have hmax_ne_bot : IsLocalRing.maximalIdeal A ≠ ⊥ := by
    simpa [ne_eq, ← IsLocalRing.isField_iff_maximalIdeal_eq] using
      (IsDiscreteValuationRing.not_isField A)
  have hπ0 : π ≠ 0 := by
    intro hπ
    exact hmax_ne_bot <|
      (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero (IsLocalRing.maximalIdeal A)).2 hπ
  have hπK0 : (algebraMap A K π : K) ≠ 0 :=
    IsFractionRing.to_map_eq_zero_iff.not.mpr hπ0
  exact smul_right_injective E hπK0

/-- Helper for Theorem 15-15.2-2: equal invariant submodules define isomorphic
subrepresentations. -/
theorem subrepresentation_equiv_of_toSubmodule_eq
    {V : Type u} [AddCommGroup V] [Module k V]
    {ρ : Representation k G V}
    {U W : Subrepresentation ρ}
    (hUW : U.toSubmodule = W.toSubmodule) :
    Nonempty (U.toRepresentation.Equiv W.toRepresentation) := by
  -- Turn equality of the underlying invariant submodules into literal equality of the bundled
  -- subrepresentations, then reuse the identity equivalence.
  have hEq : U = W := Subrepresentation.toSubmodule_injective hUW
  subst hEq
  exact ⟨Representation.Equiv.refl _⟩

/-- Helper for Theorem 15-15.2-2: in LinearRepresentations_Serre_1977's nested exact sequence, the kernel of
`\bar E₂ → \bar E₁` is exactly the image of the generator map `\bar E₁ → \bar E₂`. -/
theorem reductionNestedMap_ker_eq_reductionGeneratorMap_range
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    (reductionNestedMap (A := A) (K := K) (G := G) (ρ := ρ) h21).ker.toSubmodule =
      (reductionGeneratorMap (A := A) (K := K) (G := G) (ρ := ρ) h𝔪).range.toSubmodule := by
  -- Compare both submodules on represented quotient classes, so the two descended maps become
  -- the evident inclusion map and the evident generator-multiplication map.
  ext x
  constructor
  · intro hx
    simp only [IntertwiningMap.ker, LinearMap.mem_ker] at hx
    rcases Quotient.exists_rep x with ⟨x', rfl⟩
    have hx' : (Submodule.inclusion h21 x') ∈ L₁.maximalIdealSubmodule := by
      change (Submodule.Quotient.mk (Submodule.inclusion h21 x') : L₁.reduction) = 0 at hx
      exact (Submodule.Quotient.mk_eq_zero _).1 hx
    -- Rewrite the maximal-ideal condition as a generator multiple inside `L₁`.
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul] at hx'
    rcases hx' with ⟨y, hy, hxy⟩
    have hxyE :
        (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A) : A) • (y : E) =
          (x' : E) := by
      exact congrArg Subtype.val hxy
    have hrep :
        mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 y = x' := by
      ext
      simpa [mulGeneratorToNestedLattice] using hxyE
    simp only [IntertwiningMap.range, LinearMap.mem_range]
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    simpa [reductionGeneratorMap_apply_mk] using
      congrArg (fun z : L₂.toSubmodule => (Submodule.Quotient.mk z : L₂.reduction)) hrep
  · intro hx
    simp only [IntertwiningMap.range, LinearMap.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rcases Quotient.exists_rep y with ⟨y', rfl⟩
    simp only [IntertwiningMap.ker, LinearMap.mem_ker]
    -- The nested map kills every generator image because that image already lies in `𝔪_A L₁`.
    change (Submodule.Quotient.mk
      (Submodule.inclusion h21
        (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 y')) :
        L₁.reduction) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul]
    refine ⟨y', show y' ∈ (⊤ : Submodule A L₁.toSubmodule) by trivial, ?_⟩
    ext
    simp [mulGeneratorToNestedLattice]

/-- Helper for Theorem 15-15.2-2: in LinearRepresentations_Serre_1977's nested exact sequence, the kernel of the generator
map `\bar E₁ → \bar E₂` is exactly the image of `\bar E₂ → \bar E₁`. -/
theorem reductionGeneratorMap_ker_eq_reductionNestedMap_range
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    (reductionGeneratorMap (A := A) (K := K) (G := G) (ρ := ρ) h𝔪).ker.toSubmodule =
      (reductionNestedMap (A := A) (K := K) (G := G) (ρ := ρ) h21).range.toSubmodule := by
  -- Again compare both sides on represented quotient classes, but now the key step is to cancel
  -- the chosen generator in the ambient `K`-vector space.
  ext x
  constructor
  · intro hx
    simp only [IntertwiningMap.ker, LinearMap.mem_ker] at hx
    rcases Quotient.exists_rep x with ⟨x', rfl⟩
    have hx' :
        mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x' ∈
          L₂.maximalIdealSubmodule := by
      change (Submodule.Quotient.mk
        (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪 x') :
          L₂.reduction) = 0 at hx
      exact (Submodule.Quotient.mk_eq_zero _).1 hx
    -- Rewrite the maximal-ideal condition as a generator witness and then cancel that generator.
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul] at hx'
    rcases hx' with ⟨y, hy, hxy⟩
    have hxyE :
        ((algebraMap A K (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)) : K) •
            (y : E)) =
          ((algebraMap A K (Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)) : K) •
            (x' : E)) := by
      simpa using congrArg Subtype.val hxy
    have hcancel : (y : E) = (x' : E) := by
      exact maximalIdeal_generator_smul_injective (A := A) (K := K) (E := E) hxyE
    have hxL2 : (x' : E) ∈ L₂.toSubmodule := by
      simpa [hcancel] using y.property
    let x₂ : L₂.toSubmodule := ⟨x', hxL2⟩
    have hx₂ : (Submodule.inclusion h21 x₂ : L₁.toSubmodule) = x' := by
      ext
      rfl
    simp only [IntertwiningMap.range, LinearMap.mem_range]
    refine ⟨Submodule.Quotient.mk x₂, ?_⟩
    change (Submodule.Quotient.mk (Submodule.inclusion h21 x₂) : L₁.reduction) =
      Submodule.Quotient.mk x'
    rw [hx₂]
  · intro hx
    simp only [IntertwiningMap.range, LinearMap.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rcases Quotient.exists_rep y with ⟨y', rfl⟩
    simp only [IntertwiningMap.ker, LinearMap.mem_ker]
    -- A class coming from `L₂` is killed by the generator map because its image is already in
    -- `𝔪_A L₂`.
    change (Submodule.Quotient.mk
      (mulGeneratorToNestedLattice (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
        (Submodule.inclusion h21 y')) : L₂.reduction) = 0
    apply (Submodule.Quotient.mk_eq_zero _).2
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul]
    refine ⟨y', show y' ∈ (⊤ : Submodule A L₂.toSubmodule) by trivial, ?_⟩
    ext
    simp [mulGeneratorToNestedLattice]

/-- Helper for Theorem 15-15.2-2: in the special nested case `𝔪_A • L₁ ≤ L₂ ≤ L₁`, LinearRepresentations_Serre_1977's
five-term exact-sequence argument shows that the two reduction classes agree. -/
theorem reduction_grothendieckClass_eq_of_maximalIdeal_le
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ}
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (h𝔪 : (IsLocalRing.maximalIdeal A) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    [FDRep.of L₁.reductionRepresentation]₀ = [FDRep.of L₂.reductionRepresentation]₀ := by
  -- Route correction: instead of transporting separate quotient owners at the end, compare the
  -- two reductions through the exact sequence `0 → ker → source → range → 0` for the actual
  -- descended maps, then identify the crossed kernel/range terms directly.
  let f :=
    reductionNestedMap (A := A) (K := K) (G := G) (ρ := ρ) h21
  let g :=
    reductionGeneratorMap (A := A) (K := K) (G := G) (ρ := ρ) h𝔪
  let fr : L₂.reductionRepresentation.IntertwiningMap f.range.toRepresentation :=
    f.toLinearMap.rangeRestrict.intertwiningMap_of_isIntertwiningMap
      L₂.reductionRepresentation f.range.toRepresentation fun g' x ↦ by
        ext
        exact LinearMap.congr_fun (f.2 g') x
  let gr : L₁.reductionRepresentation.IntertwiningMap g.range.toRepresentation :=
    g.toLinearMap.rangeRestrict.intertwiningMap_of_isIntertwiningMap
      L₁.reductionRepresentation g.range.toRepresentation fun g' x ↦ by
        ext
        exact LinearMap.congr_fun (g.2 g') x
  have hfr :
      [FDRep.of L₂.reductionRepresentation]₀ =
        [FDRep.of (V := ↥fr.ker.toSubmodule) fr.ker.toRepresentation]₀ +
          [FDRep.of f.range.toRepresentation]₀ := by
    -- Split `\bar E₂` as the kernel of the surjection onto `im(f)` plus that image.
    exact finiteRepGrothendieckClass_eq_kernel_add_target_of_surjective_intertwining
      (A := A) (G := G) fr <|
        by simpa [fr] using LinearMap.surjective_rangeRestrict f.toLinearMap
  have hgr :
      [FDRep.of L₁.reductionRepresentation]₀ =
        [FDRep.of (V := ↥gr.ker.toSubmodule) gr.ker.toRepresentation]₀ +
          [FDRep.of g.range.toRepresentation]₀ := by
    -- Split `\bar E₁` in the same way using the surjection onto `im(g)`.
    exact finiteRepGrothendieckClass_eq_kernel_add_target_of_surjective_intertwining
      (A := A) (G := G) gr <|
        by simpa [gr] using LinearMap.surjective_rangeRestrict g.toLinearMap
  have hkerf : fr.ker.toSubmodule = f.ker.toSubmodule := by
    -- The range restriction does not change the kernel subrepresentation.
    ext x
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      ext
      exact hx
  have hkerg : gr.ker.toSubmodule = g.ker.toSubmodule := by
    -- The same owner-level kernel comparison holds for `gr`.
    ext x
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      ext
      exact hx
  have hfrkerIso :
      Nonempty (FDRep.of (V := ↥fr.ker.toSubmodule) fr.ker.toRepresentation ≅
        FDRep.of f.ker.toRepresentation) := by
    -- Transport the class term from `ker(fr)` back to the actual kernel `ker(f)`.
    exact ⟨Representation.Equiv.toFDRepIso
      (subrepresentation_equiv_of_toSubmodule_eq
        (A := A) (G := G) (U := fr.ker) (W := f.ker) hkerf).some⟩
  have hgrkerIso :
      Nonempty (FDRep.of (V := ↥gr.ker.toSubmodule) gr.ker.toRepresentation ≅
        FDRep.of g.ker.toRepresentation) := by
    -- Transport the other kernel term from `ker(gr)` back to `ker(g)`.
    exact ⟨Representation.Equiv.toFDRepIso
      (subrepresentation_equiv_of_toSubmodule_eq
        (A := A) (G := G) (U := gr.ker) (W := g.ker) hkerg).some⟩
  have hcross1 :
      Nonempty (FDRep.of g.ker.toRepresentation ≅ FDRep.of f.range.toRepresentation) := by
    -- LinearRepresentations_Serre_1977's second exactness identity identifies `ker(g)` with `im(f)`.
    exact ⟨Representation.Equiv.toFDRepIso
      (subrepresentation_equiv_of_toSubmodule_eq
        (A := A) (G := G) (U := g.ker) (W := f.range)
        (reductionGeneratorMap_ker_eq_reductionNestedMap_range
          (A := A) (K := K) (G := G) (ρ := ρ) h21 h𝔪)).some⟩
  have hcross2 :
      Nonempty (FDRep.of f.ker.toRepresentation ≅ FDRep.of g.range.toRepresentation) := by
    -- LinearRepresentations_Serre_1977's first exactness identity identifies `ker(f)` with `im(g)`.
    exact ⟨Representation.Equiv.toFDRepIso
      (subrepresentation_equiv_of_toSubmodule_eq
        (A := A) (G := G) (U := f.ker) (W := g.range)
        (reductionNestedMap_ker_eq_reductionGeneratorMap_range
          (A := A) (K := K) (G := G) (ρ := ρ) h21 h𝔪)).some⟩
  rw [hgr, hfr]
  rw [finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hgrkerIso,
    finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hfrkerIso,
    finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hcross1,
    finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G) hcross2]
  exact add_comm _ _

/-- Helper for Theorem 15-15.2-2: the nested case
`𝔪_A ^ n • L₁ ≤ L₂ ≤ L₁` should be proved by induction on `n`, using the special case
`𝔪_A • L' ≤ L'' ≤ L'` and the induction-step lattice
`(𝔪_A ^ n) • L₁ + L₂`. -/
theorem reduction_grothendieckClass_eq_of_pow_le
    (ρ : Representation K G E) {L₁ L₂ : StableLattice A ρ} (n : ℕ)
    (h21 : L₂.toSubmodule ≤ L₁.toSubmodule)
    (hpow : (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ≤ L₂.toSubmodule) :
    [FDRep.of L₁.reductionRepresentation]₀ = [FDRep.of L₂.reductionRepresentation]₀ := by
  induction n generalizing L₁ L₂ with
  | zero =>
      -- At power `0`, the containment `L₁ ≤ L₂` combines with `L₂ ≤ L₁`, so the lattices agree.
      have h12 : L₁.toSubmodule ≤ L₂.toSubmodule := by
        simpa [pow_zero, Ideal.one_eq_top] using hpow
      have hEq : L₁.toSubmodule = L₂.toSubmodule := le_antisymm h12 h21
      have hL : L₁ = L₂ := StableLattice.ext_toSubmodule hEq
      cases hL
      rfl
  | succ n ih =>
      let L₃ : StableLattice A ρ :=
        StableLattice.maximalIdealPowSupStableLattice (A := A) (K := K) (ρ := ρ) L₁ L₂ n
      have h31 : L₃.toSubmodule ≤ L₁.toSubmodule := by
        -- The induction-step lattice still sits inside `L₁`.
        simpa [L₃] using
          StableLattice.maximalIdealPowSupStableLattice_le_left
            (A := A) (K := K) (ρ := ρ) (L₁ := L₁) (L₂ := L₂) h21
      have h13pow : (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ≤ L₃.toSubmodule := by
        -- The left summand of the supremum defining `L₃` gives the smaller power bound.
        simpa [L₃, StableLattice.maximalIdealPowSupStableLattice_toSubmodule] using
          (le_sup_left :
            (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ≤
              (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ⊔ L₂.toSubmodule)
      have h23 : L₂.toSubmodule ≤ L₃.toSubmodule := by
        -- The original lattice is the right summand of the same supremum.
        simpa [L₃, StableLattice.maximalIdealPowSupStableLattice_toSubmodule] using
          (le_sup_right :
            L₂.toSubmodule ≤
              (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ⊔ L₂.toSubmodule)
      have h𝔪3 : (IsLocalRing.maximalIdeal A) • L₃.toSubmodule ≤ L₂.toSubmodule := by
        -- This is exactly the purpose of the induction-step lattice `L₃`.
        simpa [L₃] using
          StableLattice.maximalIdealPowSupStableLattice_maximalIdeal_le
            (A := A) (K := K) (ρ := ρ) (L₁ := L₁) (L₂ := L₂) hpow
      calc
        [FDRep.of L₁.reductionRepresentation]₀ =
            [FDRep.of L₃.reductionRepresentation]₀ := by
              -- First drop the exponent from `n + 1` to `n` by replacing `L₂` with `L₃`.
              exact ih h31 h13pow
        _ = [FDRep.of L₂.reductionRepresentation]₀ := by
              -- Then apply LinearRepresentations_Serre_1977's special nested-lattice comparison to `L₃` and `L₂`.
              exact reduction_grothendieckClass_eq_of_maximalIdeal_le
                (A := A) (K := K) (G := G) (ρ := ρ) (L₁ := L₃) (L₂ := L₂) h23 h𝔪3

-- Proof sketch: first compare two lattices in the special case
-- `𝔪_A L₁ ≤ L₂ ≤ L₁` using the exact sequence
-- `0 → T → L₂ / 𝔪_A L₂ → L₁ / 𝔪_A L₁ → T → 0`, where multiplication by a chosen generator of
-- the maximal ideal supplies the connecting maps; then reduce the general case to this one by
-- scaling one lattice and inducting on the least `n` with `𝔪_A ^ n • L₁ ≤ L₂ ≤ L₁`.
/-- Theorem 15-15.2-2: the class in `R_k(G)` of the reduction modulo the maximal ideal of a
`G`-stable lattice is independent of the chosen stable lattice. Source-faithful constraint: this
is stated in the discrete-valuation-ring setting used in LinearRepresentations_Serre_1977's proof, not for an arbitrary local
ring. -/
theorem stableLatticeReduction_grothendieckClass_eq
    (ρ : Representation K G E) (L₁ L₂ : StableLattice A ρ) :
    [FDRep.of L₁.reductionRepresentation]₀ = [FDRep.of L₂.reductionRepresentation]₀ := by
  -- Route correction: the previous attempt jumped directly to LinearRepresentations_Serre_1977's five-term exact sequence.
  -- The stabilized prefix is now fully bundled: rescaling a lattice does not change the
  -- Grothendieck class of its reduction representation.
  have hhomothety :
      ∀ a : Kˣ,
        [FDRep.of L₂.reductionRepresentation]₀ =
          [FDRep.of (a • L₂).reductionRepresentation]₀ := by
    intro a
    exact StableLattice.reduction_grothendieckClass_eq_of_smul
      (A := A) (K := K) (ρ := ρ) L₂ a
  obtain ⟨a, ha⟩ := StableLattice.exists_smul_le_of_lattices
    (A := A) (K := K) (ρ := ρ) L₁ L₂
  have hpow :
      ∃ n : ℕ,
        (IsLocalRing.maximalIdeal A ^ n) • L₁.toSubmodule ≤ (a • L₂).toSubmodule := by
    -- The nested case is now reduced to an induction on a maximal-ideal power bound.
    exact StableLattice.exists_maximalIdeal_pow_le_of_le
      (A := A) (K := K) (ρ := ρ) (L₁ := L₁) (L₂ := a • L₂) ha
  obtain ⟨n, hn⟩ := hpow
  calc
    [FDRep.of L₁.reductionRepresentation]₀ =
        [FDRep.of (a • L₂).reductionRepresentation]₀ := by
          -- The normalization is complete; only the nested case remains.
          exact reduction_grothendieckClass_eq_of_pow_le
            (A := A) (K := K) (G := G) (ρ := ρ) (L₁ := L₁) (L₂ := a • L₂) n ha hn
    _ = [FDRep.of L₂.reductionRepresentation]₀ := by
          symm
          exact hhomothety a

/-- Helper for Theorem 15-15.2-2: after clearing finitely many denominator coordinates, a
homothetic copy of any finitely generated `A`-submodule of the ambient representation lies inside
a chosen stable lattice. -/
theorem exists_smul_le_of_fg_submodule
    (ρ : Representation K G E) (L : StableLattice A ρ) {N : Submodule A E}
    (hNfg : N.FG) :
    ∃ a : Kˣ, a • N ≤ L.toSubmodule := by
  classical
  letI : Module.Finite A N := Module.Finite.of_fg hNfg
  letI : Module.IsTorsionFree A K := by
    infer_instance
  letI : Module.IsTorsionFree A E := Module.IsTorsionFree.trans_faithfulSMul A K E
  letI : Module.IsTorsionFree A N := Submodule.instIsTorsionFree (p := N)
  let bL : Module.Basis (Module.Free.ChooseBasisIndex A L.toSubmodule) A L.toSubmodule :=
    Module.Free.chooseBasis A L.toSubmodule
  let eL : Module.Basis (Module.Free.ChooseBasisIndex A L.toSubmodule) K E :=
    bL.extendOfIsLattice K
  let bN : Module.Basis (Module.Free.ChooseBasisIndex A N) A N :=
    Module.Free.chooseBasis A N
  let coeff :
      Module.Free.ChooseBasisIndex A N ×
          Module.Free.ChooseBasisIndex A L.toSubmodule → K :=
    fun ij ↦ eL.repr ((bN ij.1 : N) : E) ij.2
  -- Clear the finitely many denominators occurring in the coordinates of an `A`-basis of `N`
  -- with respect to the `K`-basis induced by `L`.
  obtain ⟨d, hd⟩ :=
    IsLocalization.exist_integer_multiples_of_finite (M := nonZeroDivisors A) coeff
  let a : Kˣ := (IsLocalization.map_units K d).unit
  refine ⟨a, ?_⟩
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  let yN : N := ⟨y, hy⟩
  change (algebraMap A K d) • (yN : E) ∈ L.toSubmodule
  have hbasis_mem (i : Module.Free.ChooseBasisIndex A N) :
      (algebraMap A K d) • ((bN i : N) : E) ∈ L.toSubmodule := by
    let c : Module.Free.ChooseBasisIndex A L.toSubmodule → A :=
      fun j ↦ Classical.choose (hd (i, j))
    let z : L.toSubmodule := ∑ j, c j • bL j
    -- Reassemble the cleared coefficients in the `A`-basis of `L`.
    have hz : ((z : L.toSubmodule) : E) = (algebraMap A K d) • ((bN i : N) : E) := by
      calc
        ((z : L.toSubmodule) : E) =
            ∑ j, (algebraMap A K (c j)) • (((bL j : L.toSubmodule) : E)) := by
              simp [z, c]
        _ = ∑ j, eL.repr ((algebraMap A K d) • (((bN i : N) : E))) j • eL j := by
              apply Finset.sum_congr rfl
              intro j _
              have hc : algebraMap A K (c j) =
                  eL.repr ((algebraMap A K d) • (((bN i : N) : E))) j := by
                calc
                  algebraMap A K (c j) = (algebraMap A K d) * coeff (i, j) := by
                    simpa [c, Algebra.smul_def] using (Classical.choose_spec (hd (i, j)))
                  _ = eL.repr ((algebraMap A K d) • (((bN i : N) : E))) j := by
                    simpa [coeff, Algebra.smul_def] using
                      ((congrArg (fun f => f j)
                        (LinearEquiv.map_smul eL.repr (algebraMap A K d)
                          (((bN i : N) : E)))).symm)
              simpa [eL, Module.Basis.extendOfIsLattice_apply] using
                congrArg (fun t => t • (((bL j : L.toSubmodule) : E))) hc
        _ = (algebraMap A K d) • ((bN i : N) : E) := by
              simpa [eL, Module.Basis.extendOfIsLattice_apply] using
                (eL.sum_repr ((algebraMap A K d) • (((bN i : N) : E))))
    exact hz ▸ z.property
  have hy_expand_sub : (∑ i, (bN.repr yN i : A) • bN i : N) = yN := by
    simpa using bN.sum_repr yN
  -- Expand the chosen vector in the `A`-basis of `N` and use the basiswise containment.
  rw [← hy_expand_sub]
  change (algebraMap A K d) •
        (((∑ i, (bN.repr yN i : A) • bN i : N) : N) : E) ∈
      L.toSubmodule
  simp_rw [Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [Finset.smul_sum]
  refine Submodule.sum_mem _ ?_
  intro i _
  simpa [smul_smul, mul_comm] using
    L.toSubmodule.smul_mem (bN.repr yN i) (hbasis_mem i)

section DecompositionHomAux

variable (hstable : ∀ V : FDRep K G, Nonempty (StableLattice A V.ρ))

private noncomputable abbrev reductionClassLift :
    FreeAbelianGroup (FDRep K G) →+ R₀[k](G) :=
  FreeAbelianGroup.lift fun V ↦
    let L : StableLattice A V.ρ := Classical.choice (hstable V)
    [FDRep.of L.reductionRepresentation]₀

/-- Helper for Theorem 15-15.2-2: the value of `reductionClassLift` on a generator can be
computed using any chosen stable lattice on that representation. -/
private theorem reductionClassLift_eq_reductionClass
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    reductionClassLift hstable (FreeAbelianGroup.of V) =
      [FDRep.of L.reductionRepresentation]₀ := by
  let L₀ : StableLattice A V.ρ := Classical.choice (hstable V)
  -- Replace the arbitrary choice inside `reductionClassLift` by the requested lattice using
  -- lattice-independence of the reduction class.
  dsimp [reductionClassLift]
  simpa [L₀] using
    stableLatticeReduction_grothendieckClass_eq
      (A := A) (K := K) (G := G) V.ρ L₀ L

/-- Helper for Theorem 15-15.2-2: in a short exact sequence of finite-dimensional
`K[G]`-representations, the source identifies with the range of the left map. -/
private theorem source_iso_range_of_shortExact
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    let fRep : IntertwiningMap S.X₁.ρ S.X₂.ρ :=
      ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom
    Nonempty (S.X₁ ≅ FDRep.of fRep.range.toRepresentation) := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat K` preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let fRep : IntertwiningMap S.X₁.ρ S.X₂.ρ :=
    ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom
  let f : S.X₁.V →ₗ[K] S.X₂.V := fRep.toLinearMap
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is mono, hence injective on vectors.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  let e :
      Representation.Equiv S.X₁.ρ fRep.range.toRepresentation := by
    -- The usual linear equivalence onto the range is compatible with the `G`-actions.
    refine Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_
    intro g
    ext x
    exact LinearMap.congr_fun (fRep.2 g) x
  exact ⟨Representation.Equiv.toFDRepIso e⟩

/-- Helper for Theorem 15-15.2-2: in a short exact sequence of finite-dimensional
`K[G]`-representations, the source also identifies with the kernel of the right map. -/
private theorem source_iso_kernel_of_shortExact
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    let gRep : IntertwiningMap S.X₂.ρ S.X₃.ρ :=
      ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom
    Nonempty (S.X₁ ≅ FDRep.of gRep.ker.toRepresentation) := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat K` preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let fRep : IntertwiningMap S.X₁.ρ S.X₂.ρ :=
    ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom
  let gRep : IntertwiningMap S.X₂.ρ S.X₃.ρ :=
    ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom
  let f : S.X₁.V →ₗ[K] S.X₂.V := fRep.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := gRep.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat K`, short exactness is exactness of the underlying linear maps.
    simpa [F, f, g, fRep, gRep] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hsourceRange :
      Nonempty (S.X₁ ≅ FDRep.of fRep.range.toRepresentation) := by
    -- First identify the source with the range of the left map.
    simpa [fRep] using source_iso_range_of_shortExact S hS
  have hRangeKer :
      Nonempty (FDRep.of fRep.range.toRepresentation ≅ FDRep.of gRep.ker.toRepresentation) := by
    -- Exactness identifies the range of `f` with the kernel of `g`.
    have hRangeKerEq : fRep.range.toSubmodule = gRep.ker.toSubmodule := by
      simpa [f, g, fRep, gRep] using (LinearMap.exact_iff.mp hExact).symm
    let e :
        Representation.Equiv fRep.range.toRepresentation gRep.ker.toRepresentation := by
      refine Representation.Equiv.mk (LinearEquiv.ofEq _ _ hRangeKerEq) ?_
      intro h
      ext x
      rfl
    exact ⟨Representation.Equiv.toFDRepIso e⟩
  rcases hsourceRange with ⟨e₁⟩
  rcases hRangeKer with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩

/-- Helper for Theorem 15-15.2-2: the canonical source-side lattice for LinearRepresentations_Serre_1977's exact-sequence
argument is the intersection of the chosen middle lattice with the kernel of the quotient map. -/
private noncomputable def kernelIntersectionStableLattice
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (g : ρ.IntertwiningMap σ) (L : StableLattice A ρ) :
    StableLattice A g.ker.toRepresentation := by
  let N : Submodule A g.ker.toSubmodule :=
    Submodule.comap (g.ker.toSubmodule.subtype.restrictScalars A) L.toSubmodule
  refine
    { toSubmodule := N
      apply_mem_toSubmodule := ?_
      isLattice := ?_ }
  · intro h x hx
    -- The kernel action is the restricted ambient action, so stability comes from `L`.
    change (((g.ker.toRepresentation h) x : g.ker.toSubmodule) : V) ∈ L.toSubmodule
    simpa using L.apply_mem_toSubmodule h hx
  · -- The kernel intersection is finitely generated, and every kernel vector can be scaled into
    -- the chosen middle lattice while staying in the kernel.
    refine
      { fg := ?_
        span_eq_top := ?_ }
    · letI : Module.Finite A N := by
        exact Module.Finite.of_fg <| by
          have hmap :
              (N.map (g.ker.toSubmodule.subtype.restrictScalars A)).FG := by
            apply Submodule.FG.of_le
              (Submodule.IsLattice.fg (A := K) (M := L.toSubmodule))
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            exact hx
          exact Submodule.fg_of_fg_map_injective
            (g.ker.toSubmodule.subtype.restrictScalars A) Subtype.val_injective hmap
      exact Module.Finite.iff_fg.mp (show Module.Finite A N from inferInstance)
    · apply le_antisymm le_top
      change (⊤ : Submodule K g.ker.toSubmodule) ≤ Submodule.span K ((N : Submodule A g.ker.toSubmodule) : Set g.ker.toSubmodule)
      intro x _
      let M : Submodule A V := A ∙ (x : V)
      obtain ⟨a, ha⟩ :=
        exists_smul_le_of_fg_submodule (A := A) (K := K) (ρ := ρ) L
          (N := M) (by simpa [M] using Submodule.fg_span_singleton (x : V))
      have haxL : (a : K) • (x : V) ∈ L.toSubmodule := by
        exact ha <| by
          refine ⟨x, ?_, rfl⟩
          exact Submodule.subset_span (by simp [M])
      have haxKer : (a : K) • (x : V) ∈ g.ker.toSubmodule := by
        change g.toLinearMap ((a : K) • (x : V)) = 0
        simpa [LinearMap.map_smul] using congrArg (fun z : W => (a : K) • z) x.property
      have haxN : (⟨(a : K) • (x : V), haxKer⟩ : g.ker.toSubmodule) ∈ N := haxL
      have hspan :
          (⟨(a : K) • (x : V), haxKer⟩ : g.ker.toSubmodule) ∈
            Submodule.span K ((N : Submodule A g.ker.toSubmodule) : Set g.ker.toSubmodule) := by
        exact Submodule.subset_span haxN
      have hx_eq :
          x = (↑a⁻¹ : K) • (⟨(a : K) • (x : V), haxKer⟩ : g.ker.toSubmodule) := by
        ext
        change (x : V) = (↑a⁻¹ : K) • ((a : K) • (x : V))
        simp [smul_smul]
      rw [hx_eq]
      exact Submodule.smul_mem _ _ hspan

/-- Helper for Theorem 15-15.2-2: the image of a stable lattice under an intertwining map is
stable under the target action. -/
private theorem imageStableLattice_apply_mem_toSubmodule
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ) (g : G)
    {x : W} (hx : x ∈ Submodule.map (f.toLinearMap.restrictScalars A) L.toSubmodule) :
    ((Representation.restrictScalars A σ) g) x ∈
      Submodule.map (f.toLinearMap.restrictScalars A) L.toSubmodule := by
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨ρ g y, L.apply_mem_toSubmodule g hy, ?_⟩
  exact LinearMap.congr_fun (f.2 g) y

/-- Helper for Theorem 15-15.2-2: the image of a stable lattice under a surjective intertwining
map is still a lattice over `A`. -/
private theorem imageStableLattice_isLattice
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    Submodule.IsLattice K (Submodule.map (f.toLinearMap.restrictScalars A) L.toSubmodule) := by
  refine
    { fg := ?_
      span_eq_top := ?_ }
  · -- Finite generation descends through the linear image.
    exact (Submodule.IsLattice.fg (A := K) (M := L.toSubmodule)).map
      (f.toLinearMap.restrictScalars A)
  · -- The image spans the whole target because `L` spans the source and `f` is surjective.
    apply le_antisymm le_top
    change (⊤ : Submodule K W) ≤
      Submodule.span K ((Submodule.map (f.toLinearMap.restrictScalars A) L.toSubmodule :
        Submodule A W) : Set W)
    intro w _
    rcases hf w with ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (L.toSubmodule : Set V) := by
      rw [Submodule.IsLattice.span_eq_top (A := K) (M := L.toSubmodule)]
      trivial
    have himage :
        f.toLinearMap v ∈ Submodule.span K (f.toLinearMap '' (L.toSubmodule : Set V)) := by
      exact Submodule.apply_mem_span_image_of_mem_span (f := f.toLinearMap) hv
    have hset :
        (f.toLinearMap '' (L.toSubmodule : Set V)) =
          ((Submodule.map (f.toLinearMap.restrictScalars A) L.toSubmodule :
            Submodule A W) : Set W) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
    simpa [hset] using himage

/-- Helper for Theorem 15-15.2-2: the image of a stable lattice under a surjective intertwining
map is a stable lattice on the target representation. -/
private noncomputable def imageStableLattice
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    StableLattice A σ :=
  { toSubmodule := Submodule.map (f.toLinearMap.restrictScalars A) L.toSubmodule
    apply_mem_toSubmodule := imageStableLattice_apply_mem_toSubmodule (A := A) (K := K) (G := G)
      f L
    isLattice := imageStableLattice_isLattice (A := A) (K := K) (G := G) f L hf }

/-- Helper for Theorem 15-15.2-2: a lattice vector maps to its canonical class in the image
stable lattice. -/
private noncomputable def imageStableLatticeLift
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    L.toSubmodule →ₗ[A] (imageStableLattice (A := A) (K := K) (G := G) f L hf).toSubmodule :=
  { toFun := fun x ↦ ⟨f.toLinearMap x, ⟨x, x.property, rfl⟩⟩
    map_add' := by
      -- Forget to the ambient target module, where the map is just `f`.
      intro x y
      ext
      change f.toLinearMap ↑(x + y) = f.toLinearMap ↑x + f.toLinearMap ↑y
      simp
    map_smul' := by
      -- The same reduction to the ambient module proves `A`-linearity.
      intro a x
      ext
      change f.toLinearMap ↑(a • x) = a • f.toLinearMap ↑x
      simp }

/-- Helper for Theorem 15-15.2-2: the image-lattice lift sends `𝔪_A L` into the maximal-ideal
submodule of the image lattice, so it descends to reductions. -/
private theorem imageStableLatticeLift_mem_maximalIdeal
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap)
    {x : L.toSubmodule} (hx : x ∈ L.maximalIdealSubmodule) :
    imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x ∈
      (imageStableLattice (A := A) (K := K) (G := G) f L hf).maximalIdealSubmodule := by
  -- Expand membership in `𝔪_A • ⊤` and transport each summand through the image-lattice lift.
  rw [StableLattice.maximalIdealSubmodule] at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    have hsmul :
        imageStableLatticeLift (A := A) (K := K) (G := G) f L hf (a • y) =
          a • imageStableLatticeLift (A := A) (K := K) (G := G) f L hf y := by
      ext
      simp [imageStableLatticeLift]
    rw [hsmul]
    change a • imageStableLatticeLift (A := A) (K := K) (G := G) f L hf y ∈
        (IsLocalRing.maximalIdeal A) •
          (⊤ : Submodule A (imageStableLattice (A := A) (K := K) (G := G) f L hf).toSubmodule)
    refine Submodule.smul_mem_smul (N := (⊤ : Submodule A
      (imageStableLattice (A := A) (K := K) (G := G) f L hf).toSubmodule)) ha ?_
    show imageStableLatticeLift (A := A) (K := K) (G := G) f L hf y ∈
      (⊤ : Submodule A (imageStableLattice (A := A) (K := K) (G := G) f L hf).toSubmodule)
    trivial
  · intro y z hy hz
    change
      imageStableLatticeLift (A := A) (K := K) (G := G) f L hf (y + z) ∈
        (IsLocalRing.maximalIdeal A) •
          (⊤ : Submodule A (imageStableLattice (A := A) (K := K) (G := G) f L hf).toSubmodule)
    simpa [imageStableLatticeLift] using add_mem hy hz

/-- Helper for Theorem 15-15.2-2: reducing a lattice and then mapping to the image stable lattice
gives the canonical descended quotient map. -/
private noncomputable def reductionToImageStableLatticeA
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    L.reduction →ₗ[A] (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction :=
  Submodule.liftQ L.maximalIdealSubmodule
    ((imageStableLattice (A := A) (K := K) (G := G) f L hf).maximalIdealSubmodule.mkQ.comp
      (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf))
    (fun x hx ↦
      (Submodule.Quotient.mk_eq_zero _).2 <|
        imageStableLatticeLift_mem_maximalIdeal
          (A := A) (K := K) (G := G) f L hf hx)

/-- Helper for Theorem 15-15.2-2: on represented quotient classes, the descended image-lattice map
is still the class of the original intertwining map. -/
@[simp] private theorem reductionToImageStableLatticeA_apply_mk
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) (x : L.toSubmodule) :
    reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x) := by
  -- This is the defining formula of the quotient lift on represented classes.
  rfl

/-- Helper for Theorem 15-15.2-2: the reduction-to-image map is residue-field linear and
`G`-equivariant, hence a morphism of reduced representations. -/
private noncomputable def reductionToImageStableLattice
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    L.reductionRepresentation.IntertwiningMap
      (imageStableLattice (A := A) (K := K) (G := G) f L hf).reductionRepresentation := by
  let fbar :
      L.reduction →ₗ[k] (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction :=
    { toFun := reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf
      map_add' := (reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf).map_add
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        -- Reduce residue-field linearity to represented classes in the two reductions.
        change
          reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf
              ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : k) •
                (Submodule.Quotient.mk y : L.reduction)) = _
        rw [StableLattice.reduction_smul_mk (L := L) a y]
        rw [reductionToImageStableLatticeA_apply_mk]
        change
          (Submodule.Quotient.mk
            (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf (a • y)) :
              (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction) =
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) a : k) •
              (Submodule.Quotient.mk
                (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf y) :
                  (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction)
        rw [StableLattice.reduction_smul_mk
          (L := imageStableLattice (A := A) (K := K) (G := G) f L hf)
          a (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf y)]
        change
          (Submodule.Quotient.mk
            (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf (a • y)) :
              (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction) =
            Submodule.Quotient.mk
              (a • imageStableLatticeLift (A := A) (K := K) (G := G) f L hf y)
        simp [imageStableLatticeLift] }
  -- Compare both sides on represented quotient classes, where everything is explicit.
  exact fbar.intertwiningMap_of_isIntertwiningMap
    L.reductionRepresentation
    (imageStableLattice (A := A) (K := K) (G := G) f L hf).reductionRepresentation
    (fun g x ↦ by
      refine Quotient.inductionOn' x ?_
      intro y
      change
        reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf
            (Submodule.Quotient.mk ((L.toRepresentation g) y)) =
          (imageStableLattice (A := A) (K := K) (G := G) f L hf).reductionRepresentation g
            (reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf
              (Submodule.Quotient.mk y))
      rw [reductionToImageStableLatticeA_apply_mk,
        reductionToImageStableLatticeA_apply_mk,
        StableLattice.reductionRepresentation_apply_mk]
      change
        (Submodule.Quotient.mk
          (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf
            ((L.toRepresentation g) y)) :
            (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction) =
          Submodule.Quotient.mk
            (((imageStableLattice (A := A) (K := K) (G := G) f L hf).toRepresentation g)
              (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf y))
      apply congrArg (fun z =>
        (Submodule.Quotient.mk z :
          (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction))
      ext
      simpa [imageStableLatticeLift, StableLattice.toRepresentation_apply_coe] using
        LinearMap.congr_fun (f.2 g) y)

/-- Helper for Theorem 15-15.2-2: the descended map onto the image stable lattice is surjective on
reduction classes. -/
private theorem reductionToImageStableLattice_surjective
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    Function.Surjective
      (reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf).toLinearMap := by
  intro x
  rcases Submodule.Quotient.mk_surjective
      (imageStableLattice (A := A) (K := K) (G := G) f L hf).maximalIdealSubmodule x with
    ⟨y, rfl⟩
  rcases y.property with ⟨z, hz, hzy⟩
  refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
  -- A represented class in the image lattice is hit by the corresponding represented class upstairs.
  change
    reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf
        (Submodule.Quotient.mk ⟨z, hz⟩) =
      Submodule.Quotient.mk y
  rw [reductionToImageStableLatticeA_apply_mk]
  have hy :
      imageStableLatticeLift (A := A) (K := K) (G := G) f L hf ⟨z, hz⟩ = y := by
    ext
    simpa [imageStableLatticeLift] using hzy
  simpa [hy]

/-- Helper for Theorem 15-15.2-2: if an intertwining map is injective upstairs, then its
descended map to the image stable lattice is also injective after reduction. -/
private theorem reductionToImageStableLattice_injective
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap)
    (hf_inj : Function.Injective f.toLinearMap) :
    Function.Injective
      (reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf).toLinearMap := by
  let fbar := reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf
  have hzero :
      ∀ z : L.reduction, fbar.toLinearMap z = 0 → z = 0 := by
    intro z hz
    rcases Submodule.Quotient.mk_surjective L.maximalIdealSubmodule z with ⟨x, rfl⟩
    change
      (Submodule.Quotient.mk
        (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x) :
          (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction) = 0 at hz
    have hx :
        imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x ∈
          (imageStableLattice (A := A) (K := K) (G := G) f L hf).maximalIdealSubmodule := by
      exact (Submodule.Quotient.mk_eq_zero _).1 hz
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul] at hx
    rcases hx with ⟨y, hy, hxy⟩
    rcases y.property with ⟨w, hw, hwy⟩
    let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
    have hxyW :
        f.toLinearMap (x : V) = (π : A) • f.toLinearMap (w : V) := by
      calc
        f.toLinearMap (x : V) =
            (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x : W) := by
              rfl
        _ = (π : A) • (y : W) := by
              simpa [π] using (congrArg Subtype.val hxy).symm
        _ = (π : A) • f.toLinearMap (w : V) := by
              simpa [π] using (congrArg (fun t : W ↦ (π : A) • t) hwy).symm
    have hxeq :
        (x : V) =
          (π : A) • (w : V) := by
      apply hf_inj
      simpa [π, LinearMap.map_smul] using hxyW
    apply (Submodule.Quotient.mk_eq_zero _).2
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul]
    refine ⟨⟨w, hw⟩, show (⟨w, hw⟩ : L.toSubmodule) ∈ (⊤ : Submodule A L.toSubmodule) by trivial,
      ?_⟩
    ext
    simpa [π] using hxeq.symm
  intro x y hxy
  have hsub : fbar.toLinearMap (x - y) = 0 := by
    simpa [fbar, map_sub, hxy]
  exact sub_eq_zero.mp (hzero (x - y) hsub)

/-- Helper for Theorem 15-15.2-2: a bijective intertwining map identifies the reductions of a
stable lattice and its transported image lattice at the level of the descended linear map. -/
private theorem reductionToImageStableLattice_bijective_of_bijective
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Bijective f.toLinearMap) :
    Function.Bijective
      (reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf.surjective).toLinearMap := by
  -- Both injectivity and surjectivity descend through the reduction-to-image construction.
  exact ⟨reductionToImageStableLattice_injective
      (A := A) (K := K) (G := G) f L hf.surjective hf.injective,
    reductionToImageStableLattice_surjective
      (A := A) (K := K) (G := G) f L hf.surjective⟩

/-- Helper for Theorem 15-15.2-2: a bijective intertwining map between finite-dimensional
`k[G]`-representations induces an isomorphism in the bundled owner `FDRep`. -/
private theorem fdRepIso_of_bijective_intertwining
    {V W : Type u}
    [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k G V} {σ : Representation k G W}
    [FiniteDimensional k V] [FiniteDimensional k W]
    (f : IntertwiningMap ρ σ) (hf : Function.Bijective f.toLinearMap) :
    Nonempty (FDRep.of ρ ≅ FDRep.of σ) := by
  -- Package the bijective intertwining map as a representation equivalence before rebundling.
  refine ⟨Representation.Equiv.toFDRepIso ?_⟩
  refine Representation.Equiv.mk (LinearEquiv.ofBijective f.toLinearMap hf) ?_
  intro g
  ext x
  exact LinearMap.congr_fun (f.2 g) x

/-- Helper for Theorem 15-15.2-2: a bijective intertwining map identifies the reductions of a
stable lattice and its transported image lattice. -/
private theorem reductionRepresentationEquivOfBijective
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Bijective f.toLinearMap) :
    let L' : StableLattice A σ :=
      imageStableLattice (A := A) (K := K) (G := G) f L hf.surjective
    Nonempty (FDRep.of L.reductionRepresentation ≅ FDRep.of L'.reductionRepresentation) := by
  -- Reuse the generic rebundling lemma on the descended bijective reduction map.
  exact fdRepIso_of_bijective_intertwining (G := G)
    (reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf.surjective)
    (reductionToImageStableLattice_bijective_of_bijective
      (A := A) (K := K) (G := G) f L hf)

/-- Helper for Theorem 15-15.2-2: the source of a short exact sequence is representation-
equivalent to the kernel of the right map. -/
private theorem source_repEquiv_kernel_of_shortExact
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    let gRep : IntertwiningMap S.X₂.ρ S.X₃.ρ :=
      ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom
    Nonempty (Representation.Equiv S.X₁.ρ gRep.ker.toRepresentation) := by
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat K` preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let fRep : IntertwiningMap S.X₁.ρ S.X₂.ρ :=
    ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom
  let gRep : IntertwiningMap S.X₂.ρ S.X₃.ρ :=
    ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom
  let f : S.X₁.V →ₗ[K] S.X₂.V := fRep.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := gRep.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat K`, short exactness is exactness of the underlying linear maps.
    simpa [F, f, g, fRep, gRep] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is mono, hence injective on vectors.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hsourceRange :
      Nonempty (Representation.Equiv S.X₁.ρ fRep.range.toRepresentation) := by
    -- First identify the source with the range of the left map.
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofInjective f hf) ?_⟩
    intro h
    ext x
    exact LinearMap.congr_fun (fRep.2 h) x
  have hRangeKer :
      Nonempty (Representation.Equiv fRep.range.toRepresentation gRep.ker.toRepresentation) := by
    -- Exactness identifies the range of `f` with the kernel of `g`.
    have hRangeKerEq : fRep.range.toSubmodule = gRep.ker.toSubmodule := by
      simpa [f, g, fRep, gRep] using (LinearMap.exact_iff.mp hExact).symm
    refine ⟨Representation.Equiv.mk (LinearEquiv.ofEq _ _ hRangeKerEq) ?_⟩
    intro h
    ext x
    rfl
  rcases hsourceRange with ⟨e₁⟩
  rcases hRangeKer with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩

/-- Helper for Theorem 15-15.2-2: the reduction of the kernel-intersection lattice is naturally
equivalent to the kernel of the descended quotient map onto the image lattice. -/
private noncomputable def kernelIntersectionInclusion
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ) :
    (kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L).toSubmodule →ₗ[A]
      L.toSubmodule :=
  { toFun := fun x ↦ ⟨((x : (kernelIntersectionStableLattice
        (A := A) (K := K) (G := G) f L).toSubmodule) :
          f.ker.toSubmodule), x.property⟩
    map_add' := by
      -- Forget to the ambient source module, where the map is the inclusion.
      intro x y
      ext
      rfl
    map_smul' := by
      -- The same reduction to the ambient source module proves `A`-linearity.
      intro a x
      ext
      rfl }

/-- Helper for Theorem 15-15.2-2: on represented classes in `L ∩ ker(f)`, the inclusion into `L`
is just the ambient inclusion of vectors. -/
@[simp] private theorem kernelIntersectionInclusion_apply
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (x : (kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L).toSubmodule) :
    ((kernelIntersectionInclusion (A := A) (K := K) (G := G) f L x : L.toSubmodule) : V) =
      (((x : (kernelIntersectionStableLattice
        (A := A) (K := K) (G := G) f L).toSubmodule) : f.ker.toSubmodule) : V) := by
  -- This is definitional for the inclusion of the kernel-intersection lattice into `L`.
  rfl

/-- Helper for Theorem 15-15.2-2: the inclusion `L ∩ ker(f) ↪ L` sends the maximal-ideal
submodule of the kernel-intersection lattice into the maximal-ideal submodule of `L`. -/
private theorem kernelIntersectionInclusion_mem_maximalIdeal
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    {x : (kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L).toSubmodule}
    (hx : x ∈ (kernelIntersectionStableLattice
      (A := A) (K := K) (G := G) f L).maximalIdealSubmodule) :
    kernelIntersectionInclusion (A := A) (K := K) (G := G) f L x ∈
      L.maximalIdealSubmodule := by
  let N : StableLattice A f.ker.toRepresentation :=
    kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L
  -- Expand membership in `𝔪_A • ⊤` and transport each summand through the inclusion.
  rw [StableLattice.maximalIdealSubmodule] at hx ⊢
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y hy
    have hsmul :
        kernelIntersectionInclusion (A := A) (K := K) (G := G) f L (a • y) =
          a • kernelIntersectionInclusion (A := A) (K := K) (G := G) f L y := by
      ext
      rfl
    rw [hsmul]
    change a • kernelIntersectionInclusion (A := A) (K := K) (G := G) f L y ∈
        (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A L.toSubmodule)
    refine Submodule.smul_mem_smul (N := (⊤ : Submodule A L.toSubmodule)) ha ?_
    exact Submodule.mem_top
  · intro y z hy hz
    change
      kernelIntersectionInclusion (A := A) (K := K) (G := G) f L (y + z) ∈
        (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A L.toSubmodule)
    simpa [kernelIntersectionInclusion] using add_mem hy hz

/-- Helper for Theorem 15-15.2-2: reducing the kernel-intersection lattice and then including it
into `\bar L` gives the canonical descended quotient map. -/
private noncomputable def kernelIntersectionReductionInclusionA
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ) :
    (kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L).reduction →ₗ[A]
      L.reduction :=
  Submodule.liftQ
    (kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L).maximalIdealSubmodule
    (L.maximalIdealSubmodule.mkQ.comp
      (kernelIntersectionInclusion (A := A) (K := K) (G := G) f L))
    (fun x hx ↦
      (Submodule.Quotient.mk_eq_zero _).2 <|
        kernelIntersectionInclusion_mem_maximalIdeal
          (A := A) (K := K) (G := G) f L hx)

/-- Helper for Theorem 15-15.2-2: on represented quotient classes, the descended inclusion of
`L ∩ ker(f)` into `L` is still given by the ambient inclusion of vectors. -/
@[simp] private theorem kernelIntersectionReductionInclusionA_apply_mk
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (x : (kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L).toSubmodule) :
    kernelIntersectionReductionInclusionA (A := A) (K := K) (G := G) f L
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk
        (kernelIntersectionInclusion (A := A) (K := K) (G := G) f L x) := by
  -- This is the defining formula of the quotient lift on represented classes.
  rfl

/-- Helper for Theorem 15-15.2-2: after passing to reductions, the inclusion
`L ∩ ker(f) ↪ L` remains residue-field linear and `G`-equivariant. -/
private noncomputable def kernelIntersectionReductionInclusion
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ) :
    ((kernelIntersectionStableLattice
      (A := A) (K := K) (G := G) f L).reductionRepresentation).IntertwiningMap
        L.reductionRepresentation := by
  let N : StableLattice A f.ker.toRepresentation :=
    kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L
  let j : N.toSubmodule →ₗ[A] L.toSubmodule :=
    kernelIntersectionInclusion (A := A) (K := K) (G := G) f L
  let i :
      N.reduction →ₗ[k] L.reduction :=
    { toFun := kernelIntersectionReductionInclusionA (A := A) (K := K) (G := G) f L
      map_add' := (kernelIntersectionReductionInclusionA
        (A := A) (K := K) (G := G) f L).map_add
      map_smul' := by
        intro c x
        refine Quotient.inductionOn' c ?_
        intro a
        refine Quotient.inductionOn' x ?_
        intro y
        -- Reduce residue-field linearity to represented classes in the two reductions.
        simpa [StableLattice.reduction_smul_mk (L := N) a y,
          kernelIntersectionReductionInclusionA_apply_mk,
          StableLattice.reduction_smul_mk (L := L) a (j y)] using
          (kernelIntersectionReductionInclusionA
            (A := A) (K := K) (G := G) f L).map_smul a
              (Submodule.Quotient.mk y : N.reduction) }
  -- Compare both sides on represented quotient classes, where the inclusion is explicit.
  exact i.intertwiningMap_of_isIntertwiningMap
    N.reductionRepresentation L.reductionRepresentation
    (fun g x ↦ by
      refine Quotient.inductionOn' x ?_
      intro y
      change
        kernelIntersectionReductionInclusionA (A := A) (K := K) (G := G) f L
            (Submodule.Quotient.mk ((N.toRepresentation g) y)) =
          L.reductionRepresentation g
            (kernelIntersectionReductionInclusionA
              (A := A) (K := K) (G := G) f L
              (Submodule.Quotient.mk y))
      rw [kernelIntersectionReductionInclusionA_apply_mk,
        kernelIntersectionReductionInclusionA_apply_mk,
        StableLattice.reductionRepresentation_apply_mk]
      apply congrArg (fun z => (Submodule.Quotient.mk z : L.reduction))
      ext
      rfl)

/-- Helper for Theorem 15-15.2-2: a vector in `L ∩ ker(f)` maps to zero in the reduced image
lattice, so the descended inclusion lands in `ker(f̄)`. -/
private theorem imageStableLatticeLift_kernelIntersectionInclusion_eq_zero
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap)
    (x : (kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L).toSubmodule) :
    imageStableLatticeLift (A := A) (K := K) (G := G) f L hf
        (kernelIntersectionInclusion (A := A) (K := K) (G := G) f L x) = 0 := by
  -- Forget to the ambient target module, where the image is `f(x) = 0`.
  ext
  change f.toLinearMap
      ((((x : (kernelIntersectionStableLattice
        (A := A) (K := K) (G := G) f L).toSubmodule) : f.ker.toSubmodule) : V)) = 0
  exact (x : f.ker.toSubmodule).property

/-- Helper for Theorem 15-15.2-2: the descended inclusion of `L ∩ ker(f)` into `L` remains
injective after reduction. -/
private theorem kernelIntersectionReductionInclusion_injective
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ) :
    Function.Injective
      (kernelIntersectionReductionInclusion
        (A := A) (K := K) (G := G) f L).toLinearMap := by
  let N : StableLattice A f.ker.toRepresentation :=
    kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L
  let i := kernelIntersectionReductionInclusion (A := A) (K := K) (G := G) f L
  have hzero : ∀ z : N.reduction, i.toLinearMap z = 0 → z = 0 := by
    intro z hz
    rcases Submodule.Quotient.mk_surjective N.maximalIdealSubmodule z with ⟨x, rfl⟩
    change (Submodule.Quotient.mk
      (kernelIntersectionInclusion (A := A) (K := K) (G := G) f L x) : L.reduction) = 0 at hz
    have hx :
        kernelIntersectionInclusion (A := A) (K := K) (G := G) f L x ∈
          L.maximalIdealSubmodule := by
      exact (Submodule.Quotient.mk_eq_zero _).1 hz
    -- Rewrite maximal-ideal membership as a generator witness inside `L`.
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul] at hx
    rcases hx with ⟨y, hy, hxy⟩
    let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
    have hxyV :
        (π : A) • (y : V) =
          (((x : N.toSubmodule) : f.ker.toSubmodule) : V) := by
      simpa [π, kernelIntersectionInclusion] using congrArg Subtype.val hxy
    have hyKer :
        f.toLinearMap (y : V) = 0 := by
      have hπKer :
          ((algebraMap A K π : K) • f.toLinearMap (y : V)) = 0 := by
        calc
          ((algebraMap A K π : K) • f.toLinearMap (y : V)) =
              f.toLinearMap ((π : A) • (y : V)) := by
                simp [LinearMap.map_smul]
          _ = f.toLinearMap ((((x : N.toSubmodule) : f.ker.toSubmodule) : V)) := by
                rw [hxyV]
          _ = 0 := by
                exact (x : f.ker.toSubmodule).property
      have hπKer' :
          ((algebraMap A K π : K) • f.toLinearMap (y : V)) =
            ((algebraMap A K π : K) • (0 : W)) := by
        simpa using hπKer
      exact maximalIdeal_generator_smul_injective
        (A := A) (K := K) (E := W) hπKer'
    have hyN_mem :
        (⟨(y : V), hyKer⟩ : f.ker.toSubmodule) ∈ N.toSubmodule := by
      exact y.property
    let yN : N.toSubmodule := ⟨⟨(y : V), hyKer⟩, hyN_mem⟩
    have hxyN : (π : A) • yN = x := by
      have hxyN' :
          (π : A) • ((yN : N.toSubmodule) : f.ker.toSubmodule) =
            ((x : N.toSubmodule) : f.ker.toSubmodule) := by
        ext
        change (π : A) • (y : V) =
          (((x : N.toSubmodule) : f.ker.toSubmodule) : V)
        exact hxyV
      exact Subtype.ext hxyN'
    -- The represented class of `x` vanishes because `x = π • yN`.
    apply (Submodule.Quotient.mk_eq_zero _).2
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul]
    refine ⟨yN, show yN ∈ (⊤ : Submodule A N.toSubmodule) by trivial, ?_⟩
    exact hxyN
  intro x y hxy
  have hsub : i.toLinearMap (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp (hzero (x - y) hsub)

/-- Helper for Theorem 15-15.2-2: the range of the descended inclusion
`\overline{L ∩ ker(f)} → \bar L` is exactly `ker(f̄)`. -/
private theorem kernelIntersectionReductionInclusion_range_eq_ker
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    (kernelIntersectionReductionInclusion
      (A := A) (K := K) (G := G) f L).range.toSubmodule =
      (reductionToImageStableLattice
        (A := A) (K := K) (G := G) f L hf).ker.toSubmodule := by
  let N : StableLattice A f.ker.toRepresentation :=
    kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L
  let i := kernelIntersectionReductionInclusion (A := A) (K := K) (G := G) f L
  let fbar := reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf
  ext x
  constructor
  · intro hx
    simp only [IntertwiningMap.range, LinearMap.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    rcases Quotient.exists_rep y with ⟨y', rfl⟩
    simp only [IntertwiningMap.ker, LinearMap.mem_ker]
    -- On a represented class from `L ∩ ker(f)`, the descended image map is literally zero.
    change
      reductionToImageStableLatticeA (A := A) (K := K) (G := G) f L hf
          (Submodule.Quotient.mk
            (kernelIntersectionInclusion (A := A) (K := K) (G := G) f L y')) = 0
    rw [reductionToImageStableLatticeA_apply_mk]
    rw [imageStableLatticeLift_kernelIntersectionInclusion_eq_zero
      (A := A) (K := K) (G := G) f L hf y']
    rfl
  · intro hx
    simp only [IntertwiningMap.ker, LinearMap.mem_ker] at hx
    rcases Quotient.exists_rep x with ⟨x', rfl⟩
    change
      (Submodule.Quotient.mk
        (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x') :
          (imageStableLattice (A := A) (K := K) (G := G) f L hf).reduction) = 0 at hx
    have hx' :
        imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x' ∈
          (imageStableLattice (A := A) (K := K) (G := G) f L hf).maximalIdealSubmodule := by
      exact (Submodule.Quotient.mk_eq_zero _).1 hx
    -- Rewrite `f(x') ∈ 𝔪 f(L)` using a generator witness inside the image lattice.
    rw [StableLattice.maximalIdealSubmodule,
      ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
      Submodule.ideal_span_singleton_smul] at hx'
    rcases hx' with ⟨y, hy, hxy⟩
    rcases y.property with ⟨w, hw, hwy⟩
    let π : A := Submodule.IsPrincipal.generator (IsLocalRing.maximalIdeal A)
    let wL : L.toSubmodule := ⟨w, hw⟩
    have himage :
        f.toLinearMap (x' : V) = (π : A) • f.toLinearMap (w : V) := by
      calc
        f.toLinearMap (x' : V) =
            (imageStableLatticeLift (A := A) (K := K) (G := G) f L hf x' : W) := by
              rfl
        _ = (π : A) • (y : W) := by
              simpa [π] using (congrArg Subtype.val hxy).symm
        _ = (π : A) • f.toLinearMap (w : V) := by
              simpa [π] using (congrArg (fun t : W ↦ (π : A) • t) hwy).symm
    have hcorrectedKer :
        f.toLinearMap ((x' : V) - (π : A) • (w : V)) = 0 := by
      calc
        f.toLinearMap ((x' : V) - (π : A) • (w : V)) =
            f.toLinearMap (x' : V) - (π : A) • f.toLinearMap (w : V) := by
              simp [LinearMap.map_sub, LinearMap.map_smul]
        _ = 0 := by
              rw [himage, sub_self]
    have hcorrectedL :
        (x' : V) - (π : A) • (w : V) ∈ L.toSubmodule := by
      exact sub_mem x'.property (L.toSubmodule.smul_mem π wL.property)
    let correctedKer : f.ker.toSubmodule := ⟨(x' : V) - (π : A) • (w : V), hcorrectedKer⟩
    let corrected :
        N.toSubmodule := ⟨correctedKer, hcorrectedL⟩
    have hcorrected_eq :
        kernelIntersectionInclusion (A := A) (K := K) (G := G) f L corrected =
          x' - (π : A) • wL := by
      ext
      rfl
    have hpiw_zero :
        (Submodule.Quotient.mk ((π : A) • wL) : L.reduction) = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).2
      rw [StableLattice.maximalIdealSubmodule,
        ← Ideal.span_singleton_generator (IsLocalRing.maximalIdeal A),
        Submodule.ideal_span_singleton_smul]
      refine ⟨wL, show wL ∈ (⊤ : Submodule A L.toSubmodule) by trivial, ?_⟩
      rfl
    -- Replace `x'` by the corrected representative `x' - π w`, which lies in `L ∩ ker(f)`.
    simp only [IntertwiningMap.range, LinearMap.mem_range]
    refine ⟨Submodule.Quotient.mk corrected, ?_⟩
    change
      kernelIntersectionReductionInclusionA (A := A) (K := K) (G := G) f L
          (Submodule.Quotient.mk corrected) =
        (Submodule.Quotient.mk x' : L.reduction)
    rw [kernelIntersectionReductionInclusionA_apply_mk, hcorrected_eq]
    calc
      (Submodule.Quotient.mk (x' - (π : A) • wL) : L.reduction) =
          (Submodule.Quotient.mk x' : L.reduction) -
            (Submodule.Quotient.mk ((π : A) • wL) : L.reduction) := by
              rfl
      _ = Submodule.Quotient.mk x' := by
            simp [hpiw_zero]

private theorem kernelIntersectionReductionEquivKer
    {V W : Type u}
    [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
    [AddCommGroup W] [Module A W] [Module K W] [IsScalarTower A K W]
    {ρ : Representation K G V} {σ : Representation K G W}
    (f : ρ.IntertwiningMap σ) (L : StableLattice A ρ)
    (hf : Function.Surjective f.toLinearMap) :
    let N : StableLattice A f.ker.toRepresentation :=
      kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L
    let fbar :=
      reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf
    Nonempty (FDRep.of N.reductionRepresentation ≅ FDRep.of fbar.ker.toRepresentation) := by
  let N : StableLattice A f.ker.toRepresentation :=
    kernelIntersectionStableLattice (A := A) (K := K) (G := G) f L
  let fbar := reductionToImageStableLattice (A := A) (K := K) (G := G) f L hf
  let i := kernelIntersectionReductionInclusion (A := A) (K := K) (G := G) f L
  let ir : N.reductionRepresentation.IntertwiningMap i.range.toRepresentation :=
    i.toLinearMap.rangeRestrict.intertwiningMap_of_isIntertwiningMap
      N.reductionRepresentation i.range.toRepresentation fun g x ↦ by
        ext
        exact LinearMap.congr_fun (i.2 g) x
  have hir_bijective : Function.Bijective ir.toLinearMap := by
    -- The range restriction is automatically surjective, and injectivity is inherited from `i`.
    refine ⟨?_, ?_⟩
    · simpa [ir] using
        (LinearMap.injective_rangeRestrict_iff (f := i.toLinearMap)).2
          (kernelIntersectionReductionInclusion_injective
            (A := A) (K := K) (G := G) f L)
    · simpa [ir] using LinearMap.surjective_rangeRestrict i.toLinearMap
  have hir_iso :
      Nonempty (FDRep.of N.reductionRepresentation ≅ FDRep.of i.range.toRepresentation) := by
    -- Rebundle the descended inclusion into an isomorphism onto its range.
    exact fdRepIso_of_bijective_intertwining (G := G) ir hir_bijective
  have hrange_ker : i.range.toSubmodule = fbar.ker.toSubmodule := by
    -- The range of the descended inclusion is exactly the kernel of the descended quotient map.
    exact kernelIntersectionReductionInclusion_range_eq_ker
      (A := A) (K := K) (G := G) f L hf
  have hker_iso :
      Nonempty (FDRep.of i.range.toRepresentation ≅ FDRep.of fbar.ker.toRepresentation) := by
    -- Transport the range term to the actual kernel subrepresentation.
    exact ⟨Representation.Equiv.toFDRepIso
      (subrepresentation_equiv_of_toSubmodule_eq
        (G := G) (U := i.range) (W := fbar.ker) hrange_ker).some⟩
  rcases hir_iso with ⟨e₁⟩
  rcases hker_iso with ⟨e₂⟩
  exact ⟨e₁.trans e₂⟩

private theorem reductionClassLift_shortExact_generator_mem_ker
    (S : ShortComplex (FDRep K G)) (hS : S.ShortExact) :
    FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃ ∈
      (reductionClassLift hstable).ker := by
  classical
  rw [AddMonoidHom.mem_ker]
  let F : FDRep K G ⥤ ModuleCat K :=
    (forget₂ (FDRep K G) (Rep K G)) ⋙ (forget₂ (Rep K G) (ModuleCat K))
  have hSF : (S.map F).ShortExact := by
    -- Forgetting to `ModuleCat K` preserves the given short exact sequence.
    simpa [F] using hS.map_of_exact F
  let fRep : IntertwiningMap S.X₁.ρ S.X₂.ρ :=
    ((forget₂ (FDRep K G) (Rep K G)).map S.f).hom
  let gRep : IntertwiningMap S.X₂.ρ S.X₃.ρ :=
    ((forget₂ (FDRep K G) (Rep K G)).map S.g).hom
  let f : S.X₁.V →ₗ[K] S.X₂.V := fRep.toLinearMap
  let g : S.X₂.V →ₗ[K] S.X₃.V := gRep.toLinearMap
  have hExact : Function.Exact f g := by
    -- In `ModuleCat K`, short exactness is exactness of the underlying linear maps.
    simpa [F, f, g, fRep, gRep] using
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact (S.map F)).mp hSF.exact
  have hf : Function.Injective f := by
    -- The left map of a short exact sequence is mono, hence injective on vectors.
    exact (ModuleCat.mono_iff_injective _).1 hSF.mono_f
  have hg : Function.Surjective g := by
    -- The right map of a short exact sequence is epi, hence surjective on vectors.
    exact (ModuleCat.epi_iff_surjective _).1 hSF.epi_g
  let L₂ : StableLattice A S.X₂.ρ := Classical.choice (hstable S.X₂)
  let L₁ : StableLattice A S.X₁.ρ := Classical.choice (hstable S.X₁)
  let N : StableLattice A gRep.ker.toRepresentation :=
    kernelIntersectionStableLattice (A := A) (K := K) (G := G) gRep L₂
  let L₃ : StableLattice A S.X₃.ρ :=
    imageStableLattice (A := A) (K := K) (G := G) gRep L₂ hg
  let gbar :=
    reductionToImageStableLattice (A := A) (K := K) (G := G) gRep L₂ hg
  have hsourceKerRep :
      Nonempty (Representation.Equiv S.X₁.ρ gRep.ker.toRepresentation) := by
    -- Exactness identifies the source representation with the kernel of the right map.
    simpa [gRep] using source_repEquiv_kernel_of_shortExact S hS
  let L₁ker : StableLattice A gRep.ker.toRepresentation :=
    imageStableLattice (A := A) (K := K) (G := G)
      (Classical.choice hsourceKerRep).toIntertwiningMap L₁
      (Classical.choice hsourceKerRep).surjective
  have hmiddle :
      reductionClassLift hstable (FreeAbelianGroup.of S.X₂) =
        [FDRep.of L₂.reductionRepresentation]₀ := by
    -- The middle generator can be computed using the chosen middle lattice `L₂`.
    exact reductionClassLift_eq_reductionClass
      (A := A) (K := K) (G := G) hstable S.X₂ L₂
  have htarget :
      [FDRep.of L₃.reductionRepresentation]₀ =
        reductionClassLift hstable (FreeAbelianGroup.of S.X₃) := by
    -- The same lattice-independence step computes the right endpoint using the image lattice `L₃`.
    symm
    exact reductionClassLift_eq_reductionClass
      (A := A) (K := K) (G := G) hstable S.X₃ L₃
  have hsplit :
      [FDRep.of L₂.reductionRepresentation]₀ =
        [FDRep.of (V := ↥gbar.ker.toSubmodule) gbar.ker.toRepresentation]₀ +
          [FDRep.of L₃.reductionRepresentation]₀ := by
    -- The reduced quotient map onto the image lattice splits the middle class by its kernel.
    exact finiteRepGrothendieckClass_eq_kernel_add_target_of_surjective_intertwining
      (A := A) (G := G) gbar
      (reductionToImageStableLattice_surjective
        (A := A) (K := K) (G := G) gRep L₂ hg)
  have hkernel :
      [FDRep.of (V := ↥gbar.ker.toSubmodule) gbar.ker.toRepresentation]₀ =
        reductionClassLift hstable (FreeAbelianGroup.of S.X₁) := by
    -- Route correction: instead of comparing `ker(gbar)` to a transported range lattice, move
    -- directly through the kernel-intersection lattice on `ker(g)` and the source-to-kernel
    -- equivalence coming from short exactness.
    calc
      [FDRep.of (V := ↥gbar.ker.toSubmodule) gbar.ker.toRepresentation]₀ =
          [FDRep.of N.reductionRepresentation]₀ := by
            symm
            exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G)
              (kernelIntersectionReductionEquivKer
                (A := A) (K := K) (G := G) gRep L₂ hg)
      _ = [FDRep.of L₁ker.reductionRepresentation]₀ := by
            exact stableLatticeReduction_grothendieckClass_eq
              (A := A) (K := K) (G := G) gRep.ker.toRepresentation N L₁ker
      _ = [FDRep.of L₁.reductionRepresentation]₀ := by
            symm
            exact finiteRepGrothendieckClass_eq_of_nonempty_iso (L := k) (G := G)
              (reductionRepresentationEquivOfBijective
                (A := A) (K := K) (G := G)
                (Classical.choice hsourceKerRep).toIntertwiningMap L₁
                (Classical.choice hsourceKerRep).bijective)
      _ = reductionClassLift hstable (FreeAbelianGroup.of S.X₁) := by
            symm
            exact reductionClassLift_eq_reductionClass
              (A := A) (K := K) (G := G) hstable S.X₁ L₁
  -- Once the kernel term is identified with the reduced source, the Grothendieck relation is
  -- exactly LinearRepresentations_Serre_1977's short-exact-sequence relation after applying `reductionClassLift`.
  rw [AddMonoidHom.map_sub, AddMonoidHom.map_sub, hmiddle, hsplit, hkernel, ← htarget]
  abel

-- Proof sketch: choose stable lattices simultaneously in a short exact sequence of finite
-- dimensional `K[G]`-representations so that reduction modulo `𝔪_A` remains exact; then the
-- defining relation in `R_K(G)` maps to the corresponding short-exact-sequence relation in
-- `R_k(G)`.
private theorem finiteRepGrothendieckRelations_le_reductionClassLift_ker :
    finiteRepGrothendieckRelations K G ≤ (reductionClassLift hstable).ker := by
  -- It suffices to check the short-exact-sequence generators of the Grothendieck relations.
  rw [finiteRepGrothendieckRelations, AddSubgroup.closure_le]
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  exact reductionClassLift_shortExact_generator_mem_ker hstable S hS

/-- The decomposition homomorphism `d : R_K(G) → R_k(G)` induced by reducing a stable `A`-lattice
modulo the maximal ideal. On a generator `[V]₀`, it is computed from the reduction of any stable
`A`-lattice in `V`. -/
private noncomputable def decompositionHomAux : R₀[K](G) →+ R₀[k](G) :=
  QuotientAddGroup.lift
    (finiteRepGrothendieckRelations K G)
    (reductionClassLift hstable)
    (finiteRepGrothendieckRelations_le_reductionClassLift_ker hstable)

private theorem decompositionHomAux_finiteRepClass_eq
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    decompositionHomAux hstable [V]₀ = [FDRep.of L.reductionRepresentation]₀ := by
  classical
  let L₀ : StableLattice A V.ρ := Classical.choice (hstable V)
  -- Evaluate the quotient lift on the generator class `[V]₀`.
  change [FDRep.of L₀.reductionRepresentation]₀ = [FDRep.of L.reductionRepresentation]₀
  -- The main theorem identifies the reduction class for any two stable lattices in `V`.
  simpa [L₀] using
    stableLatticeReduction_grothendieckClass_eq
      (A := A) (K := K) (G := G) V.ρ L₀ L

end DecompositionHomAux

section DecompositionHom

variable [Finite G]
variable (A) (K) (G)

/-- The decomposition homomorphism `d : R_K(G) → R_k(G)` induced by reducing a stable `A`-lattice
modulo the maximal ideal. On a generator `[V]₀`, it is computed from the reduction of any stable
`A`-lattice in `V`. -/
noncomputable def decompositionHom : R₀[K](G) →+ R₀[k](G) :=
  decompositionHomAux fun V ↦
    exists_stableLattice A V.ρ

/-- On a generator class, the decomposition homomorphism is computed by reducing any chosen stable
lattice. -/
@[simp] theorem decompositionHom_finiteRepClass_eq
    (V : FDRep K G) (L : StableLattice A V.ρ) :
    decompositionHom A K G [V]₀ = [FDRep.of L.reductionRepresentation]₀ := by
  simpa [decompositionHom] using
    decompositionHomAux_finiteRepClass_eq
      (fun V ↦ exists_stableLattice A V.ρ)
      V L

end DecompositionHom

end ReductionGrothendieckClass

end Representation
