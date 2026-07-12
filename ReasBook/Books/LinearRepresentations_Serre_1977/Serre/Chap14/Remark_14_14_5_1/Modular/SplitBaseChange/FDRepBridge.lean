import Mathlib
import LinearRepresentations_Serre_1977.Chap02.Theorem_2_2_3_5

noncomputable section
universe u
open scoped TensorProduct MonoidAlgebra

namespace Serre.SplitBaseChange

/-- If every simple object of `FDRep F G` has a one-dimensional endomorphism algebra, then so
does every simple `F[G]`-module that is finite-dimensional over `F`.  This is the bridge from the
categorical "absolute simplicity" criterion on `FDRep` to the module-theoretic statement about
`Module.End (MonoidAlgebra F G) N`. -/
theorem finrank_end_eq_one_of_isSimpleModule
    {F : Type u} [Field F] {G : Type u} [Group G] [Finite G]
    (hF : ∀ (M : FDRep F G), CategoryTheory.Simple M → Module.finrank F (M ⟶ M) = 1)
    (N : Type u) [AddCommGroup N] [Module (MonoidAlgebra F G) N]
    [Module F N] [IsScalarTower F (MonoidAlgebra F G) N] [Module.Finite F N]
    (hN : IsSimpleModule (MonoidAlgebra F G) N) :
    Module.finrank F (Module.End (MonoidAlgebra F G) N) = 1 := by
  -- Realise `N` as a representation on the carrier `N` itself.
  letI ρ : Representation F G N := Representation.ofModule' N
  -- The `F[G]`-action coming from `ρ.asModule` agrees with the ambient one on `N`.
  have hAlg : ∀ (r : MonoidAlgebra F G) (y : N), ρ.asAlgebraHom r y = r • y := by
    intro r y
    change (Representation.ofModule' N).asAlgebraHom r y = r • y
    rw [Representation.asAlgebraHom_def, Representation.ofModule']
    simp [Algebra.lsmul_coe]
  -- Upgrade the `F`-linear `asModuleEquiv` to an `F[G]`-linear equivalence `ρ.asModule ≃ N`.
  let eM : ρ.asModule ≃ₗ[MonoidAlgebra F G] N :=
    { ρ.asModuleEquiv.toAddEquiv with
      map_smul' := fun r x => by
        change ρ.asModuleEquiv (r • x) = r • ρ.asModuleEquiv x
        rw [Representation.asModuleEquiv_map_smul, hAlg] }
  -- Transport simplicity of `N` to irreducibility of `ρ` through the subobject lattices.
  let oiso : Subrepresentation ρ ≃o Submodule (MonoidAlgebra F G) N :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)).trans
      (Submodule.orderIsoMapComap eM)
  haveI : IsSimpleModule (MonoidAlgebra F G) N := hN
  haveI hirr : Representation.IsIrreducible ρ := oiso.isSimpleOrder
  -- The associated `FDRep` object is simple, so `hF` applies.
  let X : FDRep F G := FDRep.of ρ
  haveI hXirr : Representation.IsIrreducible X.ρ := hirr
  haveI hXsimple : CategoryTheory.Simple X := Representation.FDRep.simple_of_isIrreducible X
  have hX1 : Module.finrank F (X ⟶ X) = 1 := hF X hXsimple
  -- Identify `X ⟶ X` with `Module.End (MonoidAlgebra F G) N` as `F`-vector spaces.
  let e1 : (X ⟶ X) ≃ₗ[F] (Representation.linHom X.ρ X.ρ).invariants :=
    (Representation.linHom.invariantsEquivFDRepHom X X).symm
  let e2 : (Representation.linHom ρ ρ).invariants ≃ₗ[F]
      Representation.IntertwiningMap ρ ρ :=
    Representation.invariantsEquivIntertwiningMap ρ ρ
  let e3 : Representation.IntertwiningMap ρ ρ ≃ₗ[F] Module.End (MonoidAlgebra F G) ρ.asModule :=
    (Representation.IntertwiningMap.equivAlgEnd ρ).toLinearEquiv
  let e4 : Module.End (MonoidAlgebra F G) ρ.asModule ≃ₗ[F]
      Module.End (MonoidAlgebra F G) N :=
    { (LinearEquiv.conjRingEquiv eM : Module.End (MonoidAlgebra F G) ρ.asModule ≃+*
          Module.End (MonoidAlgebra F G) N) with
      map_smul' := fun c φ => by
        ext x
        change eM ((c • φ) (eM.symm x)) = c • eM (φ (eM.symm x))
        rw [LinearMap.smul_apply]
        exact LinearMapClass.map_smul_of_tower eM c (φ (eM.symm x)) }
  have hfin : Module.finrank F (Module.End (MonoidAlgebra F G) N) =
      Module.finrank F (X ⟶ X) :=
    (LinearEquiv.finrank_eq (e1.trans (e2.trans (e3.trans e4)))).symm
  rw [hfin, hX1]

end Serre.SplitBaseChange
