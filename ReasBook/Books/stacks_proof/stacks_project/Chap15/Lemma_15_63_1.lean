import stacks_proof.stacks_project.Chap15.«15_63_0_3»
import stacks_proof.stacks_project.Chap15.Definition_15_61_1
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ModuleCat
open ModuleCat.MonoidalCategory
open scoped DerivedTensorProduct TensorProduct

attribute [local instance] HasDerivedCategory.standard

section

variable {R : Type u} [CommRing R]
variable {A : Type u} [CommRing A] [Algebra R A]

local notation "HR" => DerivedCategory.homologyFunctor (ModuleCat R)
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation "single0" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
set_option quotPrecheck false in
local notation "TorA(" n ")" => ((Tor (ModuleCat R) n).flip.obj (of R A))

/- Domain-style sampling for Lemma 15.63.1:
- primary domain: first-variable functoriality of `Tor[R, n]( -, A )` together with the
  multiplicative structure on the source-facing Tor groups `Tor[R, n](B, A)`;
- sampled owner declarations:
  `Tor[R, p](M, N)`,
  `Functor.map`,
  `derivedCohomologyProduct`,
  `derivedCategory_tensorObj_iso_derivedTensorProduct`;
  best owner abstraction: the core/canonical owner is still the Tor bifunctor
  `Tor (ModuleCat R) n`, so the first-variable map should reuse `Functor.map` directly rather than
  a parallel public wrapper; because the file also defines the source-facing Tor product
  `torProduct`, the main public statement should stay at the source-facing Tor layer, and the
  realized `A`-linear comparison maps from the imported bridge files remain proof input rather than
  a second public API layer in this file;
- primitive data: the `R`-algebra `A`, the degree `n`, and an `R`-algebra map `g : B →ₐ[R] C`;
- derived API: the source-facing Tor product and unit on `Tor[R, *](B, A)`, together with the
  compatibility theorem `torMap_preserves_product_and_unit`.

Source/core/bridge triage:
- `source-facing`: the Tor product on `Tor[R, *](B, A)`;
- `core/canonical`: `Tor[R, p](M, N)`, `Functor.flip`, and ordinary `Functor.map`;
- `bridge/view`: the canonical `A`-linear realization
  `H^{-n}(B[0] ⊗_R^{\mathbf L} A)` and the imported derived-category comparison maps that justify
  the Tor-level construction, but do not remain as a parallel public wrapper surface here. -/

private theorem torProduct_degree_eq (n m : ℕ) :
    (-(n : ℤ) + -(m : ℤ)) = -((n + m : ℕ) : ℤ) := by
  omega

namespace CategoryTheory

variable (A)

private noncomputable instance : (DerivedCategory.Q : CpxR ⥤ DModR).Monoidal := by
  change (((HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)) ⋙
      (DerivedCategory.Qh :
        HomotopyCategory (ModuleCat R) (ComplexShape.up ℤ) ⥤ DModR))).Monoidal
  infer_instance

local instance : MonoidalCategory DModR := inferInstance

/-- Helper for Lemma 15.63.1: right tensoring a degree-zero single cochain complex stays a
degree-zero single complex. -/
private noncomputable def singleZeroTensorRightComplexIso
    (M N : ModuleCat R) :
    ((CategoryTheory.MonoidalCategory.tensorRight N).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M) ≅
      (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (of R ((↑M) ⊗[R] ↑N)) :=
  -- Proof comment: `singleMapHomologicalComplex` is the canonical owner of the statement that
  -- mapping a degree-zero single complex through `tensorRight N` stays degree-zero.
  (HomologicalComplex.singleMapHomologicalComplex
    (CategoryTheory.MonoidalCategory.tensorRight N) (ComplexShape.up ℤ) (0 : ℤ)).app M

private theorem singleZeroTensorComplex_eq_tensorObj (M N : ModuleCat R) :
    (CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (of R ((↑M) ⊗[R] ↑N)) =
      HomologicalComplex.tensorObj
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N) := by
  -- Route correction: the literal equality route is the wrong abstraction boundary here.
  -- TODO: first compare `M[0] ⊗ N[0]` with right tensoring `M[0]` by `N`, then compose with
  -- `singleZeroTensorRightComplexIso M N` to replace this equality witness by an iso-based bridge.
  sorry

private noncomputable def singleZeroDerivedTensorModuleIso (M N : ModuleCat R) :
    (Functor.obj single0 M ⊗[R]^L Functor.obj single0 N) ≅
      Functor.obj single0 (of R ((↑M) ⊗[R] ↑N)) :=
  ((((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      (of R ((↑M) ⊗[R] ↑N))).symm) ≪≫
    (DerivedCategory.Q.mapIso (eqToIso (singleZeroTensorComplex_eq_tensorObj M N))) ≪≫
      (Functor.Monoidal.μIso (DerivedCategory.Q : CpxR ⥤ DModR)
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj M)
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj N)).symm ≪≫
        (((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app M) ⊗ᵢ
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app N)) ≪≫
          (derivedCategory_tensorObj_iso_derivedTensorProduct
            (Functor.obj single0 M)
            (Functor.obj single0 N))).symm

private noncomputable def singleZeroTensorObjIso (M N : ModuleCat R) :
    (Functor.obj single0 M ⊗ Functor.obj single0 N) ≅
      Functor.obj single0 (of R ((↑M) ⊗[R] ↑N)) :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      (Functor.obj single0 M)
      (Functor.obj single0 N)) ≪≫
    singleZeroDerivedTensorModuleIso M N

private theorem torProduct_reindex (B : Type u) [CommRing B] [Algebra R B] (n m : ℕ) :
    (HR (-(n : ℤ) + -(m : ℤ))).obj
        ((Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A)) ⊗[R]^L
          (Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A))) =
      (HR (-((n + m : ℕ) : ℤ))).obj
        ((Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A)) ⊗[R]^L
          (Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A))) := by
  simpa using congrArg
    (fun i : ℤ ↦
      (HR i).obj
        ((Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A)) ⊗[R]^L
          (Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A))))
    (torProduct_degree_eq n m)

/-- Internal equality witness used to build the public comparison isomorphism
`Tor[R, n](B, A) ≅ H^{-n}(B[0] ⊗_R^{\mathbf L} A)`. -/
private theorem tor_eq_homology_of_singleTensor
    (B : Type u) [CommRing B] [Algebra R B] (n : ℕ) :
    Tor[R, n](B, A) =
      (HR (-(n : ℤ))).obj
        (Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A)) := by
  symm
  sorry

/-- The canonical comparison isomorphism
`Tor[R, n](B, A) ≅ H^{-n}(B[0] ⊗_R^{\mathbf L} A)`. -/
noncomputable abbrev torSingleTensorIso
    (B : Type u) [CommRing B] [Algebra R B] (n : ℕ) :
    Tor[R, n](B, A) ≅
      (HR (-(n : ℤ))).obj
        (Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A)) :=
  eqToIso (tor_eq_homology_of_singleTensor A B n)

private noncomputable def torDerivedMultiplication
    (B : Type u) [CommRing B] [Algebra R B] :
    let B0 : DModR := Functor.obj single0 (of R B)
    let A0 : DModR := Functor.obj single0 (of R A)
    let torObjRB : DModR := B0 ⊗[R]^L A0
    torObjRB ⊗[R]^L torObjRB ⟶ torObjRB :=
  let B0 : DModR := Functor.obj single0 (of R B)
  let A0 : DModR := Functor.obj single0 (of R A)
  let torObjRB : DModR := B0 ⊗[R]^L A0
  let μB : Functor.obj single0 (of R (B ⊗[R] B)) ⟶ B0 :=
    (single0).map
      (ofHom
        ((Algebra.TensorProduct.productMap (AlgHom.id R B) (AlgHom.id R B)).toLinearMap))
  let μA : Functor.obj single0 (of R (A ⊗[R] A)) ⟶ A0 :=
    (single0).map
      (ofHom
        ((Algebra.TensorProduct.productMap (AlgHom.id R A) (AlgHom.id R A)).toLinearMap))
  (derivedCategory_tensorObj_iso_derivedTensorProduct torObjRB torObjRB).inv ≫
    ((derivedCategory_tensorObj_iso_derivedTensorProduct B0 A0).inv ⊗ₘ
      (derivedCategory_tensorObj_iso_derivedTensorProduct B0 A0).inv) ≫
    (α_ B0 A0 (B0 ⊗ A0)).hom ≫
    (𝟙 B0 ⊗ₘ (α_ A0 B0 A0).inv) ≫
    (𝟙 B0 ⊗ₘ ((β_ A0 B0).hom ⊗ₘ 𝟙 A0)) ≫
    (𝟙 B0 ⊗ₘ (α_ B0 A0 A0).hom) ≫
    (α_ B0 B0 (A0 ⊗ A0)).inv ≫
    ((singleZeroTensorObjIso (of R B) (of R B)).hom ⊗ₘ
      (singleZeroTensorObjIso (of R A) (of R A)).hom) ≫
    (μB ⊗ₘ μA) ≫
    (derivedCategory_tensorObj_iso_derivedTensorProduct B0 A0).hom

/-- The canonical Tor product
`Tor[R, n](B, A) ⊗ Tor[R, m](B, A) ⟶ Tor[R, n + m](B, A)`. -/
noncomputable def torProduct (B : Type u) [CommRing B] [Algebra R B] (n m : ℕ) :
    (Tor[R, n](B, A) ⊗ Tor[R, m](B, A) : ModuleCat R) ⟶ Tor[R, n + m](B, A) :=
  let torObjRB : DModR := Functor.obj single0 (of R B) ⊗[R]^L Functor.obj single0 (of R A)
  ((torSingleTensorIso A B n).hom ⊗ₘ (torSingleTensorIso A B m).hom) ≫
    derivedCohomologyProduct (-(n : ℤ)) (-(m : ℤ)) torObjRB torObjRB ≫
    eqToHom (torProduct_reindex A B n m) ≫
      (HR (-((n + m : ℕ) : ℤ))).map (torDerivedMultiplication A B) ≫
        (torSingleTensorIso A B (n + m)).inv

/-- The canonical unit map
`Tor[R, 0](R, A) ⟶ Tor[R, 0](B, A)` induced by the structure map `R →ₐ[R] B`. -/
abbrev torUnit (B : Type u) [CommRing B] [Algebra R B] :
    Tor[R, 0](R, A) ⟶ Tor[R, 0](B, A) :=
  (TorA(0)).map (ofHom (Algebra.ofId R B).toLinearMap)

section FirstVariableMaps

variable {B C : Type u} [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
variable (g : B →ₐ[R] C)

/-- The canonical first-variable map on `Tor[R, n]( -, A )` induced by `g : B →ₐ[R] C`
preserves the canonical Tor product. -/
theorem torMap_preserves_product (n m : ℕ) :
    CommSq
      (((TorA(n)).map (ofHom g.toLinearMap)) ⊗ₘ
        ((TorA(m)).map (ofHom g.toLinearMap)))
      (torProduct A B n m)
      (torProduct A C n m)
      ((TorA(n + m)).map (ofHom g.toLinearMap)) := by
  sorry

/-- The first-variable map on `Tor[R, 0]( -, A )` induced by `g : B →ₐ[R] C` sends the canonical
Tor unit for `B` to the canonical Tor unit for `C`. -/
theorem torMap_comp_unit :
    torUnit A C =
      torUnit A B ≫ (TorA(0)).map (ofHom g.toLinearMap) := by
  -- Proof comment: the degree-zero unit is induced by the algebra structure map, so the claim is
  -- just functoriality of `(TorA(0)).map` together with `g.comp (Algebra.ofId R B) = ofId`.
  simp [torUnit, Functor.map_comp]

/-- Lemma 15.63.1: the first-variable map on `Tor[R, *]( -, A )` induced by `g : B →ₐ[R] C`
is compatible with the canonical Tor product and unit. This is the source-facing Tor-level form of
the statement that the induced map on `Tor_*^R(-, A)` is an algebra homomorphism. -/
@[stacks 068K]
theorem torMap_preserves_product_and_unit :
    (∀ n m : ℕ,
      CommSq
        (((TorA(n)).map (ofHom g.toLinearMap)) ⊗ₘ
          ((TorA(m)).map (ofHom g.toLinearMap)))
        (torProduct A B n m)
        (torProduct A C n m)
        ((TorA(n + m)).map (ofHom g.toLinearMap))) ∧
      torUnit A C =
        torUnit A B ≫ (TorA(0)).map (ofHom g.toLinearMap) := by
  constructor
  · intro n m
    simpa using torMap_preserves_product A g n m
  · simpa using torMap_comp_unit A g

end FirstVariableMaps

end CategoryTheory

end
