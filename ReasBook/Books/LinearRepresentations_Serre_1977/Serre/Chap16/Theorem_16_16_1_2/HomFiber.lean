import Mathlib
import LinearRepresentations_Serre_1977.Serre.Chap15.Definition_15_15_3_1

noncomputable section

universe u

namespace Representation

open CategoryTheory
open scoped MonoidAlgebra TensorProduct

/-!
# Brauer reciprocity "common owner" Hom-fiber equality

Abstract setting for Serre's Chapter 16 Brauer reciprocity argument.  Over a PID `A` we have a
finite group `G`, a finite projective `A[G]`-module `Q` (also finite free over `A`) and a finite
free `A[G]`-module `T`.  We prove that the `A`-module
`Q →ₗ[A[G]] T` is finite free over `A`, that for any commutative `A`-algebra `S` base change gives a
natural isomorphism
`S ⊗[A] (Q →ₗ[A[G]] T) ≃ₗ[S] ((scalarExtension ρQ).asModule →ₗ[S[G]] (scalarExtension ρT).asModule)`,
and that consequently the `S`-dimension of the intertwiner space is independent of the field
base `S`.  The last statement is the "fiber equality" used in Brauer reciprocity:
`finrank K (...) = finrank kk (...)` for any two `A`-fields `K`, `kk`.
-/

variable {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
variable {G : Type u} [Group G] [Finite G]
variable {Q : Type u} [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
variable {T : Type u} [AddCommGroup T] [Module A T] [Module A[G] T] [IsScalarTower A A[G] T]

section HFree

variable [Module.Projective A[G] Q] [Module.Finite A Q] [Module.Free A Q]
variable [Module.Finite A T] [Module.Free A T]

/-- The forgetful `A`-linear injection `(Q →ₗ[A[G]] T) ↪ (Q →ₗ[A] T)`. -/
private def homForget : (Q →ₗ[A[G]] T) →ₗ[A] (Q →ₗ[A] T) :=
  LinearMap.restrictScalarsₗ A A[G] Q T A

private theorem homForget_injective :
    Function.Injective (homForget (A := A) (G := G) (Q := Q) (T := T)) :=
  LinearMap.restrictScalars_injective A

/-- The equivariant Hom-module is finite over the PID base `A`. -/
instance homFinite : Module.Finite A (Q →ₗ[A[G]] T) :=
  Module.Finite.of_injective (homForget (A := A) (G := G) (Q := Q) (T := T))
    (homForget_injective (A := A) (G := G) (Q := Q) (T := T))

/-- The equivariant Hom-module is torsion free over the domain `A`, being (via the
restriction-of-scalars injection) a submodule of the torsion-free module `Q →ₗ[A] T`. -/
instance homIsTorsionFree : Module.IsTorsionFree A (Q →ₗ[A[G]] T) :=
  Function.Injective.moduleIsTorsionFree
    (homForget (A := A) (G := G) (Q := Q) (T := T))
    (homForget_injective (A := A) (G := G) (Q := Q) (T := T)) (fun _ _ => rfl)

/-- **(1)** The equivariant Hom-module is finite free over the PID base `A`. -/
instance homFree : Module.Free A (Q →ₗ[A[G]] T) :=
  Module.free_of_finite_type_torsion_free'

end HFree

section BaseChange

variable {S : Type u} [CommRing S] [Algebra A S]

/-- The representation of `G` on `Q` coming from its `A[G]`-module structure. -/
abbrev ρQ : Representation A G Q := Representation.ofModule' Q

/-- The representation of `G` on `T` coming from its `A[G]`-module structure. -/
abbrev ρT : Representation A G T := Representation.ofModule' T

/-- Helper: the representation `ofModule' Q` evaluated at `g` is left multiplication by the
generator `single g 1` of the group algebra. -/
private theorem ρQ_apply (g : G) (x : Q) :
    (ρQ : Representation A G Q) g x = MonoidAlgebra.of A G g • x := by
  simp [ρQ, Representation.ofModule', MonoidAlgebra.of]

private theorem ρT_apply (g : G) (x : T) :
    (ρT : Representation A G T) g x = MonoidAlgebra.of A G g • x := by
  simp [ρT, Representation.ofModule', MonoidAlgebra.of]

/-- Helper: `(scalarExtension ρ) g` is the base change of `ρ g`. -/
private theorem scalarExtension_apply_eq_baseChange
    {W : Type u} [AddCommGroup W] [Module A W] (ρ : Representation A G W) (g : G) :
    (Representation.scalarExtension (k := S) ρ) g = LinearMap.baseChange S (ρ g) := by
  simp [Representation.scalarExtension, Module.End.baseChangeHom, LinearMap.baseChangeHom_apply]

/-- Helper: an `A[G]`-linear map `f : Q →ₗ[A[G]] T`, viewed as an `A`-linear map, intertwines the
`A`-representations `ρQ` and `ρT`. -/
private theorem homForget_intertwines (f : Q →ₗ[A[G]] T) (g : G) :
    (f.restrictScalars A) ∘ₗ (ρQ : Representation A G Q) g
      = (ρT : Representation A G T) g ∘ₗ (f.restrictScalars A) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
  rw [ρQ_apply, ρT_apply, map_smul]

/-- Helper: the base change of `f.restrictScalars A` intertwines the scalar-extended
representations, hence is an intertwining map. -/
private theorem baseChange_intertwines (f : Q →ₗ[A[G]] T) (g : G) :
    LinearMap.baseChange S (f.restrictScalars A)
        ∘ₗ (Representation.scalarExtension (k := S) (ρQ : Representation A G Q)) g
      = (Representation.scalarExtension (k := S) (ρT : Representation A G T)) g
        ∘ₗ LinearMap.baseChange S (f.restrictScalars A) := by
  rw [scalarExtension_apply_eq_baseChange, scalarExtension_apply_eq_baseChange,
    ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, homForget_intertwines]

/-- Abbreviation for the target intertwiner module over `S`. -/
abbrev scalarExtIntertwiner (A : Type u) [CommRing A] (G : Type u) [Group G]
    (Q : Type u) [AddCommGroup Q] [Module A Q] [Module A[G] Q] [IsScalarTower A A[G] Q]
    (T : Type u) [AddCommGroup T] [Module A T] [Module A[G] T] [IsScalarTower A A[G] T]
    (S : Type u) [CommRing S] [Algebra A S] : Type u :=
  Representation.IntertwiningMap
    (Representation.scalarExtension (k := S) (ρQ : Representation A G Q))
    (Representation.scalarExtension (k := S) (ρT : Representation A G T))

/-- The canonical `A`-module structure on the intertwiner space over `S`, obtained from its
`S`-module structure via the algebra map `A → S`. -/
instance scalarExtIntertwinerModuleA :
    Module A (scalarExtIntertwiner A G Q T S) :=
  Module.compHom _ (algebraMap A S)

instance scalarExtIntertwinerTower :
    IsScalarTower A S (scalarExtIntertwiner A G Q T S) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/-- The intertwining map between scalar extensions obtained by base changing an equivariant
linear map. -/
def baseChangeIntertwining (f : Q →ₗ[A[G]] T) :
    scalarExtIntertwiner A G Q T S where
  toLinearMap := LinearMap.baseChange S (f.restrictScalars A)
  isIntertwining' g := baseChange_intertwines f g

@[simp] theorem baseChangeIntertwining_toLinearMap (f : Q →ₗ[A[G]] T) :
    (baseChangeIntertwining (S := S) f).toLinearMap
      = LinearMap.baseChange S (f.restrictScalars A) :=
  rfl

/-- The `A`-linear map sending an equivariant `f` to the base-changed intertwiner. -/
def homBaseChangeMap :
    (Q →ₗ[A[G]] T) →ₗ[A] scalarExtIntertwiner A G Q T S where
  toFun := baseChangeIntertwining
  map_add' f f' := by
    apply Representation.IntertwiningMap.ext
    simp [baseChangeIntertwining_toLinearMap, LinearMap.restrictScalars_add,
      LinearMap.baseChange_add]
  map_smul' a f := by
    apply Representation.IntertwiningMap.ext
    -- Both sides have underlying linear map `(algebraMap A S a) • baseChange S (f|_A)`.
    have hsmulA : (a • baseChangeIntertwining (S := S) f).toLinearMap
        = (algebraMap A S a) • (baseChangeIntertwining (S := S) f).toLinearMap := rfl
    rw [RingHom.id_apply, hsmulA, baseChangeIntertwining_toLinearMap,
      baseChangeIntertwining_toLinearMap]
    have hrs : (a • f).restrictScalars A = a • (f.restrictScalars A) := by
      ext x; simp [LinearMap.restrictScalars_apply, algebraMap_smul]
    rw [hrs, LinearMap.baseChange_smul]
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
        simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul,
          LinearMap.restrictScalars_apply]
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        congr 1
        rw [Algebra.smul_def, smul_eq_mul]
    | add y z hy hz => simp only [map_add, hy, hz]

@[simp] theorem homBaseChangeMap_apply (f : Q →ₗ[A[G]] T) :
    (homBaseChangeMap (S := S) f)
      = baseChangeIntertwining f :=
  rfl

/-- The `S`-bilinear data `s ↦ s • (homBaseChangeMap ·)` used to define the base-change map on the
tensor product. -/
private def homBaseChangeBilin :
    S →ₗ[S] ((Q →ₗ[A[G]] T) →ₗ[A] scalarExtIntertwiner A G Q T S) where
  toFun s := s • (homBaseChangeMap (S := S))
  map_add' s s' := by simp [add_smul]
  map_smul' c s := by simp [smul_smul]

/-- **(2)** The natural base-change `S`-linear map
`S ⊗[A] (Q →ₗ[A[G]] T) →ₗ[S] (intertwiner space over S)`. -/
def homBaseChange :
    TensorProduct A S (Q →ₗ[A[G]] T) →ₗ[S] scalarExtIntertwiner A G Q T S :=
  TensorProduct.AlgebraTensorModule.lift (homBaseChangeBilin (S := S))

@[simp] theorem homBaseChange_tmul (s : S) (f : Q →ₗ[A[G]] T) :
    homBaseChange (S := S) (s ⊗ₜ f)
      = s • baseChangeIntertwining f :=
  rfl

end BaseChange

section BaseChangeEquiv

variable {S : Type u} [CommRing S] [Algebra A S]

/-- Helper: for any `A[G]`-module `W`, the representation `ofModule' W` evaluated at `g` is left
multiplication by `of A G g`. -/
private theorem ofModule'_apply {W : Type u} [AddCommGroup W] [Module A W] [Module A[G] W]
    [IsScalarTower A A[G] W] (g : G) (x : W) :
    (Representation.ofModule' W : Representation A G W) g x = MonoidAlgebra.of A G g • x := by
  simp [Representation.ofModule', MonoidAlgebra.of]

/-! ### A generic base-change map

We need a version of `homBaseChange` whose source `A[G]`-module is an explicit argument, so we can
instantiate it both at the section's `Q` and at the free module `Fin n → A[G]`. -/

/-- Generic base-change intertwiner: base change of an equivariant map `f : Q' →ₗ[A[G]] T'`. -/
private def genBaseChangeIntertwining
    (Q' : Type u) [AddCommGroup Q'] [Module A Q'] [Module A[G] Q'] [IsScalarTower A A[G] Q']
    (T' : Type u) [AddCommGroup T'] [Module A T'] [Module A[G] T'] [IsScalarTower A A[G] T']
    (f : Q' →ₗ[A[G]] T') :
    scalarExtIntertwiner A G Q' T' S where
  toLinearMap := LinearMap.baseChange S (f.restrictScalars A)
  isIntertwining' g := by
    have hf : (f.restrictScalars A) ∘ₗ (Representation.ofModule' Q' : Representation A G Q') g
        = (Representation.ofModule' T' : Representation A G T') g ∘ₗ (f.restrictScalars A) := by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      rw [ofModule'_apply, ofModule'_apply, map_smul]
    rw [scalarExtension_apply_eq_baseChange, scalarExtension_apply_eq_baseChange,
      ← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, hf]

@[simp] private theorem genBaseChangeIntertwining_toLinearMap
    (Q' : Type u) [AddCommGroup Q'] [Module A Q'] [Module A[G] Q'] [IsScalarTower A A[G] Q']
    (T' : Type u) [AddCommGroup T'] [Module A T'] [Module A[G] T'] [IsScalarTower A A[G] T']
    (f : Q' →ₗ[A[G]] T') :
    (genBaseChangeIntertwining (S := S) Q' T' f).toLinearMap
      = LinearMap.baseChange S (f.restrictScalars A) :=
  rfl

/-- The generic base-change `A`-linear map `(Q' →ₗ[A[G]] T') →ₗ[A] scalarExtIntertwiner …`. -/
private def genHomBaseChangeMap
    (Q' : Type u) [AddCommGroup Q'] [Module A Q'] [Module A[G] Q'] [IsScalarTower A A[G] Q']
    (T' : Type u) [AddCommGroup T'] [Module A T'] [Module A[G] T'] [IsScalarTower A A[G] T'] :
    (Q' →ₗ[A[G]] T') →ₗ[A] scalarExtIntertwiner A G Q' T' S where
  toFun := genBaseChangeIntertwining Q' T'
  map_add' f f' := by
    apply Representation.IntertwiningMap.ext
    simp [genBaseChangeIntertwining_toLinearMap, LinearMap.restrictScalars_add,
      LinearMap.baseChange_add]
  map_smul' a f := by
    apply Representation.IntertwiningMap.ext
    have hsmulA : (a • genBaseChangeIntertwining (S := S) Q' T' f).toLinearMap
        = (algebraMap A S a) • (genBaseChangeIntertwining (S := S) Q' T' f).toLinearMap := rfl
    rw [RingHom.id_apply, hsmulA, genBaseChangeIntertwining_toLinearMap,
      genBaseChangeIntertwining_toLinearMap]
    have hrs : (a • f).restrictScalars A = a • (f.restrictScalars A) := by
      ext x; simp [LinearMap.restrictScalars_apply]
    rw [hrs, LinearMap.baseChange_smul]
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s x =>
        simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul,
          LinearMap.restrictScalars_apply]
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul']
        congr 1
        rw [Algebra.smul_def, smul_eq_mul]
    | add y z hy hz => simp only [map_add, hy, hz]

/-- The generic base-change `S`-linear map
`S ⊗[A] (Q' →ₗ[A[G]] T') →ₗ[S] scalarExtIntertwiner A G Q' T' S`. -/
private def genHomBaseChange
    (Q' : Type u) [AddCommGroup Q'] [Module A Q'] [Module A[G] Q'] [IsScalarTower A A[G] Q']
    (T' : Type u) [AddCommGroup T'] [Module A T'] [Module A[G] T'] [IsScalarTower A A[G] T'] :
    TensorProduct A S (Q' →ₗ[A[G]] T') →ₗ[S] scalarExtIntertwiner A G Q' T' S :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun s => s • (genHomBaseChangeMap (S := S) Q' T')
      map_add' := fun s s' => by simp [add_smul]
      map_smul' := fun c s => by simp [smul_smul] }

@[simp] private theorem genHomBaseChange_tmul
    (Q' : Type u) [AddCommGroup Q'] [Module A Q'] [Module A[G] Q'] [IsScalarTower A A[G] Q']
    (T' : Type u) [AddCommGroup T'] [Module A T'] [Module A[G] T'] [IsScalarTower A A[G] T']
    (s : S) (f : Q' →ₗ[A[G]] T') :
    genHomBaseChange (S := S) Q' T' (s ⊗ₜ f) = s • genBaseChangeIntertwining Q' T' f :=
  rfl

/-! ### The free case

We prove that `genHomBaseChange (Fin n → A[G]) T` is bijective.  The strategy is to identify, on each
side, with `Fin n → (S ⊗[A] T)` and check that the map corresponds to the identity. -/

/-- The `S`-linear identification `S ⊗[A] A[G] ≃ₗ[S] S[G]` (at the level of underlying finitely
supported functions; `A[G] = G →₀ A`). -/
private noncomputable def sTensorGroupAlgebra :
    TensorProduct A S A[G] ≃ₗ[S] MonoidAlgebra S G :=
  letI := Classical.decEq G
  TensorProduct.finsuppScalarRight A S S G

/-- Value of `sTensorGroupAlgebra` on a pure tensor, pointwise. -/
private theorem sTensorGroupAlgebra_tmul_apply (s : S) (p : A[G]) (g : G) :
    (sTensorGroupAlgebra (A := A) (S := S) (G := G)) (s ⊗ₜ[A] p) g = p g • s := by
  classical
  show (TensorProduct.finsuppScalarRight A S S G) (s ⊗ₜ[A] p) g = p g • s
  exact TensorProduct.finsuppScalarRight_apply_tmul_apply s p g

/-- Helper: `sTensorGroupAlgebra` intertwines the left multiplication by `of g` on `S ⊗[A] A[G]`
(coming from the `A[G]`-module self-action) with the left multiplication by `of S G g` on `S[G]`. -/
private theorem sTensorGroupAlgebra_of_smul (g : G) (s : S) (p : A[G]) :
    (sTensorGroupAlgebra (A := A) (S := S) (G := G))
        (s ⊗ₜ[A] ((MonoidAlgebra.of A G g • p : A[G])))
      = MonoidAlgebra.of S G g •
        (sTensorGroupAlgebra (A := A) (S := S) (G := G)) (s ⊗ₜ[A] p) := by
  classical
  -- Both sides are finitely supported functions; compare them pointwise at each `h : G`.
  ext h
  rw [sTensorGroupAlgebra_tmul_apply]
  -- LHS: `(of g • p) h • s = (single g 1 * p) h • s`.
  have hLHS : (MonoidAlgebra.of A G g • p) h = p (g⁻¹ * h) := by
    rw [smul_eq_mul, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, one_mul]
  -- RHS: `(of S G g • (sTensorGroupAlgebra (s⊗p))) h = (sTensorGroupAlgebra (s⊗p)) (g⁻¹ * h)`.
  have hRHS : (MonoidAlgebra.of S G g •
        (sTensorGroupAlgebra (A := A) (S := S) (G := G)) (s ⊗ₜ[A] p)) h
      = (sTensorGroupAlgebra (A := A) (S := S) (G := G)) (s ⊗ₜ[A] p) (g⁻¹ * h) := by
    rw [smul_eq_mul, MonoidAlgebra.of_apply, MonoidAlgebra.single_mul_apply, one_mul]
  rw [hLHS, hRHS, sTensorGroupAlgebra_tmul_apply]

/-- The underlying `S`-linear carrier of the free identification:
`S ⊗[A] (Fin n → A[G]) ≃ Fin n → (S ⊗[A] A[G]) ≃ Fin n → S[G]`. -/
private noncomputable def freeScalarExtCarrier (n : ℕ) :
    (Representation.scalarExtension (k := S)
        (Representation.ofModule' (k := A) (G := G) (Fin n → A[G]))).asModule ≃ₗ[S]
      (Fin n → S[G]) :=
  (TensorProduct.piRight A S S (fun _ : Fin n => A[G])).trans
    (LinearEquiv.piCongrRight fun _ : Fin n => (sTensorGroupAlgebra))

/-- The carrier evaluated on a pure tensor, pointwise. -/
private theorem freeScalarExtCarrier_tmul_apply (n : ℕ) (s : S) (z : Fin n → A[G]) (j : Fin n) :
    (freeScalarExtCarrier (S := S) n) (s ⊗ₜ[A] z) j = sTensorGroupAlgebra (s ⊗ₜ[A] (z j)) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `S[G]`-module identification of the scalar extension of the free `A[G]`-module
`Fin n → A[G]` with the free `S[G]`-module `Fin n → S[G]`. -/
private def freeScalarExtAsModuleEquiv (n : ℕ) :
    (Representation.scalarExtension (k := S)
        (Representation.ofModule' (k := A) (G := G) (Fin n → A[G]))).asModule ≃ₗ[S[G]]
      (Fin n → S[G]) := by
  classical
  refine
    { toFun := freeScalarExtCarrier (S := S) n
      invFun := (freeScalarExtCarrier (S := S) n).symm
      left_inv := (freeScalarExtCarrier (S := S) n).left_inv
      right_inv := (freeScalarExtCarrier (S := S) n).right_inv
      map_add' := (freeScalarExtCarrier (S := S) n).map_add
      map_smul' := ?_ }
  intro r x
  -- It suffices to check the generator `single g 1` of `S[G]` (then extend by linearity).
  refine MonoidAlgebra.induction_on
    (p := fun b : S[G] =>
      (freeScalarExtCarrier (S := S) n) (b • x) = b • (freeScalarExtCarrier (S := S) n) x) r ?_ ?_ ?_
  · intro g
    rw [show (MonoidAlgebra.of S G g) = MonoidAlgebra.single g (1 : S) from rfl]
    -- The `single g 1` action on the scalar extension is the scalar-extended representation.
    have hact : ∀ y :
        (Representation.scalarExtension (k := S)
          (Representation.ofModule' (k := A) (G := G) (Fin n → A[G]))).asModule,
        (MonoidAlgebra.single g (1 : S)) • y =
          (Representation.scalarExtension (k := S)
            (Representation.ofModule' (k := A) (G := G) (Fin n → A[G]))) g y := by
      intro y
      rw [Representation.single_smul, one_smul]
      rfl
    induction x using TensorProduct.induction_on with
    | zero =>
        rw [smul_zero, map_zero]
        exact (smul_zero _).symm
    | tmul s y =>
        rw [hact, scalarExtension_apply_eq_baseChange]
        have hρ : (Representation.ofModule' (k := A) (G := G) (Fin n → A[G])
            : Representation A G (Fin n → A[G])) g y
            = MonoidAlgebra.of A G g • y := ofModule'_apply g y
        rw [LinearMap.baseChange_tmul, hρ]
        funext j
        simp only [Pi.smul_apply, freeScalarExtCarrier_tmul_apply]
        exact sTensorGroupAlgebra_of_smul g s (y j)
    | add y z hy hz =>
        rw [smul_add, map_add, map_add, smul_add, hy, hz]
  · intro b c hb hc
    rw [add_smul, map_add, hb, hc, add_smul]
  · intro c b hb
    rw [smul_assoc, map_smul, hb, smul_assoc]

end BaseChangeEquiv

section FreeBijective

variable {S : Type u} [CommRing S] [Algebra A S]

/-! ### Source and target identifications for the free case

We identify both the source `S ⊗[A] ((Fin n → A[G]) →ₗ[A[G]] T)` and the target
`scalarExtIntertwiner A G (Fin n → A[G]) T S` with `Fin n → (S ⊗[A] T)`, in such a way that
`genHomBaseChange (Fin n → A[G]) T` corresponds to the identity.  This proves the latter is
bijective. -/

/-- The source identification:
`S ⊗[A] ((Fin n → A[G]) →ₗ[A[G]] T) ≃ₗ[S] (Fin n → (S ⊗[A] T))`. -/
private noncomputable def freeHomSourceEquiv (n : ℕ) :
    TensorProduct A S ((Fin n → A[G]) →ₗ[A[G]] T) ≃ₗ[S] (Fin n → TensorProduct A S T) := by
  classical
  exact
    ((LinearEquiv.piRing A[G] T (Fin n) A).baseChange A S _ _).trans
      (TensorProduct.piRight A S S (fun _ : Fin n => T))

/-- Value of the source identification on a pure tensor, pointwise. -/
private theorem freeHomSourceEquiv_tmul_apply (n : ℕ) (s : S)
    (f : (Fin n → A[G]) →ₗ[A[G]] T) (j : Fin n) :
    (freeHomSourceEquiv (S := S) (T := T) n) (s ⊗ₜ[A] f) j = s ⊗ₜ[A] (f (Pi.single j 1)) := by
  classical
  simp only [freeHomSourceEquiv, LinearEquiv.trans_apply, LinearEquiv.baseChange_tmul,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, LinearEquiv.piRing_apply]

/-- `sTensorGroupAlgebra` sends `1 ⊗ 1` to `1`. -/
private theorem sTensorGroupAlgebra_one_tmul_one :
    (sTensorGroupAlgebra (A := A) (S := S) (G := G)) ((1 : S) ⊗ₜ[A] (1 : A[G])) = 1 := by
  classical
  ext g
  rw [sTensorGroupAlgebra_tmul_apply]
  show (1 : A[G]) g • (1 : S) = (1 : S[G]) g
  by_cases h : g = 1
  · subst h
    show (MonoidAlgebra.single (1 : G) (1 : A)) 1 • (1 : S) = (MonoidAlgebra.single (1 : G) (1 : S)) 1
    rw [MonoidAlgebra.single_apply, MonoidAlgebra.single_apply, if_pos rfl, if_pos rfl, one_smul]
  · show (MonoidAlgebra.single (1 : G) (1 : A)) g • (1 : S) = (MonoidAlgebra.single (1 : G) (1 : S)) g
    rw [MonoidAlgebra.single_apply, MonoidAlgebra.single_apply, if_neg (Ne.symm h),
      if_neg (Ne.symm h), zero_smul]

/-- The carrier identification sends the pure tensor `1 ⊗ Pi.single j 1` to the standard basis
vector `Pi.single j 1` of `Fin n → S[G]`. -/
private theorem freeScalarExtCarrier_one_tmul_single (n : ℕ) (j : Fin n) :
    (freeScalarExtCarrier (S := S) n) ((1 : S) ⊗ₜ[A] (Pi.single j (1 : A[G]))) =
      Pi.single j (1 : S[G]) := by
  classical
  funext i
  rw [freeScalarExtCarrier_tmul_apply]
  by_cases h : i = j
  · subst h
    rw [Pi.single_eq_same, Pi.single_eq_same, sTensorGroupAlgebra_one_tmul_one]
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
    rw [show ((1 : S) ⊗ₜ[A] (0 : A[G])) = 0 from TensorProduct.tmul_zero _ _, map_zero]

/-- The inverse carrier sends the standard basis vector to `1 ⊗ Pi.single j 1`. -/
private theorem freeScalarExtCarrier_symm_single (n : ℕ) (j : Fin n) :
    (freeScalarExtCarrier (S := S) n).symm (Pi.single j (1 : S[G])) =
      (1 : S) ⊗ₜ[A] (Pi.single j (1 : A[G])) := by
  rw [LinearEquiv.symm_apply_eq, freeScalarExtCarrier_one_tmul_single]

variable [Module.Finite A T] [Module.Free A T]

/-- Step 1 of the target identification: an intertwiner is an `S[G]`-linear map between the
`asModule`s. -/
private noncomputable def freeHomTargetE1 (n : ℕ) :
    scalarExtIntertwiner A G (Fin n → A[G]) T S ≃ₗ[S]
      ((Representation.scalarExtension (k := S)
          (Representation.ofModule' (k := A) (G := G) (Fin n → A[G]))).asModule →ₗ[S[G]]
        (Representation.scalarExtension (k := S)
          (Representation.ofModule' (k := A) (G := G) T)).asModule) :=
  Representation.IntertwiningMap.equivLinearMapAsModule
    (Representation.scalarExtension (k := S)
      (Representation.ofModule' (k := A) (G := G) (Fin n → A[G])))
    (Representation.scalarExtension (k := S)
      (Representation.ofModule' (k := A) (G := G) T))

/-- Step 2: precompose with the free identification `(Fin n → S[G]) ≃ MF`. -/
private noncomputable def freeHomTargetE2 (n : ℕ) :
    ((Representation.scalarExtension (k := S)
        (Representation.ofModule' (k := A) (G := G) (Fin n → A[G]))).asModule →ₗ[S[G]]
      (Representation.scalarExtension (k := S)
        (Representation.ofModule' (k := A) (G := G) T)).asModule) ≃ₗ[S]
      ((Fin n → S[G]) →ₗ[S[G]]
        (Representation.scalarExtension (k := S)
          (Representation.ofModule' (k := A) (G := G) T)).asModule) :=
  LinearEquiv.congrLeft
    ((Representation.scalarExtension (k := S)
        (Representation.ofModule' (k := A) (G := G) T)).asModule) S
    (freeScalarExtAsModuleEquiv (A := A) (S := S) (G := G) n)

/-- Step 3: view an `S[G]`-linear map out of the free module as a tuple of its values. -/
private noncomputable def freeHomTargetE3 (n : ℕ) :
    ((Fin n → S[G]) →ₗ[S[G]]
        (Representation.scalarExtension (k := S)
          (Representation.ofModule' (k := A) (G := G) T)).asModule) ≃ₗ[S]
      (Fin n →
        (Representation.scalarExtension (k := S)
          (Representation.ofModule' (k := A) (G := G) T)).asModule) :=
  LinearEquiv.piRing (MonoidAlgebra S G)
    ((Representation.scalarExtension (k := S)
        (Representation.ofModule' (k := A) (G := G) T)).asModule) (Fin n) S

/-- Step 4: identify each component `MT` with `S ⊗[A] T`. -/
private noncomputable def freeHomTargetE4 (n : ℕ) :
    (Fin n →
        (Representation.scalarExtension (k := S)
          (Representation.ofModule' (k := A) (G := G) T)).asModule) ≃ₗ[S]
      (Fin n → TensorProduct A S T) :=
  LinearEquiv.piCongrRight fun _ : Fin n =>
    (Representation.scalarExtension (k := S)
      (Representation.ofModule' (k := A) (G := G) T)).asModuleEquiv

private noncomputable def freeHomTargetEquiv (n : ℕ) :
    scalarExtIntertwiner A G (Fin n → A[G]) T S ≃ₗ[S] (Fin n → TensorProduct A S T) :=
  (freeHomTargetE1 (S := S) (T := T) n).trans
    ((freeHomTargetE2 (S := S) (T := T) n).trans
      ((freeHomTargetE3 (S := S) (T := T) n).trans (freeHomTargetE4 (S := S) (T := T) n)))

set_option backward.isDefEq.respectTransparency false in
/-- The forward `S[G]`-identification agrees with the `S`-linear carrier on inputs (both have
underlying function `freeScalarExtCarrier`). -/
private theorem freeScalarExtAsModuleEquiv_apply (n : ℕ)
    (x : (Representation.scalarExtension (k := S)
        (Representation.ofModule' (k := A) (G := G) (Fin n → A[G]))).asModule) :
    (freeScalarExtAsModuleEquiv (S := S) n) x = (freeScalarExtCarrier (S := S) n) x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The inverse `S[G]`-identification sends the standard basis vector to `1 ⊗ Pi.single j 1`. -/
private theorem freeScalarExtAsModuleEquiv_symm_single (n : ℕ) (j : Fin n) :
    (freeScalarExtAsModuleEquiv (S := S) n).symm (Pi.single j (1 : S[G])) =
      (1 : S) ⊗ₜ[A] (Pi.single j (1 : A[G])) := by
  rw [LinearEquiv.symm_apply_eq, freeScalarExtAsModuleEquiv_apply,
    freeScalarExtCarrier_one_tmul_single]

set_option backward.isDefEq.respectTransparency false in
/-- The headline computation: under the two identifications, the generic base-change map
`genHomBaseChange (Fin n → A[G]) T` becomes the identity, evaluated on a pure tensor pointwise. -/
private theorem freeHomTargetEquiv_genHomBaseChange_tmul (n : ℕ) (s : S)
    (f : (Fin n → A[G]) →ₗ[A[G]] T) (j : Fin n) :
    (freeHomTargetEquiv (S := S) (T := T) n)
        (genHomBaseChange (Fin n → A[G]) T (s ⊗ₜ[A] f)) j
      = s ⊗ₜ[A] (f (Pi.single j 1)) := by
  classical
  rw [freeHomTargetEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.trans_apply]
  -- Step 4 is pointwise `asModuleEquiv`; step 3 is `piRing`; step 2 is precomposition.
  rw [freeHomTargetE4, LinearEquiv.piCongrRight_apply, freeHomTargetE3, LinearEquiv.piRing_apply,
    freeHomTargetE2, LinearEquiv.congrLeft_apply]
  -- The `arrowCongrAddEquiv` blob is precomposition by `(freeScalarExtAsModuleEquiv n).symm`.
  show ((Representation.scalarExtension (k := S)
      (Representation.ofModule' (k := A) (G := G) T)).asModuleEquiv)
        (((freeHomTargetE1 (S := S) (T := T) n)
            (genHomBaseChange (Fin n → A[G]) T (s ⊗ₜ[A] f)))
          ((freeScalarExtAsModuleEquiv (S := S) n).symm (Pi.single j (1 : S[G])))) = _
  rw [freeScalarExtAsModuleEquiv_symm_single]
  -- Evaluate the base-changed linear map on the pure tensor.
  have hψ : ((freeHomTargetE1 (S := S) (T := T) n)
        (genHomBaseChange (Fin n → A[G]) T (s ⊗ₜ[A] f))).toFun
      = (s • LinearMap.baseChange S (f.restrictScalars A) :
          TensorProduct A S (Fin n → A[G]) →ₗ[S] TensorProduct A S T) := by
    rfl
  show ((Representation.scalarExtension (k := S)
      (Representation.ofModule' (k := A) (G := G) T)).asModuleEquiv)
        (((freeHomTargetE1 (S := S) (T := T) n)
            (genHomBaseChange (Fin n → A[G]) T (s ⊗ₜ[A] f)))
          ((1 : S) ⊗ₜ[A] (Pi.single j (1 : A[G])))) = _
  rw [show (((freeHomTargetE1 (S := S) (T := T) n)
        (genHomBaseChange (Fin n → A[G]) T (s ⊗ₜ[A] f)))
        ((1 : S) ⊗ₜ[A] (Pi.single j (1 : A[G]))))
      = (s • LinearMap.baseChange S (f.restrictScalars A))
        ((1 : S) ⊗ₜ[A] (Pi.single j (1 : A[G]))) from congrFun hψ _]
  simp only [LinearMap.smul_apply, LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply]
  -- `asModuleEquiv` is the identity on `S ⊗[A] T`; finish.
  rw [show ((1 : S) ⊗ₜ[A] (f (Pi.single j 1)) : TensorProduct A S T)
        = ((Representation.scalarExtension (k := S)
            (Representation.ofModule' (k := A) (G := G) T)).asModuleEquiv).symm
          ((1 : S) ⊗ₜ[A] (f (Pi.single j 1))) from rfl]
  rw [map_smul, LinearEquiv.apply_symm_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Under the source and target identifications, `genHomBaseChange (Fin n → A[G]) T` is the
identity: `freeHomTargetEquiv ∘ genHomBaseChange = freeHomSourceEquiv`. -/
private theorem freeHomTargetEquiv_comp_genHomBaseChange (n : ℕ) :
    (freeHomTargetEquiv (S := S) (T := T) n).toLinearMap.comp
        (genHomBaseChange (A := A) (G := G) (S := S) (Fin n → A[G]) T)
      = (freeHomSourceEquiv (S := S) (T := T) n).toLinearMap := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s f
  funext j
  show (freeHomTargetEquiv (S := S) (T := T) n)
      (genHomBaseChange (Fin n → A[G]) T (s ⊗ₜ[A] f)) j
    = (freeHomSourceEquiv (S := S) (T := T) n) (s ⊗ₜ[A] f) j
  rw [freeHomTargetEquiv_genHomBaseChange_tmul, freeHomSourceEquiv_tmul_apply]

/-- **(A)** The free-case base-change map `genHomBaseChange (Fin n → A[G]) T` is bijective. -/
private theorem genHomBaseChange_free_bijective (n : ℕ) :
    Function.Bijective (genHomBaseChange (A := A) (G := G) (S := S) (Fin n → A[G]) T) := by
  have hsrc : ∀ x, (freeHomSourceEquiv (S := S) (T := T) n) x
      = (freeHomTargetEquiv (S := S) (T := T) n)
          (genHomBaseChange (A := A) (G := G) (S := S) (Fin n → A[G]) T x) := by
    intro x
    have := congrFun (congrArg DFunLike.coe
      (freeHomTargetEquiv_comp_genHomBaseChange (S := S) (T := T) n)) x
    simpa using this.symm
  have hcomp :
      (genHomBaseChange (A := A) (G := G) (S := S) (Fin n → A[G]) T)
        = ((freeHomSourceEquiv (S := S) (T := T) n).trans
            (freeHomTargetEquiv (S := S) (T := T) n).symm).toLinearMap := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.coe_coe, LinearEquiv.trans_apply, hsrc x, LinearEquiv.symm_apply_apply]
  rw [hcomp]
  exact LinearEquiv.bijective _

end FreeBijective

section GeneralBijective

variable {S : Type u} [CommRing S] [Algebra A S]

/-- Precomposition on the equivariant Hom by an `A[G]`-linear map `φ : Q₁ →ₗ[A[G]] Q₂`. -/
private def homPrecomp
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁]
    (Q₂ : Type u) [AddCommGroup Q₂] [Module A Q₂] [Module A[G] Q₂] [IsScalarTower A A[G] Q₂]
    (φ : Q₁ →ₗ[A[G]] Q₂) :
    (Q₂ →ₗ[A[G]] T) →ₗ[A] (Q₁ →ₗ[A[G]] T) :=
  LinearMap.lcomp A T φ

@[simp] private theorem homPrecomp_apply
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁]
    (Q₂ : Type u) [AddCommGroup Q₂] [Module A Q₂] [Module A[G] Q₂] [IsScalarTower A A[G] Q₂]
    (φ : Q₁ →ₗ[A[G]] Q₂) (g : Q₂ →ₗ[A[G]] T) :
    homPrecomp Q₁ Q₂ φ g = g ∘ₗ φ :=
  rfl

/-- Precomposition on the scalar-extended intertwiner space by the base change of an `A[G]`-linear
map `φ : Q₁ →ₗ[A[G]] Q₂`. -/
private def intwPrecomp
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁]
    (Q₂ : Type u) [AddCommGroup Q₂] [Module A Q₂] [Module A[G] Q₂] [IsScalarTower A A[G] Q₂]
    (φ : Q₁ →ₗ[A[G]] Q₂) :
    scalarExtIntertwiner A G Q₂ T S →ₗ[S] scalarExtIntertwiner A G Q₁ T S where
  toFun ψ := ψ.comp (genBaseChangeIntertwining (S := S) Q₁ Q₂ φ)
  map_add' ψ ψ' := by
    apply Representation.IntertwiningMap.ext
    simp only [Representation.IntertwiningMap.comp_toLinearMap,
      Representation.IntertwiningMap.add_toLinearMap, LinearMap.add_comp]
  map_smul' c ψ := by
    apply Representation.IntertwiningMap.ext
    show (Representation.IntertwiningMap.comp (c • ψ)
        (genBaseChangeIntertwining (S := S) Q₁ Q₂ φ)).toLinearMap = _
    rw [Representation.IntertwiningMap.comp_toLinearMap,
      Representation.IntertwiningMap.toLinearMap_smul, LinearMap.smul_comp]
    rfl

@[simp] private theorem intwPrecomp_toLinearMap
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁]
    (Q₂ : Type u) [AddCommGroup Q₂] [Module A Q₂] [Module A[G] Q₂] [IsScalarTower A A[G] Q₂]
    (φ : Q₁ →ₗ[A[G]] Q₂) (ψ : scalarExtIntertwiner A G Q₂ T S) :
    (intwPrecomp (S := S) Q₁ Q₂ φ ψ).toLinearMap
      = ψ.toLinearMap ∘ₗ LinearMap.baseChange S (φ.restrictScalars A) := by
  show (ψ.comp (genBaseChangeIntertwining (S := S) Q₁ Q₂ φ)).toLinearMap = _
  rw [Representation.IntertwiningMap.comp_toLinearMap, genBaseChangeIntertwining_toLinearMap]

/-- **Naturality** of the base-change map under precomposition by `φ : Q₁ →ₗ[A[G]] Q₂`:
`genHomBaseChange Q₁ T ∘ (S ⊗ homPrecomp φ) = intwPrecomp φ ∘ genHomBaseChange Q₂ T`. -/
private theorem genHomBaseChange_naturality
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁]
    (Q₂ : Type u) [AddCommGroup Q₂] [Module A Q₂] [Module A[G] Q₂] [IsScalarTower A A[G] Q₂]
    (φ : Q₁ →ₗ[A[G]] Q₂) :
    (genHomBaseChange (S := S) Q₁ T).comp
        (LinearMap.baseChange S (homPrecomp Q₁ Q₂ φ))
      = (intwPrecomp (S := S) Q₁ Q₂ φ).comp (genHomBaseChange (S := S) Q₂ T) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s g
  apply Representation.IntertwiningMap.ext
  -- Compute both underlying linear maps and compare.
  rw [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearMap.comp_apply]
  rw [homPrecomp_apply, genHomBaseChange_tmul, genHomBaseChange_tmul]
  rw [Representation.IntertwiningMap.toLinearMap_smul, genBaseChangeIntertwining_toLinearMap]
  show _ = (intwPrecomp (S := S) Q₁ Q₂ φ (s • genBaseChangeIntertwining Q₂ T g)).toLinearMap
  rw [intwPrecomp_toLinearMap, Representation.IntertwiningMap.toLinearMap_smul,
    genBaseChangeIntertwining_toLinearMap]
  -- `(g ∘ₗ φ).restrictScalars A = (g.restrictScalars A) ∘ₗ (φ.restrictScalars A)`.
  rw [show (g ∘ₗ φ).restrictScalars A
        = (g.restrictScalars A) ∘ₗ (φ.restrictScalars A) from rfl,
    LinearMap.baseChange_comp]
  rw [LinearMap.smul_comp]

/-- `homPrecomp` is contravariantly functorial: precomposing by `φ` then `χ` equals precomposing
by `χ ∘ₗ φ`. -/
private theorem homPrecomp_comp
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁]
    (Q₂ : Type u) [AddCommGroup Q₂] [Module A Q₂] [Module A[G] Q₂] [IsScalarTower A A[G] Q₂]
    (Q₃ : Type u) [AddCommGroup Q₃] [Module A Q₃] [Module A[G] Q₃] [IsScalarTower A A[G] Q₃]
    (χ : Q₂ →ₗ[A[G]] Q₃) (φ : Q₁ →ₗ[A[G]] Q₂) :
    ((homPrecomp Q₁ Q₂ φ : (Q₂ →ₗ[A[G]] T) →ₗ[A] (Q₁ →ₗ[A[G]] T)).comp
        (homPrecomp Q₂ Q₃ χ : (Q₃ →ₗ[A[G]] T) →ₗ[A] (Q₂ →ₗ[A[G]] T)))
      = (homPrecomp Q₁ Q₃ ((χ ∘ₗ φ : Q₁ →ₗ[A[G]] Q₃)) :
          (Q₃ →ₗ[A[G]] T) →ₗ[A] (Q₁ →ₗ[A[G]] T)) := by
  apply LinearMap.ext
  intro g
  rw [LinearMap.comp_apply, homPrecomp_apply, homPrecomp_apply, homPrecomp_apply,
    LinearMap.comp_assoc]

/-- `intwPrecomp` is contravariantly functorial. -/
private theorem intwPrecomp_comp
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁]
    (Q₂ : Type u) [AddCommGroup Q₂] [Module A Q₂] [Module A[G] Q₂] [IsScalarTower A A[G] Q₂]
    (Q₃ : Type u) [AddCommGroup Q₃] [Module A Q₃] [Module A[G] Q₃] [IsScalarTower A A[G] Q₃]
    (χ : Q₂ →ₗ[A[G]] Q₃) (φ : Q₁ →ₗ[A[G]] Q₂) :
    ((intwPrecomp (S := S) Q₁ Q₂ φ).comp
        (intwPrecomp (S := S) (T := T) Q₂ Q₃ χ) :
        scalarExtIntertwiner A G Q₃ T S →ₗ[S] scalarExtIntertwiner A G Q₁ T S)
      = intwPrecomp (S := S) (T := T) Q₁ Q₃ ((χ ∘ₗ φ : Q₁ →ₗ[A[G]] Q₃)) := by
  apply LinearMap.ext
  intro ψ
  apply Representation.IntertwiningMap.ext
  rw [LinearMap.comp_apply]
  rw [intwPrecomp_toLinearMap, intwPrecomp_toLinearMap, intwPrecomp_toLinearMap,
    LinearMap.comp_assoc]
  rw [show (χ ∘ₗ φ).restrictScalars A
        = (χ.restrictScalars A) ∘ₗ (φ.restrictScalars A) from rfl, LinearMap.baseChange_comp]

/-- `homPrecomp` of the identity is the identity. -/
private theorem homPrecomp_id
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁] :
    (homPrecomp Q₁ Q₁ (LinearMap.id : Q₁ →ₗ[A[G]] Q₁) :
        (Q₁ →ₗ[A[G]] T) →ₗ[A] (Q₁ →ₗ[A[G]] T)) = LinearMap.id := by
  apply LinearMap.ext
  intro g
  rw [homPrecomp_apply, LinearMap.comp_id, LinearMap.id_apply]

/-- `intwPrecomp` of the identity is the identity. -/
private theorem intwPrecomp_id
    (Q₁ : Type u) [AddCommGroup Q₁] [Module A Q₁] [Module A[G] Q₁] [IsScalarTower A A[G] Q₁] :
    (intwPrecomp (S := S) (T := T) Q₁ Q₁ (LinearMap.id : Q₁ →ₗ[A[G]] Q₁)) = LinearMap.id := by
  apply LinearMap.ext
  intro ψ
  apply Representation.IntertwiningMap.ext
  rw [intwPrecomp_toLinearMap, LinearMap.id_apply, LinearMap.restrictScalars_id,
    LinearMap.baseChange_id, LinearMap.comp_id]

variable [Module.Projective A[G] Q] [Module.Finite A Q] [Module.Free A Q]
variable [Module.Finite A T] [Module.Free A T]

/-- **(B)** The general base-change map `genHomBaseChange Q T` is bijective, transported from the
free case by the projective splitting `Q` is a retract of `Fin n → A[G]`. -/
private theorem genHomBaseChange_bijective :
    Function.Bijective (genHomBaseChange (A := A) (G := G) (S := S) Q T) := by
  classical
  -- `Q` is module-finite over `A[G]` (since `A[G]` is finite over `A`).
  haveI : Module.Finite A[G] Q :=
    Module.Finite.of_restrictScalars_finite A A[G] Q
  -- A finite free presentation `p : (Fin n → A[G]) ↠ Q` with a section `i`.
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' A[G] Q
  obtain ⟨i, hi⟩ := LinearMap.exists_rightInverse_of_surjective p
    (LinearMap.range_eq_top.2 hp)
  -- Abbreviations.
  set ΨF := genHomBaseChange (A := A) (G := G) (S := S) (Fin n → A[G]) T with hΨF
  set ΨQ := genHomBaseChange (A := A) (G := G) (S := S) Q T with hΨQ
  set α := LinearMap.baseChange S
    (homPrecomp (Fin n → A[G]) Q p :
      (Q →ₗ[A[G]] T) →ₗ[A] ((Fin n → A[G]) →ₗ[A[G]] T)) with hα
  set β := LinearMap.baseChange S
    (homPrecomp Q (Fin n → A[G]) i :
      ((Fin n → A[G]) →ₗ[A[G]] T) →ₗ[A] (Q →ₗ[A[G]] T)) with hβ
  set α' := intwPrecomp (S := S) (T := T) (Fin n → A[G]) Q p with hα'
  set β' := intwPrecomp (S := S) (T := T) Q (Fin n → A[G]) i with hβ'
  have hΨFbij : Function.Bijective ΨF := genHomBaseChange_free_bijective n
  -- Naturality squares.
  have Np : ΨF.comp α = α'.comp ΨQ := genHomBaseChange_naturality (Fin n → A[G]) Q p
  have Ni : ΨQ.comp β = β'.comp ΨF := genHomBaseChange_naturality Q (Fin n → A[G]) i
  -- The split identities.
  have hβα : β.comp α = LinearMap.id := by
    rw [hβ, hα, ← LinearMap.baseChange_comp, homPrecomp_comp, hi, homPrecomp_id,
      LinearMap.baseChange_id]
  have hβ'α' : β'.comp α' = LinearMap.id := by
    rw [hβ', hα', intwPrecomp_comp, hi, intwPrecomp_id]
  refine ⟨?_, ?_⟩
  · -- Injective.
    intro x y hxy
    have hxy0 : ΨQ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h1 : ΨF (α (x - y)) = 0 := by
      have := congrFun (congrArg DFunLike.coe Np) (x - y)
      simp only [LinearMap.comp_apply] at this
      rw [this, hxy0, map_zero]
    have h2 : α (x - y) = 0 := hΨFbij.1 (by rw [h1, map_zero])
    have h3 : β (α (x - y)) = 0 := by rw [h2, map_zero]
    have h4 : (x - y) = 0 := by
      have := congrFun (congrArg DFunLike.coe hβα) (x - y)
      simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
      rw [← this, h3]
    exact sub_eq_zero.1 h4
  · -- Surjective.
    intro y
    refine ⟨β (hΨFbij.2 (α' y)).choose, ?_⟩
    have hF : ΨF (hΨFbij.2 (α' y)).choose = α' y := (hΨFbij.2 (α' y)).choose_spec
    have := congrFun (congrArg DFunLike.coe Ni) (hΨFbij.2 (α' y)).choose
    simp only [LinearMap.comp_apply] at this
    rw [this, hF]
    have := congrFun (congrArg DFunLike.coe hβ'α') y
    simpa only [LinearMap.comp_apply, LinearMap.id_apply] using this

/-- **(3)** The natural base-change map packaged as an `S`-linear equivalence
`S ⊗[A] (Q →ₗ[A[G]] T) ≃ₗ[S] IntertwiningMap (scalarExtension ρQ) (scalarExtension ρT)`. -/
def genHomBaseChangeEquiv :
    TensorProduct A S (Q →ₗ[A[G]] T) ≃ₗ[S] scalarExtIntertwiner A G Q T S :=
  LinearEquiv.ofBijective
    (genHomBaseChange (A := A) (G := G) (S := S) Q T)
    (genHomBaseChange_bijective (A := A) (G := G) (S := S))

end GeneralBijective

section FiberFinrank

variable {S : Type u} [Field S] [Algebra A S]
variable [Module.Projective A[G] Q] [Module.Finite A Q] [Module.Free A Q]
variable [Module.Finite A T] [Module.Free A T]

/-- **(4)** The `S`-dimension of the scalar-extension intertwiner space is independent of the field
`S`: it equals the `A`-rank of the common owner `Q →ₗ[A[G]] T`.  This is Serre's "fiber equality":
applying it for `S = K` and `S = k` shows the two fibers have the same dimension. -/
theorem finrank_scalarExtIntertwiner_eq_finrank_hom :
    Module.finrank S (scalarExtIntertwiner A G Q T S)
      = Module.finrank A (Q →ₗ[A[G]] T) := by
  classical
  rw [← LinearEquiv.finrank_eq (genHomBaseChangeEquiv (A := A) (G := G) (S := S))]
  let b := Module.Free.chooseBasis A (Q →ₗ[A[G]] T)
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis S b),
    Module.finrank_eq_card_basis b]

end FiberFinrank

section FiberFinrankComparison

variable {S₁ S₂ : Type u} [Field S₁] [Algebra A S₁] [Field S₂] [Algebra A S₂]
variable [Module.Projective A[G] Q] [Module.Finite A Q] [Module.Free A Q]
variable [Module.Finite A T] [Module.Free A T]

/-- The scalar-extended intertwiner space has the same dimension over any two field fibers of the
PID base. -/
theorem scalarExtIntertwiner_finrank_eq :
    Module.finrank S₁ (scalarExtIntertwiner A G Q T S₁) =
      Module.finrank S₂ (scalarExtIntertwiner A G Q T S₂) := by
  -- Both field fibers compute the rank of the common `A`-linear Hom owner.
  rw [finrank_scalarExtIntertwiner_eq_finrank_hom,
    finrank_scalarExtIntertwiner_eq_finrank_hom]

end FiberFinrankComparison

end Representation
