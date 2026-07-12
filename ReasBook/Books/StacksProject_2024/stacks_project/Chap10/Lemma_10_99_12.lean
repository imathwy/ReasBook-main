import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

noncomputable section

section

variable {R R' R'' S : Type u}
variable [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
variable [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R'']
variable [Algebra R S]
variable {M : Type u} [AddCommGroup M] [Module R M]

/-
Domain triage:
- primary domain: homological commutative algebra for the owner bifunctor
  `Tor (ModuleCat R) 1` and its functoriality in the right variable;
- sampled owner declarations of the same kind:
  `CategoryTheory.Tor`,
  `ModuleCat.extendRestrictScalarsAdj`,
  `torBaseChangeHom`,
  `TensorProduct.comm`;
- best owner abstraction: `CategoryTheory.Tor (ModuleCat R) 1`;
- primitive data: the ring maps `R → R' → R''`, the `R`-module `M`, and multiplication
  endomorphisms of the right-variable module;
- derived API: the induced `S`-module structure on `Tor₁^R(M, S)`, the canonical
  `ModuleCat.extendScalars` comparison morphism, and its textbook tensor-product view.

Layering:
- `source-facing`: the surjectivity statement for the textbook tensor-product comparison;
- `core/canonical`: the owner bifunctor `Tor (ModuleCat R) 1`;
- `bridge/view`: the scalar action on `Tor₁^R(M, S)` obtained by transporting multiplication on
  `S` through `Tor`, and the tensor-symmetry identification of `extendScalars`.
-/

set_option quotPrecheck false in
local notation "Tor₁[" R "](" M ", " S ")" =>
  (((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).obj (ModuleCat.of R S))

private noncomputable def torOneActionEnd :
    S →+* Module.End R (Tor₁[R](M, S)) := by
  let F := ((Tor (ModuleCat R) 1).obj (ModuleCat.of R M))
  let eS : End (ModuleCat.of R S) ≃+* Module.End R (ModuleCat.of R S) :=
    (ModuleCat.of R S).endRingEquiv
  let eT : End (Tor₁[R](M, S)) ≃+* Module.End R (Tor₁[R](M, S)) :=
    (Tor₁[R](M, S)).endRingEquiv
  refine
    { toFun := fun s ↦ eT <| F.map (eS.symm (Module.toModuleEnd R S s))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry }

private noncomputable instance torOneModule :
    Module S (Tor₁[R](M, S)) := by
  let _ : Module (Module.End R (Tor₁[R](M, S))) (Tor₁[R](M, S)) := inferInstance
  let f : S →+* Module.End R (Tor₁[R](M, S)) := torOneActionEnd
  simpa using (Module.compHom (Tor₁[R](M, S)) f : Module S (Tor₁[R](M, S)))

local notation "Tor₁Obj[" R "](" M ", " S ")" =>
  (ModuleCat.of S (Tor₁[R](M, S)))
local notation "extScalars" => ModuleCat.extendScalars (algebraMap R' R'')
local notation "resScalars" => ModuleCat.restrictScalars (algebraMap R' R'')
local notation "baseChangeAdj" => ModuleCat.extendRestrictScalarsAdj (algebraMap R' R'')

variable [Module.Flat R' (TensorProduct R R' M)]

private noncomputable instance torOneBaseChangeTargetModule :
    Module R' (Tor₁[R](M, R'')) :=
  Module.compHom (Tor₁[R](M, R'')) (algebraMap R' R'')

private noncomputable instance torOneBaseChangeSourceModule :
    Module R' ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  Module.compHom _ (algebraMap R' R'')

/-- The canonical owner-level base-change comparison obtained by applying the `Tor` bifunctor in
the right variable and adjoint-transposing along extension/restriction of scalars. -/
noncomputable def torOneBaseChangeComparison :
    (extScalars).obj (Tor₁Obj[R](M, R')) ⟶ Tor₁Obj[R](M, R'') :=
  ((baseChangeAdj).homEquiv _ _).symm <|
    ModuleCat.ofHom
      { toFun :=
          ((((Tor (ModuleCat R) 1).obj (ModuleCat.of R M)).map
            (ModuleCat.ofHom ((IsScalarTower.toAlgHom R R' R'').toLinearMap))).hom)
        map_add' := sorry
        map_smul' := sorry }

private noncomputable def torOneTextbookTensorSource :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R']
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) :=
  let eR'' : R'' ≃ₗ[R'] ↑((resScalars).obj (ModuleCat.of R'' R'')) :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun r x ↦ by
        have h_source : r • x = (algebraMap R' R'') r * x := Algebra.smul_def r x
        have h_target :
            r • (show ↑((resScalars).obj (ModuleCat.of R'' R'')) from x) =
              (algebraMap R' R'') r * x := by
          simpa [Algebra.smul_def] using
            (@ModuleCat.restrictScalars.smul_def' _ _ _ _ (algebraMap R' R'')
              (ModuleCat.of R'' R'') r x)
        exact h_source.trans h_target.symm }
  let e :
      TensorProduct R' (Tor₁[R](M, R')) R'' ≃ₗ[R']
        TensorProduct R' (Tor₁[R](M, R')) ↑((resScalars).obj (ModuleCat.of R'' R'')) :=
    TensorProduct.congr (LinearEquiv.refl R' _) eR''
  let c :
      TensorProduct R' (Tor₁[R](M, R')) ↑((resScalars).obj (ModuleCat.of R'' R'')) ≃ₗ[R']
        ↑((extScalars).obj (Tor₁Obj[R](M, R'))) := by
      simpa [ModuleCat.extendScalars, ModuleCat.ExtendScalars.obj'] using
        (TensorProduct.comm R' (Tor₁[R](M, R')) ((resScalars).obj (ModuleCat.of R'' R'')))
  (e.trans c).toLinearMap

/- The source-facing tensor-product map is the bridge/view obtained from the owner comparison by
identifying `ModuleCat.extendScalars` with the textbook tensor source via
`TensorProduct.comm`. -/
noncomputable def torOneBaseChangeMap :
    TensorProduct R' (Tor₁[R](M, R')) R'' →ₗ[R'] Tor₁[R](M, R'') :=
  let comparisonLinear :
      ↑((extScalars).obj (Tor₁Obj[R](M, R'))) →ₗ[R'] Tor₁[R](M, R'') :=
    { toFun := torOneBaseChangeComparison.hom
      map_add' := torOneBaseChangeComparison.hom.map_add
      map_smul' := fun c x ↦ by
        change torOneBaseChangeComparison.hom ((algebraMap R' R'' c) • x) =
          (algebraMap R' R'' c) • torOneBaseChangeComparison.hom x
        simpa using torOneBaseChangeComparison.hom.map_smul (algebraMap R' R'' c) x }
  comparisonLinear.comp torOneTextbookTensorSource

-- Proof sketch: choose a free resolution of `M` over `R`. After tensoring with `R'`, the
-- resulting exact sequence stays exact after tensoring with `R''` because `M ⊗[R] R'` is flat
-- over `R'`. The induced surjection on the kernels descends to a surjection on the corresponding
-- `Tor₁` quotients, yielding the natural textbook map
-- `Tor₁^R(M, R') ⊗[R'] R'' → Tor₁^R(M, R'')`.
/-- Lemma 10.99.12, textbook tensor-product form: if `M ⊗[R] R'` is flat over `R'`, then the
natural base-change map `Tor₁^R(M, R') ⊗[R'] R'' → Tor₁^R(M, R'')` is surjective. -/
theorem torOne_baseChangeMap_surjective_of_flat_baseChange :
    Function.Surjective
      (torOneBaseChangeMap : TensorProduct R' (Tor₁[R](M, R')) R'' → Tor₁[R](M, R'')) := sorry

end
