import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.TensorProduct.Maps
import StacksProject_2024.Chap10.Lemma_10_76_1
import StacksProject_2024.Chap15.Definition_15_61_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ModuleCat
open scoped TensorProduct

noncomputable section

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R R' A B A' B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
variable [Module.Flat R R']

local notation "ATensor" => TensorProduct R A R'
local notation "BTensor" => TensorProduct R R' B
local notation "extScalars" => ModuleCat.extendScalars (algebraMap R R')

private noncomputable def restrictScalarsSelfEquiv
    (T : Type u) [CommRing T] [Algebra R T] :
    ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) ≃ₗ[T] T :=
  { __ := AddEquiv.refl T
    map_smul' := fun _ _ ↦ rfl }

private instance restrictScalarsSelfIsScalarTower
    (T : Type u) [CommRing T] [Algebra R T] :
    IsScalarTower R T
      ↑((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T T)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

/- 
Domain-style sampling for Lemma 15.61.3:
- primary domain: flat base change for the owner bifunctor `Tor` in module
  categories over commutative rings;
- sampled owner declarations of the same kind:
  `Tor`,
  `torBaseChangeHom`,
  `flat_tor_base_change_map_isIso`,
  `ModuleCat.extendScalars`;
- best owner abstraction: the Chapter 10 owner map `torBaseChangeHom` for `R → R'`;
- primitive data: the ring map `R → R'`, the two `R`-algebras `A`, `B`, and the two explicit
  `R'`-algebra comparison maps `A ⊗[R] R' → A'` and `R' ⊗[R] B → B'`;
- derived API: the source-facing comparison to `Tor_i^{R'}(A', B')`, obtained by composing the
  owner base-change map with functoriality in the two module variables.

Source/core/bridge triage:
- `source-facing`: the comparison morphism
  `torBaseChangeComparison : Tor_i^R(A, B) ⊗[R] R' ⟶ Tor_i^{R'}(A', B')`;
- `core/canonical`: `torBaseChangeHom` for the flat ring map `R → R'`;
- `bridge/view`: the explicit comparison maps `A ⊗[R] R' → A'` and `R' ⊗[R] B → B'`; the
  left-variable map is converted to the owner `extendScalars` order by
  `Algebra.TensorProduct.commRight`, and then both maps induce the target-side `Tor` morphism in
  `ModuleCat R'`.
-/

section

/-- The source-facing comparison of Lemma 15.61.3: start with the Chapter 10 owner
`torBaseChangeHom` for `R → R'`, then apply functoriality in the two variables to reach
`Tor_i^{R'}(A', B')`. -/
def torBaseChangeComparison
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (bMap : R' ⊗[R] B →ₐ[R'] B')
    (i : ℕ) :
    (extScalars).obj (Tor[R, i](A, B)) ⟶ Tor[R', i](A', B') :=
  letI : Algebra ATensor A' := aMap.toAlgebra
  letI : Algebra BTensor B' := bMap.toAlgebra
  let F := Tor (ModuleCat R') i
  let aTensorEquiv :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R A) ≃ₗ[R']
        R' ⊗[R] A :=
    TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv R')
      (LinearEquiv.refl R A)
  let aLinear :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R A) →ₗ[R']
        A' :=
    ((aMap.comp (Algebra.TensorProduct.commRight R R' A).toAlgHom).toLinearMap).comp
      aTensorEquiv.toLinearMap
  let aHom : (extScalars).obj (of R A) ⟶ of R' A' :=
    ofHom aLinear
  let bTensorEquiv :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R B) ≃ₗ[R']
        R' ⊗[R] B :=
    TensorProduct.AlgebraTensorModule.congr
      (restrictScalarsSelfEquiv R')
      (LinearEquiv.refl R B)
  let bLinear :
      TensorProduct R ((ModuleCat.restrictScalars (algebraMap R R')).obj (of R' R')) (of R B) →ₗ[R']
        B' :=
    bMap.toLinearMap.comp bTensorEquiv.toLinearMap
  let bHom : (extScalars).obj (of R B) ⟶ of R' B' :=
    ofHom bLinear
  torBaseChangeHom (algebraMap R R') (RingHom.flat_algebraMap_iff.mpr inferInstance)
      (of R A) (of R B) i ≫
    (F.map aHom).app ((extScalars).obj (of R B)) ≫
    (F.obj (of R' A')).map bHom

-- Proof sketch: the first arrow is the owner flat base-change isomorphism from Chapter 10. The
-- second arrow is induced by `aMap` after converting `extendScalars` from `R' ⊗[R] A` to the
-- source-facing order `A ⊗[R] R'` via `Algebra.TensorProduct.commRight`, and the third arrow is
-- induced by `bMap`. In positive degree, the extra flatness hypotheses on `A'` and `B'` are used
-- to prove that this composite is an isomorphism.
/-- Lemma 15.61.3: for a commutative square of rings
`A ← R → B`, `A' ← R' → B'` with `R'` flat over `R`, `A'` flat over `A ⊗[R] R'`, and `B'`
flat over `R' ⊗[R] B`, together with the corresponding `R'`-algebra comparison maps
`A ⊗[R] R' → A'` and `R' ⊗[R] B → B'`, the canonical comparison from the base change of
`Tor_i^R(A, B)` to `Tor_i^{R'}(A', B')` is an isomorphism for every positive degree `i`. -/
theorem torBaseChangeComparison_isIso
    (aMap : A ⊗[R] R' →ₐ[R'] A')
    (bMap : R' ⊗[R] B →ₐ[R'] B')
    (i : ℕ) (hi : 0 < i)
    (haFlat :
      letI : Algebra (A ⊗[R] R') A' := aMap.toAlgebra
      Module.Flat (A ⊗[R] R') A')
    (hbFlat :
      letI : Algebra (R' ⊗[R] B) B' := bMap.toAlgebra
      Module.Flat (R' ⊗[R] B) B') :
    IsIso (torBaseChangeComparison aMap bMap i) := by
  letI : Algebra ATensor A' := aMap.toAlgebra
  letI : Algebra BTensor B' := bMap.toAlgebra
  letI : Module.Flat ATensor A' := haFlat
  letI : Module.Flat BTensor B' := hbFlat
  sorry

end

end
