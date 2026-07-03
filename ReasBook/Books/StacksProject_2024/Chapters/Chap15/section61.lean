import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_61_1 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits

universe u

section

variable (R : Type u) [CommRing R]
variable (A B : Type u) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

set_option quotPrecheck false in
notation "Tor[" R ", " p "](" M ", " N ")" =>
  (((Tor (ModuleCat R) p).obj (ModuleCat.of R M)).obj (ModuleCat.of R N))

/-- Definition 15.61.1: two `R`-algebras are Tor independent over `R` if all positive Tor groups
`Tor_p^R(A, B)` vanish. -/
def IsTorIndependent : Prop :=
  ∀ p : ℕ, 0 < p → IsZero (Tor[R, p](A, B))

-- Proof sketch: unfold `IsTorIndependent`; the result is exactly the defining vanishing condition
-- specialized to the chosen positive degree `p`.
/-- Tor independence gives the vanishing of each positive Tor group. -/
theorem IsTorIndependent.isZero_tor (h : IsTorIndependent R A B) {p : ℕ} (hp : 0 < p) :
    IsZero (Tor[R, p](A, B)) :=
  h p hp

end

/-! ### Lemma_15_61_2 (from Chap15) -/
noncomputable section

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {A R Aprime : Type u} [CommRing A] [CommRing R] [CommRing Aprime]
variable [Algebra A R] [Algebra A Aprime]

local notation "Rprime" => (Aprime ⊗[A] R)
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAprime" => DerivedCategory (ModuleCat Aprime)
local notation "DModRprime" => DerivedCategory (ModuleCat Rprime)

/- Domain-style sampling for Lemma 15.61.2:
- primary domain: derived tensor base change for commutative algebras;
- sampled owner declarations:
  `derivedTensorBaseChange`,
  `derivedTensorBaseChangeIso`,
  `Functor.leftDerivedNatIso`;
- best owner abstraction: the canonical public owner is the isomorphism
  `derivedTensorBaseChangeIso`, whose hom is the source-facing comparison morphism
  `derivedTensorBaseChange`;
- primitive vs. derived:
  primitive data are the rings `A`, `R`, `A'`, their algebra structures, and
  `K : D(R)`;
  the comparison morphism and its `IsIso` consequence are derived API from the owner isomorphism;
- source/core/bridge triage:
  `source-facing`: the comparison between the two derived base-change constructions at `K`;
  `core/canonical`: `derivedTensorBaseChangeIso`;
  `bridge/view`: the underlying morphism `derivedTensorBaseChange A Aprime K`.

The Tor-independence hypothesis from the source statement is redundant here: the owner comparison
is already the hom of a canonical isomorphism. -/

/- Lemma 15.61.2: the derived base-change comparison is the canonical isomorphism
`derivedTensorBaseChangeIso`. -/
recall derivedTensorBaseChangeIso

end

end CategoryTheory

/-! ### Lemma_15_61_3 (from Chap15) -/
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

/-! ### Lemma_15_61_4 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] [Algebra R R']

-- Proof sketch: apply the Chapter 15 comparison morphism
-- `torBaseChangeComparison : Tor_i^R(A, B) ⊗[R] R' → Tor_i^{R'}(A ⊗[R] R', B ⊗[R] R')`,
-- specialized to the identity on `A ⊗[R] R'` and the canonical commutation map
-- `R' ⊗[R] B ≅ B ⊗[R] R'`, then use Definition 15.61.1 to reduce to the vanishing of the
-- original positive Tor groups.
/-- Lemma 15.61.4: if `A` and `B` are Tor independent over `R` and `R → R'` is flat, then
`A ⊗[R] R'` and `B ⊗[R] R'` are Tor independent over `R'`. -/
theorem IsTorIndependent.baseChange
    (h : IsTorIndependent R A B) [Module.Flat R R'] :
    IsTorIndependent R' (A ⊗[R] R') (B ⊗[R] R') := by
  intro p hp
  let aMap : A ⊗[R] R' →ₐ[R'] A ⊗[R] R' := AlgHom.id R' (A ⊗[R] R')
  let bMap : R' ⊗[R] B →ₐ[R'] B ⊗[R] R' := (Algebra.TensorProduct.commRight R R' B).toAlgHom
  have haFlat :
      letI : Algebra (A ⊗[R] R') (A ⊗[R] R') := aMap.toAlgebra
      Module.Flat (A ⊗[R] R') (A ⊗[R] R') := by
    exact Module.Flat.of_free
  have hbFlat :
      letI : Algebra (R' ⊗[R] B) (B ⊗[R] R') := bMap.toAlgebra
      Module.Flat (R' ⊗[R] B) (B ⊗[R] R') := by
    let e : R' ⊗[R] B ≃ₐ[R'] B ⊗[R] R' := Algebra.TensorProduct.commRight R R' B
    letI : Algebra (R' ⊗[R] B) (B ⊗[R] R') := bMap.toAlgebra
    let eLinear : B ⊗[R] R' ≃ₗ[R' ⊗[R] B] R' ⊗[R] B :=
      { __ := e.symm.toEquiv
        map_add' := e.symm.map_add
        map_smul' := by
          intro s x
          change e.symm (e s * x) = s * e.symm x
          simp }
    letI : Module.Flat (R' ⊗[R] B) (R' ⊗[R] B) := Module.Flat.of_free
    exact Module.Flat.of_linearEquiv eLinear
  let f := torBaseChangeComparison aMap bMap p
  letI : IsIso f := torBaseChangeComparison_isIso aMap bMap p hp haFlat hbFlat
  exact IsZero.of_iso
    ((ModuleCat.extendScalars (algebraMap R R')).map_isZero
      (h p hp))
    (asIso f).symm

end

/-! ### Lemma_15_61_5 (from Chap15) -/
noncomputable section

open CategoryTheory Algebra.TensorProduct
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R R' A B A' B' : Type u}
variable [CommRing R] [CommRing R'] [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
variable [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']
variable [Algebra R A'] [Algebra A A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
variable [Algebra R B'] [IsScalarTower R R' B']
variable [Module.Flat R R']

local notation "S" => TensorProduct R A B
local notation "T" => TensorProduct R' A' B'
local notation "ATensor" => TensorProduct R A R'
local notation "BTensor" => TensorProduct R R' B
local notation "DModA" => DerivedCategory (ModuleCat A)

private abbrev baseChangeProductMap
    (bMap : BTensor →ₐ[R'] B') : S →ₐ[R] T :=
  (productMap
      (((includeLeft : A' →ₐ[R'] T).restrictScalars R).comp (IsScalarTower.toAlgHom R A A'))
      (((includeRight : B' →ₐ[R'] T).restrictScalars R).comp
        ((bMap.restrictScalars R).comp (includeRight : B →ₐ[R] BTensor))))

private abbrev baseChangeLeftMap : ATensor →ₐ[R] A' :=
  productMap
    (IsScalarTower.toAlgHom R A A')
    (IsScalarTower.toAlgHom R R' A')

/- Domain-style sampling for Lemma 15.61.5:
- primary domain: derived base-change comparison in module-category derived categories and the
  induced maps on homology;
- sampled owner declarations of the same kind:
  `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraHomologyComparison`,
  `derivedTensorWithAlgebraAdjunction`,
  `DerivedCategory.homologyFunctor`,
  `ModuleCat.extendScalars`,
- best owner abstraction: the source-facing owner is the canonical homology base-change map for
  the canonical `Algebra S T` coming from `productMap : A ⊗[R] B →ₐ[R] A' ⊗[R'] B'`, built from
  `derivedTensorWithAlgebraHomologyComparison`, with `productMap` supplying the textbook ring
  map and no parallel local tensor-map or local homology-comparison owner;
- primitive data: the comparison map `bMap : R' ⊗[R] B →ₐ[R'] B'`, the induced canonical ring
  map `baseChangeProductMap bMap : A ⊗[R] B →ₐ[R] A' ⊗[R'] B'`, together with `M : D(A)` and
  the degree `i : ℤ`;
- derived API: the source-facing flat-base-change statement on homology, expressed by saying that
  this canonical comparison morphism is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the textbook flat-base-change isomorphism on homology modules over
  `A' ⊗[R'] B'`;
- `core/canonical`: `derivedTensorWithAlgebra`,
  `derivedTensorWithAlgebraHomologyComparison`, and `DerivedCategory.homologyFunctor`;
- `bridge/view`: the explicit tensor-product presentation via the canonical
  `Algebra.TensorProduct.productMap`; no parallel local owner theorem or local public tensor-map
  wrapper is kept. -/

-- Proof sketch: apply the flat-base-change argument of Lemma `15.61.3` to the canonical
-- ring map `A ⊗[R] B → A' ⊗[R'] B'` encoded by `baseChangeProductMap bMap`, then pass from the
-- derived-category
-- comparison to the canonical owner morphism `derivedTensorWithAlgebraHomologyComparison` for the
-- induced `S`-algebra structure on `T`.
/-- Lemma 15.61.5: under the flat base-change hypotheses of Lemma `15.61.3`, the canonical
homology comparison
`derivedTensorWithAlgebraHomologyComparison T (M ⊗[A]^L[S]) i`
for the explicit `baseChangeProductMap bMap`-induced `S`-algebra structure on
`T = A' ⊗[R'] B'` is an isomorphism. This is the owner-level formulation of the textbook
statement about `(M \otimes_A^{\mathbf L} A') \otimes_{R'}^{\mathbf L} B'`. -/
theorem derivedTensorWithAlgebraHomologyComparison_isIso_of_flat_baseChange
    (bMap : BTensor →ₐ[R'] B')
    (haFlat :
      letI : Algebra ATensor A' := baseChangeLeftMap.toAlgebra
      Module.Flat ATensor A')
    (hbFlat :
      letI : Algebra BTensor B' := bMap.toAlgebra
      Module.Flat BTensor B')
    (M : DModA) (i : ℤ) :
    letI : Algebra S T := (baseChangeProductMap bMap).toAlgebra
    IsIso (derivedTensorWithAlgebraHomologyComparison T (M ⊗[A]^L[S]) i) := sorry

end

end CategoryTheory

/-! ### Lemma_15_61_6 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

noncomputable section

universe u

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B]

/- Domain triage:
* primary domain: Tor-vanishing for commutative algebras and its behavior under localization;
* sampled owner declarations in the chapter/project:
  `IsTorIndependent`,
  `CategoryTheory.Tor`,
  `torBaseChangeComparison`,
  `IsTorIndependent.baseChange`;
* best owner abstraction: the canonical `Tor` object in `ModuleCat`, with `IsTorIndependent` as
  the source-facing vanishing predicate;
* primitive data: the rings `R`, `A`, `B` and the canonical `Tor` objects;
* derived API: the canonical `(A ⊗[R] B)`-module structure on `Tor_i^R(A, B)` and its
  localizations at prime ideals of `A ⊗[R] B`.

Source/core/bridge triage:
* `source-facing`: the TFAE statement comparing Tor independence with its localizations;
* `core/canonical`: `IsTorIndependent` and the owner bifunctor `Tor`;
* `bridge/view`: the canonical `(A ⊗[R] B)`-linear realization of the underlying `Tor` carrier,
  needed only to form `LocalizedModule.AtPrime`.
-/
set_option quotPrecheck false in
local notation "TorMod[" S ", " i "](" M ", " N ")" =>
  ↑(Tor[S, i](M, N))

private noncomputable def torLeftAction (i : ℕ) :
    A →ₐ[R] Module.End R (TorMod[R, i](A, B)) := by
  let F := Tor (ModuleCat R) i
  let eA : End (ModuleCat.of R A) ≃+* Module.End R A := (ModuleCat.of R A).endRingEquiv
  let eT : End (Tor[R, i](A, B)) ≃+* Module.End R (TorMod[R, i](A, B)) :=
    (Tor[R, i](A, B)).endRingEquiv
  refine
    { toFun := fun a ↦ eT <| ((F.map (eA.symm (Module.toModuleEnd R A a))).app (ModuleCat.of R B))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }

private noncomputable def torRightAction (i : ℕ) :
    B →ₐ[R] Module.End R (TorMod[R, i](A, B)) := by
  let F := ((Tor (ModuleCat R) i).obj (ModuleCat.of R A))
  let eB : End (ModuleCat.of R B) ≃+* Module.End R B := (ModuleCat.of R B).endRingEquiv
  let eT : End (Tor[R, i](A, B)) ≃+* Module.End R (TorMod[R, i](A, B)) :=
    (Tor[R, i](A, B)).endRingEquiv
  refine
    { toFun := fun b ↦ eT <| F.map (eB.symm (Module.toModuleEnd R B b))
      map_one' := sorry
      map_mul' := sorry
      map_zero' := sorry
      map_add' := sorry
      commutes' := sorry }

private noncomputable def torTensorAction (i : ℕ) :
    A ⊗[R] B →ₐ[R] Module.End R (TorMod[R, i](A, B)) :=
  Algebra.TensorProduct.lift (torLeftAction i) (torRightAction i) <| by
    intro a b
    sorry

private noncomputable instance torTensorProductModule (i : ℕ) :
    Module (A ⊗[R] B) (TorMod[R, i](A, B)) := by
  let _ : Module (Module.End R (TorMod[R, i](A, B))) (TorMod[R, i](A, B)) := inferInstance
  simpa using (Module.compHom (TorMod[R, i](A, B)) (torTensorAction i).toRingHom :
    Module (A ⊗[R] B) (TorMod[R, i](A, B)))

-- Proof sketch: use Lemma `15.61.3` to identify Tor after localizing at primes and after passing to
-- the local tensor product, so the local Tor-independence condition and the localized vanishing
-- condition are both equivalent to the vanishing of the global positive Tor groups. Then apply the
-- standard criterion that a module is zero iff all of its localizations at prime ideals vanish.
/-- Lemma 15.61.6: for commutative `R`-algebras `A` and `B`, the following are equivalent: `A`
and `B` are Tor independent over `R`; for every prime `𝔯` of `R` and primes `𝔭` of `A`, `𝔮` of
`B` lying over `𝔯`, the local rings `A_𝔭` and `B_𝔮` are Tor independent over `R_𝔯`; and for every
prime `𝔰` of `A ⊗[R] B`, the canonical `(A ⊗[R] B)`-linear positive Tor groups `Tor_i^R(A, B)`
become zero after localizing at `𝔰`. -/
theorem isTorIndependent_tfae_localizationAtPrimes_and_localizedTor :
    List.TFAE
      [ IsTorIndependent R A B
      , ∀ r : PrimeSpectrum R,
          ∀ p : r.asIdeal.primesOver A,
            ∀ q : r.asIdeal.primesOver B,
              IsTorIndependent (Localization.AtPrime r.asIdeal)
                (Localization.AtPrime p.1) (Localization.AtPrime q.1)
      , ∀ s : PrimeSpectrum (A ⊗[R] B),
          ∀ i : ℕ, 0 < i →
            IsZero
              (ModuleCat.of (Localization.AtPrime s.asIdeal)
                (LocalizedModule.AtPrime s.asIdeal (TorMod[R, i](A, B))))
      ] := sorry

end
