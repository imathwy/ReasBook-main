import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_7_2 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoricalPullback.CatCommSqOver

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "baseChangeFunctor" => S.relativeModuleFunctor

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes

/- Domain-style sampling for Lemma 15.7.2:
- primary domain: adjunctions between module-category base change and fibre-product module
  constructions over a commutative tensor square of rings;
- sampled owner declarations:
  `moduleCatBaseChangeSquare`,
  `moduleCatBaseChangeToCategoricalPullback`,
  `FiberProductBaseChangeSituation.relativeModuleFunctor`,
  `module_tensor_pullback_adjunction`,
  `module_tensor_pullback_adjunction_counit_isIso`;
- best owner abstraction: the specialized adjunction
  `module_tensor_pullback_adjunction S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes`;
- primitive data: the fibre-product base-change situation `S`;
- derived API: the specialized base-change functor `S.relativeModuleFunctor`, the specialized
  fibre-product functor `fiberProductFunctor`, their adjunction, and the canonical counit
  isomorphism on the composite back to the relative pullback category.

Source/core/bridge triage:
- `source-facing`: Lemma 15.7.2, asserting that the canonical base-change functor
  `Mod_{D'} → Mod_D ×_[Mod_C] Mod_{C'}` is left adjoint to the canonical fibre-product module
  functor;
- `core/canonical`: `module_tensor_pullback_adjunction`;
- `bridge/view`: the specialization of that owner adjunction to the tensor square attached to `S`.
-/

/- Lemma 15.7.2: in Situation 15.7.1, the canonical base-change functor
`Mod_{D'} → Mod_D ×_[Mod_C] Mod_{C'}`
is left adjoint to the canonical fibre-product module functor
`(N, M', φ) ↦ N ×_φ M'`. This is exactly the specialized owner adjunction from
`module_tensor_pullback_adjunction`. -/
set_option linter.hashCommand false in
#check (module_tensor_pullback_adjunction S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes :
  baseChangeFunctor ⊣ fiberProductFunctor)

/- Lemma 15.7.2: the composite from `Mod_D ×_[Mod_C] Mod_{C'}` back to itself through the
fibre-product module functor and base change is canonically isomorphic to the identity functor.
This is the specialized owner-level counit isomorphism. -/
set_option linter.hashCommand false in
#check (module_tensor_pullback_adjunction_counit_isIso
  S.dprimeToD
  S.dprimeToCPrime
  S.tensor_square_commutes :
    IsIso
      ((module_tensor_pullback_adjunction S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes)
        .counit :
          fiberProductFunctor ⋙ baseChangeFunctor ⟶ 𝟭 S.relativeModuleCategory))

end FiberProductBaseChangeSituation

end

/-! ### Lemma_15_7_3 (from Chap15) -/
open CategoryTheory Limits

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

-- Proof sketch: an element of `ker(A' → A)` determines the pullback pair `(0, a')`, so the image
-- of `ker(B' → B)` in `A'` is exactly `ker(A' → A)`.
/-- In Situation `15.7.1`, the kernel of `B' → B` maps onto the kernel of `A' → A`. -/
theorem kernelIdealToB_image_eq_kernelIdealInAprime
    (S : Situation) :
    Ideal.map S.bprimeToAprime (RingHom.ker S.bprimeToB) = RingHom.ker S.fromAprime := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    refine RingHom.mem_ker.mpr ?_
    rw [← show S.toA (S.bprimeToB x) = S.fromAprime (S.bprimeToAprime x) from
      congrArg (fun k ↦ k x) S.comm]
    simpa using congrArg S.toA (RingHom.mem_ker.mp hx)
  · intro x hx
    let f : CommRingCat.of B ⟶ CommRingCat.of A := CommRingCat.ofHom S.toA
    let g : CommRingCat.of A' ⟶ CommRingCat.of A := CommRingCat.ofHom S.fromAprime
    let y : ↑(pullback f g) :=
      Concrete.pullbackMk f g (0 : B) x
        (by simpa [f, g] using (RingHom.mem_ker.mp hx).symm)
    have hy : y ∈ RingHom.ker S.bprimeToB := by
      refine RingHom.mem_ker.mpr ?_
      change pullback.fst f g y = 0
      simp [y, f, g]
    rw [← show S.bprimeToAprime y = x by
      change pullback.snd f g y = x
      simp [y, f, g]]
    exact Ideal.mem_map_of_mem S.bprimeToAprime hy

theorem dprimeToCPrime_comp_bprimeToDp
    (S : Situation) :
    S.dprimeToCPrime.comp S.bprimeToDp = S.aprimeToCPrime.comp S.bprimeToAprime := by
  ext x
  change
    (((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.CPrime).toRingHom.comp
      (algebraMap S.Bprime Dp)) x) =
      (((Algebra.TensorProduct.includeRight : A' →ₐ[S.Bprime] S.CPrime).toRingHom.comp
        (algebraMap S.Bprime A')) x)
  simpa using congrArg (fun f : S.Bprime →+* S.CPrime ↦ f x)
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap :
      ((Algebra.TensorProduct.includeLeft : Dp →ₐ[S.Bprime] S.CPrime).toRingHom.comp
          (algebraMap S.Bprime Dp)) =
        ((Algebra.TensorProduct.includeRight : A' →ₐ[S.Bprime] S.CPrime).toRingHom.comp
          (algebraMap S.Bprime A')))

-- Proof sketch: write `C' = D' ⊗[B'] A'`. Then `I C'` is the image of `D' ⊗[B'] I → C'` by the
-- tensor-product description of extended ideals. The pullback hypothesis identifies
-- `ker(B' → B)` with `ker(A' → A)` via `B' → A'`, so tensoring with `D'` transports generators of
-- `J D'` onto generators of `I C'`.
/-- Lemma 15.7.3: in Situation 15.7.1, if `J = ker(B' → B)`, then the image of the extended ideal
`J D'` under the canonical map `D' → C'` is the extended ideal `I C'`, equivalently the map
`J D' → I C'` is surjective. -/
theorem kernelIdealToBInDp_image_eq_kernelIdealInCPrime
    (S : Situation) :
    Ideal.map S.dprimeToCPrime (Ideal.map S.bprimeToDp (RingHom.ker S.bprimeToB)) =
      Ideal.map S.aprimeToCPrime (RingHom.ker S.fromAprime) := by
  rw [Ideal.map_map, S.dprimeToCPrime_comp_bprimeToDp, ← Ideal.map_map]
  simpa using congrArg (Ideal.map S.aprimeToCPrime) (S.kernelIdealToB_image_eq_kernelIdealInAprime)

end FiberProductBaseChangeSituation

end

/-! ### Lemma_15_7_4 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CommRingCat
open scoped TensorProduct

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "fiberProductFunctor" =>
  (@module_tensor_pullback_right_adjoint
    S.C
    S.CPrime
    S.D
    Dp
    _ _ _ _
    S.dToC
    S.cprimeToC
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes : S.relativeModuleCategory ⥤ ModuleCat Dp)

/- Domain-style sampling for Lemma 15.7.4:
- primary domain: module finiteness for the canonical fibre-product functor attached to the
  tensor square `D' → D`, `D' → C'`, `D → C`, `C' → C`;
- sampled owner declarations:
  `SurjectiveRingPullbackSituation`,
  `surjectiveRingPullbackModuleAdjunctionMap_surjective`,
  `surjectiveRingPullbackModuleFiberProduct_finite`,
  `Algebra.TensorProduct.map_surjective`;
- best owner abstraction: the tensor square should be handled through the owner theorem
  `surjectiveRingPullbackModuleFiberProduct_finite`, after packaging the square
  `D → C`, `C' → C` as a `SurjectiveRingPullbackSituation`;
- primitive data: the base-change situation `S`;
- derived API: the tensor-square surjective pullback situation and the canonical comparison map
  `D' → D ×_C C'`.

Source/core/bridge triage:
- `source-facing`: `relativeModuleFiberProduct_finite`;
- `core/canonical`: `surjectiveRingPullbackModuleFiberProduct_finite`;
- `bridge/view`: the tensor-square surjective pullback situation and the comparison
  `D' → D ×_C C'`. -/

private theorem cprimeToC_surjective
    (S : Situation) :
    Function.Surjective S.cprimeToC := by
  intro z
  refine TensorProduct.induction_on z ?_ ?_ ?_
  · exact ⟨0, by simp⟩
  · intro d a
    obtain ⟨a', rfl⟩ := S.fromAprime_surjective a
    refine ⟨d ⊗ₜ[S.Bprime] a', ?_⟩
    let _ : Algebra A' A := S.fromAprime.toAlgebra
    rfl
  · intro z₁ z₂ hz₁ hz₂
    rcases hz₁ with ⟨w₁, rfl⟩
    rcases hz₂ with ⟨w₂, rfl⟩
    exact ⟨w₁ + w₂, by simp⟩

/-- The tensor square `D → C`, `C' → C` defines a surjective pullback situation whose source ring
is the canonical pullback `D ×_C C'`. -/
private def tensorPullbackSituation
    (S : Situation) :
    SurjectiveRingPullbackSituation S.D S.C S.CPrime where
  toA := S.dToC
  fromAprime := S.cprimeToC
  fromAprime_surjective := cprimeToC_surjective S

-- Proof sketch: apply Lemma `15.6.7` to the canonical surjective pullback situation attached to
-- the tensor square. The comparison map `D' → D ×_C C'` is surjective by Lemma `15.6.5` applied
-- to the original pullback square `B' → B`, `B' → A'`, `B → A`, `A' → A`, and then finiteness
-- descends along that surjection.
/-- Lemma 15.7.4: in the base-changed fibre-product situation of Lemma `15.7.2`, if `N` is finite
over `D` and `M'` is finite over `C'`, then the fibre-product module `N ×_φ M'` is finite over
`D'`. -/
theorem relativeModuleFiberProduct_finite
    (X : S.relativeModuleCategory)
    (hfst : Module.Finite S.D X.fst)
    (hsnd : Module.Finite S.CPrime X.snd) :
    Module.Finite Dp ((fiberProductFunctor).obj X) := sorry

end FiberProductBaseChangeSituation

end

/-! ### Lemma_15_7_5 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/-- The object property on `Mod_{D'}` requiring flatness over the base ring `B'`. -/
abbrev relativeFlatModuleProperty
    (S : Situation) :
    ObjectProperty (ModuleCat Dp) :=
  fun L ↦ Module.Flat S.Bprime ((ModuleCat.restrictScalars S.bprimeToDp).obj L)

/-- The full subcategory of `D'`-modules that are flat over the base ring `B'`. -/
abbrev RelativeFlatModuleCat
    (S : Situation) :=
  (relativeFlatModuleProperty S).FullSubcategory

/-- The object property on the relative pullback category requiring the `D`-component to be flat
over `B` and the `C'`-component to be flat over `A'`. -/
abbrev relativeFlatPullbackProperty
    (S : Situation) :
    ObjectProperty S.relativeModuleCategory :=
  fun X ↦
    Module.Flat B ((ModuleCat.restrictScalars S.bToD).obj X.fst) ∧
      Module.Flat A' ((ModuleCat.restrictScalars S.aprimeToCPrime).obj X.snd)

/-- The full subcategory of pullback triples `(N, M', \varphi)` whose `D`-component is flat over
`B` and whose `C'`-component is flat over `A'`. -/
abbrev RelativeFlatPullbackCat
    (S : Situation) :=
  (relativeFlatPullbackProperty S).FullSubcategory

-- Proof sketch: the two components of
-- the canonical owner-derived base-change functor on `L'` are obtained by extension of scalars
-- along `B' → B` and `B' → A'`. Flatness is preserved by
-- base change, so a `D'`-module that is flat over `B'` yields a pullback triple whose components
-- are flat over `B` and `A'`.
/-- Base change from `D'` to the relative pullback category preserves flatness over the original
base rings. -/
theorem relativeModuleFunctor_obj_mem_flatPullbackProperty
    (S : Situation)
    ⦃L' : ModuleCat Dp⦄
    (hflat : relativeFlatModuleProperty S L') :
    relativeFlatPullbackProperty S (S.relativeModuleFunctor.obj L') := sorry

/-- The relative base-change functor restricted to modules flat over `B'`. -/
noncomputable abbrev relativeFlatBaseChangeFunctor
    (S : Situation) :
    RelativeFlatModuleCat S ⥤ RelativeFlatPullbackCat S :=
  ObjectProperty.lift
    (relativeFlatPullbackProperty S)
    ((relativeFlatModuleProperty S).ι ⋙ S.relativeModuleFunctor)
    (fun L' ↦ relativeModuleFunctor_obj_mem_flatPullbackProperty S L'.2)

-- Proof sketch: the fibre-product module is the same kernel construction as in the surjective
-- pullback case, now applied to the tensor square from Situation `15.7.1`. Lemma `15.6.8`
-- predicts that flatness of the `D`-component over `B` and of the `C'`-component over `A'`
-- implies flatness of the resulting `D'`-module over `B'`.
/-- The fibre-product `D'`-module attached to a flat relative pullback triple is flat over the
base ring `B'`. -/
theorem relativeModuleFiberProduct_flat
    (S : Situation)
    ⦃X : S.relativeModuleCategory⦄
    (hflat : relativeFlatPullbackProperty S X) :
    relativeFlatModuleProperty S
      ((module_tensor_pullback_right_adjoint
        S.dprimeToD
        S.dprimeToCPrime
        S.tensor_square_commutes).obj X) := sorry

/-- The fibre-product functor restricted to the flat subcategories. -/
noncomputable abbrev relativeFlatFiberProductFunctor
    (S : Situation) :
    RelativeFlatPullbackCat S ⥤ RelativeFlatModuleCat S :=
  ObjectProperty.lift
    (relativeFlatModuleProperty S)
    ((relativeFlatPullbackProperty S).ι ⋙
      module_tensor_pullback_right_adjoint
        S.dprimeToD
        S.dprimeToCPrime
        S.tensor_square_commutes)
    (fun X ↦ relativeModuleFiberProduct_flat S X.2)

-- Proof sketch: apply the flat pullback criterion from Lemma `15.6.8` to the tensor square
-- `D' → D`, `D' → C'`, `D → C`, `C' → C`. Flatness over `B'` gives precisely the hypothesis
-- needed for the owner adjunction unit to be an isomorphism.
/-- A `D'`-module flat over `B'` is canonically isomorphic to the fibre product of its scalar
extensions to `D` and `C'`, via the unit of the owner adjunction
`module_tensor_pullback_adjunction`. -/
theorem relativeModuleAdjunctionMap_isIso_of_flat
    (S : Situation)
    (L' : ModuleCat Dp)
    (hflat : relativeFlatModuleProperty S L') :
    IsIso
      ((module_tensor_pullback_adjunction
        S.dprimeToD
        S.dprimeToCPrime
        S.tensor_square_commutes).unit.app L') := sorry

-- Proof sketch: the restricted base-change functor lands in the flat pullback full subcategory by
-- the preceding preservation theorem, and the restricted fibre-product functor lands back in the
-- flat `D'`-module subcategory by the flatness theorem above. The unit isomorphisms come from the
-- owner adjunction unit for flat modules, and the counit isomorphisms are the objectwise
-- identities from the fibre-product description of Lemma `15.7.2`.
/-- Lemma 15.7.5: the category of `D'`-modules flat over `B'` is equivalent to the full
subcategory of `Mod_D ×_[Mod_C] Mod_{C'}` consisting of triples `(N, M', \varphi)` with `N`
flat over `B` and `M'` flat over `A'`. -/
theorem relativeFlatBaseChangeFunctor_isEquivalence
    (S : Situation) :
    Functor.IsEquivalence (relativeFlatBaseChangeFunctor S) := sorry

end FiberProductBaseChangeSituation

end

/-! ### Lemma_15_7_6 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

universe u

noncomputable section

section

variable {R S : Type u} [CommRing R] [CommRing S]

/- Domain-style sampling for Lemma 15.7.6:
- primary domain: commutative algebra of flat/finitely presented factorizations of ring maps and
  finite presentation of fibre-product modules in a tensor-base-change square;
- sampled owner declarations:
  `RingHom.Flat`,
  `RingHom.FinitePresentation`,
  `module_tensor_pullback_right_adjoint`,
  `Module.FinitePresentation`;
- best owner abstraction: the factorization hypothesis should use the canonical ring-map owners
  `g.Flat` and `h.FinitePresentation`, while the fibre-product module itself is owned by
  `module_tensor_pullback_right_adjoint`;
- primitive data: the relative pullback object `X` and a factorization `B' → P → D'`;
- derived API: finite presentation of the induced fibre-product module over `D'`.

Source/core/bridge triage:
- `source-facing`: the finite-presentation theorem for the fibre-product module;
- `core/canonical`: `RingHom.Flat`, `RingHom.FinitePresentation`,
  `Module.FinitePresentation`, and `module_tensor_pullback_right_adjoint`;
- `bridge/view`: the explicit existential factorization hypothesis on `S.bprimeToDp`. -/

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _
variable (S : Situation)

local notation "fiberProductFunctor" =>
  module_tensor_pullback_right_adjoint
    S.dprimeToD
    S.dprimeToCPrime
    S.tensor_square_commutes

/-- Restricting scalars along `B → D` gives the first component of a relative pullback object its
canonical `B`-module structure. -/
private instance instModuleFstOverB
    (X : S.relativeModuleCategory) : Module B X.fst :=
  Module.compHom X.fst (algebraMap B S.D)

/-- Restricting scalars along `A' → C'` gives the second component of a relative pullback object
its canonical `A'`-module structure. -/
private instance instModuleSndOverAprime
    (X : S.relativeModuleCategory) : Module A' X.snd :=
  Module.compHom X.snd (algebraMap A' S.CPrime)

-- Proof sketch: factor `B' → D'` through a flat intermediate ring `D''` over which `D'` is
-- finitely presented, replace the original tensor square by the corresponding flat base-changed
-- one, and then combine Lemmas `15.7.4`, `15.6.8`, and the standard finite-presentation
-- criterion via a presentation of the kernel of a finite free cover.
/-- Lemma 15.7.6: in the fibre-product base-change situation of Lemma `15.7.2`, if the `D`-module
`N` is finitely presented and flat over `B`, the `C'`-module `M'` is finitely presented and flat
over `A'`, and the map `B' → D'` factors as a flat ring map followed by a finitely presented ring
map, then the fibre-product module `N ×_M M'` is finitely presented over `D'`. -/
theorem relativeModuleFiberProduct_finitePresentation_of_flat_of_factorization
    (X : S.relativeModuleCategory)
    [Module.FinitePresentation S.D X.fst]
    [Module.Flat B X.fst]
    [Module.FinitePresentation S.CPrime X.snd]
    [Module.Flat A' X.snd]
    (hfactor :
      ∃ (P : Type u) (_ : CommRing P) (g : S.Bprime →+* P) (h : P →+* Dp),
        g.Flat ∧ h.FinitePresentation ∧ S.bprimeToDp = h.comp g) :
    Module.FinitePresentation Dp (fiberProductFunctor.obj X) := sorry

end FiberProductBaseChangeSituation

end

end

/-! ### Lemma_15_7_7 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CommRingCat

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

-- Proof sketch: this is the descent statement for finite type in the fibre-product algebra
-- situation; the two directions are read off from base change along `B' → B` and `B' → A'` and
-- from the finite-generation construction in the textbook.
/-- Lemma 15.7.7 (1): the map `B' → D'` is of finite type if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are of finite type. -/
theorem baseChangeMap_finiteType_iff
    (S : Situation) :
    S.bprimeToDp.FiniteType ↔ S.bToD.FiniteType ∧ S.aprimeToCPrime.FiniteType := sorry

-- Proof sketch: the forward implication comes from base change preserving flatness, while the
-- reverse implication is the flatness part of the fibre-product descent argument for the tensor
-- square attached to `S`.
/-- Lemma 15.7.7 (2): the map `B' → D'` is flat if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are flat. -/
theorem baseChangeMap_flat_iff
    (S : Situation) :
    Module.Flat S.Bprime Dp ↔ Module.Flat B S.D ∧ Module.Flat A' S.CPrime := sorry

-- Proof sketch: combine the flatness equivalence from the previous clause with the finite-type
-- criterion and the finite-presentation descent statement already proved for fibre-product modules.
/-- Lemma 15.7.7 (3): the map `B' → D'` is flat and of finite presentation if and only if the two
base-changed maps `B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are flat and of finite
presentation. -/
theorem baseChangeMap_flat_finitePresentation_iff
    (S : Situation) :
    (S.bprimeToDp.Flat ∧ S.bprimeToDp.FinitePresentation) ↔
      (S.bToD.Flat ∧ S.bToD.FinitePresentation) ∧
        (S.aprimeToCPrime.Flat ∧ S.aprimeToCPrime.FinitePresentation) := sorry

-- Proof sketch: smoothness is equivalent to flatness plus finite presentation together with the
-- smoothness of fibres; the fibres of `B' → D'` identify with the corresponding fibres of the two
-- base changes exactly as in the textbook.
/-- Lemma 15.7.7 (4): the map `B' → D'` is smooth if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are smooth. -/
theorem baseChangeMap_smooth_iff
    (S : Situation) :
    S.bprimeToDp.Smooth ↔ S.bToD.Smooth ∧ S.aprimeToCPrime.Smooth := sorry

-- Proof sketch: an étale map is a smooth map with discrete fibres; after the fibre
-- identifications used in the smooth case, the étale criterion descends and ascends across the
-- fibre-product square.
/-- Lemma 15.7.7 (5): the map `B' → D'` is étale if and only if the two base-changed maps
`B → D = D' ⊗[B'] B` and `A' → C' = D' ⊗[B'] A'` are étale. -/
theorem baseChangeMap_etale_iff
    (S : Situation) :
    S.bprimeToDp.Etale ↔ S.bToD.Etale ∧ S.aprimeToCPrime.Etale := sorry

-- Proof sketch: this is the flat descent identification of `D'` with the pullback of its two
-- scalar extensions along `B' → B` and `B' → A'`, now stated in `CommRingCat`.
/-- Lemma 15.7.7 (6): if `D'` is flat over `B'`, then the canonical map
`D' → (D' ⊗[B'] B) ×_{D' ⊗[B'] A} (D' ⊗[B'] A')`
is an isomorphism. -/
theorem tensorPullbackComparison_isIso_of_flat
    (S : Situation)
    [Module.Flat S.Bprime Dp] :
    IsIso S.tensorPullbackComparison := sorry

end FiberProductBaseChangeSituation

namespace SurjectiveRingPullbackSituation

local notation "Situation" => @SurjectiveRingPullbackSituation B A A' _ _ _

/-- The object property on `Under (B')` selecting flat `B'`-algebras. -/
abbrev flatAlgebraProperty
    (S : Situation) :
    ObjectProperty (Under S.Bprime) :=
  fun D' ↦ Module.Flat S.Bprime D'

/-- The full subcategory of flat algebras over the fibre-product ring `B' = B ×_A A'`. -/
abbrev FlatAlgebraCat
    (S : Situation) :=
  (flatAlgebraProperty S).FullSubcategory

/-- The category of systems `(D, C', \varphi)` consisting of a `B`-algebra, an `A'`-algebra, and
an isomorphism between their two base changes to `A`. -/
abbrev algebraSystemCategory
    (S : Situation) :=
  let _ : Algebra B A := S.toA.toAlgebra
  let _ : Algebra A' A := S.fromAprime.toAlgebra
  CategoricalPullback
    (Under.pushout (CommRingCat.ofHom S.toA))
    (Under.pushout (CommRingCat.ofHom S.fromAprime))

/-- The first component of an algebra system carries its canonical `B`-algebra structure. -/
private noncomputable instance instAlgebraSystemFst
    (S : Situation) (X : algebraSystemCategory S) : Algebra B X.fst := by
  rcases X.fst with ⟨_, _, f⟩
  exact f.hom.toAlgebra

/-- The second component of an algebra system carries its canonical `A'`-algebra structure. -/
private noncomputable instance instAlgebraSystemSnd
    (S : Situation) (X : algebraSystemCategory S) : Algebra A' X.snd := by
  rcases X.snd with ⟨_, _, f⟩
  exact f.hom.toAlgebra

/-- The object property on algebra systems requiring flatness of the `B`-algebra component and of
the `A'`-algebra component. -/
abbrev flatAlgebraSystemProperty
    (S : Situation) :
    ObjectProperty (algebraSystemCategory S) :=
  fun X ↦
    Module.Flat B X.fst ∧ Module.Flat A' X.snd

/-- The full subcategory of algebra systems `(D, C', \varphi)` with `D` flat over `B` and `C'`
flat over `A'`. -/
abbrev FlatAlgebraSystemCat
    (S : Situation) :=
  (flatAlgebraSystemProperty S).FullSubcategory

/-- The comparison isomorphism between the two ways of pushing a `B'`-algebra forward to an
`A`-algebra through the pullback square `B' → B`, `B' → A'`, `B → A`, `A' → A`. -/
noncomputable def algebraBaseChangeComparison
    (S : Situation) :
    let bprimeToB : S.Bprime ⟶ of B := ofHom S.bprimeToB
    let bprimeToAprime : S.Bprime ⟶ of A' := ofHom S.bprimeToAprime
    Under.pushout bprimeToB ⋙ Under.pushout (ofHom S.toA) ≅
      Under.pushout bprimeToAprime ⋙ Under.pushout (ofHom S.fromAprime) :=
  let bprimeToB : S.Bprime ⟶ of B := ofHom S.bprimeToB
  let bprimeToAprime : S.Bprime ⟶ of A' := ofHom S.bprimeToAprime
  let hcomm : bprimeToB ≫ ofHom S.toA = bprimeToAprime ≫ ofHom S.fromAprime := by
    simpa using congrArg ofHom S.comm
  (Under.pushoutComp bprimeToB (ofHom S.toA)).symm ≪≫
    eqToIso (congrArg (fun f ↦ Under.pushout f) hcomm) ≪≫
    Under.pushoutComp bprimeToAprime (ofHom S.fromAprime)

/-- The categorical square of pushout functors from `B'`-algebras to `B`-algebras and
`A'`-algebras attached to the pullback square `B' = B ×_A A'`. -/
noncomputable def algebraBaseChangeSquare
    (S : Situation) :
    CategoricalPullback.CatCommSqOver
      (Under.pushout (ofHom S.toA))
      (Under.pushout (ofHom S.fromAprime))
      (Under S.Bprime) where
  fst := Under.pushout (ofHom S.bprimeToB)
  snd := Under.pushout (ofHom S.bprimeToAprime)
  iso := algebraBaseChangeComparison S

/-- The canonical functor sending a `B'`-algebra to the corresponding system
`(D, C', \varphi)` of its two pushouts to `B` and `A'` together with the induced isomorphism after
base change to `A`. -/
noncomputable def algebraBaseChangeFunctor
    (S : Situation) :
    Under S.Bprime ⥤ algebraSystemCategory S :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (Under.pushout (ofHom S.toA))
    (Under.pushout (ofHom S.fromAprime))
    (Under S.Bprime)).obj
    (algebraBaseChangeSquare S)

-- Proof sketch: pushout of commutative rings is tensor product, and tensoring a flat `B'`-algebra
-- with `B` or `A'` preserves flatness over the new base ring. Hence the canonical base-change
-- system attached to a flat `B'`-algebra lies in the flat full subcategory.
/-- Base change from `B'`-algebras to algebra systems preserves flatness of the two components. -/
theorem algebraBaseChange_obj_mem_flatAlgebraSystemProperty
    (S : Situation)
    ⦃D' : Under S.Bprime⦄
    (hflat : flatAlgebraProperty S D') :
    flatAlgebraSystemProperty S ((algebraBaseChangeFunctor S).obj D') := sorry

/-- The canonical base-change functor on the full subcategory of flat `B'`-algebras. -/
noncomputable abbrev flatAlgebraBaseChangeFunctor
    (S : Situation) :
    FlatAlgebraCat S ⥤ FlatAlgebraSystemCat S :=
  (flatAlgebraSystemProperty S).lift
    ((flatAlgebraProperty S).ι ⋙ algebraBaseChangeFunctor S)
    (fun D' ↦ algebraBaseChange_obj_mem_flatAlgebraSystemProperty S D'.property)

-- Proof sketch: the canonical base-change construction sends a flat `B'`-algebra `D'` to the
-- system `(D' ⊗[B'] B, D' ⊗[B'] A', \varphi)`, while the previous clause identifies a flat
-- `B'`-algebra with the pullback of such a flat system. This gives the equivalence of categories
-- described in the textbook.
/-- Lemma 15.7.7 (7): the category of flat `B'`-algebras is equivalent to the category of systems
`(D, C', \varphi)` with `D` a flat `B`-algebra, `C'` a flat `A'`-algebra, and
`D ⊗[B] A ≅ A ⊗[A'] C'`. -/
theorem flatAlgebraBaseChangeFunctor_isEquivalence
    (S : Situation) :
    Functor.IsEquivalence (flatAlgebraBaseChangeFunctor S) := sorry

end SurjectiveRingPullbackSituation

end

/-! ### Remark_15_7_8 (from Chap15) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Limits.CategoricalPullback

universe u

noncomputable section

section

variable {B A A' Dp : Type u}
variable [CommRing B] [CommRing A] [CommRing A'] [CommRing Dp]

namespace FiberProductBaseChangeSituation

local notation "Situation" => @FiberProductBaseChangeSituation B A A' Dp _ _ _ _

/- Domain-style sampling for Remark 15.7.8:
- primary domain: finitely presented flat quotients in module categories and their compatibility
  with the tensor-square pullback category from Situation `15.7.1`;
- sampled owner declarations:
  `Under`,
  `ObjectProperty.FullSubcategory`,
  `relativeFlatModuleProperty`,
  `relativeFlatPullbackProperty`;
- best owner abstraction: quotients of a fixed module are canonically objects of an `Under`
  category, while flatness is already owned upstream by
  `relativeFlatModuleProperty` and `relativeFlatPullbackProperty` from Lemma `15.7.5`;
- primitive data: an arrow out of `L'` in `ModuleCat Dp`, or an arrow out of
  `S.relativeModuleFunctor.obj L'` in the relative pullback category;
- derived API: the object properties cutting out surjective quotients whose targets are finitely
  presented and flat, and the equivalence between the resulting full subcategory types.

Source/core/bridge triage:
- `source-facing`: the bijection of Remark `15.7.8` between the two quotient families;
- `core/canonical`: `Under`, `ObjectProperty.FullSubcategory`, `Module.FinitePresentation`,
  `relativeFlatModuleProperty`, and `relativeFlatPullbackProperty`;
- `bridge/view`: the quotient properties below, which cut out the source-facing families inside
  the canonical `Under` owners. -/

/-- The object property on `Mod_{D'}` requiring finite presentation over `D'` together with
flatness over `B'`. -/
abbrev relativeFpFlatModuleProperty
    (S : Situation) :
    ObjectProperty (ModuleCat Dp) :=
  fun Q ↦ Module.FinitePresentation Dp Q ∧ relativeFlatModuleProperty S Q

/-- The object property on the relative pullback category requiring both components to be finitely
presented and flat over the original base rings. -/
abbrev relativeFpFlatPullbackProperty
    (S : Situation) :
    ObjectProperty S.relativeModuleCategory :=
  fun Q ↦
    Module.FinitePresentation S.D Q.fst ∧
      Module.FinitePresentation S.CPrime Q.snd ∧
        relativeFlatPullbackProperty S Q

/-- The object property on `Under L'` selecting surjective quotients of `L'` whose targets are
finitely presented over `D'` and flat over `B'`. -/
abbrev relativeFpFlatQuotientProperty
    (S : Situation) (L' : ModuleCat Dp) :
    ObjectProperty (Under L') :=
  fun Q ↦ Function.Surjective Q.hom.hom ∧ relativeFpFlatModuleProperty S Q.right

/-- The object property on the under-category of `S.relativeModuleFunctor.obj L'` selecting
compatible pairs of surjective quotients whose `D`- and `C'`-components are finitely presented and
flat over `B` and `A'`, respectively. -/
abbrev relativeFpFlatPullbackQuotientProperty
    (S : Situation) (L' : ModuleCat Dp) :
    ObjectProperty (Under (S.relativeModuleFunctor.obj L')) :=
  fun Q ↦
    let q := Q.hom
    Function.Surjective q.fst.hom ∧
      Function.Surjective q.snd.hom ∧
        relativeFpFlatPullbackProperty S Q.right

variable (S : Situation)

-- Proof sketch: send a surjective quotient `L' → Q'` to the pair of its scalar extensions to `D`
-- and `C'`, viewed as a quotient in the relative pullback category via the situation-level
-- base-change functor derived from `moduleCatBaseChangeToCategoricalPullback`.
-- For the converse, take the fibre-product module attached to a compatible quotient pair using
-- `module_tensor_pullback_right_adjoint S.dprimeToD S.dprimeToCPrime S.tensor_square_commutes`,
-- use Lemma `15.6.5` and Lemma `15.6.6` for surjectivity of
-- the comparison map, apply Lemma `15.7.5` for flatness, and deduce finite presentation from
-- Lemma `15.7.6` using the finite-presentation hypothesis on `B' → D'`.
/-- Remark 15.7.8: if `B' → D'` is finitely presented, then surjective quotients `L' → Q'` with
`Q'` finitely presented over `D'` and flat over `B'` are in bijection with compatible pairs of
surjective quotients of `L' ⊗[D'] D` and `L' ⊗[D'] C'` whose targets are finitely presented and
flat over `B` and `A'`, respectively. Here the right-hand side is expressed using the relative
pullback category of Situation `15.7.1`, which packages the common quotient over `C`. -/
theorem relativeFpFlatQuotientEquivPullbackQuotient
    (hfp : S.bprimeToDp.FinitePresentation)
    (L' : ModuleCat Dp) :
    (relativeFpFlatQuotientProperty S L').FullSubcategory ≃
      (relativeFpFlatPullbackQuotientProperty S L').FullSubcategory := sorry

end FiberProductBaseChangeSituation

end
