import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Topology.Sheaves.Points

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_48_1 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry.RingedSpace

section

/-
Domain-style sampling for Definition 20.48.1:
- primary domain: tor-amplitude and finite tor dimension in `D(\mathcal O_X)`;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionToOpenDerived`,
  `AlgebraicGeometry.RingedSpace.restrictedModuleDerivedOnOpen`,
  `CategoryTheory.HasTorAmplitudeIn`,
  `CategoryTheory.HasFiniteTorDimension`;
- best owner abstraction: the source-facing owners in this file are the ringed-space predicates
  `HasTorAmplitudeIn`, `HasFiniteTorDimension`, and `LocallyHasFiniteTorDimension`; the tensor
  construction and the passage to open subspaces are already canonically owned upstream.

Source/core/bridge triage:
- `source-facing`: the ringed-space tor-dimension predicates from Definition 20.48.1;
- `core/canonical`: `derivedTensorProduct`;
- `bridge/view`: restriction to open subspaces via `moduleRestrictionToOpenDerived` and
  `restrictedModuleDerivedOnOpen`.

Primitive vs derived:
- primitive data: the derived object `E`, interval bounds `a, b`, and the restricted objects on an
  open cover;
- derived API: local finite tor dimension on an open cover and the module-specialization
  predicate.
-/

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

local notation "ModX" => (RingedSpace.Modules X)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "single0" => DerivedCategory.singleFunctor ModX (0 : ℤ)
local notation "H" => DerivedCategory.homologyFunctor ModX
/-- Definition 20.48.1 (1): an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]`
if for every `\mathcal O_X`-module `\mathcal F`, the derived tensor product
`E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` has vanishing homology outside `[a, b]`. -/
def HasTorAmplitudeIn (E : DMod) (a b : ℤ) : Prop :=
  ∀ (ℱ : ModX) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((H i).obj ((derivedTensorProduct ((single0).obj ℱ)).obj E))

-- Proof sketch: unfold `HasTorAmplitudeIn`; it is exactly the defining homology-vanishing
-- condition for `E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` outside the interval
-- `[a, b]`.
/-- An object of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` exactly when derived tensoring
with every degree-zero module sheaf has vanishing homology outside `[a, b]`. -/
theorem hasTorAmplitudeIn_iff (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ (ℱ : ModX) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((H i).obj ((derivedTensorProduct ((single0).obj ℱ)).obj E)) := Iff.rfl

/-- Definition 20.48.1 (2): an object of `D(\mathcal O_X)` has finite tor dimension if it has
tor-amplitude in some finite interval `[a, b]`. -/
def HasFiniteTorDimension (E : DMod) : Prop :=
  ∃ a b : ℤ, HasTorAmplitudeIn E a b

-- Proof sketch: unfold `HasFiniteTorDimension`; it is exactly the existence of a finite
-- tor-amplitude interval.
/-- An object of `D(\mathcal O_X)` has finite tor dimension exactly when it has tor-amplitude in
some finite interval. -/
theorem hasFiniteTorDimension_iff (E : DMod) :
    HasFiniteTorDimension E ↔ ∃ a b : ℤ, HasTorAmplitudeIn E a b :=
  Iff.rfl

section LocalTorDimension

variable [∀ U : Opens X.carrier,
  CategoryWithHomology (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  HasCountableCoproducts (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  MonoidalCategory (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  MonoidalPreadditive (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  HasColimits (RingedSpace.Modules (X.restrict U.isOpenEmbedding))]
variable [∀ U : Opens X.carrier,
  (curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding))).Additive]
variable [∀ U : Opens X.carrier,
  ∀ ℱ : RingedSpace.Modules (X.restrict U.isOpenEmbedding),
    ((curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding))).obj ℱ).Additive]
variable [∀ U : Opens X.carrier,
  ∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules (X.restrict U.isOpenEmbedding)) ℤ),
    CochainComplex.HasMapBifunctor ℱ 𝒢
      (curriedTensor (RingedSpace.Modules (X.restrict U.isOpenEmbedding)))]

private abbrev HasFiniteTorDimensionOnOpen (U : Opens X.carrier) (E : DMod) : Prop :=
  HasFiniteTorDimension (restrictedModuleDerivedOnOpen U E)

/-- Definition 20.48.1 (3): an object of `D(\mathcal O_X)` locally has finite tor dimension if
there is an open covering of `X` on whose members its restriction has finite tor dimension. -/
def LocallyHasFiniteTorDimension (E : DMod) : Prop :=
  ∃ (ι : Type v) (U : ι → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i, HasFiniteTorDimensionOnOpen (U i) E

-- Proof sketch: unfold `LocallyHasFiniteTorDimension`; it is exactly the existence of an indexed
-- open cover on which the restricted derived object has finite tor dimension.
end LocalTorDimension

/-- Definition 20.48.1 (4): an `\mathcal O_X`-module `\mathcal F` has tor dimension at most `d`
if its degree-zero derived object `\mathcal F[0]` has tor-amplitude in `[-d, 0]`. -/
def ModuleHasTorDimensionLE (ℱ : ModX) (d : ℕ) : Prop :=
  HasTorAmplitudeIn ((single0).obj ℱ) (-((d : ℤ))) 0

-- Proof sketch: unfold `ModuleHasTorDimensionLE`; it is exactly the tor-amplitude condition for
-- the degree-zero derived object `\mathcal F[0]` with bounds `[-d, 0]`.
/-- An `\mathcal O_X`-module has tor dimension at most `d` exactly when its degree-zero derived
object has tor-amplitude in `[-d, 0]`. -/
theorem moduleHasTorDimensionLE_iff (ℱ : ModX) (d : ℕ) :
    ModuleHasTorDimensionLE ℱ d ↔
      HasTorAmplitudeIn ((single0).obj ℱ) (-((d : ℤ))) 0 := Iff.rfl

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_48_2 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

/-- The category of `\mathcal O_X`-modules on a ringed space. -/
section

variable {X : RingedSpace}
variable [monoidal :
  MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [Abelian (RingedSpace.Modules X)]
variable [((curriedTensor (RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 :
    CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

/-- A source-level tor-amplitude predicate for a cochain complex of `\mathcal O_X`-modules,
expressed by exactness of tensoring with every degree-zero module sheaf outside the interval
`[a, b]`. -/
def HasComplexTorAmplitudeIn
    (E : CochainComplex (RingedSpace.Modules X) ℤ)
    (a b : ℤ) : Prop :=
  ∀ (ℱ : (RingedSpace.Modules X)) (i : ℤ), i ∉ Set.Icc a b →
    HomologicalComplex.ExactAt
      (HomologicalComplex.tensorObj ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ) E) i

-- Proof sketch: this is just the defining predicate for `HasComplexTorAmplitudeIn` unfolded.
/-- The complex-level tor-amplitude predicate is exactly exactness of tensoring with every
degree-zero module sheaf outside the interval `[a, b]`. -/
theorem hasComplexTorAmplitudeIn_iff
    (E : CochainComplex (RingedSpace.Modules X) ℤ) (a b : ℤ) :
    HasComplexTorAmplitudeIn E a b ↔
      ∀ (ℱ : (RingedSpace.Modules X)) (i : ℤ), i ∉ Set.Icc a b →
        HomologicalComplex.ExactAt
          (HomologicalComplex.tensorObj ((CochainComplex.singleFunctor (RingedSpace.Modules X) 0).obj ℱ) E)
          i :=
  sorry

-- Proof sketch: for any `\mathcal F`, the tor-amplitude hypothesis gives exactness of
-- `\mathcal E^\bullet \otimes \mathcal F` at degree `a - 1`. The bounded-above flat hypotheses
-- make `\mathcal E^{a - 2} ⟶ \mathcal E^{a - 1} ⟶ \mathcal E^a ⟶ \operatorname{coker}(d^{a-1})
-- ⟶ 0` a flat resolution of the cokernel, so `\operatorname{Tor}_1` of the cokernel against any
-- `\mathcal F` vanishes. Then apply the flatness criterion from Lemma `20.26.16`.
/-- Lemma 20.48.2: if `\mathcal E^\bullet` is a bounded above complex of flat
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)` and has tor-amplitude in `[a, b]`,
then the cokernel of `d_{\mathcal E^\bullet}^{a - 1}` is a flat `\mathcal O_X`-module. -/
theorem cokernel_differential_isFlat_of_hasComplexTorAmplitudeIn
    (E : CochainComplex (RingedSpace.Modules X) ℤ) (a b : ℤ)
    (hbounded : ∃ n : ℤ, E.IsStrictlyLE n)
    (hFlat : ∀ n : ℤ, (E.X n).IsFlat)
    (hTor : HasComplexTorAmplitudeIn E a b) :
    (cokernel (E.d (a - 1) a)).IsFlat := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_48_3 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

local notation "ModX" => (RingedSpace.Modules X)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

/-- An `\mathcal O_X`-module sheaf, regarded as a presheaf of modules over the underlying
presheaf of commutative rings. -/
abbrev asCommModulePresheaf (ℱ : ModX) :
    PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat.{u}) :=
  ℱ.val

/-- The stalk of an `\mathcal O_X`-module sheaf, bundled as a module over `\mathcal O_{X, x}`. -/
abbrev stalkModule (ℱ : ModX) (x : X) : ModuleCat (X.presheaf.stalk x) :=
  ModuleCat.of (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk (asCommModulePresheaf ℱ).presheaf x)

/-- A sheaf of `\mathcal O_X`-modules is flat if each stalk is a flat module over the
corresponding stalk of the structure sheaf. -/
def IsFlatModuleSheaf (ℱ : ModX) : Prop :=
  ∀ x : X, Module.Flat (X.presheaf.stalk x) (stalkModule ℱ x)

/-- A flat representative of a derived `\mathcal O_X`-module in the degree range `[a, b]` is a
cochain complex of flat `\mathcal O_X`-modules concentrated in `[a, b]` whose image in the
derived category is isomorphic to the given object. -/
def HasFlatRepresentativeInRange (E : DMod) (a b : ℤ) : Prop :=
  ∃ K : CochainComplex ModX ℤ,
    K.IsStrictlyGE a ∧
      K.IsStrictlyLE b ∧
      (∀ i : ℤ, IsFlatModuleSheaf (K.X i)) ∧
      Nonempty (E ≅ DerivedCategory.Q.obj K)

-- Proof sketch: for the forward implication, replace `E` by a bounded-above K-flat complex of
-- flat `\mathcal O_X`-modules, truncate away the terms above `b`, and then truncate below `a`;
-- Lemma `20.48.2` shows the new degree-`a` term remains flat. For the reverse implication,
-- compute derived tensor products using the flat representative and read off the vanishing of
-- homology outside `[a, b]` from the strict support of the representing complex.
/-- Lemma 20.48.3: for a ringed space `(X, \mathcal O_X)` and `a ≤ b`, an object `E` of
`D(\mathcal O_X)` has tor-amplitude in `[a, b]` if and only if it is represented by a complex of
flat `\mathcal O_X`-modules vanishing outside `[a, b]`. -/
theorem hasTorAmplitudeIn_iff_hasFlatRepresentativeInRange
    (E : DMod) (a b : ℤ) (_hab : a ≤ b) :
    HasTorAmplitudeIn E a b ↔ HasFlatRepresentativeInRange E a b := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_48_4 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

variable [CategoryWithHomology (Modules Y)]
variable [HasCountableCoproducts (Modules Y)]
variable [MonoidalCategory (Modules Y)]
variable [MonoidalPreadditive (Modules Y)]
variable [HasColimits (Modules Y)]
variable [(curriedTensor (Modules Y)).Additive]
variable [∀ ℱ : Modules Y, ((curriedTensor (Modules Y)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules Y) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules Y))]

-- Proof sketch: by Lemma `20.48.3`, choose a representative of `E` by a complex of flat
-- `\mathcal O_Y`-modules concentrated in degrees `[a,b]`. Pull it back termwise along `f`; the
-- pulled-back terms stay flat by Lemma `17.17.4`, and the degree support is unchanged. Apply
-- Lemma `20.48.3` again to identify this pulled-back flat complex with `Lf^*E`.
/-- Lemma 20.48.4: if `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)` is a morphism of ringed
spaces and `E` is an object of `D(\mathcal O_Y)` with tor-amplitude in `[a, b]`, then the
derived pullback `Lf^*E` has tor-amplitude in `[a, b]`. -/
theorem modulePullbackDerived_hasTorAmplitudeIn
    (f : X ⟶ Y) [(modulePullback f).Additive] (E : ModuleDerived Y) (a b : ℤ)
    (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeIn ((modulePullbackDerived f).obj E) a b := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_48_5 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open ComplexShape
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

local notation "DMod" => ModuleDerived X

/-- The commutative stalk ring `\mathcal O_{X, x}` packaged via the canonical site point
associated to `x`. -/
abbrev stalkCommRing (x : X) : CommRingCat :=
  (Opens.pointGrothendieckTopology x).presheafFiber.obj X.presheaf

/-- The forgotten ring-valued stalk identifies canonically with the commutative stalk ring at
`x`. -/
private abbrev stalkPointRingEquivCommRing (x : X) :
    ↑(CategoryTheory.point_stalk_ring (Opens.pointGrothendieckTopology x) (RingedSpace.ringCatSheaf X)) ≃+*
      ↑(stalkCommRing x) :=
  (((Opens.pointGrothendieckTopology x).presheafFiberCompIso
      (forget₂ CommRingCat RingCat)).app X.presheaf).ringCatIsoToRingEquiv

/-- The stalk functor on `\mathcal O_X`-modules at the point `x`. -/
private abbrev stalkModuleFunctor (x : X) :
    Modules X ⥤ ModuleCat (stalkCommRing x) :=
  CategoryTheory.point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x)
      (RingedSpace.ringCatSheaf X) ⋙
    ModuleCat.restrictScalars (stalkPointRingEquivCommRing x).symm.toRingHom

-- Proof sketch: specialize Lemma `18.36.3` to the canonical site point associated to `x` in the
-- topological space underlying `X`.
/-- The stalk functor on `\mathcal O_X`-modules at `x` is exact. -/
private theorem stalkModuleFunctor_exact (x : X) :
    exactFunctor (Modules X) (ModuleCat (stalkCommRing x))
      (stalkModuleFunctor x) := sorry

/-- The exact-functor package attached to the stalk functor on `\mathcal O_X`-modules at `x`. -/
private abbrev stalkModuleExactFunctor (x : X) :
    Modules X ⥤ₑ ModuleCat (stalkCommRing x) :=
  let _ : PreservesFiniteLimits (stalkModuleFunctor x) :=
    ((CategoryTheory.exactFunctor_iff (stalkModuleFunctor x)).mp
      (stalkModuleFunctor_exact x)).1
  let _ : PreservesFiniteColimits (stalkModuleFunctor x) :=
    ((CategoryTheory.exactFunctor_iff (stalkModuleFunctor x)).mp
      (stalkModuleFunctor_exact x)).2
  ExactFunctor.of (stalkModuleFunctor x)

-- Proof sketch: the site-theoretic stalk functor is additive, and restriction of scalars along a
-- ring isomorphism is additive, so their composite exact functor is additive as well.
/-- The exact stalk functor on `\mathcal O_X`-modules is additive. -/
private theorem stalkModuleExactFunctor_additive (x : X) :
    (stalkModuleExactFunctor x).obj.Additive := sorry

/-- The derived stalk functor `E ↦ E_x` from `D(\mathcal O_X)` to `D(\mathcal O_{X, x})`. -/
abbrev stalkDerived (x : X) :
    DMod ⥤ DerivedCategory (ModuleCat (stalkCommRing x)) :=
  let _ : (stalkModuleExactFunctor x).obj.Additive :=
    stalkModuleExactFunctor_additive x
  (stalkModuleExactFunctor x).obj.mapDerivedCategory

-- Proof sketch: for `(1) → (2)`, identify the derived stalk object with pullback along the point
-- morphism `({x}, \mathcal O_{X, x}) ⟶ (X, \mathcal O_X)` and apply Lemma `20.48.4`. For
-- `(2) → (1)`, test `E \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F` on stalks; stalks commute
-- with tensor products by Lemma `17.16.1`, and Lemma `17.3.1` lets one detect vanishing by all
-- stalks.
/-- Lemma 20.48.5: an object `E` of `D(\mathcal O_X)` has tor-amplitude in `[a, b]` if and only
if, for every point `x : X`, the derived stalk object `E_x` in `D(\mathcal O_{X, x})` has
tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_iff_forall_stalk
    (E : DMod) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ x : X, CategoryTheory.HasTorAmplitudeIn ((stalkDerived x).obj E) a b := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_48_6 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Pretriangulated
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "ModX" => (RingedSpace.Modules X)

variable {a b : ℤ}

local notation "DMod" => ModuleDerived X

variable [CategoryWithHomology ModX]
variable [HasCountableCoproducts ModX]
variable [MonoidalCategory ModX]
variable [MonoidalPreadditive ModX]
variable [HasColimits ModX]
variable [(curriedTensor ModX).Additive]
variable [∀ ℱ : ModX, ((curriedTensor ModX).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex ModX ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ModX)]

/- Domain-style sampling for Lemma 20.48.6:
- primary domain: tor-amplitude in the derived category of module sheaves on a ringed space and
  its behavior under distinguished triangles;
- sampled owner declarations:
  `CategoryTheory.HasTorAmplitudeIn`,
  `CategoryTheory.hasTorAmplitudeIn_obj₃_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₂_of_distinguishedTriangle`,
  `CategoryTheory.hasTorAmplitudeIn_obj₁_of_distinguishedTriangle`,
  `hasTorAmplitudeIn_iff_forall_stalk`,
  `stalkDerived`;
- best owner abstraction: the chapter owner is
  `CategoryTheory.HasTorAmplitudeIn` on stalkwise derived module categories, with
  `hasTorAmplitudeIn_iff_forall_stalk` as the canonical ringed-space bridge;
- primitive vs. derived:
  primitive data are the ringed-space tor-amplitude predicate `HasTorAmplitudeIn` and the derived
  stalk functor `stalkDerived`;
  derived API are the three distinguished-triangle closure statements below, obtained by applying
  the canonical module-category theorem stalkwise;
- source/core/bridge triage:
  `source-facing`: the three ringed-space closure statements below;
  `core/canonical`: `CategoryTheory.HasTorAmplitudeIn` together with the Chapter 15
    distinguished-triangle theorem;
  `bridge/view`: `stalkDerived` and `hasTorAmplitudeIn_iff_forall_stalk`, which transport between
    ringed-space objects and the canonical stalkwise module-category owner.

This file keeps the Stacks ringed-space statements as the public surface, but removes the parallel
proof wheel by deriving them directly from the canonical module-category owner theorem through the
stalk bridge. -/

-- Proof sketch: apply `- ⊗_{\mathcal O_X}^{\mathbf L} \mathcal F[0]` to the distinguished
-- triangle for an arbitrary module sheaf `\mathcal F`, use that derived tensor preserves
-- distinguished triangles, and read off the vanishing range for the third term from the
-- associated long exact homology sequence.
/-- Lemma 20.48.6 (1): in a distinguished triangle in `D(\mathcal O_X)`, if the first term has
tor-amplitude in `[a + 1, b + 1]` and the second term has tor-amplitude in `[a, b]`, then the
third term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1))
    (h₂ : HasTorAmplitudeIn T.obj₂ a b) :
    HasTorAmplitudeIn T.obj₃ a b := by
  rw [hasTorAmplitudeIn_iff_forall_stalk] at h₁ h₂ ⊢
  intro x
  simpa using CategoryTheory.hasTorAmplitudeIn_obj₃_of_distinguishedTriangle
    ((stalkDerived x).mapTriangle.obj T)
    ((stalkDerived x).map_distinguished T hT)
    (h₁ x) (h₂ x)

-- Proof sketch: tensor with an arbitrary module sheaf placed in degree `0`, use the long exact
-- homology sequence of the distinguished triangle, and apply two-out-of-three for vanishing in
-- degrees outside `[a, b]`.
/-- Lemma 20.48.6 (2): in a distinguished triangle in `D(\mathcal O_X)`, if the first and third
terms have tor-amplitude in `[a, b]`, then the second term has tor-amplitude in `[a, b]`. -/
theorem hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₁ : HasTorAmplitudeIn T.obj₁ a b)
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₂ a b := by
  rw [hasTorAmplitudeIn_iff_forall_stalk] at h₁ h₃ ⊢
  intro x
  simpa using CategoryTheory.hasTorAmplitudeIn_obj₂_of_distinguishedTriangle
    ((stalkDerived x).mapTriangle.obj T)
    ((stalkDerived x).map_distinguished T hT)
    (h₁ x) (h₃ x)

-- Proof sketch: rotate the distinguished triangle and reduce to part `(1)`, which shifts the
-- tor-amplitude interval on the first vertex by one exactly as required.
/-- Lemma 20.48.6 (3): in a distinguished triangle in `D(\mathcal O_X)`, if the second term has
tor-amplitude in `[a + 1, b + 1]` and the third term has tor-amplitude in `[a, b]`, then the
first term has tor-amplitude in `[a + 1, b + 1]`. -/
theorem hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    (T : Triangle DMod) (hT : T ∈ distTriang DMod)
    (h₂ : HasTorAmplitudeIn T.obj₂ (a + 1) (b + 1))
    (h₃ : HasTorAmplitudeIn T.obj₃ a b) :
    HasTorAmplitudeIn T.obj₁ (a + 1) (b + 1) := by
  rw [hasTorAmplitudeIn_iff_forall_stalk] at h₂ h₃ ⊢
  intro x
  simpa using CategoryTheory.hasTorAmplitudeIn_obj₁_of_distinguishedTriangle
    ((stalkDerived x).mapTriangle.obj T)
    ((stalkDerived x).map_distinguished T hT)
    (h₂ x) (h₃ x)

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_48_7 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open scoped RingedSpaceDerivedTensor

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

/-
Domain-style sampling for Lemma 20.48.7:
- primary domain: tor-amplitude in `D(\mathcal O_X)` under the derived tensor product;
- sampled owner declarations:
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn`,
  `CategoryTheory.HasTorAmplitudeIn` from Chapter 15;
- best owner abstraction: the ambient owners are the source-facing tor-amplitude predicate
  `HasTorAmplitudeIn` and the derived tensor-product owner `derivedTensorProduct`; this file should
  state only the closure property for those owners, not introduce a parallel tensor or
  tor-amplitude wrapper.

Source/core/bridge triage:
- `source-facing`: the tor-amplitude bound for `K ⊗^L L` on a ringed space;
- `core/canonical`: `HasTorAmplitudeIn` together with `derivedTensorProduct`;
- `bridge/view`: this lemma, which records the closure of the source-facing predicate under the
  canonical tensor owner.

Primitive vs derived:
- primitive data: the objects `K`, `L` and their tor-amplitude bounds;
- derived API: the induced tor-amplitude bound for `K ⊗^L L`.

No extra local wrapper is needed here, so the file keeps only the theorem surface.
-/

variable {X : RingedSpace.{u}}

local notation "ModX" => (RingedSpace.Modules X)
local notation "DMod" => DerivedCategory ModX

variable [CategoryWithHomology ModX]
variable [HasCountableCoproducts ModX]
variable [MonoidalCategory ModX]
variable [MonoidalPreadditive ModX]
variable [HasColimits ModX]
variable [(curriedTensor ModX).Additive]
variable [∀ ℱ : ModX, ((curriedTensor ModX).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex ModX ℤ), CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ModX)]

variable {a b c d : ℤ}

-- Proof sketch: test the defining tor-amplitude condition against an arbitrary module sheaf
-- placed in degree `0`, rewrite the resulting triple derived tensor product by associativity, and
-- apply the Tor spectral sequence to combine the ranges `[a, b]` and `[c, d]` into
-- `[a + c, b + d]`.
/-- Lemma 20.48.7: if `K` has tor-amplitude in `[a, b]` and `L` has tor-amplitude in `[c, d]`,
then `K \otimes_{\mathcal O_X}^{\mathbf L} L` has tor-amplitude in `[a + c, b + d]`. -/
theorem hasTorAmplitudeIn_derivedTensorProduct
    (K L : DMod)
    (hK : HasTorAmplitudeIn K a b)
    (hL : HasTorAmplitudeIn L c d) :
    HasTorAmplitudeIn (K ⊗^L L) (a + c) (b + d) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_48_8 (from Chap20) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts
open AlgebraicGeometry

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [CategoryWithHomology (Modules X)]
variable [HasCountableCoproducts (Modules X)]
variable [MonoidalCategory (Modules X)]
variable [MonoidalPreadditive (Modules X)]
variable [HasColimits (Modules X)]
variable [(curriedTensor (Modules X)).Additive]
variable [∀ ℱ : Modules X, ((curriedTensor (Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (Modules X))]

variable {a b : ℤ}

local notation "DMod" => ModuleDerived X
local notation "TorAmp" => fun E : DMod ↦ HasTorAmplitudeIn E a b

/- Domain-style sampling for Lemma 20.48.8:
- primary domain: retract-stable object properties in derived categories, with ringed-space
  tor-amplitude as the source-facing predicate and module-category tor-amplitude as the canonical
  owner abstraction;
- sampled owner declarations:
  `CategoryTheory.ObjectProperty.IsStableUnderRetracts`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_left`,
  `ObjectProperty.IsStableUnderRetracts.of_biprod_right`,
  `CategoryTheory.hasTorAmplitudeIn_isStableUnderRetracts`,
  `hasTorAmplitudeIn_iff_forall_stalk`;
- best owner abstraction: the source-facing predicate remains
  `fun E : DMod ↦ HasTorAmplitudeIn E a b`, but its retract-stability is derived from the
  canonical Chapter 15 owner instance for `CategoryTheory.HasTorAmplitudeIn` via the stalk bridge
  `hasTorAmplitudeIn_iff_forall_stalk`;
- primitive vs. derived:
  primitive data are the ringed-space tor-amplitude predicate and the canonical derived stalk
  functors;
  the retract-stability instance and the left/right biproduct consequences are derived API;
- source/core/bridge triage:
  `source-facing`: the two textbook direct-summand consequences;
  `core/canonical`: `CategoryTheory.HasTorAmplitudeIn` together with
    `ObjectProperty.IsStableUnderRetracts`;
  `bridge/view`: `stalkDerived`, `hasTorAmplitudeIn_iff_forall_stalk`,
    `of_biprod_left`, and `of_biprod_right`.

Accordingly, this file exposes the owner-level retract-stability instance and derives the two
source-facing biproduct lemmas from the canonical object-property API, transporting the proof to
the Chapter 15 module-category owner stalkwise instead of keeping a parallel local retract
argument. -/

/-- Objects of `D(\mathcal O_X)` with tor-amplitude in `[a, b]` are stable under retracts/direct
summands. -/
instance hasTorAmplitudeIn_isStableUnderRetracts :
    ObjectProperty.IsStableUnderRetracts TorAmp where
  of_retract h hE := by
    rw [hasTorAmplitudeIn_iff_forall_stalk] at hE ⊢
    intro x
    exact prop_of_retract
      (fun E : DerivedCategory (ModuleCat (stalkCommRing x)) ↦
        CategoryTheory.HasTorAmplitudeIn E a b)
      (h.map (stalkDerived x)) (hE x)

/-- Lemma 20.48.8 (1): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `K` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_left_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn K a b :=
  of_biprod_left TorAmp hKL

/-- Lemma 20.48.8 (2): if `K ⊞ L` has tor-amplitude in `[a, b]`, then `L` has tor-amplitude in
`[a, b]`. -/
theorem hasTorAmplitudeIn_right_of_biprod
    (K L : DMod)
    (hKL : HasTorAmplitudeIn (K ⊞ L) a b) :
    HasTorAmplitudeIn L a b :=
  of_biprod_right TorAmp hKL

end

end AlgebraicGeometry.RingedSpace
