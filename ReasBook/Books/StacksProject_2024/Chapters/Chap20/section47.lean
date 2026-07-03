import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_20_47_1 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

/- 
Domain-style sampling for Definition 20.47.1:
- primary domain: pseudo-coherence for derived `\mathcal O_X`-modules via local strictly perfect
  approximations after restriction to open subspaces and representative complexes in the derived
  category;
- inspected owner declarations:
  `TopologicalSpace.IsOpenCover`,
  `CochainComplex.IsStrictlyPerfect`,
  `RingedSpace.IsMPseudoCoherent`,
  `DerivedCategory.Q.objPreimage`;
- best owner abstraction: the intrinsic derived owner family `IsMPseudoCoherent` from Lemma
  `20.47.9`, with derived pseudo-coherence owned intrinsically by the universal condition
  `∀ m, IsMPseudoCoherent E m`, and the canonical quotient functor owner `DerivedCategory.Q`;
  this file should keep the source-facing complex predicates while relegating representative-based
  derived criteria to bridge theorems rather than second owner definitions;
- primitive data: an open cover, local strictly perfect complexes, and comparison maps whose
  induced maps on homology are isomorphisms above degree `m` and epimorphisms in degree `m`, plus
  a representative complex of the derived object;
- derived API: the source-facing complex predicates, the intrinsic derived owners
  `IsMPseudoCoherent` and `IsPseudoCoherent`, the open-cover bridge theorem for
  `IsMPseudoCoherent`, and the representative bridge theorems relating the complex and derived
  notions.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsMPseudoCoherent` and `CochainComplex.IsPseudoCoherent`;
- `core/canonical`: `TopologicalSpace.IsOpenCover`, `RingedSpace.IsMPseudoCoherent`,
  `RingedSpace.IsPseudoCoherent`, and `DerivedCategory.Q`;
- `bridge/view`: `isMPseudoCoherent_iff_exists_openCover`,
  `isMPseudoCoherent_iff_exists_mPseudoCoherent_representative`, and
  `isPseudoCoherent_iff_exists_pseudoCoherent_representative`.
-/
namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The category of `\mathcal O_X`-modules on a ringed space carries its standard derived
category. -/
instance sheafModules_hasDerivedCategory (X : RingedSpace.{u}) :
    HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

local notation "DModX" => ModuleDerived X
local notation "OpenComplex" U => CochainComplex (OpenSubsetSheafModules X U) ℤ

/-- Definition 20.47.1: a complex of `\mathcal O_X`-modules is `m`-pseudo-coherent if there is
an open covering of `X` such that on each member of the cover its restriction admits a morphism
from a strictly perfect complex inducing isomorphisms on cohomology in degrees `> m` and an
epimorphism in degree `m`. -/
def CochainComplex.IsMPseudoCoherent (E : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι, ∃ Ei : OpenComplex (U i),
        ∃ α : Ei ⟶
            (((moduleSheafRestrictionToOpen (U i)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj E),
          CochainComplex.IsStrictlyPerfect Ei ∧
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
              Epi (HomologicalComplex.homologyMap α m)

-- Proof sketch: unfold `CochainComplex.IsMPseudoCoherent`; the statement is exactly the local
-- strictly-perfect approximation condition from the definition, expressed using restriction of
-- complexes to opens and the induced maps on homology.
/-- Unfolding `IsMPseudoCoherent` gives the local strictly-perfect approximation criterion on an
open covering. -/
theorem cochainComplex_isMPseudoCoherent_iff
    (E : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ) :
    CochainComplex.IsMPseudoCoherent E m ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ α : Ei ⟶
                (((moduleSheafRestrictionToOpen (U i)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj E),
              CochainComplex.IsStrictlyPerfect Ei ∧
                (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
                  Epi (HomologicalComplex.homologyMap α m) :=
  Iff.rfl

/-- A complex of `\mathcal O_X`-modules is pseudo-coherent if it is `m`-pseudo-coherent for every
integer `m`. -/
def CochainComplex.IsPseudoCoherent (E : CochainComplex (RingedSpace.Modules X) ℤ) : Prop :=
  ∀ m : ℤ, CochainComplex.IsMPseudoCoherent E m

-- Proof sketch: unfold `CochainComplex.IsPseudoCoherent`; it is definitionally the universal
-- quantification of `m`-pseudo-coherence over all integers.
/-- A complex is pseudo-coherent exactly when it is `m`-pseudo-coherent for all integers. -/
theorem cochainComplex_isPseudoCoherent_iff
    (E : CochainComplex (RingedSpace.Modules X) ℤ) :
    CochainComplex.IsPseudoCoherent E ↔
      ∀ m : ℤ, CochainComplex.IsMPseudoCoherent E m :=
  Iff.rfl

/- Definition 20.47.1 (derived `m`-version): the intrinsic owner is the existing ringed-space
predicate `IsMPseudoCoherent`. -/
recall IsMPseudoCoherent

-- Proof sketch: convert between the pointwise neighborhoodwise approximation data from
-- `IsMPseudoCoherent` and a family indexed by an open cover, using `TopologicalSpace.IsOpenCover`
-- as the canonical cover owner.
/-- The owner predicate `IsMPseudoCoherent` is equivalently the existence of a strict-perfect
open-cover approximation of the restricted derived object. -/
theorem isMPseudoCoherent_iff_exists_openCover
    (E : DModX) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι, ∃ Ei : OpenComplex (U i),
            ∃ α : DerivedCategory.Q.obj Ei ⟶ (moduleDerivedRestrictionToOpen (U i)).obj E,
              CochainComplex.IsStrictlyPerfect Ei ∧
                (∀ j : ℤ, m < j →
                  IsIso
                    ((DerivedCategory.homologyFunctor (OpenSubsetSheafModules X (U i)) j).map
                      α)) ∧
                  Epi
                    ((DerivedCategory.homologyFunctor (OpenSubsetSheafModules X (U i)) m).map
                      α) := by
  sorry

/-- Definition 20.47.1 (derived `m`-version): an object of `D(\mathcal O_X)` is
`m`-pseudo-coherent exactly when it is represented by an `m`-pseudo-coherent complex. This keeps
the source-facing representative criterion visible while using the intrinsic owner
`IsMPseudoCoherent` as the canonical core notion. -/
theorem isMPseudoCoherent_iff_exists_mPseudoCoherent_representative
    (E : DModX) (m : ℤ) :
    IsMPseudoCoherent E m ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅
            (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DModX).obj K,
          CochainComplex.IsMPseudoCoherent K m := by
  sorry

/-- Definition 20.47.1 (derived version): an object of `D(\mathcal O_X)` is pseudo-coherent if
it is `m`-pseudo-coherent for every integer `m`. -/
def IsPseudoCoherent (E : DModX) : Prop :=
  ∀ m : ℤ, IsMPseudoCoherent E m

-- Proof sketch: unfold `IsPseudoCoherent`; it is definitionally the universal quantification of
-- `m`-pseudo-coherence over all integers.
/-- A derived `\mathcal O_X`-module is pseudo-coherent exactly when it is `m`-pseudo-coherent for
all integers. -/
theorem isPseudoCoherent_iff
    (E : DModX) :
    IsPseudoCoherent E ↔ ∀ m : ℤ, IsMPseudoCoherent E m :=
  Iff.rfl

/-- A derived `\mathcal O_X`-module is pseudo-coherent exactly when it has a pseudo-coherent
representative complex. This is the companion bridge from the intrinsic owner to the source-facing
representative criterion. -/
theorem isPseudoCoherent_iff_exists_pseudoCoherent_representative
    (E : DModX) :
    IsPseudoCoherent E ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅ DerivedCategory.Q.obj K,
          CochainComplex.IsPseudoCoherent K := by
  sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_2 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/- Lemma 20.47.2 (1): the intrinsic owner is the ringed-space predicate
`AlgebraicGeometry.RingedSpace.IsMPseudoCoherent`, and
`isMPseudoCoherent_iff_exists_openCover` is its open-cover bridge. -/
recall IsMPseudoCoherent

-- Proof sketch: unpack the intrinsic local strictly perfect approximation data witnessing
-- `DerivedCategory.IsMPseudoCoherent E m`, then use Lemma `20.46.8` to realize each derived local
-- map by an actual morphism of restricted complexes for the chosen representative `K`. Those
-- local morphisms satisfy the complex-level approximation criterion and therefore witness
-- `CochainComplex.IsMPseudoCoherent K m`.
/-- Lemma 20.47.2 (2): if a derived `\mathcal O_X`-module is `m`-pseudo-coherent, then every
cochain complex representing it is `m`-pseudo-coherent. -/
theorem representing_complex_isMPseudoCoherent_of_derived_isMPseudoCoherent
    (E : DModX) (m : ℤ) (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (e :
      E ≅
        (DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤ DModX).obj K)
    (hE : IsMPseudoCoherent E m) :
    CochainComplex.IsMPseudoCoherent K m := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_3 (from Chap20) -/
open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions on `Y`, use preservation of K-flatness by pullback,
-- and invoke the universal property of the total left derived functor.
/-- Pullback on homotopy categories admits a total left derived functor. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for module pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) \to D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

section

variable {X Y : RingedSpace.{u}}

-- Proof sketch: represent `E` by an `m`-pseudo-coherent complex on `Y`, pull back the local
-- strictly perfect approximation data along `f`, use Lemma `20.46.4` to preserve strict
-- perfectness and the derived-functor cohomology-vanishing argument from Lemma `13.16.1` to keep
-- the cone acyclic in degrees `≥ m`, and then apply Lemma `20.47.2` to conclude.
/-- Lemma 20.47.3: if an object `E` of `D(\mathcal O_Y)` is `m`-pseudo-coherent, then the
derived pullback `Lf^*E` is `m`-pseudo-coherent. -/
theorem modulePullbackDerived_isMPseudoCoherent
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    (f : X ⟶ Y) [(modulePullback f).Additive]
    (E : DerivedCategory (RingedSpace.Modules Y)) (m : ℤ)
    (hE : IsMPseudoCoherent E m) :
    IsMPseudoCoherent ((modulePullbackDerived f).obj E) m := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_4 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: choose local strictly perfect approximations of `T.obj₁` in degree `m + 1` and
-- of `T.obj₂` in degree `m`, realize the first morphism of the distinguished triangle by an
-- actual map between those local models, and compare the cone triangle with `T` locally. The cone
-- stays strictly perfect, and the long exact cohomology sequence gives the required
-- cohomological bounds for `T.obj₃`, so Lemma `20.47.2` yields `m`-pseudo-coherence.
/-- Lemma 20.47.4 (1): in a distinguished triangle in `D(\mathcal O_X)`, if the first term is
`(m + 1)`-pseudo-coherent and the second term is `m`-pseudo-coherent, then the third term is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₃_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : IsMPseudoCoherent T.obj₁ (m + 1))
    (h₂ : IsMPseudoCoherent T.obj₂ m) :
    IsMPseudoCoherent T.obj₃ m := sorry

-- Proof sketch: rotate the distinguished triangle to put `T.obj₂` in the cone position covered
-- by part `(1)`. The hypotheses on `T.obj₁` and `T.obj₃` become the needed
-- `(m + 1)`-pseudo-coherence and `m`-pseudo-coherence assumptions for the rotated triangle.
/-- Lemma 20.47.4 (2): in a distinguished triangle in `D(\mathcal O_X)`, if the first and third
terms are `m`-pseudo-coherent, then the second term is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₂_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₁ : IsMPseudoCoherent T.obj₁ m)
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₂ m := sorry

-- Proof sketch: rotate the distinguished triangle so that `T.obj₁` becomes the third vertex, and
-- apply part `(1)` to the rotated triangle. The shift in the first hypothesis matches the
-- `(m + 1)`-pseudo-coherence requirement exactly.
/-- Lemma 20.47.4 (3): in a distinguished triangle in `D(\mathcal O_X)`, if the second term is
`(m + 1)`-pseudo-coherent and the third term is `m`-pseudo-coherent, then the first term is
`(m + 1)`-pseudo-coherent. -/
theorem isMPseudoCoherent_obj₁_of_distinguishedTriangle
    {m : ℤ} (T : Triangle DModX) (hT : T ∈ distTriang DModX)
    (h₂ : IsMPseudoCoherent T.obj₂ (m + 1))
    (h₃ : IsMPseudoCoherent T.obj₃ m) :
    IsMPseudoCoherent T.obj₁ (m + 1) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_5 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open TopologicalSpace
open scoped RingedSpaceDerivedTensor

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

/-- The derived tensor product on `D(\mathcal O_X)` with ambient ringed space fixed by the local
context. -/
private abbrev derivedTensorObj (K L : DModX) : DModX :=
  (derivedTensorProduct L).obj K

local notation:70 K:70 " ⊗^L " L:71 => derivedTensorObj K L

-- Proof sketch: work locally on an open neighborhood where `K` and `L` admit strictly perfect
-- approximations in degrees `n` and `m`. Tensor those representatives termwise, use the local
-- vanishing hypotheses to control the Tor spectral sequence, and conclude that the induced map to
-- the restricted derived tensor product is an isomorphism above
-- `max (m + a, n + b)` and an epimorphism in degree `max (m + a, n + b)`.
/-- Lemma 20.47.5 (1): if `K` is `n`-pseudo-coherent with vanishing cohomology sheaves above `a`
and `L` is `m`-pseudo-coherent with vanishing cohomology sheaves above `b`, then the derived
tensor product `K \otimes_{\mathcal O_X}^{\mathbf L} L` is
`max (m + a, n + b)`-pseudo-coherent. -/
theorem derivedTensorProduct_isMPseudoCoherent_of_isMPseudoCoherent_of_vanishingAbove
    (K L : DModX) (n m a b : ℤ)
    (hK : IsMPseudoCoherent K n)
    (hKvanish : ∀ i : ℤ, a < i →
      IsZero ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) i).obj K))
    (hL : IsMPseudoCoherent L m)
    (hLvanish : ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) j).obj L)) :
    IsMPseudoCoherent (K ⊗^L L) (max (m + a) (n + b)) := sorry

-- Proof sketch: pseudo-coherence gives local `m`-pseudo-coherence for every `m`, and locally one
-- first replaces `K` and `L` by bounded-above strictly perfect complexes. Applying part `(1)` to
-- those local bounded-above presentations yields local `m`-pseudo-coherence for every `m` of the
-- derived tensor product, hence pseudo-coherence.
/-- Lemma 20.47.5 (2): the derived tensor product of two pseudo-coherent objects of
`D(\mathcal O_X)` is pseudo-coherent. -/
theorem derivedTensorProduct_isPseudoCoherent_of_isPseudoCoherent
    (K L : DModX)
    (hK : IsPseudoCoherent K)
    (hL : IsPseudoCoherent L) :
    IsPseudoCoherent (K ⊗^L L) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_6 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: use the distinguished triangle from Derived Categories, Lemma `13.4.10` attached
-- to the projection `K ⊞ L ⟶ K`, identify the third term with `L ⊞ L⟦(1 : ℤ)⟧`, and apply
-- Lemma `20.47.4` repeatedly exactly as in the affine case to descend from large shifts back to
-- `K`.
/-- Lemma 20.47.6 (1): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O_X)`, then `K` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_left_of_biprod
    (K L : DModX) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent K m := sorry

-- Proof sketch: apply the previous distinguished-triangle argument after swapping the two
-- biproduct factors, or equivalently use the symmetric triangle attached to the projection
-- `K ⊞ L ⟶ L`.
/-- Lemma 20.47.6 (2): if `K ⊞ L` is `m`-pseudo-coherent in `D(\mathcal O_X)`, then `L` is
`m`-pseudo-coherent. -/
theorem isMPseudoCoherent_right_of_biprod
    (K L : DModX) (m : ℤ)
    (hKL : IsMPseudoCoherent (K ⊞ L) m) :
    IsMPseudoCoherent L m := sorry

-- Proof sketch: pseudo-coherence means `m`-pseudo-coherence for every integer. Apply part `(1)`
-- degreewise to the biproduct and then repackage the resulting family of statements.
/-- Lemma 20.47.6 (3): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O_X)`, then `K` is
pseudo-coherent. -/
theorem isPseudoCoherent_left_of_biprod
    (K L : DModX)
    (hKL : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent K := sorry

-- Proof sketch: as in part `(3)`, pseudo-coherence is checked degreewise; apply part `(2)` for
-- every integer `m` and collect the resulting `m`-pseudo-coherence statements for `L`.
/-- Lemma 20.47.6 (4): if `K ⊞ L` is pseudo-coherent in `D(\mathcal O_X)`, then `L` is
pseudo-coherent. -/
theorem isPseudoCoherent_right_of_biprod
    (K L : DModX)
    (hKL : IsPseudoCoherent (K ⊞ L)) :
    IsPseudoCoherent L := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_7 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "single0" => DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)

/-- A cochain complex of `\mathcal O_X`-modules is locally bounded above if every point has an
open neighborhood on which the restricted complex vanishes in all sufficiently high degrees. -/
def CochainComplex.IsLocallyBoundedAbove (K : CochainComplex (RingedSpace.Modules X) ℤ) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ b : ℤ, ((moduleComplexRestrictionToOpen X U).obj K).IsStrictlyLE b

-- Proof sketch: choose the top open `⊤` as a neighborhood of every point and reuse the same
-- global upper bound after restricting the complex to `⊤`.
/-- A bounded-above complex of `\mathcal O_X`-modules is locally bounded above. -/
theorem cochainComplex_isLocallyBoundedAbove_of_boundedAbove
    (K : CochainComplex (RingedSpace.Modules X) ℤ) (hK : ∃ b : ℤ, K.IsStrictlyLE b) :
    CochainComplex.IsLocallyBoundedAbove K := sorry

-- Proof sketch: for each point, choose an open neighborhood on which `K` is bounded above. Apply
-- the truncation argument of Lemma `15.65.9` to the restricted complex on that neighborhood,
-- using Lemma `20.47.4` for the induction step on stupid truncation triangles. This gives local
-- derived `m`-pseudo-coherence of the restriction, and Lemma `20.47.2` converts the resulting
-- derived statement back to the restricted cochain complex, which is exactly the local data
-- required in Definition `20.47.1`.
/-- Lemma 20.47.7: a locally bounded-above cochain complex of `\mathcal O_X`-modules whose term
in degree `i` is `(m - i)`-pseudo-coherent is `m`-pseudo-coherent. -/
theorem cochainComplex_isMPseudoCoherent_of_locallyBoundedAbove_of_termwise
    (K : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ)
    (hbounded : CochainComplex.IsLocallyBoundedAbove K)
    (hterm : ∀ i : ℤ, IsMPseudoCoherent ((single0).obj (K.X i)) (m - i)) :
    CochainComplex.IsMPseudoCoherent K m := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_8 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open DerivedCategory.TStructure
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "single0" => DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)

/-- A derived `\mathcal O_X`-module is locally bounded above if every point has an open
neighborhood on which its restriction lies in the bounded-above derived category. -/
def IsLocallyBoundedAbove (E : DModX) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    (t.minus : ObjectProperty (DerivedCategory (openSubspaceModuleCategory X U)))
      ((moduleRestrictionToOpenDerived X U).obj E)

-- Proof sketch: unfold `IsLocallyBoundedAbove`; this is exactly the neighborhoodwise bounded-above
-- condition on the derived restrictions to open subspaces.
/-- The local bounded-above condition is exactly bounded-above-ness after restricting to a
neighborhood of each point. -/
theorem isLocallyBoundedAbove_iff (E : DModX) :
    IsLocallyBoundedAbove E ↔
      ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
        (t.minus : ObjectProperty (DerivedCategory (openSubspaceModuleCategory X U)))
          ((moduleRestrictionToOpenDerived X U).obj E) := sorry

-- Proof sketch: work locally near each point. On a neighborhood where `E` becomes bounded above,
-- apply the bounded-above algebraic argument of Lemma `15.65.10` to the restricted object, using
-- the hypotheses on the cohomology sheaves `H^i(E)`. This yields local `m`-pseudo-coherence of
-- the restriction, and Lemma `20.47.2` upgrades the local strictly perfect approximations to
-- `IsMPseudoCoherent E m`.
/-- Lemma 20.47.8: if `E` is locally bounded above and every cohomology sheaf `H^i(E)` is
`(m - i)`-pseudo-coherent, then `E` is `m`-pseudo-coherent. This local formulation covers the
parenthetical bounded-above case as a special case. -/
theorem isMPseudoCoherent_of_locallyBoundedAbove_of_homology
    (E : DModX) (m : ℤ)
    (hbounded : IsLocallyBoundedAbove E)
    (hH :
      ∀ i : ℤ,
        IsMPseudoCoherent
          ((single0).obj ((DerivedCategory.homologyFunctor (RingedSpace.Modules X) i).obj E))
          (m - i)) :
    IsMPseudoCoherent E m := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_9 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The unbounded derived category `D(\mathcal O_X)` of a ringed space. -/
abbrev ModuleDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

/-- The category of `\mathcal O_U`-modules on the open subset `U \subset X`. -/
abbrev OpenSubsetSheafModules (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  SheafOfModules ((TopCat.Sheaf.pullback RingCat.{u} U.inclusion').obj (RingedSpace.ringCatSheaf X))

/-- The derived category `D(\mathcal O_U)` on the open subset `U \subset X`. -/
abbrev OpenSubsetModuleDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :=
  DerivedCategory (OpenSubsetSheafModules X U)

/-- Restriction of `\mathcal O_X`-modules to an open subset. -/
noncomputable abbrev moduleSheafRestrictionToOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ OpenSubsetSheafModules X U :=
  SheafOfModules.pullback
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
      (RingedSpace.ringCatSheaf X))

/-- Restriction to an open subset is additive on module sheaves. -/
instance moduleSheafRestrictionToOpen_additive {X : RingedSpace.{u}} (U : Opens X.carrier) :
    (moduleSheafRestrictionToOpen U).Additive := sorry

/-- Restriction to an open subset preserves finite limits on module sheaves. -/
instance moduleSheafRestrictionToOpen_preservesFiniteLimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteLimits (moduleSheafRestrictionToOpen U) := sorry

/-- Restriction to an open subset preserves finite colimits on module sheaves. -/
instance moduleSheafRestrictionToOpen_preservesFiniteColimits
    {X : RingedSpace.{u}} (U : Opens X.carrier) :
    PreservesFiniteColimits (moduleSheafRestrictionToOpen U) := sorry

/-- Restriction on derived categories to an open subset. -/
noncomputable abbrev moduleDerivedRestrictionToOpen {X : RingedSpace.{u}}
    (U : Opens X.carrier) :
    ModuleDerived X ⥤ OpenSubsetModuleDerived X U :=
  (moduleSheafRestrictionToOpen U).mapDerivedCategory

/-- A complex of modules over a sheaf of rings is strictly perfect if it is bounded and each term
is a retract of a finite free module sheaf. -/
def CochainComplex.IsStrictlyPerfect
    {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (E : CochainComplex (SheafOfModules R) ℤ) : Prop :=
  (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
    ∀ i : ℤ, ∃ I : Type u, Finite I ∧
      Nonempty (Retract (E.X i) (SheafOfModules.free.{u} I : SheafOfModules R))

-- Proof sketch: unfold `CochainComplex.IsStrictlyPerfect`; the right-hand side is exactly the
-- boundedness condition together with the termwise finite-free retract condition.
/-- Unfolding `CochainComplex.IsStrictlyPerfect` yields boundedness together with the requirement
that every term is a retract of a finite free module sheaf. -/
theorem cochainComplex_isStrictlyPerfect_iff
    {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (E : CochainComplex (SheafOfModules R) ℤ) :
    CochainComplex.IsStrictlyPerfect E ↔
      (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
        ∀ i : ℤ, ∃ I : Type u, Finite I ∧
          Nonempty (Retract (E.X i) (SheafOfModules.free.{u} I : SheafOfModules R)) := sorry

/-- The cohomology `\mathcal O_X`-module `H^i(K)` of a derived `\mathcal O_X`-module `K`. -/
abbrev derivedCohomologyModule
    (X : RingedSpace.{u}) (K : ModuleDerived X) (i : ℤ) : Modules X :=
  (DerivedCategory.homologyFunctor (Modules X) i).obj K

-- Proof sketch: unfold `derivedCohomologyModule`; it is defined to be the value of the
-- homology functor in degree `i` on the derived object `K`.
/-- Unfolding `derivedCohomologyModule` identifies it with the degree-`i` homology object of `K`
in `\operatorname{Mod}(\mathcal O_X)`. -/
theorem derivedCohomologyModule_def
    (X : RingedSpace.{u}) (K : ModuleDerived X) (i : ℤ) :
    derivedCohomologyModule X K i =
      (DerivedCategory.homologyFunctor (Modules X) i).obj K := sorry

/-- A neighborhoodwise strict-perfect approximation of a derived `\mathcal O_X`-module at a point
`x`, controlling cohomology above degree `m`. -/
structure MPseudoCoherentNeighborhoodApproximation
    {X : RingedSpace.{u}} (K : ModuleDerived X) (m : ℤ) (x : X) where
  /-- The chosen open neighborhood of `x`. -/
  U : Opens X.carrier
  /-- The chosen open contains `x`. -/
  mem_U : x ∈ U
  /-- The strict-perfect complex on the open neighborhood. -/
  complex : CochainComplex (OpenSubsetSheafModules X U) ℤ
  /-- The comparison map from the strict-perfect model to the restriction of `K` to `U`. -/
  hom :
    ((DerivedCategory.Q :
      CochainComplex (OpenSubsetSheafModules X U) ℤ ⥤
        OpenSubsetModuleDerived X U).obj complex) ⟶
      (moduleDerivedRestrictionToOpen U).obj K
  /-- The local model is strictly perfect. -/
  isStrictlyPerfect : CochainComplex.IsStrictlyPerfect complex
  /-- The comparison is an isomorphism on cohomology in degrees strictly above `m`. -/
  isIso_above :
    ∀ i : ℤ, m < i →
      IsIso ((DerivedCategory.homologyFunctor
        (OpenSubsetSheafModules X U) i).map hom)
  /-- The comparison is surjective on cohomology in degree `m`. -/
  epi_at :
    Epi ((DerivedCategory.homologyFunctor
      (OpenSubsetSheafModules X U) m).map hom)

/-- A derived `\mathcal O_X`-module is `m`-pseudo-coherent if every point admits a neighborhood on
which the restriction is approximated by a strict-perfect complex inducing cohomology
isomorphisms above degree `m` and an epimorphism in degree `m`. -/
def IsMPseudoCoherent {X : RingedSpace.{u}} (K : ModuleDerived X) (m : ℤ) : Prop :=
  ∀ x : X, Nonempty (MPseudoCoherentNeighborhoodApproximation K m x)

-- Proof sketch: unfold `IsMPseudoCoherent`; it is exactly the pointwise existence of the
-- neighborhoodwise strict-perfect approximations packaged above.
/-- The predicate `IsMPseudoCoherent` is the local existence of strict-perfect approximations with
the required cohomological control above degree `m`. -/
theorem isMPseudoCoherent_iff
    {X : RingedSpace.{u}} (K : ModuleDerived X) (m : ℤ) :
    IsMPseudoCoherent K m ↔
      ∀ x : X, Nonempty (MPseudoCoherentNeighborhoodApproximation K m x) := sorry

-- Proof sketch: work Zariski-locally on `X`. On a neighborhood of each point, choose the
-- strict-perfect approximation from `hK`, replace it inductively by one concentrated in degrees
-- at most `m`, and identify the top surviving cohomology as a quotient of the degree-`m` term,
-- which is locally a retract of a finite free module sheaf. Local finite generation then glues.
/-- Lemma 20.47.9 (1): if `K` is `m`-pseudo-coherent and `H^i(K) = 0` for `i > m`, then
`H^m(K)` is a finite type `\mathcal O_X`-module. -/
theorem derivedCohomologyModule_isFiniteType_of_isMPseudoCoherent
    {X : RingedSpace.{u}} {K : ModuleDerived X} {m : ℤ}
    (hK : IsMPseudoCoherent K m)
    (hvanish : ∀ i : ℤ, m < i → IsZero (derivedCohomologyModule X K i)) :
    (derivedCohomologyModule X K m).IsFiniteType := sorry

-- Proof sketch: again work locally and choose a strict-perfect approximation from `hK`. Use the
-- stronger vanishing bound to truncate the local model so that only degrees up to `m + 1`
-- remain, then identify `H^{m+1}(K)` with the cokernel of a morphism between finite free local
-- terms. Such cokernels are locally finitely presented, and the local data glue.
/-- Lemma 20.47.9 (2): if `K` is `m`-pseudo-coherent and `H^i(K) = 0` for `i > m + 1`, then
`H^{m + 1}(K)` is a finitely presented `\mathcal O_X`-module. -/
theorem derivedCohomologyModule_isFinitePresentation_of_isMPseudoCoherent
    {X : RingedSpace.{u}} {K : ModuleDerived X} {m : ℤ}
    (hK : IsMPseudoCoherent K m)
    (hvanish : ∀ i : ℤ, m + 1 < i → IsZero (derivedCohomologyModule X K i)) :
    (derivedCohomologyModule X K (m + 1)).IsFinitePresentation := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_47_10 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "single0" => DerivedCategory.singleFunctor (RingedSpace.Modules X) (0 : ℤ)

-- Proof sketch: for the forward implication, apply Lemma `20.47.9` to the degree-zero derived
-- object `ℱ[0]`, whose higher cohomology sheaves vanish, to identify `H⁰(ℱ[0]) = ℱ` as a finite
-- type module. For the converse, `ℱ[0]` is locally bounded above and its only nonzero cohomology
-- sheaf is `ℱ` in degree `0`, so Lemma `20.47.8` yields `0`-pseudo-coherence.
/-- Lemma 20.47.10 (1): a sheaf of `\mathcal O_X`-modules, viewed in `D(\mathcal O_X)` as a
complex concentrated in degree `0`, is `0`-pseudo-coherent if and only if it is of finite type. -/
theorem ringedSpaceModule_isZeroPseudoCoherent_iff_isFiniteType
    (ℱ : (RingedSpace.Modules X)) :
    IsMPseudoCoherent ((single0).obj ℱ) 0 ↔ ℱ.IsFiniteType := sorry

-- Proof sketch: for the forward implication, apply Lemma `20.47.9` with `m = -1` to `ℱ[0]`; the
-- vanishing of cohomology in degrees `> 0` identifies `H⁰(ℱ[0]) = ℱ` as finitely presented. For
-- the converse, `ℱ[0]` is locally bounded above and its only nonzero homology sheaf is `ℱ` in
-- degree `0`, so Lemma `20.47.8` with `m = -1` gives `(-1)`-pseudo-coherence.
/-- Lemma 20.47.10 (2): a sheaf of `\mathcal O_X`-modules, viewed in `D(\mathcal O_X)` as a
complex concentrated in degree `0`, is `(-1)`-pseudo-coherent if and only if it is of finite
presentation. -/
theorem ringedSpaceModule_isMinusOnePseudoCoherent_iff_isFinitePresentation
    (ℱ : (RingedSpace.Modules X)) :
    IsMPseudoCoherent ((single0).obj ℱ) (-1) ↔ ℱ.IsFinitePresentation := sorry

end AlgebraicGeometry.RingedSpace
