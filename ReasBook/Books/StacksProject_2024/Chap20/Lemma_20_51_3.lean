import Mathlib
import StacksProject_2024.Chap15.Definition_15_67_1
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- The morphism `f` has finite tor dimension at `x` when the local ring
`\mathcal O_{X, x}` has finite tor dimension as a module over
`\mathcal O_{Y, f(x)}`. -/
def MorphismFiniteTorDimensionAt (f : X ⟶ Y) (x : X) : Prop :=
  let _ : Algebra ↑(Y.presheaf.stalk (f.hom.base x)) ↑(X.presheaf.stalk x) :=
    (f.hom.stalkMap x).hom.toAlgebra
  ModuleHasFiniteTorDimension
    (ModuleCat.of ↑(Y.presheaf.stalk (f.hom.base x)) ↑(X.presheaf.stalk x))

-- Proof sketch: unfold `MorphismFiniteTorDimensionAt`; it is exactly the finite tor-dimension
-- condition for the stalk module over the induced local ring map at `x`.
/-- Unfolding `MorphismFiniteTorDimensionAt` gives finite tor dimension for the stalk module over
the induced local ring map. -/
theorem morphismFiniteTorDimensionAt_iff (f : X ⟶ Y) (x : X) :
    MorphismFiniteTorDimensionAt f x ↔
      let _ : Algebra ↑(Y.presheaf.stalk (f.hom.base x)) ↑(X.presheaf.stalk x) :=
        (f.hom.stalkMap x).hom.toAlgebra
      ModuleHasFiniteTorDimension
        (ModuleCat.of ↑(Y.presheaf.stalk (f.hom.base x)) ↑(X.presheaf.stalk x)) := sorry

/-- A morphism of ringed spaces has finite tor dimension when it has finite tor dimension at every
point of the source. -/
def MorphismHasFiniteTorDimension (f : X ⟶ Y) : Prop :=
  ∀ x : X, MorphismFiniteTorDimensionAt f x

-- Proof sketch: unfold `MorphismHasFiniteTorDimension`; it is the universal pointwise finite
-- tor-dimension condition on the stalk maps of `f`.
/-- A morphism has finite tor dimension exactly when all of its stalk maps do. -/
theorem morphismHasFiniteTorDimension_iff (f : X ⟶ Y) :
    MorphismHasFiniteTorDimension f ↔ ∀ x : X, MorphismFiniteTorDimensionAt f x := sorry

/-- The structure-sheaf morphism `\mathcal O_Y \to f_*\mathcal O_X` attached to a morphism of
ringed spaces. -/
noncomputable abbrev commRingSheafPushforwardMap (f : X ⟶ Y) :
    Y.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} f.hom.base).obj X.sheaf :=
  ⟨f.hom.c⟩

/-- The structure-sheaf morphism of a ringed-space morphism after forgetting commutativity. -/
noncomputable abbrev pushforwardStructureSheafHom (f : X ⟶ Y) :
    (RingedSpace.ringCatSheaf Y) ⟶
      (TopCat.Sheaf.pushforward RingCat.{u} f.hom.base).obj (RingedSpace.ringCatSheaf X) :=
  (sheafCompose (Opens.grothendieckTopology Y) (forget₂ CommRingCat RingCat.{u})).map
    (commRingSheafPushforwardMap f)

/-- The pullback functor on `\mathcal O_Y`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePullback (f : X ⟶ Y) :
    (RingedSpace.Modules Y) ⥤ (RingedSpace.Modules X) :=
  SheafOfModules.pullback (pushforwardStructureSheafHom f)

/-- The quasi-isomorphisms in the homotopy category of complexes of `\mathcal O_X`-modules. -/
abbrev ModuleQis (X : RingedSpace.{u}) :=
  HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category functor used to define the total left derived pullback. -/
abbrev modulePullbackToDerived (f : X ⟶ Y) [(modulePullback f).Additive] :
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

-- Proof sketch: choose K-flat resolutions on `Y`, use preservation of K-flatness by pullback, and
-- invoke the universal property of the total left derived functor.
/-- Pullback on homotopy categories admits a total left derived functor. -/
theorem modulePullbackToDerived_hasLeftDerivedFunctor
    (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) := sorry

/-- The canonical left-derived-functor instance for module pullback. -/
instance instHasLeftDerivedFunctorModulePullbackToDerived
    (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y) :=
  modulePullbackToDerived_hasLeftDerivedFunctor f

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) \to D(\mathcal O_X)`. -/
abbrev modulePullbackDerived
    (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive] :
    DerivedCategory (RingedSpace.Modules Y) ⥤ DerivedCategory (RingedSpace.Modules X) :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DerivedCategory (RingedSpace.Modules Y))
    (ModuleQis Y)

/-- Restriction of `\mathcal O_X`-modules to an open subspace is additive. -/
instance moduleRestrictionToOpen_additive (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (moduleRestrictionToOpen X U).Additive := sorry

-- Proof sketch: exactness of restriction is checked stalkwise, where restriction along an open
-- embedding is exact on sheaves of modules. Translating this exactness to the abstract exact-functor
-- predicate yields the result.
/-- Restriction of `\mathcal O_X`-modules to an open subspace is exact. -/
theorem moduleRestrictionToOpen_exact (X : RingedSpace.{u}) (U : Opens X.carrier) :
    exactFunctor (RingedSpace.Modules X) (openSubspaceModuleCategory X U)
      (moduleRestrictionToOpen X U) := sorry

/-- The exact-functor package attached to restriction of `\mathcal O_X`-modules to an open
subspace. -/
abbrev moduleRestrictionToOpenExactFunctor (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (RingedSpace.Modules X) ⥤ₑ openSubspaceModuleCategory X U :=
  let _ : PreservesFiniteLimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact X U)).1
  let _ : PreservesFiniteColimits (moduleRestrictionToOpen X U) :=
    ((CategoryTheory.exactFunctor_iff (moduleRestrictionToOpen X U)).mp
      (moduleRestrictionToOpen_exact X U)).2
  ExactFunctor.of (moduleRestrictionToOpen X U)

/-- Restriction on derived categories induced by exact restriction of modules to an open
subspace. -/
abbrev moduleRestrictionToOpenDerived (X : RingedSpace.{u}) (U : Opens X.carrier) :
    DerivedCategory (RingedSpace.Modules X) ⥤ DerivedCategory (openSubspaceModuleCategory X U) :=
  let _ : (moduleRestrictionToOpenExactFunctor X U).obj.Additive :=
    moduleRestrictionToOpen_additive X U
  (moduleRestrictionToOpenExactFunctor X U).obj.mapDerivedCategory

/-- A complex of `\mathcal O_X`-modules is `m`-pseudo-coherent if there is an open covering of
`X` on which its restrictions admit strictly perfect approximations inducing cohomology
isomorphisms above degree `m` and an epimorphism in degree `m`. -/
def CochainComplex.IsMPseudoCoherent (E : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    iSup U = ⊤ ∧
      ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
        ∃ α : Ei ⟶ (moduleComplexRestrictionToOpen X (U i)).obj E,
          CochainComplex.IsStrictlyPerfect Ei ∧
            (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
              Epi (HomologicalComplex.homologyMap α m)

-- Proof sketch: unfold `CochainComplex.IsMPseudoCoherent`; the right-hand side is exactly the
-- local strictly-perfect approximation condition on an open covering.
/-- Unfolding `CochainComplex.IsMPseudoCoherent` gives the local strictly-perfect approximation
criterion on an open covering. -/
theorem cochainComplex_isMPseudoCoherent_iff
    (E : CochainComplex (RingedSpace.Modules X) ℤ) (m : ℤ) :
    CochainComplex.IsMPseudoCoherent E m ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        iSup U = ⊤ ∧
          ∀ i : ι, ∃ Ei : CochainComplex (openSubspaceModuleCategory X (U i)) ℤ,
            ∃ α : Ei ⟶ (moduleComplexRestrictionToOpen X (U i)).obj E,
              CochainComplex.IsStrictlyPerfect Ei ∧
                (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
                  Epi (HomologicalComplex.homologyMap α m) := sorry

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
      ∀ m : ℤ, CochainComplex.IsMPseudoCoherent E m := sorry

namespace DerivedCategory

/-- An object of `D(\mathcal O_X)` is pseudo-coherent if it is represented by a pseudo-coherent
complex of `\mathcal O_X`-modules. -/
def IsPseudoCoherent (E : DerivedCategory (RingedSpace.Modules X)) : Prop :=
  ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
    ∃ _ : E ≅
        ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
          DerivedCategory (RingedSpace.Modules X)).obj K),
      CochainComplex.IsPseudoCoherent K

-- Proof sketch: unfold `DerivedCategory.IsPseudoCoherent`; this is exactly the existence of one
-- pseudo-coherent complex representing the derived object.
/-- An object of `D(\mathcal O_X)` is pseudo-coherent exactly when it has a pseudo-coherent
representative complex. -/
theorem isPseudoCoherent_iff
    (E : DerivedCategory (RingedSpace.Modules X)) :
    DerivedCategory.IsPseudoCoherent E ↔
      ∃ K : CochainComplex (RingedSpace.Modules X) ℤ,
        ∃ _ : E ≅
            ((DerivedCategory.Q : CochainComplex (RingedSpace.Modules X) ℤ ⥤
              DerivedCategory (RingedSpace.Modules X)).obj K),
          CochainComplex.IsPseudoCoherent K := sorry

end DerivedCategory

/-- A derived `\mathcal O_X`-module is locally bounded below when every point has an open
neighborhood on which its restriction lies in the bounded-below derived category. -/
abbrev IsLocallyBoundedBelow (E : DerivedCategory (RingedSpace.Modules X)) : Prop :=
  ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
    ∃ n : ℤ, ((moduleRestrictionToOpenDerived X U).obj E).IsGE n

-- Proof sketch: unfold `IsLocallyBoundedBelow`; this is exactly the requirement that after
-- restricting to a neighborhood of each point, the object acquires some lower cohomological bound.
/-- The local bounded-below condition is exactly bounded-below-ness after restricting to a
neighborhood of each point. -/
theorem isLocallyBoundedBelow_iff (E : DerivedCategory (RingedSpace.Modules X)) :
    IsLocallyBoundedBelow E ↔
      ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
        ∃ n : ℤ, ((moduleRestrictionToOpenDerived X U).obj E).IsGE n := sorry

section

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules Y))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules Y))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules Y))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModY" => DerivedCategory (RingedSpace.Modules Y)

/-- The tensor-internal-Hom adjunction on `D(\mathcal O_X)`, written in the Stacks Project order
`A ⊗ B`. -/
private abbrev ringedSpaceDerivedInternalHomAdjunction
    {Z : RingedSpace.{u}}
    [MonoidalCategory (DerivedCategory (RingedSpace.Modules Z))]
    [BraidedCategory (DerivedCategory (RingedSpace.Modules Z))]
    [MonoidalClosed (DerivedCategory (RingedSpace.Modules Z))]
    (A B C : DerivedCategory (RingedSpace.Modules Z)) :
    (A ⟶ (ihom B).obj C) ≃ (A ⊗ B ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    ((β_ A B).symm.homCongr (Iso.refl C))

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} K \to L`
in `D(\mathcal O_X)`. -/
private abbrev ringedSpaceDerivedInternalHomEvaluation
    {Z : RingedSpace.{u}}
    [MonoidalCategory (DerivedCategory (RingedSpace.Modules Z))]
    [BraidedCategory (DerivedCategory (RingedSpace.Modules Z))]
    [MonoidalClosed (DerivedCategory (RingedSpace.Modules Z))]
    (K L : DerivedCategory (RingedSpace.Modules Z)) :
    (ihom K).obj L ⊗ K ⟶ L :=
  ringedSpaceDerivedInternalHomAdjunction ((ihom K).obj L) K L (𝟙 ((ihom K).obj L))

variable (f : X ⟶ Y) [(modulePullback f).Additive]
variable
  (pullbackTensorIso :
    ∀ (A B : DModY),
      (modulePullbackDerived f).obj (A ⊗ B) ≅
        ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))

  /-- The canonical pullback-to-derived-internal-Hom comparison morphism attached to a morphism of
ringed spaces and a chosen pullback-tensor comparison isomorphism. -/
noncomputable def pullbackDerivedInternalHomComparison
    (K L : DModY) :
    (modulePullbackDerived f).obj ((ihom K).obj L) ⟶
      (ihom ((modulePullbackDerived f).obj K)).obj ((modulePullbackDerived f).obj L) :=
  (ringedSpaceDerivedInternalHomAdjunction
      ((modulePullbackDerived f).obj ((ihom K).obj L))
      ((modulePullbackDerived f).obj K)
      ((modulePullbackDerived f).obj L)).symm
    ((pullbackTensorIso ((ihom K).obj L) K).inv ≫
      (modulePullbackDerived f).map (ringedSpaceDerivedInternalHomEvaluation K L))

-- Proof sketch: unfold `pullbackDerivedInternalHomComparison`; by definition it is the inverse
-- image of the pulled-back evaluation morphism under the target-side tensor-internal-Hom
-- adjunction, after transporting along the pullback-tensor comparison
-- `Lh^*(R\mathcal H\!\mathit{om}(K, L) ⊗^{\mathbf L} K) ≅
--   Lh^*R\mathcal H\!\mathit{om}(K, L) ⊗^{\mathbf L} Lh^*K`.
/-- Applying the tensor-internal-Hom adjunction to the pullback comparison recovers the pullback
of the evaluation morphism after transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (K L : DModY) :
    ringedSpaceDerivedInternalHomAdjunction
        ((modulePullbackDerived f).obj ((ihom K).obj L))
        ((modulePullbackDerived f).obj K)
        ((modulePullbackDerived f).obj L)
        (pullbackDerivedInternalHomComparison f pullbackTensorIso K L) =
      (pullbackTensorIso ((ihom K).obj L) K).inv ≫
        (modulePullbackDerived f).map (ringedSpaceDerivedInternalHomEvaluation K L) := sorry

-- Proof sketch: this is the first case of the Stacks Project proof. Replace `K` locally by a
-- strictly perfect complex, compute derived internal Hom by the explicit internal-Hom complex,
-- pull everything back termwise, and identify the pulled-back internal-Hom complex with the
-- internal Hom of the pulled-back representatives.
/-- Lemma 20.51.3 (1): for a morphism of ringed spaces `h : X ⟶ Y`, if `K` is a perfect object of
`D(\mathcal O_Y)`, then the canonical map
`Lh^* R\mathcal H\!\mathit{om}(K, M) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* M)` from Remark `20.42.13` is an isomorphism. -/
theorem pullbackDerivedInternalHomComparison_isIso_of_isPerfect
    (K M : DModY) (hK : DerivedCategory.IsPerfect K) :
    IsIso
      (show (modulePullbackDerived f).obj ((ihom K).obj M) ⟶
          (ihom ((modulePullbackDerived f).obj K)).obj ((modulePullbackDerived f).obj M) from
        pullbackDerivedInternalHomComparison f pullbackTensorIso K M) := sorry

-- Proof sketch: use flatness of `h` to compute `Lh^*` by ordinary pullback, then truncate the
-- pseudo-coherent source `K` high enough relative to the lower bound on `M`. The truncated source
-- is locally strictly perfect, so part `(1)` applies and gives the comparison isomorphism on all
-- sufficiently low cohomology; varying the truncation yields an isomorphism everywhere.
/-- Lemma 20.51.3 (2): for a flat morphism of ringed spaces `h : X ⟶ Y`, if `K` is
pseudo-coherent and `M` is locally bounded below, then the canonical map
`Lh^* R\mathcal H\!\mathit{om}(K, M) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* M)` from Remark `20.42.13` is an isomorphism. -/
theorem pullbackDerivedInternalHomComparison_isIso_of_isFlat_of_isPseudoCoherent_of_locallyBoundedBelow
    (hf : ∀ x : X, (f.hom.stalkMap x).hom.Flat) (K M : DModY)
    (hK : DerivedCategory.IsPseudoCoherent K)
    (hM : IsLocallyBoundedBelow M) :
    IsIso
      (show (modulePullbackDerived f).obj ((ihom K).obj M) ⟶
          (ihom ((modulePullbackDerived f).obj K)).obj ((modulePullbackDerived f).obj M) from
        pullbackDerivedInternalHomComparison f pullbackTensorIso K M) := sorry

-- Proof sketch: argue as in part `(2)`, but replace flatness by the finite-tor-dimension bound on
-- the stalk maps of `h`, which gives bounded cohomological amplitude for `Lh^*` on bounded-below
-- objects. After truncating `K`, reduce again to the perfect case `(1)`.
/-- Lemma 20.51.3 (3): for a morphism of ringed spaces `h : X ⟶ Y`, if `\mathcal O_X` has finite
tor dimension over `h^{-1}\mathcal O_Y`, `K` is pseudo-coherent, and `M` is locally bounded
below, then the canonical map
`Lh^* R\mathcal H\!\mathit{om}(K, M) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* M)` from Remark `20.42.13` is an isomorphism. -/
theorem pullbackDerivedInternalHomComparison_isIso_of_isFiniteTorDimension_of_isPseudoCoherent_of_locallyBoundedBelow
    (hf : MorphismHasFiniteTorDimension f) (K M : DModY)
    (hK : DerivedCategory.IsPseudoCoherent K)
    (hM : IsLocallyBoundedBelow M) :
    IsIso
      (show (modulePullbackDerived f).obj ((ihom K).obj M) ⟶
          (ihom ((modulePullbackDerived f).obj K)).obj ((modulePullbackDerived f).obj M) from
        pullbackDerivedInternalHomComparison f pullbackTensorIso K M) := sorry

end

end AlgebraicGeometry.RingedSpace
