import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_51_1 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Pretriangulated
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

local instance ringedSpaceSheafModulesAbelian : Abelian (RingedSpace.Modules X) :=
  inferInstance

local instance ringedSpaceSheafModulesHasDerivedCategory :
    HasDerivedCategory (RingedSpace.Modules X) :=
  HasDerivedCategory.standard (RingedSpace.Modules X)

variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

/-- The inverse system of derived duals
`\cdots \to K_{n + 1}^\vee \to K_n^\vee` attached to a sequential system
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(\mathcal O_X)`. -/
abbrev ringedSpaceDerivedDualInverseSystem
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    ℕᵒᵖ ⥤ DMod :=
  @Functor.ofOpSequence DMod _ (fun n ↦ (ihom (K n)).obj (𝟙_ DMod))
    (fun n ↦ (MonoidalClosed.pre (f n)).app (𝟙_ DMod))

-- Proof sketch: unfold `ringedSpaceDerivedDualInverseSystem`; `Functor.ofOpSequence` is defined
-- so that evaluation at `op n` returns the `n`-th object of the underlying sequence.
/-- The `n`-th object of the dual inverse system is the derived dual `K_n^\vee`. -/
theorem ringedSpaceDerivedDualInverseSystem_obj
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) (n : ℕ) :
    (ringedSpaceDerivedDualInverseSystem K f).obj (op n) =
      (ihom (K n)).obj (𝟙_ DMod) := sorry

/-- The inverse system
`\cdots \to E \otimes_{\mathcal O_X}^{\mathbf L} K_{n + 1}^\vee
\to E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee`
obtained by tensoring the dual inverse system stagewise with a fixed object `E`. -/
abbrev ringedSpaceDerivedDualTensorInverseSystem
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) :
    ℕᵒᵖ ⥤ DMod :=
  @Functor.ofOpSequence DMod _ (fun n ↦ E ⊗ (ihom (K n)).obj (𝟙_ DMod))
    (fun n ↦ E ◁ (MonoidalClosed.pre (f n)).app (𝟙_ DMod))

-- Proof sketch: unfold `ringedSpaceDerivedDualTensorInverseSystem`; by construction of
-- `Functor.ofOpSequence`, the object at `op n` is exactly the `n`-th tensor-dual stage.
/-- The `n`-th object of the tensor-dual inverse system is
`E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee`. -/
theorem ringedSpaceDerivedDualTensorInverseSystem_obj
    (E : DMod) (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) (n : ℕ) :
    (ringedSpaceDerivedDualTensorInverseSystem E K f).obj (op n) =
      E ⊗ (ihom (K n)).obj (𝟙_ DMod) := sorry

-- Proof sketch: apply Lemma `20.50.5` termwise to identify
-- `E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee` with `R\mathcal H\!\mathit{om}(K_n, E)`.
-- The homotopy-colimit triangle for `Khocolim` then turns, under `R\mathcal H\!\mathit{om}(-, E)`,
-- into the Milnor triangle defining a derived limit of the inverse system of these terms.
/-- Lemma 20.51.1: if `Khocolim` is a homotopy colimit of a sequential system of perfect objects
`K₀ ⟶ K₁ ⟶ K₂ ⟶ ⋯` in `D(\mathcal O_X)`, then for every `E ∈ D(\mathcal O_X)` the derived
internal Hom `R\mathcal H\!\mathit{om}(Khocolim, E)` is a derived limit of the inverse system
`n ↦ E \otimes_{\mathcal O_X}^{\mathbf L} K_n^\vee`, where `K_n^\vee` is the derived dual of
`K_n`. -/
theorem ringedSpaceDerivedInternalHom_isDerivedLimit_of_homotopyColimit
    (K : ℕ → DMod) (f : ∀ n, K n ⟶ K (n + 1)) {Khocolim : DMod}
    [HasColimitsOfShape (Discrete ℕ) DMod]
    (hperfect : ∀ n, DerivedCategory.IsPerfect (K n))
    (g : ∐ K ⟶ Khocolim)
    (δ : Khocolim ⟶ (∐ K)⟦(1 : ℤ)⟧)
    (hKhocolim :
      Triangle.mk (sequentialTelescopeMap (Functor.ofSequence f)) g δ ∈ distTriang DMod)
    (E : DMod) :
    IsDerivedLimit
      (ringedSpaceDerivedDualTensorInverseSystem E K f)
      ((ihom Khocolim).obj E) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_51_2 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [BraidedCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: the top arrow sends a pair of degree-zero classes to their tensor product, the
-- left arrow is the canonical map `H^0(X, K ⊗ E^\vee) → Hom(E, K)` from Lemma `20.50.5`, and the
-- right arrow evaluates against `ε : E^\vee ⊗ E → \mathcal O_X`. Unwinding the definitions, both
-- composites send `(ξ, η)` to `(1_K ⊗ ε) ∘ (ξ ⊗ η)`, with the bottom route factoring this through
-- the morphism `E ⟶ K` associated to `ξ`.
/-- Lemma 20.51.2: for a ringed space `(X, \mathcal O_X)`, objects `K, E ∈ D(\mathcal O_X)`, and
`E` perfect, the square comparing the cup product
`H^0(X, K \otimes_{\mathcal O_X}^{\mathbf L} E^\vee) × H^0(X, E) →
H^0(X, K \otimes_{\mathcal O_X}^{\mathbf L} E^\vee \otimes_{\mathcal O_X}^{\mathbf L} E)` with
the identification
`H^0(X, K \otimes_{\mathcal O_X}^{\mathbf L} E^\vee) → \operatorname{Hom}_{D(\mathcal O_X)}(E, K)`
from Lemma `20.50.5` and the evaluation map
`ε : E^\vee \otimes_{\mathcal O_X}^{\mathbf L} E → \mathcal O_X` from Example `20.50.7`
commutes. In Lean, `H^0(X, M)` is modeled by morphisms `𝟙_ D(\mathcal O_X) ⟶ M`. -/
theorem ringedSpaceDerivedCupProduct_evaluation_commSq
    {K E : DMod} (hE : DerivedCategory.IsPerfect E) :
    let A := (𝟙_ DMod ⟶ K ⊗ ringedSpaceDerivedDual E) × (𝟙_ DMod ⟶ E)
    let B := 𝟙_ DMod ⟶ (K ⊗ ringedSpaceDerivedDual E) ⊗ E
    let C := (E ⟶ K) × (𝟙_ DMod ⟶ E)
    let D := 𝟙_ DMod ⟶ K
    let top : A ⟶ B := fun p ↦ (λ_ (𝟙_ DMod)).inv ≫ (p.1 ⊗ₘ p.2)
    let left : A ⟶ C := fun p ↦ (ringedSpaceDerivedEvaluationH0ToHom E K p.1, p.2)
    let right : B ⟶ D := fun s ↦
      s ≫ (α_ K (ringedSpaceDerivedDual E) E).hom ≫
        (K ◁ ringedSpaceDerivedDualEvaluation E) ≫
        (ρ_ K).hom
    let bot : C ⟶ D := fun p ↦ p.2 ≫ p.1
    CommSq top left right bot := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_51_3 (from Chap20) -/
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

/-! ### Lemma_20_51_4 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable (x : X)

variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (Modules (pointRingedSpace x))]
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (Modules (pointRingedSpace x)))]
variable [MonoidalClosed (DerivedCategory (Modules (pointRingedSpace x)))]
variable [(modulePullback (pointInclusion x)).Additive]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

/-- The canonical pullback-to-internal-Hom comparison for the point inclusion
`i_x : ({x}, \mathcal O_{X, x}) ⟶ X`. This is the point-ringed-space avatar of the stalk map
`R\mathcal H\!\mathit{om}(K, M)_x \to R\mathrm{Hom}_{\mathcal O_{X, x}}(K_x, M_x)`. -/
noncomputable def stalkDerivedInternalHomComparison
    (K M : DModX) :
    (modulePullbackDerived (pointInclusion x)).obj ((ihom K).obj M) ⟶
      (ihom ((modulePullbackDerived (pointInclusion x)).obj K)).obj
        ((modulePullbackDerived (pointInclusion x)).obj M) :=
  pullbackDerivedInternalHomComparison (pointInclusion x) K M

-- Proof sketch: apply Lemma `20.51.3 (1)` to the point inclusion
-- `i_x : ({x}, \mathcal O_{X, x}) ⟶ X`. The resulting pullback comparison is exactly the
-- point-ringed-space form of the canonical stalk map
-- `R\mathcal H\!\mathit{om}(K, M)_x \to R\mathrm{Hom}_{\mathcal O_{X, x}}(K_x, M_x)`.
/-- Lemma 20.51.4 (1): if `K` is perfect, then the canonical map from the stalk of
`R\mathcal H\!\mathit{om}(K, M)` at `x` to the derived internal Hom over the stalk ring
`\mathcal O_{X, x}` is an isomorphism. -/
theorem stalkDerivedInternalHomComparison_isIso_of_isPerfect
    (K M : DModX) (hK : DerivedCategory.IsPerfect K) :
    IsIso (stalkDerivedInternalHomComparison x K M) := sorry

-- Proof sketch: the point inclusion `i_x : ({x}, \mathcal O_{X, x}) ⟶ X` is flat on stalks, so
-- Lemma `20.51.3 (2)` applies. Its pullback comparison is the point-ringed-space expression of
-- the canonical stalk map
-- `R\mathcal H\!\mathit{om}(K, M)_x \to R\mathrm{Hom}_{\mathcal O_{X, x}}(K_x, M_x)`.
/-- Lemma 20.51.4 (2): if `K` is pseudo-coherent and `M` is locally bounded below, then the
canonical map from the stalk of `R\mathcal H\!\mathit{om}(K, M)` at `x` to the derived internal
Hom over the stalk ring `\mathcal O_{X, x}` is an isomorphism. -/
theorem stalkDerivedInternalHomComparison_isIso_of_isPseudoCoherent_of_locallyBoundedBelow
    (K M : DModX) (hK : DerivedCategory.IsPseudoCoherent K)
    (hM : IsLocallyBoundedBelow M) :
    IsIso (stalkDerivedInternalHomComparison x K M) := sorry

end

end AlgebraicGeometry.RingedSpace
