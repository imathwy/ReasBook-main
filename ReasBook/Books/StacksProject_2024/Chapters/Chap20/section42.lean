import Mathlib
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_42_1 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (openSubspaceModuleCategory X U))]
variable [MonoidalClosed (DerivedCategory (openSubspaceModuleCategory X U))]

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)
local notation "DModU" => DerivedCategory (openSubspaceModuleCategory X U)

-- Proof sketch: first rewrite `H^0(U, R\mathcal H\!\mathit{om}(L, M))` as the degree-zero
-- hypercohomology of the restricted derived internal Hom on the open subspace via
-- `openHypercohomology_isomorphic_restricted`. Then identify the restriction of
-- `R\mathcal H\!\mathit{om}(L, M)` with `R\mathcal H\!\mathit{om}(L|_U, M|_U)` using
-- Lemma `20.42.3`, and finally compute degree-zero hypercohomology of the internal-Hom object on
-- `U` by Lemma `20.41.6`, which gives morphisms in `D(\mathcal O_U)`.
/-- Lemma 20.42.1: for a ringed space `(X, \mathcal O_X)`, an open subset `U ⊆ X`, and objects
`L, M ∈ D(\mathcal O_X)`, the degree-zero hypercohomology group
`H^0(U, R\mathcal H\!\mathit{om}(L, M))` is canonically identified with the morphism group
`\operatorname{Hom}_{D(\mathcal O_U)}(L|_U, M|_U)`. Specializing to `U = X` yields the global
identification `H^0(X, R\mathcal H\!\mathit{om}(L, M)) =
\operatorname{Hom}_{D(\mathcal O_X)}(L, M)`. -/
theorem open_zeroHypercohomology_internalHom_addEquiv_restrictedDerivedHom
    (L M : DModX) :
    Nonempty
      (((moduleOpenHypercohomology X U ((ihom L).obj M) (0 : ℤ)) : Type u) ≃+
        (((moduleRestrictionToOpenDerived X U).obj L : DModU) ⟶
          ((moduleRestrictionToOpenDerived X U).obj M : DModU))) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_2 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev RingedSpaceDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Tensoring on the left by `K ⊗ L` is naturally isomorphic to first tensoring on the left by
`K` and then by `L`, using the braiding to put the tensor factors in the Stacks Project order. -/
noncomputable abbrev ringedSpaceDerivedTensorLeftTensorIso
    (K L : RingedSpaceDerived X) :
    tensorLeft (K ⊗ L) ≅ tensorLeft K ⋙ tensorLeft L :=
  ((MonoidalCategory.tensoringLeft (RingedSpaceDerived X)).mapIso (β_ K L)) ≪≫
    MonoidalCategory.tensorLeftTensor L K

/-- The functorial tensor-internal-Hom currying isomorphism on `D(\mathcal O_X)`. -/
noncomputable def ringedSpaceDerivedInternalHomTensorNatIso
    (K L : RingedSpaceDerived X) :
    ihom L ⋙ ihom K ≅ ihom (K ⊗ L) :=
  (Adjunction.rightAdjointUniq
      (ihom.adjunction (K ⊗ L))
      (((ihom.adjunction K).comp (ihom.adjunction L)).ofNatIsoLeft
        (ringedSpaceDerivedTensorLeftTensorIso K L).symm)).symm

/-- Lemma 20.42.2: for a ringed space `(X, \mathcal O_X)` and objects
`K, L, M ∈ D(\mathcal O_X)`, there is a canonical isomorphism
`R\mathcal H\!\mathit{om}(K, R\mathcal H\!\mathit{om}(L, M)) \cong
R\mathcal H\!\mathit{om}(K \otimes_{\mathcal O_X}^{\mathbf L} L, M)`,
functorial in `K`, `L`, and `M`. Taking `H^0(X, -)` recovers `20.42.0.1`. -/
noncomputable def ringedSpaceDerivedInternalHomTensorIso
    (K L M : RingedSpaceDerived X) :
    (ihom K).obj ((ihom L).obj M) ≅ (ihom (K ⊗ L)).obj M :=
  (ringedSpaceDerivedInternalHomTensorNatIso K L).app M

-- Proof sketch: both sides are definitionally the component at `M` of the functorial
-- isomorphism `ringedSpaceDerivedInternalHomTensorNatIso K L`.
/-- The textbook isomorphism is the component at `M` of the functorial currying isomorphism. -/
theorem ringedSpaceDerivedInternalHomTensorIso_eq_app
    (K L M : RingedSpaceDerived X) :
    ringedSpaceDerivedInternalHomTensorIso K L M =
      (ringedSpaceDerivedInternalHomTensorNatIso K L).app M := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_3 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalClosed (DerivedCategory (RingedSpace.Modules X))]
variable [MonoidalCategory (DerivedCategory (openSubspaceModuleCategory X U))]
variable [MonoidalClosed (DerivedCategory (openSubspaceModuleCategory X U))]

-- Proof sketch: represent `K` by a K-injective complex `I`. By Lemma `20.32.1`, the restricted
-- complex `I|_U` is again K-injective, so both derived internal-Hom objects are computed by the
-- underived internal-Hom complexes of `I|_U` and the restriction of a representative of `L`.
-- The ordinary internal-Hom construction commutes with restriction to opens, giving the required
-- identification in the derived category on `U`.
/-- Lemma 20.42.3: for a ringed space `(X, \mathcal O_X)`, an open subset `U \subset X`, and
objects `K, L` of `D(\mathcal O_X)`, restricting `R\mathcal H\!\mathit{om}(K, L)` to `U` is
canonically isomorphic to the derived internal Hom of the restricted objects
`K|_U` and `L|_U`. -/
theorem ringedSpaceDerivedInternalHom_restrict_isomorphic
    (K L : DerivedCategory (RingedSpace.Modules X)) :
    IsIsomorphic
      ((moduleRestrictionToOpenDerived X U).obj ((ihom K).obj L))
      ((ihom ((moduleRestrictionToOpenDerived X U).obj K)).obj
        ((moduleRestrictionToOpenDerived X U).obj L)) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_4 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.Pretriangulated.Opposite
open Opposite

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.42.4:
- primary domain: triangulatedness of derived internal-Hom functors on `D(\mathcal O_X)`;
- sampled owner declarations:
  `(RingedSpace.Modules AlgebraicGeometry.RingedSpace)`,
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct`,
  `AlgebraicGeometry.RingedSpace.derivedTensorProduct_isTriangulated`,
  `CategoryTheory.ihom`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.Adjunction.isTriangulated_rightAdjoint`;
- best owner abstraction:
  `ihom K` for the second-variable functor `R\mathcal H\!\mathit{om}(K,-)`, whose left adjoint is
  the chapter owner `derivedTensorProduct K = tensorLeft K`, and
  `MonoidalClosed.internalHom.flip.obj L` for the first-variable contravariant functor
  `R\mathcal H\!\mathit{om}(-,L)`;
- primitive data:
  a ringed space `X`, the owner category `DerivedCategory (RingedSpace.Modules X)`, and a fixed object of
  that category;
- derived API:
  the exactness of `tensorLeft K` from `derivedTensorProduct_isTriangulated`, the induced
  `Functor.CommShift` on `ihom K`, and the resulting `Functor.IsTriangulated` statements.

Source/core/bridge triage:
- `source-facing`: Lemma 20.42.4, asserting exactness of derived internal Hom in each variable;
- `core/canonical`: `derivedTensorProduct`, `ihom`, `MonoidalClosed.internalHom`, and
  `Adjunction.isTriangulated_rightAdjoint`;
- `bridge/view`: the specialization from the canonical owner category `DerivedCategory
  (RingedSpace.Modules X)` to the ringed-space language of the lemma.
-/

section

variable {X : RingedSpace.{u}}
local notation "ModX" => (RingedSpace.Modules X)
local notation "DModX" => DerivedCategory ModX

local instance : Abelian ModX := inferInstance

-- Proof sketch: `ihom K` is the right adjoint of `tensorLeft K`, and on `D(\mathcal O_X)` the
-- left adjoint is exactly the chapter owner `derivedTensorProduct K`. Definition `20.26.14`
-- gives that this left adjoint is triangulated, so the canonical adjunction theorem
-- `Adjunction.isTriangulated_rightAdjoint` yields exactness of `R\mathcal H\!\mathit{om}(K,-)`.
/-- Lemma 20.42.4 (1): for a ringed space `(X, \mathcal O_X)` and a fixed object
`K ∈ D(\mathcal O_X)`, the functor `R\mathcal H\!\mathit{om}(K, -)` sends distinguished triangles
in `D(\mathcal O_X)` to distinguished triangles. -/
theorem ringedSpaceDerivedInternalHom_isTriangulated_in_second_variable
    (K : DModX)
    [CategoryWithHomology ModX] [HasCountableCoproducts ModX]
    [MonoidalCategory ModX] [MonoidalPreadditive ModX] [HasColimits ModX]
    [(curriedTensor ModX).Additive]
    [∀ F : ModX, ((curriedTensor ModX).obj F).Additive]
    [∀ (F G : CochainComplex ModX ℤ), CochainComplex.HasMapBifunctor F G (curriedTensor ModX)]
    [MonoidalCategory DModX] [MonoidalClosed DModX]
    [HasZeroObject DModX] [Preadditive DModX]
    [HasShift DModX ℤ] [∀ n : ℤ, (shiftFunctor DModX n).Additive]
    [Pretriangulated DModX] [Functor.CommShift (ihom K) ℤ] :
    (ihom K).IsTriangulated := sorry

-- Proof sketch: the contravariant owner `MonoidalClosed.internalHom.flip.obj L` becomes
-- `ihom (op L)` after passing to the opposite category. Part (1) applied on `D(\mathcal O_X)ᵒᵖ`
-- shows that this opposite functor is triangulated, and `Functor.isTriangulated_of_op` transports
-- the result back to the contravariant source-variable functor.
/-- Lemma 20.42.4 (2): for a ringed space `(X, \mathcal O_X)` and a fixed object
`L ∈ D(\mathcal O_X)`, the contravariant functor `R\mathcal H\!\mathit{om}(-, L)` from
`D(\mathcal O_X)ᵒᵖ` to `D(\mathcal O_X)` sends distinguished triangles to distinguished
triangles. -/
theorem ringedSpaceDerivedInternalHom_isTriangulated_in_first_variable
    (L : DModX)
    [CategoryWithHomology ModX] [HasCountableCoproducts ModX]
    [MonoidalCategory ModX] [MonoidalPreadditive ModX] [HasColimits ModX]
    [(curriedTensor ModX).Additive]
    [∀ F : ModX, ((curriedTensor ModX).obj F).Additive]
    [∀ (F G : CochainComplex ModX ℤ), CochainComplex.HasMapBifunctor F G (curriedTensor ModX)]
    [MonoidalCategory DModX] [MonoidalClosed DModX]
    [HasZeroObject DModX] [Preadditive DModX]
    [HasShift DModX ℤ] [∀ n : ℤ, (shiftFunctor DModX n).Additive]
    [Pretriangulated DModX]
    [Functor.CommShift (MonoidalClosed.internalHom.flip.obj L) ℤ] :
    (MonoidalClosed.internalHom.flip.obj L).IsTriangulated := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_5 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.42.5:
- primary domain: internal-Hom composition in a braided monoidal closed derived category of
  `\mathcal O_X`-modules;
- inspected owner declarations:
  `AlgebraicGeometry.RingedSpace.RingedSpaceDerived`,
  `CategoryTheory.ihom`,
  `CategoryTheory.MonoidalClosed.comp`,
  `CategoryTheory.ihom.ev`,
  `CategoryTheory.MonoidalClosed.curry`;
- best owner abstraction: the closed-monoidal composition morphism `comp K L M` on the ambient
  owner `RingedSpaceDerived X`, together with the standard internal-Hom notation `K ⟹ L`;
- primitive data: the braided monoidal closed structure on `RingedSpaceDerived X` and the three
  objects `K`, `L`, `M`;
- derived API: the Stacks-ordered comparison map obtained by braiding the two internal-Hom factors
  into the order expected by `comp K L M`.

Source/core/bridge triage:
- `source-facing`: the chapter-level morphism
  `R\mathcal H\!\mathit{om}(L, M) \otimes^{\mathbf L} R\mathcal H\!\mathit{om}(K, L) ⟶
    R\mathcal H\!\mathit{om}(K, M)`;
- `core/canonical`: the ambient internal-Hom owner notation `K ⟹ L` and the composition morphism
  `comp K L M`;
- `bridge/view`: the braiding that swaps the Stacks Project factor order into mathlib's canonical
  order for `comp`.

This item is therefore a `source-facing` bridge built directly from the `core/canonical` owner
data, so the public API should expose the standard internal-Hom notation and the shortest
unambiguous owner form `comp K L M`, rather than raw `(ihom _).obj _` terms or redundant namespace
scaffolding. Downstream constructions that do not need the Stacks-ordered factor swap should call
`comp K L M` directly.
-/

section

variable {X : RingedSpace.{u}}

variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.5: for `K`, `L`, and `M` in `D(\mathcal O_X)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_{\mathcal O_X}^{\mathbf L}
R\mathcal H\!\mathit{om}(K, L) \to R\mathcal H\!\mathit{om}(K, M)`, functorial in `K`, `L`, and
`M`. In the closed monoidal structure on `D(\mathcal O_X)`, this is the usual internal-Hom
composition morphism after swapping the two factors into mathlib's order. -/
noncomputable def internalHomComposition
    (K L M : RingedSpaceDerived X) :
    (L ⟹ M) ⊗ (K ⟹ L) ⟶ (K ⟹ M) :=
  (β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_6 (from Chap20) -/
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
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.6: the canonical morphism
`K \otimes_{\mathcal O_X}^{\mathbf L} R\mathcal H\!\mathit{om}(M, L) \to
R\mathcal H\!\mathit{om}(M, K \otimes_{\mathcal O_X}^{\mathbf L} L)`
in `D(\mathcal O_X)`, obtained from the chapter's tensor-internal-Hom comparison by viewing the
left tensor factor `K` as `R\mathcal H\!\mathit{om}(\mathbf 1, K)` and then restricting the source
of the resulting internal Hom along the left unitor. -/
noncomputable def ringedSpaceDerivedTensorLeftInternalHomComparison
    (K L M : RingedSpaceDerived X) :
    K ⊗ (ihom M).obj L ⟶ (ihom M).obj (K ⊗ L) :=
  ((MonoidalClosed.unitIsoSelf K).inv ⊗ₘ 𝟙 ((ihom M).obj L)) ≫
    ringedSpaceDerivedTensorInternalHomComparison (𝟙_ (RingedSpaceDerived X)) K M L ≫
    (MonoidalClosed.pre (λ_ M).inv).app (K ⊗ L)

-- Proof sketch: uncurry both sides and use the naturality of the associator, braiding,
-- evaluation morphism, and `MonoidalClosed.pre`. This is the abstract monoidal-closed form of
-- the complex-level comparison from Lemma 20.41.3.
/-- Naturality of the derived tensor-internal-Hom comparison in the tensor factor, the target of
the internal Hom, and contravariantly in its source. -/
theorem ringedSpaceDerivedTensorLeftInternalHomComparison_naturality
    {K K' L L' M M' : RingedSpaceDerived X}
    (f : K ⟶ K') (g : L ⟶ L') (h : M' ⟶ M) :
    (f ⊗ₘ ((MonoidalClosed.pre h).app L ≫ (ihom M').map g)) ≫
        ringedSpaceDerivedTensorLeftInternalHomComparison K' L' M' =
      ringedSpaceDerivedTensorLeftInternalHomComparison K L M ≫
        (MonoidalClosed.pre h).app (K ⊗ L) ≫
        (ihom M').map (f ⊗ₘ g) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_7 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Lemma 20.42.7:
- primary domain: the braided closed monoidal structure on `D(\mathcal O_X)`;
- sampled owner declarations:
  `RingedSpaceDerived`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.uncurry_curry`,
  `MonoidalClosed.curry_natural_left`,
  `MonoidalClosed.curry_pre_app`;
- best owner abstraction: the chapter owner `RingedSpaceDerived X`, with the coevaluation map
  obtained from the tensor-internal-Hom adjunction on that owner;
- primitive data: a ringed space `X`, a braided monoidal closed structure on
  `RingedSpaceDerived X`, and objects `K`, `L`;
- derived API: the source-facing coevaluation morphism
  `K ⟶ R\mathcal H\!\mathit{om}(L, K ⊗^{\mathbf L} L)` and its functoriality.

Source/core/bridge triage:
- `source-facing`: the textbook coevaluation morphism
  `K ⟶ R\mathcal H\!\mathit{om}(L, K ⊗^{\mathbf L} L)`;
- `core/canonical`: `MonoidalClosed.curry` together with the braided-monoidal naturality API;
- `bridge/view`: the specialization of that owner API to `RingedSpaceDerived X` and the Stacks
  Project tensor order `K ⊗ L`.
-/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.7: for objects `K, L ∈ D(\mathcal O_X)` on a ringed space `(X, \mathcal O_X)`,
there is a canonical morphism
`K \to R\mathcal H\!\mathit{om}(L, K \otimes_{\mathcal O_X}^{\mathbf L} L)`,
obtained by transporting the braiding `L \otimes_{\mathcal O_X}^{\mathbf L} K \to
K \otimes_{\mathcal O_X}^{\mathbf L} L` across the derived tensor-internal-Hom adjunction. -/
noncomputable def ringedSpaceDerivedTensorInternalHomUnit
    (K L : RingedSpaceDerived X) :
    K ⟶ (ihom L).obj (K ⊗ L) :=
  MonoidalClosed.curry ((β_ L K).hom)

/-- Uncurrying the canonical unit morphism recovers the braiding
`L \otimes_{\mathcal O_X}^{\mathbf L} K \to K \otimes_{\mathcal O_X}^{\mathbf L} L`. -/
theorem ringedSpaceDerivedTensorInternalHomUnit_spec
    (K L : RingedSpaceDerived X) :
    MonoidalClosed.uncurry (ringedSpaceDerivedTensorInternalHomUnit K L) =
      (β_ L K).hom := by
  simp [ringedSpaceDerivedTensorInternalHomUnit]

/-- The canonical morphism `K \to R\mathcal H\!\mathit{om}(L, K \otimes^{\mathbf L} L)` is
natural in the first variable `K`. -/
theorem ringedSpaceDerivedTensorInternalHomUnit_natural_left
    {K K' L : RingedSpaceDerived X} (f : K ⟶ K') :
    f ≫ ringedSpaceDerivedTensorInternalHomUnit K' L =
      ringedSpaceDerivedTensorInternalHomUnit K L ≫
        (ihom L).map (f ⊗ₘ 𝟙 L) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_natural_right,
    ringedSpaceDerivedTensorInternalHomUnit_spec, ringedSpaceDerivedTensorInternalHomUnit_spec]
  simp

/-- The canonical morphism `K \to R\mathcal H\!\mathit{om}(L, K \otimes^{\mathbf L} L)` is
natural in the second variable `L`. -/
theorem ringedSpaceDerivedTensorInternalHomUnit_natural_right
    (K : RingedSpaceDerived X) {L L' : RingedSpaceDerived X} (g : L ⟶ L') :
    ringedSpaceDerivedTensorInternalHomUnit K L' ≫
        (MonoidalClosed.pre g).app (K ⊗ L') =
      ringedSpaceDerivedTensorInternalHomUnit K L ≫
        (ihom L).map (𝟙 K ⊗ₘ g) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_pre_app, MonoidalClosed.uncurry_natural_right,
    ringedSpaceDerivedTensorInternalHomUnit_spec, ringedSpaceDerivedTensorInternalHomUnit_spec]
  simp

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_8 (from Chap20) -/
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

variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.8: for `L, M ∈ D(\mathcal O_X)`, the canonical morphism
`M \otimes_{\mathcal O_X}^{\mathbf L} L^\vee \to R\mathcal H\!\mathit{om}(L, M)` from
`20.42.8.1` induces a canonical map
`H^0(X, M \otimes_{\mathcal O_X}^{\mathbf L} L^\vee) \to \operatorname{Hom}_{D(\mathcal O_X)}(L, M)`.
In Lean, `H^0(X, K)` is modeled by morphisms `𝟙_ (RingedSpaceDerived X) ⟶ K`, where the monoidal unit is the
structure sheaf `\mathcal O_X` in `D(\mathcal O_X)`. -/
noncomputable def ringedSpaceDerivedEvaluationH0ToHom
    (L M : RingedSpaceDerived X) :
    (𝟙_ (RingedSpaceDerived X) ⟶ M ⊗ L^∨) → (L ⟶ M) :=
  fun s ↦
    (ρ_ L).inv ≫
      MonoidalClosed.uncurry (s ≫ ringedSpaceDerivedEvaluationHom L M)

-- Proof sketch: postcompose a class `𝟙 ⟶ M ⊗ L^\vee` with the evaluation morphism
-- `M ⊗ L^\vee ⟶ R\mathcal H\!\mathit{om}(L, M)`, then uncurry to a morphism
-- `L ⊗ 𝟙 ⟶ M` and transport across the right unitor `L ⊗ 𝟙 ≅ L`. Naturality in `M` comes from
-- functoriality of the evaluation morphism in its target variable together with naturality of
-- uncurrying.
/-- The induced map on `H^0(X, -)` is functorial in the target object `M`. -/
theorem ringedSpaceDerivedEvaluationH0ToHom_natural
    {L M M' : RingedSpaceDerived X} (f : M ⟶ M')
    (s : 𝟙_ (RingedSpaceDerived X) ⟶ M ⊗ L^∨) :
    ringedSpaceDerivedEvaluationH0ToHom L M' (s ≫ (f ⊗ₘ 𝟙 L^∨)) =
      ringedSpaceDerivedEvaluationH0ToHom L M s ≫ f := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_42_9 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Lemma 20.42.9:
- primary domain: tensor-internal-Hom comparison morphisms in a braided monoidal closed derived
category of `\mathcal O_X`-modules;
- inspected owner declarations:
  `CategoryTheory.MonoidalClosed.comp`,
  `MonoidalClosed.curry`,
  `MonoidalClosed.pre`,
  `MonoidalClosed.uncurry`;
- best owner abstraction: the ambient closed-monoidal composition map `comp K L M`, together with
  currying and precomposition in the internal-Hom variable; Lemma `20.42.9` is its adjoint
  transpose after transporting the tensor factors into the Stacks Project order
  `R\mathcal H\!\mathit{om}(L, M) \otimes^{\mathbf L} K`;
- primitive data: the ambient braided monoidal closed structure on `RingedSpaceDerived X` and
  the objects `K`, `L`, `M`;
- derived API: the canonical comparison morphism together with its uncurrying formula and
  naturality lemmas.

Source/core/bridge triage:
- `source-facing`: the comparison morphism of Lemma 20.42.9;
- `core/canonical`: `comp K L M`, `MonoidalClosed.curry`,
  `MonoidalClosed.pre`, and `MonoidalClosed.uncurry`;
- `bridge/view`: the braiding and associator rearrangement that converts the canonical
  internal-Hom composition/evaluation data into the Stacks Project tensor order.

This file therefore keeps the source-facing comparison map as the public owner and derives it
directly from the canonical internal-Hom composition owner `comp K L M`; downstream files should
reuse that owner directly when they do not need the Stacks-ordered bridge of Lemma `20.42.5`.
-/

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- Lemma 20.42.9: for a ringed space `(X, \mathcal O_X)` and objects `K`, `L`, `M` of
`D(\mathcal O_X)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(L, M) \otimes_{\mathcal O_X}^{\mathbf L} K \to
R\mathcal H\!\mathit{om}(R\mathcal H\!\mathit{om}(K, L), M)`. -/
noncomputable def tensorInternalHomToIteratedInternalHom
    (K L M : RingedSpaceDerived X) :
    (L ⟹ M) ⊗ K ⟶ ((K ⟹ L) ⟹ M) :=
  MonoidalClosed.curry
    ((α_ (K ⟹ L) (L ⟹ M) K).inv ≫
      ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
      ((β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M) ▷ K ≫
      (β_ (K ⟹ M) K).hom ≫
      MonoidalClosed.uncurry (𝟙 (K ⟹ M)))

-- Proof sketch: the main morphism is defined as the currying of the displayed transpose, so
-- uncurrying it recovers that transpose by `MonoidalClosed.uncurry_curry`.
/-- Uncurrying the canonical tensor-to-iterated-internal-Hom morphism recovers its explicit
transpose. -/
theorem tensorInternalHomToIteratedInternalHom_uncurry
    (K L M : RingedSpaceDerived X) :
    MonoidalClosed.uncurry
        (tensorInternalHomToIteratedInternalHom K L M) =
      (α_ (K ⟹ L) (L ⟹ M) K).inv ≫
        ((β_ (K ⟹ L) (L ⟹ M)).hom ▷ K) ≫
        ((β_ (L ⟹ M) (K ⟹ L)).hom ≫ comp K L M) ▷ K ≫
        (β_ (K ⟹ M) K).hom ≫
        MonoidalClosed.uncurry (𝟙 (K ⟹ M)) := by
  simp [tensorInternalHomToIteratedInternalHom]

-- Proof sketch: use naturality of currying in the tensor factor `K`, together with the
-- contravariant functoriality of the inner internal Hom in its source variable.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the first variable
`K`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_first_variable
    {K K' L M : RingedSpaceDerived X} (f : K ⟶ K') :
    ((𝟙 ((ihom L).obj M)) ⊗ₘ f) ≫
        tensorInternalHomToIteratedInternalHom K' L M =
      tensorInternalHomToIteratedInternalHom K L M ≫
        (MonoidalClosed.pre ((MonoidalClosed.pre f).app L)).app M := sorry

-- Proof sketch: compare the two transposes obtained from a morphism `L ⟶ L'`; on the source side
-- this acts by precomposition on `R\mathcal H\!\mathit{om}(L', M)`, and on the target side by
-- precomposition on the outer internal Hom along `R\mathcal H\!\mathit{om}(K, L) ⟶
-- R\mathcal H\!\mathit{om}(K, L')`.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the second variable
`L`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_second_variable
    {K L L' M : RingedSpaceDerived X} (g : L ⟶ L') :
    (((MonoidalClosed.pre g).app M) ⊗ₘ 𝟙 K) ≫
        tensorInternalHomToIteratedInternalHom K L M =
      tensorInternalHomToIteratedInternalHom K L' M ≫
        (MonoidalClosed.pre ((ihom K).map g)).app M := sorry

-- Proof sketch: use functoriality of both internal-Hom factors in the target object `M` and the
-- naturality of currying in the codomain.
/-- The canonical tensor-to-iterated-internal-Hom morphism is natural in the third variable
`M`. -/
theorem tensorInternalHomToIteratedInternalHom_natural_in_third_variable
    {K L M M' : RingedSpaceDerived X} (h : M ⟶ M') :
    (((ihom L).map h) ⊗ₘ 𝟙 K) ≫
        tensorInternalHomToIteratedInternalHom K L M' =
      tensorInternalHomToIteratedInternalHom K L M ≫
        (ihom ((ihom K).obj L)).map h := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_42_10 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, viewed as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The unbounded derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
abbrev RingedSpaceDerived (X : RingedSpace.{u}) :=
  DerivedCategory (RingedSpace.Modules X)

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]

/-- The evaluation morphism `R\mathcal H\!\mathit{om}(K, K') \otimes^{\mathbf L} K \to K'`,
written in the textbook's factor order. -/
noncomputable def ringedSpaceDerivedInternalHomEvaluation
    (K K' : RingedSpaceDerived X) :
    (ihom K).obj K' ⊗ K ⟶ K' :=
  (β_ ((ihom K).obj K') K).hom ≫ MonoidalClosed.uncurry (𝟙 ((ihom K).obj K'))

-- Proof sketch: unfold `ringedSpaceDerivedInternalHomEvaluation`; the morphism is defined by
-- first braiding `R\mathcal H\!\mathit{om}(K, K')` past `K`, and then applying the counit
-- `K \otimes^{\mathbf L} R\mathcal H\!\mathit{om}(K, K') \to K'` of the internal-Hom adjunction.
/-- The book-order evaluation morphism is the braiding followed by the closed-monoidal
evaluation map. -/
theorem ringedSpaceDerivedInternalHomEvaluation_eq
    (K K' : RingedSpaceDerived X) :
    ringedSpaceDerivedInternalHomEvaluation K K' =
      (β_ ((ihom K).obj K') K).hom ≫ MonoidalClosed.uncurry (𝟙 ((ihom K).obj K')) := sorry

/-- The uncurried morphism underlying the tensor-internal-Hom comparison on
`D(\mathcal O_X)`. -/
noncomputable def ringedSpaceDerivedTensorInternalHomComparisonTranspose
    (K K' M M' : RingedSpaceDerived X) :
    (((ihom K).obj K' ⊗ (ihom M).obj M') ⊗ (K ⊗ M)) ⟶ (K' ⊗ M') :=
  (α_ ((ihom K).obj K') ((ihom M).obj M') (K ⊗ M)).hom ≫
    (((ihom K).obj K') ◁ (α_ ((ihom M).obj M') K M).inv) ≫
    (((ihom K).obj K') ◁ (((β_ ((ihom M).obj M') K).hom) ▷ M)) ≫
    (((ihom K).obj K') ◁ (α_ K ((ihom M).obj M') M).hom) ≫
    (α_ ((ihom K).obj K') K (((ihom M).obj M') ⊗ M)).inv ≫
    ringedSpaceDerivedInternalHomEvaluation K K' ▷ (((ihom M).obj M') ⊗ M) ≫
    K' ◁ ringedSpaceDerivedInternalHomEvaluation M M'

-- Proof sketch: unfold
-- `ringedSpaceDerivedTensorInternalHomComparisonTranspose`; it first reassociates the four
-- factors, flips the middle two by the braiding, then evaluates
-- `R\mathcal H\!\mathit{om}(K, K') \otimes^{\mathbf L} K` and
-- `R\mathcal H\!\mathit{om}(M, M') \otimes^{\mathbf L} M` separately.
/-- The uncurried comparison morphism flips the middle two factors and then applies the two
evaluation maps. -/
theorem ringedSpaceDerivedTensorInternalHomComparisonTranspose_eq
    (K K' M M' : RingedSpaceDerived X) :
    ringedSpaceDerivedTensorInternalHomComparisonTranspose K K' M M' =
      (α_ ((ihom K).obj K') ((ihom M).obj M') (K ⊗ M)).hom ≫
        (((ihom K).obj K') ◁ (α_ ((ihom M).obj M') K M).inv) ≫
        (((ihom K).obj K') ◁ (((β_ ((ihom M).obj M') K).hom) ▷ M)) ≫
        (((ihom K).obj K') ◁ (α_ K ((ihom M).obj M') M).hom) ≫
        (α_ ((ihom K).obj K') K (((ihom M).obj M') ⊗ M)).inv ≫
        ringedSpaceDerivedInternalHomEvaluation K K' ▷ (((ihom M).obj M') ⊗ M) ≫
        K' ◁ ringedSpaceDerivedInternalHomEvaluation M M' := sorry

/-- Remark 20.42.10: in `D(\mathcal O_X)`, there is a canonical morphism
`R\mathcal H\!\mathit{om}(K, K') \otimes_{\mathcal O_X}^{\mathbf L}
R\mathcal H\!\mathit{om}(M, M') \to
R\mathcal H\!\mathit{om}(K \otimes_{\mathcal O_X}^{\mathbf L} M,
K' \otimes_{\mathcal O_X}^{\mathbf L} M')`. -/
noncomputable def ringedSpaceDerivedTensorInternalHomComparison
    (K K' M M' : RingedSpaceDerived X) :
    (ihom K).obj K' ⊗ (ihom M).obj M' ⟶ (ihom (K ⊗ M)).obj (K' ⊗ M') :=
  MonoidalClosed.curry <|
    (β_ (K ⊗ M) ((ihom K).obj K' ⊗ (ihom M).obj M')).hom ≫
      ringedSpaceDerivedTensorInternalHomComparisonTranspose K K' M M'

-- Proof sketch: `ringedSpaceDerivedTensorInternalHomComparison` is defined as the adjoint
-- transpose of the explicit four-factor morphism. Uncurrying therefore recovers the braiding
-- that puts `K \otimes^{\mathbf L} M` into the left slot, followed by the transpose map.
/-- Uncurrying the canonical tensor-internal-Hom comparison recovers the explicit morphism
obtained by braiding `K \otimes^{\mathbf L} M` to the front and then evaluating each internal
Hom factor. -/
theorem ringedSpaceDerivedTensorInternalHomComparison_uncurry
    (K K' M M' : RingedSpaceDerived X) :
    MonoidalClosed.uncurry (ringedSpaceDerivedTensorInternalHomComparison K K' M M') =
      (β_ (K ⊗ M) ((ihom K).obj K' ⊗ (ihom M).obj M')).hom ≫
        ringedSpaceDerivedTensorInternalHomComparisonTranspose K K' M M' := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_42_11 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape
open scoped CartesianClosed

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

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

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
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ RingedSpaceDerived X :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-category functor used to define the total right derived pushforward. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ RingedSpaceDerived Y :=
  (modulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    RingedSpaceDerived Y ⥤ RingedSpaceDerived X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ RingedSpaceDerived Y)
    (ModuleQis Y)

/-- The derived pushforward functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    RingedSpaceDerived X ⥤ RingedSpaceDerived Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ RingedSpaceDerived X)
    (ModuleQis X)

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)

variable [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
variable [(modulePullback f).Additive] [(modulePushforward f).Additive]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]
variable [MonoidalCategory (RingedSpaceDerived X)]
variable [BraidedCategory (RingedSpaceDerived X)]
variable [MonoidalClosed (RingedSpaceDerived X)]
variable [MonoidalCategory (RingedSpaceDerived Y)]
variable [BraidedCategory (RingedSpaceDerived Y)]
variable [MonoidalClosed (RingedSpaceDerived Y)]

/-- The tensor-internal-Hom adjunction on `D(\mathcal O_Y)`, written with the tensor factors in
the order used by the Stacks Project. -/
abbrev ringedSpaceDerivedInternalHomAdjunction
    (A B C : RingedSpaceDerived Y) :
    (A ⟶ (ihom B).obj C) ≃ (A ⊗ B ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    ((β_ A B).symm.homCongr (Iso.refl C))

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(L, K) \otimes^{\mathbf L} L \to K` in `D(\mathcal O_X)`,
obtained from internal-Hom composition and the unit object. -/
noncomputable def ringedSpaceDerivedInternalHomEvaluation
    (L K : RingedSpaceDerived X) :
    (L ⟹ K) ⊗ L ⟶ K :=
  (𝟙 (L ⟹ K) ⊗ₘ
      (unitIsoSelf L).symm.hom) ≫
    (β_ (L ⟹ K) ((𝟙_ (RingedSpaceDerived X)) ⟹ L)).hom ≫
    comp (𝟙_ (RingedSpaceDerived X)) L K ≫
    (unitIsoSelf K).hom

/-- The relative cup product
`Rf_* A \otimes^{\mathbf L} Rf_* B \to Rf_*(A \otimes^{\mathbf L} B)` on derived categories of
module sheaves, given a chosen derived adjunction and pullback-tensor comparison. -/
noncomputable def ringedSpaceDerivedPushforwardCupProduct
    (pullPushAdj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (pullbackTensorIso :
      ∀ (A B : RingedSpaceDerived Y),
        (modulePullbackDerived f).obj (A ⊗ B) ≅
          ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))
    (A B : RingedSpaceDerived X) :
    (moduleDerivedPushforward f).obj A ⊗ (moduleDerivedPushforward f).obj B ⟶
      (moduleDerivedPushforward f).obj (A ⊗ B) :=
  (pullPushAdj.homEquiv _ _)
    ((pullbackTensorIso
        ((moduleDerivedPushforward f).obj A)
        ((moduleDerivedPushforward f).obj B)).hom ≫
      (pullPushAdj.counit.app A ▷
        (modulePullbackDerived f).obj ((moduleDerivedPushforward f).obj B)) ≫
      (A ◁ pullPushAdj.counit.app B))

/-- Remark 20.42.11: after fixing the derived adjunction `Lf^* ⊣ Rf_*` and the pullback-tensor
comparison used in Remark `20.28.7`, there is a canonical morphism
`Rf_* R\mathcal H\!\mathit{om}(L, K) \to
R\mathcal H\!\mathit{om}(Rf_* L, Rf_* K)` in `D(\mathcal O_Y)`. -/
noncomputable def ringedSpaceDerivedPushforwardInternalHomComparison
    (pullPushAdj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (pullbackTensorIso :
      ∀ (A B : RingedSpaceDerived Y),
        (modulePullbackDerived f).obj (A ⊗ B) ≅
          ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))
    (L K : RingedSpaceDerived X) :
    (moduleDerivedPushforward f).obj ((ihom L).obj K) ⟶
      (ihom ((moduleDerivedPushforward f).obj L)).obj ((moduleDerivedPushforward f).obj K) :=
  (ringedSpaceDerivedInternalHomAdjunction
      ((moduleDerivedPushforward f).obj ((ihom L).obj K))
      ((moduleDerivedPushforward f).obj L)
      ((moduleDerivedPushforward f).obj K)).symm
    (ringedSpaceDerivedPushforwardCupProduct f pullPushAdj pullbackTensorIso
        ((ihom L).obj K) L ≫
      (moduleDerivedPushforward f).map
        (ringedSpaceDerivedInternalHomEvaluation L K))

-- Proof sketch: unfold
-- `ringedSpaceDerivedPushforwardInternalHomComparison`; it is defined as the inverse image of the
-- displayed tensor morphism under the tensor-internal-Hom adjunction on `D(\mathcal O_Y)`.
/-- Applying the tensor-internal-Hom adjunction to the pushforward-internal-Hom comparison
recovers the relative cup product followed by the pushed-forward evaluation morphism. -/
theorem ringedSpaceDerivedPushforwardInternalHomComparison_homEquiv
    (pullPushAdj : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (pullbackTensorIso :
      ∀ (A B : RingedSpaceDerived Y),
        (modulePullbackDerived f).obj (A ⊗ B) ≅
          ((modulePullbackDerived f).obj A ⊗ (modulePullbackDerived f).obj B))
    (L K : RingedSpaceDerived X) :
    ringedSpaceDerivedInternalHomAdjunction
        ((moduleDerivedPushforward f).obj ((ihom L).obj K))
        ((moduleDerivedPushforward f).obj L)
        ((moduleDerivedPushforward f).obj K)
        (ringedSpaceDerivedPushforwardInternalHomComparison f pullPushAdj pullbackTensorIso
          L K) =
      ringedSpaceDerivedPushforwardCupProduct f pullPushAdj pullbackTensorIso
          ((ihom L).obj K) L ≫
        (moduleDerivedPushforward f).map
          (ringedSpaceDerivedInternalHomEvaluation L K) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_42_12 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a sheaf of rings. -/
section

variable {X Y : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (SheafOfModules (ringCatSheaf X))
local notation "DModY" => DerivedCategory (SheafOfModules (ringCatSheaf Y))

variable (rightDerivedPushforward : DModX ⥤ DModY)
variable (derivedTensorX : DModX ⥤ DModX ⥤ DModX)
variable (derivedTensorY : DModY ⥤ DModY ⥤ DModY)
variable (derivedInternalHomX : DModXᵒᵖ ⥤ DModX ⥤ DModX)
variable (derivedInternalHomY : DModYᵒᵖ ⥤ DModY ⥤ DModY)
variable
  (relativeDerivedCupProduct :
    ∀ (A B : DModX),
      (derivedTensorY.obj (rightDerivedPushforward.obj B)).obj
          (rightDerivedPushforward.obj A) ⟶
        rightDerivedPushforward.obj ((derivedTensorX.obj B).obj A))
variable
  (pushforwardInternalHomComparison :
    ∀ (K M : DModX),
      rightDerivedPushforward.obj ((derivedInternalHomX.obj (Opposite.op K)).obj M) ⟶
        (derivedInternalHomY.obj (Opposite.op (rightDerivedPushforward.obj K))).obj
          (rightDerivedPushforward.obj M))
variable
  (evaluationX :
    ∀ (K M : DModX),
      (derivedTensorX.obj K).obj ((derivedInternalHomX.obj (Opposite.op K)).obj M) ⟶ M)
variable
  (evaluationY :
    ∀ (K M : DModY),
      (derivedTensorY.obj K).obj ((derivedInternalHomY.obj (Opposite.op K)).obj M) ⟶ M)

-- Proof sketch: this is the compatibility of the pushforward-internal-Hom comparison with the
-- evaluation maps. The top arrow is the relative cup product, the left arrow is obtained by
-- tensoring the comparison map with `Rf_* K`, and the right and bottom arrows are the evaluation
-- morphisms on `X` and `Y`; the two routes through the square both express the pushed-forward
-- evaluation pairing.
/-- Remark 20.42.12: for a morphism of ringed spaces, the pushforward-internal-Hom comparison of
Remark `20.42.11` is compatible with evaluation. In the derived categories of module sheaves on
`X` and `Y`, if the top edge is the relative cup product of Remark `20.28.7`, the left edge is
the tensor of the comparison map
`Rf_* R\mathcal H\!\mathit{om}_{\mathcal O_X}(K, M) ⟶
R\mathcal H\!\mathit{om}_{\mathcal O_Y}(Rf_* K, Rf_* M)` with `Rf_* K`, and the right and
bottom edges are the evaluation morphisms on `X` and `Y`, then the resulting square commutes. -/
theorem pushforwardInternalHomComparison_evaluation_commSq
    (K M : DModX) :
    let A :=
      (derivedTensorY.obj (rightDerivedPushforward.obj K)).obj
        (rightDerivedPushforward.obj ((derivedInternalHomX.obj (Opposite.op K)).obj M))
    let B :=
      rightDerivedPushforward.obj
        ((derivedTensorX.obj K).obj ((derivedInternalHomX.obj (Opposite.op K)).obj M))
    let C :=
      (derivedTensorY.obj (rightDerivedPushforward.obj K)).obj
        ((derivedInternalHomY.obj (Opposite.op (rightDerivedPushforward.obj K))).obj
          (rightDerivedPushforward.obj M))
    let D :=
      rightDerivedPushforward.obj M
    let top : A ⟶ B :=
      relativeDerivedCupProduct ((derivedInternalHomX.obj (Opposite.op K)).obj M) K
    let left : A ⟶ C :=
      (derivedTensorY.obj (rightDerivedPushforward.obj K)).map
        (pushforwardInternalHomComparison K M)
    let right : B ⟶ D :=
      rightDerivedPushforward.map (evaluationX K M)
    let bot : C ⟶ D :=
      evaluationY (rightDerivedPushforward.obj K) (rightDerivedPushforward.obj M)
    CommSq top left right bot := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_42_13 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
/-- The derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules. -/
private abbrev DMod (X : RingedSpace.{u}) :=
  DerivedCategory (SheafOfModules (ringCatSheaf X))

/-- The tensor-internal-Hom adjunction on `D(\mathcal O_X)`, written in the Stacks Project order
`A ⊗ B`. -/
private abbrev ringedSpaceDerivedInternalHomAdjunction
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (A B C : DMod X) :
    (A ⟶ (ihom B).obj C) ≃ (A ⊗ B ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    ((β_ A B).symm.homCongr (Iso.refl C))

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} K \to L`
in `D(\mathcal O_X)`. -/
private abbrev ringedSpaceDerivedInternalHomEvaluation
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (K L : DMod X) :
    (ihom K).obj L ⊗ K ⟶ L :=
  ringedSpaceDerivedInternalHomAdjunction X ((ihom K).obj L) K L (𝟙 ((ihom K).obj L))

section

variable {X Y : RingedSpace.{u}}

variable (leftDerivedPullback : DMod Y ⥤ DMod X)

variable [MonoidalCategory (DMod X)]
variable [BraidedCategory (DMod X)]
variable [MonoidalClosed (DMod X)]
variable [MonoidalCategory (DMod Y)]
variable [BraidedCategory (DMod Y)]
variable [MonoidalClosed (DMod Y)]

/-- Remark 20.42.13: after choosing a derived pullback functor `Lh^* : D(\mathcal O_Y) ⥤
D(\mathcal O_X)` and the pullback-tensor comparison isomorphism of Lemma `20.27.3`, there is a
canonical morphism
`Lh^* R\mathcal H\!\mathit{om}(K, L) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)`. -/
noncomputable def pullbackDerivedInternalHomComparison
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    leftDerivedPullback.obj ((ihom K).obj L) ⟶
      (ihom (leftDerivedPullback.obj K)).obj (leftDerivedPullback.obj L) :=
  (ringedSpaceDerivedInternalHomAdjunction X
      (leftDerivedPullback.obj ((ihom K).obj L))
      (leftDerivedPullback.obj K)
      (leftDerivedPullback.obj L)).symm
    ((pullbackTensorIso ((ihom K).obj L) K).inv ≫
      leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L))

-- Proof sketch: unfold `pullbackDerivedInternalHomComparison`; by definition it is the inverse
-- image of the pulled-back evaluation morphism under the target-side tensor-internal-Hom
-- adjunction, after transporting along the pullback-tensor comparison
-- `Lh^*(R\mathcal H\!\mathit{om}(K, L) ⊗^{\mathbf L} K) ≅
--   Lh^*R\mathcal H\!\mathit{om}(K, L) ⊗^{\mathbf L} Lh^*K`.
/-- Applying the tensor-internal-Hom adjunction to the pullback comparison recovers the pullback
of the evaluation morphism after transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    ringedSpaceDerivedInternalHomAdjunction X
        (leftDerivedPullback.obj ((ihom K).obj L))
        (leftDerivedPullback.obj K)
        (leftDerivedPullback.obj L)
        (pullbackDerivedInternalHomComparison leftDerivedPullback pullbackTensorIso K L) =
      (pullbackTensorIso ((ihom K).obj L) K).inv ≫
        leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Remark_20_42_14 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open ComplexShape

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The structure sheaf of a ringed space, regarded as a `RingCat`-valued sheaf. -/
/-- The category of sheaves of `\mathcal O_X`-modules on a ringed space. -/
/-- The derived category `D(\mathcal O_X)` of sheaves of `\mathcal O_X`-modules on a ringed
space. -/
private abbrev DMod (X : RingedSpace.{u}) :=
  DerivedCategory (SheafOfModules (ringCatSheaf X))

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

/-- The direct-image functor on `\mathcal O_X`-modules attached to a morphism of ringed spaces. -/
noncomputable abbrev modulePushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y) :
    (RingedSpace.Modules X) ⥤ (RingedSpace.Modules Y) :=
  SheafOfModules.pushforward (pushforwardStructureSheafHom f)

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
    HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DMod X :=
  (modulePullback f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The homotopy-category functor used to define the total right derived pushforward. -/
abbrev modulePushforwardToDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive] :
    HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DMod Y :=
  (modulePushforward f).mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The derived pullback functor `Lf^* : D(\mathcal O_Y) ⥤ D(\mathcal O_X)`. -/
abbrev modulePullbackDerived {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [CategoryWithHomology (RingedSpace.Modules X)] [CategoryWithHomology (RingedSpace.Modules Y)]
    [(modulePullback f).Additive]
    [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis Y)] :
    DMod Y ⥤ DMod X :=
  Functor.totalLeftDerived (modulePullbackToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules Y) (up ℤ) ⥤ DMod Y)
    (ModuleQis Y)

/-- The derived pushforward functor `Rf_* : D(\mathcal O_X) ⥤ D(\mathcal O_Y)`. -/
abbrev moduleDerivedPushforward {X Y : RingedSpace.{u}} (f : X ⟶ Y)
    [(modulePushforward f).Additive]
    [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)] :
    DMod X ⥤ DMod Y :=
  Functor.totalRightDerived (modulePushforwardToDerived f)
    (DerivedCategory.Qh : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤ DMod X)
    (ModuleQis X)

/-- The tensor-internal-Hom adjunction on `D(\mathcal O_X)`, written in the Stacks Project order
`A ⊗ B`. -/
private abbrev ringedSpaceDerivedInternalHomAdjunction
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (A B C : DMod X) :
    (A ⟶ (ihom B).obj C) ≃ (A ⊗ B ⟶ C) :=
  ((ihom.adjunction B).homEquiv A C).symm.trans
    ((β_ A B).symm.homCongr (Iso.refl C))

/-- The evaluation morphism
`R\mathcal H\!\mathit{om}(K, L) \otimes^{\mathbf L} K \to L`
in `D(\mathcal O_X)`. -/
private abbrev ringedSpaceDerivedInternalHomEvaluation
    (X : RingedSpace.{u})
    [MonoidalCategory (DMod X)] [BraidedCategory (DMod X)] [MonoidalClosed (DMod X)]
    (K L : DMod X) :
    (ihom K).obj L ⊗ K ⟶ L :=
  ringedSpaceDerivedInternalHomAdjunction X ((ihom K).obj L) K L (𝟙 ((ihom K).obj L))

section

variable {X Y : RingedSpace.{u}}

variable (leftDerivedPullback : DMod Y ⥤ DMod X)

variable [MonoidalCategory (DMod X)]
variable [BraidedCategory (DMod X)]
variable [MonoidalClosed (DMod X)]
variable [MonoidalCategory (DMod Y)]
variable [BraidedCategory (DMod Y)]
variable [MonoidalClosed (DMod Y)]

/-- The pullback comparison
`Lh^* R\mathcal H\!\mathit{om}(K, L) \to
R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)` induced by the pullback-tensor comparison. -/
noncomputable def pullbackDerivedInternalHomComparison
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    leftDerivedPullback.obj ((ihom K).obj L) ⟶
      (ihom (leftDerivedPullback.obj K)).obj (leftDerivedPullback.obj L) :=
  (ringedSpaceDerivedInternalHomAdjunction X
      (leftDerivedPullback.obj ((ihom K).obj L))
      (leftDerivedPullback.obj K)
      (leftDerivedPullback.obj L)).symm
    ((pullbackTensorIso ((ihom K).obj L) K).inv ≫
      leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L))

-- Proof sketch: unfold `pullbackDerivedInternalHomComparison`; by definition it is the inverse
-- image of the pulled-back evaluation morphism under the target-side tensor-internal-Hom
-- adjunction, after transporting along the pullback-tensor comparison.
/-- Applying the tensor-internal-Hom adjunction to the pullback comparison recovers the pullback
of the evaluation morphism after transport across the pullback-tensor comparison. -/
theorem pullbackDerivedInternalHomComparison_spec
    (pullbackTensorIso :
      ∀ (A B : DMod Y),
        leftDerivedPullback.obj (A ⊗ B) ≅
          (leftDerivedPullback.obj A ⊗ leftDerivedPullback.obj B))
    (K L : DMod Y) :
    ringedSpaceDerivedInternalHomAdjunction X
        (leftDerivedPullback.obj ((ihom K).obj L))
        (leftDerivedPullback.obj K)
        (leftDerivedPullback.obj L)
        (pullbackDerivedInternalHomComparison leftDerivedPullback pullbackTensorIso K L) =
      (pullbackTensorIso ((ihom K).obj L) K).inv ≫
        leftDerivedPullback.map (ringedSpaceDerivedInternalHomEvaluation Y K L) := sorry

end

section

variable {X' X S' S : RingedSpace.{u}}
variable (h : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S) (f : X ⟶ S)

variable [CategoryWithHomology (RingedSpace.Modules X')]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules S')]
variable [CategoryWithHomology (RingedSpace.Modules S)]

variable [(modulePullback h).Additive]
variable [(modulePullback f').Additive]
variable [(modulePullback g).Additive]
variable [(modulePullback f).Additive]
variable [(modulePushforward f').Additive]
variable [(modulePushforward f).Additive]

variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived h) (ModuleQis X)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f') (ModuleQis S')]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived g) (ModuleQis S)]
variable [Functor.HasLeftDerivedFunctor (modulePullbackToDerived f) (ModuleQis S)]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f') (ModuleQis X')]
variable [Functor.HasRightDerivedFunctor (modulePushforwardToDerived f) (ModuleQis X)]

variable [MonoidalCategory (DMod X')]
variable [BraidedCategory (DMod X')]
variable [MonoidalClosed (DMod X')]
variable [MonoidalCategory (DMod X)]
variable [BraidedCategory (DMod X)]
variable [MonoidalClosed (DMod X)]

/-- Remark 20.42.14: given a commutative square of ringed spaces together with the induced
pullback-commutativity isomorphism on derived pullbacks, the adjunctions `Lf^* ⊣ Rf_*` and
`L(f')^* ⊣ R(f')_*`, and the pullback-tensor comparison for `h`, there is a canonical base-change
morphism
`Lg^* Rf_* R\mathcal H\!\mathit{om}(K, L) ⟶
R(f')_* R\mathcal H\!\mathit{om}(Lh^* K, Lh^* L)`. -/
noncomputable def derivedInternalHomBaseChangeMap
    (pullbackCommIso :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived h)
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_f' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (pullbackTensorIso_h :
      ∀ (A B : DMod X),
        (modulePullbackDerived h).obj (A ⊗ B) ≅
          ((modulePullbackDerived h).obj A ⊗ (modulePullbackDerived h).obj B))
    (K L : DMod X) :
    (modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj ((ihom K).obj L)) ⟶
      (moduleDerivedPushforward f').obj
        ((ihom ((modulePullbackDerived h).obj K)).obj ((modulePullbackDerived h).obj L)) :=
  adj_f'.homEquiv
      ((modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj ((ihom K).obj L)))
      ((ihom ((modulePullbackDerived h).obj K)).obj ((modulePullbackDerived h).obj L))
    (pullbackCommIso.hom.app ((moduleDerivedPushforward f).obj ((ihom K).obj L)) ≫
      (modulePullbackDerived h).map (adj_f.counit.app ((ihom K).obj L)) ≫
      pullbackDerivedInternalHomComparison (modulePullbackDerived h) pullbackTensorIso_h K L)

-- Proof sketch: unfold `derivedInternalHomBaseChangeMap`. By definition it is the transpose,
-- under `L(f')^* ⊣ R(f')_*`, of the composite obtained by transporting `L(f')^*Lg^*` to
-- `Lh^*Lf^*`, applying the counit `Lf^*Rf_* → 𝟭`, and then using the pullback-internal-Hom
-- comparison from Remark `20.42.13`.
/-- Applying the adjunction `L(f')^* ⊣ R(f')_*` to the internal-Hom base-change map recovers the
composite prescribed in the remark. -/
theorem derivedInternalHomBaseChangeMap_spec
    (pullbackCommIso :
      modulePullbackDerived g ⋙ modulePullbackDerived f' ≅
        modulePullbackDerived f ⋙ modulePullbackDerived h)
    (adj_f : modulePullbackDerived f ⊣ moduleDerivedPushforward f)
    (adj_f' : modulePullbackDerived f' ⊣ moduleDerivedPushforward f')
    (pullbackTensorIso_h :
      ∀ (A B : DMod X),
        (modulePullbackDerived h).obj (A ⊗ B) ≅
          ((modulePullbackDerived h).obj A ⊗ (modulePullbackDerived h).obj B))
    (K L : DMod X) :
    (adj_f'.homEquiv
        ((modulePullbackDerived g).obj ((moduleDerivedPushforward f).obj ((ihom K).obj L)))
        ((ihom ((modulePullbackDerived h).obj K)).obj ((modulePullbackDerived h).obj L))
        ).symm
        (derivedInternalHomBaseChangeMap h f' g f pullbackCommIso adj_f adj_f'
          pullbackTensorIso_h K L) =
      pullbackCommIso.hom.app ((moduleDerivedPushforward f).obj ((ihom K).obj L)) ≫
        (modulePullbackDerived h).map (adj_f.counit.app ((ihom K).obj L)) ≫
        pullbackDerivedInternalHomComparison (modulePullbackDerived h) pullbackTensorIso_h K L := sorry

end

end AlgebraicGeometry.RingedSpace
