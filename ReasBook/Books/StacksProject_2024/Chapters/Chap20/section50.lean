import Mathlib
import Mathlib.CategoryTheory.Localization.Monoidal.Braided

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_50_1 (from Chap20) -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [SymmetricCategory (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (RingedSpace.Modules X), GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ ℱ : (RingedSpace.Modules X),
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X)) ((curriedTensor (RingedSpace.Modules X)).obj ℱ)]
variable [∀ ℱ : (RingedSpace.Modules X),
  PreservesColimit (Functor.empty.{0} (RingedSpace.Modules X)) ((curriedTensor (RingedSpace.Modules X)).flip.obj ℱ)]

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ

/- Domain-style sampling for Lemma 20.50.1:
- primary domain: symmetric monoidal structures on cochain complexes, specialized to
  `\mathcal O_X`-modules on a ringed space;
- sampled owner declarations:
  `MonoidalCategory (CochainComplex C ℤ)`,
  `BraidedCategory (CochainComplex C ℤ)`,
  `SymmetricCategory (CochainComplex C ℤ)`,
  `SymmetricCategory.ofFaithful`;
- best owner abstraction: the core owner is the ambient typeclass
  `SymmetricCategory (CochainComplex (RingedSpace.Modules X) ℤ)`, supplied in the project by Chapter 15's generic
  cochain-complex construction;
- primitive vs. derived: the primitive data are the monoidal and symmetric structures on
  `(RingedSpace.Modules X)`
  together with the tensor exactness hypotheses needed to build the complex tensor product. The
  symmetric structure on `CpxX` is derived owner API and should therefore be recalled directly,
  not reintroduced through a local wrapper or witness declaration.

Source/core/bridge triage:
- `source-facing`: Lemma 20.50.1, the ringed-space specialization of the tensor symmetry on
  complexes of modules;
- `core/canonical`: the chapter owner instance `SymmetricCategory (CochainComplex C ℤ)` from
  Lemma 15.58.1;
- `bridge/view`: the specialization from a general preadditive symmetric monoidal category `C` to
  `(RingedSpace.Modules X)`.
-/

/- Lemma 20.50.1: the category of complexes of `\mathcal O_X`-modules on a ringed space carries
the symmetric monoidal structure whose tensor product is the total complex
`\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X} \mathcal G^\bullet)`. In Lean, this is
the canonical `SymmetricCategory` instance on `CochainComplex (RingedSpace.Modules X) ℤ`, inherited from
the generic Chapter 15 owner for cochain complexes in any suitable symmetric monoidal preadditive
category. -/
#synth SymmetricCategory CpxX

end

end AlgebraicGeometry.RingedSpace

/-! ### Example_20_50_2 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ
local notation "OpenComplex" U => CochainComplex (openSubspaceModuleCategory X U) ℤ

/-- Restriction of cochain complexes of `\mathcal O_X`-modules to an open subspace. -/
private abbrev restrictionComplex (U : Opens X.carrier) :
    CpxX ⥤ OpenComplex U :=
  (moduleRestrictionToOpen X U).mapHomologicalComplex (ComplexShape.up ℤ)

/- 
Domain-style sampling for Example 20.50.2:
- primary domain: closed-monoidal duality for cochain complexes of `\mathcal O_X`-modules on a
  ringed space;
- inspected owner declarations:
  `CategoryTheory.ExactPairing`,
  `CategoryTheory.BraidedCategory.exactPairing_swap`,
  `unitInternalHomExactPairing`,
  `internalHomToUnit_exactPairing`,
  `ringedSiteModuleComplexDualExactPairing`;
- best owner abstraction: `CategoryTheory.ExactPairing` is the core owner for the left-dual datum,
  while `CochainComplex.IsLocallyStrictlyPerfect` is the source-facing local hypothesis;
- primitive data: the canonical internal-Hom object `(ihom F).obj (𝟙_ CpxX)`, the
  tensor-to-endomorphism comparison, and the canonical evaluation/coevaluation maps;
- derived API: the exact-pairing package and the downstream uniqueness isomorphism from an
  arbitrary chosen dual to the canonical internal-Hom dual.

Source/core/bridge triage:
- `source-facing`: `CochainComplex.IsLocallyStrictlyPerfect`;
- `core/canonical`: `CategoryTheory.ExactPairing`;
- `bridge/view`: `ringedSpaceModuleComplexDualExactPairing`.
-/

/-- A complex of `\mathcal O_X`-modules is locally strictly perfect if some open covering of `X`
has strictly perfect restrictions of the complex. -/
def CochainComplex.IsLocallyStrictlyPerfect (E : CpxX) : Prop :=
  ∃ (ι : Type u) (U : ι → Opens X.carrier),
    IsOpenCover U ∧
      ∀ i : ι,
        CochainComplex.IsStrictlyPerfect ((restrictionComplex (U i)).obj E)

-- Proof sketch: unfold `CochainComplex.IsLocallyStrictlyPerfect`; this is exactly the chosen
-- open-cover formulation saying that the restriction of `E` to each member of the cover is
-- strictly perfect.
/-- Unfolding `IsLocallyStrictlyPerfect` gives the open-cover criterion by strictly perfect
restrictions. -/
theorem cochainComplex_isLocallyStrictlyPerfect_iff
    (E : CpxX) :
    CochainComplex.IsLocallyStrictlyPerfect E ↔
      ∃ (ι : Type u) (U : ι → Opens X.carrier),
        IsOpenCover U ∧
          ∀ i : ι,
            CochainComplex.IsStrictlyPerfect ((restrictionComplex (U i)).obj E) :=
  Iff.rfl

section Duality

variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [BraidedCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSpace.Modules X) ℤ)]

/-- The canonical morphism
`K^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, K^\bullet)`. -/
noncomputable def ringedSpaceModuleComplexEvaluationHom
    (F K : CpxX) :
    K ⊗ (ihom F).obj (𝟙_ CpxX) ⟶ (ihom F).obj K :=
  (β_ K ((ihom F).obj (𝟙_ CpxX))).hom ≫
    ((ihom F).obj (𝟙_ CpxX) ◁ (unitIsoSelf K).symm.hom) ≫
    comp F (𝟙_ CpxX) K

/-- The canonical tensor-to-endomorphism morphism
`F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X) \to
\mathcal H\!\mathit{om}^\bullet(F^\bullet, F^\bullet)`. -/
noncomputable abbrev ringedSpaceModuleComplexDualTensorToEnd
    (F : CpxX) :
    F ⊗ (ihom F).obj (𝟙_ CpxX) ⟶ (ihom F).obj F :=
  ringedSpaceModuleComplexEvaluationHom F F

-- Proof sketch: the question is local on `X`. On each open of the chosen cover the restricted
-- complex is strictly perfect, so degreewise finite-free duality and Lemma `15.73.2` give the
-- tensor-to-endomorphism isomorphism for the restricted complex; then glue these local
-- isomorphisms back along the cover.
/-- The canonical tensor-to-endomorphism map is an isomorphism for a locally strictly perfect
complex. -/
theorem ringedSpaceModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect
    {F : CpxX} (hF : CochainComplex.IsLocallyStrictlyPerfect F) :
    IsIso (ringedSpaceModuleComplexDualTensorToEnd F) := sorry

/-- The evaluation morphism
`\mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X) \otimes F^\bullet \to \mathcal O_X`
for the internal-Hom dual complex. -/
noncomputable def ringedSpaceModuleComplexDualEvaluation
    (F : CpxX) :
    ((ihom F).obj (𝟙_ CpxX)) ⊗ F ⟶ 𝟙_ CpxX :=
  (β_ ((ihom F).obj (𝟙_ CpxX)) F).hom ≫
    MonoidalClosed.uncurry (𝟙 ((ihom F).obj (𝟙_ CpxX)))

/-- The coevaluation morphism
`\mathcal O_X \to F^\bullet \otimes \mathcal H\!\mathit{om}^\bullet(F^\bullet, \mathcal O_X)`
obtained from the identity of `F^\bullet` via the tensor-to-endomorphism isomorphism. -/
noncomputable def ringedSpaceModuleComplexDualCoevaluation
    (F : CpxX)
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    𝟙_ CpxX ⟶ F ⊗ (ihom F).obj (𝟙_ CpxX) :=
  MonoidalClosed.curry' (𝟙 F) ≫
    inv (ringedSpaceModuleComplexDualTensorToEnd F)

-- Proof sketch: transport the identity endomorphism of the dual complex across the adjunction
-- defining `ringedSpaceModuleComplexDualCoevaluation`. After applying the tensor-to-endomorphism
-- isomorphism, the composite becomes the identity, which is exactly the first triangle identity.
/-- The coevaluation and evaluation maps satisfy the first triangle identity. -/
theorem ringedSpaceModuleComplexDual_coevaluation_evaluation
    {F : CpxX}
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    ((ihom F).obj (𝟙_ CpxX)) ◁ ringedSpaceModuleComplexDualCoevaluation F ≫
        (α_ _ _ _).inv ≫
        ringedSpaceModuleComplexDualEvaluation F ▷ (ihom F).obj (𝟙_ CpxX) =
      (ρ_ ((ihom F).obj (𝟙_ CpxX))).hom ≫
        (λ_ ((ihom F).obj (𝟙_ CpxX))).inv := sorry

-- Proof sketch: similarly, transport the identity of `F^\bullet` across the same
-- tensor-to-endomorphism isomorphism. The defining property of
-- `ringedSpaceModuleComplexDualCoevaluation` then yields the second triangle identity.
/-- The coevaluation and evaluation maps satisfy the second triangle identity. -/
theorem ringedSpaceModuleComplexDual_evaluation_coevaluation
    {F : CpxX}
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    ringedSpaceModuleComplexDualCoevaluation F ▷ F ≫
        (α_ _ _ _).hom ≫
        F ◁ ringedSpaceModuleComplexDualEvaluation F =
      (λ_ F).hom ≫ (ρ_ F).inv := sorry

/-- The internal-Hom dual, together with the canonical coevaluation and evaluation maps, gives a
chosen left dual whenever the tensor-to-endomorphism comparison is an isomorphism. -/
@[reducible] private noncomputable def ringedSpaceModuleComplexDualExactPairingOfIsIso
    (F : CpxX)
    [IsIso (ringedSpaceModuleComplexDualTensorToEnd F)] :
    ExactPairing ((ihom F).obj (𝟙_ CpxX)) F :=
  letI : ExactPairing F ((ihom F).obj (𝟙_ CpxX)) :=
    { coevaluation' := ringedSpaceModuleComplexDualCoevaluation F
      evaluation' := ringedSpaceModuleComplexDualEvaluation F
      coevaluation_evaluation' := ringedSpaceModuleComplexDual_coevaluation_evaluation
      evaluation_coevaluation' := ringedSpaceModuleComplexDual_evaluation_coevaluation }
  BraidedCategory.exactPairing_swap F ((ihom F).obj (𝟙_ CpxX))

/-- Example 20.50.2: if `\mathcal F^\bullet` is locally strictly perfect on the ringed space
`(X, \mathcal O_X)`, then the internal-Hom dual
`\mathcal G^\bullet = \mathcal H\!\mathit{om}^\bullet(\mathcal F^\bullet, \mathcal O_X)`,
together with the canonical coevaluation and evaluation morphisms
`\eta : \mathcal O_X \to \mathrm{Tot}(\mathcal F^\bullet \otimes \mathcal G^\bullet)` and
`\epsilon : \mathrm{Tot}(\mathcal G^\bullet \otimes \mathcal F^\bullet) \to \mathcal O_X`,
forms a left dual of `\mathcal F^\bullet`. In Lean this left-dual datum is packaged by
`CategoryTheory.ExactPairing`. -/
noncomputable abbrev ringedSpaceModuleComplexDualExactPairing
    {F : CpxX} (hF : CochainComplex.IsLocallyStrictlyPerfect F) :
    ExactPairing ((ihom F).obj (𝟙_ CpxX)) F :=
  letI : IsIso (ringedSpaceModuleComplexDualTensorToEnd F) :=
    ringedSpaceModuleComplexDualTensorToEnd_isIso_of_isLocallyStrictlyPerfect hF
  ringedSpaceModuleComplexDualExactPairingOfIsIso F

end Duality

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_50_3 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [BraidedCategory (CochainComplex (RingedSpace.Modules X) ℤ)]
variable [MonoidalClosed (CochainComplex (RingedSpace.Modules X) ℤ)]

local notation "CpxX" => CochainComplex (RingedSpace.Modules X) ℤ

-- Proof sketch: write the coevaluation and evaluation of the chosen left dual degreewise. The
-- triangle identities show that each term `F.X n` is locally a retract of a finite free
-- `\mathcal O_X`-module, by the module-sheaf lemma `17.18.2` applied in every degree. The
-- coevaluation is locally a finite sum, so only finitely many degrees occur near each point,
-- giving local boundedness; combine these two pieces into local strict perfectness.
/-- Lemma 20.50.3: if a complex `F^\bullet` of `\mathcal O_X`-modules has a left dual in the
monoidal category of complexes, then `F^\bullet` is locally strictly perfect. Equivalently, near
every point it is bounded and each term is a direct summand of a finite free `\mathcal O_X`
module. -/
theorem exactPairing_isLocallyStrictlyPerfect
    {F G : CpxX} (hpair : ExactPairing F G) :
    CochainComplex.IsLocallyStrictlyPerfect F := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_50_4 (from Chap20) -/
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

-- Proof sketch: work locally on `X` using compatibility of both sides with localization. Replace
-- the perfect object `K` by a strictly perfect representative, then argue by distinguished
-- triangles and stupid truncations to reduce to a finite free module sheaf in one degree, where
-- the comparison is the evident isomorphism.
/-- Lemma 20.50.4: let `(X, \mathcal O_X)` be a ringed space and let `K`, `L`, `M ∈ D(\mathcal
O_X)`. If `K` is perfect, then the canonical map
`R\mathcal H\!\mathit{om}(L, M) \otimes_{\mathcal O_X}^{\mathbf L} K \to
R\mathcal H\!\mathit{om}(R\mathcal H\!\mathit{om}(K, L), M)` from Lemma `20.42.9` is an
isomorphism. -/
theorem isIso_tensorInternalHomToIteratedInternalHom_of_isPerfect
    {K L M : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (tensorInternalHomToIteratedInternalHom K L M) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_50_5 (from Chap20) -/
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

/-- The canonical bidual morphism `K ⟶ (K^∨)^∨` in `D(\mathcal O_X)`, obtained by currying the
evaluation map `K^∨ ⊗ K ⟶ \mathcal O_X`. -/
noncomputable def ringedSpaceDerivedBidualMap
    (K : DMod) :
    K ⟶ ringedSpaceDerivedDual (ringedSpaceDerivedDual K) :=
  MonoidalClosed.curry
    ((β_ (ringedSpaceDerivedDual K) K).hom ≫
      MonoidalClosed.uncurry (𝟙 (ringedSpaceDerivedDual K)))

-- Proof sketch: work locally on `X` and replace `K` by a strictly perfect representative. The
-- termwise dual complex is again strictly perfect, hence represents the derived dual, so the dual
-- object is perfect locally and therefore perfect.
/-- Lemma 20.50.5 (1): if `K` is a perfect object of `D(\mathcal O_X)`, then its derived dual
`K^∨ = R\mathcal H\!\mathit{om}(K, \mathcal O_X)` is perfect. -/
theorem isPerfect_derivedDual_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    DerivedCategory.IsPerfect (ringedSpaceDerivedDual K) := sorry

-- Proof sketch: apply Lemma `20.50.4` with `L = \mathcal O_X` and `M = \mathcal O_X` to see that
-- the tensor-to-iterated-internal-Hom comparison for `K` is an isomorphism. Under the
-- tensor-internal-Hom adjunction, this comparison is exactly the canonical bidual morphism.
/-- Lemma 20.50.5 (2): if `K` is a perfect object of `D(\mathcal O_X)`, then the canonical
bidual morphism `K ⟶ (K^∨)^∨` is an isomorphism, so `(K^∨)^∨` is canonically isomorphic to
`K`. -/
theorem isIso_ringedSpaceDerivedBidualMap_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedBidualMap K) := sorry

-- Proof sketch: this is exactly Lemma `20.50.4` specialized to `L = \mathcal O_X`, since
-- `K^∨ = R\mathcal H\!\mathit{om}(K, \mathcal O_X)` and
-- `M ⊗_{\mathcal O_X}^{\mathbf L} K^∨ ⟶ R\mathcal H\!\mathit{om}(K, M)` is the canonical map of
-- Lemma `20.42.8`.
/-- Lemma 20.50.5 (3): if `K` is a perfect object of `D(\mathcal O_X)`, then for every
`M ∈ D(\mathcal O_X)` the canonical morphism
`M \otimes_{\mathcal O_X}^{\mathbf L} K^∨ ⟶ R\mathcal H\!\mathit{om}(K, M)` is an
isomorphism. -/
theorem isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect
    {K M : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedEvaluationHom K M) := sorry

-- Proof sketch: the map on `H^0(X, -)` is induced by the canonical morphism of part `(3)`. Since
-- that morphism is an isomorphism for perfect `K`, taking degree-zero global sections gives a
-- bijection with `Hom_{D(\mathcal O_X)}(K, M)`.
/-- Lemma 20.50.5 (4): if `K` is a perfect object of `D(\mathcal O_X)`, then for every
`M ∈ D(\mathcal O_X)` the canonical map
`H^0(X, M \otimes_{\mathcal O_X}^{\mathbf L} K^∨) \to \operatorname{Hom}_{D(\mathcal O_X)}(K, M)`
is bijective. In Lean, `H^0(X, -)` is modeled by morphisms from the monoidal unit
`\mathcal O_X`. -/
theorem bijective_ringedSpaceDerivedEvaluationH0ToHom_of_isPerfect
    {K M : DMod} (hK : DerivedCategory.IsPerfect K) :
    Function.Bijective (ringedSpaceDerivedEvaluationH0ToHom K M) := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_50_6 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

attribute [local instance] HasDerivedCategory.standard
set_option checkBinderAnnotations false

section

/-
Domain-style sampling for Lemma 20.50.6:
- primary domain: localization of symmetric monoidal homotopy categories to derived categories of
  `\mathcal O_X`-modules on a ringed space;
- sampled owner declarations:
  `CategoryTheory.LocalizedMonoidal`,
  `CategoryTheory.Localization.Monoidal.toMonoidalCategory`,
  `CategoryTheory.Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal`,
  `CategoryTheory.derivedCategory_moduleCat_symmetricCategory`,
  `CategoryTheory.SymmetricCategory`;
- best owner abstraction: the public owner is the `SymmetricCategory` structure on
  `DerivedCategory (RingedSpace.Modules X)`, obtained from the canonical localization functor
  `DerivedCategory.Qh : K(X) ⥤ D(X)` by transporting the owner instance on `LocalizedMonoidal`;
- primitive data: the ringed space `X`, the homotopy category `K(X)`, the derived category
  `D(X)`, and the monoidal stability of quasi-isomorphisms in `K(X)`;
- derived API: the public owner is the localized symmetric structure on `D(X)`; its monoidal
  superclass is still needed explicitly so the symmetric instance can be stated on the owner type.

Layer triage:
- `source-facing`: the symmetric monoidal structure on `D(\mathcal O_X)`;
- `core/canonical`: `DerivedCategory (RingedSpace.Modules X)` together with `LocalizedMonoidal`;
- `bridge/view`: any later comparison with a source-facing derived tensor-product owner belongs in
  a separate bridge file, not in the public owner API here.
-/

variable {X : RingedSpace.{u}}
variable [CategoryWithHomology (RingedSpace.Modules X)]
local notation "KMod" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)
variable [MonoidalCategory (HomotopyCategory (RingedSpace.Modules X) (up ℤ))]
variable [SymmetricCategory (HomotopyCategory (RingedSpace.Modules X) (up ℤ))]

-- Proof sketch: quasi-isomorphisms in `K(\mathcal O_X)` are detected on homology, and the tensor
-- product on the homotopy category is induced by the symmetric monoidal tensor product on cochain
-- complexes. Tensoring two quasi-isomorphisms therefore again yields a quasi-isomorphism.
/-- Quasi-isomorphisms in the homotopy category of `\mathcal O_X`-module complexes are stable
under tensor product. -/
private theorem homotopyCategory_quasiIso_isMonoidal :
    (Qis).IsMonoidal := by
  sorry

/-- The monoidal category structure on `D(\mathcal O_X)` obtained by localizing the tensor product
on the homotopy category of complexes of `\mathcal O_X`-modules. -/
noncomputable instance : MonoidalCategory DMod := by
  let _ : (Qis).IsMonoidal := homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : MonoidalCategory
      (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (𝟙_ KMod)))))

/-- Lemma 20.50.6: the derived category `D(\mathcal O_X)` inherits a symmetric monoidal
structure by localizing the symmetric monoidal structure on the homotopy category of complexes of
`\mathcal O_X`-modules, with the usual associativity and commutativity constraints. -/
noncomputable instance : SymmetricCategory DMod := by
  let _ : (Qis).IsMonoidal := homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance : SymmetricCategory
      (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (𝟙_ KMod)))))

end

end AlgebraicGeometry.RingedSpace

/-! ### Example_20_50_7 (from Chap20) -/
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

/-- The canonical morphism
`K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee \to R\mathcal H\!\mathit{om}(K, K)` attached to the
derived dual `K^\vee = R\mathcal H\!\mathit{om}(K, \mathcal O_X)`. -/
noncomputable abbrev ringedSpaceDerivedDualTensorToEnd
    (K : DMod) :
    K ⊗ ringedSpaceDerivedDual K ⟶ (ihom K).obj K :=
  ringedSpaceDerivedEvaluationHom K K

-- Proof sketch: this is Lemma `20.50.5 (3)` specialized to `M = K`: for a perfect object, the
-- canonical tensor-to-internal-Hom comparison is an isomorphism, hence in particular so is the
-- tensor-to-endomorphism morphism.
/-- For a perfect object, the canonical morphism
`K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee \to R\mathcal H\!\mathit{om}(K, K)` is an
isomorphism. -/
theorem ringedSpaceDerivedDualTensorToEnd_isIso_of_isPerfect
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    IsIso (ringedSpaceDerivedDualTensorToEnd K) := by
  simpa [ringedSpaceDerivedDualTensorToEnd] using
    isIso_ringedSpaceDerivedEvaluationHom_of_isPerfect (K := K) (M := K) hK

/-- The evaluation morphism
`\epsilon : K^\vee \otimes_{\mathcal O_X}^{\mathbf L} K \to \mathcal O_X`. -/
noncomputable def ringedSpaceDerivedDualEvaluation
    (K : DMod) :
    ringedSpaceDerivedDual K ⊗ K ⟶ 𝟙_ DMod :=
  (β_ (ringedSpaceDerivedDual K) K).hom ≫
    MonoidalClosed.uncurry (𝟙 (ringedSpaceDerivedDual K))

/-- The coevaluation morphism
`\eta : \mathcal O_X \to K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee` corresponding to
`\mathrm{id}_K` under the tensor-to-endomorphism isomorphism. -/
noncomputable def ringedSpaceDerivedDualCoevaluation
    (K : DMod)
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    𝟙_ DMod ⟶ K ⊗ ringedSpaceDerivedDual K :=
  MonoidalClosed.curry' (𝟙 K) ≫
    inv (ringedSpaceDerivedDualTensorToEnd K)

-- Proof sketch: transport the identity morphism of `K^\vee` across the adjunction defining
-- `ringedSpaceDerivedDualCoevaluation`. After composing with the inverse of the
-- tensor-to-endomorphism isomorphism, the composite reduces to the first triangle identity.
/-- The derived coevaluation and evaluation maps satisfy the first triangle identity. -/
theorem ringedSpaceDerivedDual_coevaluation_evaluation
    {K : DMod}
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    ringedSpaceDerivedDual K ◁ ringedSpaceDerivedDualCoevaluation K ≫
        (α_ _ _ _).inv ≫
        ringedSpaceDerivedDualEvaluation K ▷ ringedSpaceDerivedDual K =
      (ρ_ (ringedSpaceDerivedDual K)).hom ≫
        (λ_ (ringedSpaceDerivedDual K)).inv := sorry

-- Proof sketch: transport the identity morphism of `K` through the same tensor-to-endomorphism
-- isomorphism. The adjunction formulas for `curry'` and `uncurry` then give the second triangle
-- identity.
/-- The derived coevaluation and evaluation maps satisfy the second triangle identity. -/
theorem ringedSpaceDerivedDual_evaluation_coevaluation
    {K : DMod}
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    ringedSpaceDerivedDualCoevaluation K ▷ K ≫
        (α_ _ _ _).hom ≫
        K ◁ ringedSpaceDerivedDualEvaluation K =
      (λ_ K).hom ≫ (ρ_ K).inv := sorry

/-- The derived dual together with the canonical coevaluation and evaluation maps gives a left
dual once the tensor-to-endomorphism morphism is an isomorphism. -/
@[reducible] noncomputable def ringedSpaceDerivedDualExactPairingOfIsIso
    (K : DMod)
    [IsIso (ringedSpaceDerivedDualTensorToEnd K)] :
    ExactPairing K (ringedSpaceDerivedDual K) :=
  { coevaluation' := ringedSpaceDerivedDualCoevaluation K
    evaluation' := ringedSpaceDerivedDualEvaluation K
    coevaluation_evaluation' := ringedSpaceDerivedDual_coevaluation_evaluation
    evaluation_coevaluation' := ringedSpaceDerivedDual_evaluation_coevaluation }

/-- Example 20.50.7: if `K` is a perfect object of `D(\mathcal O_X)`, then the derived dual
`K^\vee = R\mathcal H\!\mathit{om}(K, \mathcal O_X)`, together with the coevaluation
`\eta : \mathcal O_X \to K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee` corresponding to
`\mathrm{id}_K` under the isomorphism
`K \otimes_{\mathcal O_X}^{\mathbf L} K^\vee \cong R\mathcal H\!\mathit{om}(K, K)` and the
evaluation map `\epsilon : K^\vee \otimes_{\mathcal O_X}^{\mathbf L} K \to \mathcal O_X`, is a
left dual of `K`. In Lean this left-duality datum is packaged by
`CategoryTheory.ExactPairing`. -/
noncomputable abbrev ringedSpaceDerivedDualExactPairing
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    ExactPairing K (ringedSpaceDerivedDual K) :=
  letI : IsIso (ringedSpaceDerivedDualTensorToEnd K) :=
    ringedSpaceDerivedDualTensorToEnd_isIso_of_isPerfect hK
  ringedSpaceDerivedDualExactPairingOfIsIso K

-- Proof sketch: unfold `ringedSpaceDerivedDualExactPairing`; after introducing the local `IsIso`
-- instance coming from perfectness, the coevaluation field of the packaged `ExactPairing` is
-- definitionally `ringedSpaceDerivedDualCoevaluation K`.
/-- The coevaluation of the exact pairing from Example 20.50.7 is the canonical coevaluation map
attached to the derived dual. -/
theorem ringedSpaceDerivedDualExactPairing_coevaluation
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    letI : IsIso (ringedSpaceDerivedDualTensorToEnd K) :=
      ringedSpaceDerivedDualTensorToEnd_isIso_of_isPerfect hK
    @ExactPairing.coevaluation _ _ _ K (ringedSpaceDerivedDual K)
        (ringedSpaceDerivedDualExactPairing hK) =
      ringedSpaceDerivedDualCoevaluation K := sorry

-- Proof sketch: unfold `ringedSpaceDerivedDualExactPairing`; the evaluation field of the
-- packaged `ExactPairing` is definitionally `ringedSpaceDerivedDualEvaluation K`.
/-- The evaluation of the exact pairing from Example 20.50.7 is the canonical evaluation map
attached to the derived dual. -/
theorem ringedSpaceDerivedDualExactPairing_evaluation
    {K : DMod} (hK : DerivedCategory.IsPerfect K) :
    @ExactPairing.evaluation _ _ _ K (ringedSpaceDerivedDual K)
        (ringedSpaceDerivedDualExactPairing hK) =
      ringedSpaceDerivedDualEvaluation K := sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_50_8 (from Chap20) -/
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

-- Proof sketch: this is the derived-category analogue of the module statement from
-- `Lemma 15.127.3`. Starting from a left dual pairing, the textbook proof factors the
-- coevaluation through a bounded flat subcomplex, showing that `M` is a retract of an object with
-- finite tor amplitude; then the pseudo-coherence induction of Lemma `20.49.4` upgrades this to
-- perfection.
/-- Lemma 20.50.8: if an object `M` of `D(\mathcal O_X)` has a left dual in the monoidal
category `D(\mathcal O_X)`, then `M` is perfect. -/
theorem exactPairing_isPerfect
    {M N : DMod} (hpair : ExactPairing M N) :
    DerivedCategory.IsPerfect M := sorry

/-- The unique isomorphism from a chosen left dual of `M` in `D(\mathcal O_X)` to the canonical
derived dual `R\mathcal H\!\mathit{om}(M, \mathcal O_X)` from Example `20.50.7`. This is the
textbook identification of an arbitrary left dual with the one constructed there. -/
noncomputable def exactPairing_rightDualIso_ringedSpaceDerivedDual
    {M N : DMod} (hpair : ExactPairing M N) :
    N ≅ ringedSpaceDerivedDual M :=
  rightDualIso hpair (ringedSpaceDerivedDualExactPairing (exactPairing_isPerfect hpair))

end

end AlgebraicGeometry.RingedSpace
