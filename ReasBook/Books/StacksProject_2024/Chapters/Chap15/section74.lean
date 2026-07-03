import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_74_1 (from Chap15) -/
noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom
open scoped DerivedTensorProduct

/- Domain-style sampling for Lemma 15.74.1:
- primary domain: tensor/internal-Hom currying in the closed monoidal derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.derivedCategory_tensorObj_iso_derivedTensorProduct`,
  `CategoryTheory.tensoringRightIsoDerivedTensorProduct`,
  `CategoryTheory.Adjunction.rightAdjointUniq`;
  `source-facing`: the textbook objectwise currying isomorphism
    `RHom_R(K, RHom_R(L, M)) ≅ RHom_R(K ⊗^L_R L, M)`;
  `core/canonical`: a chosen owner `H : MonoidalClosed DMod`, together with the canonical
    internal Hom functors `ihom K` and the derived tensor functors `derivedTensorProduct K`;
  `bridge/view`: the comparison isomorphism between iterated fixed-right-factor derived tensoring
    and tensoring by the derived tensor product `K ⊗[R]^L L`, reused from the upstream bridge
    `derivedTensorProductTensorIso`, and the resulting functor-level right-adjoint uniqueness
    isomorphism.
- primitive data: only the owner `H : MonoidalClosed DMod`;
- derived API: the objectwise textbook isomorphism and its naturality squares; the functor-level
  uniqueness isomorphism is only an internal bridge.

Source/core/bridge triage:
- `source-facing`: `derivedInternalHomTensorIso`;
- `core/canonical`: `H.derivedTensorAdj`, `ihom`, and the monoidal coherence isomorphisms on
  `D(R)`;
- `bridge/view`: the upstream tensor-functor comparison `derivedTensorProductTensorIso`, used to
  transport the composite adjunction to the source-facing derived tensor notation, together with
  the private functor-level right-adjoint-uniqueness isomorphism whose component at `M` is
  `derivedInternalHomTensorIso`. -/

private noncomputable def derivedInternalHomTensorNatIso
    (H : RHomPkg) (K L : DMod) :
    letI := H
    ihom L ⋙ ihom K ≅ ihom (K ⊗[R]^L L) :=
  letI := H
  (Adjunction.rightAdjointUniq
      (H.derivedTensorAdj (K ⊗[R]^L L))
      (((H.derivedTensorAdj K).comp (H.derivedTensorAdj L)).ofNatIsoLeft
        (derivedTensorProductTensorIso K L))).symm

/-- Lemma 15.74.1: for a chosen derived internal Hom on `D(R)` and objects `K`, `L`, `M`, there is
a canonical isomorphism
`R\mathrm{Hom}_R(K, R\mathrm{Hom}_R(L, M)) \cong
R\mathrm{Hom}_R(K \otimes_R^{\mathbf L} L, M)`,
functorial in `K`, `L`, and `M`. This is the component at `M` of the canonical right-adjoint
uniqueness isomorphism comparing `ihom L ⋙ ihom K` with `ihom (K ⊗[R]^L L)`. -/
noncomputable def derivedInternalHomTensorIso
    (H : RHomPkg) (K L M : DMod) :
    RHom[H](K, (RHom[H](L, M))) ≅ RHom[H]((K ⊗[R]^L L), M) :=
  (derivedInternalHomTensorNatIso H K L).app M

private theorem derivedInternalHomTensorNatIso_natural_left
    (H : RHomPkg) {K₁ K₂ L : DMod} (f : K₁ ⟶ K₂) :
    letI := H
    Functor.whiskerLeft (ihom L) (MonoidalClosed.pre f) ≫
        (derivedInternalHomTensorNatIso H K₁ L).hom =
      (derivedInternalHomTensorNatIso H K₂ L).hom ≫
        MonoidalClosed.pre ((derivedTensorProduct L).map f) := by
  sorry

private theorem derivedInternalHomTensorNatIso_natural_middle
    (H : RHomPkg) (K : DMod) {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    letI := H
    Functor.whiskerRight (MonoidalClosed.pre f) (ihom K) ≫
        (derivedInternalHomTensorNatIso H K L₁).hom =
      (derivedInternalHomTensorNatIso H K L₂).hom ≫
        MonoidalClosed.pre ((derivedTensorProductMap H f).app K) := by
  sorry

/-- Lemma 15.74.1 is contravariantly natural in the first variable `K`. -/
theorem derivedInternalHomTensorIso_natural_left
    (H : RHomPkg) {K₁ K₂ L M : DMod} (f : K₁ ⟶ K₂) :
    CommSq
      (derivedInternalHomMap H f (𝟙 (RHom[H](L, M))))
      (derivedInternalHomTensorIso H K₂ L M).hom
      (derivedInternalHomTensorIso H K₁ L M).hom
      (derivedInternalHomMap H ((derivedTensorProduct L).map f) (𝟙 M)) := by
  letI : RHomPkg := H
  refine ⟨?_⟩
  simpa [derivedInternalHomMap, derivedInternalHomTensorIso] using
    NatTrans.congr_app (derivedInternalHomTensorNatIso_natural_left H f) M

/-- Lemma 15.74.1 is contravariantly natural in the middle variable `L`. -/
theorem derivedInternalHomTensorIso_natural_middle
    (H : RHomPkg) (K : DMod) {L₁ L₂ M : DMod} (f : L₁ ⟶ L₂) :
    CommSq
      (derivedInternalHomMap H (𝟙 K) (derivedInternalHomMap H f (𝟙 M)))
      (derivedInternalHomTensorIso H K L₂ M).hom
      (derivedInternalHomTensorIso H K L₁ M).hom
      (derivedInternalHomMap H ((derivedTensorProductMap H f).app K) (𝟙 M)) := by
  letI : RHomPkg := H
  refine ⟨?_⟩
  simpa [derivedInternalHomMap, derivedInternalHomTensorIso] using
    NatTrans.congr_app (derivedInternalHomTensorNatIso_natural_middle H K f) M

/-- Lemma 15.74.1 is functorial in the target variable `M`. -/
theorem derivedInternalHomTensorIso_natural_right
    (H : RHomPkg) (K L : DMod) {M₁ M₂ : DMod} (f : M₁ ⟶ M₂) :
    CommSq
      (derivedInternalHomMap H (𝟙 K) (derivedInternalHomMap H (𝟙 L) f))
      (derivedInternalHomTensorIso H K L M₁).hom
      (derivedInternalHomTensorIso H K L M₂).hom
      (derivedInternalHomMap H (𝟙 (K ⊗[R]^L L)) f) := by
  letI : RHomPkg := H
  refine ⟨?_⟩
  simpa [derivedInternalHomMap, derivedInternalHomTensorIso] using
    (derivedInternalHomTensorNatIso H K L).hom.naturality f

end

end CategoryTheory

/-! ### Lemma_15_74_2 (from Chap15) -/
open CategoryTheory ComplexShape DerivedCategory HomotopyCategory
open CochainComplex.HomComplex.CohomologyClass

noncomputable section

universe v u

attribute [local instance] HasDerivedCategory.standard

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

local notation "KQ" => HomotopyCategory.quotient 𝒜 (up ℤ)

namespace CochainComplex

/- Domain-style sampling:
- primary domain: bounded-above projective cochain complexes in an abelian category and their
  derived-category `Ext` computation via shifted morphisms;
- sampled owner declarations:
  `ShiftedHom`,
  `CochainComplex.ProjectiveMinus`,
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`,
  `DerivedCategory.Q.commShiftIso`,
  `CochainComplex.HomComplex.homologyAddEquiv`,
  `CochainComplex.HomComplex.CohomologyClass.homAddEquiv`;
- best owner abstraction: the source-side bounded-above/projective owner is
  `CochainComplex.ProjectiveMinus 𝒜`; its canonical bridge to the derived category is the Chapter
  13 owner theorem
  `CochainComplex.homotopyCategory_to_derived_bijective_of_boundedAbove_projective`, while
  `ShiftedHom (Q.obj P) (Q.obj L) n` is the canonical shifted-Hom owner on the derived-category
  side;
- source/core/bridge triage:
  `source-facing`: the textbook identification
  `H^n(Hom^•(P^•, L^•)) ≃ Hom_D(P^•, L^•[n])`;
  `core/canonical`: `ProjectiveMinus`, `Qh.mapAddHom`, `Q.commShiftIso`, and `ShiftedHom`;
  `bridge/view`: the direct composite from Hom-complex cohomology classes to homotopy morphisms,
  then to derived morphisms out of the owner `ProjectiveMinus 𝒜`.

This file should therefore keep only the source-facing bridge at the abelian-category owner level,
not a duplicate projective-resolution wrapper around the same owner data. -/

namespace ProjectiveMinus

private noncomputable def isoHomCongrAddEquiv
    {C : Type*} [Category C] [Preadditive C] {X Y X₁ Y₁ : C} (α : X ≅ X₁) (β : Y ≅ Y₁) :
    (X ⟶ Y) ≃+ (X₁ ⟶ Y₁) where
  toEquiv := α.homCongr β
  map_add' := by
    intro f g
    simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

private noncomputable def homotopyShiftedHomAddEquiv
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) (n : ℤ) :
    ((KQ).obj P ⟶ (KQ).obj (L⟦n⟧)) ≃+ ShiftedHom (Q.obj P) (Q.obj L) n :=
  (AddEquiv.ofBijective
      (Qh.mapAddHom : ((KQ).obj P ⟶ (KQ).obj (L⟦n⟧)) →+ _)
      (homotopyCategory_to_derived_bijective_of_boundedAbove_projective P (L⟦n⟧))).trans
    (isoHomCongrAddEquiv (Iso.refl _) ((Q.commShiftIso n).app L))

/- Lemma 15.74.2: if `P^•` is a bounded-above cochain complex of projective objects in an
abelian category `𝒜` and `L^•` is any cochain complex in `𝒜`, then the complex
`Hom^•(P^•, L^•)` computes the derived Hom from `P^•` to shifts of `L^•`; in degree `n` its
cohomology identifies with morphisms `P^• ⟶ L^•[n]` in the derived category `D(𝒜)` as an
additive equivalence. This is exactly the canonical composite of the Hom-complex cohomology
bridge, the owner bijectivity theorem for `ProjectiveMinus 𝒜`, and the derived shift
identification. -/
noncomputable def homologyAddEquivShiftedHom
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) (n : ℤ) :
    (HomComplex P L).homology n ≃+ ShiftedHom (Q.obj P) (Q.obj L) n
  :=
  ((HomComplex.homologyAddEquiv P L n).trans homAddEquiv).trans
    (homotopyShiftedHomAddEquiv P L n)

end ProjectiveMinus

end CochainComplex

end

/-! ### Lemma_15_74_3 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom
open scoped DerivedTensorProduct

/-
Domain-style sampling for Lemma 15.74.3:
- primary domain: tensor/internal-Hom comparison morphisms on `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.derivedInternalHom_comp`,
  `CategoryTheory.MonoidalClosed.compTranspose`,
  `CategoryTheory.derivedTensorProduct_associator`,
  `CategoryTheory.derivedTensorProduct_comm`;
- best owner abstraction:
  `source-facing`: the canonical tensor-right comparison morphism
  `RHom_R(L, M) ⊗^L_R K ⟶ RHom_R(RHom_R(K, L), M)`;
  `core/canonical`: the owner `H : MonoidalClosed DMod`, together with the established tensor owner
  `derivedTensorProduct`;
  `bridge/view`: the adjoint transpose of the composition-evaluation composite below;
- primitive data: the chosen monoidal-closed owner `H`, the canonical composition morphism
  `derivedInternalHom_comp`, and the tensor associativity/commutativity isomorphisms;
- derived API: the tensor-right comparison map itself and its naturality in `K`, `L`, and `M`.

The source-facing owner here is therefore a single canonical comparison morphism, not the full
type of arbitrary natural transformations between the associated trivariant functors.
-/

private noncomputable def derivedInternalHom_tensor_right_comparisonTranspose
    (H : RHomPkg) (K L M : DMod) :
    ((RHom[H](L, M) ⊗[R]^L K) ⊗[R]^L (RHom[H](K, L))) ⟶ M :=
  let _ : RHomPkg := H
  (derivedTensorProduct_associator (RHom[H](L, M)) K (RHom[H](K, L))).hom ≫
      (derivedTensorProductMap H ((derivedTensorProduct_comm K (RHom[H](K, L))).hom)).app
        (RHom[H](L, M)) ≫
    (derivedTensorProduct_associator (RHom[H](L, M)) (RHom[H](K, L)) K).inv ≫
      (derivedTensorProduct K).map (derivedInternalHom_comp H K L M) ≫
        (H.derivedTensorAdj K).counit.app M

-- Proof sketch: curry the composite
-- `((RHom_R(L, M) ⊗^L K) ⊗^L RHom_R(K, L)) ⟶ M`
-- obtained by swapping `K` and `RHom_R(K, L)`, composing
-- `RHom_R(L, M) ⊗^L RHom_R(K, L) ⟶ RHom_R(K, M)`, and then evaluating at `K`.
/-- Lemma 15.74.3: for a chosen derived internal Hom on `D(R)`, there is a canonical morphism
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} K \to
R\mathrm{Hom}_R(R\mathrm{Hom}_R(K, L), M)` in `D(R)`. -/
noncomputable def derivedInternalHom_tensor_right_comparison
    (H : RHomPkg) (K L M : DMod) :
    (RHom[H](L, M) ⊗[R]^L K) ⟶ RHom[H](RHom[H](K, L), M) :=
  let _ : RHomPkg := H
  (H.derivedTensorAdj (RHom[H](K, L))).homEquiv _ _
    (derivedInternalHom_tensor_right_comparisonTranspose H K L M)

-- Proof sketch: this is immediate from the definition as the adjoint transpose of
-- `derivedInternalHom_tensor_right_comparisonTranspose`.
/-- Applying the inverse adjunction equivalence to the tensor-right comparison recovers the
defining composition-evaluation transpose. -/
theorem derivedInternalHom_tensor_right_comparison_def
    (H : RHomPkg) (K L M : DMod) :
    ((H.derivedTensorAdj (RHom[H](K, L))).homEquiv _ _).symm
        (derivedInternalHom_tensor_right_comparison H K L M) =
      derivedInternalHom_tensor_right_comparisonTranspose H K L M := by
  sorry

-- Proof sketch: both sides are mates, under
-- `- ⊗^L_R RHom_R(K₂, L) ⊣ RHom_R(RHom_R(K₂, L), -)`, of the same morphism built from the
-- functoriality of the tensor factor `K` and the composition map `derivedInternalHom_comp`.
/-- The tensor-right comparison is natural in the tensor factor `K`. -/
theorem derivedInternalHom_tensor_right_comparison_natural_tensor
    (H : RHomPkg)
    {K₁ K₂ L M : DMod} (fK : K₁ ⟶ K₂) :
    CommSq
      ((derivedTensorProductMap H fK).app (RHom[H](L, M)))
      (derivedInternalHom_tensor_right_comparison H K₁ L M)
      (derivedInternalHom_tensor_right_comparison H K₂ L M)
      (derivedInternalHomMap H (derivedInternalHomMap H fK (𝟙 L)) (𝟙 M)) := by
  sorry

-- Proof sketch: both composites are mates of the same map out of
-- `((RHom_R(L₁, M) ⊗^L K) ⊗^L RHom_R(K, L₁))`, comparing the route that first changes `L`
-- inside `RHom_R(L, M)` with the route that first changes the argument `RHom_R(K, L)` of the
-- outer internal Hom.
/-- The tensor-right comparison is contravariantly natural in the source variable `L` of the
inner internal Hom. -/
theorem derivedInternalHom_tensor_right_comparison_natural_source
    (H : RHomPkg) (K : DMod)
    {L₁ L₂ M : DMod} (fL : L₁ ⟶ L₂) :
    CommSq
      ((derivedTensorProduct K).map (derivedInternalHomMap H fL (𝟙 M)))
      (derivedInternalHom_tensor_right_comparison H K L₂ M)
      (derivedInternalHom_tensor_right_comparison H K L₁ M)
      (derivedInternalHomMap H (derivedInternalHomMap H (𝟙 K) fL) (𝟙 M)) := by
  sorry

-- Proof sketch: both sides are mates, under
-- `- ⊗^L_R RHom_R(K, L) ⊣ RHom_R(RHom_R(K, L), -)`, of the map obtained by functoriality of
-- `RHom_R(L, -)` in the target variable `M`.
/-- The tensor-right comparison is natural in the target variable `M`. -/
theorem derivedInternalHom_tensor_right_comparison_natural_target
    (H : RHomPkg) (K L : DMod)
    {M₁ M₂ : DMod} (fM : M₁ ⟶ M₂) :
    CommSq
      ((derivedTensorProduct K).map (derivedInternalHomMap H (𝟙 L) fM))
      (derivedInternalHom_tensor_right_comparison H K L M₁)
      (derivedInternalHom_tensor_right_comparison H K L M₂)
      (derivedInternalHomMap H (𝟙 (RHom[H](K, L))) fM) := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_74_4 (from Chap15) -/
noncomputable section

open CategoryTheory
open Opposite
open CategoryTheory.MonoidalCategory
open BraidedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

open scoped DerivedTensorProduct

/-
Domain-style sampling for derived internal-Hom composition on `D(R)`:
- primary domain: closed symmetric monoidal structure on the derived category `D(R)`;
- sampled owner declarations:
  `CategoryTheory.derivedTensorProduct`,
  `CategoryTheory.MonoidalClosed.internalHom`,
  `CategoryTheory.MonoidalClosed.internalHomAdjunction₂`,
  `CategoryTheory.MonoidalClosed.comp`;
- best owner abstraction:
  `core/canonical`: the monoidal-closed owner `H : MonoidalClosed DMod`, together with
  `ihom`, `MonoidalClosed.pre`, and `MonoidalClosed.comp`;
  `source-facing`: the notation `RHom[H](K, L)` and the source-facing right-tensor adjunction
  `derivedTensorProduct L ⊣ RHom[H](L,-)`;
  `bridge/view`: the transported adjunction `H.derivedTensorAdj`, the tensor map
  `derivedTensorProductMap`, and the composition map `derivedInternalHom_comp`;
- primitive data: only the canonical owner `H : MonoidalClosed DMod`;
- derived API: the `RHom` notation and the bridge morphisms below.

This file therefore keeps the public API centered on `MonoidalClosed DMod`. The only local data
added here are thin source-facing bridges from the canonical owner tensor/internal-Hom structure to
the notation `- ⊗[R]^L L` and `RHom[H](K, L)`. The notation itself is defined directly over the
canonical internal-Hom owner `(ihom K).obj L`, not through a parallel wrapper declaration.
-/

namespace DerivedInternalHom

/- Textbook notation for the derived internal-Hom object `RHom_R(K, L)` in `D(R)`. -/
set_option quotPrecheck false in
scoped notation:70 "RHom[" H:70 "](" K:70 ", " L:70 ")" =>
  (letI := H
   (ihom K).obj L)

end DerivedInternalHom

open scoped DerivedInternalHom

namespace MonoidalClosed

/-- The source-facing adjunction
`- \otimes_R^{\mathbf L} L ⊣ R\mathrm{Hom}_R(L,-)`,
transported from the canonical left-tensor adjunction by the braiding on `D(R)` and the standard
comparison between the owner tensor and `⊗[R]^L`. -/
noncomputable def derivedTensorAdj
    (H : MonoidalClosed DMod)
    (L : DMod) :
    derivedTensorProduct L ⊣
      (let _ := H
       ihom L) := by
  letI := H
  exact
    ((ihom.adjunction L).ofNatIsoLeft (BraidedCategory.tensorLeftIsoTensorRight L)).ofNatIsoLeft
      (tensoringRightIsoDerivedTensorProduct L)

end MonoidalClosed

/-- The morphism on a chosen derived internal Hom induced contravariantly by a map on the source
object and covariantly by a map on the target object. -/
noncomputable def derivedInternalHomMap
    (H : MonoidalClosed DMod)
    {K₁ K₂ L₁ L₂ : DMod}
    (fK : K₂ ⟶ K₁) (fL : L₁ ⟶ L₂) :
    RHom[H](K₁, L₁) ⟶ RHom[H](K₂, L₂) :=
  letI := H
  (MonoidalClosed.pre fK).app L₁ ≫ (ihom K₂).map fL

/-- The natural transformation on derived tensor functors induced by a morphism of right tensor
factors, obtained as the adjoint mate of the corresponding map on derived internal-Hom functors.
-/
noncomputable def derivedTensorProductMap
    (H : MonoidalClosed DMod)
    {L₁ L₂ : DMod} (f : L₁ ⟶ L₂) :
    derivedTensorProduct L₁ ⟶ derivedTensorProduct L₂ :=
  letI := H
  (conjugateEquiv (H.derivedTensorAdj L₂) (H.derivedTensorAdj L₁)).symm
    (MonoidalClosed.pre f)

/-- Lemma 15.74.4: for a chosen monoidal-closed owner on `D(R)`, the canonical composition
morphism
`R\mathrm{Hom}_R(L, M) \otimes_R^{\mathbf L} R\mathrm{Hom}_R(K, L) \to
R\mathrm{Hom}_R(K, M)` is the canonical closed-monoidal composition map
`MonoidalClosed.comp`, transported to the source-facing derived tensor notation by the standard
tensor/derived-tensor comparison and the braiding on `D(R)`. -/
noncomputable def derivedInternalHom_comp
    (H : MonoidalClosed DMod)
    (K L M : DMod) :
    ((RHom[H](L, M)) ⊗[R]^L (RHom[H](K, L))) ⟶ RHom[H](K, M) :=
  letI := H
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      (RHom[H](L, M))
      (RHom[H](K, L))).inv ≫
    (β_ (RHom[H](L, M)) (RHom[H](K, L))).hom ≫
      (MonoidalClosed.comp K L M)

-- Proof sketch: both sides are the mates, under the adjunction
-- `- \otimes_R^{\mathbf L} RHom_R(K₂, L) ⊣ RHom_R(RHom_R(K₂, L), -)`, of the same morphism
-- obtained from functoriality of `RHom_R(-, M)` in the first variable together with the canonical
-- closed-monoidal composition map.
end

end CategoryTheory

/-! ### Lemma_15_74_5 (from Chap15) -/
noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedInternalHom DerivedTensorProduct

/- Domain-style sampling for 15.74.5:
- primary domain: tensor/internal-Hom comparison morphisms in the monoidal closed derived category
  `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.ihom`,
  `CategoryTheory.derivedTensorProduct_associator`,
  `CategoryTheory.derivedTensorProductMap`,
  `CategoryTheory.derivedInternalHomMap`;
- best owner abstraction:
  `source-facing`: the canonical morphism
  `K ⊗^L RHom_R(M, L) ⟶ RHom_R(M, K ⊗^L L)`;
  `core/canonical`: the chosen owner `H : MonoidalClosed DMod`, the canonical internal-Hom object
  `RHom[H](M, L)`, the transported right adjunction `H.derivedTensorAdj M`, and the canonical
  associator for `⊗[R]^L`;
  `bridge/view`: the adjoint transpose of the evaluation composite below;
- primitive data vs. derived API: the primitive data are only the owner `H`, its counit map for
  `- ⊗[R]^L M ⊣ RHom[H](M,-)`, and the established tensor owner `⊗[R]^L`; the comparison map and
  its functoriality in `K`, `L`, and `M` are derived API.
-/
private noncomputable def derivedInternalHom_tensor_left_comparisonTranspose
    (H : RHomPkg)
    (K L M : DMod) :
    ((K ⊗[R]^L (RHom[H](M, L))) ⊗[R]^L M) ⟶ K ⊗[R]^L L :=
  (derivedTensorProduct_associator K (RHom[H](M, L)) M).hom ≫
    (derivedTensorProductMap H ((H.derivedTensorAdj M).counit.app L)).app K

/-- Lemma 15.74.5: in a monoidal closed structure on `D(R)`, there is a canonical morphism
`K \otimes_R^{\mathbf L} R\mathrm{Hom}_R(M, L) \to R\mathrm{Hom}_R(M, K \otimes_R^{\mathbf L} L)`
in `D(R)`. -/
noncomputable def derivedInternalHom_tensor_left_comparison
    (H : RHomPkg)
    (K L M : DMod) :
    (K ⊗[R]^L (RHom[H](M, L))) ⟶ RHom[H](M, K ⊗[R]^L L) :=
  (H.derivedTensorAdj M).homEquiv _ _
    (derivedInternalHom_tensor_left_comparisonTranspose H K L M)

-- Proof sketch: the comparison map is defined as the mate, under
-- `- ⊗[R]^L M ⊣ RHom_R(M,-)`, of the composite obtained by reassociating
-- `K ⊗[R]^L RHom_R(M,L) ⊗[R]^L M` and then applying the counit
-- `RHom_R(M,L) ⊗[R]^L M ⟶ L`.
/-- Applying the inverse adjunction equivalence to the tensor-left comparison recovers the
associativity-counit composite used to define it. -/
theorem derivedInternalHom_tensor_left_comparison_def
    (H : RHomPkg)
    (K L M : DMod) :
    ((H.derivedTensorAdj M).homEquiv _ _).symm
        (derivedInternalHom_tensor_left_comparison H K L M) =
      derivedInternalHom_tensor_left_comparisonTranspose H K L M := by
  simpa [derivedInternalHom_tensor_left_comparison]

-- Proof sketch: both sides are mates, under `- ⊗[R]^L M ⊣ RHom_R(M,-)`, of the same morphism
-- obtained by functoriality of the derived tensor product in the left variable together with the
-- canonical transpose defining `derivedInternalHom_tensor_left_comparison`.
/-- The tensor-left comparison is natural in the tensor factor `K`. -/
theorem derivedInternalHom_tensor_left_comparison_natural_tensor
    (H : RHomPkg)
    {K₁ K₂ L M : DMod} (fK : K₁ ⟶ K₂) :
    CommSq
      ((derivedTensorProduct (RHom[H](M, L))).map fK)
      (derivedInternalHom_tensor_left_comparison H K₁ L M)
      (derivedInternalHom_tensor_left_comparison H K₂ L M)
      (derivedInternalHomMap H (𝟙 M) ((derivedTensorProduct L).map fK)) := by
  sorry

-- Proof sketch: compare the two mates of the canonical map out of
-- `((K ⊗[R]^L RHom_R(M,L₁)) ⊗[R]^L M)` obtained either by changing `L` first inside `RHom_R` or by
-- changing the target `K ⊗[R]^L L` after taking the comparison map.
/-- The tensor-left comparison is natural in the target variable `L` of the internal Hom. -/
theorem derivedInternalHom_tensor_left_comparison_natural_target
    (H : RHomPkg)
    (K M : DMod) {L₁ L₂ : DMod} (fL : L₁ ⟶ L₂) :
    CommSq
      ((derivedTensorProductMap H (derivedInternalHomMap H (𝟙 M) fL)).app K)
      (derivedInternalHom_tensor_left_comparison H K L₁ M)
      (derivedInternalHom_tensor_left_comparison H K L₂ M)
      (derivedInternalHomMap H (𝟙 M) ((derivedTensorProductMap H fL).app K)) := by
  sorry

-- Proof sketch: both composites are mates, under `- ⊗[R]^L M₁ ⊣ RHom_R(M₁,-)`, of the map
-- induced by contravariant functoriality of `RHom_R(-,L)` in its source variable.
/-- The tensor-left comparison is contravariantly natural in the source variable `M` of the
internal Hom. -/
theorem derivedInternalHom_tensor_left_comparison_natural_source
    (H : RHomPkg)
    (K L : DMod) {M₁ M₂ : DMod} (fM : M₂ ⟶ M₁) :
    CommSq
      ((derivedTensorProductMap H (derivedInternalHomMap H fM (𝟙 L))).app K)
      (derivedInternalHom_tensor_left_comparison H K L M₁)
      (derivedInternalHom_tensor_left_comparison H K L M₂)
      (derivedInternalHomMap H fM (𝟙 (K ⊗[R]^L L))) := by
  sorry

end

end CategoryTheory

/-! ### Lemma_15_74_6 (from Chap15) -/
noncomputable section

open CategoryTheory
universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "RHomPkg" => MonoidalClosed DMod

open scoped DerivedTensorProduct
open scoped DerivedInternalHom

/- Domain-style sampling for Lemma 15.74.6:
- primary domain: adjunction units and mate naturality for the chosen derived internal Hom on
  `D(R)`;
- sampled owner declarations:
  `CategoryTheory.MonoidalClosed.derivedTensorAdj`,
  `CategoryTheory.Adjunction.unit`,
  `CategoryTheory.NatTrans.naturality`,
  `CategoryTheory.unit_conjugateEquiv_symm`;
- best owner abstraction:
  `source-facing`: the canonical morphism
  `K ⟶ R\mathrm{Hom}_R(L, K \otimes_R^{\mathbf L} L)`;
  `core/canonical`: the adjunction
  `H.derivedTensorAdj L`;
  `bridge/view`: rewriting the generic unit and mate naturality identities through
  `derivedInternalHomMap` and `derivedTensorProductMap`;
- primitive data: only the canonical owner `H : MonoidalClosed DMod`;
- derived API: the specialized naturality formulas below.

This file is therefore a recall/view layer. The canonical map itself is exactly the adjunction unit
of `H.derivedTensorAdj L`, so the file should reuse that owner directly rather than keeping a parallel
local wrapper.

Source/core/bridge triage:
- `source-facing`: the canonical unit morphism and its functoriality in `K` and `L`;
- `core/canonical`: `H.derivedTensorAdj L`;
- `bridge/view`: the specialization of `NatTrans.naturality` and `unit_conjugateEquiv_symm` to the
  derived tensor/internal-Hom notation. -/

/- Lemma 15.74.6: for derived `R`-complexes `K` and `L`, the canonical morphism
`K ⟶ R\mathrm{Hom}_R(L, K \otimes_R^{\mathbf L} L)` is exactly the adjunction unit of
`derivedTensorProduct L ⊣ ihom L`. -/
set_option linter.hashCommand false in
#check fun (H : RHomPkg) (K L : DMod) ↦
  ((H.derivedTensorAdj L).unit.app K :
    K ⟶ RHom[H](L, K ⊗[R]^L L))

/- Naturality in the left variable `K` is the canonical unit naturality square, with top edge
`fK`, vertical edges the two unit components, and bottom edge the induced `derivedInternalHomMap`.
-/
set_option linter.hashCommand false in
#check fun (H : RHomPkg) {K₁ K₂ L : DMod} (fK : K₁ ⟶ K₂) ↦
  let η₁ : K₁ ⟶ RHom[H](L, K₁ ⊗[R]^L L) := (H.derivedTensorAdj L).unit.app K₁
  let η₂ : K₂ ⟶ RHom[H](L, K₂ ⊗[R]^L L) := (H.derivedTensorAdj L).unit.app K₂
  let β :
      RHom[H](L, K₁ ⊗[R]^L L) ⟶ RHom[H](L, K₂ ⊗[R]^L L) :=
    derivedInternalHomMap H (𝟙 L) ((derivedTensorProduct L).map fK)
  show CommSq fK η₁ η₂ β from by
    refine ⟨?_⟩
    dsimp [η₁, η₂, β]
    rw [derivedInternalHomMap]
    simpa using (H.derivedTensorAdj L).unit.naturality fK

/- Naturality in the right variable `L` is the unit-side mate naturality square for the conjugate
map `derivedTensorProductMap H fL`, specialized via `unit_conjugateEquiv_symm`. -/
set_option linter.hashCommand false in
#check
  fun (H : RHomPkg) (K : DMod) {L₁ L₂ : DMod} (fL : L₁ ⟶ L₂) ↦
    let η₁ : K ⟶ RHom[H](L₁, K ⊗[R]^L L₁) := (H.derivedTensorAdj L₁).unit.app K
    let η₂ : K ⟶ RHom[H](L₂, K ⊗[R]^L L₂) := (H.derivedTensorAdj L₂).unit.app K
    let α :
        RHom[H](L₂, K ⊗[R]^L L₂) ⟶ RHom[H](L₁, K ⊗[R]^L L₂) :=
      derivedInternalHomMap H fL (𝟙 (K ⊗[R]^L L₂))
    let β :
        RHom[H](L₁, K ⊗[R]^L L₁) ⟶ RHom[H](L₁, K ⊗[R]^L L₂) :=
      derivedInternalHomMap H (𝟙 L₁) ((derivedTensorProductMap H fL).app K)
    show CommSq η₂ η₁ α β from by
      refine ⟨?_⟩
      dsimp [η₁, η₂, α, β]
      convert unit_conjugateEquiv_symm
          (H.derivedTensorAdj L₂)
          (H.derivedTensorAdj L₁)
          (MonoidalClosed.pre fL)
          K using 1 <;>
        simp [derivedInternalHomMap, derivedTensorProductMap]

end

end CategoryTheory
