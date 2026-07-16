import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import stacks_proof.stacks_project.Chap13.Lemma_13_35_7
import stacks_proof.stacks_project.Chap15.Lemma_15_59_14
import stacks_proof.stacks_project.Chap15.RingSingle

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open DerivedCategory
open DerivedCategory.TStructure
open Opposite
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

end

section

variable {R : Type u} [CommRing R]

local notation "DMod" => DerivedCategory (ModuleCat R)

local notation "RHomPkg" => MonoidalClosed DMod
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)
local notation "𝓗" => DerivedCategory.homologyFunctor (ModuleCat R)

namespace DerivedInternalHom

/- Source-facing notation for the derived internal-Hom object `RHom_R(L, M)` in `D(R)`. -/
set_option quotPrecheck false in
scoped notation:70 "RHom[" H:70 "](" L:70 ", " M:70 ")" =>
  (letI := H
   (ihom L).obj M)

end DerivedInternalHom

open scoped DerivedInternalHom

namespace MonoidalClosed

/-- Helper for 15.74.0.2: the source-facing adjunction
`- \otimes_R^{\mathbf L} L ⊣ R\mathrm{Hom}_R(L, -)`, transported from the canonical tensor
adjunction on `D(R)`. -/
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

/- Domain-style sampling for 15.74.0.2:
- primary domain: cohomology of chosen derived internal-Hom objects in `D(R)` and its comparison
  with shifted morphisms in the derived category;
- sampled owner declarations:
  `DerivedInternalHom.obj`,
  `DerivedInternalHom.tensorLeftAdj`,
  `DerivedCategory.homologyFunctor`,
  `ShiftedHom`;
- best owner abstraction: the source-facing bridge should compare the cohomology module
  `H^n(RHom_R(L, M))`, realized as
  `((DerivedCategory.homologyFunctor (ModuleCat R) n).obj (RHom[H](L, M)))`, with the canonical
  `R`-module `ShiftedHom L M n`;
- primitive data: only the chosen derived internal-Hom owner `H : MonoidalClosed DMod`;
- derived API: the canonical tensor-unit bridge `R[0] ⊗^L L ≅ L`, the module-level comparison
  between `H^n(RHom_R(L, M))` and `ShiftedHom L M n`, and the resulting linear equivalence;
- source/core/bridge triage:
  `source-facing`: the source statement `H^n(RHom_R(L, M)) = Hom_{D(R)}(L, M[n])`;
  `core/canonical`: `DerivedInternalHom.obj`, `DerivedCategory.homologyFunctor`, `ShiftedHom`;
  `bridge/view`: the tensor-unit comparison below, the explicit comparison morphism, and the
  resulting isomorphism.

The previous file weakened the statement to an `AddEquiv` on an `ULift`ed underlying type, and
then to a bare existence witness. This refinement keeps the `R`-module semantics on both sides
and exposes the actual comparison map, with the isomorphism packaged from its `IsIso` theorem.
-/

/-- The canonical identification `R[0] ≅ 𝟙` in `D(R)`. -/
noncomputable def singleZeroIsoTensorUnit :
    (single₀).obj (ModuleCat.of R R) ≅ 𝟙_ DMod :=
  ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) (0 : ℤ)).app
      (ModuleCat.of R R)) ≪≫
    ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app
        ((CochainComplex.singleFunctor (ModuleCat R) (0 : ℤ)).obj
        (ModuleCat.of R R))).symm

/-- The canonical identification `R[0] \otimes_R^{\mathbf L} L ≅ L` in `D(R)`. -/
noncomputable def singleZeroDerivedTensorIso (L : DMod) :
    ((single₀).obj (ModuleCat.of R R)) ⊗[R]^L L ≅ L :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct
      ((single₀).obj (ModuleCat.of R R))
      L).symm ≪≫
    whiskerRightIso singleZeroIsoTensorUnit L ≪≫
      λ_ L

section

/- Route correction: the final comparison should be controlled by the owner-level composite
`Hom(L, M[n]) -> Hom(R[0], RHom(L, M)[n]) -> H^n(RHom(L, M))`, rather than by reproving
linearity and bijectivity elementwise from scratch. -/

variable (R)

/-- Helper for 15.74.0.2: the linear map `r ↦ r • x` evaluates to `x` at `1`. -/
lemma hom_from_ring_linear_equiv_left_inv {N : ModuleCat R} (x : N) :
    (ModuleCat.homEquiv (ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight x))) (1 : R) = x := by
  change (((LinearMap.id : R →ₗ[R] R).smulRight x) (1 : R)) = x
  simp [LinearMap.smulRight_apply]

/-- Helper for 15.74.0.2: a morphism `R → N` is recovered from the image of `1`. -/
lemma hom_from_ring_linear_equiv_right_inv {N : ModuleCat R}
    (f : (ModuleCat.of R R) ⟶ N) :
    ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight ((ModuleCat.homEquiv f) (1 : R)))) = f := by
  apply ModuleCat.hom_injective
  exact LinearMap.ext fun x ↦ by
    simp [LinearMap.smulRight_apply]
    simpa using ((ModuleCat.homEquiv f).map_smul x (1 : R)).symm

/-- Helper for 15.74.0.2: evaluation at `1` preserves addition on morphisms `R → N`. -/
lemma hom_from_ring_linear_equiv_map_add {N : ModuleCat R}
    (f g : (ModuleCat.of R R) ⟶ N) :
    (ModuleCat.homEquiv (f + g)) (1 : R) =
      (ModuleCat.homEquiv f) (1 : R) + (ModuleCat.homEquiv g) (1 : R) :=
  rfl

/-- Helper for 15.74.0.2: evaluation at `1` is `R`-linear on morphisms `R → N`. -/
lemma hom_from_ring_linear_equiv_map_smul {N : ModuleCat R}
    (r : R) (f : (ModuleCat.of R R) ⟶ N) :
    (ModuleCat.homEquiv (r • f)) (1 : R) = r • (ModuleCat.homEquiv f) (1 : R) :=
  rfl

/-- Helper for 15.74.0.2: the inverse map `x ↦ (r ↦ r • x)` preserves addition. -/
lemma hom_from_ring_linear_equiv_inv_map_add {N : ModuleCat R} (x y : N) :
    ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight (x + y))) =
      ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight x)) +
        ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight y)) := by
  apply ModuleCat.hom_injective
  exact LinearMap.ext fun r ↦ by
    simp [LinearMap.smulRight_apply]

/-- Helper for 15.74.0.2: the inverse map `x ↦ (r ↦ r • x)` preserves scalar multiplication. -/
lemma hom_from_ring_linear_equiv_inv_map_smul {N : ModuleCat R} (r : R) (x : N) :
    ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight (r • x))) =
      r • ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight x)) := by
  apply ModuleCat.hom_injective
  exact LinearMap.ext fun s ↦ by
    simpa [LinearMap.smulRight_apply, smul_smul, mul_comm]

/-- Helper for 15.74.0.2: morphisms from the free rank-one module `R` are equivalent to elements
of the target module, via evaluation at `1`. -/
noncomputable def hom_from_ring_linear_equiv (N : ModuleCat R) :
    ((ModuleCat.of R R) ⟶ N) ≃ₗ[R] N :=
  { toFun := fun f ↦ (ModuleCat.homEquiv f) (1 : R)
    invFun := fun x ↦ ModuleCat.ofHom (((LinearMap.id : R →ₗ[R] R).smulRight x))
    map_add' := hom_from_ring_linear_equiv_map_add R
    map_smul' := hom_from_ring_linear_equiv_map_smul R
    left_inv := hom_from_ring_linear_equiv_right_inv R
    right_inv := hom_from_ring_linear_equiv_left_inv R }

/-- Helper for 15.74.0.2: an isomorphism in `ModuleCat R` induces an `R`-linear equivalence on
underlying modules. -/
noncomputable def moduleCatIsoToLinearEquiv {M N : ModuleCat R} (e : M ≅ N) :
    M ≃ₗ[R] N :=
  LinearEquiv.ofLinear e.hom.hom e.inv.hom
    (by
      ext x
      simp)
    (by
      ext x
      simp)

/-- Helper for 15.74.0.2: postcomposition with an isomorphism is an `R`-linear equivalence on
hom-sets. -/
noncomputable def postcompose_hom_linear_equiv {X Y Z : DMod} (e : Y ≅ Z) :
    (X ⟶ Y) ≃ₗ[R] (X ⟶ Z) :=
  { toFun := fun f ↦ f ≫ e.hom
    invFun := fun f ↦ f ≫ e.inv
    map_add' := by
      intro f g
      simp
    map_smul' := by
      intro r f
      simp
    left_inv := by
      intro f
      simp
    right_inv := by
      intro f
      simp }

/-- Helper for 15.74.0.2: precomposition with an isomorphism is an `R`-linear equivalence on
hom-sets. -/
noncomputable def precompose_hom_linear_equiv {X Y Z : DMod} (e : X ≅ Y) :
    (Y ⟶ Z) ≃ₗ[R] (X ⟶ Z) :=
  { toFun := fun f ↦ e.hom ≫ f
    invFun := fun f ↦ e.inv ≫ f
    map_add' := by
      intro f g
      simp
    map_smul' := by
      intro r f
      simp
    left_inv := by
      intro f
      simp
    right_inv := by
      intro f
      simp }

/-- Helper for 15.74.0.2: in an `R`-linear adjunction, the inverse hom-equivalence is an
`R`-linear equivalence on hom-sets. -/
noncomputable def adjunction_symm_hom_linear_equiv
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [CategoryTheory.Linear R C] [CategoryTheory.Linear R D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive] [F.Linear R]
    (X : C) (Y : D) :
    (X ⟶ G.obj Y) ≃ₗ[R] (F.obj X ⟶ Y) :=
  { toFun := (adj.homEquiv X Y).symm
    invFun := adj.homEquiv X Y
    map_add' := by
      intro f g
      simpa using (adj.homAddEquiv X Y).symm.map_add f g
    map_smul' := by
      intro r f
      rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit, Functor.map_smul]
      simp
    left_inv := by
      intro f
      exact (adj.homEquiv X Y).apply_symm_apply f
    right_inv := by
      intro f
      exact (adj.homEquiv X Y).symm_apply_apply f }

/-- Helper for 15.74.0.2: an object of `D(R)` concentrated in degree `n` is canonically the
single object on its degree-`n` cohomology module. -/
private noncomputable def singleFunctorIsoOfIsGEOfIsLE_local
    (X : DMod) (n : ℤ) [X.IsGE n] [X.IsLE n] :
    X ≅ (DerivedCategory.singleFunctor (ModuleCat R) n).obj ((𝓗 n).obj X) := by
  classical
  -- Choose the canonical concentrated representative, then identify its cohomology module with
  -- the given `H^n(X)` by functoriality of `𝓗 n`.
  let hX := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X n
  let Y := Classical.choose hX
  let e : X ≅ (DerivedCategory.singleFunctor (ModuleCat R) n).obj Y :=
    Classical.choice (Classical.choose_spec hX)
  let eH : (𝓗 n).obj X ≅ Y :=
    (𝓗 n).mapIso e ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) n).app Y
  exact e ≪≫ (DerivedCategory.singleFunctor (ModuleCat R) n).mapIso eH.symm

/-- Helper for 15.74.0.2: shifting a derived object by `n` shifts degree-`i` cohomology to
degree `i + n`. -/
private noncomputable def homology_shift_iso_local
    (X : DMod) (i n : ℤ) :
    (𝓗 i).obj (X⟦n⟧) ≅ (𝓗 (i + n)).obj X :=
  ((𝓗 0).shiftIso n i (i + n) (add_comm n i)).app X

/-- Helper for 15.74.0.2: the upper truncation inclusion induces an isomorphism on the last
remaining cohomology group. -/
private theorem isIso_homologyMap_truncLTι_local
    (K : DMod) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    IsIso ((𝓗 n₀).map ((DerivedCategory.TStructure.t.truncLTι n₁).app K)) := by
  simpa using isIso_homologyMap_truncLTι (A := ModuleCat R) K n₀ n₁ h

/-- Helper for 15.74.0.2: the lower truncation projection induces an isomorphism on degree-`n`
cohomology. -/
private theorem isIso_homologyMap_truncGEπ_local
    (K : DMod) (n : ℤ) :
    IsIso ((𝓗 n).map ((DerivedCategory.TStructure.t.truncGEπ n).app K)) := by
  simpa using isIso_homologyMap_truncGEπ (A := ModuleCat R) K n

/-- Helper for 15.74.0.2: the lower-step degree-zero truncation piece has the same degree-zero
cohomology as the original derived object. -/
private noncomputable def truncLT_truncGE_zero_homologyIso
    (X : DMod) :
    (𝓗 0).obj ((DerivedCategory.TStructure.t.truncLT 1).obj
      ((DerivedCategory.TStructure.t.truncGE 0).obj X)) ≅
        (𝓗 0).obj X :=
  by
  let eι :
      (𝓗 0).obj ((DerivedCategory.TStructure.t.truncLT 1).obj
        ((DerivedCategory.TStructure.t.truncGE 0).obj X)) ≅
          (𝓗 0).obj ((DerivedCategory.TStructure.t.truncGE 0).obj X) :=
    @asIso _ _ _ _
      ((𝓗 0).map
        ((DerivedCategory.TStructure.t.truncLTι 1).app
          ((DerivedCategory.TStructure.t.truncGE 0).obj X)))
      (isIso_homologyMap_truncLTι_local (R := R)
        ((DerivedCategory.TStructure.t.truncGE 0).obj X) 0 1 rfl)
  let eπ : (𝓗 0).obj X ≅ (𝓗 0).obj ((DerivedCategory.TStructure.t.truncGE 0).obj X) :=
    @asIso _ _ _ _
      ((𝓗 0).map ((DerivedCategory.TStructure.t.truncGEπ 0).app X))
      (isIso_homologyMap_truncGEπ_local (R := R) X 0)
  -- Both truncation maps are isomorphisms on degree-zero cohomology, so the sandwich carries the
  -- same `H^0`.
  exact eι ≪≫ eπ.symm

/-- Helper for 15.74.0.2: the degree-zero truncation piece `τ_{<1}(τ_{≥0} X)` is canonically the
single object on `H^0(X)`. -/
private noncomputable def truncLT_truncGE_zero_termIso
    (X : DMod) :
    ((DerivedCategory.TStructure.t.truncLT 1).obj
      ((DerivedCategory.TStructure.t.truncGE 0).obj X)) ≅
        (single₀).obj ((𝓗 0).obj X) := by
  have hLE :
      ((DerivedCategory.TStructure.t.truncLT 1).obj
        ((DerivedCategory.TStructure.t.truncGE 0).obj X)).IsLE 0 := by
    simpa using
      (inferInstance :
        ((DerivedCategory.TStructure.t.truncLT 1).obj
          ((DerivedCategory.TStructure.t.truncGE 0).obj X)).IsLE ((1 : ℤ) - 1))
  -- Apply the concentrated-object identification and then rewrite the cohomology term back to
  -- `H^0(X)` using the previous homology isomorphism.
  exact
    singleFunctorIsoOfIsGEOfIsLE_local (R := R)
      ((DerivedCategory.TStructure.t.truncLT 1).obj
        ((DerivedCategory.TStructure.t.truncGE 0).obj X)) 0 ≪≫
      (single₀).mapIso (truncLT_truncGE_zero_homologyIso (R := R) X)

/-- Helper for 15.74.0.2: the two canonical orders of the degree-zero truncation sandwich agree,
and hence `τ_{≥0}(τ_{<1} X)` is also canonically `H^0(X)[0]`. -/
private noncomputable def truncGE_truncLT_zero_termIso
    (X : DMod) :
    (DerivedCategory.TStructure.t.truncGE 0).obj
        ((DerivedCategory.TStructure.t.truncLT 1).obj X) ≅
      (single₀).obj ((𝓗 0).obj X) := by
  -- Route correction: the source proof passes through the concentrated truncation piece, and the
  -- owner commutation isomorphism `τ_{≥0}τ_{<1} ≅ τ_{<1}τ_{≥0}` keeps that route intact.
  exact
    (DerivedCategory.TStructure.t.truncGELTIsoLTGE 0 1).app X ≪≫
      truncLT_truncGE_zero_termIso (R := R) X

/-- Helper for 15.74.0.2: shifting `R[0]` by `k` identifies it with the single object
`R[-k]`. -/
private noncomputable def shifted_ring_single_iso_single (k : ℤ) :
    (ringSingle (R := R))⟦k⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat R) (-k)).obj (ModuleCat.of R R) :=
  ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso k (-k) 0 (by omega)).app
    (ModuleCat.of R R)

/-- Helper for 15.74.0.2: maps from `R[0]` into an object supported strictly below degree `0`
vanish because `R` is projective. -/
private theorem ring_single_hom_eq_zero_of_isLE_negOne
    {Y : DMod} (hY : Y.IsLE (-1))
    (φ : ringSingle (R := R) ⟶ Y) :
    φ = 0 := by
  -- Replace the target by a strictly upper-bounded complex and use projectivity of `R`.
  rcases hY with ⟨L, eL, hL⟩
  apply (cancel_mono eL.hom).1
  simpa using
    (DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective
      (P := ModuleCat.of R R) (L := L) (i := 0) (φ := φ ≫ eL.hom) (n := -1)
      (hn := by omega))

/-- Helper for 15.74.0.2: precomposing with the canonical shift identification transports maps
out of `R[0]⟦k⟧` to maps out of `R[-k]`. -/
private noncomputable def shifted_ring_single_hom_transport (X : DMod) (k : ℤ) :
    (((ringSingle (R := R))⟦k⟧) ⟶ X) ≃+
      (((DerivedCategory.singleFunctor (ModuleCat R) (-k)).obj (ModuleCat.of R R)) ⟶ X) :=
  { toFun := fun g ↦ (shifted_ring_single_iso_single (R := R) k).inv ≫ g
    invFun := fun g ↦ (shifted_ring_single_iso_single (R := R) k).hom ≫ g
    left_inv := by
      intro g
      -- Cancel the inverse pair of the shift identification on the source.
      simpa [Category.assoc] using
        (Iso.hom_inv_id_assoc (shifted_ring_single_iso_single (R := R) k) g)
    right_inv := by
      intro g
      -- Cancel the inverse pair of the shift identification on the source.
      simpa [Category.assoc] using
        (Iso.inv_hom_id_assoc (shifted_ring_single_iso_single (R := R) k) g)
    map_add' := by
      intro g h
      simp }

/-- Helper for 15.74.0.2: shifting the source by `-n` identifies `Hom(A, B[n])` with ordinary
morphisms `A[-n] ⟶ B`. -/
private noncomputable def shiftedHom_linear_equiv_shifted_source_hom
    (A B : DMod) (n : ℤ) :
    ShiftedHom A B n ≃ₗ[R] (A⟦-n⟧ ⟶ B) := sorry

/-- Helper for 15.74.0.2: after shifting the source once to `R[-1]`, maps into an object
supported strictly below degree `0` still vanish by projectivity of `R`. -/
private theorem ring_single_hom_shift_eq_zero_of_isLE_negOne
    {Y : DMod} (hY : Y.IsLE (-1))
    (φ : ringSingle (R := R) ⟶ Y⟦(1 : ℤ)⟧) :
    φ = 0 := by
  sorry

/-- Helper for 15.74.0.2: morphisms from `A[0]` factor uniquely through the upper truncation
`τ_{<1} X`. -/
private noncomputable def single_zero_hom_equiv_truncLT_zero
    (A : ModuleCat R) (X : DMod) :
    (((single₀).obj A) ⟶ X) ≃ₗ[R]
      (((single₀).obj A) ⟶ (DerivedCategory.TStructure.t.truncLT 1).obj X) := sorry

/-- Helper for 15.74.0.2: once a map already lands in the concentrated degree-zero truncation
piece, full faithfulness of `single₀` identifies it with a map into `H^0(X)`. -/
private noncomputable def single_zero_fullyFaithful_linear_equiv
    (A B : ModuleCat R) :
    (((single₀).obj A) ⟶ ((single₀).obj B)) ≃ₗ[R] (A ⟶ B) := sorry

/-- Helper for 15.74.0.2: once a map already lands in the concentrated degree-zero truncation
piece, full faithfulness of `single₀` identifies it linearly with a map into `H^0(X)`. -/
private noncomputable def single_zero_hom_equiv_homology_zero_truncation
    (A : ModuleCat R) (X : DMod) :
    (((single₀).obj A) ⟶ (DerivedCategory.TStructure.t.truncGE 0).obj
      ((DerivedCategory.TStructure.t.truncLT 1).obj X)) ≃ₗ[R]
        (A ⟶ (𝓗 0).obj X) := sorry

/-- Helper for 15.74.0.2: postcomposition with `τ_{≥ 0}(τ_{< 1} X)` is the forward map in the
remaining degree-zero truncation bridge. -/
private noncomputable def single_zero_hom_map_truncGE_truncLT_zero
    (X : DMod) :
    ((ringSingle (R := R)) ⟶ (DerivedCategory.TStructure.t.truncLT 1).obj X) →ₗ[R]
      ((ringSingle (R := R)) ⟶ (DerivedCategory.TStructure.t.truncGE 0).obj
        ((DerivedCategory.TStructure.t.truncLT 1).obj X)) :=
  { toFun := fun f ↦ f ≫ (DerivedCategory.TStructure.t.truncGEπ 0).app
      ((DerivedCategory.TStructure.t.truncLT 1).obj X)
    map_add' := by
      intro f g
      simp
    map_smul' := by
      intro r f
      simp }

/-- Helper for 15.74.0.2: after the target has been replaced by the concentrated degree-zero
truncation piece, maps out of `R[0]` are already identified with elements of `H^0(X)`. -/
private noncomputable def ring_single_hom_equiv_homology_zero_truncation
    (X : DMod) :
    ((ringSingle (R := R)) ⟶ (DerivedCategory.TStructure.t.truncGE 0).obj
      ((DerivedCategory.TStructure.t.truncLT 1).obj X)) ≃ₗ[R] (𝓗 0).obj X :=
  -- Specialize the generic `A[0]` comparison to `A = R`, then evaluate at `1 : R`.
  (single_zero_hom_equiv_homology_zero_truncation (R := R) (A := ModuleCat.of R R) (X := X)).trans
    (hom_from_ring_linear_equiv R ((𝓗 0).obj X))

/-- Helper for 15.74.0.2: exactness of the truncation triangle makes postcomposition with
`τ_{≥0}` injective on maps out of `R[0]`. -/
private theorem single_zero_hom_map_truncGE_truncLT_zero_injective
    (X : DMod) :
    Function.Injective (single_zero_hom_map_truncGE_truncLT_zero (R := R) X) := by
  sorry

/-- Helper for 15.74.0.2: exactness of the truncation triangle makes postcomposition with
`τ_{≥0}` surjective on maps out of `R[0]`. -/
private theorem single_zero_hom_map_truncGE_truncLT_zero_surjective
    (X : DMod) :
    Function.Surjective (single_zero_hom_map_truncGE_truncLT_zero (R := R) X) := by
  sorry

/-- Helper for 15.74.0.2: postcomposition with `τ_{≥0}` on `τ_{<1} X` is an `R`-linear
equivalence on maps out of `R[0]`. -/
private noncomputable def single_zero_hom_equiv_truncGE_truncLT_zero
    (X : DMod) :
    ((ringSingle (R := R)) ⟶ (DerivedCategory.TStructure.t.truncLT 1).obj X) ≃ₗ[R]
      ((ringSingle (R := R)) ⟶ (DerivedCategory.TStructure.t.truncGE 0).obj
        ((DerivedCategory.TStructure.t.truncLT 1).obj X)) :=
  LinearEquiv.ofBijective
    (single_zero_hom_map_truncGE_truncLT_zero (R := R) X)
    ⟨single_zero_hom_map_truncGE_truncLT_zero_injective (R := R) X,
      single_zero_hom_map_truncGE_truncLT_zero_surjective (R := R) X⟩

/-- Helper for 15.74.0.2: the unresolved source-faithful heart bridge identifies degree-zero
cohomology with morphisms from `R[0]`. -/
noncomputable def cohomology_zero_linear_equiv_single_zero_hom
    (X : DMod) :
    (𝓗 0).obj X ≃ₗ[R] (ringSingle (R := R) ⟶ X) :=
  sorry

/-- Helper for 15.74.0.2: degree-`n` cohomology of a derived object is canonically identified
with morphisms from `R[0]` into its `n`-fold shift. -/
noncomputable def cohomology_linear_equiv_single_zero_hom
    (X : DMod) (n : ℤ) :
    (𝓗 n).obj X ≃ₗ[R] (((single₀).obj (ModuleCat.of R R)) ⟶ X⟦n⟧) := sorry

/-- Helper for 15.74.0.2: `ShiftedHom L M n` is linearly equivalent to the ordinary Hom-module
`L ⟶ M[n]`. -/
private noncomputable def shiftedHom_linear_equiv_hom
    (L M : DMod) (n : ℤ) :
    ShiftedHom L M n ≃ₗ[R] (L ⟶ M⟦n⟧) := by
  -- `ShiftedHom` is only the source-facing name for the same Hom-module.
  exact LinearEquiv.refl R (L ⟶ M⟦n⟧)

/-- Helper for 15.74.0.2: the source-faithful owner composite sends cohomology of `RHom` to the
shifted-Hom module. -/
noncomputable def derivedHom_cohomology_linear_equiv_shiftedHom
    (H : RHomPkg) (L M : DMod) (n : ℤ) :
    (𝓗 n).obj (RHom[H](L, M)) ≃ₗ[R] ShiftedHom L M n := sorry

/-- Helper for 15.74.0.2: the textbook comparison
`Hom_{D(R)}(L, M[n]) -> H^n(RHom_R(L, M))` packaged as an `R`-linear equivalence. -/
noncomputable def shiftedHom_linear_equiv_derivedHom_cohomology
    (H : RHomPkg) (L M : DMod) (n : ℤ) :
    ShiftedHom L M n ≃ₗ[R] (𝓗 n).obj (RHom[H](L, M)) :=
  -- This is the inverse of the owner-level cohomology-to-shifted-Hom composite above.
  (derivedHom_cohomology_linear_equiv_shiftedHom R H L M n).symm

-- Proof sketch: use the owner-side unit comparison
-- `(derivedTensorProduct L).obj R[0] ≅ L` and the shift-compatibility of `derivedTensorProduct L`
-- to transport the adjunction `H.derivedTensorAdj L` into a map
-- `ShiftedHom L M n → H^n(RHom_R(L,M))`, viewed directly as an `R`-linear map.
/-- The canonical comparison map
`Hom_{D(R)}(L, M[n]) → H^n(RHom_R(L, M))`
attached to a chosen derived internal-Hom package on `D(R)`. -/
noncomputable def derivedHom_cohomology_comparison
    (H : RHomPkg) (L M : DMod) (n : ℤ) :
    ShiftedHom L M n →ₗ[R] (𝓗 n).obj (RHom[H](L, M)) :=
  (shiftedHom_linear_equiv_derivedHom_cohomology R H L M n).toLinearMap

/-- 15.74.0.2: for a chosen derived internal-Hom package on `D(R)`, the degree-`n` cohomology
module of `RHom_R(L, M)` is canonically linearly equivalent to the canonical shifted-Hom module
`ShiftedHom L M n = Hom_{D(R)}(L, M[n])`. -/
@[stacks 0A64]
noncomputable abbrev derivedHom_cohomology_iso_shiftedHom
    (H : RHomPkg) (L M : DMod) (n : ℤ) :
    ((𝓗 n).obj (RHom[H](L, M))) ≃ₗ[R] ShiftedHom L M n :=
  (shiftedHom_linear_equiv_derivedHom_cohomology R H L M n).symm

end

end

end CategoryTheory
