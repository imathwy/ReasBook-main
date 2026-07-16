import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Localization
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Triangulated.Subcategory
import StacksProject_2024.stacks_project.Chap13.Remark_13_10_9
import StacksProject_2024.stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CochainComplex.HomComplex
open ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

universe v u

section AbelianConeCriterion

variable {C : Type u} [Category.{v} C] [Abelian C] [HasBinaryBiproducts C]

/-- Helper for Lemma 15.59.2: the abelian cone criterion reads quasi-isomorphisms as acyclic
mapping cones in `K(C)`. -/
private theorem mappingCone_acyclic_of_quasiIso
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (hf : QuasiIso f) :
    (CochainComplex.mappingCone f).Acyclic := by
  have hq :
      HomotopyCategory.quasiIso C (up ℤ) ((HomotopyCategory.quotient C (up ℤ)).map f) :=
    (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := C) (c := up ℤ) f).2 hf
  have hq' :
      (HomotopyCategory.subcategoryAcyclic C).trW
        ((HomotopyCategory.quotient C (up ℤ)).map f) := by
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := C)] using hq
  have hmem :
      HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (up ℤ)).obj (CochainComplex.mappingCone f)) := by
    -- The standard mapping-cone triangle identifies the cone term with the `trW` witness.
    simpa using
      ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).1 hq'
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (C := C) (CochainComplex.mappingCone f)).1 hmem

/-- Helper for Lemma 15.59.2: the converse abelian cone criterion recovers a quasi-isomorphism
from an acyclic mapping cone in `K(C)`. -/
private theorem quasiIso_of_mappingCone_acyclic
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (hCone : (CochainComplex.mappingCone f).Acyclic) :
    QuasiIso f := by
  have hmem :
      HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (up ℤ)).obj (CochainComplex.mappingCone f)) :=
    (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
      (C := C) (CochainComplex.mappingCone f)).2 hCone
  have hq :
      HomotopyCategory.quasiIso C (up ℤ) ((HomotopyCategory.quotient C (up ℤ)).map f) := by
    -- Package the acyclic cone as the `trW` witness in the standard mapping-cone triangle.
    simpa [HomotopyCategory.quasiIso_eq_subcategoryAcyclic_W (C := C)] using
      ((HomotopyCategory.subcategoryAcyclic C).trW_iff_of_distinguished
        (CochainComplex.mappingCone.triangleh f)
        (HomotopyCategory.mappingCone_triangleh_distinguished f)).2 hmem
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff (C := C) (c := up ℤ) f).1 hq

end AbelianConeCriterion

section ConeTransport

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Helper for Lemma 15.59.2: acyclicity transports across an isomorphism of cochain complexes. -/
private theorem acyclic_of_iso
    {K L : CochainComplex C ℤ} (e : K ≅ L) (hK : K.Acyclic) :
    L.Acyclic := by
  -- Read acyclicity degreewise and move each exactness witness across the isomorphism.
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hK n) e

end ConeTransport

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [CategoryWithHomology C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

variable (K : CochainComplex C ℤ)
variable [∀ X : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X K (curriedTensor C)]

local notation "KHom" => HomotopyCategory C (up ℤ)

/- Domain-style sampling:
- primary domain: quasi-isomorphism invariance of totalized tensoring by a fixed K-flat cochain
  complex;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `HomologicalComplex.HasTensor`,
  `tensorHom`,
  `QuasiIso`,
  `Functor.map`;
- best owner abstraction: the source-facing owner map is the canonical tensor morphism
  `tensorHom f (𝟙 K)` induced by fixed-right totalized tensoring with `K`, rather than a separate
  local functor wrapper;
- primitive vs derived:
  primitive data are the complex `K`, the source morphism `f`, and the K-flat/quasi-isomorphism
  hypotheses;
  the tensor-induced morphism `tensorHom f (𝟙 K)` is derived API from fixed-right tensoring;
- source/core/bridge triage:
  `source-facing`: the quasi-isomorphism preservation statement from Lemma 15.59.2;
  `core/canonical`: `CochainComplex.IsKFlat`, `tensorHom`, and `QuasiIso`;
  `bridge/view`: the functorial interpretation of `tensorHom f (𝟙 K)` as the map induced by
    fixed-right tensoring on the homotopy category. -/

/-- Helper for Lemma 15.59.2: a cochain map is a quasi-isomorphism exactly when its image in the
homotopy category is a quasi-isomorphism. -/
lemma quasiIso_iff_quotient_map_quasiIso {L M : CochainComplex C ℤ} (f : L ⟶ M) :
    HomotopyCategory.quasiIso C (up ℤ) ((HomotopyCategory.quotient C (up ℤ)).map f) ↔ QuasiIso f := by
  -- Pass between cochain-level and homotopy-category homology maps through the quotient factors.
  exact HomotopyCategory.quotient_map_mem_quasiIso_iff (C := C) (c := up ℤ) f

/-- Helper for Lemma 15.59.2: fixed-right tensoring with `K` descends to an endofunctor of the
homotopy category by quotienting the cochain-level tensor-totalization functor. -/
private abbrev tensor_right_homotopy_functor [HasBinaryBiproducts C]
    [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ X Y : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X Y (curriedTensor C)]
    (K : CochainComplex C ℤ) : KHom ⥤ KHom :=
  -- Route correction: on `K(C)` the correct owner is the quotient lift on cochain complexes,
  -- since `mapHomotopyCategory` here would act on complexes of complexes rather than on `K(C)`.
  CategoryTheory.Quotient.lift _
    (((((curriedTensor C).map₂CochainComplex).flip).obj K) ⋙ HomotopyCategory.quotient C (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 K)
          (curriedTensor C) (up ℤ)))

/-- Helper for Lemma 15.59.2: on quotient representatives, the descended fixed-right tensor
functor evaluates by taking the totalized tensor product with `K`. -/
private theorem tensor_right_homotopy_functor_obj_quotient [HasBinaryBiproducts C]
    [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ X Y : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X Y (curriedTensor C)]
    (K L : CochainComplex C ℤ) :
    (tensor_right_homotopy_functor (C := C) K).obj ((HomotopyCategory.quotient C (up ℤ)).obj L) =
      (HomotopyCategory.quotient C (up ℤ)).obj (HomologicalComplex.tensorObj L K) := by
  -- The quotient lift computes on representatives by the underlying tensor-totalization functor.
  rfl

/-- Helper for Lemma 15.59.2: on the chosen representative `X.as` of an object of `K(C)`, the
descended fixed-right tensor functor still computes by tensor totalization with `K`. -/
private theorem tensor_right_homotopy_functor_obj_as [HasBinaryBiproducts C]
    [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ X Y : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X Y (curriedTensor C)]
    (K : CochainComplex C ℤ) (X : KHom) :
    (tensor_right_homotopy_functor (C := C) K).obj X =
      (HomotopyCategory.quotient C (up ℤ)).obj (HomologicalComplex.tensorObj X.as K) := by
  -- Unpack the chosen representative so the quotient lift reduces to the cochain-level tensor
  -- totalization functor on that representative.
  cases X
  rfl

/-- Helper for Lemma 15.59.2: on quotient morphisms, the descended fixed-right tensor functor
acts by the canonical tensor map `tensorHom f (𝟙 K)`. -/
private theorem tensor_right_homotopy_functor_map_quotient [HasBinaryBiproducts C]
    [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ X Y : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X Y (curriedTensor C)]
    {L M : CochainComplex C ℤ} (K : CochainComplex C ℤ) (f : L ⟶ M) :
    (tensor_right_homotopy_functor (C := C) K).map
        ((HomotopyCategory.quotient C (up ℤ)).map f) =
      (HomotopyCategory.quotient C (up ℤ)).map (HomologicalComplex.tensorHom f (𝟙 K)) := by
  -- The quotient lift maps a represented morphism by applying the cochain-level tensor functor.
  rfl

/-- Helper for Lemma 15.59.2: in an abelian category, fixed-right tensoring by a K-flat complex
sends acyclic representatives to acyclic tensor totalizations. -/
private theorem tensor_right_tensorObj_acyclic_of_isKFlat [Abelian C]
    [HasBinaryBiproducts C] [(curriedTensor C).Additive]
    [∀ X : C, ((curriedTensor C).obj X).Additive]
    [∀ X Y : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X Y (curriedTensor C)]
    (hK : K.IsKFlat) {L : CochainComplex C ℤ} (hL : L.Acyclic) :
    (HomologicalComplex.tensorObj L K).Acyclic := by
  -- This is exactly the defining K-flatness test specialized to the acyclic input `L`.
  exact CochainComplex.acyclic_tensorObj_of_isKFlat hK hL

/-- Lemma 15.59.2: if `K^\bullet` is a K-flat cochain complex in a monoidal preadditive category,
then for every quasi-isomorphism `f : L^\bullet ⟶ M^\bullet`, the induced tensor map
`\mathrm{Tot}(f \otimes \mathrm{id}_{K^\bullet}) = tensorHom f (\mathrm{id}_{K^\bullet})` is again
a quasi-isomorphism. -/
-- Proof sketch: identify the cone of `tensorHom f (𝟙 K)` with the totalized tensor of the cone
-- of `f` with `K`. If `f` is a quasi-isomorphism, its cone is acyclic, and K-flatness of `K`
-- keeps that tensor cone acyclic.
theorem tensorHom_right_quasiIso_of_isKFlat
    (hK : K.IsKFlat)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (hf : QuasiIso f) :
    QuasiIso (tensorHom f (𝟙 K)) :=
  -- Route correction: the source-faithful proof now runs entirely through the abelian owner
  -- `HomotopyCategory.subcategoryAcyclic`.
  -- The remaining blocker is structural: the current generic header does not provide an
  -- abelian-free replacement for that owner or for the induced quasi-isomorphism
  -- characterization on `K(C)`.
  -- TODO: either construct a genuine nonabelian replacement for
  -- `HomotopyCategory.subcategoryAcyclic C` together with its `trW`-identification of
  -- quasi-isomorphisms, or re-plan the theorem with the extra abelian hypotheses needed by the
  -- available source route.
  sorry

end
