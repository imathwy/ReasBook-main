import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_21_17_1 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory MonoidalCategory

noncomputable section

universe u

set_option checkBinderAnnotations false

namespace CategoryTheory

/-
Domain-style sampling for Lemma 21.17.1:
- primary domain: triangulated tensor-totalization functors on homotopy categories of cochain
  complexes in a preadditive monoidal category;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.IsTriangulated`;
- best owner abstraction: the Chapter 13 owner theorem
  `Functor.mapHomotopyCategory` on the fixed-factor tensor-complex functors for a bilinear
  bifunctor;
- primitive data: the bilinear tensor bifunctor `curriedTensor (ringedSiteModuleCategory J 𝒪)` and
  a fixed complex in each variable;
- derived API here: the ringed-site specialization to the homotopy-category endofunctors
  `𝒜 ↦ Tot (𝒢 ⊗ 𝒜)` and `𝒜 ↦ Tot (𝒜 ⊗ 𝒢)`.

Source/core/bridge triage:
- `source-facing`: exactness of tensoring on either side by a fixed complex of `𝒪`-modules on a
  ringed site;
- `core/canonical`: the two fixed-factor tensor functors
  `((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex.obj 𝒢).mapHomotopyCategory
    (up ℤ)` and
  `((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory
    (up ℤ)`;
- `bridge/view`: specializing the Chapter 13 owner theorem to
  `curriedTensor (ringedSiteModuleCategory J 𝒪)`.

This file adds no ringed-site-specific primitive tensor data beyond that specialization, so the
correct refinement is direct recall/use of the Chapter 13 owner theorem rather than a duplicate
Chapter 21 wrapper.
-/

section

variable {C : Type u} [Category.{u} C]
variable (J : GrothendieckTopology C)
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable (𝒪 : Sheaf J CommRingCat.{u})

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModuleCategory J 𝒪)]
variable [HasCountableCoproducts (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ F : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj F).Additive]
variable [∀ (F G : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ),
  CochainComplex.HasMapBifunctor F G (curriedTensor (ringedSiteModuleCategory J 𝒪))]

variable (𝒢 : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ)

/- Lemma 21.17.1 is the ringed-site specialization of the canonical fixed-factor
tensor-totalization functors on the homotopy category, given by the Chapter 13 exactness
theorems specialized to `curriedTensor (ringedSiteModuleCategory J 𝒪)`. -/
example :
    let F : HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) ⥤
        HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

example :
    let F : HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) ⥤
        HomotopyCategory (ringedSiteModuleCategory J 𝒪) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (ringedSiteModuleCategory J 𝒪) (up ℤ))
        ((((curriedTensor (ringedSiteModuleCategory J 𝒪)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (ringedSiteModuleCategory J 𝒪) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (ringedSiteModuleCategory J 𝒪)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

end

end CategoryTheory

/-! ### Definition_21_17_2 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/- Domain-style sampling for Definition 21.17.2:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`;
- best owner abstraction: the Chapter 15 owner predicate `CochainComplex.IsKFlat` on
  `CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ`;
- primitive vs derived: the primitive data are only the complex `K`, while preservation of
  acyclic complexes under totalized tensoring is exactly the companion theorem
  `CochainComplex.isKFlat_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook K-flatness notion for complexes of `\mathcal O`-modules on a
  ringed site;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: no extra bridge is needed, because the ringed-site notion is exactly this owner
  specialized to `ringedSiteModuleCategory J 𝒪`. -/

/- Definition 21.17.2: a cochain complex `\mathcal K^\bullet` of `\mathcal O`-modules on a
ringed site `(\mathcal C, \mathcal O)` is K-flat if for every acyclic cochain complex
`\mathcal F^\bullet`, the totalized tensor product
`\mathrm{Tot}(\mathcal F^\bullet \otimes_\mathcal O \mathcal K^\bullet)` is acyclic. This is the
canonical owner `CochainComplex.IsKFlat` specialized to `ringedSiteModuleCategory J 𝒪`. -/
recall CochainComplex.IsKFlat

/- Totalized tensoring with `K` preserves acyclic complexes exactly when `K` is K-flat; the
canonical companion theorem is `CochainComplex.isKFlat_iff`. -/
recall CochainComplex.isKFlat_iff

section

variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [Preadditive Mod]
variable [HasZeroObject Mod]
variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]
variable [(curriedTensor Mod).Additive]
variable [∀ ℱ : Mod, ((curriedTensor Mod).obj ℱ).Additive]
variable (K : CochainComplex Mod ℤ)

/- Source-facing specialization: for a ringed site `(\mathcal C, \mathcal O)`, Definition
21.17.2 uses exactly the Chapter 15 owner predicate and its canonical iff-formulation on
`ringedSiteModuleCategory J 𝒪`. -/
#check K.IsKFlat
#check CochainComplex.isKFlat_iff K

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_3 (from Chap21) -/
namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.17.3:
- primary domain: K-flat complexes and quasi-isomorphisms in the homotopy category of
  `ringedSiteModuleCategory J 𝒪`;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `tensor_left_homotopy_functor`,
  `tensorHom_right_quasiIso_of_isKFlat`;
- best owner abstraction: the Chapter 15 owner theorem
  `tensorHom_right_quasiIso_of_isKFlat`;
- primitive vs derived: the primitive data are a complex `K`, a proof `hK : K.IsKFlat`, a map
  `f`, and a proof that `f` is a quasi-isomorphism; the ringed-site statement is derived API by
  specializing the ambient category to `ringedSiteModuleCategory J 𝒪`, not by introducing a
  second owner theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-site formulation of the Stacks Project lemma;
- `core/canonical`: `tensorHom_right_quasiIso_of_isKFlat`;
- `bridge/view`: this file, which records only the direct specialization to
  `ringedSiteModuleCategory J 𝒪`. -/

-- Proof sketch: by Lemma `21.17.1`, the fixed-right-factor tensor-totalization functor on
-- `K(\mathrm{Mod}(\mathcal O))` is triangulated. A quasi-isomorphism is characterized by its
-- cone being acyclic, and Definition `21.17.2` says that tensoring an acyclic complex with a
-- K-flat complex remains acyclic. Therefore the image cone is acyclic, so the image morphism is a
-- quasi-isomorphism.
/- Lemma 21.17.3 is the ringed-site specialization of the Chapter 15 owner theorem asserting that
totalized tensoring with a fixed K-flat right factor preserves quasi-isomorphisms in the homotopy
category. -/
recall tensorHom_right_quasiIso_of_isKFlat

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_4 (from Chap21) -/
open CategoryTheory Limits MonoidalCategory ComplexShape

noncomputable section

universe u v

set_option checkBinderAnnotations false
set_option quotPrecheck false

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

section

variable {𝒪 : Sheaf J CommRingCat.{max u v}}

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ X : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj X).Additive]

variable (U : C)

variable [Preadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [HasZeroObject (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))]
variable [(curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).Additive]
variable [∀ X : ringedSiteModuleCategory (J.over U) (𝒪.over U),
  ((curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).obj X).Additive]
variable [(SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))).Additive]

/- Domain-style sampling for Lemma 21.17.4:
- primary domain: K-flat cochain complexes of sheaves of modules on a ringed site and their
  restriction to a localized ringed site;
- sampled owner declarations:
  `ringSheaf`,
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `ringedSiteLocalizedExtensionByZero_exact_iff`;
- best owner abstraction: the K-flat predicate `K.IsKFlat` on cochain complexes in the canonical
  module category `ringedSiteModuleCategory`, together with the canonical localized restriction
  functor `SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))`;
- primitive data: the ambient and localized module categories, the object `U : C`, and the given
  K-flat complex `K`;
- derived API: the localized restriction complex obtained by applying the canonical restriction
  functor degreewise.

Source/core/bridge triage:
- `source-facing`: K-flatness of the localized restriction `K^•|_U`;
- `core/canonical`: `ringSheaf J 𝒪`, `ringedSiteModuleCategory`, and `CochainComplex.IsKFlat`;
- `bridge/view`: the restriction functor on complexes induced by
  `SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))`.

The old local alias `ringedSiteRingSheaf` duplicated the chapter owner `ringSheaf`, so the refined
file uses `ringSheaf` directly and keeps only this source-facing specialization. -/

local instance : Preadditive (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change Preadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance : HasZeroObject (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change HasZeroObject (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance : MonoidalCategory (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change MonoidalCategory (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance : MonoidalPreadditive (SheafOfModules ((ringSheaf J 𝒪).over U)) := by
  change MonoidalPreadditive (ringedSiteModuleCategory (J.over U) (𝒪.over U))
  infer_instance

local instance :
    (curriedTensor (SheafOfModules ((ringSheaf J 𝒪).over U))).Additive := by
  change (curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).Additive
  infer_instance

local instance (X : SheafOfModules ((ringSheaf J 𝒪).over U)) :
    ((curriedTensor (SheafOfModules ((ringSheaf J 𝒪).over U))).obj X).Additive := by
  change ((curriedTensor (ringedSiteModuleCategory (J.over U) (𝒪.over U))).obj X).Additive
  infer_instance

-- Proof sketch: let `𝒢^•` be an acyclic complex of `\mathcal O_U`-modules. Apply extension by zero
-- `j_{U!}` to `Tot(𝒢^• \otimes_{\mathcal O_U} K^•|_U)`. Lemma `18.19.3` makes `j_{U!}` exact, and
-- Lemma `18.27.9` identifies the image with `Tot(j_{U!} 𝒢^• \otimes_{\mathcal O} K^•)`, which is
-- acyclic by the K-flatness of `K^•`. Lemma `18.19.4` then reflects exactness back to the
-- localized site.
/-- Lemma 21.17.4: if `K^•` is a K-flat complex of `\mathcal O`-modules on a ringed site and
`U : C`, then the restricted complex `K^•|_U`, formalized by applying the canonical localized
restriction functor degreewise, is K-flat over `\mathcal O_U`. -/
theorem isKFlat_localizedRestriction
    (K : CochainComplex (ringedSiteModuleCategory J 𝒪) ℤ) (hK : K.IsKFlat) :
    (((SheafOfModules.pushforward (𝟙 ((ringSheaf J 𝒪).over U))).mapHomologicalComplex
        (up ℤ)).obj K).IsKFlat := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_5 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (RingedSiteModules 𝒪)]
variable [HasZeroObject (RingedSiteModules 𝒪)]
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]
variable [(curriedTensor (RingedSiteModules 𝒪)).Additive]
variable [∀ X : RingedSiteModules 𝒪, ((curriedTensor (RingedSiteModules 𝒪)).obj X).Additive]
variable [∀ (K L : CochainComplex (RingedSiteModules 𝒪) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor (RingedSiteModules 𝒪))]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site and closure of
  K-flatness under totalized tensor products;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the owner is the predicate `K.IsKFlat` on cochain complexes, and the
  tensor product complex is the canonical derived object `HomologicalComplex.tensorObj K L`;
- primitive vs derived: the primitive data are only the complexes `K`, `L` and their K-flatness
  hypotheses. The tensor product complex is derived from the ambient monoidal structure, so this
  ringed-site file should expose only the specialization of the owner theorem rather than a
  parallel local statement.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of the tensor-closure statement for K-flat
  complexes;
- `core/canonical`: `CochainComplex.tensorObj_isKFlat_of_isKFlat`;
- `bridge/view`: specialization of that owner theorem to `SheafOfModules.RingedSite`. -/

/- Lemma 21.17.5: if `\mathcal K^\bullet` and `\mathcal L^\bullet` are K-flat cochain complexes of
`\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, then the totalized tensor
product `\mathrm{Tot}(\mathcal K^\bullet \otimes_\mathcal O \mathcal L^\bullet)` is K-flat. This
is exactly the specialization of the canonical owner theorem
`CochainComplex.tensorObj_isKFlat_of_isKFlat` to `RingedSiteModules 𝒪`. -/
recall CochainComplex.tensorObj_isKFlat_of_isKFlat

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_6 (from Chap21) -/
namespace SheafOfModules.RingedSite

/- Domain-style sampling for Lemma 21.17.6:
- primary domain: K-flat cochain complexes in distinguished triangles;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 generic distinguished-triangle two-out-of-three theorems
  for the owner predicate `CochainComplex.IsKFlat`;
- primitive vs derived: primitive data are only a distinguished triangle in the relevant homotopy
  category together with K-flatness of two of its vertices; the ringed-site formulation is derived
  API by specialization, not a second local owner.

Source/core/bridge triage:
- `source-facing`: the ringed-site two-out-of-three property for K-flat complexes in a
  distinguished triangle;
- `core/canonical`: the generic owner theorems
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`, and
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: this file, which should remain only a direct recall of that specialization, with
  no parallel local theorem or extra ambient scaffolding. -/

-- Proof sketch: Lemma `21.17.1` identifies totalized tensoring with a fixed complex on
-- `K(\mathrm{Mod}(\mathcal O))` as a triangulated functor, and Definition `21.17.2` says that
-- K-flatness means this functor sends acyclic complexes to acyclic complexes. Applying the generic
-- Chapter 15 distinguished-triangle two-out-of-three theorem at the owner level yields the
-- ringed-site statement directly.
/- Lemma 21.17.6 is the ringed-site specialization of the generic distinguished-triangle
two-out-of-three property for the owner predicate `CochainComplex.IsKFlat`. -/
recall CochainComplex.isKFlat_obj₃_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₂_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₁_of_distinguished_triangle

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_7 (from Chap21) -/
open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 : Sheaf J CommRingCat.{u}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable {S : ShortComplex (CochainComplex Mod ℤ)}

/- Domain-style sampling for Lemma 21.17.7:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site in a short
  exact sequence;
- inspected owner declarations:
  `ShortComplex.ShortExact`,
  `CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃`,
  `CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃_of_flat_X₃`,
  `CochainComplex.IsKFlat`;
- best owner abstraction: the primitive owner data are the short complex `S` and its short
  exactness proof `hS : S.ShortExact`; the three K-flatness conclusions are derived API attached
  to the owner namespace `CategoryTheory.ShortComplex.ShortExact`;
- primitive vs derived: primitive data are only `S`, `hS`, and the termwise flatness hypothesis on
  `S.X₃`; the K-flatness of `S.X₁`, `S.X₂`, `S.X₃` remains theorem-level derived API.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of the short-exact two-out-of-three K-flatness
  criterion from the Stacks Project;
- `core/canonical`: the short-exact owner namespace `CategoryTheory.ShortComplex.ShortExact`;
- `bridge/view`: the owner predicate `CochainComplex.IsKFlat` on the three terms of `S`. -/

-- Proof sketch: for any acyclic complex `L`, Lemma `18.28.9` gives a short exact sequence of
-- tensor complexes
-- `0 ⟶ Tot(L ⊗ K₁) ⟶ Tot(L ⊗ K₂) ⟶ Tot(L ⊗ K₃) ⟶ 0`
-- because the terms of `K₃` are flat. If `K₁` and `K₂` are K-flat, the first two tensor complexes
-- are acyclic, so the third is acyclic by the long exact sequence of cohomology sheaves.
/-- Lemma 21.17.7 (1): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
every term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_2^\bullet` are K-flat, then `\mathcal K_3^\bullet` is K-flat. -/
theorem isKFlat_X₃_of_flat_X₃ (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, IsFlat 𝒪 (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

-- Proof sketch: tensor the given short exact sequence with an arbitrary acyclic complex and use
-- Lemma `18.28.9` to preserve short exactness under the termwise flatness hypothesis on
-- `\mathcal K_3^\bullet`. If `K₁` and `K₃` are K-flat, the outer tensor complexes are acyclic, so
-- the middle one is acyclic by the long exact sequence of cohomology sheaves.
/-- Lemma 21.17.7 (2): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
every term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_2^\bullet` is K-flat. -/
theorem isKFlat_X₂_of_flat_X₃ (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, IsFlat 𝒪 (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

-- Proof sketch: after tensoring with an arbitrary acyclic complex, Lemma `18.28.9` again gives a
-- short exact sequence of tensor complexes because the terms of `K₃` are flat. If `K₂` and `K₃`
-- are K-flat, the last two tensor complexes are acyclic, and the first becomes acyclic by the
-- associated long exact sequence on cohomology sheaves.
/-- Lemma 21.17.7 (3): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, if
every term of `\mathcal K_3^\bullet` is flat and `\mathcal K_2^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_1^\bullet` is K-flat. -/
theorem isKFlat_X₁_of_flat_X₃ (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, IsFlat 𝒪 (S.X₃.X n))
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end CategoryTheory.ShortComplex.ShortExact

/-! ### Lemma_21_17_8 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

variable {𝒪 : Sheaf J CommRingCat.{u}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]

/- Domain-style sampling for Lemma 21.17.8:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site;
- inspected owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`;
- best owner abstraction: the ambient module category is the Chapter 18 owner
  `ringedSiteModuleCategory J 𝒪`, and K-flatness is the Chapter 15 owner predicate `K.IsKFlat`
  on complexes in that category;
- primitive data: the complex `K`, the bounded-above hypothesis, and termwise flatness of the
  modules `K.X n`;
- derived API: the K-flatness conclusion.

Source/core/bridge triage:
- `source-facing`: the bounded-above flat criterion on the ringed site;
- `core/canonical`: `ringedSiteModuleCategory` and `CochainComplex.IsKFlat`;
- `bridge/view`: this specialization of the canonical K-flat owner to ringed-site modules.
-/

-- Proof sketch: let `ℒ` be an acyclic complex of `\mathcal O`-modules. Write `ℒ` as the
-- termwise filtered colimit of its bounded-above truncations `τ_{\le m} ℒ`, so the total tensor
-- product with `K` is the corresponding filtered colimit of the total tensors with these
-- truncations. It is therefore enough to treat bounded-above acyclic `ℒ`. For such `ℒ`, apply the
-- homology spectral sequence of the double complex `ℒ ⊗ K`; the `E₁`-page is
-- `H^p(ℒ ⊗ K^q)`, which vanishes because each term `K^q` is flat and `ℒ` is acyclic. Hence the
-- total tensor product is acyclic, so `K` is K-flat.
/-- Lemma 21.17.8: a bounded above cochain complex of flat `\mathcal O`-modules on a ringed site
`(\mathcal C, \mathcal O)` is K-flat, expressed in the canonical owner predicate `K.IsKFlat`.
-/
theorem isKFlat_of_boundedAbove_of_flat
    (K : CochainComplex Mod ℤ)
    (hbounded : IsBoundedAbove K)
    (hFlat : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    K.IsKFlat := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_9 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

variable [Preadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasZeroObject (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [(curriedTensor (ringedSiteModuleCategory J 𝒪)).Additive]
variable [∀ ℱ : ringedSiteModuleCategory J 𝒪,
  ((curriedTensor (ringedSiteModuleCategory J 𝒪)).obj ℱ).Additive]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O`-modules on a ringed site and their
  stability under sequential colimits;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.isKFlat_colimit_of_isFiltered`;
- best owner abstraction: the ambient owner category is `ringedSiteModuleCategory J 𝒪`, and the
  K-flatness predicate is the generic owner `(K : CochainComplex Mod ℤ).IsKFlat`;
- primitive vs derived: the primitive data are only the sequential diagram `F` and the K-flatness
  hypotheses on its stages. The colimit complex and its K-flatness are derived from the ambient
  colimit and the owner predicate, so this file should not keep a parallel local module-category
  alias or a local K-flat wrapper in the theorem surface.

Source/core/bridge triage:
- `source-facing`: the ringed-site specialization of sequential-colimit stability for K-flat
  complexes;
- `core/canonical`: `ringedSiteModuleCategory J 𝒪` and `CochainComplex.IsKFlat`;
- `bridge/view`: none. This file should state the ringed-site theorem directly using those owners.

The module-category theorem `CochainComplex.isKFlat_colimit_of_isFiltered` is the owner
declaration in the same domain; the present file keeps the genuinely new ringed-site sequential
specialization rather than a duplicate local wrapper around the ambient category or predicate. -/

-- Proof sketch: tensor an arbitrary acyclic complex `ℱ^•` with the sequential diagram `F`.
-- Termwise tensor products commute with the colimit, so
-- `Tot(ℱ^• ⊗ colim_i K_i^•)` is identified with the colimit of the acyclic tensor complexes
-- `Tot(ℱ^• ⊗ K_i^•)`. Exactness of filtered colimits on sheaves of modules then implies that this
-- colimit tensor complex is acyclic.
/-- Lemma 21.17.9: for a system `\mathcal K_1^\bullet \to \mathcal K_2^\bullet \to \cdots` of
K-flat cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)`, the
sequential colimit `\mathop{\mathrm{colim}}_i \mathcal K_i^\bullet` is K-flat. -/
theorem sequentialColimit_isKFlat
    (F : ℕ ⥤ CochainComplex Mod ℤ)
    [HasColimit F]
    (hF : ∀ i : ℕ, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_10 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J CommRingCat.{u})
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]

local notation "ModCat" => SheafOfModules (ringSheaf J 𝒪)

/-- The object property on `Mod(\mathcal O)` saying that a module is a direct sum, equivalently a
categorical coproduct, of modules of the form `j_{U!}\mathcal O_U`. -/
def isCoproductOfLocalizedStructureModules : CategoryTheory.ObjectProperty ModCat :=
  fun ℱ ↦ ∃ (I : Type u) (U : I → C), Nonempty (ℱ ≅ ∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i))

-- Proof sketch: this is immediate from the definition by packaging the displayed coproduct
-- presentation as a witness for the object property.
/-- A chosen coproduct presentation by modules `j_{U!}\mathcal O_U` gives the corresponding object
property. -/
theorem isCoproductOfLocalizedStructureModules_of_iso
    {ℱ : ModCat} {I : Type u} {U : I → C}
    (e : ℱ ≅ ∐ fun i : I ↦ localizedStructureModuleExtensionByZero 𝒪 (U i)) :
    isCoproductOfLocalizedStructureModules 𝒪 ℱ := sorry

/-- The zero `\mathcal O`-module is the empty coproduct of localized structure modules. -/
instance isCoproductOfLocalizedStructureModules_containsZero :
    (isCoproductOfLocalizedStructureModules 𝒪).ContainsZero := sorry

/-- Finite coproducts of coproducts of localized structure modules are again coproducts of
localized structure modules. -/
instance isCoproductOfLocalizedStructureModules_isClosedUnderFiniteCoproducts :
    (isCoproductOfLocalizedStructureModules 𝒪).IsClosedUnderFiniteCoproducts := sorry

/-- Every `\mathcal O`-module admits an epimorphism from a coproduct of localized structure
modules. -/
instance isCoproductOfLocalizedStructureModules_hasEpiCover :
    CategoryTheory.ObjectProperty.HasEpiCover
      (isCoproductOfLocalizedStructureModules 𝒪) := sorry

-- Proof sketch: use Lemma `18.28.8 (3)` to obtain objectwise epimorphic covers by coproducts of
-- `j_{U!}\mathcal O_U`, feed this object property into Lemma `13.29.1` to get the compatible
-- upper-truncation resolution tower, and then apply exactness of filtered colimits in `Mod(𝒪)`
-- to deduce that the canonical colimit map is a quasi-isomorphism.
/-- Lemma 21.17.10: every complex of `\mathcal O`-modules on a ringed site admits a compatible
upper-truncation resolution tower by bounded-above complexes whose terms and successive degreewise
cokernels are coproducts of modules `j_{U!}\mathcal O_U` such that the canonical morphism from
the sequential colimit of the tower to the original complex is a quasi-isomorphism. -/
theorem exists_upperTruncationResolutionTower_of_localizedStructureModuleCoproducts
    (𝒢 : CochainComplex ModCat ℤ) :
    ∃ T :
        CategoryTheory.UpperTruncationResolutionTower
          (isCoproductOfLocalizedStructureModules 𝒪) 𝒢,
      QuasiIso T.fromColimit := sorry

end

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_11 (from Chap21) -/
open CategoryTheory CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

-- Proof sketch: choose the upper-truncation resolution tower from Lemma `21.17.10`. Each stage is
-- bounded above and has terms that are coproducts of the localized structure modules
-- `j_{U!}\mathcal O_U`, hence flat by Lemma `18.28.7`; then Lemma `21.17.8` makes every stage
-- K-flat. Apply Lemma `21.17.9` to the sequential colimit of the tower. The induced comparison to
-- `\mathcal G^\bullet` is a quasi-isomorphism and termwise epimorphic by the construction in
-- Lemma `21.17.10`, and each term of the colimit is again flat because it is a direct sum of flat
-- modules.
/-- Lemma 21.17.11: every cochain complex `\mathcal G^\bullet` of `\mathcal O`-modules on a
ringed site `(\mathcal C, \mathcal O)` admits a quasi-isomorphism from a K-flat cochain complex
whose terms are flat `\mathcal O`-modules, and this quasi-isomorphism is termwise surjective. -/
theorem exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex (RingedSiteModules 𝒪) ℤ) :
    ∃ (K : CochainComplex (RingedSiteModules 𝒪) ℤ) (hK : IsKFlat K)
      (hFlat : ∀ n : ℤ,
        IsFlat 𝒪 (show SheafOfModules (ringSheaf J 𝒪) from K.X n))
      (α : K ⟶ 𝒢), QuasiIso α ∧ ∀ n : ℤ, Epi (α.f n) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_12 (from Chap21) -/
open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed
site `(\mathcal C, \mathcal O)`. -/
private abbrev ringedSiteModules (𝒪 : Sheaf J CommRingCat.{max u v}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable [Preadditive (ringedSiteModules 𝒪)]
variable [HasZeroObject (ringedSiteModules 𝒪)]
variable [HasBinaryBiproducts (ringedSiteModules 𝒪)]
variable [Abelian (ringedSiteModules 𝒪)]
variable [CategoryWithHomology (ringedSiteModules 𝒪)]
variable [HasCountableCoproducts (ringedSiteModules 𝒪)]
variable [MonoidalCategory (ringedSiteModules 𝒪)]
variable [MonoidalPreadditive (ringedSiteModules 𝒪)]
variable [HasColimits (ringedSiteModules 𝒪)]
variable [(curriedTensor (ringedSiteModules 𝒪)).Additive]
variable [∀ X : ringedSiteModules 𝒪,
  ((curriedTensor (ringedSiteModules 𝒪)).obj X).Additive]
variable [∀ (X Y : CochainComplex (ringedSiteModules 𝒪) ℤ),
  CochainComplex.HasMapBifunctor X Y (curriedTensor (ringedSiteModules 𝒪))]

-- Proof sketch: choose a quasi-isomorphism `K^• ⟶ F^•` from a K-flat complex using Lemma
-- `21.17.11`. Lemma `21.17.3` shows that tensoring this comparison with either `P^•` or `Q^•`
-- gives quasi-isomorphisms on the vertical maps, and tensoring the quasi-isomorphism `α` with the
-- K-flat complex `K^•` gives a quasi-isomorphism on the top horizontal map. The commutative
-- square then forces the bottom horizontal map to be a quasi-isomorphism.
/-- Lemma 21.17.12: if `α : \mathcal P^\bullet ⟶ \mathcal Q^\bullet` is a quasi-isomorphism
between K-flat cochain complexes of `\mathcal O`-modules on a ringed site `(\mathcal C,
\mathcal O)`, then for every cochain complex `\mathcal F^\bullet` the induced map
`\mathrm{Tot}(\mathrm{id}_{\mathcal F^\bullet} \otimes \alpha) :
\mathrm{Tot}(\mathcal F^\bullet \otimes_\mathcal O \mathcal P^\bullet) ⟶
\mathrm{Tot}(\mathcal F^\bullet \otimes_\mathcal O \mathcal Q^\bullet)` is a quasi-isomorphism.
-/
theorem quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat
    (F P Q : CochainComplex (ringedSiteModules 𝒪) ℤ)
    (hP : CochainComplex.IsKFlat P) (hQ : CochainComplex.IsKFlat Q)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) α) := sorry

end SheafOfModules.RingedSite

/-! ### Definition_21_17_13 (from Chap21) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace SheafOfModules.RingedSite

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪
local notation "KMod" => HomotopyCategory Mod (up ℤ)
local notation "DMod" => DerivedCategory Mod
local notation "Qis" => HomotopyCategory.quasiIso Mod (up ℤ)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)

/- Domain-style sampling for Definition 21.17.13:
- primary domain: derived tensor products on the unbounded derived category of sheaves of
  `\mathcal O`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `tensor_left_homotopy_functor`,
  `Functor.HasLeftDerivedFunctor`,
  `Functor.totalLeftDerived`;
- best owner abstraction: the ambient owner is `ringedSiteModuleCategory J 𝒪`, and the source
  definition is the total left derived endofunctor of homotopy-category tensoring with a fixed
  right factor;
- primitive vs derived: the primitive public data are the ambient ringed-site module category and
  the fixed object `F : DerivedCategory (ringedSiteModuleCategory J 𝒪)`. Chosen representatives in
  the homotopy category are internal implementation data, while the endofunctor
  `derivedTensorProduct F` and the notation `K ⊗^L L` are the derived public API.

Source/core/bridge triage:
- `source-facing`: the derived tensor product endofunctor `- ⊗^L F` on `D(\mathcal O)`;
- `core/canonical`: `Functor.totalLeftDerived` applied to the fixed-right-factor homotopy tensor
  functor on `ringedSiteModuleCategory J 𝒪`;
- `bridge/view`: the scoped notation `K ⊗^L L` for evaluating the owner endofunctor on objects. -/

variable [hAbelian : Abelian Mod]
variable [CategoryWithHomology Mod]
variable [hCount : HasCountableCoproducts Mod]
variable (monoidalMod : MonoidalCategory Mod)
local instance instMonoidalMod : MonoidalCategory Mod := monoidalMod
variable [MonoidalPreadditive Mod]
variable [hColim : HasColimits Mod]
variable (hCurriedTensorAdditive : (curriedTensor Mod).Additive)
local instance instCurriedTensorAdditive : (curriedTensor Mod).Additive := hCurriedTensorAdditive

variable (hTensorObjAdditive : ∀ X : Mod, ((curriedTensor Mod).obj X).Additive)
local instance instTensorObjAdditive (X : Mod) : ((curriedTensor Mod).obj X).Additive :=
  hTensorObjAdditive X

variable
    (hMapBifunctor :
      ∀ (X Y : CochainComplex Mod ℤ), CochainComplex.HasMapBifunctor X Y (curriedTensor Mod))
local instance instMapBifunctor
    (X Y : CochainComplex Mod ℤ) :
    CochainComplex.HasMapBifunctor X Y (curriedTensor Mod) :=
  hMapBifunctor X Y

/-- The homotopy-category tensor functor whose left derived functor defines derived tensoring with
a fixed right factor in `D(\mathcal O)`. -/
private noncomputable abbrev derivedTensorSourceFunctor
    (F : DMod) :
    KMod ⥤ DMod :=
  CategoryTheory.Quotient.lift (homotopic Mod (up ℤ))
    ((((curriedTensor Mod).map₂CochainComplex).flip.obj
        (Qh.objPreimage F).as) ⋙ HomotopyCategory.quotient Mod (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 (Qh.objPreimage F).as)
          (curriedTensor Mod) (up ℤ))) ⋙
    Qh

-- Proof sketch: choose a homotopy-category representative of `F`, replace it by a K-flat
-- resolution using the flat-resolution results developed above, and use the quasi-isomorphism
-- invariance of tensoring with a K-flat complex to invoke the universal property of the total left
-- derived functor.
/-- Tensoring on the homotopy category with a fixed derived right factor admits a total left
derived functor on `D(\mathcal O)`. -/
theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (F : DMod) :
    (derivedTensorSourceFunctor F).HasLeftDerivedFunctor Qis := sorry

/-- Definition 21.17.13: for an object `\mathcal F^\bullet` of `D(\mathcal O)`, the derived tensor
product `- \otimes_\mathcal O^{\mathbf L} \mathcal F^\bullet` is the endofunctor of `D(\mathcal
O)` obtained by left deriving the homotopy-category tensor functor with fixed right factor a
chosen representative of `\mathcal F^\bullet`. -/
noncomputable def derivedTensorProduct
    (F : DMod) :
    DMod ⥤ DMod :=
  let G : KMod ⥤ DMod := derivedTensorSourceFunctor F
  letI : G.HasLeftDerivedFunctor Qis :=
    derivedTensorSourceFunctor_hasLeftDerivedFunctor F
  G.totalLeftDerived Qh Qis

-- Proof sketch: the homotopy-category tensor functor with fixed right factor commutes with the
-- shift by Remark `13.10.9`, and the total left derived functor inherits this commutation.
/-- Derived tensoring with a fixed right factor commutes with the triangulated shift. -/
noncomputable instance derivedTensorProduct_commShift
    (F : DMod) :
    (derivedTensorProduct F).CommShift ℤ := sorry

-- Proof sketch: the underived tensor functor on the homotopy category is triangulated by Remark
-- `13.10.9`, and passing to its total left derived functor yields an exact functor on the derived
-- category.
/-- The derived tensor product endofunctor on `D(\mathcal O)` is exact in the triangulated sense.
-/
theorem derivedTensorProduct_isTriangulated
    (F : DMod) :
    (derivedTensorProduct F).IsTriangulated := sorry

end

end SheafOfModules.RingedSite

namespace RingedSiteDerivedTensor

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in `D(\mathcal O)`.
-/
scoped notation:70 K:70 " ⊗^L " L:71 =>
  CategoryTheory.Functor.obj (SheafOfModules.RingedSite.derivedTensorProduct L) K

end RingedSiteDerivedTensor

/-! ### Definition_21_17_14 (from Chap21) -/
open CategoryTheory

noncomputable section

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Definition 21.17.14:
- primary domain: the monoidal homological algebra of sheaves of `𝒪`-modules on a ringed site;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `CategoryTheory.Tor`,
  `SheafOfModules`,
  `SheafOfModules.RingedSite.derivedTensorProduct`;
- best owner abstraction: the ambient module category owner is `ringedSiteModuleCategory J 𝒪`,
  and the `p`-th Tor construction is the canonical bifunctor `Tor Mod p`;
- primitive data versus derived API: primitive data are only the ringed site and the ambient
  monoidal/projective-resolution structure on `Mod`; the object
  `((Tor Mod p).obj ℱ).obj 𝒢` is derived API obtained by evaluating the canonical owner.

Source/core/bridge triage:
- `source-facing`: the object `\operatorname{Tor}_p^\mathcal O(\mathcal F, \mathcal G)`;
- `core/canonical`: `Tor Mod p`;
- `bridge/view`: this file is only the ringed-site specialization of that canonical owner, so it
  should reuse `ringedSiteModuleCategory` and `Tor` directly rather than reintroducing a local
  category alias. -/

variable [MonoidalCategory (ringedSiteModuleCategory J 𝒪)]
variable [MonoidalPreadditive (ringedSiteModuleCategory J 𝒪)]
variable [HasProjectiveResolutions (ringedSiteModuleCategory J 𝒪)]
variable (p : ℕ)

/- Definition 21.17.14: for a ringed site `(\mathcal C, \mathcal O)`, the `p`-th Tor on
`Mod(\mathcal O)` is the canonical monoidal `Tor` bifunctor. Evaluated at `\mathcal F` and
`\mathcal G`, it is the source object `\operatorname{Tor}_p^\mathcal O(\mathcal F, \mathcal G)`,
which the text describes as `H^{-p}(\mathcal F \otimes_\mathcal O^{\mathbf L} \mathcal G)`. -/
#check (Tor Mod p)

variable (ℱ 𝒢 : Mod)

/- Companion recall: evaluating the canonical Tor bifunctor at `\mathcal F` and `\mathcal G`
gives the object `\operatorname{Tor}_p^\mathcal O(\mathcal F, \mathcal G)`. -/
#check (((Tor Mod p).obj ℱ).obj 𝒢)

/-! ### Lemma_21_17_15 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}

local notation "Mod" => ringedSiteModuleCategory J 𝒪

/- Domain-style sampling for Lemma 21.17.15:
- primary domain: flat sheaves of modules on a ringed site and the first left-derived tensor
  functor on the ambient monoidal abelian category `Mod`;
- sampled owner declarations:
  `ringedSiteModuleCategory`,
  `SheafOfModules.RingedSite.IsFlat`,
  `CategoryTheory.Tor`,
  `Definition_21_17_14`'s chapter-21 specialization `Tor Mod p`;
- best owner abstraction: flatness is already owned by `SheafOfModules.RingedSite.IsFlat`, while
  the Tor side of the criterion is already owned by the canonical bifunctor `Tor Mod 1`; this item
  should stay a source-facing criterion theorem and reuse that owner directly;
- primitive data: the module `ℱ : Mod`;
- derived API: the vanishing condition `∀ 𝒢 : Mod, IsZero (((Tor Mod 1).obj ℱ).obj 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the flatness criterion stated as vanishing of `Tor₁`;
- `core/canonical`: `SheafOfModules.RingedSite.IsFlat` and `Tor Mod 1`;
- `bridge/view`: no extra bridge is needed here, because Definition `21.17.14` already records the
  ringed-site specialization of the canonical Tor owner. -/

variable [MonoidalCategory Mod]
variable [MonoidalPreadditive Mod]
variable [HasProjectiveResolutions Mod]

-- Proof sketch: if `ℱ` is flat, then tensoring with `ℱ` is exact, so its first left derived
-- functor vanishes and hence `Tor₁` is zero against every `𝒢`. Conversely, apply the long exact
-- `Tor` sequence to a short exact sequence `0 ⟶ 𝒢 ⟶ ℋ ⟶ 𝒬 ⟶ 0`; vanishing of `Tor₁(ℱ, 𝒬)` forces
-- tensoring with `ℱ` to preserve monomorphisms, which is the flatness criterion.
/-- Lemma 21.17.15: a sheaf of `\mathcal O`-modules on a ringed site is flat if and only if
`\operatorname{Tor}_1^\mathcal O(\mathcal F, \mathcal G)` vanishes for every
`\mathcal O`-module `\mathcal G`. -/
theorem isFlat_iff_isZero_tor_one
    (ℱ : Mod) :
    IsFlat 𝒪 ℱ ↔
      ∀ 𝒢 : Mod, IsZero (((Tor Mod 1).obj ℱ).obj 𝒢) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_16 (from Chap21) -/
open CategoryTheory
open CategoryTheory.Limits
open CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the given
ringed site. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

-- Proof sketch: let `ℱ := kernel (K.dFrom n)`. Because `K` is acyclic, the brutal truncation
-- `\cdots ⟶ K^{n-2} ⟶ K^{n-1} ⟶ ℱ ⟶ 0` is a flat resolution of `ℱ`. Lemma `21.17.8` makes that
-- bounded-above flat complex K-flat, so it computes `Tor_1^\mathcal O(ℱ, 𝒢)` for every module
-- `𝒢`. Since `K` itself is K-flat and acyclic, derived tensoring `K` with `𝒢` is zero, forcing
-- `Tor_1^\mathcal O(ℱ, 𝒢) = 0`; then Lemma `21.17.15` yields flatness of `ℱ`.
/-- Lemma 21.17.16: if `K` is a K-flat acyclic cochain complex of flat `\mathcal O`-modules on a
ringed site, then the kernel of the differential `K^n \to K^{n+1}` is a flat
`\mathcal O`-module. -/
theorem isFlat_kernel_dFrom_of_isKFlat_of_acyclic
    (K : CochainComplex (RingedSiteModules 𝒪) ℤ) (n : ℤ)
    (hKFlat : IsKFlat K) (hAcyclic : K.Acyclic)
    (hFlat : ∀ i : ℤ, IsFlat 𝒪 (K.X i)) :
    IsFlat 𝒪 (kernel (K.dFrom n)) := sorry

end SheafOfModules.RingedSite

/-! ### Lemma_21_17_17 (from Chap21) -/
open CategoryTheory HomologicalComplex CochainComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The category `\mathrm{Mod}(\mathcal O)` of sheaves of `\mathcal O`-modules on the ringed site
`(\mathcal C, \mathcal O)`. -/
private abbrev RingedSiteModules (𝒪 : Sheaf J CommRingCat.{u}) :=
  SheafOfModules ((sheafCompose J (forget₂ CommRingCat RingCat)).obj 𝒪)

variable {𝒪 : Sheaf J CommRingCat.{u}}
variable [MonoidalCategory (RingedSiteModules 𝒪)]
variable [MonoidalPreadditive (RingedSiteModules 𝒪)]

variable {K L N : CochainComplex (RingedSiteModules 𝒪) ℤ}

/-- A factorization of `a` up to homotopy through a quasi-isomorphism `c : \mathcal N^\bullet ⟶
\mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
class IsKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop where
  /-- The morphism `a` is homotopic to the composite factorization `b ≫ c`. -/
  homotopy : Nonempty (Homotopy a (b ≫ c))
  /-- The intermediate complex is K-flat. -/
  isKFlat : IsKFlat N
  /-- The comparison map to `\mathcal L^\bullet` is a quasi-isomorphism. -/
  quasiIso : QuasiIso c

/-- A K-flat factorization up to homotopy whose intermediate complex has flat terms. -/
class IsTermwiseFlatKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop
    extends IsKFlatFactorizationUpToHomotopy a b c where
  /-- Every term of the intermediate complex is a flat `\mathcal O`-module. -/
  term_flat : ∀ n : ℤ, IsFlat 𝒪 (N.X n)

-- Proof sketch: complete `a` to a distinguished triangle in the homotopy category, choose a
-- K-flat quasi-isomorphism `M ⟶ cone(a)` with flat terms using Lemma `21.17.11`, and then fit the
-- composite `M ⟶ cone(a) ⟶ K⟦1⟧` into a distinguished triangle `K ⟶ N ⟶ M ⟶ K⟦1⟧`. Lemma
-- `21.17.6` gives `N` K-flat, and the comparison of distinguished triangles yields a map `N ⟶ L`
-- whose composite with `K ⟶ N` is homotopic to `a`; two-out-of-three shows `N ⟶ L` is a
-- quasi-isomorphism.
/-- Lemma 21.17.17: if `a : \mathcal K^\bullet ⟶ \mathcal L^\bullet` is a morphism of cochain
complexes of `\mathcal O`-modules on a ringed site `(\mathcal C, \mathcal O)` and
`\mathcal K^\bullet` is K-flat, then `a` factors up to homotopy through a quasi-isomorphism
`c : \mathcal N^\bullet ⟶ \mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (a : K ⟶ L) (hK : IsKFlat K) :
    ∃ (N : CochainComplex (RingedSiteModules 𝒪) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsKFlatFactorizationUpToHomotopy a b c := sorry

-- Proof sketch: apply the main factorization theorem after choosing the comparison triangle in the
-- degreewise split form of Lemma `13.10.7`. In that model, each term of the middle complex is a
-- direct sum of the corresponding terms of `K` and of the chosen K-flat replacement of the cone,
-- so the flatness of the terms of `K` and of the replacement passes termwise to `N`.
/-- If the source complex has flat terms, the K-flat factorization can be chosen with flat terms as
well. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (a : K ⟶ L) (hK : IsKFlat K)
    (hFlatK : ∀ n : ℤ, IsFlat 𝒪 (K.X n)) :
    ∃ (N : CochainComplex (RingedSiteModules 𝒪) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsTermwiseFlatKFlatFactorizationUpToHomotopy a b c := sorry

end SheafOfModules.RingedSite
