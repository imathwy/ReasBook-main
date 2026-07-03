import Mathlib
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_20_26_1 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits ComplexShape HomotopyCategory MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

set_option checkBinderAnnotations false

/-
Domain-style sampling for Lemma 20.26.1:
- primary domain: triangulated tensor-totalization functors on homotopy categories of cochain
  complexes in a preadditive monoidal category;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.IsTriangulated`;
- best owner abstraction: the Chapter 13 owner theorem
  `Functor.mapHomotopyCategory` on the fixed-factor tensor-complex functors for a bilinear
  bifunctor;
- primitive data: a bilinear bifunctor `tensor : 𝒜 ⥤ ℬ ⥤ 𝒞` together with fixed complexes in the
  source variables;
- derived API here: the specialization `tensor := curriedTensor (RingedSpace.Modules X)` on the homotopy
  category of `\mathcal O_X`-modules.

Source/core/bridge triage:
- `source-facing`: the exactness of the two endofunctors
  `\mathcal F^\bullet ↦ \mathrm{Tot}(\mathcal G^\bullet \otimes_{\mathcal O_X}
  \mathcal F^\bullet)` and
  `\mathcal F^\bullet ↦ \mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X}
  \mathcal G^\bullet)`;
- `core/canonical`: the two fixed-factor tensor functors
  `((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex.obj 𝒢).mapHomotopyCategory
    (up ℤ)` and
  `((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex.flip.obj 𝒢).mapHomotopyCategory
    (up ℤ)`;
- `bridge/view`: specializing the bilinear owner theorem to the ringed-space tensor bifunctor
  `curriedTensor (RingedSpace.Modules X)`.

This file carries no ringed-space-specific primitive tensor data beyond that specialization, so the
correct refinement is to recall the Chapter 13 owner theorem directly rather than keep a duplicate
Chapter 20 wrapper with the same interface.
-/

section

variable {X : RingedSpace.{u}}

variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [HasBinaryBiproducts (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

variable (𝒢 : CochainComplex (RingedSpace.Modules X) ℤ)

/- Lemma 20.26.1: for a ringed space `(X, \mathcal O_X)` and a complex `\mathcal G^\bullet`, the
two fixed-factor tensor-totalization functors on the homotopy category are exactly the Chapter 13
triangulated tensor functors specialized to `curriedTensor (RingedSpace.Modules X)`. -/
example :
    let F : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
        HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₂ (𝟙 𝒢) h
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

example :
    let F : HomotopyCategory (RingedSpace.Modules X) (up ℤ) ⥤
        HomotopyCategory (RingedSpace.Modules X) (up ℤ) :=
      CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))
    let _ : F.CommShift ℤ := by
      change (CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
        ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj 𝒢) ⋙
          HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
        (fun _ _ _ _ ⟨h⟩ ↦
          HomotopyCategory.eq_of_homotopy _ _
            (HomologicalComplex.mapBifunctorMapHomotopy₁ h (𝟙 𝒢)
              (curriedTensor (RingedSpace.Modules X)) (up ℤ)))).CommShift ℤ
      infer_instance
    Functor.IsTriangulated F := by
  sorry

end

end AlgebraicGeometry.RingedSpace

/-! ### Definition_20_26_2 (from Chap20) -/
noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 20.26.2:
- primary domain: K-flat cochain complexes of sheaves of modules on a ringed space;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 owner is the predicate `CochainComplex.IsKFlat K` on the
  cochain complex itself;
  ringed-space K-flatness is the specialization of that owner to `(RingedSpace.Modules X)`, not a second
  local predicate;
- primitive vs derived: the primitive data is only the complex `K`, while the preservation of
  acyclic complexes under totalized tensoring is exactly the companion theorem
  `CochainComplex.isKFlat_iff`.

Source/core/bridge triage:
- `source-facing`: the textbook K-flatness notion for complexes of `\mathcal O_X`-modules;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: no extra bridge is needed, because the ringed-space notion is exactly this owner
  specialized to `(RingedSpace.Modules X)`. -/

/- Definition 20.26.2: a complex `\mathcal K^\bullet` of `\mathcal O_X`-modules on a ringed
space `(X, \mathcal O_X)` is K-flat if for every acyclic complex `\mathcal F^\bullet`, the
totalized tensor product `\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X}
\mathcal K^\bullet)` is acyclic. This is the canonical owner
`CochainComplex.IsKFlat` specialized to `(RingedSpace.Modules X)`. -/
recall CochainComplex.IsKFlat

/- Totalized tensoring with `K` preserves acyclic complexes exactly when `K` is K-flat; the
canonical companion theorem is `CochainComplex.isKFlat_iff`. -/
recall CochainComplex.isKFlat_iff

section

variable (X : AlgebraicGeometry.RingedSpace)
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable (K : CochainComplex (RingedSpace.Modules X) ℤ)

/- Source-facing specialization: for a ringed space `(X, \mathcal O_X)`, Definition 20.26.2 uses
exactly the Chapter 15 owner predicate and its canonical iff-formulation on `(RingedSpace.Modules X)`. -/
#check K.IsKFlat
#check CochainComplex.isKFlat_iff K

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_3 (from Chap20) -/
/- Domain-style sampling for Lemma 20.26.3:
- primary domain: K-flat complexes and quasi-isomorphisms in the homotopy category of
  `(RingedSpace.Modules X)`;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `tensor_left_homotopy_functor`,
  `tensorHom_right_quasiIso_of_isKFlat`;
- best owner abstraction: the Chapter 15 owner theorem
  `tensorHom_right_quasiIso_of_isKFlat`;
- primitive vs derived: the primitive data are a complex `K`, a proof `hK : K.IsKFlat`, a map
  `f`, and a proof that `f` is a quasi-isomorphism; the ringed-space statement is derived API by
  specializing the ambient category to `(RingedSpace.Modules X)`, not by introducing a second owner
  theorem.

Source/core/bridge triage:
- `source-facing`: the ringed-space formulation of the Stacks Project lemma;
- `core/canonical`: `tensorHom_right_quasiIso_of_isKFlat`;
- `bridge/view`: this file, which records only the direct recall of that owner theorem for later
  specialization to `(RingedSpace.Modules X)`. -/

-- Proof sketch: by Lemma `20.26.1`, the fixed-right-factor tensor-totalization functor on
-- `K(\mathrm{Mod}(\mathcal O_X))` is triangulated. A quasi-isomorphism is characterized by its
-- cone being acyclic, and Definition `20.26.2` says that tensoring an acyclic complex with a
-- K-flat complex remains acyclic. Therefore the image cone is acyclic, so the image morphism is a
-- quasi-isomorphism.
/- Lemma 20.26.3 is the ringed-space specialization of the Chapter 15 owner theorem asserting
that totalized tensoring with a fixed K-flat right factor preserves quasi-isomorphisms in the
homotopy category. -/
recall tensorHom_right_quasiIso_of_isKFlat

/-! ### Lemma_20_26_4 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open ComplexShape

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

/- Domain-style sampling:
- primary domain: stalk functors on sheaves of modules over a ringed space and K-flatness of
  cochain complexes;
- sampled owner declarations:
  `CategoryTheory.point_sheaf_module_stalk_functor`,
  `CategoryTheory.point_stalk_ring`,
  `CategoryTheory.Functor.mapHomologicalComplex`,
  `CochainComplex.IsKFlat`;
- best owner abstraction: the site-point stalk functor
  `point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (RingedSpace.ringCatSheaf X)`; the
  stalk complex is then the canonical derived API obtained via `mapHomologicalComplex`;
- primitive data: a point `x : X` and a complex `K : CochainComplex (RingedSpace.Modules X) ℤ`;
- derived API: the induced stalk complex and its K-flatness predicate.

Source/core/bridge triage:
- `source-facing`: Lemma 20.26.4, which detects K-flatness of a complex on stalks;
- `core/canonical`: `point_sheaf_module_stalk_functor`, `Functor.mapHomologicalComplex`, and
  `CochainComplex.IsKFlat`;
- `bridge/view`: the specialization from the canonical site point `Opens.pointGrothendieckTopology x`
  to the ringed-space stalk functor; no separate local owner is introduced here. -/

-- Proof sketch: for the forward implication, apply K-flatness to the skyscraper-module complex
-- attached to an acyclic stalk complex and then evaluate at `x`. For the converse, test acyclicity
-- of `Tot(F ⊗ K)` on stalks; stalks commute with tensor products and exactness is stalkwise.
/-- Lemma 20.26.4: a complex `\mathcal K^\bullet` of `\mathcal O_X`-modules is K-flat if and only
if, for every point `x : X`, the stalk complex obtained by applying the canonical stalk functor
`point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x) (RingedSpace.ringCatSheaf X)` is
K-flat. -/
theorem isKFlat_iff_stalkwise_isKFlat (K : CochainComplex (RingedSpace.Modules X) ℤ) :
    IsKFlat K ↔
      ∀ x : X, IsKFlat
        (((point_sheaf_module_stalk_functor (Opens.pointGrothendieckTopology x)
            (RingedSpace.ringCatSheaf X)).mapHomologicalComplex (up ℤ)).obj K) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_5 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (K L : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor K L (curriedTensor ((RingedSpace.Modules X)))]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O_X`-modules and their totalized tensor
  product;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.tensorObj_isKFlat_of_isKFlat`,
  `HomologicalComplex.tensorObj`;
- best owner abstraction: the owner is the predicate `K.IsKFlat` on the complex itself, and the
  tensor product is the canonical monoidal tensor `K ⊗ L` on cochain complexes;
- primitive vs derived: the primitive data are only the complexes `K`, `L`, and their K-flatness
  hypotheses. The tensor complex `K ⊗ L` is derived from the ambient monoidal structure, so no
  extra wrapper data should appear in the public API.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the tensor-closure statement for K-flat
  complexes;
- `core/canonical`: the owner theorem `CochainComplex.tensorObj_isKFlat_of_isKFlat`;
- `bridge/view`: the specialization of that owner theorem to `(RingedSpace.Modules X)`. -/

/- Lemma 20.26.5: if `\mathcal K^\bullet` and `\mathcal L^\bullet` are K-flat complexes of
`\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, then the totalized tensor product
`\mathrm{Tot}(\mathcal K^\bullet \otimes_{\mathcal O_X} \mathcal L^\bullet)` is K-flat. This is
exactly the specialization of the canonical owner theorem
`CochainComplex.tensorObj_isKFlat_of_isKFlat` to `(RingedSpace.Modules X)`. -/
recall CochainComplex.tensorObj_isKFlat_of_isKFlat

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_6 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Preadditive (RingedSpace.Modules X)]
variable [HasZeroObject (RingedSpace.Modules X)]
variable [HasBinaryBiproducts (RingedSpace.Modules X)]
variable [Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor (RingedSpace.Modules X)).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor (RingedSpace.Modules X)).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor (RingedSpace.Modules X))]

local notation "KX" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)

/- Domain-style sampling for Lemma 20.26.6:
- primary domain: distinguished triangles of cochain complexes of `\mathcal O_X`-modules on a
  ringed space and the K-flat owner predicate on those complexes;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- best owner abstraction: the Chapter 15 generic `CochainComplex` distinguished-triangle
  two-out-of-three theorems for `IsKFlat`, specialized to `(RingedSpace.Modules X)`;
- primitive vs derived:
  primitive data are only a distinguished triangle in `K((RingedSpace.Modules X))` and the K-flatness
  hypotheses on two of its vertices;
  the ringed-space formulation is derived API by specialization, not a second local owner or
  wrapper.

Source/core/bridge triage:
- `source-facing`: the ringed-space two-out-of-three property for K-flat complexes in a
  distinguished triangle;
- `core/canonical`: the generic owner theorems
  `CochainComplex.isKFlat_obj₃_of_distinguished_triangle`,
  `CochainComplex.isKFlat_obj₂_of_distinguished_triangle`, and
  `CochainComplex.isKFlat_obj₁_of_distinguished_triangle`;
- `bridge/view`: this file, which records only the direct specialization to `(RingedSpace.Modules X)`. -/

-- Proof sketch: Lemma `20.26.1` identifies totalized tensoring with a fixed complex on
-- `K(\mathrm{Mod}(\mathcal O_X))` as a triangulated functor, and Definition `20.26.2` says that
-- K-flatness means this functor sends acyclic complexes to acyclic complexes. Applying the generic
-- Chapter 15 distinguished-triangle two-out-of-three theorem at the owner level yields the
-- ringed-space statement directly.
/- Lemma 20.26.6 is the ringed-space specialization of the generic distinguished-triangle
two-out-of-three property for the owner predicate `CochainComplex.IsKFlat`. -/
recall CochainComplex.isKFlat_obj₃_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₂_of_distinguished_triangle
recall CochainComplex.isKFlat_obj₁_of_distinguished_triangle

section

variable (T : Triangle KX) (hT : T ∈ distTriang KX)

/- Source-facing specialization: for a ringed space `(X, \mathcal O_X)`, the canonical owner
theorems specialize exactly to distinguished triangles in `K(\mathrm{Mod}(\mathcal O_X))`. -/
#check CochainComplex.isKFlat_obj₃_of_distinguished_triangle T hT
#check CochainComplex.isKFlat_obj₂_of_distinguished_triangle T hT
#check CochainComplex.isKFlat_obj₁_of_distinguished_triangle T hT

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_7 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open AlgebraicGeometry.RingedSpace

noncomputable section

/- Domain-style sampling for Lemma 20.26.7:
- primary domain: K-flat cochain complexes of `\mathcal O_X`-modules in a short exact sequence of
  complexes on a ringed space;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`,
  `CategoryTheory.ShortComplex.ShortExact.isKFlat_X₃`;
- best owner abstraction: the primitive owner data are a short complex
  `S : ShortComplex (CochainComplex (RingedSpace.Modules X) ℤ)` together with `hS : S.ShortExact`;
  the three K-flatness conclusions are derived API attached to that owner, not separate ringed
  space wrapper data;
- primitive vs derived: primitive data are only `S`, `hS`, and the termwise flatness hypothesis on
  `S.X₃`; the conclusions that `S.X₁`, `S.X₂`, or `S.X₃` are K-flat are derived theorems.

Source/core/bridge triage:
- `source-facing`: the ringed-space specialization of the short-exact two-out-of-three K-flatness
  statements from the Stacks Project;
- `core/canonical`: `CochainComplex.IsKFlat` and the short-exact owner
  `CategoryTheory.ShortComplex.ShortExact`;
- `bridge/view`: the earlier tensor-exactness theorem
  `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`, which supplies the
  short-exact tensor sequence used in the proof sketch. -/

namespace CategoryTheory.ShortComplex.ShortExact

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]
variable {S : ShortComplex (CochainComplex (RingedSpace.Modules X) ℤ)}

-- Proof sketch: tensor the given short exact sequence with an arbitrary acyclic complex. Since the
-- terms of `S.X₃` are flat, the canonical tensor-right owner theorem
-- `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient` preserves short exactness
-- after tensoring termwise. If
-- `S.X₁` and `S.X₂` are K-flat, the first two tensor complexes are acyclic, so the third is
-- acyclic by the long exact sequence of cohomology sheaves.
/-- Lemma 20.26.7 (1): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, if every
term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_2^\bullet` are K-flat, then `\mathcal K_3^\bullet` is K-flat. -/
theorem isKFlat_X₃_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

-- Proof sketch: after tensoring with an arbitrary acyclic complex, the canonical tensor-right
-- owner theorem `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient` again gives
-- a short exact sequence of tensor complexes because the terms of `S.X₃` are flat. If `S.X₁` and
-- `S.X₃` are K-flat, the outer tensor complexes are acyclic, so the middle one is acyclic by the
-- associated long exact sequence on cohomology sheaves.
/-- Lemma 20.26.7 (2): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, if every
term of `\mathcal K_3^\bullet` is flat and `\mathcal K_1^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_2^\bullet` is K-flat. -/
theorem isKFlat_X₂_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

-- Proof sketch: tensor the short exact sequence with an arbitrary acyclic complex and use the
-- flatness of the terms of `S.X₃` to keep the tensor sequence short exact by
-- `SheafOfModules.RingedSite.shortExact_tensor_right_of_flat_quotient`. If
-- `S.X₂` and `S.X₃` are K-flat, then the last two tensor complexes are acyclic, and the first is
-- acyclic by the resulting long exact sequence of cohomology sheaves.
/-- Lemma 20.26.7 (3): in a short exact sequence
`0 ⟶ \mathcal K_1^\bullet ⟶ \mathcal K_2^\bullet ⟶ \mathcal K_3^\bullet ⟶ 0`
of cochain complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, if every
term of `\mathcal K_3^\bullet` is flat and `\mathcal K_2^\bullet` and
`\mathcal K_3^\bullet` are K-flat, then `\mathcal K_1^\bullet` is K-flat. -/
theorem isKFlat_X₁_of_flat_X₃
    (hS : S.ShortExact)
    (hFlat₃ : ∀ n : ℤ, SheafOfModules.IsFlat (S.X₃.X n))
    (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end CategoryTheory.ShortComplex.ShortExact

/-! ### Lemma_20_26_8 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules Y)] [MonoidalPreadditive (RingedSpace.Modules Y)]

-- Proof sketch: by Lemma `20.26.4`, it suffices to check K-flatness on stalk complexes. For
-- `x : X`, Lemma `6.26.4` identifies the stalk of the pullback complex with extension of scalars
-- of the stalk complex of `K` along `\mathcal O_{Y, f(x)} \to \mathcal O_{X, x}`. Then Lemma
-- `15.59.3` shows that extension of scalars preserves K-flatness.
/-- Lemma 20.26.8: for a morphism of ringed spaces
`f : (X, \mathcal O_X) \to (Y, \mathcal O_Y)`, the pullback of a K-flat complex of
`\mathcal O_Y`-modules is a K-flat complex of `\mathcal O_X`-modules. -/
lemma pullback_isKFlat (f : X ⟶ Y) (K : CochainComplex (RingedSpace.Modules Y) ℤ) (hK : IsKFlat K) :
    IsKFlat (((RingedSpace.Hom.pullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_9 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

-- Proof sketch: apply Lemma `isKFlat_iff_stalkwise_isKFlat` to reduce to canonical stalk
-- complexes. For each `x : X`, the stalk complex of `K` at `x` is bounded above whenever `K` is bounded
-- above, and its term in degree `n` is flat over `\mathcal O_{X, x}` because `K.X n` is a flat
-- `\mathcal O_X`-module sheaf. Then use the module-theoretic bounded-above flat criterion from
-- Lemma `15.59.7` on every stalk complex.
/-- Lemma 20.26.9: a bounded above complex of flat `\mathcal O_X`-modules on a ringed space
`(X, \mathcal O_X)` is K-flat. -/
theorem isKFlat_of_boundedAbove_of_flat
    (K : CochainComplex (RingedSpace.Modules X) ℤ)
    (hbounded : ∃ n : ℤ, K.IsStrictlyLE n)
    (hFlat : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    IsKFlat K := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_10 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

/- Domain-style sampling pass:
- primary domain: K-flat cochain complexes of `\mathcal O_X`-modules on a ringed space and their
  stability under sequential colimits;
- sampled owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `AB5 (SheafOfModules ((RingedSpace.ringCatSheaf X)))`;
- best owner abstraction: the core owner is the predicate `K.IsKFlat` on the cochain complex
  itself. The ringed-space statement is a source-facing specialization of that owner to
  `(RingedSpace.Modules X)`, together with the chapter-level exactness of filtered colimits in
  `SheafOfModules ((RingedSpace.ringCatSheaf X))`;
- primitive vs derived: the primitive data are only the sequential diagram `F` and the K-flatness
  hypotheses on its stages. The sequential colimit object and its K-flatness are derived from the
  ambient colimit and owner predicate, so no extra wrapper data belongs in the public API.

Source/core/bridge triage:
- `source-facing`: Lemma 20.26.10, the ringed-space closure of K-flatness under sequential
  colimits;
- `core/canonical`: `CochainComplex.IsKFlat` together with the ambient colimit in
  `CochainComplex (RingedSpace.Modules X) ℤ`;
- `bridge/view`: none. This file should state the ringed-space specialization directly in terms of
  the canonical K-flat owner rather than introduce a parallel local notion. -/

-- Proof sketch: tensor an arbitrary acyclic complex `\mathcal F^\bullet` with the sequential
-- diagram `F`. Termwise tensor products commute with the colimit, so
-- `Tot(\mathcal F^\bullet \otimes \operatorname{colim}_i \mathcal K_i^\bullet)` identifies with
-- the colimit of the acyclic tensor complexes `Tot(\mathcal F^\bullet \otimes \mathcal K_i^\bullet)`.
-- Exactness of filtered colimits in sheaves of modules then shows that the resulting tensor
-- complex is acyclic.
/-- Lemma 20.26.10: for a system `\mathcal K_1^\bullet \to \mathcal K_2^\bullet \to \cdots` of
K-flat complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, the sequential
colimit `\mathop{\mathrm{colim}}_i \mathcal K_i^\bullet` is K-flat. -/
theorem sequentialColimit_isKFlat
    (F : ℕ ⥤ CochainComplex (RingedSpace.Modules X) ℤ)
    [HasColimit F]
    (hF : ∀ i : ℕ, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_11 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleSheaf

section

variable {X : RingedSpace.{u}}

local notation "ModCat" => SheafOfModules (RingedSpace.ringCatSheaf X)

-- Proof sketch: apply Lemma `17.17.7` degreewise to produce epimorphic covers of the terms of the
-- upper truncations of `𝒢`, then feed the resulting object property into Lemma `13.29.1` to build
-- the compatible resolution tower. Exactness of filtered colimits gives the quasi-isomorphism from
-- the colimit complex to `𝒢`.
/-- Lemma 20.26.11: every complex of `\mathcal O_X`-modules on a ringed space admits a compatible
upper-truncation resolution tower by bounded-above complexes whose terms and successive degreewise
cokernels are coproducts of lower-shriek structure sheaves `j_{U!}\mathcal O_U`, and whose
canonical map from the sequential colimit of the tower to the original complex is a
quasi-isomorphism. -/
theorem exists_upperTruncationResolutionTower_of_openSubsetStructureSheafLowerShrieks
    (𝒢 : CochainComplex ModCat ℤ) :
    ∃ T : UpperTruncationResolutionTower (isCoproductOfOpenSubsetStructureSheafLowerShrieks X) 𝒢,
      QuasiIso T.fromColimit := sorry

end

end AlgebraicGeometry.RingedSpace.ModuleSheaf

/-! ### Lemma_20_26_12 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

-- Proof sketch: choose the compatible upper-truncation resolution tower from Lemma `20.26.11`.
-- Each stage is bounded above and has flat terms because its terms are coproducts of
-- `j_{U!}\mathcal O_U`, which are flat by Lemma `17.17.6`; hence every stage is K-flat by
-- Lemma `20.26.9`. Apply Lemma `20.26.10` to the sequential colimit of the tower. The comparison
-- map from that colimit to `\mathcal G^\bullet` is a quasi-isomorphism and degreewise epi by the
-- construction in Lemma `20.26.11`, and each term of the colimit remains flat because it is a
-- direct sum of flat modules.
/-- Lemma 20.26.12: every complex `\mathcal G^\bullet` of `\mathcal O_X`-modules on a ringed
space `(X, \mathcal O_X)` admits a quasi-isomorphism from a K-flat complex whose terms are flat
`\mathcal O_X`-modules, and this quasi-isomorphism is termwise surjective. -/
theorem exists_termwiseEpi_quasiIso_from_KFlat_complex_of_flat_terms
    (𝒢 : CochainComplex (RingedSpace.Modules X) ℤ) :
    ∃ (K : CochainComplex (RingedSpace.Modules X) ℤ) (hK : IsKFlat K)
      (hFlat : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n))
      (α : K ⟶ 𝒢), QuasiIso α ∧ ∀ n : ℤ, Epi (α.f n) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_13 (from Chap20) -/
open CategoryTheory CategoryTheory.Limits ComplexShape MonoidalCategory
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

-- Proof sketch: choose a quasi-isomorphism `K^• ⟶ F^•` from a K-flat complex using Lemma
-- `20.26.12`. Tensoring this comparison with either `P^•` or `Q^•` gives quasi-isomorphisms on
-- the vertical arrows by Lemma `20.26.3`, while tensoring `α` with the K-flat complex `K^•`
-- gives a quasi-isomorphism on the top horizontal map. The commutative square then forces the
-- bottom horizontal map to be a quasi-isomorphism.
/-- Lemma 20.26.13: if `α : \mathcal P^\bullet \to \mathcal Q^\bullet` is a quasi-isomorphism
between K-flat complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)`, then
for every complex `\mathcal F^\bullet` of `\mathcal O_X`-modules the induced map
`\mathrm{Tot}(\mathrm{id}_{\mathcal F^\bullet} \otimes \alpha) :
\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X} \mathcal P^\bullet) ⟶
\mathrm{Tot}(\mathcal F^\bullet \otimes_{\mathcal O_X} \mathcal Q^\bullet)` is a
quasi-isomorphism. -/
lemma quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat
    (F P Q : CochainComplex (RingedSpace.Modules X) ℤ)
    (hP : CochainComplex.IsKFlat P) (hQ : CochainComplex.IsKFlat Q)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) α) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Definition_20_26_14 (from Chap20) -/
noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

set_option checkBinderAnnotations false

namespace AlgebraicGeometry.RingedSpace

/-
Domain-style sampling for Definition 20.26.14:
- primary domain: fixed-right-factor tensoring on the homotopy category of `\mathcal O_X`-modules
  and its total left derived functor on `D(\mathcal O_X)`;
- sampled owner declarations:
  `Functor.map₂CochainComplex`,
  `Functor.mapHomotopyCategory`,
  `Functor.totalLeftDerived`,
  `Functor.totalLeftDerivedCounit`,
  `CategoryTheory.derivedTensorProduct` from Chapter 15;
- best owner abstraction: the public owner here is the endofunctor-valued
  `derivedTensorProduct : D(\mathcal O_X) → D(\mathcal O_X) ⥤ D(\mathcal O_X)`, while the chosen
  representative of the right factor, the homotopy-category source functor, and the derived-functor
  witness data are internal construction data for that owner via `Functor.totalLeftDerived`;
- primitive vs derived: the primitive mathematical input is only the fixed right factor
  `ℱ : D(\mathcal O_X)`, while the shift compatibility and triangulated exactness of
  `derivedTensorProduct ℱ` are derived API.

Source/core/bridge triage:
- `source-facing`: the derived tensor product on `D(\mathcal O_X)`;
- `core/canonical`: `Functor.totalLeftDerived` of the canonical fixed-right-factor homotopy tensor
  functor;
- `bridge/view`: no extra bridge owner is needed, since the source item is already the canonical
  endofunctor built from that core construction.

Notation decision:
- the high-frequency source-facing surface is the object-level derived tensor product, so the file
  exposes a scoped notation `K ⊗^L L` for downstream object statements;
- the owner remains the functor-valued declaration `derivedTensorProduct`, and the notation is only
  its object-level surface. -/

variable {X : RingedSpace}
variable [hAbelian : Abelian (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [HasCountableCoproducts (RingedSpace.Modules X)]
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasColimits (RingedSpace.Modules X)]
variable [(curriedTensor ((RingedSpace.Modules X))).Additive]
variable [∀ ℱ : (RingedSpace.Modules X), ((curriedTensor ((RingedSpace.Modules X))).obj ℱ).Additive]
variable [∀ (ℱ 𝒢 : CochainComplex (RingedSpace.Modules X) ℤ),
  CochainComplex.HasMapBifunctor ℱ 𝒢 (curriedTensor ((RingedSpace.Modules X)))]

/-- An abelian category of `\mathcal O_X`-modules is preadditive. -/
local instance : Preadditive (RingedSpace.Modules X) :=
  hAbelian.toPreadditive

/-- An abelian category of `\mathcal O_X`-modules has binary biproducts. -/
local instance :
    HasBinaryBiproducts (RingedSpace.Modules X) :=
  Abelian.hasBinaryBiproducts

local notation "KMod" => HomotopyCategory (RingedSpace.Modules X) (up ℤ)
local notation "DMod" => DerivedCategory (RingedSpace.Modules X)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (RingedSpace.Modules X) (up ℤ)

/-- The homotopy-category tensor functor whose left derived functor defines derived tensoring with
a fixed right factor in `D(\mathcal O_X)`. -/
private noncomputable abbrev derivedTensorSourceFunctor (ℱ : DMod) : KMod ⥤ DMod :=
  CategoryTheory.Quotient.lift (homotopic (RingedSpace.Modules X) (up ℤ))
    ((((curriedTensor (RingedSpace.Modules X)).map₂CochainComplex).flip.obj
        (DerivedCategory.Qh.objPreimage ℱ).as) ⋙
      HomotopyCategory.quotient (RingedSpace.Modules X) (up ℤ))
    (fun _ _ _ _ ⟨h⟩ ↦
      HomotopyCategory.eq_of_homotopy _ _
        (HomologicalComplex.mapBifunctorMapHomotopy₁ h
          (𝟙 (DerivedCategory.Qh.objPreimage ℱ).as)
          (curriedTensor (RingedSpace.Modules X)) (up ℤ))) ⋙
    Qh

-- Proof sketch: choose a homotopy-category representative of `\mathcal F^\bullet`, replace it by
-- a K-flat resolution using the flat-resolution results developed above, and use the
-- quasi-isomorphism invariance of tensoring with a K-flat complex to invoke the universal
-- property of the total left derived functor.
/-- Tensoring on the homotopy category with a fixed derived right factor admits a total left
derived functor on `D(\mathcal O_X)`. -/
private theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (ℱ : DMod) :
    (derivedTensorSourceFunctor ℱ).HasLeftDerivedFunctor Qis := sorry

/-- Definition 20.26.14: for an object `\mathcal F^\bullet` of `D(\mathcal O_X)`, the derived
tensor product `- \otimes_{\mathcal O_X}^{\mathbf L} \mathcal F^\bullet` is the endofunctor of
`D(\mathcal O_X)` obtained by left deriving the homotopy-category tensor functor with fixed right
factor a chosen representative of `\mathcal F^\bullet`. -/
noncomputable def derivedTensorProduct (ℱ : DMod) : DMod ⥤ DMod :=
  letI := derivedTensorSourceFunctor_hasLeftDerivedFunctor ℱ
  (derivedTensorSourceFunctor ℱ).totalLeftDerived Qh Qis

-- Proof sketch: the homotopy-category tensor functor with fixed right factor commutes with
-- shifts by Remark `13.10.9`, and the same compatibility is inherited by the total left derived
-- functor on the derived category.
/-- Derived tensoring with a fixed right factor commutes with the triangulated shift. -/
noncomputable instance derivedTensorProduct_commShift (ℱ : DMod) :
    (derivedTensorProduct ℱ).CommShift ℤ := sorry

-- Proof sketch: the underived tensor functor on the homotopy category is triangulated by the
-- preceding homotopy-category tensor formalism, and passing to its total left derived functor
-- yields an exact functor on the derived category.
/-- The derived tensor product endofunctor on `D(\mathcal O_X)` is exact in the triangulated
sense. -/
theorem derivedTensorProduct_isTriangulated (ℱ : DMod) :
    (derivedTensorProduct ℱ).IsTriangulated := sorry

end AlgebraicGeometry.RingedSpace

namespace RingedSpaceDerivedTensor

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in
`D(\mathcal O_X)`. -/
scoped notation:70 K:70 " ⊗^L " L:71 =>
  Functor.obj (AlgebraicGeometry.RingedSpace.derivedTensorProduct L) K

end RingedSpaceDerivedTensor

/-! ### Definition_20_26_15 (from Chap20) -/
noncomputable section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.RingedSpace

/- Domain-style sampling for Definition 20.26.15:
- primary domain: Tor objects of sheaves of modules on a ringed space;
- sampled owner declarations:
  `CategoryTheory.Tor`,
  `Functor.leftDerived`,
  `MonoidalCategory.tensoringLeft`;
- best owner abstraction: the public owner for `\operatorname{Tor}_p^{\mathcal O_X}` is the
  canonical bifunctor `CategoryTheory.Tor (RingedSpace.Modules X) p`;
- primitive vs derived: the primitive data is only the pair of module objects `\mathcal F`,
  `\mathcal G`; the Tor bifunctor is the owner abstraction, while tensoring in one variable and
  left derivation are already canonical derived API behind that owner.

Source/core/bridge triage:
- `source-facing`: the evaluated object `(((Tor (RingedSpace.Modules X) p).obj ℱ).obj 𝒢)`;
- `core/canonical`: `CategoryTheory.Tor`;
- `bridge/view`: none needed in this file, since the numbered item is just the canonical Tor
  object specialized to `(RingedSpace.Modules X)`. -/

recall CategoryTheory.Tor

section

variable {X : RingedSpace}
variable [Abelian (RingedSpace.Modules X)]
local instance : Preadditive (RingedSpace.Modules X) := (inferInstance : Abelian (RingedSpace.Modules X)).toPreadditive
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasProjectiveResolutions (RingedSpace.Modules X)]
variable (p : ℕ)

/- Definition 20.26.15: for a ringed space `(X, \mathcal O_X)`, the owner of
`\operatorname{Tor}_p^{\mathcal O_X}` on `\mathcal O_X`-modules is the canonical bifunctor
`CategoryTheory.Tor` on the monoidal abelian category `(RingedSpace.Modules X)`. -/
#check (Tor (RingedSpace.Modules X) p)

variable (ℱ 𝒢 : (RingedSpace.Modules X))

/- Companion recall: evaluating the canonical Tor bifunctor at `\mathcal F` and `\mathcal G`
gives the source object `\operatorname{Tor}_p^{\mathcal O_X}(\mathcal F, \mathcal G)`, which the
text describes as `H^{-p}(\mathcal F \otimes_{\mathcal O_X}^{\mathbf L} \mathcal G)`. -/
#check ((((Tor (RingedSpace.Modules X) p).obj ℱ).obj 𝒢) : (RingedSpace.Modules X))

end

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_16 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)]
variable [MonoidalPreadditive (RingedSpace.Modules X)]
variable [HasProjectiveResolutions (RingedSpace.Modules X)]

/- Domain-style sampling for Lemma 20.26.16:
- primary domain: flat sheaves of modules on a ringed space and the first left-derived tensor
  functor on the ambient monoidal abelian category `(RingedSpace.Modules X)`;
- inspected owner declarations:
  `SheafOfModules.IsFlat`,
  `CategoryTheory.Tor`,
  `CategoryTheory.isZero_Tor_succ_of_projective`;
- best owner abstraction: flatness is already owned by `SheafOfModules.IsFlat`, while the Tor side
  of the criterion is already owned by the canonical derived functor `CategoryTheory.Tor` on
  `(RingedSpace.Modules X)`; this item should therefore stay a source-facing criterion theorem and not
  introduce a parallel local Tor owner;
- primitive data: the module sheaf `ℱ : (RingedSpace.Modules X)`;
- derived API: the vanishing criterion `∀ 𝒢, IsZero (((Tor (RingedSpace.Modules X) 1).obj ℱ).obj 𝒢)`.

Source/core/bridge triage:
- `source-facing`: the flatness criterion stated as vanishing of `Tor₁`;
- `core/canonical`: `SheafOfModules.IsFlat` and `CategoryTheory.Tor`;
- `bridge/view`: the specialization of those owners to the ringed-space module category
  `(RingedSpace.Modules X)`. -/

-- Proof sketch: if `ℱ` is flat, then tensoring with `ℱ` is exact, so its first left derived
-- functor vanishes and hence `Tor₁` is zero against every `𝒢`. Conversely, apply the long exact
-- `Tor` sequence to a short exact sequence `0 ⟶ 𝒢 ⟶ ℋ ⟶ 𝒬 ⟶ 0`; vanishing of `Tor₁(ℱ, 𝒬)` forces
-- tensoring with `ℱ` to preserve monomorphisms, which is the flatness criterion.
/-- Lemma 20.26.16: an `\mathcal O_X`-module `\mathcal F` on a ringed space `(X, \mathcal O_X)`
is flat if and only if `\operatorname{Tor}_1^{\mathcal O_X}(\mathcal F, \mathcal G)` vanishes for
every `\mathcal O_X`-module `\mathcal G`. -/
theorem isFlat_iff_isZero_tor_one
    (ℱ : (RingedSpace.Modules X)) :
    ℱ.IsFlat ↔
      ∀ 𝒢 : (RingedSpace.Modules X), IsZero (((Tor (RingedSpace.Modules X) 1).obj ℱ).obj 𝒢) := sorry

end AlgebraicGeometry.RingedSpace

/-! ### Lemma_20_26_17 (from Chap20) -/
open AlgebraicGeometry
open CategoryTheory HomologicalComplex

noncomputable section

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace}
variable [MonoidalCategory (RingedSpace.Modules X)] [MonoidalPreadditive (RingedSpace.Modules X)]

variable {K L N : CochainComplex (RingedSpace.Modules X) ℤ}

/-- A factorization of `a` up to homotopy through a quasi-isomorphism `c : \mathcal N^\bullet ⟶
\mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
class IsKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop where
  /-- The morphism `a` is homotopic to the composite `b ≫ c`. -/
  homotopy : Nonempty (Homotopy a (b ≫ c))
  /-- The intermediate complex is K-flat. -/
  isKFlat : IsKFlat N
  /-- The comparison map to `\mathcal L^\bullet` is a quasi-isomorphism. -/
  quasiIso : QuasiIso c

/-- A K-flat factorization up to homotopy whose intermediate complex has flat terms. -/
class IsTermwiseFlatKFlatFactorizationUpToHomotopy
    (a : K ⟶ L) (b : K ⟶ N) (c : N ⟶ L) : Prop
    extends IsKFlatFactorizationUpToHomotopy a b c where
  /-- Every term of the intermediate complex is a flat `\mathcal O_X`-module. -/
  term_flat : ∀ n : ℤ, SheafOfModules.IsFlat (N.X n)

-- Proof sketch: choose a distinguished triangle for `a` in the homotopy category, resolve its
-- cone by a quasi-isomorphic K-flat complex with flat terms using Lemma `20.26.12`, and fit the
-- composite to `K⟦1⟧` into a distinguished triangle `K ⟶ N ⟶ M ⟶ K⟦1⟧`. Lemma `20.26.6` gives
-- that `N` is K-flat; a morphism of distinguished triangles yields `c : N ⟶ L`, and
-- two-out-of-three shows `c` is a quasi-isomorphism while the triangle comparison identifies `a`
-- with `b ≫ c` up to homotopy.
/-- Lemma 20.26.17: if `a : \mathcal K^\bullet ⟶ \mathcal L^\bullet` is a morphism of cochain
complexes of `\mathcal O_X`-modules on a ringed space `(X, \mathcal O_X)` and
`\mathcal K^\bullet` is K-flat, then `a` factors up to homotopy through a quasi-isomorphism
`c : \mathcal N^\bullet ⟶ \mathcal L^\bullet` with K-flat source `\mathcal N^\bullet`. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso
    (a : K ⟶ L) (hK : IsKFlat K) :
    ∃ (N : CochainComplex (RingedSpace.Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsKFlatFactorizationUpToHomotopy a b c := sorry

-- Proof sketch: carry out the construction of the main factorization theorem using the split-form
-- distinguished triangle from Lemma `13.10.7`, so that each term of `N` is isomorphic to
-- `M.X n ⊞ K.X n` for the chosen K-flat replacement `M` of the cone. Since `M` has flat terms by
-- Lemma `20.26.12` and `K` is assumed termwise flat, the terms of `N` are flat as well.
/-- If the source complex has flat terms, the K-flat factorization can be chosen with flat terms as
well. -/
theorem exists_homotopy_factorization_through_kFlat_quasiIso_of_termwiseFlat
    (a : K ⟶ L) (hK : IsKFlat K)
    (hFlatK : ∀ n : ℤ, SheafOfModules.IsFlat (K.X n)) :
    ∃ (N : CochainComplex (RingedSpace.Modules X) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      IsTermwiseFlatKFlatFactorizationUpToHomotopy a b c := sorry

end AlgebraicGeometry.RingedSpace
