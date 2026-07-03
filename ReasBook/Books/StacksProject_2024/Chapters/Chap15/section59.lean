import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.HomotopyCategory
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Localization.Monoidal.Braided
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.RingTheory.Flat.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_15_59_1 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace CochainComplex

section

variable {R : Type u} [Ring R]

/-- A cochain complex of `R`-modules is termwise free if each module `K^n` is free. -/
def IsTermwiseFree (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ n : ℤ, Module.Free R (K.X n : Type u)

end

section

variable {R : Type u} [CommRing R]

/-- A cochain complex of `R`-modules is termwise flat if each module `K^n` is flat. -/
def IsTermwiseFlat (K : CochainComplex (ModuleCat R) ℤ) : Prop :=
  ∀ n : ℤ, Module.Flat R (K.X n : Type u)

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- A cochain complex in a monoidal preadditive category is K-flat if totalized tensoring with it
preserves acyclic cochain complexes. Definition 15.59.1 is the specialization to complexes of
modules over a commutative ring. -/
def IsKFlat (K : CochainComplex C ℤ) : Prop :=
  ∀ ⦃M : CochainComplex C ℤ⦄ [_h : HomologicalComplex.HasTensor M K], M.Acyclic →
    (HomologicalComplex.tensorObj M K).Acyclic

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [(curriedTensor C).Additive] [∀ X : C, ((curriedTensor C).obj X).Additive]

-- Proof sketch: unfold `CochainComplex.IsKFlat`; the right-hand side is exactly the defining
-- acyclicity condition for totalized tensoring with `K`.
/-- A cochain complex is K-flat exactly when totalized tensoring with it preserves acyclic
cochain complexes. -/
theorem isKFlat_iff (K : CochainComplex C ℤ) :
    K.IsKFlat ↔
      ∀ ⦃M : CochainComplex C ℤ⦄
        [_h : HomologicalComplex.HasTensor M K], M.Acyclic →
        (HomologicalComplex.tensorObj M K).Acyclic :=
  Iff.rfl

end

end CochainComplex

namespace HomologicalComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- The K-flatness owner for cochain complexes, viewed through the canonical identification
`HomologicalComplex C (ComplexShape.up ℤ) = CochainComplex C ℤ`. This bridge lets homotopy-category
objects use the same postfix surface `K.IsKFlat` on their `.as` representatives. -/
abbrev IsKFlat (K : HomologicalComplex C (ComplexShape.up ℤ)) : Prop :=
  CochainComplex.IsKFlat K

end

end HomologicalComplex

namespace HomotopyCategory

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [CategoryTheory.Limits.HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]

/-- The K-flatness owner for objects of the homotopy category of cochain complexes. This is the
canonical `K(C)`-level surface for the representative-level predicate on `K.as`. -/
abbrev IsKFlat (K : HomotopyCategory C (ComplexShape.up ℤ)) : Prop :=
  K.as.IsKFlat

end

end HomotopyCategory

/-! ### Lemma_15_59_2 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

universe v u

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [CategoryWithHomology C]
variable [MonoidalCategory C] [MonoidalPreadditive C]

variable (K : CochainComplex C ℤ)
variable [∀ X : CochainComplex C ℤ, CochainComplex.HasMapBifunctor X K (curriedTensor C)]

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
  sorry

end

/-! ### Lemma_15_59_3 (from Chap15) -/
open CategoryTheory
open ComplexShape
open ModuleCat

noncomputable section

universe u

section

variable {R R' : Type u} [CommRing R] [CommRing R']

/- Domain-style sampling:
- primary domain: change of rings for module-valued cochain complexes and preservation of the
  owner predicate `CochainComplex.IsKFlat`;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `ModuleCat.extendScalars`,
  `Functor.mapHomologicalComplex`.
- best owner abstraction: the owner is still the predicate `K.IsKFlat` on the cochain complex
  itself; extension of scalars is bridge data, not a second owner.
- primitive data: the ring map `f`, the complex `K`, and the hypothesis `hK : K.IsKFlat`.
- derived API: K-flatness of the canonically extended complex.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that extension of scalars preserves K-flatness;
- `core/canonical`: `CochainComplex.IsKFlat`;
- `bridge/view`: the functor `extendScalars f` on module complexes.

The target complex is canonical data coming from `extendScalars f`, so the public statement should
expose only the owner predicate on that complex rather than any auxiliary wrapper.
-/

-- Proof sketch: unfold `CochainComplex.IsKFlat`. For an acyclic `R'`-complex `L`, view `L` as an
-- `R`-complex by restriction of scalars and use the canonical identification
-- `(K ⊗[R] R') ⊗[R'] L ≅ K ⊗[R] L`; then apply the K-flatness of `K`.
/-- Lemma 15.59.3: for a ring map `R → R'`, extension of scalars sends a K-flat complex of
`R`-modules to a K-flat complex of `R'`-modules. -/
theorem extendScalarsComplex_isKFlat
    (f : R →+* R') (K : CochainComplex (ModuleCat R) ℤ)
    (hK : K.IsKFlat) :
    CochainComplex.IsKFlat (((extendScalars f).mapHomologicalComplex (up ℤ)).obj K) :=
  sorry

end

/-! ### Lemma_15_59_4 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u v

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [MonoidalCategory C] [MonoidalPreadditive C] [(curriedTensor C).Additive]
  [∀ X : C, ((curriedTensor C).obj X).Additive]
  [∀ (K L : CochainComplex C ℤ), CochainComplex.HasMapBifunctor K L (curriedTensor C)]

/- Domain sampling pass:
* primary domain: K-flat cochain complexes in a monoidal preadditive category and their totalized
  tensor product on `CochainComplex C ℤ`;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_iff` from `Definition_15_59_1`, the canonical eliminator exposing only
    the acyclicity-preservation content of that owner;
  - `HomologicalComplex.tensorObj`, the canonical tensor construction on cochain complexes whose
    K-flatness is the mathematical content of this lemma;
  - mathlib's `HomologicalComplex.monoidalCategory`, whose tensor notation `K ⊗ L` is a derived
    surface only under stronger ambient hypotheses than this lemma assumes;
  - the ringed-space and ringed-site specializations later in the project, which should be derived
    by specialization from this owner theorem rather than carried as parallel owners.

Source/core/bridge triage:
* `source-facing`: the tensor-closure statement for K-flat cochain complexes in the ambient
  monoidal category;
* `core/canonical`: `CochainComplex.IsKFlat` together with `HomologicalComplex.tensorObj`;
* `bridge/view`: the later ringed-space and ringed-site specializations.

Primitive data are only the two K-flatness hypotheses `hK` and `hL`. The tensor product
`HomologicalComplex.tensorObj K L` is canonical derived structure, so this file should expose only
the owner-level closure theorem and not introduce any auxiliary wrapper for tensor-K-flat data.
The raw `tensorObj` spelling is also the right public surface here: replacing it by monoidal
notation would silently strengthen the ambient API by demanding a `MonoidalCategory` instance on
cochain complexes instead of only the tensor data used by `IsKFlat`.
-/

-- Proof sketch: for any acyclic complex `M^•`, use the associativity isomorphism for totalized
-- tensor products to identify `Tot(M^• ⊗ Tot(K^• ⊗ L^•))` with
-- `Tot(Tot(M^• ⊗ K^•) ⊗ L^•)`. K-flatness of `K^•` makes the inner total tensor acyclic, and
-- then K-flatness of `L^•` finishes.
/-- Lemma 15.59.4: if `K^•` and `L^•` are K-flat cochain complexes in a monoidal preadditive
category, then the totalized tensor product `\mathrm{Tot}(K^• \otimes L^•)` is again K-flat. -/
theorem tensorObj_isKFlat_of_isKFlat
    (K L : CochainComplex C ℤ) (hK : K.IsKFlat) (hL : L.IsKFlat) :
    IsKFlat (HomologicalComplex.tensorObj K L) := sorry

end

end CochainComplex

/-! ### Lemma_15_59_5 (from Chap15) -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open ComplexShape HomotopyCategory MonoidalCategory

noncomputable section

universe v u

namespace CochainComplex

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [MonoidalCategory C] [MonoidalPreadditive C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]
variable [∀ (X Y : CochainComplex C ℤ), CochainComplex.HasMapBifunctor X Y (curriedTensor C)]

local notation "KHom" => HomotopyCategory C (up ℤ)

/- Domain-style sampling for Lemma 15.59.5:
- primary domain: K-flat objects in the homotopy category `K(C)` of cochain complexes in a
  monoidal preadditive category, together with the distinguished-triangle owner API on `K(C)`;
- sampled owner declarations:
  `HomotopyCategory.IsKFlat`,
  `CochainComplex.isKFlat_iff`,
  `HomotopyCategory.subcategoryAcyclic`,
  `ObjectProperty.IsTriangulatedClosed₁/₂/₃`;
- best owner abstraction: the source-facing statements remain the three `obj₁`/`obj₂`/`obj₃`
  closure theorems for `K.IsKFlat`, but their natural canonical owner layer is the object property
  on `K(C)` given by `K ↦ K.IsKFlat`; the acyclicity argument belongs to the canonical
  triangulated object property `HomotopyCategory.subcategoryAcyclic C`, not to a parallel local
  tensor wrapper;
- primitive vs derived:
  primitive data are only the distinguished triangle `T` and the K-flatness hypotheses on its
  vertices;
  the two-out-of-three closure mechanism is derived API from the triangulated object-property layer
  on `K(C)`, and does not require extra ambient assumptions such as abelianness, homology, or
  cocompleteness in the public theorem headers.

Source/core/bridge triage:
* `source-facing`: the three two-out-of-three closure statements for `IsKFlat` in distinguished
  triangles of `K(C)`;
* `core/canonical`: `HomotopyCategory.IsKFlat`, `HomotopyCategory.subcategoryAcyclic C`, and the
  canonical mapping-cone distinguished triangles in `K(C)`;
* `bridge/view`: the identification of K-flatness with preservation of acyclicity after tensoring
  against an acyclic test complex. -/

-- Proof sketch: K-flatness is an object property on `K(C)` via `K ↦ K.IsKFlat`. The proof of
-- closure under isomorphisms compares chosen representatives of isomorphic homotopy-category
-- objects, and the triangulated-owner proof tensors a distinguished triangle with an arbitrary
-- acyclic test complex and uses the two-out-of-three property of
-- `HomotopyCategory.subcategoryAcyclic C`.
/-- The K-flat objects of `K(C)` form an object property closed under isomorphisms. -/
instance isKFlat_isClosedUnderIsomorphisms :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : KHom ↦ K.IsKFlat) where
  of_iso e hK := by
    sorry

/-- Canonical owner form of Lemma 15.59.5: the K-flat objects of `K(C)` form a triangulated
object property. -/
instance isKFlat_isTriangulated :
    ObjectProperty.IsTriangulated (fun K : KHom ↦ K.IsKFlat) where
  exists_zero := by
    sorry
  isStableUnderShiftBy n := by
    refine .mk ?_
    intro K hK
    sorry
  ext₂' T hT h₁ h₃ := by
    sorry

end

section

variable {C : Type u} [Category.{v} C]
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
variable [MonoidalCategory C]
variable [(curriedTensor C).Additive]
variable [∀ X : C, ((curriedTensor C).obj X).Additive]

local notation "KHom" => HomotopyCategory C (up ℤ)

/-- Lemma 15.59.5 (1): if `T` is a distinguished triangle in `K(C)` and the first two vertices are
represented by K-flat cochain complexes, then the third vertex is also represented by a K-flat
cochain complex. -/
theorem isKFlat_obj₃_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : T.obj₁.IsKFlat)
    (h₂ : T.obj₂.IsKFlat) :
    T.obj₃.IsKFlat := by
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₃ T hT h₁ h₂

/-- Lemma 15.59.5 (2): if `T` is a distinguished triangle in `K(C)` and the first and third
vertices are represented by K-flat cochain complexes, then the second vertex is also represented
by a K-flat cochain complex. -/
theorem isKFlat_obj₂_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₁ : T.obj₁.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₂.IsKFlat := by
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₂ T hT h₁ h₃

/-- Lemma 15.59.5 (3): if `T` is a distinguished triangle in `K(C)` and the second and third
vertices are represented by K-flat cochain complexes, then the first vertex is also represented by
a K-flat cochain complex. -/
theorem isKFlat_obj₁_of_distinguished_triangle
    (T : Triangle KHom) (hT : T ∈ distTriang KHom)
    (h₂ : T.obj₂.IsKFlat)
    (h₃ : T.obj₃.IsKFlat) :
    T.obj₁.IsKFlat := by
  let P : ObjectProperty KHom := fun K ↦ K.IsKFlat
  exact P.ext_of_isTriangulatedClosed₁ T hT h₂ h₃

end

end CochainComplex

/-! ### Lemma_15_59_6 (from Chap15) -/
open CategoryTheory

universe u

section

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (CochainComplex (ModuleCat R) ℤ)}

namespace CategoryTheory.ShortComplex.ShortExact

/- Domain-style sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules in short exact sequences of complexes;
* sampled owner declarations:
  - `CochainComplex.IsKFlat`, `CochainComplex.isKFlat_iff`, and
    `CochainComplex.IsTermwiseFlat` from `Definition_15_59_1`, the owner predicate, its canonical
    eliminator, and the termwise flatness hypothesis used in the statement;
  - `ShortComplex.ShortExact.homology_exact₁`, `homology_exact₂`, and `homology_exact₃`, the
    canonical exactness owners for the long exact homology sequence of a short exact sequence of
    complexes;
  - `tensorLeft_of_flat_cokernel` from `Chap10/Lemma_10_39_12`, the termwise tensor-exactness
    bridge applied degreewise after using the termwise flatness of `S.X₃`;
  - `ShortComplex.ShortExact`, the canonical short-complex owner namespace for the source-facing
    three-term statements.

Source/core/bridge triage:
* `source-facing`: the three two-out-of-three K-flatness implications for a short exact sequence of
  cochain complexes;
* `core/canonical`: `CochainComplex.IsKFlat`, `CochainComplex.isKFlat_iff`,
  `CochainComplex.IsTermwiseFlat`, `ShortComplex.ShortExact`, and its exactness consequences
  `homology_exact₁`, `homology_exact₂`, `homology_exact₃`;
* `bridge/view`: tensoring the short exact sequence with an acyclic test complex via the degreewise
  flatness bridge `tensorLeft_of_flat_cokernel`.

Primitive data are only the short exactness proof `hS`, the termwise flatness of `S.X₃`, and the
relevant K-flatness hypotheses on two of the three terms. The tensor short exact sequence is
derived API from the Chapter 10 tensor-exactness bridge together with the canonical short-exact
homology sequence, so this file should keep only the three source-facing consequences below and
not introduce an auxiliary wrapper for the tensorized sequence.
-/

variable (hS : S.ShortExact) (hFlat₃ : S.X₃.IsTermwiseFlat)

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Since each term `S.X₃.X n` is flat, the Chapter 10 tensor-exactness bridge theorem
-- `tensorLeft_of_flat_cokernel` gives degreewise short exactness after
-- tensoring. If `S.X₁` and `S.X₂` are K-flat, the first two tensor complexes are acyclic, so the
-- third is acyclic by the canonical short-exact homology sequence. Via
-- `CochainComplex.isKFlat_iff`, this is exactly the K-flatness condition for `S.X₃`.
/-- Lemma 15.59.6 (1): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₁^\bullet` and
`K₂^\bullet` are K-flat, then `K₃^\bullet` is K-flat. -/
theorem isKFlat_X₃ (hK₁ : S.X₁.IsKFlat) (hK₂ : S.X₂.IsKFlat) :
    S.X₃.IsKFlat := sorry

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Degreewise flatness of `S.X₃` preserves short exactness after tensoring by the same bridge
-- theorem, so the resulting sequence of total tensor products is short exact. If `S.X₁` and
-- `S.X₃` are K-flat, the outer tensor complexes are acyclic, forcing the middle one to be acyclic
-- by the canonical short-exact homology sequence. Unfolding with
-- `CochainComplex.isKFlat_iff` yields the desired owner-level statement.
/-- Lemma 15.59.6 (2): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₁^\bullet` and
`K₃^\bullet` are K-flat, then `K₂^\bullet` is K-flat. -/
theorem isKFlat_X₂ (hK₁ : S.X₁.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₂.IsKFlat := sorry

-- Proof sketch: tensor the short exact sequence `S` on the left with an acyclic complex `M`.
-- Degreewise flatness of `S.X₃` keeps the tensor sequence short exact degreewise by
-- `tensorLeft_of_flat_cokernel`, so its total complexes form a short
-- exact sequence. If `S.X₂` and `S.X₃` are K-flat, then the last two tensor complexes are
-- acyclic, and the canonical short-exact homology sequence forces acyclicity of the first one.
-- This is the `S.X₁.IsKFlat` condition after rewriting with `CochainComplex.isKFlat_iff`.
/-- Lemma 15.59.6 (3): in a short exact sequence `0 ⟶ K₁^\bullet ⟶ K₂^\bullet ⟶ K₃^\bullet ⟶ 0`
of cochain complexes of `R`-modules, if every term of `K₃^\bullet` is flat and `K₂^\bullet` and
`K₃^\bullet` are K-flat, then `K₁^\bullet` is K-flat. -/
theorem isKFlat_X₁ (hK₂ : S.X₂.IsKFlat) (hK₃ : S.X₃.IsKFlat) :
    S.X₁.IsKFlat := sorry

end CategoryTheory.ShortComplex.ShortExact

end

/-! ### Lemma_15_59_7 (from Chap15) -/
noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

namespace CochainComplex

/- Domain-style sampling:
- primary domain: K-flat cochain complexes of `R`-modules and the bounded-above flat criterion;
- inspected owner declarations:
  `CochainComplex.IsKFlat`,
  `CochainComplex.IsTermwiseFlat`,
  `CochainComplex.isKFlat_iff`,
  `CochainComplex.minus`,
  `CochainComplex.minus_iff`;
- best owner abstraction: the chapter owner predicate is `P.IsKFlat` on the complex `P` itself,
  with boundedness expressed by the existing owner predicate
  `CochainComplex.minus (ModuleCat R) P` rather than by a repeated existential spelling, and with
  termwise flatness as a separate hypothesis;
- primitive data: the complex `P`, the bounded-above hypothesis
  `hbounded : CochainComplex.minus (ModuleCat R) P`, and the termwise flatness hypothesis
  `hFlat : P.IsTermwiseFlat`;
- derived API: the K-flatness conclusion `P.IsKFlat`.

Source/core/bridge triage:
- `source-facing`: the bounded-above flat criterion from the source text;
- `core/canonical`: `CochainComplex.IsKFlat` and `CochainComplex.IsTermwiseFlat`;
- `bridge/view`: `CochainComplex.isKFlat_iff`, the owner eliminator expressing K-flatness by
  preservation of acyclicity under totalized tensoring.

The theorem is already an owner-level source-facing statement, so the refine pass should keep that
statement and move only its surface to the canonical owner-style spelling.
-/

-- Proof sketch: let `L^•` be any acyclic complex. Truncate `L^•` above a degree containing a
-- representative of a given class in the total tensor product to reduce to the bounded-above
-- case, then apply the homology spectral sequence for `Tot(L^• ⊗_R P^•)`. Its `E₁`-page is zero
-- because each `P^q` is flat and `L^•` is acyclic, so the total tensor product is acyclic.
/-- Lemma 15.59.7: a bounded above cochain complex of flat `R`-modules is K-flat, expressed in
the canonical owner predicate `P.IsKFlat`. -/
theorem isKFlat_of_boundedAbove_of_flat
    (P : CochainComplex (ModuleCat R) ℤ)
    (hbounded : CochainComplex.minus (ModuleCat R) P)
    (hFlat : P.IsTermwiseFlat) :
    P.IsKFlat := sorry

end CochainComplex

end

/-! ### Lemma_15_59_8 (from Chap15) -/
open CategoryTheory Limits

noncomputable section

universe u v

namespace CochainComplex

variable {R : Type u} [CommRing R]

/- Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules and stability of the owner predicate
  under filtered colimits;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_iff` from `Definition_15_59_1`, the canonical eliminator exposing only
    the acyclicity-preservation content of `IsKFlat`;
  - `CategoryTheory.Limits.colimit`, the canonical owner of the filtered colimit object;
  - the ambient filtered-category typeclass `IsFiltered`, which is the canonical owner abstraction
    for the indexing hypothesis rather than a bespoke sequential-system wrapper.

Source/core/bridge triage:
* `source-facing`: the textbook closure of K-flatness under filtered colimits of module-valued
  cochain complexes;
* `core/canonical`: `CochainComplex.IsKFlat` on `CochainComplex (ModuleCat R) ℤ` together with the
  canonical colimit object `colimit F`;
* `bridge/view`: the sequential specialization obtained by instantiating the owner theorem at the
  preorder category `ℕ`; this file keeps that only as derived prose, not as a second public owner.

Primitive data are only the diagram `F`, the ambient colimit instance `[HasColimit F]`, and the
stagewise K-flatness hypotheses `hF`. The colimit complex and its K-flatness are derived from the
canonical colimit owner and the predicate `CochainComplex.IsKFlat`, so this file should not
introduce any auxiliary wrapper for sequential systems or filtered-colimit K-flat data.
-/

-- Proof sketch: let `M^•` be any acyclic complex. Tensoring with the filtered colimit identifies
-- `HomologicalComplex.tensorObj M (colimit F)` with the filtered colimit of the tensor products
-- `HomologicalComplex.tensorObj M (F.obj i)` by Lemma `10.12.9`, and each stage is acyclic by the
-- assumed K-flatness. Exactness of filtered colimits from Lemma `10.8.8` then gives acyclicity of
-- the colimit tensor complex.
/-- Lemma 15.59.8: any filtered colimit of K-flat cochain complexes of `R`-modules is K-flat.
Specializing to the preorder category `ℕ` recovers the sequential-colimit case. -/
theorem isKFlat_colimit_of_isFiltered
    {I : Type v} [Category.{v} I] [IsFiltered I]
    (F : I ⥤ CochainComplex (ModuleCat R) ℤ)
    [HasColimit F]
    (hF : ∀ i : I, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end CochainComplex

/-! ### Lemma_15_59_9 (from Chap15) -/
open CategoryTheory ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/-
Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules, tested by tensoring with finitely
  presented `R`-modules;
* sampled owner declarations:
  - `CochainComplex.singleFunctor` from mathlib, used here through the standard local notation
    `single₀` for a module concentrated in degree `0`;
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_colimit_of_isFiltered` from `Lemma_15_59_8`, the chapter closure
    theorem
    used by the textbook reduction from arbitrary modules to finitely presented modules;
  - `CategoryTheory.ShortComplex.TensorShortExactForFinitelyPresented` from
    `Theorem_10_82_3`, showing the project’s canonical style for “for every finitely presented
    module” is an instance-binder quantification rather than an explicit witness argument.

Source/core/bridge triage:
* `source-facing`: the criterion that acyclicity after tensoring with finitely presented modules
  already implies K-flatness;
* `core/canonical`: `CochainComplex.IsKFlat`;
* `bridge/view`: `HomologicalComplex.tensorObj K ((single₀).obj M)`, the canonical tensor with
  `M` placed in degree `0`.

Primitive data are only the complex `K` and the finitely-presented tensor-acyclicity hypothesis.
The K-flatness conclusion is derived API over the existing owner `CochainComplex.IsKFlat`, so this
file should stay as a single owner-level criterion and avoid any auxiliary wrapper predicate.
-/

-- Proof sketch: by Lemmas `10.11.3` and `10.12.9`, the same tensor-acyclicity holds for every
-- `R`-module because every module is a filtered colimit of finitely presented modules. Then
-- truncate an arbitrary acyclic complex termwise, use exactness of filtered colimits to reduce to
-- bounded complexes, and finish by induction on the length of the bounded complex via
-- Lemma `15.58.4` and the two-out-of-three argument from Lemma `15.59.6`.
/-- Lemma 15.59.9: if tensoring a cochain complex `K^•` of `R`-modules on the right with every
finitely presented `R`-module gives an acyclic cochain complex, then `K^•` is K-flat. -/
theorem isKFlat_of_tensor_finitelyPresented_acyclic
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic) :
    K.IsKFlat := sorry

end CochainComplex

/-! ### Lemma_15_59_10 (from Chap15) -/
open CategoryTheory

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-
Domain sampling pass:
* primary domain: K-flat resolutions of cochain complexes of `R`-modules;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` and `CochainComplex.IsTermwiseFlat` from
    `Definition_15_59_1`, the chapter owners for the two ambient properties carried by the
    resolving complex;
  - `cochainComplex_epi_iff_degreewise_epi` from `Lemma_12_13_9`, the source-facing bridge
    between the termwise epimorphism condition from the text and the canonical complex-level owner
    `Epi π`;
  - `CategoryTheory.IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn` and
    `CategoryTheory.UpperTruncationResolutionTower` from Chapter 13, the canonical owner
    abstractions for the bounded-above, termwise-epimorphic quasi-isomorphism data used in the
    truncation tower construction;
  - `Module.Flat R`, the canonical owner predicate for flat `R`-modules.

Source/core/bridge triage:
* `source-facing`: the existence of a termwise-epimorphic quasi-isomorphism from a K-flat complex
  with flat terms;
* `core/canonical`: the predicates `IsKFlat`, `IsTermwiseFlat`, `QuasiIso`, and the
  complex-level epimorphism owner `Epi π`;
* `bridge/view`: `cochainComplex_epi_iff_degreewise_epi` and the Chapter 13 upper-truncation
  resolution tower used to construct the witness.

Primitive data are only the resolving complex `K` and comparison morphism `π`. The four
properties above are derived API over existing owner abstractions, so they should not be bundled
into a parallel local wrapper class in this file.
-/

-- Proof sketch: choose the truncation-resolution tower from Derived Categories, Lemma `13.29.1`
-- with flat terms in each bounded-above stage. Each stage is K-flat by Lemma `15.59.7`, and the
-- sequential colimit is K-flat by Lemma `15.59.8`. Filtered colimits of flat modules are flat by
-- Algebra, Lemma `10.39.3`, and the induced map from the colimit complex to `M^•` is a
-- termwise-epimorphic quasi-isomorphism by the construction of the tower.
/-- Lemma 15.59.10: every cochain complex of `R`-modules admits a termwise-epimorphic
quasi-isomorphism from a K-flat cochain complex whose terms are flat `R`-modules. -/
lemma exists_termwiseEpi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (π : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso π ∧ ∀ i : ℤ, Epi (π.f i) := sorry

-- The source-facing lemma above keeps the textbook termwise-epimorphism conclusion. This
-- companion re-expresses the same existence statement through the canonical complex-level owner
-- `Epi π`.
/-- Canonical owner-level form of Lemma 15.59.10: every cochain complex of `R`-modules admits a
quasi-isomorphism from a K-flat cochain complex with flat terms whose comparison morphism is
epimorphic. -/
lemma exists_epi_kFlatResolution
    (M : CochainComplex (ModuleCat R) ℤ) :
    ∃ (K : CochainComplex (ModuleCat R) ℤ) (π : K ⟶ M),
      K.IsKFlat ∧ K.IsTermwiseFlat ∧ QuasiIso π ∧ Epi π := by
  obtain ⟨K, π, hKFlat, hTermwiseFlat, hπ, hEpi⟩ := exists_termwiseEpi_kFlatResolution M
  exact ⟨K, π, hKFlat, hTermwiseFlat, hπ,
    (cochainComplex_epi_iff_degreewise_epi π).2 hEpi⟩

end CochainComplex

/-! ### Remark_15_59_11 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

open FilteredComplex
open FilteredCochainComplex

/-
Domain-style sampling for Remark 15.59.11:
- primary domain: filtered cochain-complex models and approximation towers for cochain complexes
  of `R`-modules and for the induced objects of the triangulated derived category `D(R)`;
- sampled owner declarations:
  `FilteredCochainComplex`,
  `FilteredCochainComplex.underlying`,
  `FilteredCochainComplex.stageMapOfLE`,
  `#check (∀ n : ℤ, IsSplitMono (α.f n))` from `Chap13/Definition_13_9_4`,
  `FilteredComplex`,
  `IsGeneratingFamilyApproximation`,
  `exists_generating_family_resolution`,
  `IsWeakGenerator`,
  `IsGeneratingFamily`,
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsClosedUnderIsomorphisms`,
  `ObjectProperty.IsClosedUnderColimitsOfShape`,
  `CategoryTheory.ringSingle`;
- best owner abstractions: `FilteredCochainComplex (ModuleCat R)` for the source-facing filtered
  witness together with an explicit quasi-isomorphism on its underlying complex, the underlying
  Chapter `12` owner `FilteredComplex (ModuleCat R)` as the core canonical model behind the
  `F^{p}` / `gr^{p}` surface, and the explicit recursive data of
  `exists_generating_family_resolution` together with
  `IsGeneratingFamilyApproximation (fun _ : Unit ↦ ringSingle) ...` for the induced
  distinguished-triangle resolution layer, and `IsWeakGenerator (ringSingle : DMod)` for the
  canonical object-level generation consequence;
- primitive data: a cochain complex `M`, a filtered cochain complex `F`, and a quasi-isomorphism
  `F.underlying ⟶ M`, where the negative-index stages encode the source increasing filtration
  `0 = F_{-1} ⊆ F_0 ⊆ F_1 ⊆ ⋯`, whose consecutive source inclusions are termwise split in the
  Chapter `13` sense `∀ n, IsSplitMono ((-).f n)`, and whose successive quotients are direct sums
  of shifts of the rank-one single complex;
- derived API: the generating-family resolution data in `D(R)`, the object-property consequence
  for arbitrary coproduct-stable triangulated properties, and the weak-generator reformulation;
- source/core/bridge triage:
  `source-facing`: the filtered-complex existence theorem below;
  `core/canonical`: the companion theorem `IsWeakGenerator (ringSingle : DMod)`;
  `bridge/view`: the generating-family resolution theorem and the object-property consequence,
    which translate the filtered witness into the chapter's triangulated owner vocabulary.

The previous version kept only the downstream object-property corollary. This file now restores
the source-facing filtered witness on the Chapter `15` owner
`FilteredCochainComplex (ModuleCat R)` and its induced distinguished-triangle resolution,
encoding the Stacks increasing filtration by the negative-index stages of the underlying canonical
owner `FilteredComplex`, and retains the object-property and weak-generator statements only as
companion consequences. -/

section

variable {R : Type u} [Ring R]

local notation "CpxMod" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "single" => CochainComplex.singleFunctor (ModuleCat R)

-- Proof sketch: build the approximation tower for the given complex `M`, take its colimit
-- `P^•`, and let the negative-index stages of the resulting filtered cochain complex encode the source
-- increasing filtration `0 = F_{-1} ⊆ F_0 ⊆ F_1 ⊆ ⋯`. The resulting comparison
-- `P^• ⟶ M^•` is a quasi-isomorphism, each component of every successor stage inclusion is split
-- mono, and the graded pieces are direct sums of shifts of the rank-one single complex.
/-- Remark 15.59.11: for every cochain complex `M^•` of `R`-modules there exists a
quasi-isomorphism `P^• ⟶ M^•` from a filtered cochain complex whose negative-index stages encode
an increasing filtration `0 = F_{-1}P^\bullet ⊆ F_0P^\bullet ⊆ F_1P^\bullet ⊆ ⋯` with union
`P^\bullet`, whose successor inclusions `F_iP^\bullet ⟶ F_{i + 1}P^\bullet` are termwise split,
i.e. each component map is a split monomorphism, and whose successive quotients
`F_iP^\bullet / F_{i - 1}P^\bullet` are direct sums of shifts of the one-term complex `R[k]`. In
the canonical decreasing owner `FilteredComplex`, the source stage `F_iP^\bullet` is encoded as
the stage `F^{-i} P^\bullet`. -/
theorem exists_splitFiltered_model_of_cochainComplex
    (M : CpxMod) :
    ∃ (P : FilteredCochainComplex (ModuleCat.{u} R)) (π : P.underlying ⟶ M),
      QuasiIso π ∧
      IsZero (F^{1} P) ∧
      (∀ n : ℤ, ((P.X n).filtration).IsExhaustive) ∧
      (∀ i : ℕ, ∀ n : ℤ,
        IsSplitMono
          ((P.stageMapOfLE
            (show -((i + 1 : ℕ) : ℤ) ≤ -((i : ℕ) : ℤ) by omega)).f n)) ∧
      (∀ i : ℕ,
        ∃ (J : Type u) (shift : J → ℤ),
          Nonempty
            (gr^{-((i : ℕ) : ℤ)} P ≅
              ∐ fun j : J ↦ (single (shift j)).obj ((ModuleCat.of R R) : ModuleCat.{u} R))) :=
  sorry

-- Proof sketch: choose a cochain-complex representative of `M`, apply the previous theorem, and
-- pass from the filtered model to the associated tower of negative-index stages in `D(R)`. The
-- graded-piece hypothesis identifies the initial term and all successive cones with direct sums of
-- shifts of `R[0]`, and the telescope triangle of the tower gives the distinguished triangle whose
-- homotopy colimit is `M`.
/-- Bridge/view form of Remark 15.59.11: every object of `D(R)` admits the Chapter `13`
generating-family resolution whose initial term and successive cone terms are direct sums of
shifts of `R[0]`, and whose canonical homotopy-colimit triangle resolves the object. -/
theorem exists_ringSingle_resolution
    [HasCoproducts DMod] (M : DMod) :
    ∃ (X : ℕ → DMod)
      (map : ∀ n : ℕ, X n ⟶ X (n + 1))
      (Y : ℕ → DMod)
      (triangleHom : ∀ n : ℕ, Y n ⟶ X n)
      (triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧)
      (Khocolim : DMod) (e : Khocolim ≅ M),
        IsGeneratingFamilyApproximation
            (fun _ : Unit ↦ (ringSingle : DMod))
            X map Y triangleHom triangleConnecting ∧
          IsHomotopyColimitOf (Functor.ofSequence map) Khocolim := by
  sorry

-- Proof sketch: apply the preceding generating-family resolution of `M`. The initial term and all
-- successive cone terms satisfy `T` by the shift and coproduct hypotheses, so repeated
-- two-out-of-three along the distinguished triangles of the resolution propagates `T` to every
-- stage and then to `M` through the telescope triangle.
/-- Companion consequence of Remark 15.59.11: let `T` be a property of objects of `D(R)`. If `T`
is preserved under arbitrary direct sums, satisfies the two-out-of-three property for
distinguished triangles, and holds for every shift `R[k]` of the ring object `R[0]`, then `T`
holds for every object of `D(R)`. -/
theorem objectProperty_on_all_derivedModules_of_coproducts_triangles_and_ring_shifts
    (T : ObjectProperty DMod) [∀ ι : Type u, T.IsClosedUnderColimitsOfShape (Discrete ι)]
    (htriangulated₁ :
      ∀ {Δ : Triangle DMod}, Δ ∈ distTriang DMod → T Δ.obj₂ → T Δ.obj₃ → T Δ.obj₁)
    (htriangulated₂ :
      ∀ {Δ : Triangle DMod}, Δ ∈ distTriang DMod → T Δ.obj₁ → T Δ.obj₃ → T Δ.obj₂)
    (htriangulated₃ :
      ∀ {Δ : Triangle DMod}, Δ ∈ distTriang DMod → T Δ.obj₁ → T Δ.obj₂ → T Δ.obj₃)
    (hshiftedRing : ∀ k : ℤ, T ((ringSingle : DMod)⟦k⟧)) : ∀ M : DMod, T M := sorry

-- Proof sketch: `ObjectProperty.IsTriangulated` only produces closure under distinguished
-- triangles up to `T.isoClosure`, so to recover the literal textbook hypotheses we also assume
-- `T` is closed under isomorphisms; then `ObjectProperty.ext_of_isTriangulatedClosedᵢ` gives the
-- three explicit two-out-of-three implications, and the source-facing theorem applies.
/-- Canonical triangulated-owner bridge for Remark 15.59.11: if `T` is stable under arbitrary
direct sums, is closed under isomorphisms, is a triangulated object property on `D(R)`, and holds
for every shift of `R[0]`, then `T` holds for every object of `D(R)`. -/
theorem objectProperty_on_all_derivedModules_of_coproducts_triangulated_and_ring_shifts
    (T : ObjectProperty DMod)
    [T.IsClosedUnderIsomorphisms] [T.IsTriangulated]
    [∀ ι : Type u, T.IsClosedUnderColimitsOfShape (Discrete ι)]
    (hshiftedRing : ∀ k : ℤ, T ((ringSingle : DMod)⟦k⟧)) : ∀ M : DMod, T M := by
  exact
    objectProperty_on_all_derivedModules_of_coproducts_triangles_and_ring_shifts T
      (fun hΔ h₂ h₃ ↦ T.ext_of_isTriangulatedClosed₁ _ hΔ h₂ h₃)
      (fun hΔ h₁ h₃ ↦ T.ext_of_isTriangulatedClosed₂ _ hΔ h₁ h₃)
      (fun hΔ h₁ h₂ ↦ T.ext_of_isTriangulatedClosed₃ _ hΔ h₁ h₂)
      hshiftedRing

-- Proof sketch: if `K` is right-orthogonal to all shifts of `R[0]`, let `A` be the shift-closure
-- of the singleton object property generated by `R[0]`. Then `K ∈ A.rightOrthogonal`, so the left
-- orthogonal `A.rightOrthogonal.leftOrthogonal` contains every shift of `R[0]`. This property is
-- triangulated and closed under arbitrary coproducts, hence the source-facing theorem shows it
-- contains every object, in particular `K`. Applying the defining left-orthogonality to
-- `𝟙 K : K ⟶ K` forces `K` to be zero.
/-- Canonical owner form of Remark 15.59.11: the degree-zero ring object `R[0]` is a weak
generator of the derived category `D(R)`. -/
theorem ringSingle_isWeakGenerator :
    IsWeakGenerator (ringSingle : DMod) := by
  rw [isWeakGenerator_iff_rightOrthogonal_shifts_eq_isZero]
  ext K
  constructor
  · intro hK
    let A : ObjectProperty DMod := (singleton (ringSingle : DMod)).shiftClosure ℤ
    have hAshifted :
        ∀ k : ℤ, A ((ringSingle : DMod)⟦k⟧) := fun k ↦
      ⟨(ringSingle : DMod), k, Iso.refl _, by simp⟩
    let P : ObjectProperty DMod := A.rightOrthogonal
    have hAorth : P K := by
      simpa [A, P] using hK
    let T : ObjectProperty DMod := P.leftOrthogonal
    letI : T.IsClosedUnderIsomorphisms := inferInstance
    letI : T.IsTriangulated := inferInstance
    letI (ι : Type u) : T.IsClosedUnderColimitsOfShape (Discrete ι) := by
      let hT : T = P.trW.isColocal := by
        simpa [T, P] using
          (show P.leftOrthogonal = P.trW.isColocal from
            (show P.trW.isColocal = P.leftOrthogonal from isColocal_trW P).symm)
      rw [hT]
      infer_instance
    have hTK : T K :=
      objectProperty_on_all_derivedModules_of_coproducts_triangulated_and_ring_shifts T
        (fun k ↦ by
          intro Y f hY
          exact hY f (hAshifted k)) K
    exact (Limits.IsZero.iff_id_eq_zero K).2 <| hTK (𝟙 K) hAorth
  · intro hK X f hX
    exact hK.eq_of_tgt f 0

end

end CategoryTheory

/-! ### Lemma_15_59_12 (from Chap15) -/
open CategoryTheory ComplexShape MonoidalCategory

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

/-
Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules and quasi-isomorphism invariance of the
  totalized tensor product;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the chapter owner for the source-facing
    K-flatness predicate;
  - `SymmetricCategory (CochainComplex (ModuleCat R) ℤ)` from `Lemma_15_58_1`, the chapter owner
    that identifies left tensoring with right tensoring via the canonical braiding `β_`;
  - `tensorHom_right_quasiIso_of_isKFlat` from `Lemma_15_59_2`, the chapter owner for
    quasi-isomorphism invariance after tensoring with a fixed K-flat right factor;
  - `CochainComplex.exists_epi_kFlatResolution` from `Lemma_15_59_10`, the chapter owner for the
    K-flat resolution used to reduce the arbitrary left tensor factor to the K-flat case;
  - `HomologicalComplex.tensorHom`, the canonical
    owner abstraction for the induced morphism on totalized tensor products of complexes.

Source/core/bridge triage:
* `source-facing`: the quasi-isomorphism invariance of `Tot(L^• ⊗_R -)` on a quasi-isomorphism
  `α : P^• ⟶ Q^•` between K-flat complexes;
* `core/canonical`: `CochainComplex.IsKFlat`, `tensorHom (𝟙 L) α`, and the symmetric-monoidal
  braiding `β_`;
* `bridge/view`: the right-tensor quasi-isomorphism owner of `Lemma_15_59_2` and the K-flat
  resolution owner of `Lemma_15_59_10`, used to justify the left-tensor statement.

Primitive data are only the complexes `L`, `P`, `Q`, the morphism `α`, and the K-flat/quasi-iso
hypotheses. The induced tensor morphism and the symmetry comparison maps are derived API from the
monoidal owners, so the theorem surface should use `tensorHom (𝟙 L) α` rather than restating the
underlying `mapBifunctorMap` machinery or packaging the braiding into a separate local wrapper.
-/

-- Proof sketch: choose a termwise-epimorphic K-flat resolution `K^• ⟶ L^•` from Lemma `15.59.10`.
-- Lemma `15.59.2` gives quasi-isomorphisms on the vertical maps after tensoring with `P^•` and
-- `Q^•`, and also on the top horizontal map after tensoring the quasi-isomorphism `α` with the
-- K-flat complex `K^•`. The commutative square then shows that the bottom horizontal map is a
-- quasi-isomorphism.
/-- Lemma 15.59.12: if `α : P^• ⟶ Q^•` is a quasi-isomorphism between K-flat cochain complexes of
`R`-modules, then for every cochain complex `L^•` the induced map
`\mathrm{Tot}(\mathrm{id}_{L^•} \otimes \alpha) :
\mathrm{Tot}(L^• \otimes_R P^•) ⟶ \mathrm{Tot}(L^• \otimes_R Q^•)` is a quasi-isomorphism. -/
theorem quasiIso_totalizedTensor_map_right_of_quasiIso_of_isKFlat
    (L P Q : CochainComplex (ModuleCat R) ℤ)
    (hP : P.IsKFlat) (hQ : Q.IsKFlat)
    (α : P ⟶ Q) (hα : QuasiIso α) :
    QuasiIso (tensorHom (𝟙 L) α) := by
  obtain ⟨K, π, hK, _, hπ, _⟩ := CochainComplex.exists_epi_kFlatResolution L
  have hπP : QuasiIso (tensorHom π (𝟙 P)) :=
    tensorHom_right_quasiIso_of_isKFlat P hP π hπ
  have hπQ : QuasiIso (tensorHom π (𝟙 Q)) :=
    tensorHom_right_quasiIso_of_isKFlat Q hQ π hπ
  have hKα_right : QuasiIso (tensorHom α (𝟙 K)) :=
    tensorHom_right_quasiIso_of_isKFlat K hK α hα
  have hKα : QuasiIso (tensorHom (𝟙 K) α) := by
    have hcomp : QuasiIso (tensorHom (𝟙 K) α ≫ (β_ K Q).hom) := by
      letI : QuasiIso ((β_ K P).hom) := inferInstance
      letI := hKα_right
      simpa [BraidedCategory.braiding_naturality_right K α] using
        (quasiIso_comp ((β_ K P).hom) (tensorHom α (𝟙 K)))
    letI : QuasiIso ((β_ K Q).hom) := inferInstance
    letI := hcomp
    exact quasiIso_of_comp_right (tensorHom (𝟙 K) α) (β_ K Q).hom
  have hsquare :
      tensorHom π (𝟙 P) ≫ tensorHom (𝟙 L) α =
        tensorHom (𝟙 K) α ≫ tensorHom π (𝟙 Q) := by
    simpa using (((curriedTensor (CochainComplex (ModuleCat R) ℤ)).map π).naturality α).symm
  have hcomp : QuasiIso (tensorHom π (𝟙 P) ≫ tensorHom (𝟙 L) α) := by
    letI := hKα
    letI := hπQ
    have hcomp' : QuasiIso (tensorHom (𝟙 K) α ≫ tensorHom π (𝟙 Q)) :=
      quasiIso_comp (tensorHom (𝟙 K) α) (tensorHom π (𝟙 Q))
    rw [← hsquare] at hcomp'
    exact hcomp'
  letI := hπP
  letI := hcomp
  exact quasiIso_of_comp_left (tensorHom π (𝟙 P)) (tensorHom (𝟙 L) α)

end

/-! ### Definition_15_59_13 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]

local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)

/-- The homotopy-category functor whose total left derived functor defines tensoring with a fixed
derived object of `D(R)`. -/
private noncomputable abbrev derivedTensorSourceFunctor (M : DMod) : KMod ⥤ DMod :=
  tensorRight (DerivedCategory.Qh.objPreimage M) ⋙ Qh

-- Proof sketch: choose a representative complex of `M` in `K(R)`, replace it by a K-flat
-- resolution using the preceding K-flat theory, and use quasi-isomorphism invariance of tensoring
-- with a K-flat complex to invoke the universal property of the total left derived functor.
/-- Totalized tensoring with a chosen representative of a derived `R`-complex admits a total left
derived functor on `D(R)`. -/
private theorem derivedTensorSourceFunctor_hasLeftDerivedFunctor
    (M : DMod) :
    (derivedTensorSourceFunctor M).HasLeftDerivedFunctor Qis := sorry

/-- Definition 15.59.13: for an object `M^•` of `D(R)`, the derived tensor product
`- \otimes_R^{\mathbf L} M^•` is the endofunctor of `D(R)` obtained by left deriving totalized
tensoring with a chosen representative of `M^•` in `K(R)`. -/
noncomputable def derivedTensorProduct (M : DMod) : DMod ⥤ DMod :=
  letI := derivedTensorSourceFunctor_hasLeftDerivedFunctor M
  (derivedTensorSourceFunctor M).totalLeftDerived Qh Qis

-- Proof sketch: the homotopy-category tensor functor with fixed right factor commutes with shifts,
-- and the same compatibility is inherited by the total left derived functor on the derived
-- category.
/-- The derived tensor product functor commutes with the triangulated shift. -/
noncomputable instance derivedTensorProduct_commShift (M : DMod) :
    (derivedTensorProduct M).CommShift ℤ := sorry

-- Proof sketch: the underived tensor functor on `K(R)` with fixed right factor is triangulated by
-- Lemma `15.58.4`; passing to its total left derived functor yields an exact functor on `D(R)`.
/-- The derived tensor product functor is exact in the triangulated sense. -/
theorem derivedTensorProduct_isTriangulated (M : DMod) :
    (derivedTensorProduct M).IsTriangulated := sorry

end

end CategoryTheory

namespace DerivedTensorProduct

/- Textbook notation for the derived tensor product object `K ⊗[R]^L L` in `D(R)`. -/
scoped notation:70 K:70 " ⊗[" R:70 "]^L " L:71 =>
  Functor.obj (@CategoryTheory.derivedTensorProduct R _ L) K

end DerivedTensorProduct

/-! ### Lemma_15_59_14 (from Chap15) -/
noncomputable section

open CategoryTheory
open ComplexShape
open CategoryTheory.MonoidalCategory
open BraidedCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable [∀ (K₁ K₂ : CochainComplex (ModuleCat R) ℤ),
  CochainComplex.HasMapBifunctor K₁ K₂ (curriedTensor (ModuleCat R))]

/- Domain-style sampling for Lemma 15.59.14:
- primary domain: monoidal localization of the homotopy category of cochain complexes, and its
  comparison with the derived tensor product on `D(R)`;
- sampled owner declarations:
  `homotopyCategory_moduleCat_symmetric_category`,
  `LocalizedMonoidal`,
  `Functor.totalLeftDerived`,
  `derivedTensorProduct`;
- best owner abstraction: the canonical owner of commutativity for derived tensor product is the
  symmetric monoidal structure on `DerivedCategory (ModuleCat R)` induced from the symmetric
  monoidal structure on `HomotopyCategory (ModuleCat R) (up ℤ)`, with the notation
  `K ⊗[R]^L L` as the source-facing bridge to the owner tensor;
- primitive vs. derived:
  primitive data are the symmetric monoidal structure on `K(R)` from Lemma `15.58.3`, the
  monoidal stability of quasi-isomorphisms, and the localized monoidal tensor on `D(R)`;
  the tensor-vs-derived-tensor comparison and the commutativity statement below are derived API;
- source/core/bridge triage:
  `source-facing`: the canonical commutativity of `K ⊗[R]^L L`;
  `core/canonical`: the `MonoidalCategory`/`SymmetricCategory` instances on `D(R)`;
  `bridge/view`: the comparison theorem identifying the localized tensor object with
  `K ⊗[R]^L L`;
- layer: this file is a `bridge/view` owner for the source-facing derived-tensor symmetry, so it
  should reuse the localized symmetric-monoidal owner directly rather than keep a parallel
  standalone existence theorem. -/

local notation "KMod" => HomotopyCategory (ModuleCat R) (up ℤ)
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "Qh" => (DerivedCategory.Qh : KMod ⥤ DMod)
local notation "Qis" => HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)
local notation "Cpx" => CochainComplex (ModuleCat R) ℤ

-- Proof sketch: quasi-isomorphisms in `K(R)` are detected on homology, tensoring in the homotopy
-- category comes from the symmetric monoidal tensor product on complexes from Lemma `15.58.3`,
-- and tensoring two quasi-isomorphisms again yields a quasi-isomorphism.
/-- Quasi-isomorphisms in the homotopy category `K(R)` are stable under tensor product. -/
private theorem homotopyCategory_quasiIso_isMonoidal :
    (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal := by
  sorry

/-- The monoidal category structure on `D(R)` obtained by localizing the tensor product on the
homotopy category `K(R)`. -/
noncomputable instance : MonoidalCategory DMod := by
  let _ : (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  change MonoidalCategory
    (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KMod))))
  infer_instance

-- Proof sketch: localize the symmetric monoidal structure on `K(R)` along quasi-isomorphisms,
-- using the preceding monoidal stability theorem.
/-- The derived category `D(R)` inherits the symmetric monoidal structure obtained by localizing
the tensor product on `K(R)`. -/
noncomputable instance : SymmetricCategory DMod := by
  let _ : (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  change SymmetricCategory
    (LocalizedMonoidal Qh Qis (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KMod))))
  infer_instance

noncomputable instance : (DerivedCategory.Qh : KMod ⥤ DMod).Monoidal := by
  let _ : (HomotopyCategory.quasiIso (ModuleCat R) (up ℤ)).IsMonoidal :=
    homotopyCategory_quasiIso_isMonoidal
  simpa using
    (inferInstance :
      (Localization.Monoidal.toMonoidalCategory
        Qh
        Qis
        (Iso.refl ((Qh).obj (MonoidalCategoryStruct.tensorUnit KMod)))).Monoidal)

private noncomputable def derivedCategory_tensorLeftComparisonIso
    (L : DMod) :
    Qh ⋙ MonoidalCategory.tensorLeft L ≅
      MonoidalCategory.tensorRight (tensorRightRepresentative L) ⋙ Qh := by
  exact
    Functor.isoWhiskerLeft Qh
        ((tensoringLeft DMod).mapIso
          (tensorRightRepresentativeIso L)).symm ≪≫
      Functor.Monoidal.commTensorLeft Qh
        (tensorRightRepresentative L) ≪≫
      Functor.isoWhiskerRight
        (tensorLeftIsoTensorRight (tensorRightRepresentative L))
        Qh

-- Proof sketch: the comparison isomorphism identifies `tensorLeft L` with a localization of the
-- underived tensor functor, and that source functor is already inverted on quasi-isomorphisms.
private noncomputable instance derivedCategory_tensorLeft_isLeftDerived
    (L : DMod) :
    (MonoidalCategory.tensorLeft L).IsLeftDerivedFunctor
      (derivedCategory_tensorLeftComparisonIso L).hom Qis := by
  simpa using
    (Functor.isLeftDerivedFunctor_of_inverts Qis (MonoidalCategory.tensorLeft L)
      (derivedCategory_tensorLeftComparisonIso L))

private noncomputable def tensorLeftIsoDerivedTensorProduct
    (L : DMod) :
    MonoidalCategory.tensorLeft L ≅ derivedTensorProduct L := by
  let F : KMod ⥤ DMod :=
    MonoidalCategory.tensorRight (tensorRightRepresentative L) ⋙ Qh
  let _ : F.HasLeftDerivedFunctor Qis := tensorRightCompQh_hasLeftDerivedFunctor L
  let G : DMod ⥤ DMod :=
    F.totalLeftDerived Qh Qis
  let e : MonoidalCategory.tensorLeft L ≅ G :=
    Functor.leftDerivedNatIso
      (MonoidalCategory.tensorLeft L)
      G
      (derivedCategory_tensorLeftComparisonIso L).hom
      (Functor.totalLeftDerivedCounit
        F
        Qh
        Qis)
      Qis
      (Iso.refl F)
  simpa [F, G, derivedTensorProduct] using e

-- Proof sketch: the localized tensor product on `D(R)` is the total left derived functor of
-- tensoring with a fixed right factor in `K(R)`, hence agrees with the source-facing derived tensor
-- product notation from Definition `15.59.13`.
/-- The localized tensor product on `D(R)` is canonically isomorphic to the source-facing derived
tensor product `K ⊗[R]^L L`. -/
noncomputable def derivedCategory_tensorObj_iso_derivedTensorProduct
    (K L : DMod) :
    K ⊗ L ≅ (derivedTensorProduct L).obj K :=
  β_ K L ≪≫ (tensorLeftIsoDerivedTensorProduct L).app K

/-- The fixed-right-factor tensor functor on `D(R)` is canonically isomorphic to the source-facing
derived tensor product functor `- ⊗[R]^L L`. -/
noncomputable def tensoringRightIsoDerivedTensorProduct
    (L : DMod) :
    (tensoringRight DMod).obj L ≅ derivedTensorProduct L :=
  NatIso.ofComponents
    (fun K ↦ derivedCategory_tensorObj_iso_derivedTensorProduct K L)
    (fun {_ _} _ ↦ by
      sorry)

@[simp] theorem tensoringRightIsoDerivedTensorProduct_hom_app (L K : DMod) :
    (tensoringRightIsoDerivedTensorProduct L).hom.app K =
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L).hom :=
  rfl

@[simp] theorem tensoringRightIsoDerivedTensorProduct_inv_app (L K : DMod) :
    (tensoringRightIsoDerivedTensorProduct L).inv.app K =
      (derivedCategory_tensorObj_iso_derivedTensorProduct K L).inv :=
  rfl

-- Proof sketch: compare both derived-tensor objects with the owner tensor `K ⊗ L` on `D(R)`, and
-- then apply the braiding isomorphism of the symmetric monoidal structure on `D(R)`.
/-- Lemma 15.59.14: for derived `R`-complexes `K^•` and `L^•`, the derived tensor products
`K^• \otimes_R^{\mathbf L} L^•` and `L^• \otimes_R^{\mathbf L} K^•` are canonically isomorphic,
functorially in both complexes, with the chain-level symmetry using the sign `(-1)^(pq)` on
`K^p ⊗_R L^q`. -/
noncomputable def derivedTensorProduct_comm (K L : DMod) :
    (derivedTensorProduct L).obj K ≅ (derivedTensorProduct K).obj L :=
  (derivedCategory_tensorObj_iso_derivedTensorProduct K L).symm ≪≫
    β_ K L ≪≫
      derivedCategory_tensorObj_iso_derivedTensorProduct L K

end

end CategoryTheory

/-! ### Lemma_15_59_15 (from Chap15) -/
noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable [Preadditive (ModuleCat R)] [HasZeroObject (ModuleCat R)]
variable [MonoidalCategory (ModuleCat R)] [SymmetricCategory (ModuleCat R)]
variable [(curriedTensor (ModuleCat R)).Additive]
variable [∀ X : ModuleCat R, ((curriedTensor (ModuleCat R)).obj X).Additive]
variable [∀ G₁ G₂ : GradedObject ℤ (ModuleCat R), GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R), GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ (ModuleCat R), GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ (ModuleCat R), GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ X : ModuleCat R,
  PreservesColimit (Functor.empty.{0} (ModuleCat R)) ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ X : ModuleCat R,
  PreservesColimit (Functor.empty.{0} (ModuleCat R)) ((curriedTensor (ModuleCat R)).flip.obj X)]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for derived tensor associativity:
- primary domain: localized monoidal structures on homotopy and derived categories of module
  complexes;
- sampled owner declarations: `Localization.Monoidal.associator` in mathlib's localized monoidal
  API, `MonoidalCategory.tensorRightTensor`, `tensoringRightIsoDerivedTensorProduct` from Lemma
  `15.59.14`, and the ambient monoidal associator `α_`;
- layer: this file remains a `source-facing` bridge for the textbook associativity isomorphism on
  derived tensor products. The owner abstraction for associativity lives in the ambient monoidal
  coherence API, so this file should not duplicate generic inverse-identity lemmas. -/

/-- The functorial comparison identifying two successive derived tensor functors with tensoring by
the derived tensor product of the right factors. -/
noncomputable def derivedTensorProductTensorIso
    (L M : DMod) :
    derivedTensorProduct L ⋙ derivedTensorProduct M ≅
      derivedTensorProduct (L ⊗[R]^L M) :=
  Functor.isoWhiskerRight (tensoringRightIsoDerivedTensorProduct L).symm
      (derivedTensorProduct M) ≪≫
    Functor.isoWhiskerLeft ((tensoringRight DMod).obj L)
      (tensoringRightIsoDerivedTensorProduct M).symm ≪≫
      (tensorRightTensor L M).symm ≪≫
        (tensoringRight DMod).mapIso
          (derivedCategory_tensorObj_iso_derivedTensorProduct L M) ≪≫
          tensoringRightIsoDerivedTensorProduct (L ⊗[R]^L M)

/-- Lemma 15.59.15: for complexes `K^•`, `L^•`, and `M^•` of `R`-modules, there is a canonical
associativity isomorphism
`(K^• \otimes_R^{\mathbf L} L^•) \otimes_R^{\mathbf L} M^• \cong
K^• \otimes_R^{\mathbf L} (L^• \otimes_R^{\mathbf L} M^•)`,
functorial in all three complexes. -/
noncomputable def derivedTensorProduct_associator
    (K L M : DMod) :
    ((K ⊗[R]^L L) ⊗[R]^L M) ≅ (K ⊗[R]^L (L ⊗[R]^L M)) :=
  (derivedTensorProductTensorIso L M).app K

end

end CategoryTheory

/-! ### Lemma_15_59_16 (from Chap15) -/
open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

set_option checkBinderAnnotations false

universe u

namespace CochainComplex

section

variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat R) ℤ}

/- Domain sampling pass:
* primary domain: factorization up to homotopy of morphisms of cochain complexes of `R`-modules
  through quasi-isomorphisms with K-flat source, on the canonical tensor surface of
  `ModuleCat R`;
* sampled owner declarations:
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the chapter owner for the K-flatness
    clause on the intermediate complex in the canonical module-tensor context;
  - `CochainComplex.tensorHom_right_quasiIso_of_isKFlat` from `Lemma_15_59_2`, the nearby owner
    showing that tensoring with a K-flat complex preserves quasi-isomorphisms;
  - `CochainComplex.isKFlat_obj₂_of_distinguished_triangle` and
    `CochainComplex.isKFlat_obj₃_of_distinguished_triangle` from `Lemma_15_59_5`, the chapter
    owners for the two-out-of-three propagation of K-flatness in distinguished triangles;
  - `exists_termwiseEpi_kFlatResolution` from `Lemma_15_59_10`, the chapter owner supplying the
    K-flat replacement input used in the standard construction;
  - `Homotopy` and `QuasiIso`, the canonical comparison owners for the factorization data.

Source/core/bridge triage:
* `source-facing`: the Stacks lemma is stated for an arbitrary ring, but the current Chapter 15
  owner `CochainComplex.IsKFlat` is available here only on the canonical tensor surface of
  `ModuleCat R`, so this file records the faithful commutative-ring specialization instead of
  quantifying over an arbitrary monoidal structure on `ModuleCat R`;
* `core/canonical`: `N.IsKFlat`, `QuasiIso c`, and `Homotopy a (b ≫ c)`;
* `bridge/view`: the commutative-ring specialization of the source factorization statement to the
  canonical module-tensor owner used in this chapter.

Primitive data are only the intermediate complex `N` and the maps `b`, `c`. The K-flatness,
quasi-isomorphism, and homotopy clauses are derived API over existing owner abstractions, so this
file exposes them directly instead of introducing a factorization wrapper structure.
-/

-- Proof sketch: complete `a` to a distinguished triangle and replace its cone by a K-flat
-- quasi-isomorphic model. The resulting comparison triangle
-- `K^• ⟶ N^• ⟶ M^• ⟶ K^•[1]` gives `N^•` K-flat by the two-out-of-three K-flatness theorem, and
-- the triangle comparison yields a map `c : N^• ⟶ L^•` whose composite with `b` is homotopic to
-- `a`.
/-- Commutative-ring specialization of Lemma 15.59.16 (1): if
`a : K^• ⟶ L^•` is a morphism of cochain complexes of `R`-modules and `K^•` is K-flat, then `a`
factors up to homotopy through a quasi-isomorphism `c : N^• ⟶ L^•` with `N^•` K-flat. -/
theorem exists_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ QuasiIso c := sorry

/- The source also records a termwise-flat refinement. In the current Chapter 15 owner hierarchy,
`CochainComplex.IsTermwiseFlat` is likewise available on the commutative-ring tensor surface, so
the strengthened factorization theorem stays in the same canonical module-tensor context as the
preceding specialization. The source K-flatness hypothesis on `K` is retained here: termwise
flatness refines the choice of `N`, but the two-out-of-three K-flatness argument for `N` still
runs through `K.IsKFlat`. -/

-- Proof sketch: choose the comparison triangle in split degreewise form so that
-- `N^n ≅ M^n ⊕ K^n`; K-flatness of `K^•` and of the chosen cone replacement gives `N.IsKFlat`
-- by the same two-out-of-three argument as above, while flatness of the terms of `K^•` and of
-- the cone replacement propagates termwise to `N^•`.
/-- Commutative-ring bridge for the termwise-flat refinement of Lemma 15.59.16: if
`a : K^• ⟶ L^•` is a morphism of cochain
complexes of `R`-modules, `K^•` is K-flat, and each term of `K^•` is flat, then one may moreover
choose the intermediate complex `N^•` with flat terms. -/
theorem exists_termwiseFlat_kFlat_factorization_up_to_homotopy
    (a : K ⟶ L) (hK : K.IsKFlat) (hFlat : K.IsTermwiseFlat) :
    ∃ (N : CochainComplex (ModuleCat R) ℤ) (b : K ⟶ N) (c : N ⟶ L),
      Nonempty (Homotopy a (b ≫ c)) ∧ N.IsKFlat ∧ N.IsTermwiseFlat ∧ QuasiIso c := sorry

end

end CochainComplex
