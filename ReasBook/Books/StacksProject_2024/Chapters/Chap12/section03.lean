import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Tactic.Recall
import Mathlib.Tactic.TFAE

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_3_1 (from Chap12) -/
universe v u

namespace CategoryTheory

variable (A : Type u) [Category.{v} A]

/- Domain-style sampling for Definition 12.3.1:
- primary domain: preadditive categories and additive functors;
- sampled owner API:
  `Preadditive`,
  `Preadditive.preadditiveHasZeroMorphisms`,
  `Functor.Additive`,
  `Functor.mapAddHom`;
- best owner abstraction: `Preadditive A` for the additive enrichment on `A`, and
  `Functor.Additive` for additivity of functors between preadditive categories.

Primitive data live in the owner classes `Preadditive` and `Functor.Additive`. Zero morphisms are
derived from `Preadditive`, and the additive-hom API for a functor is derived from
`Functor.Additive`, so neither should be rebuilt as parallel local data.
-/
/- Source/core/bridge triage for Definition 12.3.1:
- source-facing: the additive enrichment on hom-sets, and the additivity property for functors
  between such categories
- core/canonical owners: `Preadditive A` and `Functor.Additive`
- bridge/view: `Limits.HasZeroMorphisms A` is derived API from `Preadditive A`, so it should not
  appear as parallel primitive data -/
/- Definition 12.3.1 (1): a preadditive category is a category whose hom-sets are abelian groups
and whose composition law is bilinear in both variables; this is the canonical mathlib class
`CategoryTheory.Preadditive`. -/
recall Preadditive

section

variable [Preadditive A]

/- Companion recall: in a preadditive category, zero morphisms are derived API via the canonical
instance `Preadditive.preadditiveHasZeroMorphisms`, so the owner-level statement remains
`Preadditive A`. -/
#synth Limits.HasZeroMorphisms A

end

/- Definition 12.3.1 (2): for preadditive categories, an additive functor is a functor whose map
on every hom-group is an additive homomorphism; this is the canonical mathlib class
`CategoryTheory.Functor.Additive`. -/
recall Functor.Additive

end CategoryTheory

/-! ### Lemma_12_3_2 (from Chap12) -/
universe v u

namespace CategoryTheory.Limits

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

/- Source/core/bridge triage for Lemma 12.3.2:
- source-facing: the textbook equivalences between initiality, terminality, vanishing identity, and
  factorization through a zero object
- core/canonical owner: `IsZero`
- bridge/view: the TFAE packaging in part (1) and the factorization criterion in part (2) -/

/- Lemma 12.3.2 (1), canonical owner theorem: in a category with zero morphisms, an object is zero
if and only if its identity endomorphism is zero. -/
recall IsZero.iff_id_eq_zero

/-- Lemma 12.3.2 (1): in a category with zero morphisms, an object is initial, terminal, and has
zero identity endomorphism in equivalent ways. -/
lemma isInitial_isTerminal_id_eq_zero_tfae (x : C) :
    ([Nonempty (IsInitial x),
      Nonempty (IsTerminal x),
      𝟙 x = 0] : List Prop).TFAE := by
  have hzero : IsZero x ↔ 𝟙 x = 0 := IsZero.iff_id_eq_zero x
  tfae_have 1 ↔ 3 := by
    constructor
    · rintro ⟨h⟩
      exact hzero.1 h.isZero
    · intro hx
      exact ⟨(hzero.2 hx).isInitial⟩
  tfae_have 2 ↔ 3 := by
    constructor
    · rintro ⟨h⟩
      exact hzero.1 h.isZero
    · intro hx
      exact ⟨(hzero.2 hx).isTerminal⟩
  tfae_finish

-- Proof sketch: if `α = β ≫ γ` factors through a zero object `x`, then `β = 0` and `γ = 0` by
-- the owner lemmas `IsZero.eq_zero_of_tgt` and `IsZero.eq_zero_of_src`. Conversely, the zero
-- morphism factors through any object, hence in particular through `x`.
/-- Lemma 12.3.2 (2): a morphism factors through a zero object if and only if it is the zero
morphism. -/
lemma factor_thru_isZero_iff_eq_zero {x y z : C} (hx : IsZero x) (α : y ⟶ z) :
    (∃ β : y ⟶ x, ∃ γ : x ⟶ z, α = β ≫ γ) ↔ α = 0 := by
  constructor
  · rintro ⟨β, γ, rfl⟩
    simp [hx.eq_zero_of_tgt β, hx.eq_zero_of_src γ]
  · rintro rfl
    exact ⟨hx.from_ y, hx.to_ z, by simp [hx.eq_zero_of_tgt (hx.from_ y)]⟩

end

end CategoryTheory.Limits

/-! ### Definition_12_3_3 (from Chap12) -/
universe v u

namespace CategoryTheory.Limits

/-
Domain-style sampling for Definition 12.3.3:
- primary domain: zero, initial, and terminal objects in a category;
- inspected canonical declarations:
  `IsZero`,
  `IsZero.isInitial`,
  `IsZero.isTerminal`,
  `IsInitial.isZero`;
- owner abstraction: `IsZero X`;
- primitive data: the canonical initial and terminal structures on `X`;
- derived API: `IsZero.isInitial` and `IsZero.isTerminal` already live on the owner. The
  zero-morphism layer adds one-sided reverse constructors such as `IsInitial.isZero`, so this file
  only needs the source-facing bridge from both structures to `IsZero X` without extra ambient
  hypotheses.

Source/core/bridge triage:
- `source-facing`: the source characterization that a zero object is both initial and terminal;
- `core/canonical`: the owner predicate `IsZero X`;
- `bridge/view`: the reverse constructor from `IsInitial X` and `IsTerminal X` to `IsZero X`. -/

/- Definition 12.3.3: the notion of zero object is the canonical predicate `IsZero`. -/
recall IsZero
recall IsZero.isInitial
recall IsZero.isTerminal

section

variable {C : Type u} [Category.{v} C]
variable {X : C}

namespace IsInitial

/-- Definition 12.3.3, source-facing bridge: if an initial object is also terminal, then it is a
zero object. Unlike the zero-morphism-based theorem `IsInitial.isZero`, this bridge does not
assume ambient zero morphisms. -/
theorem isZero_of_isTerminal (hI : IsInitial X) (hT : IsTerminal X) : IsZero X :=
  { unique_to := fun Y ↦ ⟨{ default := hI.to Y, uniq := fun f ↦ hI.hom_ext f _ }⟩
    unique_from := fun Y ↦ ⟨{ default := hT.from Y, uniq := fun f ↦ hT.hom_ext f _ }⟩ }

end IsInitial

end

end CategoryTheory.Limits

/-! ### Lemma_12_3_4 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (X Y : C)

/- Domain-style sampling for Lemma 12.3.4:
- primary domain: binary products, coproducts, and biproducts in a preadditive category;
- sampled canonical declarations:
  `HasBinaryBiproduct.of_hasBinaryProduct`,
  `HasBinaryBiproduct.of_hasBinaryCoproduct`,
  `HasBinaryBiproduct.hasLimit_pair`,
  `HasBinaryBiproduct.hasColimit_pair`;
- owner abstraction: `HasBinaryBiproduct X Y`;
- primitive data: a chosen binary product or binary coproduct structure on `X` and `Y`;
- derived API: the opposite finite-limit/finite-colimit structure obtained from the owner
  biproduct instance.

Source/core/bridge triage:
- `source-facing`: the textbook equivalence between existence of the binary product and binary
  coproduct of `X` and `Y`;
- `core/canonical`: the owner instance `HasBinaryBiproduct X Y`;
- `bridge/view`: the equivalence theorem below, obtained by passing through that owner. -/

/- Core/canonical owner declaration used in Lemma 12.3.4: in a preadditive category, a binary
product canonically yields a binary biproduct. -/
recall HasBinaryBiproduct.of_hasBinaryProduct (X Y : C) [HasBinaryProduct X Y] :
    HasBinaryBiproduct X Y

/- Core/canonical owner declaration used in Lemma 12.3.4: dually, a binary coproduct canonically
yields a binary biproduct. -/
recall HasBinaryBiproduct.of_hasBinaryCoproduct (X Y : C) [HasBinaryCoproduct X Y] :
    HasBinaryBiproduct X Y

/-- Lemma 12.3.4: in a preadditive category, a binary product of `x` and `y` exists if and only
if a binary coproduct of `x` and `y` exists. -/
theorem hasBinaryProduct_iff_hasBinaryCoproduct
    : HasBinaryProduct X Y ↔ HasBinaryCoproduct X Y := by
  constructor
  · intro _
    let _ : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryProduct X Y
    infer_instance
  · intro _
    let _ : HasBinaryBiproduct X Y := HasBinaryBiproduct.of_hasBinaryCoproduct X Y
    infer_instance

end

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (X Y : C) [HasBinaryBiproduct X Y]

/- The final sentence of Lemma 12.3.4 is the existing mathlib comparison isomorphism `biprodIso`
in the chosen binary biproduct context. -/
recall biprodIso

end

end CategoryTheory

/-! ### Definition_12_3_5 (from Chap12) -/
namespace CategoryTheory

open Limits

universe v u

attribute [local instance] HasBinaryBiproduct.of_hasBinaryProduct

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (x y : C) [HasBinaryProduct x y]

/- Source/core/bridge triage for Definition 12.3.5:
- source-facing: the direct sum `x ⊕ y` is the binary product `x ⨯ y` together with the two
  projections and the two canonical inclusions
- primitive data: `prod x y`, `prod.fst`, and `prod.snd`
- derived API: the canonical inclusions `prod.inl` and `prod.inr`, obtained from the product
  structure together with the zero morphisms already supplied by `Preadditive C`
- core/canonical companion: Lemma 12.3.4 upgrades the same product-based data to the canonical
  binary biproduct view via `HasBinaryBiproduct.of_hasBinaryProduct`
- bridge/view: the chosen biproduct object `x ⊞ y`, compared to the source-facing product by
  `biprod.isoProd` -/
/- Definition 12.3.5: in a preadditive category, the textbook direct sum `x ⊕ y` is the binary
product `x × y`, i.e. the product object `x ⨯ y`. -/
recall prod

/- Companion recall: the source-facing direct sum comes with the usual projection maps
`prod.fst : x ⨯ y ⟶ x` and `prod.snd : x ⨯ y ⟶ y`. -/
recall prod.fst
recall prod.snd

/- Companion recall: in a preadditive category, the direct-sum inclusions into the source-facing
product object are the canonical morphisms `prod.inl : x ⟶ x ⨯ y` and
`prod.inr : y ⟶ x ⨯ y`. -/
recall prod.inl
recall prod.inr

/- Companion recall: Lemma 12.3.4 supplies the canonical binary biproduct view of the same
product-based direct sum. -/
recall HasBinaryBiproduct.of_hasBinaryProduct (x y : C) [HasBinaryProduct x y] :
    HasBinaryBiproduct x y

/- Companion recall: the chosen binary biproduct object `x ⊞ y` is canonically isomorphic to the
source-facing product object `x ⨯ y`. -/
recall biprod.isoProd

end

end CategoryTheory

/-! ### Remark_12_3_6 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

section

variable {C : Type u} [Category.{v} C] [Preadditive C]

/- Domain-style sampling for Remark 12.3.6:
- primary domain: binary biproducts/direct sums in a preadditive category;
- sampled canonical declarations:
  `BinaryBicone`,
  `inl_of_isLimit`,
  `fst_of_isColimit`,
  `IsBilimit.binary_total`,
  `isBinaryBilimitOfTotal`;
- owner abstraction: `BinaryBicone X Y`;
- primitive data: a binary bicone `b : BinaryBicone X Y`;
- derived API: the inclusions determined by `b.toCone`, the projections determined by
  `b.toCocone`, and the total relation characterizing `b.IsBilimit`.

Source/core/bridge triage for Remark 12.3.6:
- source-facing: the three-part characterization of a binary direct sum, namely uniqueness of the
  inclusions from the projections, uniqueness of the projections from the inclusions, and the
  total identity for any bilimit bicone together with its converse;
- core/canonical: the owner object `BinaryBicone X Y` and its bilimit predicate `b.IsBilimit`;
- bridge/view: none, since each source clause is already present upstream as owner-level API. -/
/- Remark 12.3.6 (1): for a binary direct-sum diagram, the inclusions are uniquely determined by
the projections. -/
recall inl_of_isLimit {X Y : C} {b : BinaryBicone X Y} (hb : IsLimit b.toCone) :
    b.inl = hb.lift (BinaryFan.mk (𝟙 X) 0)

recall inr_of_isLimit {X Y : C} {b : BinaryBicone X Y} (hb : IsLimit b.toCone) :
    b.inr = hb.lift (BinaryFan.mk 0 (𝟙 Y))

/- Remark 12.3.6 (2): dually, the projections are uniquely determined by the inclusions. -/
recall fst_of_isColimit {X Y : C} {b : BinaryBicone X Y} (hb : IsColimit b.toCocone) :
    b.fst = hb.desc (BinaryCofan.mk (𝟙 X) 0)

recall snd_of_isColimit {X Y : C} {b : BinaryBicone X Y} (hb : IsColimit b.toCocone) :
    b.snd = hb.desc (BinaryCofan.mk 0 (𝟙 Y))

/- Remark 12.3.6 (3): any binary biproduct satisfies the total relation, and conversely that
relation already forces the bicone to be a binary biproduct. -/
recall IsBilimit.binary_total {X Y : C} {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt

recall isBinaryBilimitOfTotal {X Y : C} (b : BinaryBicone X Y)
    (total : b.fst ≫ b.inl + b.snd ≫ b.inr = 𝟙 b.pt) : b.IsBilimit

end

end CategoryTheory

/-! ### Lemma_12_3_7 (from Chap12) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

section

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A]
variable {B : Type u₂} [Category.{v₂} B] [Preadditive B]
variable (F : A ⥤ B) [F.Additive]

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

/- Source/core/bridge triage for Lemma 12.3.7:
- source-facing: an additive functor preserves binary direct sums and zero objects
- core/canonical owner: `Functor.Additive`
- bridge/view: `PreservesBinaryBiproducts F` and `Functor.map_isZero` are derived from the owner,
  so they should remain recall-level consequences rather than new local wrapper declarations -/

/- Lemma 12.3.7 (1): this is a source-facing use of the canonical owner abstraction
`Functor.Additive`. In mathlib, additivity gives `PreservesFiniteBiproducts F`, and binary direct
sums are then recovered through the canonical derived instance `PreservesBinaryBiproducts F`. -/
#synth PreservesBinaryBiproducts F

/- Lemma 12.3.7 (2): preservation of zero objects is derived API, not extra primitive data. Once
`F` is additive, the canonical owner theorem is `Functor.map_isZero`. -/
recall Functor.map_isZero

end

end CategoryTheory

/-! ### Definition_12_3_8 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

variable (A : Type u) [Category.{v} A]

/- Domain-style sampling for Definition 12.3.8:
- primary domain: additive structure on a preadditive category via finite limits/biproducts;
- sampled owner declarations:
  `HasFiniteProducts`,
  `HasFiniteBiproducts.of_hasFiniteProducts`,
  `hasZeroObject_of_hasFiniteBiproducts`;
- best owner abstraction: `HasFiniteProducts A`;
- primitive data: the preadditive enrichment and the finite-product structure;
- derived API: finite biproducts, direct sums, and the zero object. -/
/- Source/core/bridge triage for Definition 12.3.8:
- source-facing: in the source, an additive category is a preadditive category with finite
  products
- core/canonical owner: `HasFiniteProducts A`
- bridge/view: `HasFiniteBiproducts.of_hasFiniteProducts` supplies direct sums, and the zero object
  is then inferred canonically -/
section

variable [Preadditive A]

/- Definition 12.3.8: once `A` is preadditive, the source condition that `A` be additive is
exactly the canonical limit structure `HasFiniteProducts A`. -/
recall HasFiniteProducts

section

variable [HasFiniteProducts A]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/- Companion bridge: the source-level direct-sum clause is the upstream owner theorem
`HasFiniteBiproducts.of_hasFiniteProducts`; after installing that canonical instance, the
zero-object owner is the standard derived instance `hasZeroObject_of_hasFiniteBiproducts A`. -/
recall HasFiniteBiproducts.of_hasFiniteProducts
#check (hasZeroObject_of_hasFiniteBiproducts A : HasZeroObject A)

end

end

end CategoryTheory

/-! ### Definition_12_3_9 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)

/- Source/core/bridge triage for Definition 12.3.9:
- source-facing: the textbook kernel, cokernel, coimage, and image attached to a morphism
- core/canonical owners: `kernel f` and `cokernel f`
- bridge/view: `Abelian.coimage f` and `Abelian.image f` are the abelian source-facing owners
  obtained from those canonical kernel/cokernel constructions -/

section

variable [HasKernel f]

/-
Definition 12.3.9 (kernel): the textbook kernel construction in a preadditive category is the
canonical owner object `kernel f` with structure morphism `kernel.ι f`, characterized by the
universal property `kernelIsKernel f`; the owner API itself only needs zero morphisms.
-/
recall kernel
recall kernel.ι
recall kernel.condition
recall kernelIsKernel

end

section

variable [HasCokernel f]

/-
Definition 12.3.9 (cokernel): the textbook cokernel construction in a preadditive category is the
canonical owner object `cokernel f` with structure morphism `cokernel.π f`, characterized by the
universal property `cokernelIsCokernel f`; the owner API itself only needs zero morphisms.
-/
recall cokernel
recall cokernel.π
recall cokernel.condition
recall cokernelIsCokernel

end

section

variable [HasKernel f]
variable [HasCokernel (kernel.ι f)]

/- Definition 12.3.9 (coimage): the textbook coimage construction, stated for preadditive
categories, is the canonical owner object `Abelian.coimage f` with structure morphism
`Abelian.coimage.π f`. -/
recall Abelian.coimage
recall Abelian.coimage.π

/- Companion bridge: the source-facing coimage definition is exactly the canonical cokernel owner
applied to `kernel.ι f`, with universal property `cokernelIsCokernel (kernel.ι f)`. -/
#check cokernelIsCokernel (kernel.ι f)

end

section

variable [HasCokernel f]
variable [HasKernel (cokernel.π f)]

/- Definition 12.3.9 (image): the textbook image construction, stated for preadditive categories,
is the canonical owner object `Abelian.image f` with structure morphism `Abelian.image.ι f`. -/
recall Abelian.image
recall Abelian.image.ι

/- Companion bridge: the source-facing image definition is exactly the canonical kernel owner
applied to `cokernel.π f`, with universal property `kernelIsKernel (cokernel.π f)`. -/
#check kernelIsKernel (cokernel.π f)

end

end CategoryTheory

/-! ### Lemma_12_3_10 (from Chap12) -/
namespace CategoryTheory

open Limits

universe v u

section

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable (x y : C) [HasBinaryBiproduct x y]

/- Domain-style sampling for Lemma 12.3.10:
- primary domain: kernels and cokernels arising from the canonical binary biproduct square;
- sampled canonical declarations:
  `biprod.sndKernelFork`,
  `biprod.isKernelSndKernelFork`,
  `biprod.inrCokernelCofork`,
  `biprod.isCokernelInrCokernelFork`;
- owner abstraction: `HasBinaryBiproduct x y`;
- primitive data: the binary biproduct object `x ⊞ y` with structure morphisms
  `biprod.inl`, `biprod.inr`, `biprod.fst`, and `biprod.snd`;
- derived API: the kernel fork of `biprod.snd` and the cokernel cofork of `biprod.inr`,
  together with their universal properties.

Source/core/bridge triage:
- `source-facing`: the textbook statements that, in the direct sum decomposition `x ⊞ y`,
  `biprod.inl` is the kernel of `biprod.snd` and `biprod.fst` is the cokernel of `biprod.inr`;
- `core/canonical`: the mathlib owner declarations `biprod.isKernelSndKernelFork` and
  `biprod.isCokernelInrCokernelFork`;
- `bridge/view`: none is needed here, because the source-facing statements already coincide with
  the owner declarations. -/

/- Lemma 12.3.10 (1): in the direct sum `x ⊞ y` with structure morphisms
`biprod.inl`, `biprod.inr`, `biprod.fst`, and `biprod.snd` as in Lemma `12.3.4`,
the inclusion `biprod.inl : x ⟶ x ⊞ y` is a kernel of the projection
`biprod.snd : x ⊞ y ⟶ y`. This is the canonical mathlib kernel-fork statement. -/
recall biprod.isKernelSndKernelFork

/- Lemma 12.3.10 (2): dually, in the same direct-sum decomposition, the projection
`biprod.fst : x ⊞ y ⟶ x` is a cokernel of the inclusion
`biprod.inr : y ⟶ x ⊞ y`. This is the canonical mathlib cokernel-cofork statement. -/
recall biprod.isCokernelInrCokernelFork

end

end CategoryTheory

/-! ### Lemma_12_3_11 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits Abelian

local notation "coimage" => Abelian.coimage
local notation "image" => Abelian.image

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)

/-
Source/core/bridge triage for Lemma 12.3.11:
- primary domain: kernel/cokernel/coimage/image structure morphisms in a category with zero
  morphisms
- sampled owner declarations: `kernel.ι`, `cokernel.π`, `Abelian.coimage.π`, and
  `Abelian.image.ι`
- source-facing: the canonical kernel, cokernel, coimage, and image structure morphisms are
  mono or epi as appropriate
- core/canonical owner abstraction: the owner objects are the canonical kernel/cokernel/coimage/
  image constructions, and this lemma only uses their structure morphisms
- bridge/view: Definition `12.3.9` already identifies the textbook constructions with these
  owners, while the mono/epi facts themselves are supplied canonically by the upstream
  equalizer/coequalizer instances via typeclass inference
- primitive-vs-derived split: the primitive data are the existence assumptions
  `[HasKernel f]`, `[HasCokernel f]`, `[HasCokernel (kernel.ι f)]`, and
  `[HasKernel (cokernel.π f)]`; the mono/epi assertions are entirely derived from instance
  search, so there is no local wrapper data to keep
-/

section Kernel

variable [HasKernel f]

/- Lemma 12.3.11 (1): if a kernel of `f` exists, then the canonical kernel morphism
`kernel.ι f` is a monomorphism. -/
#check (inferInstance : Mono (kernel.ι f))

end Kernel

section Cokernel

variable [HasCokernel f]

/- Lemma 12.3.11 (2): if a cokernel of `f` exists, then the canonical cokernel morphism
`cokernel.π f` is an epimorphism. -/
#check (inferInstance : Epi (cokernel.π f))

end Cokernel

section Coimage

variable [HasKernel f] [HasCokernel (kernel.ι f)]

/- Lemma 12.3.11 (3): the textbook coimage projection `cokernel.π (kernel.ι f)` is the owner
morphism `coimage.π f`, and it is an epimorphism. -/
#check (inferInstance : Epi (coimage.π f))

end Coimage

section Image

variable [HasCokernel f] [HasKernel (cokernel.π f)]

/- Lemma 12.3.11 (4): the textbook image inclusion `kernel.ι (cokernel.π f)` is the owner
morphism `image.ι f`, and it is a monomorphism. -/
#check (inferInstance : Mono (image.ι f))

end Image

end CategoryTheory

/-! ### Lemma_12_3_12 (from Chap12) -/
universe v u

namespace CategoryTheory

open Limits Abelian

local notation "coimage" => Abelian.coimage
local notation "image" => Abelian.image

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {X Y : C} (f : X ⟶ Y)
variable [HasKernel f] [HasCokernel f] [HasCokernel (kernel.ι f)] [HasKernel (cokernel.π f)]

/-
Source/core/bridge triage for Lemma 12.3.12:
- primary domain: abelian coimage/image factorization in a category with zero morphisms
- sampled owner declarations: `coimage.π`, `image.ι`, `coimageImageComparison`, and
  `coimage_image_factorisation`
- source-facing: uniqueness of the factorization of `f` through its coimage and image
- core/canonical owner: `coimageImageComparison f`
- bridge/view: `coimage_image_factorisation f` identifies the owner morphism with the
  textbook factorization
- primitive data: the existence assumptions for the kernel, cokernel, coimage, and image of `f`
- derived API: the epi/mono instances for `coimage.π f` and `image.ι f`, and the comparison
  factorization equation
-/

/-- Lemma 12.3.12: the canonical morphism `coimageImageComparison f` is the unique
factorization of `f` through its abelian coimage and abelian image. -/
theorem unique_coimage_image_factorization :
    ∃! g : coimage f ⟶ image f,
      coimage.π f ≫ g ≫ image.ι f = f := by
  refine ⟨coimageImageComparison f, coimage_image_factorisation f, ?_⟩
  intro g hg
  apply (cancel_epi (coimage.π f)).1
  apply (cancel_mono (image.ι f)).1
  simpa [Category.assoc] using hg.trans (coimage_image_factorisation f).symm

end CategoryTheory

/-! ### Example_12_3_13 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits
open Abelian.OfCoimageImageComparisonIsIso
open Function OrderDual
open ModuleCat

noncomputable section

universe w v u

namespace CategoryTheory

section Ring

variable (k : Type u) [Ring k]

private abbrev lineObject : ModuleCat k := ModuleCat.of k k

private noncomputable abbrev lineSubobject (S : Submodule k k) :
    Subobject (lineObject k) :=
  (ModuleCat.subobjectModule (lineObject k)).symm S

private theorem lineSubobject_mono {S T : Submodule k k} (h : S ≤ T) :
    lineSubobject k S ≤ lineSubobject k T :=
  (ModuleCat.subobjectModule (lineObject k)).symm.monotone h

private theorem topBotSubmoduleFiltration_antitone {P : ℤ → Prop} [DecidablePred P]
    (hP : Antitone P) :
    Antitone (fun i : ℤ ↦ if P i then (⊤ : Submodule k k) else ⊥) := by
  intro i j hij
  by_cases hj : P j
  · simp [hj, hP hij hj]
  · simp [hj]

/-- The filtered `k`-module `(V, F)` with `V = k` and `F^i V = V` for `i < 0`, `F^i V = 0`
for `i ≥ 0`. -/
private def strictNegativeFilteredLine : FilteredObject (ModuleCat k) :=
  { obj := lineObject k
    filtration :=
      { toFun := fun p ↦ lineSubobject k (if ofDual p < 0 then (⊤ : Submodule k k) else ⊥)
        monotone' := by
          intro p q hpq
          exact lineSubobject_mono k <|
            topBotSubmoduleFiltration_antitone k
              (fun _ _ hij ↦ lt_of_le_of_lt hij) hpq } }

/-- The filtered `k`-module `(W, F)` with `W = k` and `F^i W = W` for `i ≤ 0`, `F^i W = 0`
for `i > 0`. -/
private def nonpositiveFilteredLine : FilteredObject (ModuleCat k) :=
  { obj := lineObject k
    filtration :=
      { toFun := fun p ↦ lineSubobject k (if ofDual p ≤ 0 then (⊤ : Submodule k k) else ⊥)
        monotone' := by
          intro p q hpq
          exact lineSubobject_mono k <|
            topBotSubmoduleFiltration_antitone k (fun _ _ hij ↦ le_trans hij) hpq } }

private theorem strictNegativeFilteredLine_zero :
    (strictNegativeFilteredLine k).filtration 0 = (⊥ : Subobject (lineObject k)) := by
  change lineSubobject k (if (0 : ℤ) < 0 then (⊤ : Submodule k k) else ⊥) = ⊥
  simp

private theorem nonpositiveFilteredLine_zero :
    (nonpositiveFilteredLine k).filtration 0 = (⊤ : Subobject (lineObject k)) := by
  change lineSubobject k (if (0 : ℤ) ≤ 0 then (⊤ : Submodule k k) else ⊥) = ⊤
  simp

/-- The identity map on the underlying line preserves the two filtrations. -/
private theorem strictNegativeToNonpositiveFilteredLine_preserves (i : ℤ) :
    ((nonpositiveFilteredLine k).filtration i).Factors
      (((strictNegativeFilteredLine k).filtration i).arrow ≫ 𝟙 (lineObject k)) := by
  have hle :
      lineSubobject k (if i < 0 then (⊤ : Submodule k k) else ⊥) ≤
        lineSubobject k (if i ≤ 0 then (⊤ : Submodule k k) else ⊥) := by
    refine lineSubobject_mono k ?_
    by_cases hi : i < 0
    · simp [hi, le_of_lt hi]
    · simp [hi]
  simpa using
    Subobject.factors_of_le (((strictNegativeFilteredLine k).filtration i).arrow) hle
      (((strictNegativeFilteredLine k).filtration i).factors_self)

/-- The morphism of filtered lines induced by the identity map on the underlying module `k`.
-/
private def strictNegativeToNonpositiveFilteredLine :
    strictNegativeFilteredLine k ⟶ nonpositiveFilteredLine k where
  hom := 𝟙 (lineObject k)
  preserves := strictNegativeToNonpositiveFilteredLine_preserves k

section Nontrivial

variable [Nontrivial k]

/-- The filtered identity map from the stricter filtration to the looser one is not an
isomorphism. -/
private theorem strictNegativeToNonpositiveFilteredLine_not_iso :
    ¬ IsIso (strictNegativeToNonpositiveFilteredLine k) := by
  let f := strictNegativeToNonpositiveFilteredLine k
  intro hIso
  haveI : IsIso f := by simpa [f] using hIso
  have hComp :
      f.hom ≫ (inv f).hom = 𝟙 (lineObject k) := by
    exact congrArg FilteredObject.Hom.hom (IsIso.hom_inv_id f)
  have hInv :
      (inv f).hom = 𝟙 (lineObject k) := by
    simpa [f, strictNegativeToNonpositiveFilteredLine] using hComp
  have hpres := (inv f).pullback_preserves 0
  have hTopBot : (⊤ : Subobject (lineObject k)) ≤ ⊥ := by
    have hpres' :
        (nonpositiveFilteredLine k).filtration 0 ≤
          (Subobject.pullback (𝟙 (lineObject k))).obj ((strictNegativeFilteredLine k).filtration 0) := by
      simpa [hInv] using hpres
    change lineSubobject k (if (0 : ℤ) ≤ 0 then (⊤ : Submodule k k) else ⊥) ≤
        (Subobject.pullback (𝟙 (lineObject k))).obj
          (lineSubobject k (if (0 : ℤ) < 0 then (⊤ : Submodule k k) else ⊥)) at hpres'
    simpa [Subobject.pullback_id] using hpres'
  have hEq : (⊥ : Subobject (lineObject k)) = ⊤ := top_le_iff.mp hTopBot
  have hSubmoduleEq : (⊥ : Submodule k k) = ⊤ := by
    simpa [lineSubobject] using congrArg (ModuleCat.subobjectModule (lineObject k)) hEq
  have hOneMem : (1 : k) ∈ (⊥ : Submodule k k) := by
    simp [hSubmoduleEq]
  exact (show (1 : k) ≠ 0 from one_ne_zero) (by simp at hOneMem)

/-- The category of filtered `k`-modules is not abelian for any nontrivial ring `k`; it is
witnessed by the identity map on `k` between the filtration `F^i = k` for `i < 0`, `F^i = 0` for
`i ≥ 0` and the filtration `F^i = k` for `i ≤ 0`, `F^i = 0` for `i > 0`, which is mono and epi
but not an isomorphism. -/
theorem filtered_modules_not_abelian :
    ¬ Nonempty (Abelian (FilteredObject (ModuleCat k))) := by
  sorry

end Nontrivial
end Ring

section Field

variable (k : Type u) [Field k]

/-- Example 12.3.13: the category of filtered vector spaces over a field `k` is not abelian; it is
witnessed by the identity map on `k` between the filtration `F^i = k` for `i < 0`, `F^i = 0` for
`i ≥ 0` and the filtration `F^i = k` for `i ≤ 0`, `F^i = 0` for `i > 0`, which is mono and epi
but not an isomorphism. -/
theorem filtered_vector_spaces_not_abelian :
    ¬ Nonempty (Abelian (FilteredObject (ModuleCat k))) :=
  filtered_modules_not_abelian k

end Field

end CategoryTheory
