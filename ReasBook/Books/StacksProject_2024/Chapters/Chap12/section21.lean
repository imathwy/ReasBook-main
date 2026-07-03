import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_12_21_1 (from Chap12) -/
namespace CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroMorphisms C]

/- Domain-style sampling for Definition 12.21.1:
- primary domain: exact couples and their page-one differential objects in a category with zero
  morphisms;
- sampled canonical declarations in the surrounding owner ecosystem:
  `ShortComplex`,
  `ShortComplex.Exact`,
  `HomologicalComplex C (ComplexShape.refl PUnit)`,
  `HomologicalComplex.sc`;
- best owner abstraction for the page-level differential data: the chapter owner
  `HomologicalComplex C (ComplexShape.refl PUnit)`;
- primitive data: the triangle objects `A`, `E`, the maps `α`, `f`, `g`, the three zero
  composites, and the three exactness assertions;
- derived API: the differential `d = f ≫ g` and the one-object page complex obtained from the
  canonical homological-complex owner;
- source/core/bridge triage:
  `source-facing`: `ExactCouple`;
  `core/canonical`: `ShortComplex` exactness and the owner type
  `HomologicalComplex C (ComplexShape.refl PUnit)`;
  `bridge/view`: `ExactCouple.page`.

The structure `ExactCouple` is the source-facing owner, while the page-level differential object is
only a bridge to the chapter's existing one-object homological-complex owner. -/
/-- Definition 12.21.1: an exact couple consists of objects `A` and `E` with morphisms
`α : A ⟶ A`, `f : E ⟶ A`, and `g : A ⟶ E` such that the three cyclic pairs `f, α`, `g, f`,
and `α, g` are exact. For the textbook abelian-category notion, the ambient abelian hypothesis
is only needed by downstream constructions using images, kernels, and homology, not by this
source-facing owner itself. -/
structure ExactCouple where
  /-- The `A`-object of the exact couple. -/
  A : C
  /-- The `E`-object of the exact couple. -/
  E : C
  /-- The endomorphism `α : A ⟶ A` in the exact-couple triangle. -/
  α : A ⟶ A
  /-- The morphism `f : E ⟶ A` in the exact-couple triangle. -/
  f : E ⟶ A
  /-- The morphism `g : A ⟶ E` in the exact-couple triangle. -/
  g : A ⟶ E
  /-- The composite `f ≫ α` vanishes. -/
  f_comp_α : f ≫ α = 0
  /-- The composite `g ≫ f` vanishes. -/
  g_comp_f : g ≫ f = 0
  /-- The composite `α ≫ g` vanishes. -/
  α_comp_g : α ≫ g = 0
  /-- Exactness of `E ⟶ A ⟶ A`, expressing `ker(α) = im(f)`. -/
  exact_f_α : (ShortComplex.mk f α f_comp_α).Exact
  /-- Exactness of `A ⟶ E ⟶ A`, expressing `ker(f) = im(g)`. -/
  exact_g_f : (ShortComplex.mk g f g_comp_f).Exact
  /-- Exactness of `A ⟶ A ⟶ E`, expressing `ker(g) = im(α)`. -/
  exact_α_g : (ShortComplex.mk α g α_comp_g).Exact

namespace ExactCouple

local notation "ExactCoupleCat" => @ExactCouple C _ _

variable (X : @ExactCouple C _ _)

/-- The differential on the middle object of an exact couple. -/
abbrev d : X.E ⟶ X.E :=
  X.f ≫ X.g

/-- The differential of an exact couple squares to zero. -/
@[simp]
theorem d_comp_d : X.d ≫ X.d = 0 := by
  simpa [d, Category.assoc] using congrArg (fun k ↦ X.f ≫ k ≫ X.g) X.g_comp_f

/-- Bridge/view layer: an exact couple carries the canonical one-object homological complex on its
middle object, with differential `d = f ≫ g`. -/
instance : CoeOut ExactCoupleCat (HomologicalComplex C (ComplexShape.refl PUnit.{1})) where
  coe X :=
    { X := fun _ ↦ X.E
      d := fun _ _ ↦ X.d
      shape := fun _ _ h ↦ False.elim (h rfl)
      d_comp_d' := fun _ _ _ _ _ ↦ X.d_comp_d }

/-- The one-object homological complex carried by the middle object of an exact couple. -/
abbrev page : HomologicalComplex C (ComplexShape.refl PUnit.{1}) :=
  X

end ExactCouple

end

end CategoryTheory

/-! ### Lemma_12_21_2 (from Chap12) -/
open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

-- Proof sketch: the kernel of a composite is characterized by the universal property of the
-- pullback of the second kernel along the first map.
/-- The kernel of a composite `f ≫ g` is the inverse image of `Ker(g)` under `f`. -/
private theorem kernelSubobject_comp_eq_pullback {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    kernelSubobject (f ≫ g) = (Subobject.pullback f).obj (kernelSubobject g) := by
  apply le_antisymm
  · refine Subobject.le_of_comm
      (((Subobject.pullback f).obj (kernelSubobject g)).factorThru (kernelSubobject (f ≫ g)).arrow ?_)
      ?_
    · exact (pullback_factors_iff f (kernelSubobject g) (kernelSubobject (f ≫ g)).arrow).2 <| by
        rw [kernelSubobject_factors_iff, Category.assoc]
        exact kernelSubobject_arrow_comp (f ≫ g)
    · exact Subobject.factorThru_arrow _ _ _
  · exact le_kernelSubobject _ _ <| by
      have hpb := (Subobject.isPullback f (kernelSubobject g)).w
      rw [← reassoc_of% hpb, kernelSubobject_arrow_comp, comp_zero]

namespace ExactCouple

local notation "ExactCoupleCat" => @ExactCouple C _ _

/- Domain-style sampling for Lemma 12.21.2:
- primary domain: exact couples in an abelian category, viewed through the kernel and image
  subobjects of the three exact short complexes and of the page-one differential;
- sampled owner declarations in the immediate chapter/mathlib ecosystem:
  `ExactCouple.d`,
  `ExactCouple.page`,
  `ShortComplex.exact_iff_image_eq_kernel`,
  `ExactCouple.derived`;
- best owner abstraction: the chapter owner `ExactCouple`, with the page-one differential and the
  derived exact couple recovered from `ExactCouple.d`, `ExactCouple.page`, and
  `ExactCouple.derived`;
- primitive data: an exact couple `T` with maps `α`, `f`, `g`;
- derived API in this file: the kernel/image comparisons for `d = f ≫ g` and the canonical recall
  that the derived data are already owned upstream by `ExactCouple.derived`;
- source/core/bridge triage:
  `source-facing`: the textbook identifications in Lemma 12.21.2;
  `core/canonical`: `ExactCouple`, `ShortComplex.exact_iff_image_eq_kernel`,
  `kernelSubobject`, `imageSubobject`, and `ExactCouple.derived`;
  `bridge/view`: the pullback/image descriptions of `kernelSubobject T.d` and
  `imageSubobject T.d`.

This file should therefore expose only the source-facing equalities and reuse the existing exact
couple owners, rather than introducing parallel derived-data wrappers. -/
variable (T : ExactCoupleCat)

-- Proof sketch: exactness of `A --α--> A --g--> E` identifies `imageSubobject α` with
-- `kernelSubobject g` via `ShortComplex.exact_iff_image_eq_kernel`.
/-- The image of `α` agrees with the kernel of `g`. -/
theorem image_alpha_eq_kernel_g :
    imageSubobject T.α = kernelSubobject T.g :=
  (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk T.α T.g T.α_comp_g)).mp T.exact_α_g

-- Proof sketch: exactness of `A --g--> E --f--> A` identifies `imageSubobject g` with
-- `kernelSubobject f`.
/-- The image of `g` agrees with the kernel of `f`. -/
theorem image_g_eq_kernel_f :
    imageSubobject T.g = kernelSubobject T.f :=
  (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk T.g T.f T.g_comp_f)).mp T.exact_g_f

-- Proof sketch: exactness of `E --f--> A --α--> A` identifies `imageSubobject f` with
-- `kernelSubobject α`.
/-- The image of `f` agrees with the kernel of `α`. -/
theorem image_f_eq_kernel_alpha :
    imageSubobject T.f = kernelSubobject T.α :=
  (ShortComplex.exact_iff_image_eq_kernel (ShortComplex.mk T.f T.α T.f_comp_α)).mp T.exact_f_α

-- Proof sketch: identify `Ker(d)` with the pullback of `Ker(g)` along `f` by unraveling the
-- kernel of `d = f ≫ g`.
/-- Lemma 12.21.2 (1): the kernel of `d = f ≫ g` is the inverse image of `Ker(g)` under `f`. -/
theorem kernel_differential_eq_preimage_kernel_g :
    kernelSubobject T.d = (Subobject.pullback T.f).obj (kernelSubobject T.g) :=
  kernelSubobject_comp_eq_pullback T.f T.g

-- Proof sketch: replace `kernelSubobject g` by `imageSubobject α` using exactness of
-- `A --α--> A --g--> E`, then pull back along `f`.
/-- Lemma 12.21.2 (2): the inverse image of `Ker(g)` under `f` equals the inverse image of
`Im(α)` under `f`. -/
theorem preimage_kernel_g_eq_preimage_image_alpha :
    (Subobject.pullback T.f).obj (kernelSubobject T.g) =
      (Subobject.pullback T.f).obj (imageSubobject T.α) :=
  congrArg ((Subobject.pullback T.f).obj) (image_alpha_eq_kernel_g T).symm

-- Proof sketch: the image of `d = f ≫ g` is the image of the restriction of `g` to
-- `imageSubobject f`.
/-- Lemma 12.21.2 (3): the image of `d = f ≫ g` is the image of `g` applied to `Im(f)`. -/
theorem image_differential_eq_image_restricted_g_on_image_f :
    imageSubobject T.d = imageSubobject ((imageSubobject T.f).arrow ≫ T.g) :=
  Limits.imageSubobject_comp_eq_imageSubobject_restriction T.f T.g

-- Proof sketch: replace `imageSubobject f` by `kernelSubobject α` using exactness of
-- `E --f--> A --α--> A`, then compare the induced images under `g`.
/-- Lemma 12.21.2 (4): the image of `g` applied to `Im(f)` equals the image of `g` applied to
`Ker(α)`. -/
theorem image_restricted_g_on_image_f_eq_image_restricted_g_on_kernel_alpha
    :
    imageSubobject ((imageSubobject T.f).arrow ≫ T.g) =
      imageSubobject ((kernelSubobject T.α).arrow ≫ T.g) :=
  congrArg (fun S : Subobject T.A ↦ imageSubobject (S.arrow ≫ T.g)) (image_f_eq_kernel_alpha T)

/- Lemma 12.21.2 (5): the derived data
`(A', E', α', f', g') = (Im(α), Ker(d) / Im(d), α', f', g')`
form an exact couple. In this chapter the owner construction is the canonical declaration
`ExactCouple.derived`, built from `ExactCouple.d` and `ExactCouple.page`. -/
recall ExactCouple.derived

end ExactCouple
end CategoryTheory

/-! ### Definition_12_21_3 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace ExactCouple

local notation "ExactCoupleCat" => @ExactCouple C _ _

/- Domain-style sampling for Definition 12.21.3:
- primary domain: exact couples in an abelian category and the spectral sequence canonically
  attached to their iterated derived couples;
- sampled owner declarations in the immediate chapter/project domain:
  `ExactCouple`,
  `ExactCouple.page`,
  `SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`,
  `ShiftedExactCouple.associatedSpectralSequence`;
- best owner abstraction: the source-facing exact-couple owner together with its canonical
  spectral-sequence construction `ExactCouple.associatedSpectralSequence`;
- primitive data in this file: the derived exact couple `X.derived` and its iterates
  `X.iterateDerived r`;
- derived API in this file: the owner spectral sequence `X.associatedSpectralSequence` and the
  textbook page/object/differential identifications recovered from it;
- source/core/bridge triage:
  `source-facing`: `derived`, `iterateDerived`, `associatedSpectralSequence`;
  `core/canonical`: `SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1`;
  `bridge/view`: `pageSc` and the page/object/differential lemmas.

There is no earlier chapter owner for the ordinary exact-couple spectral sequence beyond this
file itself, so the refinement here keeps the source-facing owner while aligning its public
surface with the canonical owner-style API already used downstream. -/

/-- The short complex underlying the one-object page complex of an exact couple. -/
private noncomputable abbrev pageSc (X : ExactCoupleCat) : ShortComplex C :=
  X.page.sc PUnit.unit

/-- The outer object of the derived exact couple, namely the image of `α`. -/
private abbrev derivedA (X : ExactCoupleCat) : C :=
  image X.α

/-- The middle object of the derived exact couple, namely the homology of the differential on
`E`. -/
private abbrev derivedE (X : ExactCoupleCat) : C :=
  (pageSc X).homology

/-- The endomorphism induced by `α` on its image. -/
private abbrev derivedα (X : ExactCoupleCat) : derivedA X ⟶ derivedA X :=
  image.map ((Arrow.homMk X.α X.α rfl : Arrow.mk X.α ⟶ Arrow.mk X.α))

-- Proof sketch: compose `Abelian.image.ι α ≫ g` with `d = f ≫ g`; the middle factor
-- `g ≫ f` vanishes by the exact-couple axioms, so the composite is zero.
/-- The map `image α ⟶ E` induced by `g` lands in the cycles of the differential `d`. -/
private theorem imageIota_comp_g_comp_d_zero (X : ExactCoupleCat) :
    (image.ι X.α ≫ X.g) ≫ X.d = 0 := by
  simpa [ExactCouple.d, Category.assoc] using
    congrArg (fun k ↦ image.ι X.α ≫ k ≫ X.g) X.g_comp_f

/-- The map from `image α` to the cycles of the page-one differential induced by `g`. -/
private def derivedgCycles (X : ExactCoupleCat) :
    derivedA X ⟶ (pageSc X).cycles :=
  (pageSc X).liftCycles (image.ι X.α ≫ X.g) (imageIota_comp_g_comp_d_zero X)

/-- The map `g' : A' ⟶ E'` in the derived exact couple. -/
private abbrev derivedg (X : ExactCoupleCat) : derivedA X ⟶ derivedE X :=
  derivedgCycles X ≫ (pageSc X).homologyπ

-- Proof sketch: a cycle for `d = f ≫ g` maps under `f` into `ker g = im α`, so the map
-- `cycles(d) ⟶ A` factors canonically through `image α`.
/-- The map from cycles of the page-one differential to `image α` induced by `f`. -/
private noncomputable def derivedfCycles (X : ExactCoupleCat) :
    (pageSc X).cycles ⟶ derivedA X :=
  let hImage := X.exact_α_g.isLimitImage'
  hImage.lift
    (KernelFork.ofι ((pageSc X).iCycles ≫ X.f) (by
      simpa [pageSc, page, d, Category.assoc] using (pageSc X).iCycles_g))

-- Proof sketch: a boundary in the page-one short complex is in the image of `d`; composing with
-- the cycles-to-`image α` map induced by `f` gives zero in `image α`.
/-- The cycles-to-`image α` map induced by `f` vanishes on boundaries. -/
private theorem toCycles_comp_derivedfCycles_zero (X : ExactCoupleCat) :
    (pageSc X).toCycles ≫ derivedfCycles X = 0 := sorry

/-- The map `f' : E' ⟶ A'` in the derived exact couple. -/
private abbrev derivedf (X : ExactCoupleCat) : derivedE X ⟶ derivedA X :=
  (pageSc X).descHomology (derivedfCycles X) (toCycles_comp_derivedfCycles_zero X)

-- Proof sketch: the map `f'` is induced from `f`, while `α'` is induced from `α`; the exactness
-- of the original couple implies the composite descends to zero on homology.
/-- In the derived exact couple, the composite `f' ≫ α'` vanishes. -/
private theorem derivedf_comp_derivedα_zero (X : ExactCoupleCat) :
    derivedf X ≫ derivedα X = 0 := sorry

-- Proof sketch: `α'` is induced by `α` on `image α`, and `g'` is induced by `g`; the original
-- relation `α ≫ g = 0` forces their composite to vanish.
/-- In the derived exact couple, the composite `α' ≫ g'` vanishes. -/
private theorem derivedα_comp_derivedg_zero (X : ExactCoupleCat) :
    derivedα X ≫ derivedg X = 0 := sorry

-- Proof sketch: `g'` lands in cycles and `f'` factors through homology; exactness of the
-- original couple shows that the resulting composite is a boundary, hence zero in `A'`.
/-- In the derived exact couple, the composite `g' ≫ f'` vanishes. -/
private theorem derivedg_comp_derivedf_zero (X : ExactCoupleCat) :
    derivedg X ≫ derivedf X = 0 := sorry

-- Proof sketch: identify `A' = image α` and `E' = H(E, d)`, then use exactness of the original
-- couple together with the universal properties of image and homology to prove exactness at `A'`.
/-- Exactness of the derived couple at the first copy of `A'`. -/
private theorem derived_exact_f_α (X : ExactCoupleCat) :
    (ShortComplex.mk (derivedf X) (derivedα X) (derivedf_comp_derivedα_zero X)).Exact := sorry

-- Proof sketch: exactness at `A'` follows from the original exact couple after passing to the
-- image of `α` and the homology of `d`.
/-- Exactness of the derived couple at the second copy of `A'`. -/
private theorem derived_exact_α_g (X : ExactCoupleCat) :
    (ShortComplex.mk (derivedα X) (derivedg X) (derivedα_comp_derivedg_zero X)).Exact := sorry

-- Proof sketch: exactness at `E'` is the standard description of homology for the differential
-- on `E`, expressed through the induced maps `g'` and `f'`.
/-- Exactness of the derived couple at `E'`. -/
private theorem derived_exact_g_f (X : ExactCoupleCat) :
    (ShortComplex.mk (derivedg X) (derivedf X) (derivedg_comp_derivedf_zero X)).Exact := sorry

/-- The derived exact couple associated to an exact couple. -/
def derived (X : ExactCoupleCat) : ExactCoupleCat where
  A := derivedA X
  E := derivedE X
  α := derivedα X
  f := derivedf X
  g := derivedg X
  f_comp_α := derivedf_comp_derivedα_zero X
  g_comp_f := derivedg_comp_derivedf_zero X
  α_comp_g := derivedα_comp_derivedg_zero X
  exact_f_α := derived_exact_f_α X
  exact_g_f := derived_exact_g_f X
  exact_α_g := derived_exact_α_g X

/-- The `n`-fold iterated derived exact couple. -/
def iterateDerived (X : ExactCoupleCat) : ℕ → ExactCoupleCat
  | 0 => X
  | n + 1 => (iterateDerived X n).derived

/-- Definition 12.21.3: the spectral sequence associated to an exact couple is the
single-object spectral sequence whose page `E_r` is the middle object of the `(r - 1)`-fold
derived exact couple, so `E₁ = E`, `d₁ = d`, `E₂ = E'`, `d₂ = d'`, `E₃ = E''`, `d₃ = d''`,
and so on. -/
noncomputable def associatedSpectralSequence (X : ExactCoupleCat) :
    SpectralSequence C (fun _ ↦ ComplexShape.refl PUnit.{1}) 1 where
  page r hr := match r with
    | Int.ofNat 0 => nomatch hr
    | Int.ofNat (n + 1) => (X.iterateDerived n).page
    | Int.negSucc _ => nomatch hr
  iso r _ _ hrr' hr := match r with
    | Int.ofNat 0 => nomatch hr
    | Int.negSucc _ => nomatch hr
    | Int.ofNat (_ + 1) => match hrr' with
      | rfl => Iso.refl _

-- Proof sketch: unfold `associatedSpectralSequence`; at page index `r + 1` the construction uses
-- the `r`-fold iterated derived couple by definition.
/-- The textbook page `E_{r+1}` of an exact couple is the page complex attached to the `r`-fold
derived exact couple. -/
theorem associatedSpectralSequence_page (X : ExactCoupleCat) (r : ℕ) :
    X.associatedSpectralSequence.page (Nat.succ r : ℤ) = (X.iterateDerived r).page :=
  rfl

-- Proof sketch: evaluate the previous page-complex identification at the unique object
-- `PUnit.unit`.
/-- The textbook page object `E_{r+1}` of an exact couple is the middle object of the `r`-fold
derived exact couple. -/
theorem associatedSpectralSequence_pageObject (X : ExactCoupleCat) (r : ℕ) :
    (X.associatedSpectralSequence.page (Nat.succ r : ℤ)).X PUnit.unit =
      (X.iterateDerived r).E :=
  rfl

-- Proof sketch: evaluate the previous page-complex identification on the unique differential of
-- the one-object complex.
/-- The textbook differential `d_{r+1}` of an exact couple is the differential of the `r`-fold
derived exact couple. -/
theorem associatedSpectralSequence_differential (X : ExactCoupleCat) (r : ℕ) :
    (X.associatedSpectralSequence.page (Nat.succ r : ℤ)).d PUnit.unit PUnit.unit =
      (X.iterateDerived r).d :=
  rfl

end ExactCouple

end CategoryTheory

/-! ### Lemma_12_21_4 (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory
namespace ExactCouple

variable {C : Type u} [Category.{v} C] [Abelian C]

local notation "ExactCoupleCat" => @ExactCouple C _ _

/- Domain-style sampling for Lemma 12.21.4:
- primary domain: the spectral sequence canonically attached to an exact couple, together with the
  source-facing filtration pieces `B_{r+1}` and `Z_{r+1}` on the original `E`-term;
- sampled owner declarations in the immediate chapter/project domain:
  `ExactCouple.associatedSpectralSequence`,
  `SpectralSequence.cycle`,
  `SpectralSequence.boundary`,
  `SpectralSequence.boundary_le_cycle`;
- best owner abstraction: the exact-couple owner `ExactCouple.associatedSpectralSequence`, with
  the recursive page-subquotient data owned by `SpectralSequence`;
- primitive data: the exact couple `X` and the iterates `α^r` of its endomorphism `α`;
- derived API in this file: the source-facing identifications
  `B_{r+1} = g(Ker(α^r))`, `Z_{r+1} = f⁻¹(Im(α^r))`, the monotone filtration chain on `E`, the
  canonical inclusion `B_{r+1} ≤ Z_{r+1}`, the quotient-to-page comparison
  `Z_{r+1} / B_{r+1} ≅ E_{r+1}`, and the representative-level description of the induced
  differential on the actual quotient `Z_{r+1} / B_{r+1}`;
- source/core/bridge triage:
  `source-facing`: the filtration formulas, the chain
  `0 = B₁ ⊆ ⋯ ⊆ B_{r+1} ⊆ ⋯ ⊆ Z_{r+1} ⊆ ⋯ ⊆ Z₁ = E`, and the quotient differential rule in
  Lemma 12.21.4;
  `core/canonical`: `ExactCouple.associatedSpectralSequence` together with the owner
  `SpectralSequence.cycle`, `boundary`, `boundary_le_cycle`, and `cycleToPage`;
  `bridge/view`: the equalities below identifying those owner subobjects with the concrete exact-
  couple image/kernel formulas, and the quotient-to-page map built from those identifications.

This item is therefore source-facing, not a pure recall: it should reuse the canonical owner
spectral sequence while keeping the textbook `B_{r+1}`/`Z_{r+1}` formulas, filtration chain, and
quotient description explicit. -/

/-- The `r`-fold iterate `α^r` of the endomorphism `α` of an exact couple. -/
def alphaIterate (X : ExactCoupleCat) (r : ℕ) : X.A ⟶ X.A :=
  End.asHom ((End.of X.α) ^ r)

/-- The positive owner page index corresponding to the source-facing stage `r + 1`. -/
private abbrev ownerPageIndex (r : ℕ) : ℕ+ :=
  Nat.succPNat r

/-- The owner cycle piece on page `r + 1`, viewed inside the original `E`-term. -/
private abbrev ownerCyclesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  X.associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r)

/-- The owner boundary piece on page `r + 1`, viewed inside the original `E`-term. -/
private abbrev ownerBoundariesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  X.associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r)

/-- The source-facing cycle piece `Z_{r + 1} = f⁻¹(Im(α^r))` inside the original `E`-term. -/
abbrev cyclesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  (Subobject.pullback X.f).obj (imageSubobject (X.alphaIterate r))

/-- The source-facing boundary piece `B_{r + 1} = g(Ker(α^r))` inside the original `E`-term. -/
abbrev boundariesSubobject (X : ExactCoupleCat) (r : ℕ) : Subobject X.E :=
  imageSubobject ((kernelSubobject (X.alphaIterate r)).arrow ≫ X.g)

/-- Textbook-style notation `Z_(r)(X)` for the source-facing cycle piece `Z_{r + 1}` inside the
original `E`-term. -/
notation:max "Z_(" r ")(" X:max ")" =>
  CategoryTheory.ExactCouple.cyclesSubobject X r

/-- Textbook-style notation `B_(r)(X)` for the source-facing boundary piece `B_{r + 1}` inside
the original `E`-term. -/
notation:max "B_(" r ")(" X:max ")" =>
  CategoryTheory.ExactCouple.boundariesSubobject X r

/-- Lemma 12.21.4: in the spectral sequence attached to an exact couple, the boundary piece
`B_{r + 1}` on the original `E`-term is `g(Ker(α^r))`. -/
theorem associatedSpectralSequence_boundary_eq_image_kernel_alphaIterate
    (X : ExactCoupleCat) (r : ℕ+) :
    X.associatedSpectralSequence.boundary PUnit.unit r = B_(r.natPred)(X) :=
  sorry

/-- Lemma 12.21.4: in the spectral sequence attached to an exact couple, the cycle piece
`Z_{r + 1}` on the original `E`-term is `f⁻¹(Im(α^r))`. -/
theorem associatedSpectralSequence_cycle_eq_preimage_image_alphaIterate
    (X : ExactCoupleCat) (r : ℕ+) :
    X.associatedSpectralSequence.cycle PUnit.unit r = Z_(r.natPred)(X) :=
  sorry

/-- Lemma 12.21.4: the first boundary piece is zero, i.e. `B₁ = 0`. -/
theorem boundariesSubobject_zero (X : ExactCoupleCat) :
    B_(0)(X) = (⊥ : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the first cycle piece is all of `E`, i.e. `Z₁ = E`. -/
theorem cyclesSubobject_zero (X : ExactCoupleCat) :
    Z_(0)(X) = (⊤ : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the boundary pieces form an increasing filtration
`B_{r + 1} ⊆ B_{s + 1}` for `r ≤ s`. -/
theorem boundariesSubobject_mono (X : ExactCoupleCat) {r s : ℕ} (hrs : r ≤ s) :
    (B_(r)(X) : Subobject X.E) ≤ (B_(s)(X) : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the cycle pieces form a decreasing filtration
`Z_{s + 1} ⊆ Z_{r + 1}` for `r ≤ s`. -/
theorem cyclesSubobject_antitone (X : ExactCoupleCat) {r s : ℕ} (hrs : r ≤ s) :
    (Z_(s)(X) : Subobject X.E) ≤ (Z_(r)(X) : Subobject X.E) :=
  sorry

/-- Lemma 12.21.4: the source-facing boundary piece `B_{r + 1}` is contained in the
source-facing cycle piece `Z_{r + 1}`. -/
theorem boundariesSubobject_le_cyclesSubobject (X : ExactCoupleCat) (r : ℕ) :
    (B_(r)(X) : Subobject X.E) ≤ (Z_(r)(X) : Subobject X.E) :=
  by
    have hBoundaries :
        X.associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r) =
          B_(r)(X) := by
      simpa [ownerPageIndex] using
        associatedSpectralSequence_boundary_eq_image_kernel_alphaIterate X (ownerPageIndex r)
    have hCycles :
        X.associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r) =
          Z_(r)(X) := by
      simpa [ownerPageIndex] using
        associatedSpectralSequence_cycle_eq_preimage_image_alphaIterate X (ownerPageIndex r)
    simpa [hBoundaries, hCycles] using
      X.associatedSpectralSequence.boundary_le_cycle PUnit.unit (ownerPageIndex r)

/-- The canonical inclusion `B_{r + 1} ⟶ Z_{r + 1}` for the source-facing filtration pieces. -/
private abbrev boundariesToCycles (X : ExactCoupleCat) (r : ℕ) :
    (B_(r)(X) : C) ⟶ (Z_(r)(X) : C) :=
  Subobject.ofLE
    (X.boundariesSubobject r)
    (X.cyclesSubobject r)
    (boundariesSubobject_le_cyclesSubobject X r)

/-- The literal source-facing quotient `Z_{r + 1} / B_{r + 1}`. -/
abbrev pageSubquotient (X : ExactCoupleCat) (r : ℕ) : C :=
  cokernel (X.boundariesToCycles r)

/-- The canonical page object `E_{r+1}` of the owner spectral sequence. -/
private noncomputable abbrev ownerPageObjectIso (X : ExactCoupleCat) (r : ℕ) :
    X.associatedSpectralSequence.pageObject PUnit.unit (ownerPageIndex r) ≅ (X.iterateDerived r).E :=
  eqToIso (by simpa using X.associatedSpectralSequence_pageObject r)

/-- The canonical inclusion of the owner boundary piece into the owner cycle piece on page
`r + 1`. -/
private abbrev ownerBoundariesToCycles (X : ExactCoupleCat) (r : ℕ) :
    (X.ownerBoundariesSubobject r : C) ⟶ (X.ownerCyclesSubobject r : C) :=
  Subobject.ofLE
    (X.ownerBoundariesSubobject r)
    (X.ownerCyclesSubobject r)
    (X.associatedSpectralSequence.boundary_le_cycle PUnit.unit (ownerPageIndex r))

/-- The literal source-facing quotient `Z_{r + 1} / B_{r + 1}` identifies canonically with the
owner quotient `Z_{r + 1} / B_{r + 1}` coming from `SpectralSequence.pageQuotientToPage`. -/
private noncomputable def pageSubquotientToOwnerPageQuotient (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ≅ cokernel (X.ownerBoundariesToCycles r) :=
  cokernel.mapIso
    (X.boundariesToCycles r)
    (X.ownerBoundariesToCycles r)
    (Subobject.isoOfEq _ _
      (associatedSpectralSequence_boundary_eq_image_kernel_alphaIterate X (ownerPageIndex r)).symm)
    (Subobject.isoOfEq _ _
      (associatedSpectralSequence_cycle_eq_preimage_image_alphaIterate X (ownerPageIndex r)).symm)
    (by
      simp [boundariesToCycles, ownerBoundariesToCycles, Subobject.ofLE_comp_ofLE])

/-- The canonical map from the source-facing quotient `Z_{r + 1} / B_{r + 1}` to the page
object `E_{r + 1}`. -/
private noncomputable def ownerPageQuotientToPageIso (X : ExactCoupleCat) (r : ℕ) :
    cokernel (X.ownerBoundariesToCycles r) ≅
      X.associatedSpectralSequence.pageObject PUnit.unit (ownerPageIndex r) := by
  simpa [ownerBoundariesToCycles, ownerBoundariesSubobject, ownerCyclesSubobject] using
    (by
      letI :
          IsIso (X.associatedSpectralSequence.pageQuotientToPage PUnit.unit (ownerPageIndex r)) :=
        by
          simpa using
            (SpectralSequence.pageQuotientToPage_isIso
              X.associatedSpectralSequence PUnit.unit (ownerPageIndex r))
      exact asIso (X.associatedSpectralSequence.pageQuotientToPage PUnit.unit (ownerPageIndex r)) :
        cokernel
          (Subobject.ofLE
            (X.associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r))
            (X.associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r))
            (X.associatedSpectralSequence.boundary_le_cycle PUnit.unit (ownerPageIndex r))) ≅
          X.associatedSpectralSequence.pageObject PUnit.unit (ownerPageIndex r))

/-- The canonical map from the source-facing quotient `Z_{r + 1} / B_{r + 1}` to the page
object `E_{r + 1}`. -/
private noncomputable def pageSubquotientToPageIso (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ≅ (X.iterateDerived r).E := by
  exact
    X.pageSubquotientToOwnerPageQuotient r ≪≫
      X.ownerPageQuotientToPageIso r ≪≫
        X.ownerPageObjectIso r

/-- The canonical map from the source-facing quotient `Z_{r + 1} / B_{r + 1}` to the page
object `E_{r + 1}`. -/
noncomputable def pageSubquotientToPage (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ⟶ (X.iterateDerived r).E :=
  (X.pageSubquotientToPageIso r).hom

/-- The canonical map `Z_{r + 1} / B_{r + 1} ⟶ E_{r + 1}` is an isomorphism. -/
theorem pageSubquotientToPage_isIso (X : ExactCoupleCat) (r : ℕ) :
    IsIso (X.pageSubquotientToPage r) :=
  by
    change IsIso (X.pageSubquotientToPageIso r).hom
    infer_instance

/-- The differential on the source-facing quotient `Z_{r + 1} / B_{r + 1}`, transported from the
owner page differential along the canonical comparison with `E_{r + 1}`. -/
noncomputable def pageSubquotientDifferential (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotient r ⟶ X.pageSubquotient r :=
  letI : IsIso (X.pageSubquotientToPage r) := pageSubquotientToPage_isIso X r
  X.pageSubquotientToPage r ≫ (X.iterateDerived r).d ≫ inv (X.pageSubquotientToPage r)

/-- The source-facing quotient differential agrees with the owner differential after the canonical
comparison `Z_{r + 1} / B_{r + 1} ≅ E_{r + 1}`. -/
theorem pageSubquotientDifferential_comm (X : ExactCoupleCat) (r : ℕ) :
    X.pageSubquotientDifferential r ≫ X.pageSubquotientToPage r =
      X.pageSubquotientToPage r ≫ (X.iterateDerived r).d :=
  sorry

/-- Lemma 12.21.4: on the source-facing quotient presentation
`E_{r + 1} = Z_(r)(X) / B_(r)(X)` (that is, `Z_{r + 1} / B_{r + 1}`), the differential sends the
class of a representative `x` to the class of `g ∘ y` whenever `f ∘ x = α^r ∘ y`. -/
theorem associatedSpectralSequence_differential_eq_on_representatives
    (X : ExactCoupleCat) {T : C} (r : ℕ)
    (x : T ⟶ (Z_(r)(X) : C))
    (y : T ⟶ X.A)
    (hy : x ≫ (Z_(r)(X)).arrow ≫ X.f = y ≫ X.alphaIterate r) :
    ∃ gy : T ⟶ (Z_(r)(X) : C),
      gy ≫ (Z_(r)(X)).arrow = y ≫ X.g ∧
        x ≫ cokernel.π (X.boundariesToCycles r) ≫ X.pageSubquotientDifferential r =
          gy ≫ cokernel.π (X.boundariesToCycles r) :=
  sorry

end ExactCouple
end CategoryTheory

/-! ### Remark_12_21_5_Variant (from Chap12) -/
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

variable [HasZeroMorphisms C]

/- Domain-style sampling for Remark 12.21.5 (Variant):
- primary domain: shifted exact couples and the shifted spectral sequences canonically attached to
  them;
- sampled owner declarations in the immediate project domain:
  `ShiftedDifferentialObject`,
  `ShiftedDifferentialObject.shortComplex`,
  `ShiftedSpectralSequence`,
  `ShiftedSpectralSequence.toSpectralSequence`;
- best owner abstraction: the chapter owner `ShiftedSpectralSequence`;
- primitive data: the source-facing shifted exact-couple objects `A`, `E`, the translated outer
  map `T A ⟶ A`, the maps `f`, `g`, the three vanishing composites, and the three exactness
  assertions;
- derived API: the adjoint form `α`, the page-one shifted differential object, the derived shifted
  exact couple, the recursive pages `iterateDerived`, and the associated shifted spectral sequence;
- source/core/bridge triage:
  `source-facing`: `ShiftedExactCouple`;
  `core/canonical`: `ShiftedSpectralSequence` and `ShiftedDifferentialObject`;
  `bridge/view`: `ShiftedExactCouple.d`, `ShiftedExactCouple.α`, the coercion to
  `ShiftedDifferentialObject`, and the page-identification lemmas for
  `ShiftedExactCouple.associatedSpectralSequence`.

The owner in this file is therefore the shifted exact couple itself; the shifted differential
object and the shifted spectral sequence are canonical downstream views derived from that source
data. -/
/-- Remark 12.21.5 (Variant): for shift autoequivalences `S` and `T`, a variant exact couple
consists of objects `A` and `E`, the intrinsic comparison map `T A ⟶ A` of the exact sequence
`T E ⟶ T A ⟶ A ⟶ S E ⟶ S A`, together with `f : E ⟶ A` and `g : A ⟶ S E`. The source-facing
map `α : A ⟶ T⁻¹ A` is recovered canonically as the adjoint transpose of `tAlpha`. As in
Definition 12.21.1, the ambient abelian hypothesis is only needed later for the derived/homology
constructions, not for this source-facing owner itself. -/
structure ShiftedExactCouple (S T : C ≌ C) where
  /-- The `A`-object of the shifted exact couple. -/
  A : C
  /-- The `E`-object of the shifted exact couple. -/
  E : C
  /-- The translated morphism `T A ⟶ A` in the exact-couple sequence. -/
  tAlpha : T.functor.obj A ⟶ A
  /-- The morphism `f : E ⟶ A`. -/
  f : E ⟶ A
  /-- The morphism `g : A ⟶ S E`. -/
  g : A ⟶ S.functor.obj E
  /-- The composite `T f` followed by `T A ⟶ A` vanishes. -/
  Tf_comp_tAlpha : T.functor.map f ≫ tAlpha = 0
  /-- The composite `T A ⟶ A ⟶ S E` vanishes. -/
  tAlpha_comp_g : tAlpha ≫ g = 0
  /-- The composite `A ⟶ S E ⟶ S A` vanishes. -/
  g_comp_Sf : g ≫ S.functor.map f = 0
  /-- Exactness of `T E ⟶ T A ⟶ A`. -/
  exact_Tf_tAlpha :
    (ShortComplex.mk (T.functor.map f) tAlpha Tf_comp_tAlpha).Exact
  /-- Exactness of `T A ⟶ A ⟶ S E`. -/
  exact_tAlpha_g :
    (ShortComplex.mk tAlpha g tAlpha_comp_g).Exact
  /-- Exactness of `A ⟶ S E ⟶ S A`. -/
  exact_g_Sf :
    (ShortComplex.mk g (S.functor.map f) g_comp_Sf).Exact

end

section

variable [Abelian C]

namespace ShiftedExactCouple

variable {S T : C ≌ C} (X : ShiftedExactCouple S T)

/-- The shift on the `r`-th page of the spectral sequence associated to a shifted exact couple:
it is `S` on page `1` and is obtained by precomposing by `T` at each successive page, giving
`T^(r - 1) ∘ S`. -/
def pageShift (S T : C ≌ C) (r : ℕ+) : C ≌ C :=
  Nat.rec S (fun _ e ↦ e.trans T) r.natPred

/-- The page-one differential on the middle object of a shifted exact couple. -/
abbrev d : X.E ⟶ S.functor.obj X.E :=
  X.f ≫ X.g

/-- The source-facing adjoint form `α : A ⟶ T⁻¹ A` of the translated map `T A ⟶ A`. -/
abbrev α : X.A ⟶ T.inverse.obj X.A :=
  (T.toAdjunction.homEquiv X.A X.A) X.tAlpha

/-- A shifted exact couple determines the page-one shifted differential object `E ⟶ S E`. -/
instance : CoeOut (ShiftedExactCouple S T) (ShiftedDifferentialObject S.functor) where
  coe X :=
    { obj := X.E
      d := X.d
      d_squared := by
        simpa [Category.assoc] using
          congrArg (fun k ↦ X.f ≫ k ≫ S.functor.map X.g) X.g_comp_Sf }

end ShiftedExactCouple

namespace ShiftedExactCouple

variable {S T : C ≌ C} (X : ShiftedExactCouple S T)

/-- The page-one shifted differential object carried by a shifted exact couple. -/
private abbrev page : ShiftedDifferentialObject S.functor :=
  X

/-- The outer object `A'` of the derived shifted exact couple. -/
private abbrev derivedA : C :=
  image X.tAlpha

/-- The middle object `E'` of the derived shifted exact couple. -/
private abbrev derivedE : C :=
  X.page.homology

/-- The short complex attached to the underlying shifted differential object. -/
private noncomputable abbrev pageSc : ShortComplex C :=
  X.page.shortComplex

/-- The translated outer map `T A' ⟶ A'` of the derived shifted exact couple. -/
private noncomputable abbrev derivedTAlpha : T.functor.obj X.derivedA ⟶ X.derivedA :=
  (PreservesImage.iso T.functor X.tAlpha).inv ≫
    image.map (Arrow.homMk' _ _ rfl)

-- Proof sketch: a cycle `z : Z₁ ⟶ E` satisfies `z ≫ f ≫ g = 0`, so `z ≫ f` lands in
-- `ker(g) = im(TA ⟶ A)` and therefore factors canonically through `A' = image(tAlpha)`.
/-- The map from cycles of the page-one differential to `A'` induced by `f`. -/
private noncomputable def derivedfCycles : X.pageSc.cycles ⟶ X.derivedA :=
  let hImage := X.exact_tAlpha_g.isLimitImage'
  hImage.lift
    (KernelFork.ofι (X.pageSc.iCycles ≫ X.f) (by
      simpa [ShiftedDifferentialObject.shortComplex, ShiftedDifferentialObject.homology,
        shiftedPageShortComplex, Category.assoc] using
          X.pageSc.iCycles_g))

-- Proof sketch: a boundary in `cycles(d₁)` is represented by the previous differential
-- `S⁻¹E ⟶ E`; after composing with `f`, exactness identifies the result with zero in `A'`.
/-- The cycles-to-`A'` map induced by `f` vanishes on boundaries. -/
private theorem toCycles_comp_derivedfCycles_zero :
    X.pageSc.toCycles ≫ X.derivedfCycles = 0 := sorry

/-- The map `f' : E' ⟶ A'` in the derived shifted exact couple. -/
private noncomputable abbrev derivedf : X.derivedE ⟶ X.derivedA :=
  X.pageSc.descHomology X.derivedfCycles X.toCycles_comp_derivedfCycles_zero

/-- The `(TS)`-shifted page-one short complex whose homology is `(TS)E'`. -/
private noncomputable abbrev derivedgPageSc : ShortComplex C :=
  (S.trans T).functor.mapShortComplex.obj X.pageSc

-- Proof sketch: `g : A ⟶ SE` followed by `S(d₁)` is zero because
-- `d₁ = f ≫ g` and the exact-couple relation `g ≫ S(f) = 0` forces
-- `g ≫ S(f) ≫ S(g) = 0`; applying `T` preserves this vanishing.
/-- The map `T(g) : T A ⟶ TS(E)` lands in the cycles of the `(TS)`-shifted page-one complex. -/
private theorem derivedgFromTA_comp_d_zero :
    T.functor.map X.g ≫ X.derivedgPageSc.g = 0 := sorry

/-- The map from `T A` to the cycles of the `(TS)`-shifted page-one complex induced by `g`. -/
private noncomputable def derivedgCycles :
    T.functor.obj X.A ⟶ X.derivedgPageSc.cycles :=
  X.derivedgPageSc.liftCycles (T.functor.map X.g) X.derivedgFromTA_comp_d_zero

/-- The homology-class map `T A ⟶ (TS)E'` induced by `T(g)`. -/
private noncomputable abbrev derivedgFromTA :
    T.functor.obj X.A ⟶ (S.trans T).functor.obj X.derivedE :=
  X.derivedgCycles ≫ X.derivedgPageSc.homologyπ ≫ (X.pageSc.mapHomologyIso (S.trans T).functor).hom

-- Proof sketch: on `T(E)`, the map `T(g)` represents the differential of the `(TS)`-shifted
-- page-one complex, hence its class in homology vanishes; exactness identifies `A'` as the
-- cokernel of `T(f)`.
/-- The homology-class map induced by `T(g)` vanishes on `T(f)`, so it descends to `A'`. -/
private theorem Tf_comp_derivedgFromTA_zero :
    T.functor.map X.f ≫ X.derivedgFromTA = 0 := sorry

/-- The canonical connecting map in the derived shifted exact couple. -/
private noncomputable def derivedg : X.derivedA ⟶ (S.trans T).functor.obj X.derivedE :=
  let hImage := X.exact_Tf_tAlpha.isColimitImage
  hImage.desc (CokernelCofork.ofπ X.derivedgFromTA X.Tf_comp_derivedgFromTA_zero)

-- Proof sketch: `T(f')` is induced from `f` on the page-one homology and `α'` is adjoint to the
-- translated outer map on `A'`; the exactness of the original couple forces the composite to
-- vanish in the derived exact couple.
/-- In the derived shifted exact couple, the composite `T(f') ≫ Tα'` vanishes. -/
private theorem derived_Tf_comp_tAlpha_zero :
    T.functor.map X.derivedf ≫ X.derivedTAlpha = 0 := sorry

-- Proof sketch: the derived `α'` and `g'` encode the next translated connecting morphism, whose
-- composite vanishes by construction of the derived exact couple.
/-- In the derived shifted exact couple, the composite `T A' ⟶ A' ⟶ (TS) E'` vanishes. -/
private theorem derived_tAlpha_comp_derivedg_zero :
    X.derivedTAlpha ≫ X.derivedg = 0 := sorry

-- Proof sketch: `g'` lands in the next page and `f'` is induced from boundaries, so the
-- resulting composite is zero in the derived exact couple.
/-- In the derived shifted exact couple, the composite `g' ≫ TS(f')` vanishes. -/
private theorem derivedg_comp_TSf_zero :
    X.derivedg ≫ (S.trans T).functor.map X.derivedf = 0 := sorry

-- Proof sketch: identify `A'` with the image of `T A ⟶ A` and use the original exactness after
-- passage to the derived page-one homology.
/-- Exactness of the derived shifted exact couple at `T A' ⟶ A'`. -/
private theorem derived_exact_Tf_tAlpha :
    (ShortComplex.mk (T.functor.map X.derivedf) X.derivedTAlpha
      X.derived_Tf_comp_tAlpha_zero).Exact := sorry

-- Proof sketch: this is the central exactness statement for the derived couple obtained from the
-- original exact couple by passing to the page-one homology.
/-- Exactness of the derived shifted exact couple at `A' ⟶ (TS) E'`. -/
private theorem derived_exact_tAlpha_g :
    (ShortComplex.mk X.derivedTAlpha X.derivedg
      X.derived_tAlpha_comp_derivedg_zero).Exact := sorry

-- Proof sketch: the image of the connecting morphism in the derived couple is the kernel of the
-- next `TS(f')`, as in the standard derived exact-couple construction.
/-- Exactness of the derived shifted exact couple at `(TS) E' ⟶ (TS) A'`. -/
private theorem derived_exact_g_TSf :
    (ShortComplex.mk X.derivedg ((S.trans T).functor.map X.derivedf)
      X.derivedg_comp_TSf_zero).Exact := sorry

/-- Remark 12.21.5 (Variant): the derived shifted exact couple attached to `X`. Its outer object
is the image of `T A ⟶ A`, its middle object is the homology of the page-one differential
`E ⟶ S E`, and its page shift is `T ∘ S`. -/
def derived : ShiftedExactCouple (S.trans T) T where
  A := X.derivedA
  E := X.derivedE
  tAlpha := X.derivedTAlpha
  f := X.derivedf
  g := X.derivedg
  Tf_comp_tAlpha := X.derived_Tf_comp_tAlpha_zero
  tAlpha_comp_g := X.derived_tAlpha_comp_derivedg_zero
  g_comp_Sf := X.derivedg_comp_TSf_zero
  exact_Tf_tAlpha := X.derived_exact_Tf_tAlpha
  exact_tAlpha_g := X.derived_exact_tAlpha_g
  exact_g_Sf := X.derived_exact_g_TSf

/-- The `n`-fold iterated derived shifted exact couple. The page-one differential of
`iterateDerived X n` is the source-facing differential on the page `E_{n+1}`. -/
def iterateDerived (X : ShiftedExactCouple S T) :
    (n : ℕ) →
      ShiftedExactCouple (pageShift S T ⟨n + 1, Nat.succ_pos _⟩) T
  | 0 => X
  | n + 1 => derived (iterateDerived X n)

/-- Remark 12.21.5 (Variant): a shifted exact couple yields a shifted spectral sequence whose
page shifts are `T^(r - 1) ∘ S`, whose first page is `E`, and whose second page is the homology
`Ker(d₁) / Im(S⁻¹ d₁)` of the induced page-one differential. -/
noncomputable def associatedSpectralSequence (X : ShiftedExactCouple S T) :
    ShiftedSpectralSequence (pageShift S T) :=
  { page := fun
      | ⟨n + 1, _⟩ => X.iterateDerived n
    iso := fun
      | ⟨n + 1, _⟩ => Iso.refl (X.iterateDerived (n + 1)).E }

/-- The textbook page `E_{r+1}` of the shifted spectral sequence associated to `X` is the
page-one shifted differential object carried by the `r`-fold derived shifted exact couple. -/
theorem associatedSpectralSequence_page (X : ShiftedExactCouple S T) (r : ℕ) :
    X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩ = X.iterateDerived r :=
  rfl

/-- The textbook page object `E_{r+1}` of the shifted spectral sequence associated to `X` is the
middle object of the `r`-fold derived shifted exact couple. -/
theorem associatedSpectralSequence_pageObject (X : ShiftedExactCouple S T) (r : ℕ) :
    (X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩).obj = (X.iterateDerived r).E :=
  rfl

/-- The textbook differential `d_{r+1}` of the shifted spectral sequence associated to `X` is the
page-one differential of the `r`-fold derived shifted exact couple. -/
theorem associatedSpectralSequence_differential (X : ShiftedExactCouple S T) (r : ℕ) :
    (X.associatedSpectralSequence.page ⟨r + 1, Nat.succ_pos _⟩).d = (X.iterateDerived r).d :=
  rfl

end ShiftedExactCouple

end

end CategoryTheory
