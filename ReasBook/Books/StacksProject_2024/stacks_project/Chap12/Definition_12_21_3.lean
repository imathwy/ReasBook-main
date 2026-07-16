import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_21_1

-- Declarations for this item will be appended below by the statement pipeline.

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
