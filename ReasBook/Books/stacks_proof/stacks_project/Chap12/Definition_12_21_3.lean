import Mathlib
import StacksProject_2024.Chap12.Definition_12_21_1

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

-- Proof sketch: a cycle for `d = f ≫ g` maps under `f` into `ker g = im α`, so the map
-- `cycles(d) ⟶ A` factors canonically through `image α`.
/-- Helper for Chap12 Definition 12 21 3: the composite of the page-one cycles inclusion with
`f` lands in `ker g`. -/
private theorem pageSc_iCycles_comp_f_comp_g_zero (X : ExactCoupleCat) :
    ((pageSc X).iCycles ≫ X.f) ≫ X.g = 0 := by
  -- The cycle inclusion lands in the kernel of the page-one differential `d = f ≫ g`.
  simpa [pageSc, page, d, Category.assoc] using (pageSc X).iCycles_g

/-- The map from cycles of the page-one differential to `image α` induced by `f`. -/
private noncomputable def derivedfCycles (X : ExactCoupleCat) :
    (pageSc X).cycles ⟶ derivedA X :=
  let hImage := X.exact_α_g.isLimitImage'
  hImage.lift
    (KernelFork.ofι ((pageSc X).iCycles ≫ X.f) (pageSc_iCycles_comp_f_comp_g_zero X))

/-- Helper for Chap12 Definition 12 21 3: the cycles-to-`image α` map induced by `f` agrees with
the ambient morphism `iCycles ≫ f` after postcomposition with the image inclusion. -/
private theorem derivedfCycles_comp_image_iota (X : ExactCoupleCat) :
    derivedfCycles X ≫ image.ι X.α = (pageSc X).iCycles ≫ X.f := by
  -- This is the defining computation rule for the lift through `image α`.
  simp only [derivedfCycles]
  erw [Fork.IsLimit.lift_ι]
  rfl

-- Proof sketch: a boundary in the page-one short complex is in the image of `d`; composing with
-- the cycles-to-`image α` map induced by `f` gives zero in `image α`.
/-- The cycles-to-`image α` map induced by `f` vanishes on boundaries. -/
private theorem toCycles_comp_derivedfCycles_zero (X : ExactCoupleCat) :
    (pageSc X).toCycles ≫ derivedfCycles X = 0 := by
  -- Compare after the mono `image.ι α`, where the boundary-to-cycles map becomes `d ≫ f`.
  apply (cancel_mono (image.ι X.α)).1
  rw [Category.assoc, derivedfCycles_comp_image_iota, ← Category.assoc, ShortComplex.toCycles_i]
  -- The page-one differential is `f ≫ g`, so `d ≫ f = f ≫ (g ≫ f) = 0`.
  rw [zero_comp]
  simpa [pageSc, page, ExactCouple.d, Category.assoc] using
    congrArg (fun k ↦ X.f ≫ k) X.g_comp_f

/-- The map `f' : E' ⟶ A'` in the derived exact couple. -/
private abbrev derivedf (X : ExactCoupleCat) : derivedE X ⟶ derivedA X :=
  (pageSc X).descHomology (derivedfCycles X) (toCycles_comp_derivedfCycles_zero X)

/-- Helper for Chap12 Definition 12 21 3: the image inclusion of `α` is killed by `g`. -/
private theorem image_iota_comp_g_zero (X : ExactCoupleCat) :
    image.ι X.α ≫ X.g = 0 := by
  -- Cancel the epi `factorThruImage α` from the defining relation `α ≫ g = 0`.
  apply (cancel_epi (factorThruImage X.α)).1
  simpa [Category.assoc] using X.α_comp_g

/-- Helper for Chap12 Definition 12 21 3: the induced endomorphism on `image α` agrees with the
ambient endomorphism `α` after postcomposition with the image inclusion. -/
private theorem derivedα_comp_image_iota (X : ExactCoupleCat) :
    derivedα X ≫ image.ι X.α = image.ι X.α ≫ X.α := by
  -- This is the standard image-map computation for the square `(α, α)`.
  simpa using
    (image.map_ι (sq := (Arrow.homMk X.α X.α rfl : Arrow.mk X.α ⟶ Arrow.mk X.α)))

/-- Helper for Chap12 Definition 12 21 3: the source-level map `g` is a cycle for the page-one
differential `d = f ≫ g`. -/
private theorem g_comp_d_zero (X : ExactCoupleCat) :
    X.g ≫ X.d = 0 := by
  -- This is exactly `g ≫ f ≫ g = 0`.
  simpa [ExactCouple.d, Category.assoc] using congrArg (fun k ↦ k ≫ X.g) X.g_comp_f

/-- Helper for Chap12 Definition 12 21 3: the source object `A` maps to page-one homology by
taking the homology class of `g`. -/
private noncomputable abbrev derivedgFromA (X : ExactCoupleCat) :
    X.A ⟶ derivedE X :=
  (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫ (pageSc X).homologyπ

/-- Helper for Chap12 Definition 12 21 3: the source-level homology class of `g` vanishes on the
image of `f`, so it descends through `factorThruImage α`. -/
private theorem f_comp_derivedgFromA_zero (X : ExactCoupleCat) :
    X.f ≫ derivedgFromA X = 0 := by
  -- Precomposing a cycle lift is the boundary cycle for `d = f ≫ g`.
  have hboundary :
      X.f ≫ (pageSc X).liftCycles X.g (g_comp_d_zero X) =
        (pageSc X).liftCycles (X.f ≫ X.g)
          (by
            simpa [pageSc, page, ExactCouple.d, Category.assoc] using
              congrArg (fun k ↦ X.f ≫ k) (g_comp_d_zero X)) := by
    simpa [Category.assoc] using
      (ShortComplex.comp_liftCycles (S := pageSc X)
        (k := X.g) (hk := g_comp_d_zero X) (α := X.f))
  -- The boundary class of `d` is zero in homology.
  calc
    X.f ≫ derivedgFromA X =
        X.f ≫ (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫ (pageSc X).homologyπ := by
          simp [derivedgFromA]
    _ =
        (pageSc X).liftCycles (X.f ≫ X.g)
          (by
            simpa [pageSc, page, ExactCouple.d, Category.assoc] using
              congrArg (fun k ↦ X.f ≫ k) (g_comp_d_zero X)) ≫
          (pageSc X).homologyπ := by
            rw [← Category.assoc, hboundary]
    _ = 0 := by
          simpa [pageSc, page, ExactCouple.d, Category.assoc] using
            (ShortComplex.liftCycles_homologyπ_eq_zero_of_boundary (S := pageSc X)
              (k := X.f ≫ X.g) (x := 𝟙 X.E)
              (by simp [pageSc, page, ExactCouple.d]))

/-- The map `g' : A' ⟶ E'` in the derived exact couple. -/
private noncomputable abbrev derivedg (X : ExactCoupleCat) : derivedA X ⟶ derivedE X :=
  let hImage := X.exact_f_α.isColimitImage
  hImage.desc (CokernelCofork.ofπ (derivedgFromA X) (f_comp_derivedgFromA_zero X))

/-- Helper for Chap12 Definition 12 21 3: the induced endomorphism on `image α` is represented on
the source object by the original endomorphism `α`. -/
private theorem factorThruImage_comp_derivedα (X : ExactCoupleCat) :
    factorThruImage X.α ≫ derivedα X = X.α ≫ factorThruImage X.α := by
  -- This is the source-side image-map computation for the square `(α, α)`.
  simpa using
    (image.factor_map (sq := (Arrow.homMk X.α X.α rfl : Arrow.mk X.α ⟶ Arrow.mk X.α)))

/-- Helper for Chap12 Definition 12 21 3: the descended map `derivedg` is represented on the
source object `A` by the homology class map induced by `g`. -/
private theorem factorThruImage_comp_derivedg (X : ExactCoupleCat) :
    factorThruImage X.α ≫ derivedg X = derivedgFromA X := by
  -- This is the defining computation rule for the cokernel descent.
  simpa [derivedg] using
    (Cofork.IsColimit.π_desc
      (t := CokernelCofork.ofπ (derivedgFromA X) (f_comp_derivedgFromA_zero X))
      X.exact_f_α.isColimitImage)

/-- Helper for Chap12 Definition 12 21 3: the source-level homology class of `g` is killed by
the derived `f`-map. -/
private theorem derivedgFromA_comp_derivedf_zero (X : ExactCoupleCat) :
    derivedgFromA X ≫ derivedf X = 0 := by
  -- Compare after the mono `image.ι α`, where `derivedf` is represented by `f` on cycles.
  apply (cancel_mono (image.ι X.α)).1
  rw [zero_comp]
  calc
    (derivedgFromA X ≫ derivedf X) ≫ image.ι X.α =
        (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫
          (pageSc X).homologyπ ≫ derivedf X ≫ image.ι X.α := by
            simp [derivedgFromA, Category.assoc]
    _ =
        (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫
          derivedfCycles X ≫ image.ι X.α := by
            simpa [Category.assoc] using
              congrArg
                (fun k ↦ (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫ k ≫ image.ι X.α)
                (ShortComplex.π_descHomology (S := pageSc X)
                  (k := derivedfCycles X) (hk := toCycles_comp_derivedfCycles_zero X))
    _ =
        (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫
          (pageSc X).iCycles ≫ X.f := by
            rw [derivedfCycles_comp_image_iota]
    _ = X.g ≫ X.f := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ X.f)
              (ShortComplex.liftCycles_i (S := pageSc X) (k := X.g) (hk := g_comp_d_zero X))
    _ = 0 := X.g_comp_f

-- Proof sketch: the map `f'` is induced from `f`, while `α'` is induced from `α`; the exactness
-- of the original couple implies the composite descends to zero on homology.
/-- In the derived exact couple, the composite `f' ≫ α'` vanishes. -/
private theorem derivedf_comp_derivedα_zero (X : ExactCoupleCat) :
    derivedf X ≫ derivedα X = 0 := by
  -- Compare after `homologyπ` and the mono `image.ι α`, where the composite is `f ≫ α`.
  apply (cancel_mono (image.ι X.α)).1
  rw [zero_comp]
  apply (cancel_epi (pageSc X).homologyπ).1
  rw [comp_zero]
  calc
    (pageSc X).homologyπ ≫ (derivedf X ≫ derivedα X) ≫ image.ι X.α =
        (pageSc X).homologyπ ≫ derivedf X ≫ (derivedα X ≫ image.ι X.α) := by
          simp [Category.assoc]
    _ = (pageSc X).homologyπ ≫ derivedf X ≫ (image.ι X.α ≫ X.α) := by
          rw [derivedα_comp_image_iota]
    _ = derivedfCycles X ≫ image.ι X.α ≫ X.α := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ image.ι X.α ≫ X.α)
              (ShortComplex.π_descHomology (S := pageSc X)
                (k := derivedfCycles X) (hk := toCycles_comp_derivedfCycles_zero X))
    _ = (pageSc X).iCycles ≫ X.f ≫ X.α := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ X.α) (derivedfCycles_comp_image_iota X)
    _ = 0 := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ (pageSc X).iCycles ≫ k) X.f_comp_α

/-- Helper for Chap12 Definition 12 21 3: the cycle representative of `derivedg` is already
killed by `α`. -/
private theorem α_comp_liftCycles_g_zero (X : ExactCoupleCat) :
    X.α ≫ (pageSc X).liftCycles X.g (g_comp_d_zero X) = 0 := by
  -- Compare after the mono of cycles, where this is exactly `α ≫ g = 0`.
  apply (cancel_mono (pageSc X).iCycles).1
  rw [zero_comp]
  calc
    (X.α ≫ (pageSc X).liftCycles X.g (g_comp_d_zero X)) ≫ (pageSc X).iCycles = X.α ≫ X.g := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ X.α ≫ k)
          (ShortComplex.liftCycles_i (S := pageSc X) (k := X.g) (hk := g_comp_d_zero X))
    _ = 0 := X.α_comp_g

-- Proof sketch: `α'` is induced by `α` on `image α`, and `g'` is induced by `g`; the original
-- relation `α ≫ g = 0` forces their composite to vanish.
/-- In the derived exact couple, the composite `α' ≫ g'` vanishes. -/
private theorem derivedα_comp_derivedg_zero (X : ExactCoupleCat) :
    derivedα X ≫ derivedg X = 0 := by
  -- Route correction: descend to the source-level representative on `A`, where the cycle lift
  -- is already killed by `α`.
  apply (cancel_epi (factorThruImage X.α)).1
  calc
    factorThruImage X.α ≫ derivedα X ≫ derivedg X =
        (factorThruImage X.α ≫ derivedα X) ≫ derivedg X := by
          simp [Category.assoc]
    _ = (X.α ≫ factorThruImage X.α) ≫ derivedg X := by
          rw [factorThruImage_comp_derivedα]
    _ = X.α ≫ (factorThruImage X.α ≫ derivedg X) := by
          simp [Category.assoc]
    _ = X.α ≫ derivedgFromA X := by
          rw [factorThruImage_comp_derivedg]
    _ = 0 := by
          calc
            X.α ≫ derivedgFromA X =
                (X.α ≫ (pageSc X).liftCycles X.g (g_comp_d_zero X)) ≫
                  (pageSc X).homologyπ := by
                    simp [derivedgFromA, Category.assoc]
            _ = 0 := by
                  rw [α_comp_liftCycles_g_zero]
                  simp
    _ = factorThruImage X.α ≫ 0 := by
          simp

-- Proof sketch: `g'` lands in cycles and `f'` factors through homology; exactness of the
-- original couple shows that the resulting composite is a boundary, hence zero in `A'`.
/-- In the derived exact couple, the composite `g' ≫ f'` vanishes. -/
private theorem derivedg_comp_derivedf_zero (X : ExactCoupleCat) :
    derivedg X ≫ derivedf X = 0 := by
  -- The descended map `derivedg` is represented on `A` by `derivedgFromA`.
  apply (cancel_epi (factorThruImage X.α)).1
  calc
    factorThruImage X.α ≫ derivedg X ≫ derivedf X =
        (factorThruImage X.α ≫ derivedg X) ≫ derivedf X := by
          simp [Category.assoc]
    _ = derivedgFromA X ≫ derivedf X := by
          rw [factorThruImage_comp_derivedg]
    _ = 0 := derivedgFromA_comp_derivedf_zero X
    _ = factorThruImage X.α ≫ 0 := by
          simp

-- Proof sketch: identify `A' = image α` and `E' = H(E, d)`, then use exactness of the original
-- couple together with the universal properties of image and homology to prove exactness at `A'`.
/-- Exactness of the derived couple at the first copy of `A'`. -/
private theorem derived_exact_f_α (X : ExactCoupleCat) :
    (ShortComplex.mk (derivedf X) (derivedα X) (derivedf_comp_derivedα_zero X)).Exact := by
  -- Route correction: refine a map into `image α` back to `A`, then lift its source-level
  -- preimage under `f` to a homology class whose image under `derivedf` recovers the refinement.
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₂ hx₂
  have hx₂α : (x₂ ≫ image.ι X.α) ≫ X.α = 0 := by
    simpa [Category.assoc, derivedα_comp_image_iota] using
      congrArg (fun k ↦ k ≫ image.ι X.α) hx₂
  obtain ⟨T', π, hπ, y, hy⟩ :=
    X.exact_f_α.exact_up_to_refinements (x₂ ≫ image.ι X.α) hx₂α
  have hyCycle : y ≫ X.d = 0 := by
    calc
      y ≫ X.d = y ≫ X.f ≫ X.g := by
        simp [ExactCouple.d]
      _ = π ≫ x₂ ≫ image.ι X.α ≫ X.g := by
        simpa [Category.assoc] using (congrArg (fun k ↦ k ≫ X.g) hy).symm
      _ = 0 := by
        simp [image_iota_comp_g_zero]
  refine ⟨T', π, hπ, (pageSc X).liftCycles y hyCycle ≫ (pageSc X).homologyπ, ?_⟩
  -- Compare after the mono `image.ι α`, where `derivedf` is represented by `f` on cycles.
  apply (cancel_mono (image.ι X.α)).1
  rw [Category.assoc]
  calc
    π ≫ x₂ ≫ image.ι X.α = y ≫ X.f := by
      simpa [Category.assoc] using hy
    _ = (pageSc X).liftCycles y hyCycle ≫ (pageSc X).iCycles ≫ X.f := by
      symm
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ X.f)
          (ShortComplex.liftCycles_i (S := pageSc X) (k := y) (hk := hyCycle))
    _ =
        (pageSc X).liftCycles y hyCycle ≫ derivedfCycles X ≫ image.ι X.α := by
          rw [derivedfCycles_comp_image_iota]
    _ =
        (((pageSc X).liftCycles y hyCycle ≫ (pageSc X).homologyπ) ≫
          derivedf X) ≫ image.ι X.α := by
            simp [Category.assoc]

-- Proof sketch: exactness at `A'` follows from the original exact couple after passing to the
-- image of `α` and the homology of `d`.
/-- Exactness of the derived couple at the second copy of `A'`. -/
private theorem derived_exact_α_g (X : ExactCoupleCat) :
    (ShortComplex.mk (derivedα X) (derivedg X) (derivedα_comp_derivedg_zero X)).Exact := by
  -- Route correction: refine through `factorThruImage α`, convert the vanishing homology class
  -- of `g` into a boundary, and then use the original exact row `A --α--> A --g--> E`.
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₂ hx₂
  obtain ⟨T₁, π₁, hπ₁, y, hy⟩ :=
    surjective_up_to_refinements_of_epi (factorThruImage X.α) x₂
  have hyZero : y ≫ derivedgFromA X = 0 := by
    have hx₂' : π₁ ≫ x₂ ≫ derivedg X = 0 := by
      simpa [Category.assoc] using congrArg (fun k ↦ π₁ ≫ k) hx₂
    calc
      y ≫ derivedgFromA X = y ≫ factorThruImage X.α ≫ derivedg X := by
        rw [factorThruImage_comp_derivedg]
      _ = π₁ ≫ x₂ ≫ derivedg X := by
        simpa [Category.assoc] using (congrArg (fun k ↦ k ≫ derivedg X) hy).symm
      _ = 0 := hx₂'
  have hyCycle : (y ≫ X.g) ≫ X.d = 0 := by
    simpa [Category.assoc] using congrArg (fun k ↦ y ≫ k) (g_comp_d_zero X)
  have hyHomologyZero :
      (pageSc X).liftCycles (y ≫ X.g) hyCycle ≫ (pageSc X).homologyπ = 0 := by
    calc
      (pageSc X).liftCycles (y ≫ X.g) hyCycle ≫ (pageSc X).homologyπ =
          y ≫ derivedgFromA X := by
            calc
              (pageSc X).liftCycles (y ≫ X.g) hyCycle ≫ (pageSc X).homologyπ =
                  y ≫ (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫
                    (pageSc X).homologyπ := by
                      rw [← Category.assoc, ShortComplex.comp_liftCycles]
              _ = y ≫ derivedgFromA X := by
                    simp [derivedgFromA]
      _ = 0 := hyZero
  obtain ⟨T₂, ρ, hρ, b, hb⟩ :=
    ((pageSc X).liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements (y ≫ X.g) hyCycle).1
      hyHomologyZero
  have hb' : ρ ≫ y ≫ X.g = b ≫ X.f ≫ X.g := by
    simpa [pageSc, page, ExactCouple.d, Category.assoc] using hb
  have hkernel : (ρ ≫ y - b ≫ X.f) ≫ X.g = 0 := by
    calc
      (ρ ≫ y - b ≫ X.f) ≫ X.g = ρ ≫ y ≫ X.g - b ≫ X.f ≫ X.g := by
        simp [Category.assoc, Preadditive.sub_comp]
      _ = 0 := by
        rw [hb']
        simp
  obtain ⟨T₃, σ, hσ, c, hc⟩ :=
    X.exact_α_g.exact_up_to_refinements (ρ ≫ y - b ≫ X.f) hkernel
  have hc' : σ ≫ ρ ≫ y = c ≫ X.α + σ ≫ b ≫ X.f := by
    have hc'' : σ ≫ ρ ≫ y - σ ≫ b ≫ X.f = c ≫ X.α := by
      simpa [Category.assoc, Preadditive.comp_sub] using hc
    rwa [sub_eq_iff_eq_add] at hc''
  refine ⟨T₃, σ ≫ ρ ≫ π₁, inferInstance, c ≫ factorThruImage X.α, ?_⟩
  calc
    (σ ≫ ρ ≫ π₁) ≫ x₂ = σ ≫ ρ ≫ (π₁ ≫ x₂) := by
      simp [Category.assoc]
    _ = σ ≫ ρ ≫ (y ≫ factorThruImage X.α) := by
      rw [hy]
    _ = (σ ≫ ρ ≫ y) ≫ factorThruImage X.α := by
      simp [Category.assoc]
    _ = (c ≫ X.α + σ ≫ b ≫ X.f) ≫ factorThruImage X.α := by
      rw [hc']
    _ = c ≫ X.α ≫ factorThruImage X.α + σ ≫ b ≫ X.f ≫ factorThruImage X.α := by
      simp [Category.assoc, Preadditive.add_comp]
    _ = c ≫ X.α ≫ factorThruImage X.α := by
      have hfim' : σ ≫ b ≫ X.f ≫ factorThruImage X.α = σ ≫ b ≫ 0 := by
        exact congrArg (fun k ↦ σ ≫ b ≫ k) (comp_factorThruImage_eq_zero X.f_comp_α)
      have hfim : σ ≫ b ≫ X.f ≫ factorThruImage X.α = 0 := by
        calc
          σ ≫ b ≫ X.f ≫ factorThruImage X.α = σ ≫ b ≫ 0 := hfim'
          _ = σ ≫ 0 := by rw [comp_zero]
          _ = 0 := by rw [comp_zero]
      rw [hfim, add_zero]
    _ = (c ≫ factorThruImage X.α) ≫ derivedα X := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ c ≫ k) (factorThruImage_comp_derivedα X).symm

-- Proof sketch: exactness at `E'` is the standard description of homology for the differential
-- on `E`, expressed through the induced maps `g'` and `f'`.
/-- Exactness of the derived couple at `E'`. -/
private theorem derived_exact_g_f (X : ExactCoupleCat) :
    (ShortComplex.mk (derivedg X) (derivedf X) (derivedg_comp_derivedf_zero X)).Exact := by
  -- Route correction: first refine a homology class to a cycle, then use the original exact
  -- row `A --g--> E --f--> A` on that cycle.
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro T x₂ hx₂
  obtain ⟨T', π, hπ, z, hz, hfac⟩ :=
    (pageSc X).eq_liftCycles_homologyπ_up_to_refinements x₂
  have hzf : z ≫ X.f = 0 := by
    have hx₂' : π ≫ x₂ ≫ derivedf X ≫ image.ι X.α = 0 := by
      simpa [Category.assoc] using congrArg (fun k ↦ π ≫ k ≫ image.ι X.α) hx₂
    have hx₂z :
        (pageSc X).liftCycles z hz ≫ (pageSc X).homologyπ ≫ derivedf X ≫ image.ι X.α = 0 := by
      calc
        (pageSc X).liftCycles z hz ≫ (pageSc X).homologyπ ≫ derivedf X ≫ image.ι X.α =
            π ≫ x₂ ≫ derivedf X ≫ image.ι X.α := by
              simpa [Category.assoc] using
                (congrArg (fun k ↦ k ≫ derivedf X ≫ image.ι X.α) hfac).symm
        _ = 0 := hx₂'
    have hzf' : (pageSc X).liftCycles z hz ≫ (pageSc X).iCycles ≫ X.f = 0 := by
      simpa [Category.assoc, derivedf, derivedfCycles_comp_image_iota] using hx₂z
    calc
      z ≫ X.f = (pageSc X).liftCycles z hz ≫ (pageSc X).iCycles ≫ X.f := by
        symm
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ X.f)
            (ShortComplex.liftCycles_i (S := pageSc X) (k := z) (hk := hz))
      _ = 0 := hzf'
  obtain ⟨T'', ρ, hρ, a, ha⟩ := X.exact_g_f.exact_up_to_refinements z hzf
  have hagCycle : (a ≫ X.g) ≫ X.d = 0 := by
    simpa [Category.assoc] using congrArg (fun k ↦ a ≫ k) (g_comp_d_zero X)
  have hzρ' : ρ ≫ z ≫ X.d = ρ ≫ (0 : T' ⟶ X.E) := by
    exact congrArg (fun k ↦ ρ ≫ k) hz
  have hzρ : (ρ ≫ z) ≫ X.d = 0 := by
    rw [Category.assoc, hzρ', comp_zero]
  have hlift : (pageSc X).liftCycles (ρ ≫ z) hzρ = (pageSc X).liftCycles (a ≫ X.g) hagCycle := by
    apply (cancel_mono (pageSc X).iCycles).1
    simpa [Category.assoc, ShortComplex.liftCycles_i, ha]
  refine ⟨T'', ρ ≫ π, inferInstance, a ≫ factorThruImage X.α, ?_⟩
  calc
    (ρ ≫ π) ≫ x₂ = ρ ≫ (π ≫ x₂) := by simp [Category.assoc]
    _ = ρ ≫ ((pageSc X).liftCycles z hz ≫ (pageSc X).homologyπ) := by rw [hfac]
    _ = (ρ ≫ (pageSc X).liftCycles z hz) ≫ (pageSc X).homologyπ := by
          simp [Category.assoc]
    _ =
        (pageSc X).liftCycles (ρ ≫ z) hzρ ≫
          (pageSc X).homologyπ := by
            rw [ShortComplex.comp_liftCycles]
    _ = (pageSc X).liftCycles (a ≫ X.g) hagCycle ≫ (pageSc X).homologyπ := by
          rw [hlift]
    _ = (a ≫ factorThruImage X.α) ≫ derivedg X := by
          calc
            (pageSc X).liftCycles (a ≫ X.g) hagCycle ≫ (pageSc X).homologyπ =
                a ≫ (pageSc X).liftCycles X.g (g_comp_d_zero X) ≫ (pageSc X).homologyπ := by
                  rw [← Category.assoc, ShortComplex.comp_liftCycles]
            _ = a ≫ derivedgFromA X := by
                  simp [derivedgFromA]
            _ = (a ≫ factorThruImage X.α) ≫ derivedg X := by
                  simpa [Category.assoc] using
                    (congrArg (fun k ↦ a ≫ k) (factorThruImage_comp_derivedg X)).symm

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

/-- Chap12 Definition 12 21 3: the spectral sequence associated to an exact couple is the
single-object spectral sequence whose page `E_r` is the middle object of the `(r - 1)`-fold
derived exact couple, so `E₁ = E`, `d₁ = d`, `E₂ = E'`, `d₂ = d'`, `E₃ = E''`, `d₃ = d''`,
and so on. -/
@[stacks 011S]
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
