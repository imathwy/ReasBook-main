import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Topology.Category.TopCat.Sphere
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Example_9_4_8
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_2

open Bundle OnePoint
open scoped TopCat ComplexKTheory

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a verified topological-`K`-theory owner
-- for this `S²` calculation. The local Chapter 24 `complexKTheory` owner therefore uses the
-- explicit Chapter 9 comparison `S² ≃ₜ OnePoint ℂ ≃ ℂP¹`.

/-- The canonical `S²` owner used for this Chapter 24 `K`-theory calculation. -/
abbrev SphereTwo := TopCat.sphere 2

/-- The source `S³` of the Hopf map, bundled in the same universe as `SphereTwo`. -/
abbrev SphereThree := TopCat.sphere 3

/-- The tautological complex line over a point of `ℂP¹`, viewed as a type-valued fiber. -/
abbrev complexProjectiveLineTautologicalFiber
    (x : ComplexProjectiveLine) : Type :=
  Projectivization.submodule x

private abbrev complexFinTwoArrowSymm : (ℂ × ℂ) →ₗ[ℂ] (Fin 2 → ℂ) :=
  ((LinearEquiv.finTwoArrow ℂ ℂ).symm : (ℂ × ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))

/-- The tautological complex line over `OnePoint ℂ`, obtained from the explicit Chapter 9
comparison `OnePoint ℂ ≃ ℂP¹`. -/
private abbrev onePointHopfLine
    (x : OnePoint ℂ) : Type :=
  complexProjectiveLineTautologicalFiber (complexProjectiveLineEquivOnePointComplex x)

private abbrev onePointHopfFiniteGenerator
    (z : ℂ) : Fin 2 → ℂ :=
  complexFinTwoArrowSymm (z, 1)

private abbrev onePointHopfNonzeroGenerator
    (z : ℂ) : Fin 2 → ℂ :=
  complexFinTwoArrowSymm (1, z⁻¹)

private abbrev onePointHopfInfinityGenerator : Fin 2 → ℂ :=
  complexFinTwoArrowSymm (1, 0)

private def onePointHopfFiniteBaseSet : Set (OnePoint ℂ) :=
  ({(∞ : OnePoint ℂ)} : Set (OnePoint ℂ))ᶜ

private def onePointHopfNonzeroBaseSet : Set (OnePoint ℂ) :=
  ({((0 : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ))ᶜ

private def onePointHopfFiniteSymm
    (x : OnePoint ℂ) (a : ℂ) : onePointHopfLine x :=
  match x with
  | ∞ => 0
  | (z : ℂ) =>
      ⟨a • onePointHopfFiniteGenerator z, by
        sorry⟩

private def onePointHopfNonzeroSymm
    (x : OnePoint ℂ) (a : ℂ) : onePointHopfLine x :=
  match x with
  | ∞ =>
      ⟨a • onePointHopfInfinityGenerator, by
        sorry⟩
  | (z : ℂ) =>
      if hz : z = 0 then
        0
      else
        ⟨a • onePointHopfNonzeroGenerator z, by
          sorry⟩

private def onePointHopfFinitePretrivialization :
    Pretrivialization ℂ (π ℂ onePointHopfLine) where
  toFun p := (p.1, p.2.1 1)
  invFun p := ⟨p.1, onePointHopfFiniteSymm p.1 p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' onePointHopfFiniteBaseSet
  target := onePointHopfFiniteBaseSet ×ˢ Set.univ
  map_source' := by
    intro p hp
    simpa [onePointHopfFiniteBaseSet] using hp
  map_target' := by
    intro p hp
    simpa [onePointHopfFiniteBaseSet] using hp.1
  left_inv' := by
    sorry
  right_inv' := by
    sorry
  open_target := (isClosed_singleton.isOpen_compl).prod isOpen_univ
  baseSet := onePointHopfFiniteBaseSet
  open_baseSet := isClosed_singleton.isOpen_compl
  source_eq := rfl
  target_eq := rfl
  proj_toFun := by
    intro p hp
    rfl

private def onePointHopfNonzeroPretrivialization :
    Pretrivialization ℂ (π ℂ onePointHopfLine) where
  toFun p := (p.1, p.2.1 0)
  invFun p := ⟨p.1, onePointHopfNonzeroSymm p.1 p.2⟩
  source := Bundle.TotalSpace.proj ⁻¹' onePointHopfNonzeroBaseSet
  target := onePointHopfNonzeroBaseSet ×ˢ Set.univ
  map_source' := by
    intro p hp
    simpa [onePointHopfNonzeroBaseSet] using hp
  map_target' := by
    intro p hp
    simpa [onePointHopfNonzeroBaseSet] using hp.1
  left_inv' := by
    sorry
  right_inv' := by
    sorry
  open_target := (isClosed_singleton.isOpen_compl).prod isOpen_univ
  baseSet := onePointHopfNonzeroBaseSet
  open_baseSet := isClosed_singleton.isOpen_compl
  source_eq := rfl
  target_eq := rfl
  proj_toFun := by
    intro p hp
    rfl

private def onePointHopfPretrivializationAtlas :
    Set (Pretrivialization ℂ (π ℂ onePointHopfLine)) :=
  {e | e = onePointHopfFinitePretrivialization ∨ e = onePointHopfNonzeroPretrivialization}

private def onePointHopfFiniteToNonzeroCoordChange :
    OnePoint ℂ → ℂ →L[ℂ] ℂ
  | ∞ => ContinuousLinearMap.id ℂ ℂ
  | (z : ℂ) => z • ContinuousLinearMap.id ℂ ℂ

private def onePointHopfNonzeroToFiniteCoordChange :
    OnePoint ℂ → ℂ →L[ℂ] ℂ
  | ∞ => ContinuousLinearMap.id ℂ ℂ
  | (z : ℂ) => z⁻¹ • ContinuousLinearMap.id ℂ ℂ

private local instance : DecidableEq (OnePoint ℂ) :=
  Classical.decEq _

private def onePointHopfVectorPrebundle :
    VectorPrebundle ℂ ℂ onePointHopfLine where
  pretrivializationAtlas := onePointHopfPretrivializationAtlas
  pretrivialization_linear' := by
    intro e he
    change e = onePointHopfFinitePretrivialization ∨
      e = onePointHopfNonzeroPretrivialization at he
    rcases he with rfl | rfl
    · refine ⟨?_⟩
      intro b hb
      refine
        { map_add := fun x y ↦ rfl
          map_smul := fun c x ↦ rfl }
    · refine ⟨?_⟩
      intro b hb
      refine
        { map_add := fun x y ↦ rfl
          map_smul := fun c x ↦ rfl }
  pretrivializationAt := fun x ↦
    if x = (∞ : OnePoint ℂ) then
      onePointHopfNonzeroPretrivialization
    else
      onePointHopfFinitePretrivialization
  mem_base_pretrivializationAt := by
    classical
    intro x
    by_cases hx : x = (∞ : OnePoint ℂ)
    · simp [hx, onePointHopfNonzeroPretrivialization, onePointHopfNonzeroBaseSet]
    · simp [hx, onePointHopfFinitePretrivialization, onePointHopfFiniteBaseSet]
  pretrivialization_mem_atlas := by
    classical
    intro x
    by_cases hx : x = (∞ : OnePoint ℂ)
    · simp [hx, onePointHopfPretrivializationAtlas]
    · simp [hx, onePointHopfPretrivializationAtlas]
  exists_coordChange := by
    intro e he e' he'
    have he_mem :
        e = onePointHopfFinitePretrivialization ∨ e = onePointHopfNonzeroPretrivialization := by
      change e = onePointHopfFinitePretrivialization ∨
        e = onePointHopfNonzeroPretrivialization at he
      exact he
    have he'_mem :
        e' = onePointHopfFinitePretrivialization ∨ e' = onePointHopfNonzeroPretrivialization := by
      change e' = onePointHopfFinitePretrivialization ∨
        e' = onePointHopfNonzeroPretrivialization at he'
      exact he'
    rcases he_mem with rfl | rfl <;> rcases he'_mem with rfl | rfl
    · refine ⟨fun _ ↦ ContinuousLinearMap.id ℂ ℂ, continuousOn_const, ?_⟩
      intro b hb v
      sorry
    · refine ⟨onePointHopfFiniteToNonzeroCoordChange, by
        sorry, ?_⟩
      intro b hb v
      sorry
    · refine ⟨onePointHopfNonzeroToFiniteCoordChange, by
        sorry, ?_⟩
      intro b hb v
      sorry
    · refine ⟨fun _ ↦ ContinuousLinearMap.id ℂ ℂ, continuousOn_const, ?_⟩
      intro b hb v
      sorry
  totalSpaceMk_isInducing := by
    intro b
    sorry

private instance onePointHopfLine_totalSpaceTopologicalSpace :
    TopologicalSpace (Bundle.TotalSpace ℂ onePointHopfLine) :=
  onePointHopfVectorPrebundle.totalSpaceTopology

private instance onePointHopfLine_fiberBundle :
    FiberBundle ℂ onePointHopfLine :=
  onePointHopfVectorPrebundle.toFiberBundle

private instance onePointHopfLine_vectorBundle :
    VectorBundle ℂ ℂ onePointHopfLine :=
  onePointHopfVectorPrebundle.toVectorBundle

/-- The actual Hopf line bundle on `S²`, obtained by transporting the tautological line on
`ℂP¹` along the explicit Chapter 9 comparison `S² ≃ₜ OnePoint ℂ ≃ ℂP¹`. -/
abbrev sphereTwoHopfLine : SphereTwo → Type :=
  fun x ↦ onePointHopfLine (sphereTwoHomeomorphOnePointComplex x)

/-- Each fiber of `sphereTwoHopfLine` carries the inherited complex module structure. -/
instance sphereTwoHopfLine_module (x : SphereTwo) :
    Module ℂ (sphereTwoHopfLine x) :=
  inferInstanceAs
    (Module ℂ
      (complexProjectiveLineTautologicalFiber
        (complexProjectiveLineEquivOnePointComplex
          (sphereTwoHomeomorphOnePointComplex x))))

/-- The Hopf line bundle on `S²` carries its pointwise complex module structure. -/
instance sphereTwoHopfLine_instModule :
    (x : SphereTwo) → Module ℂ (sphereTwoHopfLine x) :=
  fun x ↦ inferInstanceAs (Module ℂ (sphereTwoHopfLine x))

/-- The transported Hopf family on `S²` carries the pulled-back total-space topology. -/
instance sphereTwoHopfLine_totalSpaceTopologicalSpace :
    TopologicalSpace (Bundle.TotalSpace ℂ sphereTwoHopfLine) :=
  inferInstanceAs
    (TopologicalSpace
      (Bundle.TotalSpace ℂ
        ((sphereTwoHomeomorphOnePointComplex : SphereTwo → OnePoint ℂ) *ᵖ onePointHopfLine)))

/-- Each fiber of the transported Hopf family carries its induced topology. -/
instance sphereTwoHopfLine_fiberTopologicalSpace
    (x : SphereTwo) :
    TopologicalSpace (sphereTwoHopfLine x) :=
  inferInstanceAs
    (TopologicalSpace
      (((sphereTwoHomeomorphOnePointComplex : SphereTwo → OnePoint ℂ) *ᵖ onePointHopfLine) x))

/-- The actual Hopf family on `S²` is a fiber bundle, via pullback of the tautological line over
`OnePoint ℂ ≃ ℂP¹`. -/
instance sphereTwoHopfLine_fiberBundle :
    FiberBundle ℂ sphereTwoHopfLine :=
  inferInstanceAs
    (FiberBundle ℂ
      ((sphereTwoHomeomorphOnePointComplex : SphereTwo → OnePoint ℂ) *ᵖ onePointHopfLine))

/-- The actual Hopf family on `S²` is a complex line bundle, via pullback of the tautological line
over `OnePoint ℂ ≃ ℂP¹`. -/
instance sphereTwoHopfLine_vectorBundle :
    VectorBundle ℂ ℂ sphereTwoHopfLine :=
  inferInstanceAs
    (VectorBundle ℂ ℂ
      ((sphereTwoHomeomorphOnePointComplex : SphereTwo → OnePoint ℂ) *ᵖ onePointHopfLine))

/-- The honest presentation of the actual Hopf line bundle on `S²`. -/
noncomputable abbrev sphereTwoHopfLinePresentation :
    ComplexVectorBundle.Presentation SphereTwo :=
  ComplexVectorBundle.Presentation.ofFamily ℂ sphereTwoHopfLine

/-- The actual class `[H]` in `K(S²)`, defined directly from the actual Hopf line bundle on
`S²`. -/
noncomputable abbrev sphereTwoHopfLineClass :
    K(SphereTwo) :=
  ComplexVectorBundle.toVirtualPresentation sphereTwoHopfLinePresentation

/-- `sphereTwoHopfLineClass` is the virtual class of the direct presentation
`sphereTwoHopfLinePresentation`. -/
theorem sphereTwoHopfLineClass_def :
    sphereTwoHopfLineClass =
      ComplexVectorBundle.toVirtualPresentation sphereTwoHopfLinePresentation := rfl

/-- Polynomial evaluation at the Hopf line-bundle class `[H] ∈ K(S²)`. -/
noncomputable abbrev sphereTwoComplexKTheoryPolynomialEval :
    Polynomial ℤ →+* K(SphereTwo) :=
  Polynomial.eval₂RingHom
    (Int.castRingHom (K(SphereTwo)))
    sphereTwoHopfLineClass

/-- Theorem 24.2.1 (1). For the actual Hopf line bundle on `S²`, the corresponding class
`[H] ∈ K(S²)` satisfies the relation `([H] - 1)^2 = 0`. -/
theorem sphereTwoHopfLineClass_sub_one_sq :
    (sphereTwoHopfLineClass - 1) ^ (2 : ℕ) = (0 : K(SphereTwo)) := sorry

/-- Theorem 24.2.1 (2). The ring `K(S²)` is generated by the actual Hopf class `[H]` with
defining relation `([H] - 1)^2 = 0`; equivalently, polynomial evaluation at `[H]` is surjective
and has kernel the ideal generated by `(Polynomial.X - 1)^2`. -/
theorem sphereTwoComplexKTheory_polynomialAeval_presentation :
    Function.Surjective sphereTwoComplexKTheoryPolynomialEval ∧
      RingHom.ker sphereTwoComplexKTheoryPolynomialEval =
        Ideal.span ({(Polynomial.X - 1) ^ (2 : ℕ)} : Set (Polynomial ℤ)) := sorry

/-- The reduced Hopf class on `S²` is represented by `1 - [H]`. -/
theorem one_sub_sphereTwoHopfLineClass_mem_reducedComplexKTheory
    (x₀ : SphereTwo) :
    1 - sphereTwoHopfLineClass ∈ K̃(SphereTwo, x₀) := sorry

/-- The canonical reduced Hopf class on `S²`, represented by `1 - [H]`. -/
noncomputable def sphereTwoReducedHopfLineClass
    (x₀ : SphereTwo) :
    K̃(SphereTwo, x₀) :=
  ⟨1 - sphereTwoHopfLineClass,
    one_sub_sphereTwoHopfLineClass_mem_reducedComplexKTheory x₀⟩

/-- The underlying `K(S²)`-class of `sphereTwoReducedHopfLineClass x₀` is `1 - [H]`. -/
theorem sphereTwoReducedHopfLineClass_coe
    (x₀ : SphereTwo) :
    (sphereTwoReducedHopfLineClass x₀).1 = 1 - sphereTwoHopfLineClass := rfl

/-- Theorem 24.2.1 (3). Any reduced class `η` equal to the canonical reduced Hopf class
`1 - [H]` generates `K̃(S²)` additively. -/
theorem sphereTwoReducedComplexKTheory_generated_by_one_sub_hopfLineClass
    (x₀ : SphereTwo) (η : K̃(SphereTwo, x₀))
    (hη : η = sphereTwoReducedHopfLineClass x₀) :
    Function.Surjective (zmultiplesHom (K̃(SphereTwo, x₀)) η) := sorry
