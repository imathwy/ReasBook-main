import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap24.Definition_24_1_1
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

-- Semantic recall: this item keeps the source-facing based `K`-theory surface, while the current
-- Chapter 24 bundle presentations use one model fiber over all of `X`. The resulting based
-- dimension map is therefore a source-facing view of the canonical dimension map from
-- `Definition_24_1_1`.

noncomputable section

universe u

namespace ComplexKTheory

@[inherit_doc complexKTheory]
scoped notation "K(" X ")" => _root_.complexKTheory X

end ComplexKTheory

open scoped ComplexKTheory

namespace ComplexVectorBundle

variable {X : Type u} [TopologicalSpace X]

/-- The complex dimension of the chosen model fiber of a presented bundle over `X`. -/
def presentationDimension (V : Presentation X) : ℤ :=
  (Module.finrank ℂ V.fiber : ℤ)

/-- Each fiber of a presented bundle over `X` is finite-dimensional over `ℂ`. -/
noncomputable instance (V : Presentation X) (x : X) : FiniteDimensional ℂ (V.bundle x) := sorry

/-- The complex dimension of the actual fiber of a presented bundle over `X` at the chosen point
`x₀`. For the current presentation model, this is the same as `presentationDimension V`. -/
def presentationDimensionAt (V : Presentation X) (x₀ : X) : ℤ :=
  (Module.finrank ℂ (V.bundle x₀) : ℤ)

/-- In the current presentation model, the fiber dimension at `x₀` is the model-fiber
dimension. -/
theorem presentationDimensionAt_eq (V : Presentation X) (x₀ : X) :
    presentationDimensionAt V x₀ = presentationDimension V := sorry

/-- Bundle isomorphism preserves the dimension of the chosen model fiber. -/
theorem presentationDimension_eq_of_iso {V W : Presentation X} (h : Nonempty (Iso V W)) :
    presentationDimension V = presentationDimension W := sorry

/-- Bundle isomorphism preserves the dimension of the fiber over the chosen point. -/
theorem presentationDimensionAt_eq_of_iso {V W : Presentation X} (x₀ : X) (h : Nonempty (Iso V W)) :
    presentationDimensionAt V x₀ = presentationDimensionAt W x₀ := by
  simpa [presentationDimensionAt_eq V x₀, presentationDimensionAt_eq W x₀] using
    presentationDimension_eq_of_iso h

/-- The dimension of a complex vector-bundle isomorphism class over `X`. -/
def classesDimension (X : Type u) [TopologicalSpace X] : classes X →+ ℤ where
  toFun :=
    Quotient.lift
      (fun V : Presentation X ↦ presentationDimension V)
      (fun _ _ h ↦ presentationDimension_eq_of_iso h)
  map_zero' := sorry
  map_add' := sorry

/-- `classesDimension` sends a presented bundle to the dimension of its model fiber. -/
theorem classesDimension_def (V : Presentation X) :
    classesDimension X (classOfPresentation V) = presentationDimension V := sorry

/-- The dimension of the fiber over `x₀` defines a homomorphism on bundle-isomorphism classes
over `X`. For the current presentation model, this is the source-facing based view of
`classesDimension X`. -/
def classesDimensionAt (X : Type u) [TopologicalSpace X] (x₀ : X) : classes X →+ ℤ where
  toFun :=
    Quotient.lift
      (fun V : Presentation X ↦ presentationDimensionAt V x₀)
      (fun _ _ h ↦ presentationDimensionAt_eq_of_iso x₀ h)
  map_zero' := sorry
  map_add' := sorry

/-- In the current presentation model, the based dimension map on bundle classes agrees with the
canonical dimension map. -/
theorem classesDimensionAt_eq (X : Type u) [TopologicalSpace X] (x₀ : X) :
    classesDimensionAt X x₀ = classesDimension X := sorry

/-- `classesDimensionAt` sends a presented bundle to the dimension of its fiber over `x₀`. -/
theorem classesDimensionAt_def (x₀ : X) (V : Presentation X) :
    classesDimensionAt X x₀ (classOfPresentation V) = presentationDimensionAt V x₀ := sorry

/-- The trivial complex line bundle has dimension `1`. -/
theorem presentationDimension_trivialLine (X : Type u) [TopologicalSpace X] :
    presentationDimension (trivialLine X) = 1 := sorry

/-- The dimension of the trivial complex line-bundle class is `1`. -/
theorem classesDimension_classesOne (X : Type u) [TopologicalSpace X] :
    classesDimension X classesOne = 1 := sorry

end ComplexVectorBundle

/-- The dimension map `K(X) → ℤ` on complex topological `K`-theory, obtained by extending the
fiber-dimension map on honest bundle classes. -/
def complexKTheoryDimension (X : Type u) [TopologicalSpace X] :
    K(X) →+ ℤ :=
  Algebra.GrothendieckAddGroup.lift (ComplexVectorBundle.classesDimension X)

/-- The based dimension map `K(X) → ℤ`, obtained by taking the fiber dimension at the chosen
basepoint `x₀`. On this Chapter 24 Lean surface, bundle presentations use one model fiber over all
of `X`, so this agrees with the canonical dimension map. -/
def complexKTheoryDimensionAt (X : Type u) [TopologicalSpace X] (x₀ : X) :
    K(X) →+ ℤ :=
  Algebra.GrothendieckAddGroup.lift (ComplexVectorBundle.classesDimensionAt X x₀)

/-- In the current presentation model, the based dimension map agrees with the canonical
dimension map. -/
theorem complexKTheoryDimensionAt_eq (X : Type u) [TopologicalSpace X] (x₀ : X) :
    complexKTheoryDimensionAt X x₀ = complexKTheoryDimension X := sorry

/-- The dimension map sends an honest bundle class to the dimension of its chosen model fiber. -/
theorem complexKTheoryDimension_toVirtualPresentation
    {X : Type u} [TopologicalSpace X]
    (V : ComplexVectorBundle.Presentation X) :
    complexKTheoryDimension X (ComplexVectorBundle.toVirtualPresentation V) =
      ComplexVectorBundle.presentationDimension V := sorry

/-- The based dimension map sends an honest bundle class to the dimension of its fiber over
`x₀`. -/
theorem complexKTheoryDimensionAt_toVirtualPresentation
    {X : Type u} [TopologicalSpace X] (x₀ : X)
    (V : ComplexVectorBundle.Presentation X) :
    complexKTheoryDimensionAt X x₀ (ComplexVectorBundle.toVirtualPresentation V) =
      ComplexVectorBundle.presentationDimensionAt V x₀ := by
  simpa [complexKTheoryDimensionAt_eq X x₀,
    ComplexVectorBundle.presentationDimensionAt_eq V x₀] using
    complexKTheoryDimension_toVirtualPresentation V

/-- The trivial line-bundle class in `K(X)` has dimension `1`. -/
theorem complexKTheoryDimension_one
    {X : Type u} [TopologicalSpace X] :
    complexKTheoryDimension X (1 : K(X)) = 1 := sorry

/-- Integer multiples of the trivial line-bundle class give the canonical map `ℤ → K(X)`. -/
def complexKTheoryIntSection (X : Type u) [TopologicalSpace X] :
    ℤ →+ K(X) :=
  zmultiplesHom (K(X)) (1 : K(X))

/-- The dimension map is a left inverse to the canonical `ℤ → K(X)` section. -/
theorem complexKTheoryDimension_intSection
    {X : Type u} [TopologicalSpace X] (n : ℤ) :
    complexKTheoryDimension X (complexKTheoryIntSection X n) = n := sorry

/-- `complexKTheoryIntSection X` is a right inverse to the canonical dimension map. -/
theorem complexKTheoryDimension_rightInverse
    (X : Type u) [TopologicalSpace X] :
    Function.RightInverse (complexKTheoryIntSection X) (complexKTheoryDimension X) :=
  complexKTheoryDimension_intSection

/-- The canonical dimension map splits the canonical section `ℤ → K(X)`. -/
theorem complexKTheoryDimension_comp_intSection
    (X : Type u) [TopologicalSpace X] :
    (complexKTheoryDimension X).comp (complexKTheoryIntSection X) = AddMonoidHom.id ℤ := by
  exact AddMonoidHom.ext <| complexKTheoryDimension_intSection

/-- The based dimension map is a left inverse to the canonical `ℤ → K(X)` section. -/
theorem complexKTheoryDimensionAt_intSection
    {X : Type u} [TopologicalSpace X] (x₀ : X) (n : ℤ) :
    complexKTheoryDimensionAt X x₀ (complexKTheoryIntSection X n) = n := by
  simpa [complexKTheoryDimensionAt_eq X x₀] using complexKTheoryDimension_intSection n

/-- `complexKTheoryIntSection X` is a right inverse to the based dimension map. -/
theorem complexKTheoryDimensionAt_rightInverse
    (X : Type u) [TopologicalSpace X] (x₀ : X) :
    Function.RightInverse (complexKTheoryIntSection X) (complexKTheoryDimensionAt X x₀) :=
  complexKTheoryDimensionAt_intSection x₀

/-- The based dimension map splits the canonical section `ℤ → K(X)`. -/
theorem complexKTheoryDimensionAt_comp_intSection
    (X : Type u) [TopologicalSpace X] (x₀ : X) :
    (complexKTheoryDimensionAt X x₀).comp (complexKTheoryIntSection X) = AddMonoidHom.id ℤ := by
  exact AddMonoidHom.ext <| complexKTheoryDimensionAt_intSection x₀

/-- Definition 24.1.2 (1): `K̃(X, x₀)` is the kernel of the based dimension map
`complexKTheoryDimensionAt X x₀ : K(X) →+ ℤ`. In the chapter's source-facing compact-based-space
setting, this is the reduced complex topological `K`-theory group. -/
abbrev reducedComplexKTheory (X : Type u) [TopologicalSpace X] (x₀ : X) :=
  AddMonoidHom.ker (complexKTheoryDimensionAt X x₀)

namespace ComplexKTheory

@[inherit_doc reducedComplexKTheory]
scoped notation "K̃(" X ", " x₀ ")" => _root_.reducedComplexKTheory X x₀

end ComplexKTheory

/-- An element of `K(X)` lies in `K̃(X, x₀)` exactly when its dimension is `0`. -/
theorem mem_reducedComplexKTheory_iff
    {X : Type u} [TopologicalSpace X] {x₀ : X} {ξ : K(X)} :
    ξ ∈ K̃(X, x₀) ↔ complexKTheoryDimensionAt X x₀ ξ = 0 := Iff.rfl

/-- The based dimension map and the inclusion `K̃(X, x₀) ↪ K(X)` form the additive extension
`0 → K̃(X, x₀) → K(X) → ℤ → 0`. -/
def complexKTheoryReducedDimensionExtension
    (X : Type u) [TopologicalSpace X] (x₀ : X) :
    AddGroupExtension (K̃(X, x₀)) (K(X)) ℤ where
  inl := (K̃(X, x₀)).subtype
  rightHom := complexKTheoryDimensionAt X x₀
  inl_injective := fun _ _ h ↦ Subtype.ext h
  range_inl_eq_ker_rightHom := by
    ext ξ
    constructor
    · rintro ⟨η, rfl⟩
      exact η.2
    · intro hξ
      exact ⟨⟨ξ, hξ⟩, rfl⟩
  rightHom_surjective := (complexKTheoryDimensionAt_rightInverse X x₀).surjective

/-- The canonical section `ℤ → K(X)` splits the reduced-dimension extension. -/
def complexKTheoryReducedDimensionSplitting
    (X : Type u) [TopologicalSpace X] (x₀ : X) :
    (complexKTheoryReducedDimensionExtension X x₀).Splitting where
  toFun := complexKTheoryIntSection X
  map_zero' := (complexKTheoryIntSection X).map_zero
  map_add' := (complexKTheoryIntSection X).map_add
  rightInverse_rightHom := complexKTheoryDimensionAt_rightInverse X x₀

/-- Subtracting the dimension contribution lands in reduced `K`-theory. -/
def complexKTheoryToReducedProdInt
    (X : Type u) [TopologicalSpace X] (x₀ : X) :
    K(X) →+ K̃(X, x₀) × ℤ where
  toFun := fun ξ ↦
    (⟨ξ - complexKTheoryIntSection X (complexKTheoryDimensionAt X x₀ ξ), by
        rw [mem_reducedComplexKTheory_iff, map_sub,
          complexKTheoryDimensionAt_intSection x₀]
        simp⟩,
      complexKTheoryDimensionAt X x₀ ξ)
  map_zero' := sorry
  map_add' := sorry

/-- The first component of `complexKTheoryToReducedProdInt X x₀ ξ` is represented by subtracting
the integer-dimension summand from `ξ`. -/
theorem complexKTheoryToReducedProdInt_fst_coe
    {X : Type u} [TopologicalSpace X] {x₀ : X} (ξ : K(X)) :
    ((complexKTheoryToReducedProdInt X x₀ ξ).1 : K(X)) =
      ξ - complexKTheoryIntSection X (complexKTheoryDimensionAt X x₀ ξ) := rfl

/-- Recombining a reduced class with an integer recovers a class in `K(X)`. -/
def reducedProdIntToComplexKTheory
    (X : Type u) [TopologicalSpace X] (x₀ : X) :
    K̃(X, x₀) × ℤ →+ K(X) where
  toFun := fun p ↦ p.1.1 + complexKTheoryIntSection X p.2
  map_zero' := sorry
  map_add' := sorry

/-- `reducedProdIntToComplexKTheory X x₀` adds back the integer summand to the reduced class. -/
theorem reducedProdIntToComplexKTheory_apply
    {X : Type u} [TopologicalSpace X] {x₀ : X}
    (p : K̃(X, x₀) × ℤ) :
    reducedProdIntToComplexKTheory X x₀ p = p.1.1 + complexKTheoryIntSection X p.2 := rfl

/-- `complexKTheoryToReducedProdInt` records the reduced part and the dimension part of a class
in `K(X)`. -/
theorem complexKTheoryToReducedProdInt_snd
    {X : Type u} [TopologicalSpace X] {x₀ : X} (ξ : K(X)) :
    (complexKTheoryToReducedProdInt X x₀ ξ).2 = complexKTheoryDimensionAt X x₀ ξ := rfl

/-- Definition 24.1.2 (2): complex topological `K`-theory splits as reduced `K`-theory together
with the integer dimension summand. In the chapter's source-facing compact-based-space setting,
this is the usual splitting for `(X, x₀)`. -/
def complexKTheoryReducedProdIntEquiv
    (X : Type u) [TopologicalSpace X] (x₀ : X) :
    K(X) ≃+ K̃(X, x₀) × ℤ where
  toFun := complexKTheoryToReducedProdInt X x₀
  invFun := reducedProdIntToComplexKTheory X x₀
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- `complexKTheoryReducedProdIntEquiv X x₀` records the reduced class together with the based
dimension of `ξ`. -/
theorem complexKTheoryReducedProdIntEquiv_apply
    {X : Type u} [TopologicalSpace X] {x₀ : X} (ξ : K(X)) :
    complexKTheoryReducedProdIntEquiv X x₀ ξ = complexKTheoryToReducedProdInt X x₀ ξ := rfl

/-- The inverse of `complexKTheoryReducedProdIntEquiv X x₀` recombines the reduced class with the
integer dimension summand. -/
theorem complexKTheoryReducedProdIntEquiv_symm_apply
    {X : Type u} [TopologicalSpace X] {x₀ : X}
    (p : K̃(X, x₀) × ℤ) :
    (complexKTheoryReducedProdIntEquiv X x₀).symm p = reducedProdIntToComplexKTheory X x₀ p := rfl

/-- `complexKTheoryReducedProdIntEquiv` has second component equal to the based dimension map. -/
theorem complexKTheoryReducedProdIntEquiv_snd
    {X : Type u} [TopologicalSpace X] {x₀ : X} (ξ : K(X)) :
    (complexKTheoryReducedProdIntEquiv X x₀ ξ).2 = complexKTheoryDimensionAt X x₀ ξ := rfl
