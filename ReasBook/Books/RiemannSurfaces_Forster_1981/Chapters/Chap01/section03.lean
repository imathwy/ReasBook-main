import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_1_3 (from Chap01) -/
open scoped Manifold

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `mem_maximalAtlas_iff`, `StructureGroupoid.maximalAtlas`, `atlas`.
- Verified locally: `biholomorphicGroupoid`, `holomorphicallyCompatible`,
  `StructureGroupoid.subset_maximalAtlas`, `analyticallyEquivalent`.
- Owner choice: Definition 1.3 is a canonical-recall/bridge item on the ambient
  `[ChartedSpace ℂ X]` and `[HasGroupoid X biholomorphicGroupoid]` surface, with maximal atlas
  `biholomorphicGroupoid.maximalAtlas X`.
-/

/- In this development, a complex structure on `X` is represented canonically by a chosen complex
atlas `[ChartedSpace ℂ X]`, with analytic equivalence tracked by `analyticallyEquivalent` and
biholomorphic compatibility recorded by `[HasGroupoid X biholomorphicGroupoid]`. The unique
maximal atlas attached to that choice is `biholomorphicGroupoid.maximalAtlas X`. -/

/-- Definition 1.3 (1): a complex chart lies in the biholomorphic maximal atlas exactly when it is
holomorphically compatible, in both directions, with every chart of the chosen complex atlas. -/
theorem memBiholomorphicMaximalAtlas_iff {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    {e : OpenPartialHomeomorph X ℂ} :
    e ∈ biholomorphicGroupoid.maximalAtlas X ↔
      ∀ e' ∈ atlas ℂ X, holomorphicallyCompatible e e' ∧ holomorphicallyCompatible e' e :=
  Iff.rfl

/-- Definition 1.3 (2): any chosen complex atlas is contained in its biholomorphic maximal atlas. -/
theorem complexAtlas_subset_biholomorphicMaximalAtlas {X : Type u} [TopologicalSpace X]
    [ChartedSpace ℂ X] [HasGroupoid X biholomorphicGroupoid] :
    atlas ℂ X ⊆ biholomorphicGroupoid.maximalAtlas X :=
  biholomorphicGroupoid.subset_maximalAtlas

/-! ### Exercise_1_3 (from Chap01) -/
open scoped Manifold OnePoint

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `onePointEquivSphereOfFinrankEq`, `stereographic'`,
  `Matrix.specialOrthogonalGroup`.
- Verified locally: `Matrix.specialOrthogonalGroup`, `onePointEquivSphereOfFinrankEq`,
  and `Matrix.mulVec`.
- Owner choice: model `ℙ¹(ℂ)` as `OnePoint ℂ`, use the canonical `Matrix.specialOrthogonalGroup`
  owner for `SO(3)`, and express biholomorphicity by `Structomorph biholomorphicGroupoid`.
-/

/-- The dimension count identifying the one-point compactification of `ℂ` with the unit sphere in
`ℝ³`. -/
private theorem complex_finrank_add_one_eq_fin3 :
    Module.finrank ℝ ℂ + 1 = Fintype.card (Fin 3) := sorry

/-- The stereographic identification of the unit sphere in `ℝ³` with the Riemann sphere
`ℙ¹(ℂ) = OnePoint ℂ`. -/
private def stereographicProjectionComplexHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ OnePoint ℂ :=
  (onePointEquivSphereOfFinrankEq complex_finrank_add_one_eq_fin3).symm

/-- A special orthogonal matrix preserves the unit sphere in `ℝ³`. -/
private theorem specialOrthogonalGroup_maps_unitSphere
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Matrix.toEuclideanLin A.1 x.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := sorry

/-- The self-map of the Riemann sphere obtained by conjugating a rotation of `S²` by the
stereographic projection. -/
def rotationOnRiemannSphere (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    OnePoint ℂ → OnePoint ℂ :=
  fun z ↦
    let σ := stereographicProjectionComplexHomeomorph
    σ
      ⟨Matrix.toEuclideanLin A.1 (σ.symm z).1,
        specialOrthogonalGroup_maps_unitSphere A (σ.symm z)⟩

/-- The defining conjugation formula for `rotationOnRiemannSphere`. -/
theorem rotationOnRiemannSphere_def (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (z : OnePoint ℂ) :
    rotationOnRiemannSphere A z =
      let σ := stereographicProjectionComplexHomeomorph
      σ
        ⟨Matrix.toEuclideanLin A.1 (σ.symm z).1,
          specialOrthogonalGroup_maps_unitSphere A (σ.symm z)⟩ := rfl

/-- The rotation of the Riemann sphere induced by `A ∈ SO(3)` as a homeomorphism. -/
def rotationOnRiemannSphereHomeomorph (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    OnePoint ℂ ≃ₜ OnePoint ℂ where
  toEquiv :=
    { toFun := rotationOnRiemannSphere A
      invFun := rotationOnRiemannSphere A⁻¹
      left_inv := by
        sorry
      right_inv := by
        sorry }
  continuous_toFun := by
    sorry
  continuous_invFun := by
    sorry

/-- Exercise 1.3: after identifying `ℙ¹(ℂ)` with the unit sphere in `ℝ³` by stereographic
projection, every rotation `A ∈ SO(3)` induces a bundled biholomorphic self-map
`σ ∘ A ∘ σ⁻¹ : ℙ¹(ℂ) → ℙ¹(ℂ)`. -/
def rotationOnRiemannSphereStructomorph (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Structomorph biholomorphicGroupoid (OnePoint ℂ) (OnePoint ℂ) where
  toHomeomorph := rotationOnRiemannSphereHomeomorph A
  mem_groupoid := by
    sorry

@[simp] theorem rotationOnRiemannSphereStructomorph_apply
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (z : OnePoint ℂ) :
    (rotationOnRiemannSphereStructomorph A).toHomeomorph z = rotationOnRiemannSphere A z :=
  rfl

/-- The underlying map of the induced rotation structomorphism of the Riemann sphere is
holomorphic. -/
theorem rotationOnRiemannSphere_holomorphic
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    RiemannSurface.Holomorphic (rotationOnRiemannSphere A) := by
  simpa using
    RiemannSurface.structomorph_holomorphic (rotationOnRiemannSphereStructomorph A)
