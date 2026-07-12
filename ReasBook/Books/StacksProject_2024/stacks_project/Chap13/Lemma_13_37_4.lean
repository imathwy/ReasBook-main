import Mathlib
import StacksProject_2024.Chap13.Lemma_13_35_4
import StacksProject_2024.Chap13.Lemma_13_37_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open Opposite
open scoped CategoryTheory.ObjectProperty.GeneratedNotation

noncomputable section

universe w v u

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v w} D]
variable {I : Type w} (E : I → D)

/- Domain-style sampling for Lemma 13.37.4:
- primary domain: compact objects and finitely generated extension stages in a triangulated
  category, expressed through `ObjectProperty`;
- sampled owner declarations:
  `ObjectProperty.objectGeneratedProperty`,
  `ObjectProperty.objectGeneratedProperty_le_iff`,
  `ObjectProperty.objectGeneratedStage`,
  `ObjectProperty.additiveExtensionStage`,
  `CategoryTheory.ObjectProperty.GeneratedNotation`;
- best owner abstraction: the source-facing statement should express the factor object as lying in
  the generated triangulated subcategory `⟨∐ fun j ↦ E (ι j)⟩` attached to a finite coproduct of
  generators, and the stronger stage-level statement should use the canonical coproduct stage
  `⟨∐ fun j ↦ E (ι j)⟩_m`; any finite-family additive-extension presentation is a derived bridge,
  not the public owner;
- primitive-vs-derived split:
  primitive data are the finite index type `J`, the chosen subfamily `ι : J → I`, and the finite
  coproduct `∐ fun j ↦ E (ι j)`;
  derived API is the stage-level witness `⟨∐ fun j ↦ E (ι j)⟩_m A`, whose internal description is
  `additiveExtensionStage ((singleton (∐ fun j ↦ E (ι j))).shiftClosure ℤ) m A`.

Source/core/bridge triage:
- `source-facing`: the compact-factorization theorem for a finite subfamily of generators;
- `core/canonical`: `objectGeneratedProperty` with the textbook notation `⟨-⟩`;
- `bridge/view`: the companion theorem below retains the stronger finite-coproduct stage witness
  `⟨∐ fun j ↦ E (ι j)⟩_m`. -/

-- Proof sketch: first prove the stronger stage-level statement below, producing a factor object in
-- a canonical generated stage `⟨∐ fun j ↦ E (ι j)⟩_m` attached to finitely many chosen generators.
-- Then pass from that stage witness to membership in the generated triangulated subcategory of the
-- same finite coproduct, since `⟨∐ fun j ↦ E (ι j)⟩` is the supremum of its positive stages.
/-- Helper for Lemma 13.37.4: membership in the generated property of a finite generator coproduct
comes from some positive stage of that same coproduct. -/
private theorem finite_generator_coproduct_stage_witness
    {A : D} {J : Type (max u v w)} [Finite J] (ι : J → I)
    (hA : ⟨∐ fun j : J ↦ E (ι j)⟩ A) :
    ∃ m : ℕ+, (⟨∐ fun j : J ↦ E (ι j)⟩_m) A := by
  -- The generated property is the supremum of its positive stages, so membership already carries
  -- the required stage witness.
  rw [objectGeneratedProperty, prop_iSup_iff] at hA
  exact hA

/-- Helper for Lemma 13.37.4: once the factor object lies in the generated property of a finite
generator coproduct, the stage index is extracted by unfolding `⟨-⟩` as a supremum. -/
private theorem stage_factorization_of_generated_factorization
    {X C : D} {f : C ⟶ X}
    (h :
      ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (k : A ⟶ X), g ≫ k = f) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I) (m : ℕ+),
        (⟨∐ fun j : J ↦ E (ι j)⟩_m) A ∧
        ∃ (g : C ⟶ A) (k : A ⟶ X), g ≫ k = f := by
  rcases h with ⟨A, J, hJ, ι, hA, g, k, hgk⟩
  letI : Finite J := hJ
  -- Extract the positive stage witness before returning the same factorization data.
  obtain ⟨m, hm⟩ := finite_generator_coproduct_stage_witness (E := E) ι hA
  exact ⟨A, J, hJ, ι, m, hm, g, k, hgk⟩

/-- Helper for Lemma 13.37.4: a morphism into `X (n + 1)` with zero connecting composite lifts
through the stage map `X n ⟶ X (n + 1)`. -/
private theorem lift_zero_connecting
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (n : ℕ) {d : C ⟶ X (n + 1)} (hd : d ≫ triangleConnecting n = 0) :
    ∃ u : C ⟶ X n, u ≫ map n = d := by
  let T : Triangle D := Triangle.mk (triangleHom n) (map n) (triangleConnecting n)
  have hT : T ∈ distTriang D := by
    simpa [T] using
      IsGeneratingFamilyApproximation.triangleDistinguished (E := E) hR n
  -- Read the vanishing hypothesis as exactness at the third vertex of the approximation triangle.
  obtain ⟨u, hu⟩ := T.coyoneda_exact₃ hT d (by simpa [T] using hd)
  exact ⟨u, by simpa [T] using hu.symm⟩

/-- Helper for Lemma 13.37.4: the source-faithful induction should first factor through an object
of the generated property `⟨∐ fun j ↦ E (ι j)⟩`; the public theorem then extracts the stage
parameter `m`. -/
private theorem compact_factors_through_finite_generator_coproduct_generated
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := by
  -- Route correction: carry the induction in the generated property `⟨F⟩` and extract the
  -- positive stage only after the factor object has been built.
  -- TODO: first prove the compactness bridge for maps `C ⟶ S⟦a⟧`, where `S` is a direct sum of
  -- shifts of the family `E`; then run the source-style triangle induction using
  -- `distinguished_cocone_triangle₂`, `complete_distinguished_triangle_morphism₂`,
  -- `complete_distinguished_triangle_morphism`, and `lift_zero_connecting`.
  -- The remaining source-faithful blocker is the compactness of the cone-side source object `C'`
  -- in the induction step; with only `hR`, the current theorem no longer carries the textbook
  -- hypothesis that the generators `E i` are compact, so the required compactness transfer
  -- cannot presently be justified from the available dependency-closed API.
  sorry

/-- A stage-level strengthening of Lemma 13.37.4: the factor object can be placed in an explicit
generated stage attached to a finite coproduct of chosen generators. -/
theorem compact_factors_through_finite_generator_coproduct_stage
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I) (m : ℕ+),
        (⟨∐ fun j : J ↦ E (ι j)⟩_m) A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := by
  -- Reduce the public stage statement to the generated-property induction and then read off the
  -- stage witness from the definition of `⟨-⟩`.
  exact stage_factorization_of_generated_factorization (E := E) <|
    compact_factors_through_finite_generator_coproduct_generated
      (E := E) hR hC n f

/-- Lemma 13.37.4: let
`X₀ ⟶ X₁ ⟶ X₂ ⟶ ⋯`
be a generating-family approximation as in Lemma `13.37.3`, and let `C` be a compact object.
Then any morphism from `C` to the stage `X n` factors through an object of the generated
triangulated subcategory `⟨E_{i₁} ⊕ ⋯ ⊕ E_{i_t}⟩` for some finite subfamily of the generators.
Here `X 0` corresponds to the textbook object `X₁`. -/
theorem compact_factors_through_finite_generator_stage
    {X : ℕ → D} {map : ∀ n : ℕ, X n ⟶ X (n + 1)} {Y : ℕ → D}
    {triangleHom : ∀ n : ℕ, Y n ⟶ X n}
    {triangleConnecting : ∀ n : ℕ, X (n + 1) ⟶ (Y n)⟦(1 : ℤ)⟧}
    (hR : IsGeneratingFamilyApproximation E X map Y triangleHom triangleConnecting) {C : D}
    (hC : IsCompactObject C) (n : ℕ) (f : C ⟶ X n) :
    ∃ (A : D) (J : Type (max u v w)) (_ : Finite J) (ι : J → I),
        ⟨∐ fun j : J ↦ E (ι j)⟩ A ∧
        ∃ (g : C ⟶ A) (h : A ⟶ X n), g ≫ h = f := by
  rcases compact_factors_through_finite_generator_coproduct_stage E hR hC n f with
    ⟨A, J, hJ, ι, m, hA, g, h, hgf⟩
  refine ⟨A, J, hJ, ι, ?_, g, h, hgf⟩
  rw [objectGeneratedProperty, prop_iSup_iff]
  exact ⟨m, hA⟩

end
