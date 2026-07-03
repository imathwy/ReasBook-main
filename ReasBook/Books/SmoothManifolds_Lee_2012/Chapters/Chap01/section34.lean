

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_1_34 (from Chap01/Sec01_04) -/
open scoped Manifold Torus

universe u v w

/- Example 1.34 (1): this source-facing smooth product statement is the `ℝ`-specialization of the
canonical finite-product manifold owner `instIsManifoldPi`. -/
example
    {ι : Type u} [Fintype ι]
    {E : ι → Type v} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    {H : ι → Type w} [∀ i, TopologicalSpace (H i)]
    {I : ∀ i, ModelWithCorners ℝ (E i) (H i)}
    {M : ι → Type w} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace (H i) (M i)]
    [∀ i, IsManifold (I i) (⊤ : WithTop ℕ∞) (M i)] :
    IsManifold (ModelWithCorners.pi I) (⊤ : WithTop ℕ∞) (∀ i, M i) :=
  instIsManifoldPi

variable (n : ℕ) in
/- Example 1.34 (2): the `n`-torus, represented as the product of `n` copies of `Circle`, carries
the canonical product smooth manifold structure. -/
#check (inferInstance :
  IsManifold (ModelWithCorners.pi fun _ : Fin n ↦ 𝓡 1) (⊤ : WithTop ℕ∞) (𝕋^{n}))
