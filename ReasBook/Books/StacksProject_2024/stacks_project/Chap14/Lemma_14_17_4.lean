import StacksProject_2024.stacks_project.Chap14.Definition_14_17_1
import StacksProject_2024.stacks_project.Chap14.Lemma_14_13_4
import StacksProject_2024.stacks_project.Chap14.Lemma_14_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.17.4:
- primary domain: representable simplicial mapping-object presheaves;
- sampled owner-style declarations:
  `Functor.IsRepresentable`,
  `Functor.representableBy`,
  `simplicialHomPresheaf`,
  `simplicialHom`;
- best owner abstraction: the source-facing owner remains `simplicialHomPresheaf U V`, and the
  file’s main content is the owner predicate `(simplicialHomPresheaf U V).IsRepresentable`;
- primitive data: the simplicial set `U`, the target simplicial object `V`, the degreewise
  finiteness family on `U`, a `0`-simplex of `U`, and the eventual degeneracy hypothesis;
- derived API: the source-facing representability theorem and its `Fact`-packaged instance.

Any later comparison between concrete representing objects should be expressed through the
canonical owner API `Functor.RepresentableBy.uniqueUpToIso` or `Functor.RepresentableBy.isoReprX`,
not by introducing a parallel local chosen-object wrapper here. -/

-- Proof sketch: evaluate the presheaf `W ↦ Mor(W × U, V)` degreewise at each simplex `[n]`.
-- Lemma `14.17.3` gives representability of the resulting `C`-valued presheaf
-- `X ↦ Mor(X × (U ⊗ Δ[n]), V)`, and Lemma `14.13.4` identifies maps out of `X × Δ[n]` with maps
-- into the `n`-th component, allowing these representing objects to assemble into a simplicial
-- object. This yields representability of `simplicialHomPresheaf U V`.
section EventuallyDegenerate

variable [HasBinaryCoproducts C] [HasFiniteLimits C]
variable (U : SSet.{w}) [∀ Δ : SimplexCategoryᵒᵖ, Finite (U.obj Δ)] [Nonempty (U _⦋0⦌)]
variable (V : SimplicialObject C)

/-- Helper for Lemma 14.17.4: the standard simplex has enough finite nonempty fibers to build
the coproducts needed by `stdSimplexProductHomEquiv`. -/
private instance stdSimplex_hasCoproducts (k : ℕ) (X : C) :
    ∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ X) := by
  intro Δ
  -- Proof comment: every standard simplex degree has a constant simplex, so the finite-family
  -- coproduct instance from Definition `14.17.1` applies directly.
  letI : Nonempty ((Δ[k] : SSet.{w}).obj Δ) := ⟨SSet.stdSimplex.const k 0 Δ⟩
  infer_instance

/-- Helper for Lemma 14.17.4: tensoring `U` with a standard simplex preserves the eventual
degeneracy bound needed to invoke Lemma `14.17.3` degreewise. -/
private theorem tensor_stdSimplex_eventually_degenerate (n : ℕ)
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    ∃ e : ℕ, (U ⊗ Δ[n]).HasDimensionLE e := by
  -- Proof comment: combine the given bound for `U` with the standard dimension bound for `Δ[n]`
  -- through the product formula `SSet.hasDimensionLE_prod`.
  rcases hU with ⟨d, hd⟩
  letI : U.HasDimensionLE d := hd
  refine ⟨d + n, ?_⟩
  exact SSet.hasDimensionLE_prod U (Δ[n] : SSet.{w}) d n (d + n)

/-- Helper for Lemma 14.17.4: in each simplicial degree `n`, Lemma `14.17.3` represents the
restricted presheaf attached to `U ⊗ Δ[n]`. -/
private theorem tensor_stdSimplex_const_hom_presheaf_isRepresentable (n : ℕ)
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (((SimplicialObject.const C).op ⋙ simplicialHomPresheaf (U ⊗ Δ[n]) V)).IsRepresentable := by
  -- Proof comment: this is exactly the previous lemma plus Lemma `14.17.3` applied to the
  -- tensor product source simplicial set.
  exact simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate
    (U ⊗ Δ[n]) V (tensor_stdSimplex_eventually_degenerate (U := U) n hU)

/-- Helper for Lemma 14.17.4: when the target simplicial object is constant, the tensor source
`U ⊗ Δ[n]` still has the finite nonempty coproducts needed for simplicial copowers. -/
private instance tensor_stdSimplex_const_hasCoproducts (n : ℕ) (X : C) :
    ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct
        (fun _ : (U ⊗ Δ[n] : SSet.{w}).obj Δ ↦ ((SimplicialObject.const C).obj X).obj Δ) := by
  intro Δ
  letI : Nonempty ((U ⊗ Δ[n] : SSet.{w}).obj Δ) :=
    nonempty_obj_of_nonempty_zero (U := U ⊗ Δ[n]) Δ
  change HasCoproduct (fun _ : (U ⊗ Δ[n] : SSet.{w}).obj Δ ↦ X)
  infer_instance

/-- Helper for Lemma 14.17.4: the degree indexed by `Δ` is represented by the constant-object
restriction for `U ⊗ Δ[len]`. -/
private noncomputable abbrev eventually_degenerate_mapping_object_obj
    (Δ : SimplexCategoryᵒᵖ) (hU : ∃ d : ℕ, U.HasDimensionLE d) : C :=
  @Functor.reprX _ _ ((((SimplicialObject.const C).op ⋙
      simplicialHomPresheaf (U ⊗ Δ[Δ.unop.len]) V)))
    (tensor_stdSimplex_const_hom_presheaf_isRepresentable (U := U) (V := V) Δ.unop.len hU)

/-- Helper for Lemma 14.17.4: the canonical representing equivalence for the degree indexed by
`Δ`. -/
private noncomputable abbrev eventually_degenerate_mapping_object_degreeRepresentable
    (Δ : SimplexCategoryᵒᵖ) (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    ((((SimplicialObject.const C).op ⋙
        simplicialHomPresheaf (U ⊗ Δ[Δ.unop.len]) V))).RepresentableBy
      (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU) :=
  @Functor.representableBy _ _ ((((SimplicialObject.const C).op ⋙
      simplicialHomPresheaf (U ⊗ Δ[Δ.unop.len]) V)))
    (tensor_stdSimplex_const_hom_presheaf_isRepresentable (U := U) (V := V) Δ.unop.len hU)

/-- Helper for Lemma 14.17.4: the source-side simplex operator induces the corresponding tensor
reindexing map `U ⊗ Δ[Δ₂] ⟶ U ⊗ Δ[Δ₁]`. -/
private noncomputable abbrev eventually_degenerate_mapping_reindex
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    U ⊗ Δ[Δ₂.unop.len] ⟶ U ⊗ Δ[Δ₁.unop.len] :=
  tensorHom (𝟙 U) (SSet.stdSimplex.map σ.unop)

/-- Helper for Lemma 14.17.4: evaluation on the distinguished simplex of `Δ[k]` is natural in
the object variable. -/
private theorem stdSimplexProductHomEquiv_naturality
    (k : ℕ) {X Y : C} (f : X ⟶ Y) (W : SimplicialObject C)
    (γ : ((Δ[k] : SSet.{w}) × (SimplicialObject.const C).obj Y) ⟶ W) :
    stdSimplexProductHomEquiv k X W
        (simplicialCopowerHom (Δ[k] : SSet.{w}) ((SimplicialObject.const C).map f) ≫ γ) =
      f ≫ stdSimplexProductHomEquiv k Y W γ := by
  -- Proof comment: both sides evaluate `γ` on the identity simplex of `Δ[k]`; the only new
  -- source-side contribution is precomposition by `f` on the chosen coproduct summand.
  rw [stdSimplexProductHomEquiv_apply, stdSimplexProductHomEquiv_apply]
  simp [simplicialCopowerHom_app]

/-- Helper for Lemma 14.17.4: on the constant-object restriction for `U ⊗ Δ[n]`, a morphism
`f : X ⟶ Y` acts by precomposition with the induced map on simplicial copowers. -/
private theorem tensor_stdSimplex_const_hom_presheaf_map_app
    (n : ℕ) {X Y : C} (f : X ⟶ Y)
    (γ : (((SimplicialObject.const C).op ⋙ simplicialHomPresheaf (U ⊗ Δ[n]) V).obj
      (Opposite.op Y))) :
    (((SimplicialObject.const C).op ⋙ simplicialHomPresheaf (U ⊗ Δ[n]) V).map f.op γ) =
      simplicialCopowerHom (U ⊗ Δ[n]) ((SimplicialObject.const C).map f) ≫ γ :=
  rfl

/-- Helper for Lemma 14.17.4: reindexing the degreewise representing objects along a simplex map.
This is the source-faithful bridge from `Δ₂ → Δ₁` on standard simplices to the induced map on the
degree-`Δᵢ` representers. -/
private noncomputable def eventually_degenerate_mapping_object_map
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂)
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU ⟶
      eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU :=
  -- Proof comment: define the map as the preimage, under the degree-`Δ₂` representing
  -- equivalence, of precomposition along the source-side reindexing
  -- `U ⊗ Δ[Δ₂] ⟶ U ⊗ Δ[Δ₁]`.
  (eventually_degenerate_mapping_object_degreeRepresentable
      (U := U) (V := V) Δ₂ hU).homEquiv.symm
    (simplicialCopowerIndexHom
        ((SimplicialObject.const C).obj
          (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
        (eventually_degenerate_mapping_reindex (U := U) σ) ≫
      (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₁ hU).homEquiv (𝟙 _))

/-- Helper for Lemma 14.17.4: the reindexing map is characterized by the expected formula after
applying the codomain degreewise representing equivalence. -/
private theorem eventually_degenerate_mapping_object_map_homEquiv
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂)
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₂ hU).homEquiv
        (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU) =
      simplicialCopowerIndexHom
          ((SimplicialObject.const C).obj
            (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
          (eventually_degenerate_mapping_reindex (U := U) σ) ≫
        (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ₁ hU).homEquiv (𝟙 _) := by
  -- Proof comment: this is immediate from the definition as `homEquiv.symm` of the displayed
  -- source-side precomposition map.
  exact Equiv.apply_symm_apply
    ((eventually_degenerate_mapping_object_degreeRepresentable
      (U := U) (V := V) Δ₂ hU).homEquiv)
    _

/-- Helper for Lemma 14.17.4: the degreewise reindexing maps satisfy the identity law. -/
private theorem eventually_degenerate_mapping_object_map_id
    (Δ : SimplexCategoryᵒᵖ) (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    eventually_degenerate_mapping_object_map (U := U) (V := V) (𝟙 Δ) hU = 𝟙 _ := by
  -- Proof comment: the remaining gap is to rewrite the tensor-side identity reindexing through
  -- the chosen representing equivalence.
  sorry

/-- Helper for Lemma 14.17.4: the degreewise reindexing maps compose exactly as the simplex maps
do. -/
private theorem eventually_degenerate_mapping_object_map_comp
    {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) (τ : Δ₂ ⟶ Δ₃)
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    eventually_degenerate_mapping_object_map (U := U) (V := V) (σ ≫ τ) hU =
      eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU ≫
        eventually_degenerate_mapping_object_map (U := U) (V := V) τ hU := by
  -- Proof comment: the remaining gap is the transport-stable composition identity for the source
  -- reindexing maps under the codomain representing equivalence.
  sorry

/-- Helper for Lemma 14.17.4: assemble the degreewise representing objects into the simplicial
mapping object predicted by the source proof. -/
private noncomputable def eventually_degenerate_mapping_object
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    SimplicialObject C where
  obj Δ := eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU
  map σ := eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU
  map_id := fun Δ ↦ eventually_degenerate_mapping_object_map_id (U := U) (V := V) Δ hU
  map_comp := fun σ τ ↦
    eventually_degenerate_mapping_object_map_comp (U := U) (V := V) σ τ hU

/-- Lemma 14.17.4: if `C` has binary coproducts and finite limits, if `U` is degreewise finite
with a `0`-simplex, and if all sufficiently high simplices of `U` are degenerate, then the presheaf
`W ↦ Mor_{Simp(C)}(W × U, V)` is representable. Equivalently, the simplicial mapping object
`simplicialHom U V` exists. -/
theorem simplicialHomPresheaf_isRepresentable_of_eventually_degenerate
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (simplicialHomPresheaf U V).IsRepresentable := by
  -- Route correction: keep the source-faithful degreewise construction from Lemma `14.17.3`,
  -- and avoid introducing a parallel constant-presheaf witness inside this file.
  -- TODO: the degreewise representers are now assembled into
  -- `eventually_degenerate_mapping_object U V hU`. The remaining source-faithful work is to
  -- define the two global maps
  -- `(W ⟶ eventually_degenerate_mapping_object U V hU) → (U × W ⟶ V)` and
  -- `(U × W ⟶ V) → (W ⟶ eventually_degenerate_mapping_object U V hU)` using
  -- `stdSimplexProductHomEquiv`, then prove they are inverse.
  sorry

instance simplicialHomPresheaf_isRepresentable_of_fact_eventually_degenerate
    [Fact (∃ d : ℕ, U.HasDimensionLE d)] :
    (simplicialHomPresheaf U V).IsRepresentable :=
  simplicialHomPresheaf_isRepresentable_of_eventually_degenerate U V Fact.out

end EventuallyDegenerate

end CategoryTheory
