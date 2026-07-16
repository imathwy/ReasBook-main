import stacks_proof.stacks_project.Chap14.Definition_14_17_1
import stacks_proof.stacks_project.Chap14.Lemma_14_13_4
import stacks_proof.stacks_project.Chap14.Lemma_14_17_3
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Chap14 Lemma 14 17 4: the simplex-side reindexing map is the identity for the
identity simplex operator. -/
private theorem eventually_degenerate_mapping_reindex_id
    (Δ : SimplexCategoryᵒᵖ) :
    eventually_degenerate_mapping_reindex (U := U) (𝟙 Δ) =
      𝟙 (U ⊗ Δ[Δ.unop.len]) := by
  -- Proof comment: `eventually_degenerate_mapping_reindex` is the tensor of identities on `U`
  -- and on the standard simplex, so the monoidal identity law gives the result.
  simp [eventually_degenerate_mapping_reindex]

/-- Helper for Chap14 Lemma 14 17 4: the simplex-side reindexing map is contravariantly
compatible with composition. -/
private theorem eventually_degenerate_mapping_reindex_comp
    {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) (τ : Δ₂ ⟶ Δ₃) :
    eventually_degenerate_mapping_reindex (U := U) (σ ≫ τ) =
      eventually_degenerate_mapping_reindex (U := U) τ ≫
        eventually_degenerate_mapping_reindex (U := U) σ := by
  -- Proof comment: the reindexing map is the tensor of `𝟙 U` with the standard-simplex map, and
  -- `Functor.map_comp` plus the monoidal tensor-composition law compute that tensor composite.
  simp [eventually_degenerate_mapping_reindex, Functor.map_comp]

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

/-- Helper for Chap14 Lemma 14 17 4: the codomain universal element normalizes to the
source-side reindexing composite after applying the degreewise map induced by `σ`. -/
private theorem eventually_degenerate_mapping_object_map_universalElement
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂)
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
        ((SimplicialObject.const C).map
          (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU)) ≫
      (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₂ hU).homEquiv (𝟙 _) =
    simplicialCopowerIndexHom
        ((SimplicialObject.const C).obj
          (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
        (eventually_degenerate_mapping_reindex (U := U) σ) ≫
      (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₁ hU).homEquiv (𝟙 _) := by
  -- Proof comment: rewrite the left-hand side by the representer naturality formula
  -- `homEquiv_comp`, then unfold the defining image of `eventually_degenerate_mapping_object_map`.
  have hComp :
      simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
          ((SimplicialObject.const C).map
            (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU)) ≫
        (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ₂ hU).homEquiv (𝟙 _) =
      (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₂ hU).homEquiv
          (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU) := by
    simpa [tensor_stdSimplex_const_hom_presheaf_map_app, Category.comp_id] using
      ((eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₂ hU).homEquiv_comp
          (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU)
          (𝟙 _)).symm
  exact hComp.trans <| by
    simpa using
      eventually_degenerate_mapping_object_map_homEquiv (U := U) (V := V) σ hU

/-- Helper for Chap14 Lemma 14 17 4: the universal element of the degreewise representer can be
written using the explicit carrier `eventually_degenerate_mapping_object_obj`. -/
private theorem eventually_degenerate_mapping_object_degreeRepresentable_universalElement_eq
    {Δ : SimplexCategoryᵒᵖ} (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ hU).homEquiv
        (𝟙 (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU)) =
      (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ hU).homEquiv (𝟙 _) := by
  -- Proof comment: both sides are definitionally the same universal element; this lemma fixes
  -- the explicit carrier spelling so later rewrites do not depend on hidden inference.
  rfl

/-- Helper for Chap14 Lemma 14 17 4: postcomposing the degreewise universal element preserves the
explicit-carrier normalization fixed above. -/
private theorem eventually_degenerate_mapping_object_degreeRepresentable_universalElement_assoc
    {Δ : SimplexCategoryᵒᵖ} (hU : ∃ d : ℕ, U.HasDimensionLE d) {A : SimplicialObject C}
    (k :
      A ⟶
        (U ⊗ Δ[Δ.unop.len]) ×
          (SimplicialObject.const C).obj
            (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU)) :
    k ≫
        (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ hU).homEquiv
          (𝟙 (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU)) =
      k ≫
        (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ hU).homEquiv
          (𝟙 _) := by
  -- Proof comment: the explicit and implicit carrier spellings of the universal element are
  -- equal, so postcomposition by any `k` preserves that normalization.
  exact
    congrArg (fun t ↦ k ≫ t)
      (eventually_degenerate_mapping_object_degreeRepresentable_universalElement_eq
        (U := U) (V := V) (Δ := Δ) hU)

/-- Helper for Lemma 14.17.4: the degreewise reindexing maps satisfy the identity law. -/
private theorem eventually_degenerate_mapping_object_map_id
    (Δ : SimplexCategoryᵒᵖ) (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    eventually_degenerate_mapping_object_map (U := U) (V := V) (𝟙 Δ) hU = 𝟙 _ := by
  -- Proof comment: push the claim through the degree-`Δ` representing equivalence, where the
  -- left-hand side is the source-side identity reindexing map and the right-hand side is the
  -- universal element of the same representer.
  apply
    (eventually_degenerate_mapping_object_degreeRepresentable
      (U := U) (V := V) Δ hU).homEquiv.injective
  -- Proof comment: after translating through `homEquiv`, the left side is the identity
  -- reindexing map on the simplicial copower, so the goal reduces to the copower identity law.
  rw [eventually_degenerate_mapping_object_map_homEquiv]
  rw [eventually_degenerate_mapping_reindex_id]
  rw [simplicialCopowerIndexHom_id]
  simpa using
    (eventually_degenerate_mapping_object_degreeRepresentable_universalElement_assoc
      (U := U) (V := V) (Δ := Δ) hU
      (k := 𝟙
        ((U ⊗ Δ[Δ.unop.len]) ×
          (SimplicialObject.const C).obj
            (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU)))).symm

/-- Helper for Lemma 14.17.4: the degreewise reindexing maps compose exactly as the simplex maps
do. -/
private theorem eventually_degenerate_mapping_object_map_comp
    {Δ₁ Δ₂ Δ₃ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) (τ : Δ₂ ⟶ Δ₃)
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    eventually_degenerate_mapping_object_map (U := U) (V := V) (σ ≫ τ) hU =
      eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU ≫
        eventually_degenerate_mapping_object_map (U := U) (V := V) τ hU := by
  -- Proof comment: evaluate both sides in the degree-`Δ₃` representer. After that, the target
  -- composite is the canonical source-side precomposition chain, so only the reindexing
  -- composition law and the standard copower naturality square remain.
  -- Route correction: normalize the codomain universal element with `homEquiv_comp` before using
  -- the copower naturality square, rather than transporting with `homEquiv_eq`.
  apply
    (eventually_degenerate_mapping_object_degreeRepresentable
      (U := U) (V := V) Δ₃ hU).homEquiv.injective
  -- Proof comment: the left side is already the expected source-side reindexing composite after
  -- `homEquiv`, while the right side is rewritten using `homEquiv_comp`.
  have hComp :
      (eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₃ hU).homEquiv
          (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU ≫
            eventually_degenerate_mapping_object_map (U := U) (V := V) τ hU) =
        simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
            ((SimplicialObject.const C).map
              (eventually_degenerate_mapping_object_map
                (U := U) (V := V) σ hU)) ≫
          (eventually_degenerate_mapping_object_degreeRepresentable
            (U := U) (V := V) Δ₃ hU).homEquiv
            (eventually_degenerate_mapping_object_map (U := U) (V := V) τ hU) := by
    -- Proof comment: this is the representer naturality formula specialized to the degree-`Δ₃`
    -- representer, written in the explicit simplicial-copower spelling of the presheaf map.
    simpa [tensor_stdSimplex_const_hom_presheaf_map_app, Category.assoc] using
      ((eventually_degenerate_mapping_object_degreeRepresentable
        (U := U) (V := V) Δ₃ hU).homEquiv_comp
          (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU)
          (eventually_degenerate_mapping_object_map (U := U) (V := V) τ hU))
  -- Proof comment: commute the simplicial-copower map past the simplex reindexing square,
  -- then rewrite the remaining universal element by the map formula for `σ`.
  have hNat :=
    (simplicialCopowerIndexHom_naturality
      (X := (SimplicialObject.const C).obj
        (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
      (Y := (SimplicialObject.const C).obj
        (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))
      (eventually_degenerate_mapping_reindex (U := U) τ)
      ((SimplicialObject.const C).map
        (eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU))).w
  have hNatExplicit :
      ((simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
            (eventually_degenerate_mapping_reindex (U := U) τ) ≫
          simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
            ((SimplicialObject.const C).map
              (eventually_degenerate_mapping_object_map
                (U := U) (V := V) σ hU))) ≫
        (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ₂ hU).homEquiv
          (𝟙
            (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))) =
      ((simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
            ((SimplicialObject.const C).map
              (eventually_degenerate_mapping_object_map
                (U := U) (V := V) σ hU)) ≫
          simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))
            (eventually_degenerate_mapping_reindex (U := U) τ)) ≫
        (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ₂ hU).homEquiv
          (𝟙
            (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))) := by
    exact
      congrArg
        (fun k =>
          k ≫
            (eventually_degenerate_mapping_object_degreeRepresentable
              (U := U) (V := V) Δ₂ hU).homEquiv
              (𝟙
                (eventually_degenerate_mapping_object_obj
                  (U := U) (V := V) Δ₂ hU)))
        hNat.symm
  have hChain :
      (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ₃ hU).homEquiv
          (eventually_degenerate_mapping_object_map (U := U) (V := V) (σ ≫ τ) hU) =
        simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
            ((SimplicialObject.const C).map
              (eventually_degenerate_mapping_object_map
                (U := U) (V := V) σ hU)) ≫
          (eventually_degenerate_mapping_object_degreeRepresentable
            (U := U) (V := V) Δ₃ hU).homEquiv
            (eventually_degenerate_mapping_object_map (U := U) (V := V) τ hU) := by
    calc
      (eventually_degenerate_mapping_object_degreeRepresentable
          (U := U) (V := V) Δ₃ hU).homEquiv
          (eventually_degenerate_mapping_object_map (U := U) (V := V) (σ ≫ τ) hU) =
        simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
            (eventually_degenerate_mapping_reindex (U := U) (σ ≫ τ)) ≫
          (eventually_degenerate_mapping_object_degreeRepresentable
            (U := U) (V := V) Δ₁ hU).homEquiv
            (𝟙 _) := by
              simpa using
                eventually_degenerate_mapping_object_map_homEquiv
                  (U := U) (V := V) (σ ≫ τ) hU
      _ =
        simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
            (eventually_degenerate_mapping_reindex (U := U) τ ≫
              eventually_degenerate_mapping_reindex (U := U) σ) ≫
          (eventually_degenerate_mapping_object_degreeRepresentable
            (U := U) (V := V) Δ₁ hU).homEquiv
            (𝟙 _) := by
              rw [eventually_degenerate_mapping_reindex_comp]
      _ =
        (simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
            (eventually_degenerate_mapping_reindex (U := U) τ) ≫
          simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
            (eventually_degenerate_mapping_reindex (U := U) σ)) ≫
          (eventually_degenerate_mapping_object_degreeRepresentable
            (U := U) (V := V) Δ₁ hU).homEquiv
            (𝟙 _) := by
              rw [simplicialCopowerIndexHom_comp]
      _ =
        simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
            (eventually_degenerate_mapping_reindex (U := U) τ) ≫
          (simplicialCopowerIndexHom
              ((SimplicialObject.const C).obj
                (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
              (eventually_degenerate_mapping_reindex (U := U) σ) ≫
            (eventually_degenerate_mapping_object_degreeRepresentable
              (U := U) (V := V) Δ₁ hU).homEquiv
              (𝟙 _)) := by
                simp [Category.assoc]
      _ =
        simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
            (eventually_degenerate_mapping_reindex (U := U) τ) ≫
          (simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
              ((SimplicialObject.const C).map
                (eventually_degenerate_mapping_object_map
                  (U := U) (V := V) σ hU)) ≫
            (eventually_degenerate_mapping_object_degreeRepresentable
              (U := U) (V := V) Δ₂ hU).homEquiv
              (𝟙 _)) := by
                simpa [Category.assoc] using
                  congrArg
                    (fun k =>
                      simplicialCopowerIndexHom
                          ((SimplicialObject.const C).obj
                            (eventually_degenerate_mapping_object_obj
                              (U := U) (V := V) Δ₁ hU))
                          (eventually_degenerate_mapping_reindex (U := U) τ) ≫
                        k)
                    (eventually_degenerate_mapping_object_map_universalElement
                      (U := U) (V := V) σ hU).symm
      _ =
        (simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
            ((SimplicialObject.const C).map
              (eventually_degenerate_mapping_object_map
                (U := U) (V := V) σ hU)) ≫
          simplicialCopowerIndexHom
            ((SimplicialObject.const C).obj
              (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))
            (eventually_degenerate_mapping_reindex (U := U) τ)) ≫
          (eventually_degenerate_mapping_object_degreeRepresentable
            (U := U) (V := V) Δ₂ hU).homEquiv
            (𝟙 _) := by
              calc
                simplicialCopowerIndexHom
                    ((SimplicialObject.const C).obj
                      (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
                    (eventually_degenerate_mapping_reindex (U := U) τ) ≫
                  simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
                    ((SimplicialObject.const C).map
                      (eventually_degenerate_mapping_object_map
                        (U := U) (V := V) σ hU)) ≫
                  (eventually_degenerate_mapping_object_degreeRepresentable
                    (U := U) (V := V) Δ₂ hU).homEquiv
                    (𝟙 _) =
                (simplicialCopowerIndexHom
                    ((SimplicialObject.const C).obj
                      (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
                    (eventually_degenerate_mapping_reindex (U := U) τ) ≫
                  simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
                    ((SimplicialObject.const C).map
                      (eventually_degenerate_mapping_object_map
                        (U := U) (V := V) σ hU))) ≫
                  (eventually_degenerate_mapping_object_degreeRepresentable
                    (U := U) (V := V) Δ₂ hU).homEquiv
                    (𝟙 _) := by
                      simp [Category.assoc]
                _ =
                  ((simplicialCopowerIndexHom
                      ((SimplicialObject.const C).obj
                        (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU))
                      (eventually_degenerate_mapping_reindex (U := U) τ) ≫
                    simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
                      ((SimplicialObject.const C).map
                        (eventually_degenerate_mapping_object_map
                          (U := U) (V := V) σ hU))) ≫
                    (eventually_degenerate_mapping_object_degreeRepresentable
                      (U := U) (V := V) Δ₂ hU).homEquiv
                      (𝟙
                        (eventually_degenerate_mapping_object_obj
                          (U := U) (V := V) Δ₂ hU))) := by
                        simpa [Category.assoc] using
                          (eventually_degenerate_mapping_object_degreeRepresentable_universalElement_assoc
                            (U := U) (V := V) (Δ := Δ₂) hU
                            (k :=
                              simplicialCopowerIndexHom
                                  ((SimplicialObject.const C).obj
                                    (eventually_degenerate_mapping_object_obj
                                      (U := U) (V := V) Δ₁ hU))
                                  (eventually_degenerate_mapping_reindex (U := U) τ) ≫
                                simplicialCopowerHom (U ⊗ Δ[Δ₂.unop.len])
                                  ((SimplicialObject.const C).map
                                    (eventually_degenerate_mapping_object_map
                                      (U := U) (V := V) σ hU)))).symm
                _ =
                  (simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
                      ((SimplicialObject.const C).map
                        (eventually_degenerate_mapping_object_map
                          (U := U) (V := V) σ hU)) ≫
                    simplicialCopowerIndexHom
                      ((SimplicialObject.const C).obj
                        (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))
                      (eventually_degenerate_mapping_reindex (U := U) τ)) ≫
                    (eventually_degenerate_mapping_object_degreeRepresentable
                      (U := U) (V := V) Δ₂ hU).homEquiv
                      (𝟙
                        (eventually_degenerate_mapping_object_obj
                          (U := U) (V := V) Δ₂ hU)) := by
                        exact hNatExplicit
                _ =
                  (simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
                      ((SimplicialObject.const C).map
                        (eventually_degenerate_mapping_object_map
                          (U := U) (V := V) σ hU)) ≫
                    simplicialCopowerIndexHom
                      ((SimplicialObject.const C).obj
                        (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))
                      (eventually_degenerate_mapping_reindex (U := U) τ)) ≫
                    (eventually_degenerate_mapping_object_degreeRepresentable
                      (U := U) (V := V) Δ₂ hU).homEquiv
                      (𝟙 _) := by
                        exact
                          eventually_degenerate_mapping_object_degreeRepresentable_universalElement_assoc
                            (U := U) (V := V) (Δ := Δ₂) hU
                            (k :=
                              simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
                                  ((SimplicialObject.const C).map
                                    (eventually_degenerate_mapping_object_map
                                      (U := U) (V := V) σ hU)) ≫
                                simplicialCopowerIndexHom
                                  ((SimplicialObject.const C).obj
                                    (eventually_degenerate_mapping_object_obj
                                      (U := U) (V := V) Δ₂ hU))
                                  (eventually_degenerate_mapping_reindex (U := U) τ))
      _ =
        simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
            ((SimplicialObject.const C).map
              (eventually_degenerate_mapping_object_map
                (U := U) (V := V) σ hU)) ≫
          (simplicialCopowerIndexHom
              ((SimplicialObject.const C).obj
                (eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₂ hU))
              (eventually_degenerate_mapping_reindex (U := U) τ) ≫
            (eventually_degenerate_mapping_object_degreeRepresentable
              (U := U) (V := V) Δ₂ hU).homEquiv
              (𝟙 _)) := by
                simp [Category.assoc]
      _ =
        simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
            ((SimplicialObject.const C).map
              (eventually_degenerate_mapping_object_map
                (U := U) (V := V) σ hU)) ≫
          (eventually_degenerate_mapping_object_degreeRepresentable
            (U := U) (V := V) Δ₃ hU).homEquiv
            (eventually_degenerate_mapping_object_map (U := U) (V := V) τ hU) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k =>
                    simplicialCopowerHom (U ⊗ Δ[Δ₃.unop.len])
                        ((SimplicialObject.const C).map
                          (eventually_degenerate_mapping_object_map
                            (U := U) (V := V) σ hU)) ≫
                      k)
                  (eventually_degenerate_mapping_object_map_homEquiv
                    (U := U) (V := V) τ hU).symm
  exact hChain.trans hComp.symm

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

/-- Helper for Lemma 14.17.4: compatible families are the same data as `Functor.HomObj`
sections for the simplicial hom functor. -/
private def compatibleEquivHomObj
    {U' : SSet.{w}} {W' V' : SimplicialObject C} :
    SimplicialCopowerHomFamily.Compatible U' W' V' ≃ W'.HomObj V' U' where
  toFun F :=
    { app := fun Δ u ↦ F.1 Δ u
      naturality := fun {Δ Δ'} σ u ↦ F.2 σ u }
  invFun F :=
    ⟨fun Δ u ↦ F.app Δ u, fun {Δ Δ'} σ u ↦ F.naturality σ u⟩
  left_inv F := by
    cases F
    rfl
  right_inv F := by
    cases F
    rfl

/-- Helper for Lemma 14.17.4: precomposing a compatible family with a morphism in the source
simplicial object acts degreewise by left composition. -/
private theorem precomposeCompatibleFamily_isCompatible
    {W₁ W₂ : SimplicialObject C} (f : W₁ ⟶ W₂)
    (F : SimplicialCopowerHomFamily.Compatible U W₂ V) :
    SimplicialCopowerHomFamily.IsCompatible
      (U := U) (V := W₁) (W := V)
      (fun Δ u ↦ f.app Δ ≫ F.1 Δ u) := by
  intro Δ Δ' σ u
  -- Proof comment: use the naturality square of `f` to move `W₁.map σ` past `f.app Δ'`, then
  -- apply the compatibility relation for `F`.
  calc
    W₁.map σ ≫ (f.app Δ' ≫ F.1 Δ' (U.map σ u))
        = (W₁.map σ ≫ f.app Δ') ≫ F.1 Δ' (U.map σ u) := by simp [Category.assoc]
    _ = (f.app Δ ≫ W₂.map σ) ≫ F.1 Δ' (U.map σ u) := by
          rw [f.naturality]
    _ = f.app Δ ≫ (W₂.map σ ≫ F.1 Δ' (U.map σ u)) := by simp [Category.assoc]
    _ = f.app Δ ≫ (F.1 Δ u ≫ V.map σ) := by
          rw [F.2 σ u]
    _ = (f.app Δ ≫ F.1 Δ u) ≫ V.map σ := by simp [Category.assoc]

/-- Helper for Lemma 14.17.4: source-side precomposition of compatible families. -/
private def precomposeCompatibleFamily
    {W₁ W₂ : SimplicialObject C} (f : W₁ ⟶ W₂)
    (F : SimplicialCopowerHomFamily.Compatible U W₂ V) :
    SimplicialCopowerHomFamily.Compatible U W₁ V :=
  ⟨fun Δ u ↦ f.app Δ ≫ F.1 Δ u,
    precomposeCompatibleFamily_isCompatible (U := U) (V := V) f F⟩

/-- Helper for Lemma 14.17.4: a global compatible family on `U` restricts in simplicial degree
`Δ` to a compatible family on `U ⊗ Δ[len]` with constant source `W.obj Δ`. -/
private def degreewiseHomObjOfCompatible
    {W : SimplicialObject C} (Δ : SimplexCategoryᵒᵖ)
    (F : SimplicialCopowerHomFamily.Compatible U W V) :
    ((SimplicialObject.const C).obj (W.obj Δ)).HomObj V (U ⊗ Δ[Δ.unop.len]) where
  app Γ ua := W.map (objEquiv ua.2).op ≫ F.1 Γ ua.1
  naturality {Γ Γ'} φ ua := by
    -- Proof comment: the simplex coordinate contributes the map `(objEquiv ua.2).op : Δ ⟶ Γ`,
    -- so after rewriting the standard-simplex action on `ua.2`, compatibility of `F` supplies
    -- the remaining square.
    rcases ua with ⟨u, a⟩
    simpa [SSet.stdSimplex.map_apply, Functor.map_comp, Category.assoc] using
      congrArg
        (fun k ↦ W.map (objEquiv a).op ≫ k)
        (F.2 φ u)

/-- Helper for Lemma 14.17.4: evaluating the degreewise reconstruction at the distinguished
simplex recovers the original compatible-family component. -/
private theorem degreewiseHomObjOfCompatible_apply_id
    {W : SimplicialObject C} (Δ : SimplexCategoryᵒᵖ)
    (F : SimplicialCopowerHomFamily.Compatible U W V) (u : U.obj Δ) :
    (degreewiseHomObjOfCompatible (U := U) (V := V) (W := W) Δ F).app Δ
        (u, objEquiv.symm (𝟙 Δ.unop)) =
      F.1 Δ u := by
  -- Proof comment: the distinguished simplex corresponds to the identity on `Δ`, so the extra
  -- precomposition on `W.obj Δ` is trivial.
  simp [degreewiseHomObjOfCompatible]

/-- Helper for Lemma 14.17.4: in simplicial degree `Δ`, maps into the assembled representing
object are equivalent to `HomObj` data on `U ⊗ Δ[len]`. -/
private noncomputable def eventually_degenerate_mapping_object_degreeHomObjEquiv
    (Δ : SimplexCategoryᵒᵖ) (hU : ∃ d : ℕ, U.HasDimensionLE d) (X : C) :
    (X ⟶ eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU) ≃
      ((SimplicialObject.const C).obj X).HomObj V (U ⊗ Δ[Δ.unop.len]) :=
  ((eventually_degenerate_mapping_object_degreeRepresentable
      (U := U) (V := V) Δ hU).homEquiv).trans
    ((((simplicialCopowerCompatibleFamilyCorepresentableBy
        (U := U ⊗ Δ[Δ.unop.len]) (V := (SimplicialObject.const C).obj X)).homEquiv)).trans
      (compatibleEquivHomObj
        (U' := U ⊗ Δ[Δ.unop.len]) (W' := (SimplicialObject.const C).obj X) (V' := V)))

/-- Helper for Lemma 14.17.4: the degree-`Δ` component of the inverse map from a global
compatible family to the assembled representing object. -/
private noncomputable def eventually_degenerate_mapping_object_fromCompatibleApp
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C} (F : SimplicialCopowerHomFamily.Compatible U W V)
    (Δ : SimplexCategoryᵒᵖ) :
    W.obj Δ ⟶ eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU :=
  (eventually_degenerate_mapping_object_degreeHomObjEquiv
      (U := U) (V := V) Δ hU (W.obj Δ)).symm
    (degreewiseHomObjOfCompatible (U := U) (V := V) (W := W) Δ F)

/-- Helper for Lemma 14.17.4: applying the degreewise `HomObj` equivalence back to the component
constructed from a global compatible family recovers the expected distinguished-simplex formula.
-/
private theorem eventually_degenerate_mapping_object_fromCompatibleApp_apply_id
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C} (F : SimplicialCopowerHomFamily.Compatible U W V)
    (Δ : SimplexCategoryᵒᵖ) (u : U.obj Δ) :
    ((eventually_degenerate_mapping_object_degreeHomObjEquiv
        (U := U) (V := V) Δ hU (W.obj Δ))
        (eventually_degenerate_mapping_object_fromCompatibleApp
          (U := U) (V := V) hU F Δ)).app Δ
        (u, objEquiv.symm (𝟙 Δ.unop)) =
      F.1 Δ u := by
  -- Proof comment: this is the right-inverse statement of the degreewise equivalence, followed
  -- by evaluation at the distinguished simplex.
  simpa [eventually_degenerate_mapping_object_fromCompatibleApp] using
    degreewiseHomObjOfCompatible_apply_id (U := U) (V := V) (W := W) Δ F u

/-- Helper for Chap14 Lemma 14 17 4: left composition in the source object passes through the
degreewise `HomObj` equivalence as left composition on each pointwise value. -/
private theorem eventually_degenerate_mapping_object_degreeHomObjEquiv_comp_app
    (Δ : SimplexCategoryᵒᵖ) (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {X Y : C} (g : X ⟶ Y)
    (f : Y ⟶ eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ hU)
    (Γ : SimplexCategoryᵒᵖ) (ua : (U ⊗ Δ[Δ.unop.len]).obj Γ) :
    ((eventually_degenerate_mapping_object_degreeHomObjEquiv
        (U := U) (V := V) Δ hU X (g ≫ f)).app Γ ua) =
      g ≫
        ((eventually_degenerate_mapping_object_degreeHomObjEquiv
          (U := U) (V := V) Δ hU Y f).app Γ ua) :=
  -- Proof comment: rewrite the representer equivalence along `homEquiv_comp`, then evaluate the
  -- resulting compatible family at `ua`; this turns source precomposition into left composition
  -- by `g` on the constant-object factor.
  rw [(eventually_degenerate_mapping_object_degreeRepresentable
    (U := U) (V := V) Δ hU).homEquiv_comp g f]
  simp [eventually_degenerate_mapping_object_degreeHomObjEquiv, compatibleEquivHomObj,
    tensor_stdSimplex_const_hom_presheaf_map_app, simplicialCopowerHom_app, Category.assoc]

/-- Helper for Chap14 Lemma 14 17 4: composing with the degreewise reindexing map transports the
degreewise `HomObj` equivalence by reindexing the source simplex coordinate. -/
private theorem eventually_degenerate_mapping_object_degreeHomObjEquiv_reindex_app
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂)
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {X : C}
    (f : X ⟶ eventually_degenerate_mapping_object_obj (U := U) (V := V) Δ₁ hU)
    (Γ : SimplexCategoryᵒᵖ) (ua : (U ⊗ Δ[Δ₂.unop.len]).obj Γ) :
    ((eventually_degenerate_mapping_object_degreeHomObjEquiv
        (U := U) (V := V) Δ₂ hU X
        (f ≫ eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU)).app Γ ua) =
      ((eventually_degenerate_mapping_object_degreeHomObjEquiv
          (U := U) (V := V) Δ₁ hU X f).app Γ
          ((eventually_degenerate_mapping_reindex (U := U) σ).app Γ ua)) :=
  -- Proof comment: rewrite the reindexing map under the degree-`Δ₂` representer, then read the
  -- resulting compatible family in `HomObj` coordinates; the source simplex is transported by
  -- `eventually_degenerate_mapping_reindex σ`.
  rw [eventually_degenerate_mapping_object_map_universalElement (U := U) (V := V) σ hU]
  simp [eventually_degenerate_mapping_object_degreeHomObjEquiv, compatibleEquivHomObj,
    simplicialCopowerHom_app, Category.assoc]

/-- Helper for Chap14 Lemma 14 17 4: the degreewise `HomObj` section extracted from a compatible
family reindexes exactly by left composition with `W.map σ`. -/
private theorem degreewiseHomObjOfCompatible_reindex
    {W : SimplicialObject C} (F : SimplicialCopowerHomFamily.Compatible U W V)
    {Δ₁ Δ₂ Γ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂)
    (ua : (U ⊗ Δ[Δ₂.unop.len]).obj Γ) :
    (degreewiseHomObjOfCompatible (U := U) (V := V) (W := W) Δ₁ F).app Γ
        (((eventually_degenerate_mapping_reindex (U := U) σ).app Γ ua)) =
      W.map σ ≫
        (degreewiseHomObjOfCompatible (U := U) (V := V) (W := W) Δ₂ F).app Γ ua := by
  -- Proof comment: unfold the degreewise section and compute the tensor reindexing on the
  -- simplex coordinate by the standard-simplex formula.
  rcases ua with ⟨u, a⟩
  change
    W.map (objEquiv (((SSet.stdSimplex.map σ.unop).app Γ) a)).op ≫ F.1 Γ u =
      W.map σ ≫ W.map (objEquiv a).op ≫ F.1 Γ u
  have hSimplex :
      (SSet.stdSimplex.map σ.unop).app Γ a =
        objEquiv.symm (objEquiv a ≫ σ.unop) := by
    exact (SSet.stdSimplex.objEquiv_symm_comp (f := objEquiv a) (g := σ.unop)).symm
  rw [hSimplex]
  simp [Functor.map_comp, Category.assoc]

/-- Helper for Chap14 Lemma 14 17 4: the inverse degreewise components assembled from a global
compatible family are natural in the simplicial degree. -/
private theorem eventually_degenerate_mapping_object_fromCompatibleApp_naturality
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C} (F : SimplicialCopowerHomFamily.Compatible U W V)
    {Δ₁ Δ₂ : SimplexCategoryᵒᵖ} (σ : Δ₁ ⟶ Δ₂) :
    W.map σ ≫
        eventually_degenerate_mapping_object_fromCompatibleApp
          (U := U) (V := V) hU F Δ₂ =
      eventually_degenerate_mapping_object_fromCompatibleApp
          (U := U) (V := V) hU F Δ₁ ≫
        eventually_degenerate_mapping_object_map (U := U) (V := V) σ hU :=
  -- TODO: compare both sides under the degree-`Δ₂` `HomObj` equivalence, then close by the
  -- left-composition and reindex bridges above.
  sorry

/-- Helper for Chap14 Lemma 14 17 4: the forward compatible-family component attached to a map
into the assembled representing object is evaluation at the distinguished simplex. -/
private noncomputable def eventually_degenerate_mapping_object_toCompatibleFamilyApp
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C}
    (f : W ⟶ eventually_degenerate_mapping_object (U := U) (V := V) hU)
    (Δ : SimplexCategoryᵒᵖ) (u : U.obj Δ) :
    W.obj Δ ⟶ V.obj Δ :=
  ((eventually_degenerate_mapping_object_degreeHomObjEquiv
      (U := U) (V := V) Δ hU (W.obj Δ))
      (f.app Δ)).app Δ
    (u, objEquiv.symm (𝟙 Δ.unop))

/-- Helper for Chap14 Lemma 14 17 4: the distinguished-simplex evaluation extracted from a map
into the assembled object satisfies the compatible-family relation. -/
private theorem eventually_degenerate_mapping_object_toCompatibleFamily_isCompatible
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C}
    (f : W ⟶ eventually_degenerate_mapping_object (U := U) (V := V) hU) :
    SimplicialCopowerHomFamily.IsCompatible
      (U := U) (V := W) (W := V)
      (eventually_degenerate_mapping_object_toCompatibleFamilyApp
        (U := U) (V := V) hU f) :=
  -- TODO: apply the naturality of `f` under the degree-`Δ₂` `HomObj` equivalence and close
  -- with the reindex bridge plus the `HomObj.naturality` computation at the distinguished simplex.
  sorry

/-- Helper for Chap14 Lemma 14 17 4: maps into the assembled degreewise representer determine a
global compatible family by distinguished-simplex evaluation. -/
private noncomputable def eventually_degenerate_mapping_object_toCompatibleFamily
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C}
    (f : W ⟶ eventually_degenerate_mapping_object (U := U) (V := V) hU) :
    SimplicialCopowerHomFamily.Compatible U W V :=
  ⟨eventually_degenerate_mapping_object_toCompatibleFamilyApp
      (U := U) (V := V) hU f,
    eventually_degenerate_mapping_object_toCompatibleFamily_isCompatible
      (U := U) (V := V) hU f⟩

/-- Helper for Chap14 Lemma 14 17 4: rebuilding the degreewise `HomObj` section from the
compatible family extracted from `f` recovers the original degreewise section. -/
private theorem degreewiseHomObjOfCompatible_toCompatibleFamily
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C}
    (f : W ⟶ eventually_degenerate_mapping_object (U := U) (V := V) hU)
    (Δ : SimplexCategoryᵒᵖ) (Γ : SimplexCategoryᵒᵖ)
    (ua : (U ⊗ Δ[Δ.unop.len]).obj Γ) :
    (degreewiseHomObjOfCompatible (U := U) (V := V) (W := W) Δ
        (eventually_degenerate_mapping_object_toCompatibleFamily
          (U := U) (V := V) hU f)).app Γ ua =
      ((eventually_degenerate_mapping_object_degreeHomObjEquiv
          (U := U) (V := V) Δ hU (W.obj Δ))
        (f.app Δ)).app Γ ua :=
  -- TODO: transport the distinguished-simplex evaluation along the simplex represented by
  -- `ua.2`, then rewrite the resulting right-composition by the reindex bridge above.
  sorry

/-- Helper for Chap14 Lemma 14 17 4: applying the forward compatible-family map to the inverse
construction from a compatible family recovers that family. -/
private theorem eventually_degenerate_mapping_object_toCompatibleFamily_fromCompatible
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C}
    (F : SimplicialCopowerHomFamily.Compatible U W V) :
    eventually_degenerate_mapping_object_toCompatibleFamily
        (U := U) (V := V) hU
        { app := eventually_degenerate_mapping_object_fromCompatibleApp
            (U := U) (V := V) hU F
          naturality := fun {Δ₁ Δ₂} σ ↦
            eventually_degenerate_mapping_object_fromCompatibleApp_naturality
              (U := U) (V := V) hU F σ } =
      F := by
  -- Proof comment: each component is recovered by applying the degreewise equivalence and then
  -- evaluating at the distinguished simplex.
  apply Subtype.ext
  funext Δ u
  exact eventually_degenerate_mapping_object_fromCompatibleApp_apply_id
    (U := U) (V := V) hU F Δ u

/-- Helper for Chap14 Lemma 14 17 4: the inverse built from the compatible family extracted from
`f` is the original simplicial morphism. -/
private theorem eventually_degenerate_mapping_object_fromCompatible_toCompatible
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C}
    (f : W ⟶ eventually_degenerate_mapping_object (U := U) (V := V) hU) :
    { app := eventually_degenerate_mapping_object_fromCompatibleApp
        (U := U) (V := V) hU
        (eventually_degenerate_mapping_object_toCompatibleFamily
          (U := U) (V := V) hU f)
      naturality := fun {Δ₁ Δ₂} σ ↦
        eventually_degenerate_mapping_object_fromCompatibleApp_naturality
          (U := U) (V := V) hU
          (eventually_degenerate_mapping_object_toCompatibleFamily
            (U := U) (V := V) hU f) σ } = f := by
  -- Proof comment: compare componentwise, and then use injectivity of the degreewise `HomObj`
  -- equivalence to reduce to the previous recovery theorem.
  ext Δ
  apply
    (eventually_degenerate_mapping_object_degreeHomObjEquiv
      (U := U) (V := V) Δ hU (W.obj Δ)).injective
  ext Γ ua
  simpa [eventually_degenerate_mapping_object_fromCompatibleApp] using
    degreewiseHomObjOfCompatible_toCompatibleFamily
      (U := U) (V := V) hU f Δ Γ ua

/-- Helper for Chap14 Lemma 14 17 4: morphisms into the assembled representing object are
equivalent to global compatible families. -/
private noncomputable def eventually_degenerate_mapping_object_compatibleEquiv
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W : SimplicialObject C} :
    (W ⟶ eventually_degenerate_mapping_object (U := U) (V := V) hU) ≃
      SimplicialCopowerHomFamily.Compatible U W V where
  toFun := eventually_degenerate_mapping_object_toCompatibleFamily
    (U := U) (V := V) hU
  invFun := fun F =>
    { app := eventually_degenerate_mapping_object_fromCompatibleApp
        (U := U) (V := V) hU F
      naturality := fun {Δ₁ Δ₂} σ ↦
        eventually_degenerate_mapping_object_fromCompatibleApp_naturality
          (U := U) (V := V) hU F σ }
  left_inv := eventually_degenerate_mapping_object_fromCompatible_toCompatible
    (U := U) (V := V) hU
  right_inv := eventually_degenerate_mapping_object_toCompatibleFamily_fromCompatible
    (U := U) (V := V) hU

/-- Helper for Chap14 Lemma 14 17 4: source-side precomposition of a simplicial morphism into the
assembled representing object corresponds to source-side precomposition of the extracted
compatible family. -/
private theorem eventually_degenerate_mapping_object_compatibleEquiv_comp
    (hU : ∃ d : ℕ, U.HasDimensionLE d)
    {W₁ W₂ : SimplicialObject C}
    (g : W₁ ⟶ W₂)
    (f : W₂ ⟶ eventually_degenerate_mapping_object (U := U) (V := V) hU) :
    eventually_degenerate_mapping_object_compatibleEquiv
        (U := U) (V := V) hU (g ≫ f) =
      precomposeCompatibleFamily (U := U) (V := V) g
        (eventually_degenerate_mapping_object_compatibleEquiv
          (U := U) (V := V) hU f) := by
  -- Proof comment: both compatible families are defined by distinguished-simplex evaluation, and
  -- the only change under source precomposition is left composition by `g.app Δ`.
  apply Subtype.ext
  funext Δ u
  simpa [eventually_degenerate_mapping_object_compatibleEquiv,
    eventually_degenerate_mapping_object_toCompatibleFamily,
    eventually_degenerate_mapping_object_toCompatibleFamilyApp,
    precomposeCompatibleFamily] using
    eventually_degenerate_mapping_object_degreeHomObjEquiv_comp_app
      (U := U) (V := V) Δ hU (g.app Δ) (f.app Δ) Δ
      (u, objEquiv.symm (𝟙 Δ.unop))

/-- Helper for Chap14 Lemma 14 17 4: under the canonical compatible-family equivalence, the
presheaf map induced by `g : W₁ ⟶ W₂` is source-side precomposition on compatible families. -/
private theorem simplicialHomPresheaf_homEquiv_precompose
    {W₁ W₂ : SimplicialObject C} (g : W₁ ⟶ W₂)
    (γ : (simplicialHomPresheaf U V).obj (Opposite.op W₂)) :
    (simplicialCopowerCompatibleFamilyCorepresentableBy
        (U := U) (V := W₁)).homEquiv
        ((simplicialHomPresheaf U V).map g.op γ) =
      precomposeCompatibleFamily (U := U) (V := V) g
        ((simplicialCopowerCompatibleFamilyCorepresentableBy
          (U := U) (V := W₂)).homEquiv γ) := by
  -- Proof comment: the mapping-presheaf action is precomposition by `simplicialCopowerHom U g`,
  -- and the compatible-family equivalence reads that precomposition degreewise.
  apply Subtype.ext
  funext Δ u
  change
    Sigma.ι (fun _ : U.obj Δ ↦ W₁.obj Δ) u ≫
        ((simplicialCopowerHom U g) ≫ γ).app Δ =
      g.app Δ ≫ Sigma.ι (fun _ : U.obj Δ ↦ W₂.obj Δ) u ≫ γ.app Δ
  simp [simplicialCopowerHom_app, Category.assoc]

/-- Helper for Chap14 Lemma 14 17 4: the assembled simplicial object corepresents the mapping
presheaf `simplicialHomPresheaf U V`. -/
private noncomputable def eventually_degenerate_mapping_object_representableBy
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (simplicialHomPresheaf U V).RepresentableBy
      (eventually_degenerate_mapping_object (U := U) (V := V) hU) :=
  -- TODO: package the global compatible-family equivalence with
  -- `simplicialCopowerCompatibleFamilyCorepresentableBy`, then prove `homEquiv_comp` by
  -- source-precomposition naturality.
  sorry

/-- Lemma 14.17.4: if `C` has binary coproducts and finite limits, if `U` is degreewise finite
with a `0`-simplex, and if all sufficiently high simplices of `U` are degenerate, then the presheaf
`W ↦ Mor_{Simp(C)}(W × U, V)` is representable. Equivalently, the simplicial mapping object
`simplicialHom U V` exists. -/
@[stacks 017L]
theorem simplicialHomPresheaf_isRepresentable_of_eventually_degenerate
    (hU : ∃ d : ℕ, U.HasDimensionLE d) :
    (simplicialHomPresheaf U V).IsRepresentable := by
  -- Route correction: finish entirely in the explicit degreewise `HomObj` and compatible-family
  -- coordinates, then package the assembled simplicial object as the representing object.
  exact
    (eventually_degenerate_mapping_object_representableBy
      (U := U) (V := V) hU).isRepresentable

instance simplicialHomPresheaf_isRepresentable_of_fact_eventually_degenerate
    [Fact (∃ d : ℕ, U.HasDimensionLE d)] :
    (simplicialHomPresheaf U V).IsRepresentable :=
  simplicialHomPresheaf_isRepresentable_of_eventually_degenerate U V Fact.out

end EventuallyDegenerate

end CategoryTheory
