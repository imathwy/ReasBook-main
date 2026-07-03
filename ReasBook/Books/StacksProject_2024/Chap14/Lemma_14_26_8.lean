import StacksProject_2024.Chap14.Definition_14_26_1
import StacksProject_2024.Chap14.Lemma_14_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open MonoidalCategory
open Opposite
open SSet (ι₀ ι₁)
open SSet.stdSimplex (asOrderHom isTerminalObj₀ objMk)
open scoped Simplicial

universe u v

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]

/- Domain-style sampling for Lemma 14.26.8:
- primary domain: simplicial cylinders and endpoint maps for simplicial objects, expressed through
  the simplicial copower action of `SSet` on `SimplicialObject C`;
- sampled same-kind declarations:
  `CategoryTheory.simplicialCopower`,
  `CategoryTheory.simplicialCopowerIndexFunctor`,
  `CategoryTheory.simplicialCopowerProjection`,
  `CategoryTheory.simplicialCopowerIndexHom`,
  `SSet.stdSimplex.δ`,
  `CategoryTheory.SimplicialObject.Homotopic`;
- best owner abstraction:
  the source-facing owner here is the interval cylinder `Δ[1] × U`, while the ambient canonical
  owner is the simplicial copower API from Section 14.13;
- primitive data:
  the canonical section `U ⟶ Δ[0] × U` of the point-copower projection, together with the
  canonical coface maps `SSet.stdSimplex.δ (1 : Fin 2), SSet.stdSimplex.δ (0 : Fin 2) :
    Δ[0] ⟶ Δ[1]`;
- derived API:
  the canonical projection to `U` comes directly from `simplicialCopowerProjection`, the
  source-facing endpoint owners `e₀`, `e₁` are the reindexing maps `simplicialCopowerIndexHom`
  along those canonical endpoint maps after the point-copower bridge, and the remaining public
  projection and homotopy lemmas are source-facing consequences of that bridge.

Source/core/bridge triage:
- `source-facing`: the cylinder `Δ[1] × U`, its endpoint owners `e₀`, `e₁`, and the resulting
  homotopy relation statements;
- `core/canonical`: the simplicial copower owner `(X, U) ↦ X × U` with its reindexing and
  projection maps;
- `bridge/view`: the canonical section of `simplicialCopowerProjection U (Δ[0])`, the
  source-facing owners `e₀`, `e₁`, and the identities and homotopy statements relating
  them to the canonical projection. -/

private def pointCopowerSectionApp
    (U : SimplicialObject C) (Δ : SimplexCategoryᵒᵖ) :
    U.obj Δ ⟶ ((Δ[0] : SSet.{0}) × U).obj Δ :=
  Sigma.ι (fun _ : (Δ[0] : SSet.{0}).obj Δ ↦ U.obj Δ) (SSet.stdSimplex.const 0 0 Δ)

-- Proof sketch: the point simplicial set has exactly one simplex in every degree, so the unique
-- coproduct summand indexed by that point is preserved by the structure maps.
private theorem pointCopowerSection_naturality
    (U : SimplicialObject C) {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    U.map f ≫ pointCopowerSectionApp U Δ' =
      pointCopowerSectionApp U Δ ≫ ((Δ[0] : SSet.{0}) × U).map f := by
  -- The point simplicial set has a unique simplex in every degree, so reindexing preserves the
  -- chosen coproduct summand.
  have hpoint :
      (Δ[0] : SSet.{0}).map f (SSet.stdSimplex.const 0 0 Δ) =
        SSet.stdSimplex.const 0 0 Δ' := by
    apply SSet.stdSimplex.ext
    intro k
    exact Fin.ext (by simp [SSet.stdSimplex.const])
  simp [pointCopowerSectionApp, simplicialCopower_map, hpoint]

private def pointCopowerSection (U : SimplicialObject C) :
    U ⟶ (Δ[0] : SSet.{0}) × U where
  app Δ := pointCopowerSectionApp U Δ
  naturality := fun {_ _} f ↦ pointCopowerSection_naturality U f

/-- The endpoint inclusion `e₁ : U ⟶ Δ[1] × U`. -/
abbrev e₁ (U : SimplicialObject C) :
    U ⟶ (Δ[1] : SSet.{0}) × U :=
  pointCopowerSection U ≫
    simplicialCopowerIndexHom U (SSet.stdSimplex.δ (0 : Fin 2))

/-- The endpoint inclusion `e₀ : U ⟶ Δ[1] × U`. -/
abbrev e₀ (U : SimplicialObject C) :
    U ⟶ (Δ[1] : SSet.{0}) × U :=
  pointCopowerSection U ≫
    simplicialCopowerIndexHom U (SSet.stdSimplex.δ (1 : Fin 2))

-- Proof sketch: in each simplicial degree, the endpoint inclusion `e₁` lands in the coproduct
-- summand indexed by the vertex map `Δ[0] ⟶ Δ[1]` selecting `1`; after reindexing naturality,
-- this reduces to the splitting of the point-copower projection.
private theorem pointCopowerSection_comp_projection
    (U : SimplicialObject C) :
    pointCopowerSection U ≫ simplicialCopowerProjection U (Δ[0] : SSet.{0}) = 𝟙 U :=
  by
  -- Degreewise, the canonical section lands in the unique point summand, and the projection is
  -- the identity on every summand.
  ext Δ
  simpa [pointCopowerSection, pointCopowerSectionApp] using
    (Sigma.ι_desc (fun _ : (Δ[0] : SSet.{0}).obj Δ ↦ 𝟙 (U.obj Δ))
      (SSet.stdSimplex.const 0 0 Δ))

/-- Helper for Lemma 14.26.8: projecting `Δ[1] × U` to `U` and then reinserting into the point
copower is reindexing along the unique map `Δ[1] ⟶ Δ[0]`. -/
private theorem projection_comp_pointCopowerSection
    (U : SimplicialObject C) :
    simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ pointCopowerSection U =
      simplicialCopowerIndexHom U (isTerminalObj₀.from (Δ[1] : SSet.{0})) := by
  -- Compare both morphisms componentwise on each coproduct injection of `Δ[1] × U`.
  have hpoint (Δ : SimplexCategoryᵒᵖ) (x : (Δ[1] : SSet.{0}).obj Δ) :
      (isTerminalObj₀.from (Δ[1] : SSet.{0})).app Δ x = SSet.stdSimplex.const 0 0 Δ := by
    apply SSet.stdSimplex.ext
    intro k
    change asOrderHom ((SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0)).app Δ x) k =
      asOrderHom (SSet.stdSimplex.const 0 0 Δ) k
    rfl
  ext Δ
  apply Sigma.hom_ext
  intro x
  have hmap :
      Sigma.ι (fun _ : (Δ[0] : SSet.{0}).obj Δ ↦ U.obj Δ)
          ((isTerminalObj₀.from (Δ[1] : SSet.{0})).app Δ x) =
        Sigma.ι (fun _ : (Δ[1] : SSet.{0}).obj Δ ↦ U.obj Δ) x ≫
          (simplicialCopowerIndexHom U (isTerminalObj₀.from (Δ[1] : SSet.{0}))).app Δ := by
    simpa [simplicialCopowerIndexHom_app] using
      (Sigma.ι_comp_map'
        (p := (isTerminalObj₀.from (Δ[1] : SSet.{0})).app Δ)
        (q := fun _ ↦ 𝟙 (U.obj Δ))
        x).symm
  trans Sigma.ι (fun _ : (Δ[1] : SSet.{0}).obj Δ ↦ U.obj Δ) x ≫
      (simplicialCopowerProjection U (Δ[1] : SSet.{0})).app Δ ≫ pointCopowerSectionApp U Δ
  · simp [NatTrans.comp_app, pointCopowerSection]
  trans pointCopowerSectionApp U Δ
  · simpa [simplicialCopowerProjection_app, Category.assoc] using
      (Sigma.ι_desc (fun _ : (Δ[1] : SSet.{0}).obj Δ ↦ 𝟙 (U.obj Δ)) x) =≫
        pointCopowerSectionApp U Δ
  · simpa [pointCopowerSectionApp, hpoint] using hmap

private theorem simplicialIntervalProjection_comp_endpoint
    (U : SimplicialObject C) (vertex : (Δ[0] : SSet.{0}) ⟶ (Δ[1] : SSet.{0})) :
    (pointCopowerSection U ≫ simplicialCopowerIndexHom U vertex) ≫
        simplicialCopowerProjection U (Δ[1] : SSet.{0}) =
      𝟙 U := by
  have hproj :
      simplicialCopowerIndexHom U vertex ≫ simplicialCopowerProjection U (Δ[1] : SSet.{0}) =
        simplicialCopowerProjection U (Δ[0] : SSet.{0}) ≫ 𝟙 U :=
    (simplicialCopowerProjection_index_naturality U vertex).w
  calc
    (pointCopowerSection U ≫ simplicialCopowerIndexHom U vertex) ≫
        simplicialCopowerProjection U (Δ[1] : SSet.{0}) =
        pointCopowerSection U ≫
          (simplicialCopowerIndexHom U vertex ≫
            simplicialCopowerProjection U (Δ[1] : SSet.{0})) := by
            simp [Category.assoc]
    _ = pointCopowerSection U ≫ (simplicialCopowerProjection U (Δ[0] : SSet.{0}) ≫ 𝟙 U) := by
          rw [hproj]
    _ = pointCopowerSection U ≫ simplicialCopowerProjection U (Δ[0] : SSet.{0}) := by simp
    _ = 𝟙 U := pointCopowerSection_comp_projection U

/-- Lemma 14.26.8 (1): the projection `π : Δ[1] × U ⟶ U` composed with the endpoint map
`e₁ : U ⟶ Δ[1] × U` is the identity on `U`. -/
theorem simplicialIntervalProjection_comp_endpointOne (U : SimplicialObject C) :
    e₁ U ≫ simplicialCopowerProjection U (Δ[1] : SSet.{0}) = 𝟙 U := by
  simpa [e₁] using
    simplicialIntervalProjection_comp_endpoint U (SSet.stdSimplex.δ (0 : Fin 2))

-- Proof sketch: in each simplicial degree, the endpoint inclusion `e₀` lands in the coproduct
-- summand indexed by the constant `0` simplex, and the projection is the identity on every
-- summand, so the composite is the identity componentwise.
/-- Lemma 14.26.8 (2): the projection `π : Δ[1] × U ⟶ U` composed with the endpoint map
`e₀ : U ⟶ Δ[1] × U` is the identity on `U`. -/
theorem simplicialIntervalProjection_comp_endpointZero (U : SimplicialObject C) :
    e₀ U ≫ simplicialCopowerProjection U (Δ[1] : SSet.{0}) = 𝟙 U := by
  simpa [e₀] using
    simplicialIntervalProjection_comp_endpoint U (SSet.stdSimplex.δ (1 : Fin 2))

/-- Helper for Lemma 14.26.8: the pointwise `max` formula on `Δ[1] × Δ[1]` is monotone in each
simplicial degree. -/
private theorem deltaOneMaxApp_monotone (Δ : SimplexCategoryᵒᵖ)
    (z : (((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj Δ)) :
    Monotone
      (fun k : Fin (Δ.unop.len + 1) ↦
        max (asOrderHom z.1 k) (asOrderHom z.2 k)) :=
  (SSet.stdSimplex.monotone_apply z.1).max (SSet.stdSimplex.monotone_apply z.2)

/-- Helper for Lemma 14.26.8: the pointwise `max` simplex in `Δ[1]`. -/
private def deltaOneMaxApp (Δ : SimplexCategoryᵒᵖ) :
    (((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj Δ) → (Δ[1] : SSet.{0}).obj Δ :=
  fun z ↦
    objMk
      { toFun := fun k ↦ max (asOrderHom z.1 k) (asOrderHom z.2 k)
        monotone' := deltaOneMaxApp_monotone Δ z }

/-- Helper for Lemma 14.26.8: the `max` formula commutes with simplicial reindexing. -/
private theorem deltaOneMax_naturality {Δ Δ' : SimplexCategoryᵒᵖ}
    (θ : Δ ⟶ Δ') (z : (((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj Δ)) :
    deltaOneMaxApp Δ' (((Δ[1] : SSet.{0}) ⊗ Δ[1]).map θ z) =
      (Δ[1] : SSet.{0}).map θ (deltaOneMaxApp Δ z) := by
  apply SSet.stdSimplex.ext
  intro k
  rfl

/-- Helper for Lemma 14.26.8: the simplicial map on `Δ[1] × Δ[1]` defined by pointwise
maximum. -/
private noncomputable def deltaOneMaxMap :
    ((Δ[1] : SSet.{0}) ⊗ Δ[1]) ⟶ (Δ[1] : SSet.{0}) where
  app Δ := deltaOneMaxApp Δ
  naturality := fun {_ _} θ ↦ funext (deltaOneMax_naturality θ)

/-- Helper for Lemma 14.26.8: the `max` map restricts to the identity along the `0`-endpoint of
the interval parameter. -/
private theorem deltaOneMaxMap_h₀ :
    ι₀ ≫ deltaOneMaxMap = 𝟙 (Δ[1] : SSet.{0}) := by
  ext Δ z
  apply SSet.stdSimplex.ext
  intro k
  change max (asOrderHom z k) 0 = asOrderHom z k
  simp

/-- Helper for Lemma 14.26.8: the `max` map restricts to the constant-`1` map along the
`1`-endpoint of the interval parameter. -/
private theorem deltaOneMaxMap_h₁ :
    ι₁ ≫ deltaOneMaxMap =
      isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2) := by
  -- At time `1`, the pointwise maximum is constantly the final vertex of `Δ[1]`.
  ext Δ z
  apply SSet.stdSimplex.ext
  intro k
  change max (asOrderHom z k) 1 =
    asOrderHom
      (((isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2)).app Δ) z) k
  change max (asOrderHom z k) 1 = 1
  have hk : asOrderHom z k ≤ (1 : Fin 2) := by
    simpa using (Fin.le_last (asOrderHom z k))
  simp [hk]

/-- Helper for Lemma 14.26.8: pointwise maximum gives a directed homotopy from the identity of
`Δ[1]` to the constant-`1` endomorphism. -/
private noncomputable def deltaOne_max_homotopy :
    SSet.Homotopy (𝟙 (Δ[1] : SSet.{0}))
      (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2)) where
  h := deltaOneMaxMap
  h₀ := deltaOneMaxMap_h₀
  h₁ := deltaOneMaxMap_h₁
  rel := by
    ext Δ z
    exact False.elim z.1.2

/-- Helper for Lemma 14.26.8: the pointwise `min` formula on `Δ[1] × Δ[1]` is monotone in each
simplicial degree. -/
private theorem deltaOneMinApp_monotone (Δ : SimplexCategoryᵒᵖ)
    (z : (((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj Δ)) :
    Monotone
      (fun k : Fin (Δ.unop.len + 1) ↦
        min (asOrderHom z.1 k) (asOrderHom z.2 k)) :=
  (SSet.stdSimplex.monotone_apply z.1).min (SSet.stdSimplex.monotone_apply z.2)

/-- Helper for Lemma 14.26.8: the pointwise `min` simplex in `Δ[1]`. -/
private def deltaOneMinApp (Δ : SimplexCategoryᵒᵖ) :
    (((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj Δ) → (Δ[1] : SSet.{0}).obj Δ :=
  fun z ↦
    objMk
      { toFun := fun k ↦ min (asOrderHom z.1 k) (asOrderHom z.2 k)
        monotone' := deltaOneMinApp_monotone Δ z }

/-- Helper for Lemma 14.26.8: the `min` formula commutes with simplicial reindexing. -/
private theorem deltaOneMin_naturality {Δ Δ' : SimplexCategoryᵒᵖ}
    (θ : Δ ⟶ Δ') (z : (((Δ[1] : SSet.{0}) ⊗ Δ[1]).obj Δ)) :
    deltaOneMinApp Δ' (((Δ[1] : SSet.{0}) ⊗ Δ[1]).map θ z) =
      (Δ[1] : SSet.{0}).map θ (deltaOneMinApp Δ z) := by
  apply SSet.stdSimplex.ext
  intro k
  rfl

/-- Helper for Lemma 14.26.8: the simplicial map on `Δ[1] × Δ[1]` defined by pointwise
minimum. -/
private noncomputable def deltaOneMinMap :
    ((Δ[1] : SSet.{0}) ⊗ Δ[1]) ⟶ (Δ[1] : SSet.{0}) where
  app Δ := deltaOneMinApp Δ
  naturality := fun {_ _} θ ↦ funext (deltaOneMin_naturality θ)

/-- Helper for Lemma 14.26.8: the `min` map restricts to the constant-`0` map along the
`0`-endpoint of the interval parameter. -/
private theorem deltaOneMinMap_h₀ :
    ι₀ ≫ deltaOneMinMap =
      isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (1 : Fin 2) := by
  -- At time `0`, the pointwise minimum is constantly the initial vertex of `Δ[1]`.
  ext Δ z
  apply SSet.stdSimplex.ext
  intro k
  change min (asOrderHom z k) 0 =
    asOrderHom
      (((isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (1 : Fin 2)).app Δ) z) k
  change min (asOrderHom z k) 0 = 0
  simp

/-- Helper for Lemma 14.26.8: the `min` map restricts to the identity along the `1`-endpoint of
the interval parameter. -/
private theorem deltaOneMinMap_h₁ :
    ι₁ ≫ deltaOneMinMap = 𝟙 (Δ[1] : SSet.{0}) := by
  ext Δ z
  apply SSet.stdSimplex.ext
  intro k
  change min (asOrderHom z k) 1 = asOrderHom z k
  have hk : asOrderHom z k ≤ (1 : Fin 2) := by
    simpa using (Fin.le_last (asOrderHom z k))
  simp [hk]

/-- Helper for Lemma 14.26.8: pointwise minimum gives a directed homotopy from the constant-`0`
endomorphism of `Δ[1]` to the identity. -/
private noncomputable def deltaOne_min_homotopy :
    SSet.Homotopy
      (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (1 : Fin 2))
      (𝟙 (Δ[1] : SSet.{0})) where
  h := deltaOneMinMap
  h₀ := deltaOneMinMap_h₀
  h₁ := deltaOneMinMap_h₁
  rel := by
    ext Δ z
    exact False.elim z.1.2

section CopowerIndexHomotopy

variable {K L : SSet.{0}} (U : SimplicialObject C)
variable
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : K.obj Δ ↦ U.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : L.obj Δ ↦ U.obj Δ)]
variable {a b : K ⟶ L} (H : SSet.Homotopy a b)

/-- Helper for Lemma 14.26.8: the degreewise coproduct map obtained by lifting one component of a
simplicial-set homotopy through the simplicial copower. -/
private def copower_index_homotopy_component {n : ℕ} (i : Fin (n + 1)) :
    (K × U).obj (op ⦋n⦌) ⟶ (L × U).obj (op ⦋n + 1⦌) :=
  Sigma.map' (H.toSimplicialObjectHomotopy.h i) (fun _ ↦ U.σ i)

/-- Helper for Lemma 14.26.8: precomposing the lifted component map with a coproduct injection
rewrites it to the corresponding summand map followed by the target coproduct injection. -/
private theorem copower_index_homotopy_component_comp_ι
    {n : ℕ} (i : Fin (n + 1)) (x : K.obj (op ⦋n⦌)) :
    Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
        copower_index_homotopy_component U H i =
      U.σ i ≫
        Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
          (H.toSimplicialObjectHomotopy.h i x) := by
  -- This is the canonical coproduct-injection normalization for `Sigma.map'`.
  simpa [copower_index_homotopy_component] using
    (Sigma.ι_comp_map'
      (p := H.toSimplicialObjectHomotopy.h i)
      (q := fun _ ↦ U.σ i)
      x)

/-- Helper for Lemma 14.26.8: after applying one lifted homotopy component, postcomposing by a
simplicial copower structure map collapses to the corresponding target summand. -/
private theorem copower_index_homotopy_component_comp_map_comp_ι
    {n m : ℕ} (i : Fin (n + 1)) (θ : op ⦋n + 1⦌ ⟶ op ⦋m⦌)
    (x : K.obj (op ⦋n⦌)) :
    Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
        copower_index_homotopy_component U H i ≫ (L × U).map θ =
      (U.σ i ≫ U.map θ) ≫
        Sigma.ι (fun _ : L.obj (op ⦋m⦌) ↦ U.obj (op ⦋m⦌))
          (L.map θ (H.toSimplicialObjectHomotopy.h i x)) := by
  -- First normalize the lifted homotopy component on the chosen summand.
  calc
    Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
        copower_index_homotopy_component U H i ≫ (L × U).map θ =
      (U.σ i ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (H.toSimplicialObjectHomotopy.h i x)) ≫
        (L × U).map θ := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ (L × U).map θ)
              (copower_index_homotopy_component_comp_ι (U := U) (H := H) i x)
    _ = (U.σ i ≫ U.map θ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋m⦌) ↦ U.obj (op ⦋m⦌))
            (L.map θ (H.toSimplicialObjectHomotopy.h i x)) := by
            -- Then push the target coproduct injection through the simplicial copower structure map.
            simpa [simplicialCopower_map, Category.assoc] using
              congrArg (fun k ↦ U.σ i ≫ k)
                (Sigma.ι_comp_map'
                  (p := L.map θ)
                  (q := fun _ ↦ U.map θ)
                  (H.toSimplicialObjectHomotopy.h i x))

/-- Helper for Lemma 14.26.8: precomposing a lifted homotopy component by a simplicial copower
structure map collapses to the corresponding source summand. -/
private theorem copower_index_homotopy_map_comp_component_comp_ι
    {n m : ℕ} (i : Fin (n + 1)) (θ : op ⦋m⦌ ⟶ op ⦋n⦌)
    (x : K.obj (op ⦋m⦌)) :
    Sigma.ι (fun _ : K.obj (op ⦋m⦌) ↦ U.obj (op ⦋m⦌)) x ≫
        (K × U).map θ ≫ copower_index_homotopy_component U H i =
      (U.map θ ≫ U.σ i) ≫
        Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
          (H.toSimplicialObjectHomotopy.h i (K.map θ x)) := by
  -- Rewrite the source coproduct injection through the simplicial copower structure map.
  calc
    Sigma.ι (fun _ : K.obj (op ⦋m⦌) ↦ U.obj (op ⦋m⦌)) x ≫
        (K × U).map θ ≫ copower_index_homotopy_component U H i =
      (U.map θ ≫
          Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
            (K.map θ x)) ≫
        copower_index_homotopy_component U H i := by
          simpa [simplicialCopower_map, Category.assoc] using
            congrArg (fun k ↦ k ≫ copower_index_homotopy_component U H i)
              (Sigma.ι_comp_map'
                (p := K.map θ)
                (q := fun _ ↦ U.map θ)
                x)
    _ = U.map θ ≫
          (Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
              (K.map θ x) ≫
            copower_index_homotopy_component U H i) := by
            simp [Category.assoc]
    _ = U.map θ ≫
          (U.σ i ≫
            Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
              (H.toSimplicialObjectHomotopy.h i (K.map θ x))) := by
            simpa using
              congrArg (fun k ↦ U.map θ ≫ k)
                (copower_index_homotopy_component_comp_ι
                  (U := U) (H := H) i (K.map θ x))
    _ = (U.map θ ≫ U.σ i) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (H.toSimplicialObjectHomotopy.h i (K.map θ x)) := by
            simp [Category.assoc]

/-- Helper for Lemma 14.26.8: the lifted zero component lands on the `b`-endpoint after the
target face map. -/
private theorem copower_index_homotopy_zero_field
    (n : ℕ) :
    copower_index_homotopy_component U H (0 : Fin (n + 1)) ≫ (L × U).δ 0 =
      (simplicialCopowerIndexHom U b).app (op ⦋n⦌) := by
  let H' := H.toSimplicialObjectHomotopy
  let θ : op ⦋n + 1⦌ ⟶ op ⦋n⦌ := (SimplexCategory.δ (0 : Fin (n + 2))).op
  -- Compare both morphisms on each coproduct summand of `(K × U).obj _`.
  apply Sigma.hom_ext
  intro x
  have hIndex : L.map θ (H'.h (0 : Fin (n + 1)) x) = b.app (op ⦋n⦌) x := by
    -- The simplicial-set homotopy endpoint condition identifies the target summand.
    simpa [θ, SimplicialObject.δ_def] using congrFun (H'.h_zero_comp_δ_zero n) x
  have hU : U.σ (0 : Fin (n + 1)) ≫ U.map θ = 𝟙 (U.obj (op ⦋n⦌)) := by
    -- The `U`-part collapses by the endpoint simplicial identity.
    simpa [θ, SimplicialObject.δ_def] using (U.δ_comp_σ_self (i := (0 : Fin (n + 1))))
  -- Normalize the left-hand side, then identify the index and the `U`-component separately.
  have hLeft :
      Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          copower_index_homotopy_component U H (0 : Fin (n + 1)) ≫
            (L × U).map θ =
        (U.σ (0 : Fin (n + 1)) ≫ U.map θ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
            (L.map θ (H'.h (0 : Fin (n + 1)) x)) :=
    copower_index_homotopy_component_comp_map_comp_ι
      (U := U) (H := H)
      (i := (0 : Fin (n + 1)))
      θ
      x
  have hMiddle :
      (U.σ (0 : Fin (n + 1)) ≫ U.map θ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
            (L.map θ (H'.h (0 : Fin (n + 1)) x)) =
        Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
          (b.app (op ⦋n⦌) x) := by
    simpa [hU, hIndex]
  have hRight :
      Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
          (b.app (op ⦋n⦌) x) =
        Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          (simplicialCopowerIndexHom U b).app (op ⦋n⦌) := by
    simpa [simplicialCopowerIndexHom_app] using
      (Sigma.ι_comp_map'
        (p := b.app (op ⦋n⦌))
        (q := fun _ ↦ 𝟙 (U.obj (op ⦋n⦌)))
        x).symm
  exact hLeft.trans (hMiddle.trans hRight)

/-- Helper for Lemma 14.26.8: the lifted last component lands on the `a`-endpoint after the last
target face map. -/
private theorem copower_index_homotopy_last_field
    (n : ℕ) :
    copower_index_homotopy_component U H (Fin.last n) ≫ (L × U).δ (Fin.last (n + 1)) =
      (simplicialCopowerIndexHom U a).app (op ⦋n⦌) := by
  let H' := H.toSimplicialObjectHomotopy
  let θ : op ⦋n + 1⦌ ⟶ op ⦋n⦌ := (SimplexCategory.δ (Fin.last (n + 1))).op
  -- Compare both morphisms on each coproduct summand of `(K × U).obj _`.
  apply Sigma.hom_ext
  intro x
  have hIndex :
      L.map θ (H'.h (Fin.last n) x) = a.app (op ⦋n⦌) x := by
    -- The other endpoint condition identifies the target summand.
    simpa [θ, SimplicialObject.δ_def] using congrFun (H'.h_last_comp_δ_last n) x
  have hU :
      U.σ (Fin.last n) ≫ U.map θ = 𝟙 (U.obj (op ⦋n⦌)) := by
    -- The final face and degeneracy cancel on `U`.
    simpa [θ, SimplicialObject.δ_def] using (U.δ_comp_σ_succ (i := Fin.last n))
  -- Normalize the left-hand side and then rewrite the index and `U`-part to the endpoint map.
  have hLeft :
      Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          copower_index_homotopy_component U H (Fin.last n) ≫
            (L × U).map θ =
        (U.σ (Fin.last n) ≫ U.map θ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
            (L.map θ (H'.h (Fin.last n) x)) :=
    copower_index_homotopy_component_comp_map_comp_ι
      (U := U) (H := H)
      (i := Fin.last n)
      θ
      x
  have hMiddle :
      (U.σ (Fin.last n) ≫ U.map θ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
            (L.map θ (H'.h (Fin.last n) x)) =
        Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
          (a.app (op ⦋n⦌) x) := by
    simpa [hU, hIndex]
  have hRight :
      Sigma.ι (fun _ : L.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌))
          (a.app (op ⦋n⦌) x) =
        Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          (simplicialCopowerIndexHom U a).app (op ⦋n⦌) := by
    simpa [simplicialCopowerIndexHom_app] using
      (Sigma.ι_comp_map'
        (p := a.app (op ⦋n⦌))
        (q := fun _ ↦ 𝟙 (U.obj (op ⦋n⦌)))
        x).symm
  exact hLeft.trans (hMiddle.trans hRight)

/-- Helper for Lemma 14.26.8: the lifted components satisfy the non-adjacent face identity in the
case `i ≤ j.castSucc`. -/
private theorem copower_index_homotopy_face_succ_comp_δ_castSucc_of_lt
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) :
    copower_index_homotopy_component U H j.succ ≫ (L × U).δ i.castSucc =
      (K × U).δ i ≫ copower_index_homotopy_component U H j := by
  let H' := H.toSimplicialObjectHomotopy
  -- Compare both sides on each coproduct summand of `(K × U).obj _`.
  apply Sigma.hom_ext
  intro x
  have hIndex :
      L.δ i.castSucc (H'.h j.succ x) = H'.h j (K.δ i x) := by
    -- The simplicial-set homotopy identity identifies the target summand.
    simpa using congrFun (H'.h_succ_comp_δ_castSucc_of_lt i j hij) x
  have hU : U.σ j.succ ≫ U.δ i.castSucc = U.δ i ≫ U.σ j := by
    -- The `U`-part satisfies the corresponding simplicial identity.
    simpa using (U.δ_comp_σ_of_le hij)
  -- Normalize the left-hand side, rewrite the common `U`-part and index, and read it back as the
  -- normalized right-hand side.
  have hLeft :
      Sigma.ι (fun _ : K.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌)) x ≫
          copower_index_homotopy_component U H j.succ ≫
            (L × U).δ i.castSucc =
        (U.σ j.succ ≫ U.δ i.castSucc) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ i.castSucc (H'.h j.succ x)) := by
    simpa [SimplicialObject.δ_def] using
      copower_index_homotopy_component_comp_map_comp_ι
        (U := U) (H := H)
        (i := j.succ)
        ((SimplexCategory.δ i.castSucc).op)
        x
  have hMiddle :
      (U.σ j.succ ≫ U.δ i.castSucc) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ i.castSucc (H'.h j.succ x)) =
        (U.δ i ≫ U.σ j) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (H'.h j (K.δ i x)) := by
    simpa [hU, hIndex]
  have hRight :
      (U.δ i ≫ U.σ j) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (H'.h j (K.δ i x)) =
        Sigma.ι (fun _ : K.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌)) x ≫
          (K × U).δ i ≫
            copower_index_homotopy_component U H j := by
    symm
    simpa [SimplicialObject.δ_def] using
      copower_index_homotopy_map_comp_component_comp_ι
        (U := U) (H := H)
        (i := j)
        ((SimplexCategory.δ i).op)
        x
  exact hLeft.trans (hMiddle.trans hRight)

/-- Helper for Lemma 14.26.8: the lifted components satisfy the adjacent face identity. -/
private theorem copower_index_homotopy_face_succ_comp_δ_castSucc_succ
    {n : ℕ} (j : Fin (n + 1)) :
    copower_index_homotopy_component U H j.succ ≫ (L × U).δ j.castSucc.succ =
      copower_index_homotopy_component U H j.castSucc ≫ (L × U).δ j.castSucc.succ := by
  let H' := H.toSimplicialObjectHomotopy
  -- Compare both sides on each coproduct summand of `(K × U).obj _`.
  apply Sigma.hom_ext
  intro x
  have hIndex :
      L.δ j.castSucc.succ (H'.h j.succ x) =
        L.δ j.castSucc.succ (H'.h j.castSucc x) := by
    -- The adjacent face relation identifies the two target summands.
    simpa using congrFun (H'.h_succ_comp_δ_castSucc_succ j) x
  have hULeft : U.σ j.succ ≫ U.δ j.castSucc.succ = 𝟙 (U.obj (op ⦋n + 1⦌)) := by
    -- The left `U`-composite is an adjacent degeneracy/face cancellation.
    simpa [← Fin.castSucc_succ] using (U.δ_comp_σ_self (i := j.succ))
  have hURight : U.σ j.castSucc ≫ U.δ j.castSucc.succ = 𝟙 (U.obj (op ⦋n + 1⦌)) := by
    -- The right `U`-composite is the complementary endpoint cancellation.
    simpa using (U.δ_comp_σ_succ (i := j.castSucc))
  -- Normalize both sides to the same target coproduct injection.
  have hLeft :
      Sigma.ι (fun _ : K.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌)) x ≫
          copower_index_homotopy_component U H j.succ ≫
            (L × U).δ j.castSucc.succ =
        (U.σ j.succ ≫ U.δ j.castSucc.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ j.castSucc.succ (H'.h j.succ x)) := by
    simpa [SimplicialObject.δ_def] using
      copower_index_homotopy_component_comp_map_comp_ι
        (U := U) (H := H)
        (i := j.succ)
        ((SimplexCategory.δ j.castSucc.succ).op)
        x
  have hMiddle₁ :
      (U.σ j.succ ≫ U.δ j.castSucc.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ j.castSucc.succ (H'.h j.succ x)) =
        Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
          (L.δ j.castSucc.succ (H'.h j.castSucc x)) := by
    simpa [hULeft, hIndex]
  have hMiddle₂ :
      Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
          (L.δ j.castSucc.succ (H'.h j.castSucc x)) =
        (U.σ j.castSucc ≫ U.δ j.castSucc.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ j.castSucc.succ (H'.h j.castSucc x)) := by
    simpa [hURight]
  have hRight :
      (U.σ j.castSucc ≫ U.δ j.castSucc.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ j.castSucc.succ (H'.h j.castSucc x)) =
        Sigma.ι (fun _ : K.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌)) x ≫
          copower_index_homotopy_component U H j.castSucc ≫
            (L × U).δ j.castSucc.succ := by
    symm
    simpa [SimplicialObject.δ_def] using
      copower_index_homotopy_component_comp_map_comp_ι
        (U := U) (H := H)
        (i := j.castSucc)
        ((SimplexCategory.δ j.castSucc.succ).op)
        x
  exact hLeft.trans (hMiddle₁.trans (hMiddle₂.trans hRight))

/-- Helper for Lemma 14.26.8: the lifted components satisfy the other non-adjacent face identity
in the case `j.castSucc < i`. -/
private theorem copower_index_homotopy_face_castSucc_comp_δ_succ_of_lt
    {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) :
    copower_index_homotopy_component U H j.castSucc ≫ (L × U).δ i.succ =
      (K × U).δ i ≫ copower_index_homotopy_component U H j := by
  let H' := H.toSimplicialObjectHomotopy
  -- Compare both sides on each coproduct summand of `(K × U).obj _`.
  apply Sigma.hom_ext
  intro x
  have hIndex :
      L.δ i.succ (H'.h j.castSucc x) = H'.h j (K.δ i x) := by
    -- The complementary simplicial-set homotopy identity identifies the target summand.
    simpa using congrFun (H'.h_castSucc_comp_δ_succ_of_lt i j hji) x
  have hU : U.σ j.castSucc ≫ U.δ i.succ = U.δ i ≫ U.σ j := by
    -- The `U`-part satisfies the complementary simplicial identity.
    simpa using (U.δ_comp_σ_of_gt hji)
  -- Normalize the two sides to the same coproduct injection.
  have hLeft :
      Sigma.ι (fun _ : K.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌)) x ≫
          copower_index_homotopy_component U H j.castSucc ≫
            (L × U).δ i.succ =
        (U.σ j.castSucc ≫ U.δ i.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ i.succ (H'.h j.castSucc x)) := by
    simpa [SimplicialObject.δ_def] using
      copower_index_homotopy_component_comp_map_comp_ι
        (U := U) (H := H)
        (i := j.castSucc)
        ((SimplexCategory.δ i.succ).op)
        x
  have hMiddle :
      (U.σ j.castSucc ≫ U.δ i.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (L.δ i.succ (H'.h j.castSucc x)) =
        (U.δ i ≫ U.σ j) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (H'.h j (K.δ i x)) := by
    simpa [hU, hIndex]
  have hRight :
      (U.δ i ≫ U.σ j) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌))
            (H'.h j (K.δ i x)) =
        Sigma.ι (fun _ : K.obj (op ⦋n + 1⦌) ↦ U.obj (op ⦋n + 1⦌)) x ≫
          (K × U).δ i ≫
            copower_index_homotopy_component U H j := by
    symm
    simpa [SimplicialObject.δ_def] using
      copower_index_homotopy_map_comp_component_comp_ι
        (U := U) (H := H)
        (i := j)
        ((SimplexCategory.δ i).op)
        x
  exact hLeft.trans (hMiddle.trans hRight)

/-- Helper for Lemma 14.26.8: the lifted components satisfy the first degeneracy identity when
`i ≤ j`. -/
private theorem copower_index_homotopy_degeneracy_comp_σ_castSucc_of_le
    {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    copower_index_homotopy_component U H j ≫ (L × U).σ i.castSucc =
      (K × U).σ i ≫ copower_index_homotopy_component U H j.succ := by
  let H' := H.toSimplicialObjectHomotopy
  -- Compare both sides on each coproduct summand of `(K × U).obj _`.
  apply Sigma.hom_ext
  intro x
  have hIndex :
      L.σ i.castSucc (H'.h j x) = H'.h j.succ (K.σ i x) := by
    -- The simplicial-set homotopy degeneracy identity identifies the target summand.
    simpa using congrFun (H'.h_comp_σ_castSucc_of_le i j hij) x
  have hU : U.σ j ≫ U.σ i.castSucc = U.σ i ≫ U.σ j.succ := by
    -- The `U`-part satisfies the corresponding degeneracy identity.
    simpa using (U.σ_comp_σ hij)
  -- Normalize both sides to the same target coproduct injection.
  have hLeft :
      Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          copower_index_homotopy_component U H j ≫
            (L × U).σ i.castSucc =
        (U.σ j ≫ U.σ i.castSucc) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (L.σ i.castSucc (H'.h j x)) := by
    simpa [SimplicialObject.σ_def] using
      copower_index_homotopy_component_comp_map_comp_ι
        (U := U) (H := H)
        (i := j)
        ((SimplexCategory.σ i.castSucc).op)
        x
  have hMiddle :
      (U.σ j ≫ U.σ i.castSucc) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (L.σ i.castSucc (H'.h j x)) =
        (U.σ i ≫ U.σ j.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (H'.h j.succ (K.σ i x)) := by
    simpa [hU, hIndex]
  have hRight :
      (U.σ i ≫ U.σ j.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (H'.h j.succ (K.σ i x)) =
        Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          (K × U).σ i ≫
            copower_index_homotopy_component U H j.succ := by
    symm
    simpa [SimplicialObject.σ_def] using
      copower_index_homotopy_map_comp_component_comp_ι
        (U := U) (H := H)
        (i := j.succ)
        ((SimplexCategory.σ i).op)
        x
  exact hLeft.trans (hMiddle.trans hRight)

/-- Helper for Lemma 14.26.8: the lifted components satisfy the second degeneracy identity when
`j ≤ i`. -/
private theorem copower_index_homotopy_degeneracy_comp_σ_succ_of_lt
    {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) :
    copower_index_homotopy_component U H j ≫ (L × U).σ i.succ =
      (K × U).σ i ≫ copower_index_homotopy_component U H j.castSucc := by
  let H' := H.toSimplicialObjectHomotopy
  -- Compare both sides on each coproduct summand of `(K × U).obj _`.
  apply Sigma.hom_ext
  intro x
  have hIndex :
      L.σ i.succ (H'.h j x) = H'.h j.castSucc (K.σ i x) := by
    -- The complementary simplicial-set degeneracy identity identifies the target summand.
    simpa using congrFun (H'.h_comp_σ_succ_of_lt i j hji) x
  have hU : U.σ j ≫ U.σ i.succ = U.σ i ≫ U.σ j.castSucc := by
    -- The `U`-part is the reversed standard degeneracy identity.
    simpa using (U.σ_comp_σ (i := j) (j := i) hji).symm
  -- Normalize both sides to the same target coproduct injection.
  have hLeft :
      Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          copower_index_homotopy_component U H j ≫
            (L × U).σ i.succ =
        (U.σ j ≫ U.σ i.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (L.σ i.succ (H'.h j x)) := by
    simpa [SimplicialObject.σ_def] using
      copower_index_homotopy_component_comp_map_comp_ι
        (U := U) (H := H)
        (i := j)
        ((SimplexCategory.σ i.succ).op)
        x
  have hMiddle :
      (U.σ j ≫ U.σ i.succ) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (L.σ i.succ (H'.h j x)) =
        (U.σ i ≫ U.σ j.castSucc) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (H'.h j.castSucc (K.σ i x)) := by
    simpa [hU, hIndex]
  have hRight :
      (U.σ i ≫ U.σ j.castSucc) ≫
          Sigma.ι (fun _ : L.obj (op ⦋n + 2⦌) ↦ U.obj (op ⦋n + 2⦌))
            (H'.h j.castSucc (K.σ i x)) =
        Sigma.ι (fun _ : K.obj (op ⦋n⦌) ↦ U.obj (op ⦋n⦌)) x ≫
          (K × U).σ i ≫
            copower_index_homotopy_component U H j.castSucc := by
    symm
    simpa [SimplicialObject.σ_def] using
      copower_index_homotopy_map_comp_component_comp_ι
        (U := U) (H := H)
        (i := j.castSucc)
        ((SimplexCategory.σ i).op)
        x
  exact hLeft.trans (hMiddle.trans hRight)

/-- Helper for Lemma 14.26.8: a simplicial-set homotopy lifts to a simplicial homotopy between
the induced copower reindexing maps. -/
private noncomputable def simplicialCopowerIndexHom_homotopy
    {K L : SSet.{0}} (U : SimplicialObject C)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : K.obj Δ ↦ U.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : L.obj Δ ↦ U.obj Δ)]
    {a b : K ⟶ L} (H : SSet.Homotopy a b) :
    Homotopy (simplicialCopowerIndexHom U a) (simplicialCopowerIndexHom U b) where
  h {n} i := copower_index_homotopy_component U H i
  h_zero_comp_δ_zero := copower_index_homotopy_zero_field U H
  h_last_comp_δ_last := copower_index_homotopy_last_field U H
  h_succ_comp_δ_castSucc_of_lt := copower_index_homotopy_face_succ_comp_δ_castSucc_of_lt U H
  h_succ_comp_δ_castSucc_succ := copower_index_homotopy_face_succ_comp_δ_castSucc_succ U H
  h_castSucc_comp_δ_succ_of_lt := copower_index_homotopy_face_castSucc_comp_δ_succ_of_lt U H
  h_comp_σ_castSucc_of_le := copower_index_homotopy_degeneracy_comp_σ_castSucc_of_le U H
  h_comp_σ_succ_of_lt := copower_index_homotopy_degeneracy_comp_σ_succ_of_lt U H

end CopowerIndexHomotopy

-- Proof sketch: use the combinatorial simplicial-homotopy description. The standard map
-- `Δ[1] × Δ[1] ⟶ Δ[1]` given by taking the maximum on vertices induces a homotopy from the
-- identity of `Δ[1] × U` to `π ≫ e₀`.
/-- Lemma 14.26.8 (3): the identity of `Δ[1] × U` is simplicially homotopic to `e₀ ∘ π`. -/
theorem simplicialIntervalCylinder_id_homotopy_projection_endpointZero
    (U : SimplicialObject C) :
    Homotopic (𝟙 ((Δ[1] : SSet.{0}) × U))
      (simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₀ U) := by
  -- Route correction: the `min` formula gives a directed homotopy from the constant-`0`
  -- endomorphism to the identity, so we use symmetry after lifting it to the copower cylinder.
  have hmin :
      Homotopy
        (simplicialCopowerIndexHom U
          (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (1 : Fin 2)))
        (𝟙 ((Δ[1] : SSet.{0}) × U)) :=
    by
      simpa [simplicialCopowerIndexHom_id] using
        (simplicialCopowerIndexHom_homotopy U deltaOne_min_homotopy)
  have htarget :
      simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₀ U =
        simplicialCopowerIndexHom U
          (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (1 : Fin 2)) := by
    -- Rewrite `π ≫ e₀` as reindexing along the constant-`0` interval map.
    calc
      simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₀ U =
          (simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ pointCopowerSection U) ≫
            simplicialCopowerIndexHom U (SSet.stdSimplex.δ (1 : Fin 2)) := by
              simp [e₀, Category.assoc]
      _ = simplicialCopowerIndexHom U (isTerminalObj₀.from (Δ[1] : SSet.{0})) ≫
            simplicialCopowerIndexHom U (SSet.stdSimplex.δ (1 : Fin 2)) := by
              rw [projection_comp_pointCopowerSection]
      _ = simplicialCopowerIndexHom U
            (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (1 : Fin 2)) := by
              rw [← simplicialCopowerIndexHom_comp]
  simpa [htarget] using (Homotopic.of_homotopy hmin).symm

-- Proof sketch: use the combinatorial simplicial-homotopy description. The standard map
-- `Δ[1] × Δ[1] ⟶ Δ[1]` given by taking the minimum on vertices induces a homotopy from the
-- identity of `Δ[1] × U` to `π ≫ e₁`.
/-- Lemma 14.26.8 (4): the identity of `Δ[1] × U` is simplicially homotopic to `e₁ ∘ π`. -/
theorem simplicialIntervalCylinder_id_homotopy_projection_endpointOne
    (U : SimplicialObject C) :
    Homotopic (𝟙 ((Δ[1] : SSet.{0}) × U))
      (simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₁ U) := by
  have hmax :
      Homotopy (𝟙 ((Δ[1] : SSet.{0}) × U))
        (simplicialCopowerIndexHom U
          (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2))) :=
    by
      simpa [simplicialCopowerIndexHom_id] using
        (simplicialCopowerIndexHom_homotopy U deltaOne_max_homotopy)
  have htarget :
      simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₁ U =
        simplicialCopowerIndexHom U
          (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2)) := by
    -- Rewrite `π ≫ e₁` as reindexing along the constant-`1` interval map.
    calc
      simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₁ U =
          (simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ pointCopowerSection U) ≫
            simplicialCopowerIndexHom U (SSet.stdSimplex.δ (0 : Fin 2)) := by
              simp [e₁, Category.assoc]
      _ = simplicialCopowerIndexHom U (isTerminalObj₀.from (Δ[1] : SSet.{0})) ≫
            simplicialCopowerIndexHom U (SSet.stdSimplex.δ (0 : Fin 2)) := by
              rw [projection_comp_pointCopowerSection]
      _ = simplicialCopowerIndexHom U
            (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2)) := by
              rw [← simplicialCopowerIndexHom_comp]
  simpa [htarget] using Homotopic.of_homotopy hmax

end CategoryTheory.SimplicialObject
