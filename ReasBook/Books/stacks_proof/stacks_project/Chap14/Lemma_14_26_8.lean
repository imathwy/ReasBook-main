import stacks_proof.stacks_project.Chap14.Definition_14_26_1
import stacks_proof.stacks_project.Chap14.Lemma_14_13_3
import Mathlib.Tactic.StacksAttribute

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
@[stacks 019O]
theorem simplicialIntervalProjection_comp_endpointOne (U : SimplicialObject C) :
    e₁ U ≫ simplicialCopowerProjection U (Δ[1] : SSet.{0}) = 𝟙 U := by
  simpa [e₁] using
    simplicialIntervalProjection_comp_endpoint U (SSet.stdSimplex.δ (0 : Fin 2))

-- Proof sketch: in each simplicial degree, the endpoint inclusion `e₀` lands in the coproduct
-- summand indexed by the constant `0` simplex, and the projection is the identity on every
-- summand, so the composite is the identity componentwise.
/-- Lemma 14.26.8 (2): the projection `π : Δ[1] × U ⟶ U` composed with the endpoint map
`e₀ : U ⟶ Δ[1] × U` is the identity on `U`. -/
@[stacks 019O]
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

/-- Helper for Lemma 14.26.8: a simplicial-set homotopy lifts to a simplicial homotopy between
the induced copower reindexing maps. -/
private noncomputable def simplicialCopowerIndexHom_homotopy
    {K L : SSet.{0}} (U : SimplicialObject C)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : K.obj Δ ↦ U.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : L.obj Δ ↦ U.obj Δ)]
    {a b : K ⟶ L} (H : SSet.Homotopy a b) :
    Homotopy (simplicialCopowerIndexHom U a) (simplicialCopowerIndexHom U b) where
  -- Reindex each coproduct summand using the simplicial-homotopy component on indices, and use
  -- the same degeneracy operator on the copied `U` factor.
  h {n} i :=
    Sigma.map' ((H.toSimplicialObjectHomotopy).h i) (fun _ ↦ U.σ i)
  h_zero_comp_δ_zero n := by
    apply Sigma.hom_ext
    intro x
    -- Read the face map on the chosen summand and then use the endpoint identity of `H`.
    have hface_base :
        Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            Sigma.map' (L.δ 0)
              (fun _ : L _⦋n + 1⦌ ↦ (U.δ 0 : U _⦋n + 1⦌ ⟶ U _⦋n⦌)) =
          U.δ 0 ≫
            Sigma.ι (fun y ↦ U _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ 0)
          (q := fun _ : L _⦋n + 1⦌ ↦ (U.δ 0 : U _⦋n + 1⦌ ⟶ U _⦋n⦌))
          ((H.toSimplicialObjectHomotopy).h 0 x))
    have hface :
        U.σ 0 ≫ Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            (L × U).δ 0 =
          U.σ 0 ≫ U.δ 0 ≫
            Sigma.ι (fun y ↦ U _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x)) := by
      change U.σ 0 ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            Sigma.map' (L.δ 0)
              (fun _ : L _⦋n + 1⦌ ↦ (U.δ 0 : U _⦋n + 1⦌ ⟶ U _⦋n⦌)) =
        U.σ 0 ≫ U.δ 0 ≫
          Sigma.ι (fun y ↦ U _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ 0 ≫ k) hface_base
    have hindex :
        L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x) = b.app (op ⦋n⦌) x :=
      congrFun ((H.toSimplicialObjectHomotopy).h_zero_comp_δ_zero n) x
    simpa [simplicialCopowerIndexHom_app, simplicialCopower_map, Category.assoc] using
      calc
        U.σ 0 ≫ Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            (L × U).δ 0 =
          U.σ 0 ≫ U.δ 0 ≫
            Sigma.ι (fun y ↦ U _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x)) := hface
        _ = U.σ 0 ≫ U.δ 0 ≫ Sigma.ι (fun y ↦ U _⦋n⦌) (b.app (op ⦋n⦌) x) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ U _⦋n⦌) (b.app (op ⦋n⦌) x) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ Sigma.ι (fun y ↦ U _⦋n⦌) (b.app (op ⦋n⦌) x))
                  (U.δ_comp_σ_self (i := (0 : Fin (n + 1))))
  h_last_comp_δ_last n := by
    apply Sigma.hom_ext
    intro x
    -- The last face case is the same component computation, now using the terminal endpoint.
    have hface_base :
        Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            Sigma.map' (L.δ (Fin.last (n + 1)))
              (fun _ : L _⦋n + 1⦌ ↦
                (U.δ (Fin.last (n + 1)) : U _⦋n + 1⦌ ⟶ U _⦋n⦌)) =
          U.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ U _⦋n⦌)
              (L.δ (Fin.last (n + 1))
                ((H.toSimplicialObjectHomotopy).h (Fin.last n) x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ (Fin.last (n + 1)))
          (q := fun _ : L _⦋n + 1⦌ ↦
            (U.δ (Fin.last (n + 1)) : U _⦋n + 1⦌ ⟶ U _⦋n⦌))
          ((H.toSimplicialObjectHomotopy).h (Fin.last n) x))
    have hface :
        U.σ (Fin.last n) ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            (L × U).δ (Fin.last (n + 1)) =
          U.σ (Fin.last n) ≫ U.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ U _⦋n⦌)
              (L.δ (Fin.last (n + 1))
                ((H.toSimplicialObjectHomotopy).h (Fin.last n) x)) := by
      change U.σ (Fin.last n) ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            Sigma.map' (L.δ (Fin.last (n + 1)))
              (fun _ : L _⦋n + 1⦌ ↦
                (U.δ (Fin.last (n + 1)) : U _⦋n + 1⦌ ⟶ U _⦋n⦌)) =
        U.σ (Fin.last n) ≫ U.δ (Fin.last (n + 1)) ≫
          Sigma.ι (fun y ↦ U _⦋n⦌)
            (L.δ (Fin.last (n + 1)) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ (Fin.last n) ≫ k) hface_base
    have hindex :
        L.δ (Fin.last (n + 1)) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) =
          a.app (op ⦋n⦌) x :=
      congrFun ((H.toSimplicialObjectHomotopy).h_last_comp_δ_last n) x
    simpa [simplicialCopowerIndexHom_app, simplicialCopower_map, Category.assoc] using
      calc
        U.σ (Fin.last n) ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            (L × U).δ (Fin.last (n + 1)) =
          U.σ (Fin.last n) ≫ U.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ U _⦋n⦌)
              (L.δ (Fin.last (n + 1))
                ((H.toSimplicialObjectHomotopy).h (Fin.last n) x)) := hface
        _ = U.σ (Fin.last n) ≫ U.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ U _⦋n⦌) (a.app (op ⦋n⦌) x) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ U _⦋n⦌) (a.app (op ⦋n⦌) x) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ Sigma.ι (fun y ↦ U _⦋n⦌) (a.app (op ⦋n⦌) x))
                  (U.δ_comp_σ_succ (i := Fin.last n))
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    apply Sigma.hom_ext
    intro x
    -- Move the face map across the chosen coproduct summand and rewrite the index via `H`.
    have hface_base :
        Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ i.castSucc)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ i.castSucc : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ i.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ i.castSucc)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (U.δ i.castSucc : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.succ x))
    have hface :
        U.σ j.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × U).δ i.castSucc =
          U.σ j.succ ≫ U.δ i.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      change U.σ j.succ ≫
          Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ i.castSucc)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ i.castSucc : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
        U.σ j.succ ≫ U.δ i.castSucc ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌)
            (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ j.succ ≫ k) hface_base
    have hindex :
        L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x) =
          (H.toSimplicialObjectHomotopy).h j (K.δ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_succ_comp_δ_castSucc_of_lt i j hij) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ i ≫ U.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
      let faceMap : (∐ fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) ⟶ (∐ fun _ : K _⦋n⦌ ↦ U _⦋n⦌) :=
        Sigma.map' (K.δ i) (fun _ : K _⦋n + 1⦌ ↦ (U.δ i : U _⦋n + 1⦌ ⟶ U _⦋n⦌))
      let reindex : (∐ fun _ : K _⦋n⦌ ↦ U _⦋n⦌) ⟶ (∐ fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j)
          (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
      have hδ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i =
            U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ faceMap =
          U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x)
        simpa [faceMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.δ i)
            (q := fun _ : K _⦋n + 1⦌ ↦ (U.δ i : U _⦋n + 1⦌ ⟶ U _⦋n⦌))
            x)
      have hσ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j)
                (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) =
            U.σ j ≫
              Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫ reindex =
          U.σ j ≫ Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j (K.δ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j)
            (q := fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
            (K.δ i x))
      calc
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ faceMap ≫ reindex =
                U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hδ
        _ = U.δ i ≫ U.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ U.δ i ≫ k) hσ
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        U.σ j.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × U).δ i.castSucc =
          U.σ j.succ ≫ U.δ i.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := hface
        _ = U.δ i ≫ U.σ j ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ U _⦋n + 1⦌)
                      (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)))
                  (U.δ_comp_σ_of_le hij)
        _ = U.δ i ≫ U.σ j ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j) (fun y ↦ U.σ j) := by
              exact htarget.symm
  h_succ_comp_δ_castSucc_succ {n} j := by
    apply Sigma.hom_ext
    intro x
    -- Both sides reduce to the same coproduct summand after the adjacent face identities.
    have hleft_base :
        Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ j.castSucc.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ j.castSucc.succ)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (U.δ j.castSucc.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.succ x))
    have hleft :
        U.σ j.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × U).δ j.castSucc.succ =
          U.σ j.succ ≫ U.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      change U.σ j.succ ≫
          Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ j.castSucc.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
        U.σ j.succ ≫ U.δ j.castSucc.succ ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ j.succ ≫ k) hleft_base
    have hright_base :
        Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ j.castSucc.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ j.castSucc.succ)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (U.δ j.castSucc.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.castSucc x))
    have hright :
        U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × U).δ j.castSucc.succ =
          U.σ j.castSucc ≫ U.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      change U.σ j.castSucc ≫
          Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ j.castSucc.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
        U.σ j.castSucc ≫ U.δ j.castSucc.succ ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ j.castSucc ≫ k) hright_base
    have hright' :
        U.σ j.castSucc ≫ U.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) =
          U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × U).δ j.castSucc.succ := by
      simpa [Category.assoc] using hright.symm
    have htail :
        Sigma.ι (fun y ↦ U _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) =
          U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × U).δ j.castSucc.succ := by
      have hid :
          Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) =
            U.σ j.castSucc ≫ U.δ j.castSucc.succ ≫
              Sigma.ι (fun y ↦ U _⦋n + 1⦌)
                (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫
              Sigma.ι (fun y ↦ U _⦋n + 1⦌)
                (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)))
            (U.δ_comp_σ_succ (i := j.castSucc)).symm
      exact hid.trans hright'
    have hindex :
        L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x) =
          L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_succ_comp_δ_castSucc_succ j) x
    have hleft_to_mid :
        U.σ j.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × U).δ j.castSucc.succ =
          Sigma.ι (fun y ↦ U _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      calc
        U.σ j.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × U).δ j.castSucc.succ =
          U.σ j.succ ≫ U.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := hleft
        _ = Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ U _⦋n + 1⦌)
                      (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)))
                  (U.δ_comp_σ_self (i := j.succ))
    have hmid_to_right :
        Sigma.ι (fun y ↦ U _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) =
          U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × U).δ j.castSucc.succ := by
      simpa [hindex] using htail
    simpa [simplicialCopower_map, Category.assoc] using hleft_to_mid.trans hmid_to_right
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    apply Sigma.hom_ext
    intro x
    -- This is the complementary face case, using `δ_comp_σ_of_gt` on `U`.
    have hface_base :
        Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ i.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ i.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ i.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ i.succ)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (U.δ i.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.castSucc x))
    have hface :
        U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × U).δ i.succ =
          U.σ j.castSucc ≫ U.δ i.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      change U.σ j.castSucc ≫
          Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ i.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (U.δ i.succ : U _⦋n + 1 + 1⦌ ⟶ U _⦋n + 1⦌)) =
        U.σ j.castSucc ≫ U.δ i.succ ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌)
            (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ j.castSucc ≫ k) hface_base
    have hindex :
        L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x) =
          (H.toSimplicialObjectHomotopy).h j (K.δ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_castSucc_comp_δ_succ_of_lt i j hji) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ i ≫ U.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
      let faceMap : (∐ fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) ⟶ (∐ fun _ : K _⦋n⦌ ↦ U _⦋n⦌) :=
        Sigma.map' (K.δ i) (fun _ : K _⦋n + 1⦌ ↦ (U.δ i : U _⦋n + 1⦌ ⟶ U _⦋n⦌))
      let reindex : (∐ fun _ : K _⦋n⦌ ↦ U _⦋n⦌) ⟶ (∐ fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j)
          (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
      have hδ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i =
            U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ faceMap =
          U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x)
        simpa [faceMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.δ i)
            (q := fun _ : K _⦋n + 1⦌ ↦ (U.δ i : U _⦋n + 1⦌ ⟶ U _⦋n⦌))
            x)
      have hσ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j)
                (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) =
            U.σ j ≫
              Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫ reindex =
          U.σ j ≫ Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j (K.δ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j)
            (q := fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
            (K.δ i x))
      calc
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) =
          U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (U.σ j : U _⦋n⦌ ⟶ U _⦋n + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) x ≫ faceMap ≫ reindex =
                U.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) (K.δ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hδ
        _ = U.δ i ≫ U.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ U.δ i ≫ k) hσ
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × U).δ i.succ =
          U.σ j.castSucc ≫ U.δ i.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := hface
        _ = U.δ i ≫ U.σ j ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ U _⦋n + 1⦌)
                      (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)))
                  (U.δ_comp_σ_of_gt hji)
        _ = U.δ i ≫ U.σ j ≫
            Sigma.ι (fun y ↦ U _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ U _⦋n + 1⦌) x ≫ (K × U).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j) (fun y ↦ U.σ j) := by
              exact htarget.symm
  h_comp_σ_castSucc_of_le {n} i j hij := by
    apply Sigma.hom_ext
    intro x
    -- Expand the degeneracy map on the chosen summand and rewrite with the homotopy relation.
    have hdeg_base :
        Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.castSucc)
              (fun _ : L _⦋n + 1⦌ ↦
                (U.σ i.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
          U.σ i.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.σ i.castSucc)
          (q := fun _ : L _⦋n + 1⦌ ↦
            (U.σ i.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j x))
    have hdeg :
        U.σ j ≫ Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × U).σ i.castSucc =
          U.σ j ≫ U.σ i.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := by
      change U.σ j ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.castSucc)
              (fun _ : L _⦋n + 1⦌ ↦
                (U.σ i.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
        U.σ j ≫ U.σ i.castSucc ≫
          Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
            (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ j ≫ k) hdeg_base
    have hindex :
        L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x) =
          (H.toSimplicialObjectHomotopy).h j.succ (K.σ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_comp_σ_castSucc_of_le i j hij) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ (K × U).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
              (fun _ : K _⦋n + 1⦌ ↦ (U.σ j.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
          U.σ i ≫ U.σ j.succ ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
      let degMap : (∐ fun _ : K _⦋n⦌ ↦ U _⦋n⦌) ⟶ (∐ fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) :=
        Sigma.map' (K.σ i) (fun _ : K _⦋n⦌ ↦ (U.σ i : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
      let reindex : (∐ fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) ⟶ (∐ fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
          (fun _ : K _⦋n + 1⦌ ↦ (U.σ j.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌))
      have hσ₁ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ (K × U).σ i =
            U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ degMap =
          U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x)
        simpa [degMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.σ i)
            (q := fun _ : K _⦋n⦌ ↦ (U.σ i : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
            x)
      have hσ₂ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
                (fun _ : K _⦋n + 1⦌ ↦
                  (U.σ j.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
            U.σ j.succ ≫
              Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫ reindex =
          U.σ j.succ ≫ Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j.succ)
            (q := fun _ : K _⦋n + 1⦌ ↦
              (U.σ j.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌))
            (K.σ i x))
      calc
        Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ (K × U).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
              (fun _ : K _⦋n + 1⦌ ↦ (U.σ j.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
          U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
              (fun _ : K _⦋n + 1⦌ ↦ (U.σ j.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ degMap ≫ reindex =
                U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hσ₁
        _ = U.σ i ≫ U.σ j.succ ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ U.σ i ≫ k) hσ₂
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        U.σ j ≫ Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × U).σ i.castSucc =
          U.σ j ≫ U.σ i.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := hdeg
        _ = U.σ i ≫ U.σ j.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
                      (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)))
                  (U.σ_comp_σ hij)
        _ = U.σ i ≫ U.σ j.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ U _⦋n⦌) x ≫ (K × U).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ) (fun y ↦ U.σ j.succ) := by
              exact htarget.symm
  h_comp_σ_succ_of_lt {n} i j hji := by
    apply Sigma.hom_ext
    intro x
    -- The complementary degeneracy case uses the symmetric simplicial identity on `U`.
    have hdeg_base :
        Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.succ)
              (fun _ : L _⦋n + 1⦌ ↦
                (U.σ i.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
          U.σ i.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.σ i.succ)
          (q := fun _ : L _⦋n + 1⦌ ↦
            (U.σ i.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j x))
    have hdeg :
        U.σ j ≫ Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × U).σ i.succ =
          U.σ j ≫ U.σ i.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := by
      change U.σ j ≫
          Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.succ)
              (fun _ : L _⦋n + 1⦌ ↦
                (U.σ i.succ : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
        U.σ j ≫ U.σ i.succ ≫
          Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
            (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x))
      simpa [Category.assoc] using congrArg (fun k ↦ U.σ j ≫ k) hdeg_base
    have hindex :
        L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x) =
          (H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_comp_σ_succ_of_lt i j hji) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ (K × U).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun _ : K _⦋n + 1⦌ ↦
                (U.σ j.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
          U.σ i ≫ U.σ j.castSucc ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
      let degMap : (∐ fun _ : K _⦋n⦌ ↦ U _⦋n⦌) ⟶ (∐ fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) :=
        Sigma.map' (K.σ i) (fun _ : K _⦋n⦌ ↦ (U.σ i : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
      let reindex : (∐ fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) ⟶ (∐ fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
          (fun _ : K _⦋n + 1⦌ ↦ (U.σ j.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌))
      have hσ₁ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ (K × U).σ i =
            U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ degMap =
          U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x)
        simpa [degMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.σ i)
            (q := fun _ : K _⦋n⦌ ↦ (U.σ i : U _⦋n⦌ ⟶ U _⦋n + 1⦌))
            x)
      have hσ₂ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
                (fun _ : K _⦋n + 1⦌ ↦
                  (U.σ j.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
            U.σ j.castSucc ≫
              Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫ reindex =
          U.σ j.castSucc ≫ Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j.castSucc)
            (q := fun _ : K _⦋n + 1⦌ ↦
              (U.σ j.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌))
            (K.σ i x))
      calc
        Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ (K × U).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun _ : K _⦋n + 1⦌ ↦
                (U.σ j.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) =
          U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun _ : K _⦋n + 1⦌ ↦
                (U.σ j.castSucc : U _⦋n + 1⦌ ⟶ U _⦋n + 1 + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n⦌ ↦ U _⦋n⦌) x ≫ degMap ≫ reindex =
                U.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ U _⦋n + 1⦌) (K.σ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hσ₁
        _ = U.σ i ≫ U.σ j.castSucc ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ U.σ i ≫ k) hσ₂
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        U.σ j ≫ Sigma.ι (fun y ↦ U _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × U).σ i.succ =
          U.σ j ≫ U.σ i.succ ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := hdeg
        _ = U.σ i ≫ U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
                      (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)))
                  (U.σ_comp_σ hji).symm
        _ = U.σ i ≫ U.σ j.castSucc ≫
            Sigma.ι (fun y ↦ U _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ U _⦋n⦌) x ≫ (K × U).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun y ↦ U.σ j.castSucc) := by
              exact htarget.symm

end CopowerIndexHomotopy

/-- Helper for Lemma 14.26.8: after projecting `Δ[1] × U` to `U`, reinserting the endpoint
indexed by `i` is the same as reindexing along the corresponding constant endpoint map of
`Δ[1]`. -/
private theorem projection_comp_endpoint_as_index
    (U : SimplicialObject C) (i : Fin 2) :
    simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫
        (pointCopowerSection U ≫ simplicialCopowerIndexHom U (SSet.stdSimplex.δ i)) =
      simplicialCopowerIndexHom U
        (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ i) := by
  -- Rewrite the projection-section composite first, then collapse the two reindexing steps into
  -- a single simplicial-set composite.
  calc
    simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫
        (pointCopowerSection U ≫ simplicialCopowerIndexHom U (SSet.stdSimplex.δ i)) =
        (simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ pointCopowerSection U) ≫
          simplicialCopowerIndexHom U (SSet.stdSimplex.δ i) := by
            simp [Category.assoc]
    _ = simplicialCopowerIndexHom U (isTerminalObj₀.from (Δ[1] : SSet.{0})) ≫
          simplicialCopowerIndexHom U (SSet.stdSimplex.δ i) := by
            rw [projection_comp_pointCopowerSection]
    _ = simplicialCopowerIndexHom U
          (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ i) := by
            rw [← simplicialCopowerIndexHom_comp]

-- Proof sketch: use the combinatorial simplicial-homotopy description. The standard map
-- `Δ[1] × Δ[1] ⟶ Δ[1]` given by taking the maximum on vertices induces a homotopy from the
-- identity of `Δ[1] × U` to `π ≫ e₀`.
/-- Lemma 14.26.8 (3): the identity of `Δ[1] × U` is simplicially homotopic to `e₀ ∘ π`. -/
@[stacks 019O]
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
    -- Specialize the uniform endpoint-factorization helper to the `0`-vertex.
    simpa [e₀] using projection_comp_endpoint_as_index U (1 : Fin 2)
  simpa [htarget] using (Homotopic.of_homotopy hmin).symm

-- Proof sketch: use the combinatorial simplicial-homotopy description. The standard map
-- `Δ[1] × Δ[1] ⟶ Δ[1]` given by taking the minimum on vertices induces a homotopy from the
-- identity of `Δ[1] × U` to `π ≫ e₁`.
/-- Lemma 14.26.8 (4): the identity of `Δ[1] × U` is simplicially homotopic to `e₁ ∘ π`. -/
@[stacks 019O]
theorem simplicialIntervalCylinder_id_homotopy_projection_endpointOne
    (U : SimplicialObject C) :
    Homotopic (𝟙 ((Δ[1] : SSet.{0}) × U))
      (simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₁ U) := by
  have hmax :
      Homotopy (𝟙 ((Δ[1] : SSet.{0}) × U))
        (simplicialCopowerIndexHom U
          (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2))) :=
    by
      -- Lift the source `max` homotopy through the copower reindexing functor.
      simpa [simplicialCopowerIndexHom_id] using
        (simplicialCopowerIndexHom_homotopy U deltaOne_max_homotopy)
  have htarget :
      simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ e₁ U =
        simplicialCopowerIndexHom U
          (isTerminalObj₀.from (Δ[1] : SSet.{0}) ≫ SSet.stdSimplex.δ (0 : Fin 2)) := by
    -- Specialize the uniform endpoint-factorization helper to the `1`-vertex.
    simpa [e₁] using projection_comp_endpoint_as_index U (0 : Fin 2)
  simpa [htarget] using Homotopic.of_homotopy hmax

end CategoryTheory.SimplicialObject
