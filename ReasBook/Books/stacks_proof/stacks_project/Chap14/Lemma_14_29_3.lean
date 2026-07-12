import Mathlib
import StacksProject_2024.Chap14.Lemma_14_13_3
import StacksProject_2024.Chap14.Lemma_14_27_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicTopology
open AlgebraicTopology.DoldKan
open HomologicalComplex
open SSet.stdSimplex (asOrderHom isTerminalObj₀ objMk)
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a b : U ⟶ V}

/-- Helper for Lemma 14.29.3: the canonical section of the point copower
`U ⟶ (Δ[0] × U)` selecting the unique simplex of `Δ[0]`. -/
private def pointCopowerSectionApp
    (U : SimplicialObject A) (Δ : SimplexCategoryᵒᵖ) :
    U.obj Δ ⟶ ((Δ[0] : SSet.{0}) × U).obj Δ :=
  Sigma.ι (fun _ : (Δ[0] : SSet.{0}).obj Δ ↦ U.obj Δ) (SSet.stdSimplex.const 0 0 Δ)

/-- Helper for Lemma 14.29.3: the point-copower section is natural in the simplicial degree. -/
private theorem pointCopowerSection_naturality
    (U : SimplicialObject A) {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
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

/-- Helper for Lemma 14.29.3: the canonical simplicial section `U ⟶ Δ[0] × U`. -/
private def pointCopowerSection (U : SimplicialObject A) :
    U ⟶ (Δ[0] : SSet.{0}) × U where
  app Δ := pointCopowerSectionApp U Δ
  naturality := fun {_ _} f ↦ pointCopowerSection_naturality U f

/-- Helper for Lemma 14.29.3: the `1`-endpoint inclusion `e₁ : U ⟶ Δ[1] × U`. -/
abbrev e₁ (U : SimplicialObject A) :
    U ⟶ (Δ[1] : SSet.{0}) × U :=
  pointCopowerSection U ≫
    simplicialCopowerIndexHom U (SSet.stdSimplex.δ (0 : Fin 2))

/-- Helper for Lemma 14.29.3: the `0`-endpoint inclusion `e₀ : U ⟶ Δ[1] × U`. -/
abbrev e₀ (U : SimplicialObject A) :
    U ⟶ (Δ[1] : SSet.{0}) × U :=
  pointCopowerSection U ≫
    simplicialCopowerIndexHom U (SSet.stdSimplex.δ (1 : Fin 2))

/-- Helper for Lemma 14.29.3: composing the point-copower section with the projection
`Δ[0] × U ⟶ U` is the identity. -/
private theorem pointCopowerSection_comp_projection
    (U : SimplicialObject A) :
    pointCopowerSection U ≫ simplicialCopowerProjection U (Δ[0] : SSet.{0}) = 𝟙 U := by
  -- Degreewise, the section lands in the unique coproduct summand, and the projection is the
  -- identity on that summand.
  ext Δ
  simpa [pointCopowerSection, pointCopowerSectionApp] using
    (Sigma.ι_desc (fun _ : (Δ[0] : SSet.{0}).obj Δ ↦ 𝟙 (U.obj Δ))
      (SSet.stdSimplex.const 0 0 Δ))

/-- Helper for Lemma 14.29.3: the interval projection composed with the point-copower section is
reindexing along the unique map `Δ[1] ⟶ Δ[0]`. -/
private theorem projection_comp_pointCopowerSection
    (U : SimplicialObject A) :
    simplicialCopowerProjection U (Δ[1] : SSet.{0}) ≫ pointCopowerSection U =
      simplicialCopowerIndexHom U (isTerminalObj₀.from (Δ[1] : SSet.{0})) := by
  -- Compare both sides on each coproduct injection in every simplicial degree.
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

/-- Helper for Lemma 14.29.3: composing an endpoint inclusion with the interval projection
recovers the identity on `U`. -/
private theorem simplicialIntervalProjection_comp_endpoint
    (U : SimplicialObject A) (vertex : (Δ[0] : SSet.{0}) ⟶ (Δ[1] : SSet.{0})) :
    (pointCopowerSection U ≫ simplicialCopowerIndexHom U vertex) ≫
        simplicialCopowerProjection U (Δ[1] : SSet.{0}) =
      𝟙 U := by
  -- Rewrite the projection past the reindexing map and then use the point-copower splitting.
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

/-- Helper for Lemma 14.29.3: the interval projection followed by the `1`-endpoint inclusion is
the identity on `U`. -/
theorem simplicialIntervalProjection_comp_endpointOne (U : SimplicialObject A) :
    e₁ U ≫ simplicialCopowerProjection U (Δ[1] : SSet.{0}) = 𝟙 U := by
  -- This is the general endpoint computation specialized to the terminal vertex.
  simpa [e₁] using
    simplicialIntervalProjection_comp_endpoint U (SSet.stdSimplex.δ (0 : Fin 2))

/-- Helper for Lemma 14.29.3: the interval projection followed by the `0`-endpoint inclusion is
the identity on `U`. -/
theorem simplicialIntervalProjection_comp_endpointZero (U : SimplicialObject A) :
    e₀ U ≫ simplicialCopowerProjection U (Δ[1] : SSet.{0}) = 𝟙 U := by
  -- This is the general endpoint computation specialized to the initial vertex.
  simpa [e₀] using
    simplicialIntervalProjection_comp_endpoint U (SSet.stdSimplex.δ (1 : Fin 2))

/-- Helper for Lemma 14.29.3: the constant `0` map `Δ[0] ⟶ Δ[1]` is the `0`-endpoint inclusion
`δ₁`. -/
private theorem deltaOne_const_zero_eq_endpointZero :
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 0) = SSet.stdSimplex.δ (1 : Fin 2) := by
  -- Both morphisms are maps `Δ[0] ⟶ Δ[1]`, so the finite simplicial-set equality is decidable.
  decide

/-- Helper for Lemma 14.29.3: the constant `1` map `Δ[0] ⟶ Δ[1]` is the `1`-endpoint inclusion
`δ₀`. -/
private theorem deltaOne_const_one_eq_endpointOne :
    SSet.const (SSet.stdSimplex.obj₀Equiv.symm 1) = SSet.stdSimplex.δ (0 : Fin 2) := by
  -- Both morphisms are maps `Δ[0] ⟶ Δ[1]`, so the finite simplicial-set equality is decidable.
  decide

/-- Helper for Lemma 14.29.3: the `0`-endpoint of the interval-coordinate projection
`Δ[0] × Δ[1] ⟶ Δ[1]` is the `0`-vertex inclusion `δ₁`. -/
private theorem deltaOne_vertex_homotopy_zero_endpoint :
    SSet.ι₀ ≫ CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}) =
      SSet.stdSimplex.δ (1 : Fin 2) := by
  -- Rewrite the generic endpoint formula for the tensor projection using the explicit endpoint.
  rw [SSet.ι₀_snd]
  exact deltaOne_const_zero_eq_endpointZero

/-- Helper for Lemma 14.29.3: the `1`-endpoint of the interval-coordinate projection
`Δ[0] × Δ[1] ⟶ Δ[1]` is the `1`-vertex inclusion `δ₀`. -/
private theorem deltaOne_vertex_homotopy_one_endpoint :
    SSet.ι₁ ≫ CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}) =
      SSet.stdSimplex.δ (0 : Fin 2) := by
  -- Rewrite the generic endpoint formula for the tensor projection using the explicit endpoint.
  rw [SSet.ι₁_snd]
  exact deltaOne_const_one_eq_endpointOne

/-- Helper for Lemma 14.29.3: the relative compatibility for the interval-coordinate projection
from `Δ[0] × Δ[1]` is vacuous because the source subcomplex is initial. -/
private theorem deltaOne_vertex_homotopy_rel :
    MonoidalCategoryStruct.whiskerRight (⊥ : (Δ[0] : SSet.{0}).Subcomplex).ι (Δ[1] : SSet.{0}) ≫
        CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0}) =
      SemiCartesianMonoidalCategory.fst
          (((⊥ : (Δ[0] : SSet.{0}).Subcomplex) : SSet.{0})) (Δ[1] : SSet.{0}) ≫
        (SSet.Subcomplex.isInitialBot (X := (Δ[0] : SSet.{0}))).to
            (((⊥ : (Δ[1] : SSet.{0}).Subcomplex) : SSet.{0})) ≫
          (⊥ : (Δ[1] : SSet.{0}).Subcomplex).ι := by
  -- The tensor with the initial subcomplex has no simplices, so every component equality is empty.
  ext Δ x
  exact False.elim x.1.2

/-- Helper for Lemma 14.29.3: the second projection `Δ[0] × Δ[1] ⟶ Δ[1]` is the canonical
directed simplicial-set homotopy from the `0`-endpoint to the `1`-endpoint of the interval. -/
private noncomputable def deltaOne_vertex_homotopy :
    SSet.Homotopy (SSet.stdSimplex.δ (1 : Fin 2)) (SSet.stdSimplex.δ (0 : Fin 2)) :=
  { h := CartesianMonoidalCategory.snd (Δ[0] : SSet.{0}) (Δ[1] : SSet.{0})
    h₀ := deltaOne_vertex_homotopy_zero_endpoint
    h₁ := deltaOne_vertex_homotopy_one_endpoint
    rel := deltaOne_vertex_homotopy_rel }

section CopowerIndexHomotopy

variable {K L : SSet.{0}} (W : SimplicialObject A)
variable
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : K.obj Δ ↦ W.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : L.obj Δ ↦ W.obj Δ)]
variable {f g : K ⟶ L} (H : SSet.Homotopy f g)

/-- Helper for Chap14 Lemma 14 29 3: a simplicial-set homotopy lifts to a simplicial homotopy
between the induced copower reindexing maps. -/
private noncomputable def simplicialCopowerIndexHom_homotopy
    {K L : SSet.{0}} (W : SimplicialObject A)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : K.obj Δ ↦ W.obj Δ)]
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : L.obj Δ ↦ W.obj Δ)]
    {f g : K ⟶ L} (H : SSet.Homotopy f g) :
    Homotopy (simplicialCopowerIndexHom W f) (simplicialCopowerIndexHom W g) where
  -- Reindex each coproduct summand using the simplicial-homotopy component on indices, and use
  -- the same degeneracy operator on the copied simplicial-object factor.
  h {n} i :=
    Sigma.map' ((H.toSimplicialObjectHomotopy).h i) (fun _ ↦ W.σ i)
  h_zero_comp_δ_zero n := by
    apply Sigma.hom_ext
    intro x
    -- Read the face map on the chosen summand and then use the endpoint identity of `H`.
    have hface_base :
        Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            Sigma.map' (L.δ 0)
              (fun _ : L _⦋n + 1⦌ ↦ (W.δ 0 : W _⦋n + 1⦌ ⟶ W _⦋n⦌)) =
          W.δ 0 ≫
            Sigma.ι (fun y ↦ W _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ 0)
          (q := fun _ : L _⦋n + 1⦌ ↦ (W.δ 0 : W _⦋n + 1⦌ ⟶ W _⦋n⦌))
          ((H.toSimplicialObjectHomotopy).h 0 x))
    have hface :
        W.σ 0 ≫ Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            (L × W).δ 0 =
          W.σ 0 ≫ W.δ 0 ≫
            Sigma.ι (fun y ↦ W _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x)) := by
      change W.σ 0 ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            Sigma.map' (L.δ 0)
              (fun _ : L _⦋n + 1⦌ ↦ (W.δ 0 : W _⦋n + 1⦌ ⟶ W _⦋n⦌)) =
        W.σ 0 ≫ W.δ 0 ≫
          Sigma.ι (fun y ↦ W _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ 0 ≫ k) hface_base
    have hindex :
        L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x) = g.app (Opposite.op ⦋n⦌) x :=
      congrFun ((H.toSimplicialObjectHomotopy).h_zero_comp_δ_zero n) x
    simpa [simplicialCopowerIndexHom_app, simplicialCopower_map, Category.assoc] using
      calc
        W.σ 0 ≫ Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h 0 x) ≫
            (L × W).δ 0 =
          W.σ 0 ≫ W.δ 0 ≫
            Sigma.ι (fun y ↦ W _⦋n⦌) (L.δ 0 ((H.toSimplicialObjectHomotopy).h 0 x)) := hface
        _ = W.σ 0 ≫ W.δ 0 ≫ Sigma.ι (fun y ↦ W _⦋n⦌) (g.app (Opposite.op ⦋n⦌) x) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ W _⦋n⦌) (g.app (Opposite.op ⦋n⦌) x) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ Sigma.ι (fun y ↦ W _⦋n⦌) (g.app (Opposite.op ⦋n⦌) x))
                  (W.δ_comp_σ_self (i := (0 : Fin (n + 1))))
  h_last_comp_δ_last n := by
    apply Sigma.hom_ext
    intro x
    -- The last face case is the same component computation, now using the terminal endpoint.
    have hface_base :
        Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            Sigma.map' (L.δ (Fin.last (n + 1)))
              (fun _ : L _⦋n + 1⦌ ↦
                (W.δ (Fin.last (n + 1)) : W _⦋n + 1⦌ ⟶ W _⦋n⦌)) =
          W.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ W _⦋n⦌)
              (L.δ (Fin.last (n + 1))
                ((H.toSimplicialObjectHomotopy).h (Fin.last n) x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ (Fin.last (n + 1)))
          (q := fun _ : L _⦋n + 1⦌ ↦
            (W.δ (Fin.last (n + 1)) : W _⦋n + 1⦌ ⟶ W _⦋n⦌))
          ((H.toSimplicialObjectHomotopy).h (Fin.last n) x))
    have hface :
        W.σ (Fin.last n) ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            (L × W).δ (Fin.last (n + 1)) =
          W.σ (Fin.last n) ≫ W.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ W _⦋n⦌)
              (L.δ (Fin.last (n + 1))
                ((H.toSimplicialObjectHomotopy).h (Fin.last n) x)) := by
      change W.σ (Fin.last n) ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            Sigma.map' (L.δ (Fin.last (n + 1)))
              (fun _ : L _⦋n + 1⦌ ↦
                (W.δ (Fin.last (n + 1)) : W _⦋n + 1⦌ ⟶ W _⦋n⦌)) =
        W.σ (Fin.last n) ≫ W.δ (Fin.last (n + 1)) ≫
          Sigma.ι (fun y ↦ W _⦋n⦌)
            (L.δ (Fin.last (n + 1)) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ (Fin.last n) ≫ k) hface_base
    have hindex :
        L.δ (Fin.last (n + 1)) ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) =
          f.app (Opposite.op ⦋n⦌) x :=
      congrFun ((H.toSimplicialObjectHomotopy).h_last_comp_δ_last n) x
    simpa [simplicialCopowerIndexHom_app, simplicialCopower_map, Category.assoc] using
      calc
        W.σ (Fin.last n) ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h (Fin.last n) x) ≫
            (L × W).δ (Fin.last (n + 1)) =
          W.σ (Fin.last n) ≫ W.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ W _⦋n⦌)
              (L.δ (Fin.last (n + 1))
                ((H.toSimplicialObjectHomotopy).h (Fin.last n) x)) := hface
        _ = W.σ (Fin.last n) ≫ W.δ (Fin.last (n + 1)) ≫
            Sigma.ι (fun y ↦ W _⦋n⦌) (f.app (Opposite.op ⦋n⦌) x) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ W _⦋n⦌) (f.app (Opposite.op ⦋n⦌) x) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫ Sigma.ι (fun y ↦ W _⦋n⦌) (f.app (Opposite.op ⦋n⦌) x))
                  (W.δ_comp_σ_succ (i := Fin.last n))
  h_succ_comp_δ_castSucc_of_lt {n} i j hij := by
    apply Sigma.hom_ext
    intro x
    -- Move the face map across the chosen coproduct summand and rewrite the index via `H`.
    have hface_base :
        Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ i.castSucc)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ i.castSucc : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ i.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ i.castSucc)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (W.δ i.castSucc : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.succ x))
    have hface :
        W.σ j.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × W).δ i.castSucc =
          W.σ j.succ ≫ W.δ i.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      change W.σ j.succ ≫
          Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ i.castSucc)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ i.castSucc : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
        W.σ j.succ ≫ W.δ i.castSucc ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌)
            (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ j.succ ≫ k) hface_base
    have hindex :
        L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x) =
          (H.toSimplicialObjectHomotopy).h j (K.δ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_succ_comp_δ_castSucc_of_lt i j hij) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ i ≫ W.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
      let faceMap : (∐ fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) ⟶ (∐ fun _ : K _⦋n⦌ ↦ W _⦋n⦌) :=
        Sigma.map' (K.δ i) (fun _ : K _⦋n + 1⦌ ↦ (W.δ i : W _⦋n + 1⦌ ⟶ W _⦋n⦌))
      let reindex : (∐ fun _ : K _⦋n⦌ ↦ W _⦋n⦌) ⟶ (∐ fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j)
          (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
      have hδ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i =
            W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ faceMap =
          W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x)
        simpa [faceMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.δ i)
            (q := fun _ : K _⦋n + 1⦌ ↦ (W.δ i : W _⦋n + 1⦌ ⟶ W _⦋n⦌))
            x)
      have hσ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j)
                (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) =
            W.σ j ≫
              Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫ reindex =
          W.σ j ≫ Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j (K.δ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j)
            (q := fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
            (K.δ i x))
      calc
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ faceMap ≫ reindex =
                W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hδ
        _ = W.δ i ≫ W.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ W.δ i ≫ k) hσ
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        W.σ j.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × W).δ i.castSucc =
          W.σ j.succ ≫ W.δ i.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := hface
        _ = W.δ i ≫ W.σ j ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ W _⦋n + 1⦌)
                      (L.δ i.castSucc ((H.toSimplicialObjectHomotopy).h j.succ x)))
                  (W.δ_comp_σ_of_le hij)
        _ = W.δ i ≫ W.σ j ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j) (fun y ↦ W.σ j) := by
              exact htarget.symm
  h_succ_comp_δ_castSucc_succ {n} j := by
    apply Sigma.hom_ext
    intro x
    -- Both sides reduce to the same coproduct summand after the adjacent face identities.
    have hleft_base :
        Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ j.castSucc.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ j.castSucc.succ)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (W.δ j.castSucc.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.succ x))
    have hleft :
        W.σ j.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × W).δ j.castSucc.succ =
          W.σ j.succ ≫ W.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      change W.σ j.succ ≫
          Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ j.castSucc.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
        W.σ j.succ ≫ W.δ j.castSucc.succ ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ j.succ ≫ k) hleft_base
    have hright_base :
        Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ j.castSucc.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ j.castSucc.succ)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (W.δ j.castSucc.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.castSucc x))
    have hright :
        W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × W).δ j.castSucc.succ =
          W.σ j.castSucc ≫ W.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      change W.σ j.castSucc ≫
          Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ j.castSucc.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ j.castSucc.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
        W.σ j.castSucc ≫ W.δ j.castSucc.succ ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ j.castSucc ≫ k) hright_base
    have hright' :
        W.σ j.castSucc ≫ W.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) =
          W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × W).δ j.castSucc.succ := by
      simpa [Category.assoc] using hright.symm
    have htail :
        Sigma.ι (fun y ↦ W _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) =
          W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × W).δ j.castSucc.succ := by
      have hid :
          Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) =
            W.σ j.castSucc ≫ W.δ j.castSucc.succ ≫
              Sigma.ι (fun y ↦ W _⦋n + 1⦌)
                (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫
              Sigma.ι (fun y ↦ W _⦋n + 1⦌)
                (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)))
            (W.δ_comp_σ_succ (i := j.castSucc)).symm
      exact hid.trans hright'
    have hindex :
        L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x) =
          L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_succ_comp_δ_castSucc_succ j) x
    have hleft_to_mid :
        W.σ j.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × W).δ j.castSucc.succ =
          Sigma.ι (fun y ↦ W _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
      calc
        W.σ j.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ x) ≫
            (L × W).δ j.castSucc.succ =
          W.σ j.succ ≫ W.δ j.castSucc.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := hleft
        _ = Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ W _⦋n + 1⦌)
                      (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)))
                  (W.δ_comp_σ_self (i := j.succ))
    have hmid_to_right :
        Sigma.ι (fun y ↦ W _⦋n + 1⦌)
            (L.δ j.castSucc.succ ((H.toSimplicialObjectHomotopy).h j.succ x)) =
          W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × W).δ j.castSucc.succ := by
      simpa [hindex] using htail
    simpa [simplicialCopower_map, Category.assoc] using hleft_to_mid.trans hmid_to_right
  h_castSucc_comp_δ_succ_of_lt {n} i j hji := by
    apply Sigma.hom_ext
    intro x
    -- This is the complementary face case, using `δ_comp_σ_of_gt` on `W`.
    have hface_base :
        Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ i.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ i.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ i.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.δ i.succ)
          (q := fun _ : L _⦋n + 1 + 1⦌ ↦
            (W.δ i.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j.castSucc x))
    have hface :
        W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × W).δ i.succ =
          W.σ j.castSucc ≫ W.δ i.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
      change W.σ j.castSucc ≫
          Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌) ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            Sigma.map' (L.δ i.succ)
              (fun _ : L _⦋n + 1 + 1⦌ ↦
                (W.δ i.succ : W _⦋n + 1 + 1⦌ ⟶ W _⦋n + 1⦌)) =
        W.σ j.castSucc ≫ W.δ i.succ ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌)
            (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ j.castSucc ≫ k) hface_base
    have hindex :
        L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x) =
          (H.toSimplicialObjectHomotopy).h j (K.δ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_castSucc_comp_δ_succ_of_lt i j hji) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ i ≫ W.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
      let faceMap : (∐ fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) ⟶ (∐ fun _ : K _⦋n⦌ ↦ W _⦋n⦌) :=
        Sigma.map' (K.δ i) (fun _ : K _⦋n + 1⦌ ↦ (W.δ i : W _⦋n + 1⦌ ⟶ W _⦋n⦌))
      let reindex : (∐ fun _ : K _⦋n⦌ ↦ W _⦋n⦌) ⟶ (∐ fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j)
          (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
      have hδ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i =
            W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ faceMap =
          W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x)
        simpa [faceMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.δ i)
            (q := fun _ : K _⦋n + 1⦌ ↦ (W.δ i : W _⦋n + 1⦌ ⟶ W _⦋n⦌))
            x)
      have hσ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j)
                (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) =
            W.σ j ≫
              Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫ reindex =
          W.σ j ≫ Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j (K.δ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j)
            (q := fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
            (K.δ i x))
      calc
        Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) =
          W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j)
              (fun _ : K _⦋n⦌ ↦ (W.σ j : W _⦋n⦌ ⟶ W _⦋n + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) x ≫ faceMap ≫ reindex =
                W.δ i ≫ Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) (K.δ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hδ
        _ = W.δ i ≫ W.σ j ≫
            Sigma.ι (fun _ : L _⦋n + 1⦌ ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ W.δ i ≫ k) hσ
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc x) ≫
            (L × W).δ i.succ =
          W.σ j.castSucc ≫ W.δ i.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := hface
        _ = W.δ i ≫ W.σ j ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ W _⦋n + 1⦌)
                      (L.δ i.succ ((H.toSimplicialObjectHomotopy).h j.castSucc x)))
                  (W.δ_comp_σ_of_gt hji)
        _ = W.δ i ≫ W.σ j ≫
            Sigma.ι (fun y ↦ W _⦋n + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j (K.δ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ W _⦋n + 1⦌) x ≫ (K × W).δ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j) (fun y ↦ W.σ j) := by
              exact htarget.symm
  h_comp_σ_castSucc_of_le {n} i j hij := by
    apply Sigma.hom_ext
    intro x
    -- Expand the degeneracy map on the chosen summand and rewrite with the homotopy relation.
    have hdeg_base :
        Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.castSucc)
              (fun _ : L _⦋n + 1⦌ ↦
                (W.σ i.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
          W.σ i.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.σ i.castSucc)
          (q := fun _ : L _⦋n + 1⦌ ↦
            (W.σ i.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j x))
    have hdeg :
        W.σ j ≫ Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × W).σ i.castSucc =
          W.σ j ≫ W.σ i.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := by
      change W.σ j ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.castSucc)
              (fun _ : L _⦋n + 1⦌ ↦
                (W.σ i.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
        W.σ j ≫ W.σ i.castSucc ≫
          Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
            (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ j ≫ k) hdeg_base
    have hindex :
        L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x) =
          (H.toSimplicialObjectHomotopy).h j.succ (K.σ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_comp_σ_castSucc_of_le i j hij) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ (K × W).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
              (fun _ : K _⦋n + 1⦌ ↦ (W.σ j.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
          W.σ i ≫ W.σ j.succ ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
      let degMap : (∐ fun _ : K _⦋n⦌ ↦ W _⦋n⦌) ⟶ (∐ fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) :=
        Sigma.map' (K.σ i) (fun _ : K _⦋n⦌ ↦ (W.σ i : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
      let reindex : (∐ fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) ⟶ (∐ fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
          (fun _ : K _⦋n + 1⦌ ↦ (W.σ j.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌))
      have hσ₁ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ (K × W).σ i =
            W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ degMap =
          W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x)
        simpa [degMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.σ i)
            (q := fun _ : K _⦋n⦌ ↦ (W.σ i : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
            x)
      have hσ₂ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
                (fun _ : K _⦋n + 1⦌ ↦
                  (W.σ j.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
            W.σ j.succ ≫
              Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫ reindex =
          W.σ j.succ ≫ Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j.succ)
            (q := fun _ : K _⦋n + 1⦌ ↦
              (W.σ j.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌))
            (K.σ i x))
      calc
        Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ (K × W).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
              (fun _ : K _⦋n + 1⦌ ↦ (W.σ j.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
          W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ)
              (fun _ : K _⦋n + 1⦌ ↦ (W.σ j.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ degMap ≫ reindex =
                W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hσ₁
        _ = W.σ i ≫ W.σ j.succ ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ W.σ i ≫ k) hσ₂
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        W.σ j ≫ Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × W).σ i.castSucc =
          W.σ j ≫ W.σ i.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := hdeg
        _ = W.σ i ≫ W.σ j.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
                      (L.σ i.castSucc ((H.toSimplicialObjectHomotopy).h j x)))
                  (W.σ_comp_σ hij)
        _ = W.σ i ≫ W.σ j.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.succ (K.σ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ W _⦋n⦌) x ≫ (K × W).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.succ) (fun y ↦ W.σ j.succ) := by
              exact htarget.symm
  h_comp_σ_succ_of_lt {n} i j hji := by
    apply Sigma.hom_ext
    intro x
    -- The complementary degeneracy case uses the symmetric simplicial identity on `W`.
    have hdeg_base :
        Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.succ)
              (fun _ : L _⦋n + 1⦌ ↦
                (W.σ i.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
          W.σ i.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := by
      simpa using
        (Limits.Sigma.ι_comp_map'
          (p := L.σ i.succ)
          (q := fun _ : L _⦋n + 1⦌ ↦
            (W.σ i.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌))
          ((H.toSimplicialObjectHomotopy).h j x))
    have hdeg :
        W.σ j ≫ Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × W).σ i.succ =
          W.σ j ≫ W.σ i.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := by
      change W.σ j ≫
          Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            Sigma.map' (L.σ i.succ)
              (fun _ : L _⦋n + 1⦌ ↦
                (W.σ i.succ : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
        W.σ j ≫ W.σ i.succ ≫
          Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
            (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x))
      simpa [Category.assoc] using congrArg (fun k ↦ W.σ j ≫ k) hdeg_base
    have hindex :
        L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x) =
          (H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x) :=
      congrFun ((H.toSimplicialObjectHomotopy).h_comp_σ_succ_of_lt i j hji) x
    have htarget :
        Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ (K × W).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun _ : K _⦋n + 1⦌ ↦
                (W.σ j.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
          W.σ i ≫ W.σ j.castSucc ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
      let degMap : (∐ fun _ : K _⦋n⦌ ↦ W _⦋n⦌) ⟶ (∐ fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) :=
        Sigma.map' (K.σ i) (fun _ : K _⦋n⦌ ↦ (W.σ i : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
      let reindex :
          (∐ fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) ⟶
            (∐ fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌) :=
        Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
          (fun _ : K _⦋n + 1⦌ ↦ (W.σ j.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌))
      have hσ₁ :
          Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ (K × W).σ i =
            W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) := by
        change Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ degMap =
          W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x)
        simpa [degMap] using
          (Limits.Sigma.ι_comp_map'
            (p := K.σ i)
            (q := fun _ : K _⦋n⦌ ↦ (W.σ i : W _⦋n⦌ ⟶ W _⦋n + 1⦌))
            x)
      have hσ₂ :
          Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫
              Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
                (fun _ : K _⦋n + 1⦌ ↦
                  (W.σ j.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
            W.σ j.castSucc ≫
              Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
                ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
        change Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫ reindex =
          W.σ j.castSucc ≫ Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
            ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x))
        simpa [reindex] using
          (Limits.Sigma.ι_comp_map'
            (p := H.toSimplicialObjectHomotopy.h j.castSucc)
            (q := fun _ : K _⦋n + 1⦌ ↦
              (W.σ j.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌))
            (K.σ i x))
      calc
        Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ (K × W).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun _ : K _⦋n + 1⦌ ↦
                (W.σ j.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) =
          W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun _ : K _⦋n + 1⦌ ↦
                (W.σ j.castSucc : W _⦋n + 1⦌ ⟶ W _⦋n + 1 + 1⦌)) := by
              change Sigma.ι (fun _ : K _⦋n⦌ ↦ W _⦋n⦌) x ≫ degMap ≫ reindex =
                W.σ i ≫ Sigma.ι (fun _ : K _⦋n + 1⦌ ↦ W _⦋n + 1⦌) (K.σ i x) ≫ reindex
              simpa [Category.assoc] using
                congrArg (fun k ↦ k ≫ reindex) hσ₁
        _ = W.σ i ≫ W.σ j.castSucc ≫
            Sigma.ι (fun _ : L _⦋n + 1 + 1⦌ ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
              simpa [Category.assoc] using congrArg (fun k ↦ W.σ i ≫ k) hσ₂
    simpa [simplicialCopower_map, Category.assoc] using
      calc
        W.σ j ≫ Sigma.ι (fun y ↦ W _⦋n + 1⦌) ((H.toSimplicialObjectHomotopy).h j x) ≫
            (L × W).σ i.succ =
          W.σ j ≫ W.σ i.succ ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := hdeg
        _ = W.σ i ≫ W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦ k ≫
                    Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
                      (L.σ i.succ ((H.toSimplicialObjectHomotopy).h j x)))
                  (W.σ_comp_σ hji).symm
        _ = W.σ i ≫ W.σ j.castSucc ≫
            Sigma.ι (fun y ↦ W _⦋n + 1 + 1⦌)
              ((H.toSimplicialObjectHomotopy).h j.castSucc (K.σ i x)) := by
              rw [hindex]
        _ = Sigma.ι (fun y ↦ W _⦋n⦌) x ≫ (K × W).σ i ≫
            Sigma.map' (H.toSimplicialObjectHomotopy.h j.castSucc)
              (fun y ↦ W.σ j.castSucc) := by
              exact htarget.symm

end CopowerIndexHomotopy

/-- Helper for Chap14 Lemma 14 29 3: the standard interval homotopy on `Δ[1]` induces the
directed simplicial homotopy from `e₀` to `e₁`. -/
private noncomputable def endpointIndexHomotopy
    (U : SimplicialObject A) :
    Homotopy (e₀ U) (e₁ U) :=
  (simplicialCopowerIndexHom_homotopy (W := U) deltaOne_vertex_homotopy).precomp
    (pointCopowerSection U)

/-
Domain-style sampling:
- primary domain: simplicial homotopies and their image on normalized Moore complexes under the
  Dold-Kan comparison;
- sampled owner declarations:
  `CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy`,
  `CategoryTheory.SimplicialObject.Homotopy.toNormalizedMooreComplexHomotopy`,
  `inclusionOfMooreComplexMap`,
  `PInftyToNormalizedMooreComplex`;
- best owner abstraction: the canonical owner abstraction for the derived normalized-Moore chain
  homotopy is `Homotopy.toNormalizedMooreComplexHomotopy`, built from the core owner
  `Homotopy.toChainHomotopy` and the Dold-Kan comparison maps;
- primitive data: a simplicial homotopy `H : Homotopy a b`;
- derived API: the induced normalized-Moore chain homotopy
  `H.toNormalizedMooreComplexHomotopy`, with its degreewise comparison formula.

Source/core/bridge triage:
- `source-facing`: existence of a simplicial homotopy lifting a prescribed normalized-Moore chain
  homotopy;
- `core/canonical`: `Homotopy.toChainHomotopy`;
- `bridge/view`: `Homotopy.toNormalizedMooreComplexHomotopy`.
-/

-- Proof sketch: form the Stacks cylinder object for `N(U)` as in Lemma 14.29.1 and use the
-- factorization result of Lemma 14.29.2 to lift the given chain homotopy to a simplicial homotopy
-- `H : Homotopy a b`. The lifted homotopy is then identified with the prescribed normalized-Moore
-- chain homotopy through the canonical bridge owner
-- `Homotopy.toNormalizedMooreComplexHomotopy`.
/-- Helper for Lemma 14.29.3: package a normalized-Moore chain homotopy as the corresponding
chain-cylinder map `◇N(U) ⟶ N(V)`. -/
private noncomputable def cylinderMapOfNormalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    HomologicalComplex.cylinder ((normalizedMooreComplex A).obj U) ⟶
      (normalizedMooreComplex A).obj V :=
  HomologicalComplex.cylinder.desc
    ((normalizedMooreComplex A).map a)
    ((normalizedMooreComplex A).map b)
    N

/-- Helper for Lemma 14.29.3: the cylinder map attached to `N` restricts to `N(a)` on the
left endpoint of the chain cylinder. -/
private theorem cylinderMapOfNormalizedMooreComplexHomotopy_comp_ι₀
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U) ≫
        cylinderMapOfNormalizedMooreComplexHomotopy N =
      (normalizedMooreComplex A).map a := by
  -- Unfold the corepresenting inverse map and read off the left endpoint of `cylinder.desc`.
  simp [cylinderMapOfNormalizedMooreComplexHomotopy]

/-- Helper for Lemma 14.29.3: the cylinder map attached to `N` restricts to `N(b)` on the
right endpoint of the chain cylinder. -/
private theorem cylinderMapOfNormalizedMooreComplexHomotopy_comp_ι₁
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) ≫
        cylinderMapOfNormalizedMooreComplexHomotopy N =
      (normalizedMooreComplex A).map b := by
  -- Unfold the corepresenting inverse map and read off the right endpoint of `cylinder.desc`.
  simp [cylinderMapOfNormalizedMooreComplexHomotopy]

/-- Helper for Lemma 14.29.3: the Dold-Kan inverse sends a chain map `N(X) ⟶ N(V)` to the
corresponding simplicial map `X ⟶ V`. -/
private noncomputable def simplicialMapOfNormalizedMooreComplexMap
    {X : SimplicialObject A}
    (l :
      (normalizedMooreComplex A).obj X ⟶
        (normalizedMooreComplex A).obj V) :
    X ⟶ V :=
  (Abelian.DoldKan.equivalence.unit.app X) ≫
    (Abelian.DoldKan.equivalence.inverse.map l) ≫
    (Abelian.DoldKan.equivalence.unitInv.app V)

/-- Helper for Lemma 14.29.3: the simplicial map obtained from Dold-Kan maps back to the
original normalized-Moore chain map. -/
private theorem normalizedMooreComplex_map_simplicialMapOfNormalizedMooreComplexMap
    {X : SimplicialObject A}
    (l :
      (normalizedMooreComplex A).obj X ⟶
        (normalizedMooreComplex A).obj V) :
    (normalizedMooreComplex A).map
        (simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V) l) =
      l := by
  -- Route correction: isolate the Dold-Kan inverse triangle identity once, so the main proof can
  -- stay focused on the source-faithful interval-to-cylinder comparison.
  let E : SimplicialObject A ≌ ChainComplex A ℕ := Abelian.DoldKan.equivalence
  change
    E.functor.map (E.unit.app X ≫ E.inverse.map l ≫ E.unitInv.app V) = l
  rw [Functor.map_comp, Functor.map_comp]
  have hfun :=
      congrArg
        (fun m ↦ E.functor.map (E.unit.app X) ≫ m ≫ E.functor.map (E.unitInv.app V))
        (E.fun_inv_map (X := E.functor.obj X) (Y := E.functor.obj V) l)
  have hleft :
      E.functor.map (E.unit.app X) ≫ E.counit.app (E.functor.obj X) = 𝟙 _ := by
    simpa using E.functor_unitIso_comp X
  have hright_transport :
      E.functor.map (E.unitInv.app V) = E.counit.app (E.functor.obj V) := by
    simpa using (E.counit_app_functor V).symm
  have hright :
      E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V) = 𝟙 _ := by
    simpa [hright_transport] using E.counitIso.inv_hom_id_app (E.functor.obj V)
  have hstep1 :
      E.functor.map (E.unit.app X) ≫ E.functor.map (E.inverse.map l) ≫
          E.functor.map (E.unitInv.app V) =
        l ≫ E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V) := by
    have hleft' :
        (E.functor.map (E.unit.app X) ≫ E.counit.app (E.functor.obj X)) ≫ l ≫
            E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V) =
          𝟙 _ ≫ l ≫ E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V) := by
      exact
        congrArg
          (fun m ↦ m ≫ l ≫ E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V))
          hleft
    calc
      E.functor.map (E.unit.app X) ≫ E.functor.map (E.inverse.map l) ≫
          E.functor.map (E.unitInv.app V) =
        E.functor.map (E.unit.app X) ≫
          (E.counit.app (E.functor.obj X) ≫ l ≫ E.counitInv.app (E.functor.obj V)) ≫
            E.functor.map (E.unitInv.app V) := by
          exact hfun
      _ = l ≫ E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V) := by
          simpa [Category.assoc] using hleft'
  have hstep2 :
      l ≫ E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V) = l := by
    have hright' :
        l ≫ (E.counitInv.app (E.functor.obj V) ≫ E.functor.map (E.unitInv.app V)) = l ≫ 𝟙 _ := by
      exact congrArg (fun m ↦ l ≫ m) hright
    simpa [Category.assoc] using hright'
  exact hstep1.trans hstep2

/-- Helper for Lemma 14.29.3: any chain-level endpoint formula for a map `N(X) ⟶ N(V)` can be
reflected back to the corresponding simplicial endpoint formula after taking the Dold-Kan lift. -/
private theorem comp_simplicialMapOfNormalizedMooreComplexMap_eq
    {X Y : SimplicialObject A}
    (l :
      (normalizedMooreComplex A).obj Y ⟶
        (normalizedMooreComplex A).obj V)
    {f : X ⟶ Y} {g : X ⟶ V}
    (hfg :
      (normalizedMooreComplex A).map f ≫ l =
        (normalizedMooreComplex A).map g) :
    f ≫ simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V) l = g := by
  -- Faithfulness of `N` reflects the chain-level endpoint equality back to simplicial maps.
  let _ : (normalizedMooreComplex A).Faithful := by
    simpa using
      (inferInstance :
        ((Abelian.DoldKan.equivalence : SimplicialObject A ≌ ChainComplex A ℕ).functor).Faithful)
  apply (normalizedMooreComplex A).map_injective
  rw [Functor.map_comp,
    normalizedMooreComplex_map_simplicialMapOfNormalizedMooreComplexMap, hfg]

/-- Helper for Lemma 14.29.3: lifting the normalized-Moore image of a simplicial map recovers the
original simplicial map. -/
private theorem simplicialMapOfNormalizedMooreComplexMap_map
    {X : SimplicialObject A}
    (f : X ⟶ V) :
    simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V)
        ((normalizedMooreComplex A).map f) =
      f := by
  -- Apply the endpoint-reflection lemma to the identity of `X`; the chain-level identity is
  -- exactly functoriality of `normalizedMooreComplex`.
  simpa using
    (comp_simplicialMapOfNormalizedMooreComplexMap_eq
      (A := A) (V := V)
      (l := (normalizedMooreComplex A).map f)
      (f := 𝟙 X) (g := f) (by
        rw [Functor.map_id]
        simp))

/-- Helper for Lemma 14.29.3: the Dold-Kan lift of a composite `N(f) ≫ l` is `f` followed by the
lift of `l`. -/
private theorem simplicialMapOfNormalizedMooreComplexMap_comp
    {X Y : SimplicialObject A}
    (f : X ⟶ Y)
    (l :
      (normalizedMooreComplex A).obj Y ⟶
        (normalizedMooreComplex A).obj V) :
    simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V)
        ((normalizedMooreComplex A).map f ≫ l) =
      f ≫ simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V) l := by
  -- Compare the two simplicial maps by reflecting the obvious chain-level equality along the
  -- faithful normalized-Moore functor.
  -- Reflect the chain-level identity for `N(f) ≫ l` and then remove the trivial `𝟙 ≫`.
  simpa using
    (comp_simplicialMapOfNormalizedMooreComplexMap_eq
      (A := A) (V := V)
      (l := (normalizedMooreComplex A).map f ≫ l)
      (f := 𝟙 X)
      (g := f ≫ simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V) l)
      (by
        calc
          (normalizedMooreComplex A).map (𝟙 X) ≫ (normalizedMooreComplex A).map f ≫ l =
              (normalizedMooreComplex A).map f ≫ l := by
                rw [Functor.map_id]
                simp
          _ = (normalizedMooreComplex A).map
                (f ≫ simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V) l) := by
                rw [Functor.map_comp,
                  normalizedMooreComplex_map_simplicialMapOfNormalizedMooreComplexMap]))

/-- Helper for Lemma 14.29.3: a normalized-Moore chain homotopy induces an alternating-face-map
chain homotopy after transporting across the `PInfty` retract. -/
private theorem alternatingFaceMapComplex_map_homotopic_ofNormalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    Nonempty
      (_root_.Homotopy ((alternatingFaceMapComplex A).map a) ((alternatingFaceMapComplex A).map b)) := by
  -- Route correction: before constructing the interval comparison, first move the prescribed
  -- homotopy from `N` back to `s` through the canonical `PInfty` retract.
  let hP₀ :
      _root_.Homotopy
        ((alternatingFaceMapComplex A).map a)
        (PInfty ≫ (alternatingFaceMapComplex A).map a) :=
    (_root_.Homotopy.ofEq (by simp)).trans
      ((homotopyPInftyToId U).symm.compRight ((alternatingFaceMapComplex A).map a))
  have ha :
      PInfty ≫ (alternatingFaceMapComplex A).map a =
        PInftyToNormalizedMooreComplex U ≫
          ((normalizedMooreComplex A).map a ≫ inclusionOfMooreComplexMap V) := by
    -- Rewrite the left endpoint through `PInfty = P∞→N ≫ incl` and the naturality of the
    -- inclusion of the normalized Moore complex.
    have hSplitA :
        PInfty ≫ (alternatingFaceMapComplex A).map a =
          PInftyToNormalizedMooreComplex U ≫
            inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map a := by
      calc
        PInfty ≫ (alternatingFaceMapComplex A).map a =
            (PInftyToNormalizedMooreComplex U ≫ inclusionOfMooreComplexMap U) ≫
              (alternatingFaceMapComplex A).map a := by
                rw [← PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap U]
                rfl
        _ =
            PInftyToNormalizedMooreComplex U ≫
              inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map a := by
                simpa using
                  (Category.assoc
                    (PInftyToNormalizedMooreComplex U)
                    (inclusionOfMooreComplexMap U)
                    ((alternatingFaceMapComplex A).map a))
    have hNatA :
        PInftyToNormalizedMooreComplex U ≫
            inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map a =
          PInftyToNormalizedMooreComplex U ≫
            (normalizedMooreComplex A).map a ≫ inclusionOfMooreComplexMap V := by
      simpa [Category.assoc] using
        congrArg (fun k => PInftyToNormalizedMooreComplex U ≫ k)
          ((inclusionOfMooreComplex A).naturality a).symm
    exact hSplitA.trans hNatA
  have hb :
      PInftyToNormalizedMooreComplex U ≫
          (normalizedMooreComplex A).map b ≫ inclusionOfMooreComplexMap V =
        PInfty ≫ (alternatingFaceMapComplex A).map b := by
    -- The right endpoint is the same transport calculation for `b`.
    have hNatB :
        PInftyToNormalizedMooreComplex U ≫
            (normalizedMooreComplex A).map b ≫ inclusionOfMooreComplexMap V =
          PInftyToNormalizedMooreComplex U ≫
            inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map b := by
      simpa [Category.assoc] using
        congrArg (fun k => PInftyToNormalizedMooreComplex U ≫ k)
          ((inclusionOfMooreComplex A).naturality b)
    have hSplitB :
        PInftyToNormalizedMooreComplex U ≫
            inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map b =
          PInfty ≫ (alternatingFaceMapComplex A).map b := by
      calc
        PInftyToNormalizedMooreComplex U ≫
            inclusionOfMooreComplexMap U ≫ (alternatingFaceMapComplex A).map b =
          (PInftyToNormalizedMooreComplex U ≫ inclusionOfMooreComplexMap U) ≫
            (alternatingFaceMapComplex A).map b := by
              simpa using
                (Category.assoc
                  (PInftyToNormalizedMooreComplex U)
                  (inclusionOfMooreComplexMap U)
                  ((alternatingFaceMapComplex A).map b)).symm
        _ = PInfty ≫ (alternatingFaceMapComplex A).map b := by
              rw [PInftyToNormalizedMooreComplex_comp_inclusionOfMooreComplexMap U]
              rfl
    exact hNatB.trans hSplitB
  let hMid :
      _root_.Homotopy
        (PInfty ≫ (alternatingFaceMapComplex A).map a)
        (PInfty ≫ (alternatingFaceMapComplex A).map b) :=
    (_root_.Homotopy.ofEq ha).trans
      (((N.compRight (inclusionOfMooreComplexMap V)).compLeft
          (PInftyToNormalizedMooreComplex U)).trans
        (_root_.Homotopy.ofEq hb))
  let hP₁ :
      _root_.Homotopy
        (PInfty ≫ (alternatingFaceMapComplex A).map b)
        ((alternatingFaceMapComplex A).map b) :=
    ((homotopyPInftyToId U).compRight ((alternatingFaceMapComplex A).map b)).trans
      (_root_.Homotopy.ofEq (by simp))
  -- Concatenate the two `PInfty ~ 𝟙` corrections with the transported normalized-Moore
  -- homotopy.
  exact ⟨hP₀.trans (hMid.trans hP₁)⟩

/-- Helper for Lemma 14.29.3: the successor relation in `ComplexShape.down ℕ`. -/
private abbrev downRelNat (n : ℕ) : (ComplexShape.down ℕ).Rel (n + 1) n :=
  rfl

/-- Helper for Lemma 14.29.3: the normalized-Moore interval object admits a comparison map to the
Stacks chain cylinder with the expected two endpoint formulas and canonical interval-homotopy
comparison. -/
private theorem exists_normalizedMooreComplex_interval_to_diamond
    (U : SimplicialObject A) :
    ∃ l : (normalizedMooreComplex A).obj ((Δ[1] : SSet.{0}) × U) ⟶
        HomologicalComplex.cylinder ((normalizedMooreComplex A).obj U),
      (normalizedMooreComplex A).map (e₀ U) ≫ l =
          HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U) ∧
        (normalizedMooreComplex A).map (e₁ U) ≫ l =
          HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) ∧
        ∀ n : ℕ,
          ((endpointIndexHomotopy (A := A) U).toNormalizedMooreComplexHomotopy.compRight l).hom
              n (n + 1) =
            (HomologicalComplex.cylinder.homotopy₀₁
              ((normalizedMooreComplex A).obj U)
              (fun m ↦ ⟨m + 1, downRelNat m⟩)).hom n (n + 1) := by
  -- Route correction: the only remaining structural gap is now concentrated in the normalized
  -- owner itself. The missing ingredient is an explicit direct map
  -- `N((Δ[1]) × U) ⟶ ◇N(U)` whose endpoints are `ι₀`, `ι₁`, and whose canonical interval
  -- homotopy becomes `cylinder.homotopy₀₁`.
  -- TODO: construct the direct normalized interval-to-cylinder map and verify the two endpoint
  -- formulas together with the chain-homotopy comparison.
  sorry

/-- Helper for Lemma 14.29.3: the normalized-Moore interval object maps to the Stacks chain
cylinder on `N(U)`. -/
private noncomputable def normalizedMooreComplex_interval_to_diamond
    (U : SimplicialObject A) :
    (normalizedMooreComplex A).obj ((Δ[1] : SSet.{0}) × U) ⟶
      HomologicalComplex.cylinder ((normalizedMooreComplex A).obj U) :=
  -- Use the packaged existence statement so the remaining proof frontier stays concentrated in a
  -- single structural comparison theorem.
  Classical.choose (exists_normalizedMooreComplex_interval_to_diamond (A := A) U)

/-- Helper for Lemma 14.29.3: the interval-to-diamond comparison restricts to the left endpoint
of the chain cylinder. -/
private theorem normalizedMooreComplex_interval_to_diamond_comp_e₀
    (U : SimplicialObject A) :
    (normalizedMooreComplex A).map (e₀ U) ≫
        normalizedMooreComplex_interval_to_diamond (A := A) U =
      HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U) := by
  -- Read off the left endpoint identity from the packaged comparison data.
  exact
    (Classical.choose_spec (exists_normalizedMooreComplex_interval_to_diamond (A := A) U)).1

/-- Helper for Lemma 14.29.3: the interval-to-diamond comparison restricts to the right endpoint
of the chain cylinder. -/
private theorem normalizedMooreComplex_interval_to_diamond_comp_e₁
    (U : SimplicialObject A) :
    (normalizedMooreComplex A).map (e₁ U) ≫
        normalizedMooreComplex_interval_to_diamond (A := A) U =
      HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) := by
  -- Read off the right endpoint identity from the packaged comparison data.
  exact
    (Classical.choose_spec (exists_normalizedMooreComplex_interval_to_diamond (A := A) U)).2.1

/-- Helper for Lemma 14.29.3: the packaged normalized interval-to-cylinder comparison sends the
canonical interval homotopy to the canonical cylinder homotopy. -/
private theorem endpointIndexHomotopy_toNormalizedMooreComplex_comp_intervalDiamondMap
    (U : SimplicialObject A) (n : ℕ) :
    ((endpointIndexHomotopy (A := A) U).toNormalizedMooreComplexHomotopy.compRight
        (normalizedMooreComplex_interval_to_diamond (A := A) U)).hom n (n + 1) =
      (HomologicalComplex.cylinder.homotopy₀₁
        ((normalizedMooreComplex A).obj U)
        (fun m ↦ ⟨m + 1, downRelNat m⟩)).hom n (n + 1) := by
  -- Read off the diagonal canonical homotopy comparison from the packaged normalized interval
  -- data.
  exact
    (Classical.choose_spec (exists_normalizedMooreComplex_interval_to_diamond (A := A) U)).2.2 n

/-- Helper for Lemma 14.29.3: compose the interval-to-diamond comparison with the chain-cylinder
map `φN` and lift the result back to a simplicial map `(Δ[1] × U) ⟶ V`. -/
private noncomputable def intervalLiftOfNormalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ((Δ[1] : SSet.{0}) × U) ⟶ V :=
  simplicialMapOfNormalizedMooreComplexMap (A := A) (V := V)
    (normalizedMooreComplex_interval_to_diamond (A := A) U ≫
      cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N)

/-- Helper for Lemma 14.29.3: the normalized-Moore image of the interval lift is exactly the
chosen composite `N((Δ[1]) × U) ⟶ ◇N(U) ⟶ N(V)`. -/
private theorem normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    (normalizedMooreComplex A).map
        (intervalLiftOfNormalizedMooreComplexHomotopy (A := A) (V := V) (a := a) (b := b) N) =
      normalizedMooreComplex_interval_to_diamond (A := A) U ≫
        cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N := by
  -- Read off the normalized-Moore image of the Dold-Kan lift.
  rw [intervalLiftOfNormalizedMooreComplexHomotopy]
  exact
    normalizedMooreComplex_map_simplicialMapOfNormalizedMooreComplexMap
      (A := A) (V := V)
      (normalizedMooreComplex_interval_to_diamond (A := A) U ≫
        cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N)

/-- Helper for Lemma 14.29.3: the interval lift induced by `N` restricts to `a` at the `0`
endpoint. -/
private theorem intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    e₀ U ≫ intervalLiftOfNormalizedMooreComplexHomotopy (A := A) (V := V) (a := a) (b := b) N = a := by
  -- The chain-level `e₀`-endpoint identity factors through `ι₀`, then reflects back to simplicial
  -- maps via faithfulness of `normalizedMooreComplex`.
  refine comp_simplicialMapOfNormalizedMooreComplexMap_eq (A := A) (V := V)
    (l := normalizedMooreComplex_interval_to_diamond (A := A) U ≫
      cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N)
    (f := e₀ U) (g := a) ?_
  calc
    (normalizedMooreComplex A).map (e₀ U) ≫
        (normalizedMooreComplex_interval_to_diamond (A := A) U ≫
          cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N) =
      ((normalizedMooreComplex A).map (e₀ U) ≫
          normalizedMooreComplex_interval_to_diamond (A := A) U) ≫
        cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N := by
          simp [Category.assoc]
    _ = HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U) ≫
          cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N := by
          rw [normalizedMooreComplex_interval_to_diamond_comp_e₀]
    _ = (normalizedMooreComplex A).map a := by
          simpa using
            cylinderMapOfNormalizedMooreComplexHomotopy_comp_ι₀
              (A := A) (a := a) (b := b) N

/-- Helper for Lemma 14.29.3: the interval lift induced by `N` restricts to `b` at the `1`
endpoint. -/
private theorem intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    e₁ U ≫ intervalLiftOfNormalizedMooreComplexHomotopy (A := A) (V := V) (a := a) (b := b) N = b := by
  -- The chain-level `e₁`-endpoint identity factors through `ι₁`, then reflects back to simplicial
  -- maps via faithfulness of `normalizedMooreComplex`.
  refine comp_simplicialMapOfNormalizedMooreComplexMap_eq (A := A) (V := V)
    (l := normalizedMooreComplex_interval_to_diamond (A := A) U ≫
      cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N)
    (f := e₁ U) (g := b) ?_
  calc
    (normalizedMooreComplex A).map (e₁ U) ≫
        (normalizedMooreComplex_interval_to_diamond (A := A) U ≫
          cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N) =
      ((normalizedMooreComplex A).map (e₁ U) ≫
          normalizedMooreComplex_interval_to_diamond (A := A) U) ≫
        cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N := by
          simp [Category.assoc]
    _ = HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) ≫
          cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N := by
          rw [normalizedMooreComplex_interval_to_diamond_comp_e₁]
    _ = (normalizedMooreComplex A).map b := by
          simpa using
            cylinderMapOfNormalizedMooreComplexHomotopy_comp_ι₁
              (A := A) (a := a) (b := b) N

/-- Helper for Lemma 14.29.3: the interval lift determined by `N` already satisfies the two
endpoint formulas and the expected normalized-Moore image formula. -/
private theorem intervalLiftOfNormalizedMooreComplexHomotopy_data
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    e₀ U ≫ intervalLiftOfNormalizedMooreComplexHomotopy (A := A) (V := V) (a := a) (b := b) N = a ∧
      e₁ U ≫ intervalLiftOfNormalizedMooreComplexHomotopy
          (A := A) (V := V) (a := a) (b := b) N = b ∧
        (normalizedMooreComplex A).map
            (intervalLiftOfNormalizedMooreComplexHomotopy
              (A := A) (V := V) (a := a) (b := b) N) =
          normalizedMooreComplex_interval_to_diamond (A := A) U ≫
            cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N := by
  -- Collect the verified interval-lift formulas into one reusable frontier statement.
  refine ⟨?_, ?_, ?_⟩
  · simpa using
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
        (A := A) (V := V) (a := a) (b := b) N
  · simpa using
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
        (A := A) (V := V) (a := a) (b := b) N
  · simpa using
      normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy
        (A := A) (V := V) (a := a) (b := b) N

/-- Helper for Chap14 Lemma 14 29 3: postcomposing a simplicial homotopy and then passing to the
alternating face map complex is the same as postcomposing the induced chain homotopy. -/
private theorem postcomp_toChainHomotopy
    {W : SimplicialObject A}
    {f g : U ⟶ V}
    (H : Homotopy f g) (p : V ⟶ W) :
    (H.postcomp p).toChainHomotopy =
      H.toChainHomotopy.compRight ((alternatingFaceMapComplex A).map p) := by
  -- Compare the two chain homotopies degreewise; in the only nonzero degree they are the same
  -- alternating sum with the common target map `p`.
  ext i j
  by_cases hij : i + 1 = j
  · subst hij
    simp [CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom_eq,
      _root_.Homotopy.compRight_hom, Preadditive.sum_comp]
  · simp [CategoryTheory.SimplicialObject.Homotopy.toChainHomotopy,
      CategoryTheory.SimplicialObject.Homotopy.ToChainHomotopy.hom,
      _root_.Homotopy.compRight_hom, hij]

/-- Helper for Chap14 Lemma 14 29 3: postcomposing a simplicial homotopy and then passing to the
normalized Moore complex is the same as postcomposing the induced normalized-Moore chain homotopy. -/
private theorem postcomp_toNormalizedMooreComplexHomotopy_hom
    {W : SimplicialObject A}
    {f g : U ⟶ V}
    (H : Homotopy f g) (p : V ⟶ W) (n : ℕ) :
    ((H.postcomp p).toNormalizedMooreComplexHomotopy).hom n (n + 1) =
      (H.toNormalizedMooreComplexHomotopy.compRight ((normalizedMooreComplex A).map p)).hom n
        (n + 1) := by
  -- Compare the two normalized-Moore diagonal components; this is the chain-level postcomposition
  -- formula transported across `inclusionOfMooreComplexMap` and `PInftyToNormalizedMooreComplex`.
  have hNat :
      ((alternatingFaceMapComplex A).map p).f (n + 1) ≫
          (PInftyToNormalizedMooreComplex W).f (n + 1) =
        (PInftyToNormalizedMooreComplex V).f (n + 1) ≫
          ((normalizedMooreComplex A).map p).f (n + 1) := by
    exact
      HomologicalComplex.congr_hom
        (PInftyToNormalizedMooreComplex_naturality (A := A) p)
        (n + 1)
  have hStep :
      (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            ((alternatingFaceMapComplex A).map p).f (n + 1) ≫
              (PInftyToNormalizedMooreComplex W).f (n + 1) =
        (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex V).f (n + 1) ≫
              ((normalizedMooreComplex A).map p).f (n + 1) := by
    calc
      (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            ((alternatingFaceMapComplex A).map p).f (n + 1) ≫
              (PInftyToNormalizedMooreComplex W).f (n + 1) =
        (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            (((alternatingFaceMapComplex A).map p).f (n + 1) ≫
              (PInftyToNormalizedMooreComplex W).f (n + 1)) := by
              simp
      _ =
        (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            ((PInftyToNormalizedMooreComplex V).f (n + 1) ≫
              ((normalizedMooreComplex A).map p).f (n + 1)) := by
              simpa [Category.assoc] using
                congrArg
                  (fun k ↦
                    (inclusionOfMooreComplexMap U).f n ≫ H.toChainHomotopy.hom n (n + 1) ≫ k)
                  hNat
      _ =
        (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex V).f (n + 1) ≫
              ((normalizedMooreComplex A).map p).f (n + 1) := by
              rfl
  have h0 :
      (H.postcomp p).toNormalizedMooreComplexHomotopy.hom n (n + 1) =
        (inclusionOfMooreComplexMap U).f n ≫
          (H.postcomp p).toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex W).f (n + 1) := by
    simpa using (H.postcomp p).toNormalizedMooreComplexHomotopy_hom n
  have h1 :
      (inclusionOfMooreComplexMap U).f n ≫
          (H.postcomp p).toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex W).f (n + 1) =
        (inclusionOfMooreComplexMap U).f n ≫
          (H.toChainHomotopy.compRight ((alternatingFaceMapComplex A).map p)).hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex W).f (n + 1) := by
    rw [postcomp_toChainHomotopy (A := A) (H := H) (p := p)]
  have h2 :
      (inclusionOfMooreComplexMap U).f n ≫
          (H.toChainHomotopy.compRight ((alternatingFaceMapComplex A).map p)).hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex W).f (n + 1) =
        (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            ((alternatingFaceMapComplex A).map p).f (n + 1) ≫
              (PInftyToNormalizedMooreComplex W).f (n + 1) := by
    simp [_root_.Homotopy.compRight_hom, Category.assoc]
  have h3 :
      (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            ((alternatingFaceMapComplex A).map p).f (n + 1) ≫
              (PInftyToNormalizedMooreComplex W).f (n + 1) =
        (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex V).f (n + 1) ≫
              ((normalizedMooreComplex A).map p).f (n + 1) := hStep
  have h4 :
      (inclusionOfMooreComplexMap U).f n ≫
          H.toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex V).f (n + 1) ≫
              ((normalizedMooreComplex A).map p).f (n + 1) =
        H.toNormalizedMooreComplexHomotopy.hom n (n + 1) ≫
              ((normalizedMooreComplex A).map p).f (n + 1) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦ k ≫ ((normalizedMooreComplex A).map p).f (n + 1))
        (H.toNormalizedMooreComplexHomotopy_hom n).symm
  have h5 :
      H.toNormalizedMooreComplexHomotopy.hom n (n + 1) ≫
          ((normalizedMooreComplex A).map p).f (n + 1) =
        (H.toNormalizedMooreComplexHomotopy.compRight
          ((normalizedMooreComplex A).map p)).hom n (n + 1) := by
    simp [_root_.Homotopy.compRight_hom]
  exact h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))

/-- Helper for Lemma 14.29.3: postcomposing the canonical cylinder homotopy with
`cylinderMapOfNormalizedMooreComplexHomotopy N` recovers the prescribed diagonal component `N.hom`.
-/
private theorem cylinderHomotopy₀₁_comp_cylinderMapOfNormalizedMooreComplexHomotopy_hom
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b))
    (n : ℕ) :
    ((HomologicalComplex.cylinder.homotopy₀₁
        ((normalizedMooreComplex A).obj U)
        (fun m ↦ ⟨m + 1, downRelNat m⟩)).compRight
          (cylinderMapOfNormalizedMooreComplexHomotopy
            (A := A) (a := a) (b := b) N)).hom n (n + 1) =
      N.hom n (n + 1) := by
  -- Route correction: stay entirely inside the cylinder owner. After unfolding `cylinder.desc`,
  -- the diagonal component is exactly the owner computation `inrCompHomotopy_hom_desc_hom`,
  -- and `Homotopy.equivSubZero` reduces the resulting null-homotopy component back to `N.hom`.
  simpa [cylinderMapOfNormalizedMooreComplexHomotopy,
    HomologicalComplex.cylinder.homotopy₀₁,
    HomologicalComplex.cylinder.πCompι₀Homotopy,
    HomologicalComplex.cylinder.desc,
    _root_.Homotopy.compRight_hom,
    _root_.Homotopy.compLeft_hom,
    _root_.Homotopy.trans_hom,
    _root_.Homotopy.ofEq_hom,
    Homotopy.equivSubZero] using
    (HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom_desc_hom
      (φ := biprod.lift (𝟙 ((normalizedMooreComplex A).obj U))
        (-𝟙 ((normalizedMooreComplex A).obj U)))
      (α := biprod.desc ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b))
      (hα := _root_.Homotopy.trans
        (_root_.Homotopy.ofEq (by
          simp only [biprod.lift_desc, id_comp, neg_comp, sub_eq_add_neg]))
        (Homotopy.equivSubZero N))
      (hc := fun m ↦ ⟨m + 1, downRelNat m⟩)
      (i := n) (j := n + 1))

/-- Helper for Chap14 Lemma 14 29 3: after applying `normalizedMooreComplex`, the left endpoint
formula for the interval lift becomes the expected source equality for chain-homotopy transport. -/
private theorem normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    (normalizedMooreComplex A).map a =
      (normalizedMooreComplex A).map
        (e₀ U ≫ intervalLiftOfNormalizedMooreComplexHomotopy
          (A := A) (V := V) (a := a) (b := b) N) := by
  -- Rewrite the simplicial endpoint identity through functoriality of `normalizedMooreComplex`.
  simpa using
    congrArg (fun f ↦ (normalizedMooreComplex A).map f)
      (intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
        (A := A) (V := V) (a := a) (b := b) N).symm

/-- Helper for Chap14 Lemma 14 29 3: after applying `normalizedMooreComplex`, the right endpoint
formula for the interval lift becomes the expected target equality for chain-homotopy transport. -/
private theorem normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    (normalizedMooreComplex A).map
        (e₁ U ≫ intervalLiftOfNormalizedMooreComplexHomotopy
          (A := A) (V := V) (a := a) (b := b) N) =
      (normalizedMooreComplex A).map b := by
  -- Rewrite the simplicial endpoint identity through functoriality of `normalizedMooreComplex`.
  simpa using
    congrArg (fun f ↦ (normalizedMooreComplex A).map f)
      (intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
        (A := A) (V := V) (a := a) (b := b) N)

/-- Helper for Chap14 Lemma 14 29 3: rewriting the endpoints of a simplicial homotopy and then
passing to normalized Moore complexes is the same as composing with the induced endpoint
equalities on chain maps. -/
private theorem toNormalizedMooreComplexHomotopy_transport
    {X Y : SimplicialObject A} {f₀ f₁ g₀ g₁ : X ⟶ Y}
    (h₀ : f₀ = g₀) (h₁ : f₁ = g₁) (H : Homotopy f₀ f₁) :
    (h₀ ▸ h₁ ▸ H).toNormalizedMooreComplexHomotopy =
      _root_.Homotopy.trans
        (_root_.Homotopy.ofEq
          (congrArg (fun f ↦ (normalizedMooreComplex A).map f) h₀.symm))
        (_root_.Homotopy.trans H.toNormalizedMooreComplexHomotopy
          (_root_.Homotopy.ofEq
            (congrArg (fun f ↦ (normalizedMooreComplex A).map f) h₁))) := by
  -- After both endpoint equalities are reduced to reflexivity, the statement is the canonical
  -- identity that trivial endpoint transports do not change the induced chain homotopy.
  cases h₀
  cases h₁
  ext i j
  simp [Homotopy.trans_hom]
  abel

/-- Helper for Chap14 Lemma 14 29 3: once the interval lift is known to recover the prescribed
normalized-Moore chain homotopy before rewriting the endpoints, the final transport to a homotopy
`a ∼ b` is immediate. -/
private theorem intervalLiftOfNormalizedMooreComplexHomotopy_recovers_chainHomotopy_of_eq
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b))
    (hrec :
      N =
        _root_.Homotopy.trans
          (_root_.Homotopy.ofEq
            (normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
              (A := A) (U := U) (V := V) (a := a) (b := b) N))
          (_root_.Homotopy.trans
            (((endpointIndexHomotopy (A := A) U).postcomp
              (intervalLiftOfNormalizedMooreComplexHomotopy
                (A := A) (V := V) (a := a) (b := b) N)).toNormalizedMooreComplexHomotopy)
            (_root_.Homotopy.ofEq
              (normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
                (A := A) (U := U) (V := V) (a := a) (b := b) N)))) :
    let h := intervalLiftOfNormalizedMooreComplexHomotopy
      (A := A) (V := V) (a := a) (b := b) N
    let hh₀ : e₀ U ≫ h = a :=
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
        (A := A) (V := V) (a := a) (b := b) N
    let hh₁ : e₁ U ≫ h = b :=
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
        (A := A) (V := V) (a := a) (b := b) N
    let H₀ : Homotopy (e₀ U ≫ h) (e₁ U ≫ h) :=
      (endpointIndexHomotopy (A := A) U).postcomp h
    let H : Homotopy a b :=
      hh₀ ▸ hh₁ ▸
          H₀
    N = H.toNormalizedMooreComplexHomotopy := by
  -- The remaining transport is only the endpoint rewrite already packaged in the definition of
  -- `H`.
  dsimp
  rw [toNormalizedMooreComplexHomotopy_transport
    (A := A)
    (h₀ := intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
      (A := A) (V := V) (a := a) (b := b) N)
    (h₁ := intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
      (A := A) (V := V) (a := a) (b := b) N)
    (H := (endpointIndexHomotopy (A := A) U).postcomp
      (intervalLiftOfNormalizedMooreComplexHomotopy
        (A := A) (V := V) (a := a) (b := b) N))]
  simpa using hrec

/-- Helper for Chap14 Lemma 14 29 3: the only remaining recovery step is the source-level
comparison saying that the chosen interval lift sends the canonical interval homotopy to the
prescribed normalized-Moore chain homotopy before the endpoint rewrites. -/
private theorem intervalLiftOfNormalizedMooreComplexHomotopy_recovery_hom
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b))
    (n : ℕ) :
    N.hom n (n + 1) =
      (((endpointIndexHomotopy (A := A) U).postcomp
        (intervalLiftOfNormalizedMooreComplexHomotopy
          (A := A) (V := V) (a := a) (b := b) N)).toNormalizedMooreComplexHomotopy).hom n (n + 1) := by
  -- Rewrite the recovered homotopy through normalized postcomposition, replace the interval part
  -- by the packaged cylinder comparison, and then read off the diagonal component of `φN`.
  calc
    N.hom n (n + 1) =
        ((HomologicalComplex.cylinder.homotopy₀₁
          ((normalizedMooreComplex A).obj U)
          (fun m ↦ ⟨m + 1, downRelNat m⟩)).compRight
            (cylinderMapOfNormalizedMooreComplexHomotopy
              (A := A) (a := a) (b := b) N)).hom n (n + 1) := by
              symm
              exact
                cylinderHomotopy₀₁_comp_cylinderMapOfNormalizedMooreComplexHomotopy_hom
                  (A := A) (U := U) (a := a) (b := b) N n
    _ =
        (((endpointIndexHomotopy (A := A) U).toNormalizedMooreComplexHomotopy.compRight
          (normalizedMooreComplex_interval_to_diamond (A := A) U)).compRight
            (cylinderMapOfNormalizedMooreComplexHomotopy
              (A := A) (a := a) (b := b) N)).hom n (n + 1) := by
              simpa [_root_.Homotopy.compRight_hom] using
                congrArg
                  (fun k ↦
                    k ≫ (cylinderMapOfNormalizedMooreComplexHomotopy
                      (A := A) (a := a) (b := b) N).f (n + 1))
                  (endpointIndexHomotopy_toNormalizedMooreComplex_comp_intervalDiamondMap
                    (A := A) U n).symm
    _ =
        ((endpointIndexHomotopy (A := A) U).toNormalizedMooreComplexHomotopy.compRight
          (normalizedMooreComplex_interval_to_diamond (A := A) U ≫
            cylinderMapOfNormalizedMooreComplexHomotopy
              (A := A) (a := a) (b := b) N)).hom n (n + 1) := by
              simp [_root_.Homotopy.compRight_hom, Category.assoc]
    _ =
        ((endpointIndexHomotopy (A := A) U).toNormalizedMooreComplexHomotopy.compRight
          ((normalizedMooreComplex A).map
            (intervalLiftOfNormalizedMooreComplexHomotopy
              (A := A) (V := V) (a := a) (b := b) N))).hom n (n + 1) := by
              rw [normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy
                (A := A) (V := V) (a := a) (b := b) N]
    _ =
        (((endpointIndexHomotopy (A := A) U).postcomp
          (intervalLiftOfNormalizedMooreComplexHomotopy
            (A := A) (V := V) (a := a) (b := b) N)).toNormalizedMooreComplexHomotopy).hom n
          (n + 1) := by
            rw [postcomp_toNormalizedMooreComplexHomotopy_hom
              (A := A)
              (H := endpointIndexHomotopy (A := A) U)
              (p := intervalLiftOfNormalizedMooreComplexHomotopy
                (A := A) (V := V) (a := a) (b := b) N)
              (n := n)]

/-- Helper for Chap14 Lemma 14 29 3: the only remaining recovery step is the source-level
comparison saying that the chosen interval lift sends the canonical interval homotopy to the
prescribed normalized-Moore chain homotopy before the endpoint rewrites. -/
private theorem intervalLiftOfNormalizedMooreComplexHomotopy_recovery_core
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    N =
      _root_.Homotopy.trans
        (_root_.Homotopy.ofEq
          (normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
            (A := A) (U := U) (V := V) (a := a) (b := b) N))
        (_root_.Homotopy.trans
          (((endpointIndexHomotopy (A := A) U).postcomp
            (intervalLiftOfNormalizedMooreComplexHomotopy
              (A := A) (V := V) (a := a) (b := b) N)).toNormalizedMooreComplexHomotopy)
          (_root_.Homotopy.ofEq
              (normalizedMooreComplex_map_intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
                (A := A) (U := U) (V := V) (a := a) (b := b) N))) := by
  -- Route correction: the endpoint transport is no longer the blocker. What remains is the single
  -- diagonal comparison on `(n, n + 1)`. All off-diagonal components vanish by definition of a
  -- chain homotopy.
  let Hmid :=
    ((endpointIndexHomotopy (A := A) U).postcomp
      (intervalLiftOfNormalizedMooreComplexHomotopy
        (A := A) (V := V) (a := a) (b := b) N)).toNormalizedMooreComplexHomotopy
  ext i j
  change N.hom i j = 0 + (Hmid.hom i j + 0)
  by_cases hij : i + 1 = j
  · subst hij
    -- In the only nonzero degree, the endpoint rewrites contribute zero and the diagonal
    -- comparison closes the goal.
    calc
      N.hom i (i + 1) = Hmid.hom i (i + 1) :=
        intervalLiftOfNormalizedMooreComplexHomotopy_recovery_hom
          (A := A) (U := U) (V := V) (a := a) (b := b) N i
      _ = 0 + (Hmid.hom i (i + 1) + 0) := by abel
  · -- Away from the diagonal, every component of both chain homotopies is zero.
    calc
      N.hom i j = 0 := N.zero i j hij
      _ = 0 + (Hmid.hom i j + 0) := by
            rw [Hmid.zero i j hij]
            abel

-- Proof sketch: once the interval lift `(Δ[1] × U) ⟶ V` is available with the correct endpoint
-- identities and normalized-Moore image, the remaining source-faithful step is to convert that
-- interval map to a directed simplicial homotopy and identify the induced chain homotopy using the
-- canonical interval homotopy on `Δ[1] × U`.
/-- Helper for Lemma 14.29.3: after transporting the canonical interval homotopy along the chosen
interval lift, one still has to compare the resulting normalized-Moore chain homotopy with the
prescribed `N`. -/
private theorem intervalLiftOfNormalizedMooreComplexHomotopy_recovers_chainHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    let h := intervalLiftOfNormalizedMooreComplexHomotopy
      (A := A) (V := V) (a := a) (b := b) N
    let hh₀ : e₀ U ≫ h = a :=
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
        (A := A) (V := V) (a := a) (b := b) N
    let hh₁ : e₁ U ≫ h = b :=
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
        (A := A) (V := V) (a := a) (b := b) N
    let H₀ : Homotopy (e₀ U ≫ h) (e₁ U ≫ h) :=
      (endpointIndexHomotopy (A := A) U).postcomp h
    let H : Homotopy a b :=
      hh₀ ▸ hh₁ ▸
          H₀
    N = H.toNormalizedMooreComplexHomotopy := by
  -- Route correction: the endpoint rewriting is already isolated. The whole theorem now reduces to
  -- the core source-level recovery identity for the chosen interval lift.
  exact
    intervalLiftOfNormalizedMooreComplexHomotopy_recovers_chainHomotopy_of_eq
      (A := A) (U := U) (V := V) (a := a) (b := b) N
      (intervalLiftOfNormalizedMooreComplexHomotopy_recovery_core
        (A := A) (U := U) (V := V) (a := a) (b := b) N)

/-- Helper for Lemma 14.29.3: an interval lift with the prescribed endpoint formulas and
normalized-Moore image packages into the desired simplicial homotopy. -/
private theorem exists_simplicialHomotopy_of_intervalLiftOfNormalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      N = H.toNormalizedMooreComplexHomotopy := by
  let h :=
    intervalLiftOfNormalizedMooreComplexHomotopy (A := A) (V := V) (a := a) (b := b) N
  have hh₀ : e₀ U ≫ h = a := by
    -- The left endpoint was already verified when the interval lift was constructed.
    simpa [h] using
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₀
        (A := A) (V := V) (a := a) (b := b) N
  have hh₁ : e₁ U ≫ h = b := by
    -- The right endpoint is the companion endpoint formula for the same interval lift.
    simpa [h] using
      intervalLiftOfNormalizedMooreComplexHomotopy_comp_e₁
        (A := A) (V := V) (a := a) (b := b) N
  let H₀ : Homotopy (e₀ U ≫ h) (e₁ U ≫ h) :=
    (endpointIndexHomotopy (A := A) U).postcomp h
  let H : Homotopy a b := hh₀ ▸ hh₁ ▸ H₀
  refine ⟨H, ?_⟩
  -- The remaining comparison has been isolated as the dedicated recovery theorem.
  simpa [h, H₀, H] using
    intervalLiftOfNormalizedMooreComplexHomotopy_recovers_chainHomotopy
      (A := A) (U := U) (V := V) (a := a) (b := b) N

/-- Lemma 14.29.3: every chain homotopy between the normalized Moore maps `N(a)` and `N(b)` comes
from a simplicial homotopy `H : a ⟶ b`, and the given chain homotopy is exactly the canonical
normalized-Moore homotopy induced by `H`. -/
@[stacks 01A4]
theorem exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      N = H.toNormalizedMooreComplexHomotopy := by
  -- Package the prescribed chain homotopy as the corresponding chain-cylinder map `φN`.
  let φN := cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N
  have hφ₀ :
      HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U) ≫ φN =
        (normalizedMooreComplex A).map a := by
    simpa [φN] using
      cylinderMapOfNormalizedMooreComplexHomotopy_comp_ι₀
        (A := A) (a := a) (b := b) N
  have hφ₁ :
      HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) ≫ φN =
        (normalizedMooreComplex A).map b := by
    simpa [φN] using
      cylinderMapOfNormalizedMooreComplexHomotopy_comp_ι₁
        (A := A) (a := a) (b := b) N
  -- Route correction: the Dold-Kan lift step is now isolated in
  -- `intervalLiftOfNormalizedMooreComplexHomotopy`; the remaining source-faithful work is the
  -- interval-to-cylinder comparison `N((Δ[1]) × U) ⟶ ◇N(U)` and its transport of the canonical
  -- interval homotopy to the prescribed chain homotopy `N`.
  let _ := hφ₀
  let _ := hφ₁
  exact
    exists_simplicialHomotopy_of_intervalLiftOfNormalizedMooreComplexHomotopy
      (A := A) (U := U) (V := V) (a := a) (b := b) N

/-- Degreewise reformulation of Lemma 14.29.3 via the canonical owner
`Homotopy.toNormalizedMooreComplexHomotopy`. -/
theorem exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy_hom
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      ∀ n : ℕ,
        N.hom n (n + 1) =
          (inclusionOfMooreComplexMap U).f n ≫ H.toChainHomotopy.hom n (n + 1) ≫
            (PInftyToNormalizedMooreComplex V).f (n + 1) := by
  rcases exists_simplicialHomotopy_of_normalizedMooreComplexHomotopy N with ⟨H, hH⟩
  refine ⟨H, fun n ↦ ?_⟩
  rw [hH]
  simpa using H.toNormalizedMooreComplexHomotopy_hom n

end CategoryTheory.SimplicialObject
