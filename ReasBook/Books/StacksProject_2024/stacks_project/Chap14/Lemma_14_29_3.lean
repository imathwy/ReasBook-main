import Mathlib
import StacksProject_2024.stacks_project.Chap14.Lemma_14_13_3
import StacksProject_2024.stacks_project.Chap14.Lemma_14_27_1

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

-- Proof sketch: this is the source-faithful missing bridge
-- `N((Δ[1]) × U) ⟶ ◇N(U)` from the Stacks interval object to the chain cylinder. The remaining
-- work is the explicit interval-cokernel computation from Lemma 14.29.2.
/-- Helper for Lemma 14.29.3: the normalized-Moore interval object maps to the Stacks chain
cylinder on `N(U)`. -/
private noncomputable def normalizedMooreComplex_interval_to_diamond
    (U : SimplicialObject A) :
    (normalizedMooreComplex A).obj ((Δ[1] : SSet.{0}) × U) ⟶
      HomologicalComplex.cylinder ((normalizedMooreComplex A).obj U) :=
  -- TODO: construct the source-faithful interval-to-diamond comparison by factoring the
  -- interval short exact sequence through Lemma 14.29.2 and retracting from `s(U)` to `N(U)`.
  sorry

/-- Helper for Lemma 14.29.3: the interval-to-diamond comparison restricts to the left endpoint
of the chain cylinder. -/
private theorem normalizedMooreComplex_interval_to_diamond_comp_e₀
    (U : SimplicialObject A) :
    (normalizedMooreComplex A).map (e₀ U) ≫
        normalizedMooreComplex_interval_to_diamond (A := A) U =
      HomologicalComplex.cylinder.ι₀ ((normalizedMooreComplex A).obj U) := by
  -- TODO: this is the first endpoint identity coming from the interval lift of Lemma 14.29.2.
  sorry

/-- Helper for Lemma 14.29.3: the interval-to-diamond comparison restricts to the right endpoint
of the chain cylinder. -/
private theorem normalizedMooreComplex_interval_to_diamond_comp_e₁
    (U : SimplicialObject A) :
    (normalizedMooreComplex A).map (e₁ U) ≫
        normalizedMooreComplex_interval_to_diamond (A := A) U =
      HomologicalComplex.cylinder.ι₁ ((normalizedMooreComplex A).obj U) := by
  -- TODO: this is the second endpoint identity coming from the interval lift of Lemma 14.29.2.
  sorry

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

-- Proof sketch: once the interval lift `(Δ[1] × U) ⟶ V` is available with the correct endpoint
-- identities and normalized-Moore image, the remaining source-faithful step is to convert that
-- interval map to a directed simplicial homotopy and identify the induced chain homotopy using the
-- canonical interval homotopy on `Δ[1] × U`.
/-- Helper for Lemma 14.29.3: an interval lift with the prescribed endpoint formulas and
normalized-Moore image packages into the desired simplicial homotopy. -/
private theorem exists_simplicialHomotopy_of_intervalLiftOfNormalizedMooreComplexHomotopy
    (N : _root_.Homotopy ((normalizedMooreComplex A).map a) ((normalizedMooreComplex A).map b)) :
    ∃ H : Homotopy a b,
      N = H.toNormalizedMooreComplexHomotopy := by
  let h :=
    intervalLiftOfNormalizedMooreComplexHomotopy (A := A) (V := V) (a := a) (b := b) N
  rcases intervalLiftOfNormalizedMooreComplexHomotopy_data
      (A := A) (U := U) (V := V) (a := a) (b := b) N with
    ⟨hh₀', hh₁', hhN'⟩
  have hh₀ : e₀ U ≫ h = a := by
    simpa [h] using hh₀'
  have hh₁ : e₁ U ≫ h = b := by
    simpa [h] using hh₁'
  have hhN :
      (normalizedMooreComplex A).map h =
        normalizedMooreComplex_interval_to_diamond (A := A) U ≫
          cylinderMapOfNormalizedMooreComplexHomotopy (A := A) (a := a) (b := b) N := by
    simpa [h] using hhN'
  have hEndpoint : Homotopy (e₀ U) (e₁ U) := by
    -- TODO: convert `deltaOne_vertex_homotopy` to the ordinary simplicial homotopy between the
    -- two copower-index maps and then precompose with `pointCopowerSection U`.
    sorry
  let H₀ : Homotopy (e₀ U ≫ h) (e₁ U ≫ h) :=
    hEndpoint.postcomp h
  let H : Homotopy a b := hh₀ ▸ hh₁ ▸ H₀
  refine ⟨H, ?_⟩
  let _ := hhN
  -- TODO: compare the normalized-Moore image of `H` with the prescribed chain homotopy `N` by
  -- proving the missing recovery identity for `normalizedMooreComplex_interval_to_diamond` against
  -- the chain-cylinder map coming from `endpoint_index_homotopy U`.
  sorry

/-- Lemma 14.29.3: every chain homotopy between the normalized Moore maps `N(a)` and `N(b)` comes
from a simplicial homotopy `H : a ⟶ b`, and the given chain homotopy is exactly the canonical
normalized-Moore homotopy induced by `H`. -/
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
