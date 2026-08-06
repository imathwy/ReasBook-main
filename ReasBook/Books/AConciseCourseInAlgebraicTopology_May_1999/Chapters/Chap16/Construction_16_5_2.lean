import Mathlib.RepresentationTheory.Homological.Resolution
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Homotopy.Contractible
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap16.Construction_16_5_1

noncomputable section

open CategoryTheory MonoidalCategory Simplicial

universe u

variable (G : Type u) [Group G]

-- Semantic recall via `lean_leansearch`: mathlib's canonical simplicial `G`-set
-- `classifyingSpaceUniversalCover G` already models `EG_•`, so this file keeps that owner and
-- adds the source-facing simplicial map to the nerve model for `BG`.

/-- The underlying simplicial set of the canonical simplicial universal `G`-bundle `EG_•`. -/
noncomputable abbrev groupUniversalCoverSSet : SSet :=
  classifyingSpaceUniversalCover G ⋙ forget _

/-- The `n`-simplex component of the simplicial map `EG_• ⟶ BG_•`, expressed in the nerve model
for `BG_•`. -/
def groupUniversalCoverToNerveSingleObjApp (n : ℕ) :
    (Fin (n + 1) → G) → (nerve (SingleObj G)) _⦋n⦌ :=
  fun x ↦
    CategoryTheory.SingleObj.differenceFunctor (fun j : Fin (n + 1) ↦ (x j)⁻¹)

/-- The simplicial quotient map `EG_• ⟶ BG_•` records the successive quotient coordinates
`(g_{i+1})⁻¹ * g_i` under `groupBarConstructionNSimplicesEquiv`. -/
@[simp] theorem groupUniversalCoverToNerveSingleObjApp_apply
    (n : ℕ) (x : Fin (n + 1) → G) (i : Fin n) :
    groupBarConstructionNSimplicesEquiv G n
        (groupUniversalCoverToNerveSingleObjApp G n x) i =
      (x i.succ)⁻¹ * x i.castSucc := by
  -- The repaired quotient simplex is the `differenceFunctor` on the inverse tuple.
  rw [groupBarConstructionNSimplicesEquiv_apply]
  have hs : (⟨i.1 + 1, Nat.succ_lt_succ i.2⟩ : Fin (n + 1)) = i.succ := by
    ext
    rfl
  have hc : (⟨i.1, Nat.lt_succ_of_lt i.2⟩ : Fin (n + 1)) = i.castSucc := by
    ext
    rfl
  simp [groupUniversalCoverToNerveSingleObjApp, CategoryTheory.SingleObj.differenceFunctor, hs, hc]

/-- The `n`-simplex quotient map `EG_n → BG_n` is invariant under the diagonal left
`G`-action. -/
theorem groupUniversalCoverToNerveSingleObjApp_smul
    (n : ℕ) (g : G) (x : Fin (n + 1) → G) :
    groupUniversalCoverToNerveSingleObjApp G n (g • x) =
      groupUniversalCoverToNerveSingleObjApp G n x := by
  -- The repaired inverse quotient coordinates cancel the diagonal left translate.
  apply (groupBarConstructionNSimplicesEquiv G n).injective
  ext i
  rw [groupUniversalCoverToNerveSingleObjApp_apply, groupUniversalCoverToNerveSingleObjApp_apply]
  simp [mul_assoc]

/-- The levelwise quotient maps defining `EG_• ⟶ BG_•` commute with simplicial operators. -/
theorem groupUniversalCoverToNerveSingleObj_naturality
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (groupUniversalCoverSSet G).map f ≫
        groupUniversalCoverToNerveSingleObjApp G Δ'.unop.len =
      groupUniversalCoverToNerveSingleObjApp G Δ.unop.len ≫
        (nerve (SingleObj G)).map f := by
  -- Route correction: after packaging the repaired inverse quotient coordinates by
  -- `SingleObj.differenceFunctor`, naturality is just functorial precomposition.
  funext x
  rfl

/-- The canonical simplicial map from `EG_•` to the nerve model of `BG_•`. Under
`groupBarConstructionNSimplicesEquiv`, the component on `n`-simplices sends
`(g₀, ..., gₙ)` to `((g₁)⁻¹ * g₀, ..., (gₙ)⁻¹ * g_{n - 1})`. -/
def groupUniversalCoverToNerveSingleObj :
    groupUniversalCoverSSet G ⟶ nerve (SingleObj G) where
  app Δ := groupUniversalCoverToNerveSingleObjApp G Δ.unop.len
  naturality _ _ f := groupUniversalCoverToNerveSingleObj_naturality G f

/-- The diagonal left `G`-action on each simplex space `Fin (n + 1) → G` of `EG_•` is free. -/
instance groupUniversalCoverLevelIsCancelSMul (n : ℕ) :
    IsCancelSMul G (Fin (n + 1) → G) := by
  refine { right_cancel' := ?_ }
  intro g h x hEq
  -- Equality of diagonal translates is detected on any fixed coordinate.
  have h0 : g * x 0 = h * x 0 := by
    simpa using congrFun hEq (0 : Fin (n + 1))
  calc
    g = (g * x 0) * (x 0)⁻¹ := by simp [mul_assoc]
    _ = (h * x 0) * (x 0)⁻¹ := by rw [h0]
    _ = h := by simp [mul_assoc]

/-- The geometric realization of the underlying simplicial set of `EG_•`. -/
noncomputable abbrev groupUniversalCoverSpace : TopCat :=
  SSet.toTop.obj (groupUniversalCoverSSet G)

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Regard a nerve simplex as a constant singular simplex in the `n`-simplex space of
`groupBarConstruction G`. -/
noncomputable def groupBarConstructionNerveToDiagonalApp (Δ : SimplexCategoryᵒᵖ) :
    (nerve (SingleObj G)).obj Δ →
      (groupBarConstructionDiagonalSSet G).obj Δ :=
  fun x ↦
    (TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ.unop.len) Δ).symm
      (ContinuousMap.const _ (groupBarConstructionNSimplicesEquiv G Δ.unop.len x))

/-- Helper for Construction 16.5.2: the singular-set map of a continuous map sends a constant
simplex to the constant simplex at the image point. -/
private theorem toSSetObjEquiv_map_const
    {X Y : TopCat.{u}} (h : X ⟶ Y) (Δ : SimplexCategoryᵒᵖ) (x : X) :
    TopCat.toSSetObjEquiv Y Δ
        (((TopCat.toSSet.map h).app Δ)
          ((TopCat.toSSetObjEquiv X Δ).symm (ContinuousMap.const _ x))) =
      ContinuousMap.const _ (h x) := by
  -- Under `TopCat.toSSetObjEquiv`, singular functoriality is just postcomposition by `h`.
  rfl

/-- Helper for Construction 16.5.2: simplicial operators on a singular simplicial set preserve
constant simplices. -/
private theorem toSSetObjEquiv_objMap_const
    (X : TopCat.{u}) {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (x : X) :
    TopCat.toSSetObjEquiv X Δ'
        (((TopCat.toSSet.obj X).map f)
          ((TopCat.toSSetObjEquiv X Δ).symm (ContinuousMap.const _ x))) =
      ContinuousMap.const _ x := by
  -- Precomposing a constant singular simplex with a simplex operator leaves it unchanged.
  rfl

/-- Helper for Construction 16.5.2: the tuple model of `groupBarConstruction G` was defined by
transporting the nerve map through `groupBarConstructionNSimplicesEquiv`. -/
private theorem groupBarConstruction_map_tuple
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (x : (nerve (SingleObj G)).obj Δ) :
    groupBarConstructionNSimplicesEquiv G Δ'.unop.len ((nerve (SingleObj G)).map f x) =
      ((groupBarConstruction G).map f)
        (groupBarConstructionNSimplicesEquiv G Δ.unop.len x) := by
  -- This is exactly how the simplicial bar-construction transport was packaged.
  change groupBarConstructionNSimplicesEquiv G Δ'.unop.len ((nerve (SingleObj G)).map f x) =
    groupBarConstructionNSimplicesEquiv G Δ'.unop.len
      ((nerve (SingleObj G)).map f
        ((groupBarConstructionNSimplicesEquiv G Δ.unop.len).symm
          (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)))
  simpa using
    congrArg
      (fun y ↦ groupBarConstructionNSimplicesEquiv G Δ'.unop.len ((nerve (SingleObj G)).map f y))
      ((groupBarConstructionNSimplicesEquiv G Δ.unop.len).symm_apply_apply x).symm

/-- The constant-singular-simplex bridge from the nerve model of `BG_•` to the chapter's
diagonal singular model `groupBarConstructionDiagonalSSet G`. -/
theorem groupBarConstructionNerveToDiagonal_naturality
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    (nerve (SingleObj G)).map f ≫
        groupBarConstructionNerveToDiagonalApp G Δ' =
      groupBarConstructionNerveToDiagonalApp G Δ ≫
        (groupBarConstructionDiagonalSSet G).map f := by
  -- Compare the two singular simplices after unpacking them as continuous maps out of `Δ`.
  funext x
  apply (TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ'.unop.len) Δ').injective
  -- The diagonal map preserves constant simplices, so it remains to identify the transported
  -- tuple point with the tuple description of the mapped nerve simplex.
  dsimp [groupBarConstructionDiagonalSSet, CategoryTheory.SimplicialObject.diagonalSingularSet,
    CategoryTheory.SimplicialObject.singularBisimplicialSet, groupBarConstructionNerveToDiagonalApp]
  have hconst :
      ((TopCat.toSSet.map ((groupBarConstruction G).map f)).app Δ)
          (((TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ.unop.len) Δ).symm
            (ContinuousMap.const _ (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)))) =
        ((TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ'.unop.len) Δ).symm
          (ContinuousMap.const _ (((groupBarConstruction G).map f)
            (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)))) := by
    -- First move the constant simplex across the outer simplicial-space map.
    apply (TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ'.unop.len) Δ).injective
    simpa using
      toSSetObjEquiv_map_const
        (((groupBarConstruction G).map f)) Δ
        (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)
  have hinner :
      ((TopCat.toSSet.obj ((groupBarConstruction G).obj Δ')).map f)
          (((TopCat.toSSet.map ((groupBarConstruction G).map f)).app Δ)
            (((TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ.unop.len) Δ).symm
              (ContinuousMap.const _ (groupBarConstructionNSimplicesEquiv G Δ.unop.len x))))) =
        ((TopCat.toSSet.obj ((groupBarConstruction G).obj Δ')).map f)
          (((TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ'.unop.len) Δ).symm
            (ContinuousMap.const _ (((groupBarConstruction G).map f)
              (groupBarConstructionNSimplicesEquiv G Δ.unop.len x))))) := by
    -- Now move the rewritten constant simplex through the inner simplicial operator.
    exact congrArg ((TopCat.toSSet.obj ((groupBarConstruction G).obj Δ')).map f) hconst
  rw [Equiv.apply_symm_apply]
  have hpoint :
      (ContinuousMap.const (stdSimplex ℝ (Fin (Δ'.unop.len + 1)))
          (groupBarConstructionNSimplicesEquiv G Δ'.unop.len
            ((nerve (SingleObj G)).map f x)) :
            C(stdSimplex ℝ (Fin (Δ'.unop.len + 1)), groupBarConstructionObj G Δ'.unop.len)) =
        ContinuousMap.const (stdSimplex ℝ (Fin (Δ'.unop.len + 1)))
          (((groupBarConstruction G).map f)
            (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)) := by
    -- The tuple-space owner was defined so that its transport matches the nerve transport.
    rw [groupBarConstruction_map_tuple]
    rfl
  have hdiag :
      TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ'.unop.len) Δ'
          ((TopCat.toSSet.obj ((groupBarConstruction G).obj Δ')).map f
            ((TopCat.toSSet.map ((groupBarConstruction G).map f)).app Δ
              (((TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ.unop.len) Δ).symm
                (ContinuousMap.const _ (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)))))) =
        (ContinuousMap.const (stdSimplex ℝ (Fin (Δ'.unop.len + 1)))
          (((groupBarConstruction G).map f)
            (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)) :
            C(stdSimplex ℝ (Fin (Δ'.unop.len + 1)), groupBarConstructionObj G Δ'.unop.len)) := by
    -- After the outer transport rewrite, the inner simplicial operator still fixes constants.
    exact (congrArg
      (TopCat.toSSetObjEquiv (groupBarConstructionObj G Δ'.unop.len) Δ') hinner).trans
      (toSSetObjEquiv_objMap_const
        (groupBarConstructionObj G Δ'.unop.len) f
        (((groupBarConstruction G).map f)
          (groupBarConstructionNSimplicesEquiv G Δ.unop.len x)))
  exact hpoint.trans hdiag.symm

/-- The simplicial bridge from the canonical `EG_•` owner to the chapter's `BG_•` model. -/
noncomputable def groupUniversalCoverToClassifyingSpaceSSet :
    groupUniversalCoverSSet G ⟶ groupBarConstructionDiagonalSSet G :=
  groupUniversalCoverToNerveSingleObj G ≫
    { app := groupBarConstructionNerveToDiagonalApp G
      naturality _ _ f := groupBarConstructionNerveToDiagonal_naturality G f }

/-- Construction 16.5.2 (1): the projection map `EG ⟶ BG` of the universal principal
`G`-bundle, with `EG` formalized by the canonical simplicial `G`-set
`classifyingSpaceUniversalCover G` and `BG` formalized by the chapter's classifying-space owner
`groupClassifyingSpace G`. On simplices this map is induced by
`(g₀, ..., gₙ) ↦ ((g₁)⁻¹ * g₀, ..., (gₙ)⁻¹ * g_{n - 1})`. -/
noncomputable abbrev groupUniversalCoverProjection :
    groupUniversalCoverSpace G ⟶ groupClassifyingSpace G :=
  SSet.toTop.map (groupUniversalCoverToClassifyingSpaceSSet G)

/-- `groupUniversalCoverProjection G` is the realization of the simplicial map
`groupUniversalCoverToClassifyingSpaceSSet G`. -/
theorem groupUniversalCoverProjection_def :
    groupUniversalCoverProjection G =
      SSet.toTop.map (groupUniversalCoverToClassifyingSpaceSSet G) := rfl

end Topological

/-- The simplicial left action of `g : G` on the underlying simplicial set of `EG_•`. -/
def groupUniversalCoverSSetSmul (g : G) :
    groupUniversalCoverSSet G ⟶ groupUniversalCoverSSet G where
  app Δ := fun x : Fin (Δ.unop.len + 1) → G ↦ g • x
  naturality _ _ _ := rfl

/-- Helper for Construction 16.5.2: smul by `1` acts trivially on the simplicial universal cover
`EG_•`. -/
private theorem groupUniversalCoverSSetSmul_one :
    groupUniversalCoverSSetSmul G 1 = 𝟙 (groupUniversalCoverSSet G) := by
  -- Compare the simplicial self-maps componentwise on every simplex set.
  ext Δ x
  simp [groupUniversalCoverSSetSmul]

/-- Helper for Construction 16.5.2: simplicial smul by `g * h` is the composite of smul by `h`
then smul by `g`. -/
private theorem groupUniversalCoverSSetSmul_mul (g h : G) :
    groupUniversalCoverSSetSmul G (g * h) =
      groupUniversalCoverSSetSmul G h ≫ groupUniversalCoverSSetSmul G g := by
  -- Compare the simplicial self-maps componentwise on every simplex set.
  ext Δ x
  simp [groupUniversalCoverSSetSmul, mul_smul]

/-- Smul by `1` on `EG_•` induces the identity on the realization `EG`. -/
theorem groupUniversalCoverSpace_one_smul
    (x : groupUniversalCoverSpace G) :
    (SSet.toTop.map (groupUniversalCoverSSetSmul G 1)) x = x := by
  -- Realization preserves the identity simplicial self-map.
  have hmap :=
    congrArg SSet.toTop.map (@groupUniversalCoverSSetSmul_one G _)
  simpa using congrArg (fun f ↦ f x) hmap

/-- Simplicial smul on `EG_•` realizes to a multiplicative left action on `EG`. -/
theorem groupUniversalCoverSpace_mul_smul
    (g h : G) (x : groupUniversalCoverSpace G) :
    (SSet.toTop.map (groupUniversalCoverSSetSmul G (g * h))) x =
      (SSet.toTop.map (groupUniversalCoverSSetSmul G g))
        ((SSet.toTop.map (groupUniversalCoverSSetSmul G h)) x) := by
  -- Realization sends the simplicial composition law to the corresponding topological action law.
  have hmap :=
    congrArg SSet.toTop.map (@groupUniversalCoverSSetSmul_mul G _ g h)
  simpa [Functor.map_comp] using congrArg (fun f ↦ f x) hmap

/-- The realized total space `EG` inherits the diagonal left `G`-action from
`classifyingSpaceUniversalCover G`. -/
noncomputable instance groupUniversalCoverSpaceMulAction :
    MulAction G (groupUniversalCoverSpace G) where
  smul g x := (SSet.toTop.map (groupUniversalCoverSSetSmul G g)) x
  one_smul := groupUniversalCoverSpace_one_smul G
  mul_smul := groupUniversalCoverSpace_mul_smul G

/-- Helper for Construction 16.5.2: if a diagonal translate fixes a simplex of `EG_•`, then the
translating element is trivial. -/
theorem groupUniversalCoverLevel_eq_one_of_smul_eq
    {n : ℕ} {g : G} {x : Fin (n + 1) → G} (h : g • x = x) :
    g = 1 := by
  -- The levelwise diagonal action is already free, so a fixed simplex forces `g = 1`.
  exact
    isCancelSMul_iff_eq_one_of_smul_eq.mp
      (groupUniversalCoverLevelIsCancelSMul (G := G) n) g x h

/-- Helper for Construction 16.5.2: simplicial smul by `g` is an automorphism of `EG_•`. -/
noncomputable def groupUniversalCoverSSetSmulIso (g : G) :
    groupUniversalCoverSSet G ≅ groupUniversalCoverSSet G where
  hom := groupUniversalCoverSSetSmul G g
  inv := groupUniversalCoverSSetSmul G g⁻¹
  hom_inv_id := by
    -- Compose the action with its inverse and collapse back to the identity self-map.
    rw [← groupUniversalCoverSSetSmul_mul]
    simpa using groupUniversalCoverSSetSmul_one (G := G)
  inv_hom_id := by
    -- The inverse composite is handled by the same multiplicative cancellation.
    rw [← groupUniversalCoverSSetSmul_mul]
    simpa using groupUniversalCoverSSetSmul_one (G := G)

/-- Helper for Construction 16.5.2: the simplicial `G`-action preserves nondegenerate simplices
of `EG_•`. -/
theorem groupUniversalCoverSSetSmul_mem_nonDegenerate_iff
    {n : ℕ} (g : G) (x : (groupUniversalCoverSSet G) _⦋n⦌) :
    (groupUniversalCoverSSetSmul G g).app _ x ∈ (groupUniversalCoverSSet G).nonDegenerate n ↔
      x ∈ (groupUniversalCoverSSet G).nonDegenerate n := by
  -- Nondegeneracy is invariant under simplicial isomorphisms, so apply the action iso.
  simpa using
    (SSet.nonDegenerate_iff_of_isIso (groupUniversalCoverSSetSmulIso G g).hom x)

/-- Helper for Construction 16.5.2: a fixed nondegenerate simplex of `EG_•` already forces the
acting element of `G` to be trivial. -/
theorem groupUniversalCoverNondegenerate_eq_one_of_smul_eq
    {n : ℕ} {g : G} {x : (groupUniversalCoverSSet G).nonDegenerate n}
    (h : (groupUniversalCoverSSetSmul G g).app _ x.1 = x.1) :
    g = 1 := by
  -- Forgetting nondegeneracy reduces the claim to the levelwise free action already proved.
  exact groupUniversalCoverLevel_eq_one_of_smul_eq (G := G) h

/-- Helper for Construction 16.5.2: the extra degeneracy on the augmented simplicial universal
cover picks a canonical `0`-simplex of `EG_•`. -/
noncomputable def groupUniversalCoverChosenZeroSimplex :
    (groupUniversalCoverSSet G).obj (Opposite.op ⦋0⦌) :=
  (classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented G).s'
    ((CategoryTheory.Limits.terminal.from (C := Type u) PUnit.{u + 1}) PUnit.unit)

/-- Helper for Construction 16.5.2: the canonical `0`-simplex of `EG_•` defines the constant
simplicial self-map used in the contraction route. -/
noncomputable def groupUniversalCoverSSetConst :
    groupUniversalCoverSSet G ⟶ groupUniversalCoverSSet G :=
  SSet.const (groupUniversalCoverChosenZeroSimplex G)

/-- Helper for Construction 16.5.2: the constant simplicial self-map on `EG_•` is the
augmentation followed by the section coming from the extra degeneracy. -/
theorem groupUniversalCoverSSetConst_eq_hom_section :
    groupUniversalCoverSSetConst G =
      (classifyingSpaceUniversalCover.compForgetAugmented G).hom ≫
        (classifyingSpaceUniversalCover.extraDegeneracyCompForgetAugmented G).section_ := by
  -- Both sides are the same constant endomorphism, so it suffices to compare simplexwise.
  ext Δ x
  rfl

/-- Helper for Construction 16.5.2: on each simplex set, the contracting endomorphism of `EG_•`
is obtained by pulling the chosen `0`-simplex back along the unique map to `[0]`. -/
theorem groupUniversalCoverSSetConst_app_apply
    (Δ : SimplexCategoryᵒᵖ) (x : (groupUniversalCoverSSet G).obj Δ) :
    (groupUniversalCoverSSetConst G).app Δ x =
      ((groupUniversalCoverSSet G).map (SimplexCategory.isTerminalZero.from Δ.unop).op)
        (groupUniversalCoverChosenZeroSimplex G) := by
  -- Unfold the simplicial constant map so the endpoint is expressed on the owner `EG_•`.
  rfl

/-- Helper for Construction 16.5.2: simplexwise, the contracting endomorphism of `EG_•`
forgets the input simplex. -/
theorem groupUniversalCoverSSetConst_app_eq
    (Δ : SimplexCategoryᵒᵖ)
    (x y : (groupUniversalCoverSSet G).obj Δ) :
    (groupUniversalCoverSSetConst G).app Δ x =
      (groupUniversalCoverSSetConst G).app Δ y := by
  -- Rewrite both values using the same pullback of the chosen `0`-simplex.
  rw [groupUniversalCoverSSetConst_app_apply, groupUniversalCoverSSetConst_app_apply]

/-- Helper for Construction 16.5.2: each coordinate of the constant simplicial contraction on
`EG_•` is the unique coordinate of `groupUniversalCoverChosenZeroSimplex G`. -/
private theorem groupUniversalCoverSSetConst_app_apply_base
    (Δ : SimplexCategoryᵒᵖ)
    (x : (groupUniversalCoverSSet G).obj Δ)
    (i : Fin (Δ.unop.len + 1)) :
    (groupUniversalCoverSSetConst G).app Δ x i =
      groupUniversalCoverChosenZeroSimplex G 0 := by
  -- The constant simplicial endomorphism is obtained by precomposing the chosen `0`-simplex
  -- along the unique map to `Δ[0]`, so every output coordinate reads its unique entry.
  rw [groupUniversalCoverSSetConst_app_apply]
  rfl

/-- Helper for Construction 16.5.2: the explicit simplexwise contraction of `EG_•` keeps the
original simplex on the `1`-part of `Δ[1]` and replaces the `0`-part by the chosen base
coordinate. -/
private def groupUniversalCoverSSetHomotopyApp
    (Δ : SimplexCategoryᵒᵖ) :
    ((groupUniversalCoverSSet G ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1)).obj Δ) →
      (groupUniversalCoverSSet G).obj Δ :=
  fun z i ↦
    if SSet.stdSimplex.asOrderHom z.2 i = 0 then
      groupUniversalCoverChosenZeroSimplex G 0
    else
      z.1 i

/-- Helper for Construction 16.5.2: the explicit contraction formula is compatible with every
simplicial operator because both coordinates are transported by precomposition. -/
private theorem groupUniversalCoverSSetHomotopyApp_naturality
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    ((groupUniversalCoverSSet G ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1)).map f) ≫
        groupUniversalCoverSSetHomotopyApp G Δ' =
      groupUniversalCoverSSetHomotopyApp G Δ ≫
        (groupUniversalCoverSSet G).map f := by
  -- Compare the transported contraction formula coordinatewise; both sides are definitionally
  -- the same precomposition by `f`.
  funext z
  funext i
  rfl

/-- Helper for Construction 16.5.2: the explicit contraction formula packages into a simplicial
self-map `EG_• ⊗ Δ[1] ⟶ EG_•`. -/
private def groupUniversalCoverSSetHomotopyMap :
    groupUniversalCoverSSet G ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 1) ⟶
      groupUniversalCoverSSet G where
  app Δ := groupUniversalCoverSSetHomotopyApp G Δ
  naturality _ _ f := groupUniversalCoverSSetHomotopyApp_naturality (G := G) f

/-- Helper for Construction 16.5.2: restricting the explicit contraction to the `0`-endpoint of
`Δ[1]` recovers the constant simplicial endomorphism of `EG_•`. -/
private theorem groupUniversalCoverSSetHomotopyMap_h₀ :
    SSet.ι₀ ≫ groupUniversalCoverSSetHomotopyMap G = groupUniversalCoverSSetConst G := by
  -- At the `0`-endpoint every coordinate is forced to the chosen base coordinate.
  ext Δ x
  funext i
  have hzero :
      SimplexCategory.Hom.toOrderHom (SSet.ι₀.app Δ x).2.down i = 0 := by
    rfl
  rw [groupUniversalCoverSSetConst_app_apply_base]
  change groupUniversalCoverSSetHomotopyApp G Δ (SSet.ι₀.app Δ x) i =
    groupUniversalCoverChosenZeroSimplex G 0
  dsimp [groupUniversalCoverSSetHomotopyApp, SSet.stdSimplex.asOrderHom]
  split_ifs with hcond
  · rfl
  · exact (hcond hzero).elim

/-- Helper for Construction 16.5.2: restricting the explicit contraction to the `1`-endpoint of
`Δ[1]` recovers the identity simplicial endomorphism of `EG_•`. -/
private theorem groupUniversalCoverSSetHomotopyMap_h₁ :
    SSet.ι₁ ≫ groupUniversalCoverSSetHomotopyMap G = 𝟙 (groupUniversalCoverSSet G) := by
  -- At the `1`-endpoint the formula leaves every coordinate unchanged.
  ext Δ x
  funext i
  have hone :
      SimplexCategory.Hom.toOrderHom (SSet.ι₁.app Δ x).2.down i = 1 := by
    rfl
  have hne :
      SimplexCategory.Hom.toOrderHom (SSet.ι₁.app Δ x).2.down i ≠ 0 := by
    rw [hone]
    decide
  change groupUniversalCoverSSetHomotopyApp G Δ (SSet.ι₁.app Δ x) i = x i
  dsimp [groupUniversalCoverSSetHomotopyApp, SSet.stdSimplex.asOrderHom]
  split_ifs with hcond
  · exact (hne hcond).elim
  · rfl

/-- Helper for Construction 16.5.2: the relative condition for the bottom subcomplex is vacuous,
since there are no simplices to check. -/
private theorem groupUniversalCoverSSetHomotopyMap_rel :
    ((⊥ : (groupUniversalCoverSSet G).Subcomplex).ι ▷
        SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        groupUniversalCoverSSetHomotopyMap G =
      CartesianMonoidalCategory.fst _ _ ≫
        (SSet.Subcomplex.isInitialBot (X := groupUniversalCoverSSet G)).to _ ≫
          (⊥ : (groupUniversalCoverSSet G).Subcomplex).ι := by
  -- Any simplex of the bottom subcomplex carries an impossible membership proof.
  ext Δ x
  exact x.1.2.elim

/-- Helper for Construction 16.5.2: the chosen simplicial contraction of `EG_•` gives an explicit
homotopy from the constant endomorphism to the identity. -/
private noncomputable def groupUniversalCoverSSetHomotopyToConst :
    SSet.Homotopy (groupUniversalCoverSSetConst G) (𝟙 (groupUniversalCoverSSet G)) :=
  { h := groupUniversalCoverSSetHomotopyMap G
    h₀ := groupUniversalCoverSSetHomotopyMap_h₀ (G := G)
    h₁ := groupUniversalCoverSSetHomotopyMap_h₁ (G := G)
    rel := groupUniversalCoverSSetHomotopyMap_rel (G := G) }

/-- Helper for Construction 16.5.2: precomposing the simplicial contraction with any simplex of
`EG_•` yields the same constant simplex. -/
private theorem groupUniversalCoverSSetConst_comp_eq
    {n : SimplexCategory} (σ τ : SSet.stdSimplex.obj n ⟶ groupUniversalCoverSSet G) :
    σ ≫ groupUniversalCoverSSetConst G = τ ≫ groupUniversalCoverSSetConst G := by
  -- Compare the two simplex maps by the image of the identity `n`-simplex under Yoneda.
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  exact
    groupUniversalCoverSSetConst_app_eq (G := G) (Opposite.op n)
      (SSet.yonedaEquiv σ) (SSet.yonedaEquiv τ)

/-- Helper for Construction 16.5.2: after geometric realization, the simplicial contraction is
constant on each realized simplex. -/
private theorem groupUniversalCoverSpace_const_simplex_apply_eq
    {n : SimplexCategory} (σ τ : SSet.stdSimplex.obj n ⟶ groupUniversalCoverSSet G)
    (x : SSet.toTop.obj (SSet.stdSimplex.obj n)) :
    (SSet.toTop.map (groupUniversalCoverSSetConst G)) ((SSet.toTop.map σ) x) =
      (SSet.toTop.map (groupUniversalCoverSSetConst G)) ((SSet.toTop.map τ) x) := by
  -- Realization preserves the simplicial equality above, so evaluate the resulting map equality.
  have h :
      SSet.toTop.map σ ≫ SSet.toTop.map (groupUniversalCoverSSetConst G) =
        SSet.toTop.map τ ≫ SSet.toTop.map (groupUniversalCoverSSetConst G) := by
    have hmap :=
      congrArg SSet.toTop.map (groupUniversalCoverSSetConst_comp_eq (G := G) σ τ)
    simpa [Functor.map_comp] using hmap
  exact congrArg (fun f ↦ f x) h

/-- Helper for Construction 16.5.2: every point of `|EG_•|` is represented by a simplex leg in the
left-Kan-extension colimit presentation of geometric realization. -/
private theorem groupUniversalCoverSpacePointRepresentative
    (x : groupUniversalCoverSpace G) :
    ∃ (n : SimplexCategory) (σ : SSet.stdSimplex.obj n ⟶ groupUniversalCoverSSet G)
      (u : SSet.toTop.obj (SSet.stdSimplex.obj n)),
        ((SSet.toTop.map σ).hom) u = x := by
  let diag :
      CategoryTheory.CostructuredArrow SSet.stdSimplex (groupUniversalCoverSSet G) ⥤ TopCat :=
    CategoryTheory.CostructuredArrow.proj SSet.stdSimplex (groupUniversalCoverSSet G) ⋙
      SimplexCategory.toTop
  let e :
      groupUniversalCoverSpace G ≅ CategoryTheory.Limits.colimit diag :=
    SSet.stdSimplex.leftKanExtensionObjIsoColimit
      (F := SimplexCategory.toTop) (X := groupUniversalCoverSSet G)
  let hcolim :
      CategoryTheory.Limits.IsColimit ((forget TopCat).mapCocone
        (CategoryTheory.Limits.colimit.cocone diag)) :=
    CategoryTheory.Limits.isColimitOfPreserves (forget TopCat)
      (CategoryTheory.Limits.colimit.isColimit diag)
  obtain ⟨p, y, hy⟩ := CategoryTheory.Limits.Types.jointly_surjective_of_isColimit
    (F := diag ⋙ forget TopCat)
    (t := (forget TopCat).mapCocone (CategoryTheory.Limits.colimit.cocone diag))
    hcolim (e.hom x)
  let u : SSet.toTop.obj (SSet.stdSimplex.obj p.left) :=
    (SSet.toTopSimplex.app p.left).inv y
  have hColimitLeg :
      (SSet.toTopSimplex.inv.app p.left) ≫ SSet.toTop.map p.hom ≫ e.hom =
        CategoryTheory.Limits.colimit.ι diag p := by
    -- Rewrite the generic colimit leg into the concrete realization-of-a-simplex form.
    simpa [diag, e, SSet.toTop, SSet.toTopSimplex] using
      (CategoryTheory.Functor.ι_leftKanExtensionObjIsoColimit_hom
        (L := SSet.stdSimplex) (F := SimplexCategory.toTop) (X := groupUniversalCoverSSet G) p)
  have hx :
      ((SSet.toTop.map p.hom).hom) u = x := by
    -- Evaluate the colimit leg at the chosen simplex point and cancel the realization isomorphism.
    have heInj : Function.Injective e.hom := (TopCat.homeoOfIso e).injective
    apply heInj
    have hEval :
        (((SSet.toTopSimplex.inv.app p.left) ≫ SSet.toTop.map p.hom ≫ e.hom).hom) y =
          (CategoryTheory.Limits.colimit.ι diag p) y := by
      exact congrArg
        (fun f : SimplexCategory.toTop.obj p.left ⟶ CategoryTheory.Limits.colimit diag ↦ f y)
        hColimitLeg
    have hy' : (CategoryTheory.Limits.colimit.ι diag p) y = e.hom x := by
      simpa [diag] using hy
    exact (by simpa [u] using hEval.trans hy')
  exact ⟨p.left, p.hom, u, hx⟩

/-- The distinguished realized point of `|EG_•|` determined by the chosen `0`-simplex coming from
the extra degeneracy. -/
noncomputable def groupUniversalCoverBasePoint : groupUniversalCoverSpace G :=
  SSet.toTop.map
      (SSet.const (X := SSet.stdSimplex.obj ⦋0⦌) (groupUniversalCoverChosenZeroSimplex G))
      ((SSet.toTopSimplex.app ⦋0⦌).inv (default : SimplexCategory.toTop.obj ⦋0⦌))

/-- Helper for Construction 16.5.2: the realization of a constant simplex map lands at the chosen
basepoint of `|EG_•|`, independent of the simplex dimension and source point. -/
private theorem groupUniversalCoverConstSimplex_apply_eq_basePoint
    {n : SimplexCategory} (u : SSet.toTop.obj (SSet.stdSimplex.obj n)) :
    (SSet.toTop.map
        (SSet.const (X := SSet.stdSimplex.obj n) (groupUniversalCoverChosenZeroSimplex G))) u =
      groupUniversalCoverBasePoint G := by
  let f : SSet.stdSimplex.obj n ⟶ SSet.stdSimplex.obj ⦋0⦌ :=
    SSet.stdSimplex.map (SimplexCategory.isTerminalZero.from n)
  have hconst :
      SSet.const (X := SSet.stdSimplex.obj n) (groupUniversalCoverChosenZeroSimplex G) =
        f ≫ SSet.const (X := SSet.stdSimplex.obj ⦋0⦌) (groupUniversalCoverChosenZeroSimplex G) := by
    -- A constant simplex factors through the unique simplex map to `Δ[0]`.
    simp [f]
  have hmap :
      SSet.toTop.map (SSet.const (X := SSet.stdSimplex.obj n) (groupUniversalCoverChosenZeroSimplex G)) =
        SSet.toTop.map f ≫
          SSet.toTop.map
            (SSet.const (X := SSet.stdSimplex.obj ⦋0⦌) (groupUniversalCoverChosenZeroSimplex G)) := by
    -- Realization preserves the factorization through `Δ[0]`.
    calc
      SSet.toTop.map (SSet.const (X := SSet.stdSimplex.obj n) (groupUniversalCoverChosenZeroSimplex G))
        = SSet.toTop.map
            (f ≫ SSet.const (X := SSet.stdSimplex.obj ⦋0⦌) (groupUniversalCoverChosenZeroSimplex G)) := by
              rw [hconst]
      _ = SSet.toTop.map f ≫
            SSet.toTop.map
              (SSet.const (X := SSet.stdSimplex.obj ⦋0⦌) (groupUniversalCoverChosenZeroSimplex G)) := by
              rw [Functor.map_comp]
  have hpoint :
      (SSet.toTop.map f) u =
        (SSet.toTopSimplex.app ⦋0⦌).inv (default : SimplexCategory.toTop.obj ⦋0⦌) := by
    -- The realization of `Δ[0]` is a singleton after transferring to the topological simplex.
    let e :
        SSet.toTop.obj (SSet.stdSimplex.obj ⦋0⦌) ≃ₜ SimplexCategory.toTop.obj ⦋0⦌ :=
      TopCat.homeoOfIso (SSet.toTopSimplex.app ⦋0⦌)
    have hpoint' :
        (SSet.toTopSimplex.app ⦋0⦌).hom ((SSet.toTop.map f) u) =
          (default : SimplexCategory.toTop.obj ⦋0⦌) := by
      exact Subsingleton.elim _ _
    have hpoint'' : e.symm (e ((SSet.toTop.map f) u)) = e.symm default := by
      simpa [e] using congrArg e.symm hpoint'
    calc
      (SSet.toTop.map f) u = e.symm (e ((SSet.toTop.map f) u)) := by
        exact (e.left_inv ((SSet.toTop.map f) u)).symm
      _ = e.symm default := hpoint''
      _ = (SSet.toTopSimplex.app ⦋0⦌).inv (default : SimplexCategory.toTop.obj ⦋0⦌) := by
        rfl
  calc
    (SSet.toTop.map
        (SSet.const (X := SSet.stdSimplex.obj n) (groupUniversalCoverChosenZeroSimplex G))) u
      = (SSet.toTop.map
          (SSet.const (X := SSet.stdSimplex.obj ⦋0⦌) (groupUniversalCoverChosenZeroSimplex G)))
          ((SSet.toTop.map f) u) := by
            exact congrArg (fun g ↦ g u) hmap
    _ = groupUniversalCoverBasePoint G := by
      rw [hpoint, groupUniversalCoverBasePoint]

/-- Helper for Construction 16.5.2: the realized constant simplicial endomorphism of `EG`
collapses every point to the chosen basepoint. -/
private theorem groupUniversalCoverSpaceConstApplyEq
    (x : groupUniversalCoverSpace G) :
    (SSet.toTop.map (groupUniversalCoverSSetConst G)) x = groupUniversalCoverBasePoint G := by
  obtain ⟨n, σ, u, rfl⟩ := groupUniversalCoverSpacePointRepresentative (G := G) x
  have hcomp :
      SSet.toTop.map σ ≫ SSet.toTop.map (groupUniversalCoverSSetConst G) =
        SSet.toTop.map (σ ≫ groupUniversalCoverSSetConst G) := by
    -- Rewrite the realized composite back to the simplicial composite before simplifying it.
    simpa using (Functor.map_comp SSet.toTop σ (groupUniversalCoverSSetConst G)).symm
  calc
    (SSet.toTop.map (groupUniversalCoverSSetConst G)) ((SSet.toTop.map σ) u)
      = (SSet.toTop.map (σ ≫ groupUniversalCoverSSetConst G)) u := by
          exact congrArg (fun f ↦ f u) hcomp
    _ = (SSet.toTop.map
          (SSet.const (X := SSet.stdSimplex.obj n) (groupUniversalCoverChosenZeroSimplex G))) u := by
          simp [groupUniversalCoverSSetConst]
    _ = groupUniversalCoverBasePoint G := by
          exact groupUniversalCoverConstSimplex_apply_eq_basePoint (G := G) u

/-- Helper for Construction 16.5.2: the realized constant simplicial endomorphism of `EG`
is exactly the constant map at the chosen basepoint. -/
private theorem groupUniversalCoverSpaceConstEq_basePoint :
    (SSet.toTop.map (groupUniversalCoverSSetConst G)).hom =
      ContinuousMap.const _ (groupUniversalCoverBasePoint G) := by
  -- Upgrade the pointwise collapse formula to an equality of continuous endomorphisms.
  ext x
  exact groupUniversalCoverSpaceConstApplyEq (G := G) x

/-- Helper for Construction 16.5.2: if one barycentric coordinate of a realized standard simplex
vanishes, then the point factors through the corresponding codimension-one face. -/
private theorem standardSimplexPointFactorThroughZeroCoordinateFace
    {m : ℕ} (u : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m + 1⦌)) (i : Fin (m + 2))
    (hzero : (SimplexCategory.toTopHomeo ⦋m + 1⦌ u) i = 0) :
    ∃ u' : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m⦌),
      SSet.toTop.map (SSet.stdSimplex.δ i) u' = u := by
  let v : stdSimplex ℝ (Fin (m + 2)) := SimplexCategory.toTopHomeo ⦋m + 1⦌ u
  have hvsum : 1 = v i + ∑ j : Fin (m + 1), v (i.succAbove j) := by
    -- Split the simplex-weight sum into the vanishing coordinate and the complementary face.
    simpa using (Fin.sum_univ_succAbove (fun j : Fin (m + 2) ↦ v j) i)
  have hfaceSum : ∑ j : Fin (m + 1), v (i.succAbove j) = 1 := by
    -- Removing the zero coordinate leaves a probability distribution on the face.
    have hvsum' : v i + ∑ j : Fin (m + 1), v (i.succAbove j) = 1 := hvsum.symm
    have hz : v i = 0 := by
      simpa [v] using hzero
    rw [hz, zero_add] at hvsum'
    exact hvsum'
  let w : stdSimplex ℝ (Fin (m + 1)) := by
    -- The face point is obtained by deleting the zero coordinate.
    refine ⟨fun j ↦ v (i.succAbove j), ?_⟩
    refine ⟨?_, hfaceSum⟩
    intro j
    exact v.2.1 _
  refine ⟨(SimplexCategory.toTopHomeo ⦋m⦌).symm w, ?_⟩
  apply (SimplexCategory.toTopHomeo ⦋m + 1⦌).injective
  have hnat₀ :
      SimplexCategory.toTopHomeo ⦋m + 1⦌
          (SSet.toTop.map (SSet.stdSimplex.map (SimplexCategory.δ i))
            ((SimplexCategory.toTopHomeo ⦋m⦌).symm w)) =
        stdSimplex.map (SimplexCategory.δ i)
          ((SimplexCategory.toTopHomeo ⦋m⦌)
            ((SimplexCategory.toTopHomeo ⦋m⦌).symm w)) := by
    -- Transfer the face map across the realization homeomorphism.
    simpa using
      (SimplexCategory.toTopHomeo_naturality_apply (SimplexCategory.δ i)
        ((SimplexCategory.toTopHomeo ⦋m⦌).symm w))
  have hnat :
      SimplexCategory.toTopHomeo ⦋m + 1⦌
          (SSet.toTop.map (SSet.stdSimplex.δ i) ((SimplexCategory.toTopHomeo ⦋m⦌).symm w)) =
        stdSimplex.map (SimplexCategory.δ i) w := by
    -- Simplify the inverse-followed-by-homeomorphism on the face point.
    have hw :
        (SimplexCategory.toTopHomeo ⦋m⦌) ((SimplexCategory.toTopHomeo ⦋m⦌).symm w) = w :=
      (SimplexCategory.toTopHomeo ⦋m⦌).right_inv w
    calc
      SimplexCategory.toTopHomeo ⦋m + 1⦌
          (SSet.toTop.map (SSet.stdSimplex.δ i) ((SimplexCategory.toTopHomeo ⦋m⦌).symm w))
        = stdSimplex.map (SimplexCategory.δ i)
            ((SimplexCategory.toTopHomeo ⦋m⦌)
              ((SimplexCategory.toTopHomeo ⦋m⦌).symm w)) := hnat₀
      _ = stdSimplex.map (SimplexCategory.δ i) w := by
        exact congrArg (stdSimplex.map (SimplexCategory.δ i)) hw
  rw [hnat]
  ext j
  change (FunOnFinite.linearMap ℝ ℝ (SimplexCategory.δ i) w) j = v j
  by_cases hj : j = i
  · subst j
    -- The deleted coordinate stays zero after reinserting the face point.
    rw [show v i = 0 by simpa [v] using hzero]
    have hne : ∀ x : Fin (m + 1), (SimplexCategory.δ i) x ≠ i := by
      intro x
      intro hx
      change i.succAbove x = i at hx
      exact Fin.succAbove_ne i x hx
    rw [FunOnFinite.linearMap_apply_apply]
    change (Finset.univ.filter (fun x : Fin (m + 1) => (SimplexCategory.δ i) x = i)).sum w = 0
    refine Finset.sum_eq_zero ?_
    intro x hx
    exfalso
    exact hne x ((Finset.mem_filter.mp hx).2)
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
    -- Every surviving coordinate is recovered from the unique preimage under `δ i`.
    have heq : ∀ x : Fin (m + 1), (SimplexCategory.δ i) x = i.succAbove k ↔ x = k := by
      intro x
      constructor
      · intro hx
        change i.succAbove x = i.succAbove k at hx
        exact Fin.succAbove_right_injective hx
      · intro hx
        rw [hx]
        change i.succAbove k = i.succAbove k
        rfl
    rw [FunOnFinite.linearMap_apply_apply]
    have hsingle :
        Finset.univ.filter (fun x : Fin (m + 1) => (SimplexCategory.δ i) x = i.succAbove k) =
          {k} := by
      ext x
      simpa using (heq x)
    change (Finset.univ.filter
        (fun x : Fin (m + 1) => (SimplexCategory.δ i) x = i.succAbove k)).sum w =
      v (i.succAbove k)
    rw [hsingle]
    calc
      ({k} : Finset (Fin (m + 1))).sum w = w k := by simp
      _ = v (i.succAbove k) := by
        change v (i.succAbove k) = v (i.succAbove k)
        rfl

/-- Helper for Construction 16.5.2: after reducing to a nondegenerate simplex leg, the remaining
freeness step is to compare a realized point with its `G`-translate on that normalized owner. -/
private theorem groupUniversalCoverEqOneOfSmulEqOfNondegenerateRepresentative
    {g : G} {m : ℕ}
    (τ : (groupUniversalCoverSSet G).nonDegenerate m)
    (u : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m⦌))
    (h : g • ((SSet.toTop.map (SSet.yonedaEquiv.symm τ.1)) u) =
      ((SSet.toTop.map (SSet.yonedaEquiv.symm τ.1)) u)) :
    g = 1 := by
  -- Route correction: split the realized simplex point into the zero-dimensional base case and
  -- the positive-dimensional boundary-versus-interior dichotomy from the re-plan.
  cases m with
  | zero =>
      -- In dimension `0`, the simplex leg is already a single vertex. The remaining work is to
      -- identify the realized fixed point with that vertex and reduce to levelwise freeness.
      -- TODO: rewrite the realized point through `TopCat.toSSetObj₀Equiv` and finish with
      -- `groupUniversalCoverNondegenerate_eq_one_of_smul_eq`.
      sorry
  | succ m =>
      let v : stdSimplex ℝ (Fin (m + 2)) := SimplexCategory.toTopHomeo ⦋m + 1⦌ u
      by_cases hInterior : ∀ j : Fin (m + 2), 0 < v j
      · -- The interior case is exactly the uniqueness-of-support step requested by the re-plan.
        -- TODO: compare `τ` with its `g`-translate via
        -- `SSet.unique_nonDegenerate_simplex` and `SSet.unique_nonDegenerate_map`, then finish
        -- with `groupUniversalCoverNondegenerate_eq_one_of_smul_eq`.
        sorry
      · obtain ⟨i, hi⟩ := not_forall.mp hInterior
        -- On the boundary, the first missing ingredient is to remove one zero barycentric
        -- coordinate and pass to the corresponding codimension-one face.
        have hzero : v i = 0 := by
          have hle : 0 ≤ v i := v.2.1 i
          linarith
        have hvsum : 1 = v i + ∑ j : Fin (m + 1), v (i.succAbove j) := by
          simpa using (Fin.sum_univ_succAbove (fun j : Fin (m + 2) ↦ v j) i)
        have hfaceSum : ∑ j : Fin (m + 1), v (i.succAbove j) = 1 := by
          linarith
        let w : stdSimplex ℝ (Fin (m + 1)) := by
          refine ⟨fun j ↦ v (i.succAbove j), ?_⟩
          refine ⟨?_, hfaceSum⟩
          intro j
          exact v.2.1 _
        obtain ⟨uFace, huFace⟩ :=
          standardSimplexPointFactorThroughZeroCoordinateFace (u := u) i hzero
        -- The boundary normalization is now explicit; the remaining blocker is to re-decompose
        -- the face leg through `SSet.exists_nonDegenerate` and recurse on the smaller owner.
        have hreprFace :
            (SSet.toTop.map (SSet.yonedaEquiv.symm τ.1))
                (SSet.toTop.map (SSet.stdSimplex.δ i) uFace) =
              (SSet.toTop.map (SSet.yonedaEquiv.symm τ.1)) u := by
          simpa [huFace]
        have _ := w
        have _ := uFace
        have _ := huFace
        have _ := hreprFace
        sorry

/-- Helper for Construction 16.5.2: once a realization point is presented on one simplex leg, the
remaining freeness step is to normalize that simplex to its nondegenerate support and descend the
fixed-point equation to the levelwise free action. -/
private theorem groupUniversalCoverSpaceEqOneOfSmulEqOfRepresentative
    {g : G} {n : SimplexCategory} (σ : SSet.stdSimplex.obj n ⟶ groupUniversalCoverSSet G)
    (u : SSet.toTop.obj (SSet.stdSimplex.obj n))
    (h : g • ((SSet.toTop.map σ) u) = ((SSet.toTop.map σ) u)) :
    g = 1 := by
  induction n using SimplexCategory.rec with
  | _ n =>
      let x : (groupUniversalCoverSSet G) _⦋n⦌ := SSet.yonedaEquiv σ
      obtain ⟨m, f, _, τ, hτ⟩ := (groupUniversalCoverSSet G).exists_nonDegenerate x
      let τMap :
          SSet.stdSimplex.obj ⦋m⦌ ⟶ groupUniversalCoverSSet G := SSet.yonedaEquiv.symm τ.1
      let u' : SSet.toTop.obj (SSet.stdSimplex.obj ⦋m⦌) :=
        SSet.toTop.map (SSet.stdSimplex.map f) u
      have hσ : σ = SSet.stdSimplex.map f ≫ τMap := by
        -- Rewrite the original simplex through its canonical nondegenerate decomposition.
        apply SSet.yonedaEquiv.injective
        rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map,
          SSet.stdSimplex.yonedaEquiv_symm_app_objEquiv_symm]
        simpa [x, τMap] using hτ
      have hrepr :
          ((SSet.toTop.map σ) u) = ((SSet.toTop.map τMap) u') := by
        -- Realization preserves the simplicial factorization through the nondegenerate owner.
        calc
          ((SSet.toTop.map σ) u)
              = ((SSet.toTop.map (SSet.stdSimplex.map f ≫ τMap)) u) := by rw [hσ]
          _ = ((SSet.toTop.map τMap) ((SSet.toTop.map (SSet.stdSimplex.map f)) u)) := by
            rw [Functor.map_comp]
            rfl
      have hτFixed :
          g • ((SSet.toTop.map τMap) u') = ((SSet.toTop.map τMap) u') := by
        -- After the factorization rewrite, the fixed-point equation only involves the
        -- nondegenerate simplex leg `τMap`.
        simpa [u', hrepr] using h
      exact
        groupUniversalCoverEqOneOfSmulEqOfNondegenerateRepresentative
          (G := G) τ u' hτFixed

/-- Helper for Construction 16.5.2: a realized fixed point for the diagonal action should descend
to a fixed simplex, after which levelwise freeness finishes the argument. -/
theorem groupUniversalCoverSpace_eq_one_of_smul_eq
    {g : G} {x : groupUniversalCoverSpace G} (h : g • x = x) :
    g = 1 := by
  -- Route correction: first choose one concrete simplex representative of `x`, then isolate the
  -- remaining normalization-to-nondegenerate-simplex argument on that fixed representative.
  obtain ⟨n, σ, u, rfl⟩ := groupUniversalCoverSpacePointRepresentative (G := G) x
  exact groupUniversalCoverSpaceEqOneOfSmulEqOfRepresentative (G := G) σ u h

/-- Construction 16.5.2 (2): the induced left `G`-action on the realized total space `EG`
is free. -/
instance groupUniversalCoverSpace_isCancelSMul :
    IsCancelSMul G (groupUniversalCoverSpace G) := by
  -- Reduce freeness on the realization to the fixed-point criterion recorded above.
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro g x h
  exact groupUniversalCoverSpace_eq_one_of_smul_eq (G := G) h

/-- Helper for Construction 16.5.2: the explicit simplicial contraction of `EG_•` should descend
to a topological homotopy from `id_EG` to the realized constant endomorphism. -/
private theorem groupUniversalCoverSpaceHomotopicToConstEndomorphism :
    (ContinuousMap.id (groupUniversalCoverSpace G)).Homotopic
      (SSet.toTop.map (groupUniversalCoverSSetConst G)).hom := by
  -- Route correction: the missing step is not a new simplicial contraction formula.
  -- The simplicial homotopy already exists; what remains is the left-Kan/colimit descent from
  -- simplex-leg homotopies to a global topological homotopy of the realization.
  have hSimplicial :
      SSet.Homotopy (groupUniversalCoverSSetConst G) (𝟙 (groupUniversalCoverSSet G)) :=
    groupUniversalCoverSSetHomotopyToConst (G := G)
  -- TODO: for each simplex leg `σ`, realize `σ ◁ 𝟙 Δ[1] ≫ hSimplicial.h` to a path-valued map on
  -- `|Δ[n]|`, prove those maps are compatible with the `CostructuredArrow` diagram from
  -- `groupUniversalCoverSpacePointRepresentative`, and descend them through the colimit
  -- presentation of `groupUniversalCoverSpace G`.
  sorry

/-- Helper for Construction 16.5.2: after geometric realization, the extra degeneracy should
contract `EG` to the point determined by `groupUniversalCoverChosenZeroSimplex`. -/
theorem groupUniversalCoverSpace_idNullhomotopic :
    (ContinuousMap.id (groupUniversalCoverSpace G)).Nullhomotopic := by
  -- Route correction: the generic monoidal transport route is genuinely unavailable here.
  -- A direct `lake env lean` check confirms that this snapshot has
  -- `TopCat.toSSet.Monoidal` but does *not* synthesize `SSet.toTop.LaxMonoidal` or
  -- `SSet.toTop.Monoidal`, so there is no built-in comparison
  -- `|(EG_• ⊗ Δ[1])| ≅ EG ⊗ TopCat.I` to realize an `SSet.Homotopy`.
  -- The remaining route must therefore descend the extra degeneracy through the explicit
  -- left-Kan-extension/colimit presentation of `SSet.toTop.obj`, not through a nonexistent
  -- monoidal instance.
  use groupUniversalCoverBasePoint G
  -- Rewrite the realized constant endomorphism to the actual constant map at the chosen
  -- basepoint, so the remaining task is exactly the descent lemma isolated above.
  rw [← groupUniversalCoverSpaceConstEq_basePoint (G := G)]
  exact groupUniversalCoverSpaceHomotopicToConstEndomorphism (G := G)

/-- Construction 16.5.2 (3): the realization `EG` of the simplicial universal principal
`G`-bundle is contractible. -/
instance groupUniversalCoverSpace_contractible :
    ContractibleSpace (groupUniversalCoverSpace G) := by
  -- The remaining topological endgame is exactly the nullhomotopy packaged above.
  rw [contractible_iff_id_nullhomotopic]
  exact groupUniversalCoverSpace_idNullhomotopic (G := G)
