import StacksProject_2024.stacks_project.Chap14.Definition_14_13_1
import StacksProject_2024.stacks_project.Chap14.Lemma_14_13_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open CategoryTheory.SimplicialObject.Truncated
open Opposite
open SimplexCategory
open SimplexCategory.Truncated
open SimplexCategory.Truncated.Hom
open SSet.stdSimplex
open scoped Simplicial SimplexCategory.Truncated

noncomputable section

universe w v u

namespace CategoryTheory

/- Domain-style sampling for Lemma 14.13.4:
- primary domain: simplicial copowers indexed by the standard simplex and their truncated
  restriction to `Δ_{≤ n}`;
- sampled same-kind declarations:
  `simplicialCopower`,
  `truncatedSimplicialCopower`,
  `simplicialCopowerCompatibleFamilyCorepresentableBy`,
  `SSet.truncation`,
  `evaluationAdjunctionRight`,
  `SSet.stdSimplex.map_apply`;
- best owner abstraction:
  the untruncated clause is owned by the chapter copower `simplicialCopower`; for the truncated
  clause, the right abstraction is the truncated chapter owner `truncatedSimplicialCopower`,
  specialized to the restricted standard simplex `(SSet.truncation n).obj (Δ[k])`, rather than
  `truncation n` of the full copower, which would force irrelevant higher-degree coproduct
  hypotheses;
- primitive data: the object `X`, the standard simplex `Δ[k]`, and for the truncated clause only
  the simplices of `Δ[k]` in truncated degrees;
- derived API: the identity simplex `objEquiv.symm (𝟙 ⦋k⦌)`, evaluation at the top truncated
  simplex `op ⦋k, hk⦌ₙ`, and the induced equivalences with maps `X ⟶ V_k`;
- source/core/bridge triage:
  `source-facing`: the Stacks lemma fixes the source simplicial set to `Δ[k]`;
  `core/canonical`: `simplicialCopower`, `truncatedSimplicialCopower`, `SSet.truncation`, and the
  representable-simplex owner `SSet.yonedaEquiv`;
  `bridge/view`: this file specializes the full copower owner to `Δ[k]`, and in the truncated
  clause specializes the truncated copower owner to the genuinely truncated source object with the
  same source-facing simplices in degrees `≤ n`. -/

variable {C : Type u} [Category.{v} C]

private instance constStdSimplexHasCoproduct (k : ℕ) (X : C)
    [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ X)] :
    ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct
        (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ ((const C).obj X).obj Δ) := by
  intro Δ
  dsimp
  infer_instance

section StdSimplexProduct

variable (k : ℕ) (X : C)
variable [∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ X)]

private noncomputable def stdSimplexCompatibleFamilyEquiv (V : SimplicialObject C) :
    SimplicialCopowerHomFamily.Compatible (Δ[k]) ((const C).obj X) V ≃
      (X ⟶ V _⦋k⦌) :=
  { toFun := fun F ↦
      F.1 (op ⦋k⦌) (objEquiv.symm (𝟙 ⦋k⦌))
    invFun := fun f ↦
      ⟨fun Δ u ↦ f ≫ V.map (objEquiv u).op, by
        intro Δ Δ' φ u
        simp [SSet.stdSimplex.map_apply, Category.assoc]⟩
    left_inv := by
      intro F
      apply Subtype.ext
      funext Δ u
      simpa [SSet.stdSimplex.map_apply, Category.assoc] using
        (F.2 ((objEquiv u).op) (objEquiv.symm (𝟙 ⦋k⦌))).symm
    right_inv := by
      intro f
      simp }

/-- Lemma 14.13.4 (1): morphisms from `Δ[k] × X` to a simplicial object `V` are canonically in
bijection with morphisms from `X` to the degree-`k` term `V_k`. This is the specialization of
`Δ[k] × X`, followed by evaluation at the identity simplex. -/
noncomputable def stdSimplexProductHomEquiv (V : SimplicialObject C) :
    (((Δ[k] : SSet.{w}) × (const C).obj X) ⟶ V) ≃ (X ⟶ V _⦋k⦌) :=
  (simplicialCopowerCompatibleFamilyCorepresentableBy
      (Δ[k]) ((const C).obj X)).homEquiv.trans
    (stdSimplexCompatibleFamilyEquiv k X V)

-- Proof sketch: this is immediate from the definition of `stdSimplexProductHomEquiv`.
/-- The canonical bijection sends `γ : Δ[k] × X ⟶ V` to the restriction of `γ_k` to the coproduct
summand indexed by `𝟙_[k]`. -/
theorem stdSimplexProductHomEquiv_apply (V : SimplicialObject C)
    (γ : ((Δ[k] : SSet.{w}) × (const C).obj X) ⟶ V) :
    stdSimplexProductHomEquiv k X V γ =
      Sigma.ι (fun _ : (Δ[k] : SSet.{w}).obj (op ⦋k⦌) ↦ X) (objEquiv.symm (𝟙 ⦋k⦌)) ≫
        γ.app (op ⦋k⦌) := by
  change stdSimplexCompatibleFamilyEquiv k X V
      (((simplicialCopowerCompatibleFamilyCorepresentableBy
        (Δ[k]) ((const C).obj X)).homEquiv γ)) =
    Sigma.ι (fun _ : (Δ[k] : SSet.{w}).obj (op ⦋k⦌) ↦ X) (objEquiv.symm (𝟙 ⦋k⦌)) ≫
      γ.app (op ⦋k⦌)
  rfl

end StdSimplexProduct

section TruncatedStdSimplexProduct

variable {n k : ℕ} (hk : k ≤ n) (X : C)
variable (W : SimplicialObject.Truncated C n)

private instance truncatedStdSimplexConstHasCoproduct (n k : ℕ) (X : C)
    [∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ,
      HasCoproduct (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X)] :
    ∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ,
      HasCoproduct
        (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X).obj Δ) := by
  intro Δ
  simpa using
    (inferInstance :
      HasCoproduct (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X))

variable [∀ Δ : (SimplexCategory.Truncated n)ᵒᵖ,
  HasCoproduct (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X)]

/-- The truncated simplicial operator determined by a simplex of `Δ[k]`. -/
private def truncatedStdSimplexSimplexMap (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ) :
    op ⦋k, hk⦌ₙ ⟶ Δ :=
  (tr (objEquiv u) (unop Δ).property hk).op

/-- Helper for Lemma 14.13.4: composing the truncated simplex determined by `u` with a truncated
operator matches the reindexed simplex in the target degree. -/
private theorem truncated_std_simplex_simplexMap_comp
    {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (φ : Δ₁ ⟶ Δ₂)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ₁) :
    truncatedStdSimplexSimplexMap hk Δ₁ u ≫ φ =
      truncatedStdSimplexSimplexMap hk Δ₂ (((SSet.truncation n).obj (Δ[k] : SSet.{w})).map φ u) := by
  -- Proof comment: both sides are the truncations of the same composite simplex
  -- `objEquiv u ≫ unop φ`, so this is a direct normalization of the definitions.
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext i
  rfl

/-- Helper for Lemma 14.13.4: evaluating the identity `k`-simplex along the truncated simplex map
attached to `u` recovers `u`. -/
private theorem truncated_std_simplex_top_simplex_map_apply
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ) :
    ((SSet.truncation n).obj (Δ[k] : SSet.{w})).map
        (truncatedStdSimplexSimplexMap hk Δ u)
        (objEquiv.symm (𝟙 ⦋k⦌)) = u := by
  -- Proof comment: the top simplex map was defined from the simplex represented by `u`,
  -- so evaluating it on the identity simplex returns exactly that simplex.
  apply objEquiv.injective
  ext i
  rfl

/-- Helper for Lemma 14.13.4: the truncated simplex map attached to the top identity simplex is
the identity morphism of the top truncated simplex. -/
private theorem truncated_std_simplex_top_simplex_map_id :
    truncatedStdSimplexSimplexMap hk (op ⦋k, hk⦌ₙ) (objEquiv.symm (𝟙 ⦋k⦌)) =
      𝟙 (op ⦋k, hk⦌ₙ) := by
  -- Proof comment: the identity simplex corresponds to the identity morphism on `[k]`.
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  ext i
  rfl

private def truncatedStdSimplexProductHomEquivToFun
    (γ :
      truncatedSimplicialCopower
          ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
        W) :
    X ⟶ W _⦋k, hk⦌ₙ :=
  Sigma.ι
      (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
      (objEquiv.symm (𝟙 ⦋k⦌)) ≫
    γ.app (op ⦋k, hk⦌ₙ)

private def truncatedStdSimplexProductHomEquivInvApp
    (f : X ⟶ W _⦋k,hk⦌ₙ)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    (truncatedSimplicialCopower
        ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
        ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).obj Δ ⟶
      W.obj Δ :=
  Limits.Sigma.desc (fun u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦
    f ≫ W.map (truncatedStdSimplexSimplexMap hk Δ u))

-- Proof sketch: compare both composites on each coproduct summand. Naturality of the family comes
-- from composing the simplex represented by `u` with the truncated simplicial operator and then
-- applying functoriality of `W`.
private theorem truncatedStdSimplexProductHomEquivInv_naturality
    (f : X ⟶ W _⦋k,hk⦌ₙ) :
    ∀ {Δ₁ Δ₂ : (SimplexCategory.Truncated n)ᵒᵖ} (φ : Δ₁ ⟶ Δ₂),
      CommSq
        ((truncatedSimplicialCopower
            ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).map φ)
        (truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₁)
        (truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₂)
        (W.map φ) := by
  intro Δ₁ Δ₂ φ
  refine CommSq.mk ?_
  -- Proof comment: the source is a coproduct, so it is enough to compare the two composites
  -- after precomposing with each coproduct injection indexed by a simplex `u`.
  apply Limits.Sigma.hom_ext
  intro u
  calc
    Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ₁ ↦ X) u ≫
        (truncatedSimplicialCopower
            ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).map φ ≫
        truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₂ =
      Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ₂ ↦ X)
          (((SSet.truncation n).obj (Δ[k] : SSet.{w})).map φ u) ≫
        truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₂ := by
          simpa [truncatedSimplicialCopower_map, Category.assoc] using
            congrArg
              (fun t =>
                t ≫ truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₂)
              (Sigma.ι_comp_map'
                (p := ((SSet.truncation n).obj (Δ[k] : SSet.{w})).map φ)
                (q := fun _ ↦ 𝟙 X) u)
    _ = f ≫
          W.map
            (truncatedStdSimplexSimplexMap hk Δ₂
              (((SSet.truncation n).obj (Δ[k] : SSet.{w})).map φ u)) := by
          simpa [truncatedStdSimplexProductHomEquivInvApp, Category.assoc] using
            (Sigma.ι_desc
              (fun v : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ₂ ↦
                f ≫ W.map (truncatedStdSimplexSimplexMap hk Δ₂ v))
              (((SSet.truncation n).obj (Δ[k] : SSet.{w})).map φ u))
    _ = f ≫ W.map (truncatedStdSimplexSimplexMap hk Δ₁ u) ≫ W.map φ := by
          rw [← truncated_std_simplex_simplexMap_comp (hk := hk) (φ := φ) (u := u)]
          simp [Functor.map_comp]
    _ =
      Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ₁ ↦ X) u ≫
        truncatedStdSimplexProductHomEquivInvApp hk X W f Δ₁ ≫
        W.map φ := by
          symm
          simpa [truncatedStdSimplexProductHomEquivInvApp, Category.assoc] using
            congrArg
              (fun t => t ≫ W.map φ)
              (Sigma.ι_desc
                (fun v : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ₁ ↦
                  f ≫ W.map (truncatedStdSimplexSimplexMap hk Δ₁ v))
                u)

private def truncatedStdSimplexProductHomEquivInv
    (f : X ⟶ W _⦋k,hk⦌ₙ) :
    truncatedSimplicialCopower
        ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
        ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
      W where
  app Δ := truncatedStdSimplexProductHomEquivInvApp hk X W f Δ
  naturality := fun {_ _} φ ↦
    (truncatedStdSimplexProductHomEquivInv_naturality hk X W f φ).w

-- Proof sketch: extensionality on morphisms in the truncated functor category reduces the claim to
-- equality on each truncated degree, where coproduct extensionality and the standard simplex
-- identities recover the original components of `γ`.
private theorem truncatedStdSimplexProductHomEquiv_left_inv
    (γ :
      truncatedSimplicialCopower
          ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
        W) :
    truncatedStdSimplexProductHomEquivInv hk X W
        (truncatedStdSimplexProductHomEquivToFun hk X W γ) =
      γ := by
  -- Proof comment: compare the two natural transformations degreewise, then reduce each degree
  -- to the coproduct summands indexed by simplices `u : [m] → [k]`.
  ext Δ
  apply Limits.Sigma.hom_ext
  intro u
  -- Proof comment: naturality of `γ` along the simplex represented by `u` expresses the
  -- `u`-component in degree `Δ` in terms of the top identity component.
  have hγ_raw :=
    congrArg
      (fun t =>
        Sigma.ι
            (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
            (objEquiv.symm (𝟙 ⦋k⦌)) ≫
          t)
      (γ.naturality (truncatedStdSimplexSimplexMap hk Δ u))
  have htop :
      Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
          (objEquiv.symm (𝟙 ⦋k⦌)) ≫
        (truncatedSimplicialCopower
            ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).map
          (truncatedStdSimplexSimplexMap hk Δ u) =
      Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X) u := by
    calc
      Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
          (objEquiv.symm (𝟙 ⦋k⦌)) ≫
        (truncatedSimplicialCopower
            ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
            ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).map
          (truncatedStdSimplexSimplexMap hk Δ u) =
        (𝟙 X : X ⟶ X) ≫
          Sigma.ι
            (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X)
            (((SSet.truncation n).obj (Δ[k] : SSet.{w})).map
              (truncatedStdSimplexSimplexMap hk Δ u)
              (objEquiv.symm (𝟙 ⦋k⦌)) ) := by
              simpa [truncatedSimplicialCopower_map] using
                (Sigma.ι_comp_map'
                  (f := fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
                  (g := fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X)
                  (p := ((SSet.truncation n).obj (Δ[k] : SSet.{w})).map
                    (truncatedStdSimplexSimplexMap hk Δ u))
                  (q := fun _ ↦ (𝟙 X : X ⟶ X))
                  (objEquiv.symm (𝟙 ⦋k⦌)))
      _ = Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X) u := by
            rw [truncated_std_simplex_top_simplex_map_apply (hk := hk) (Δ := Δ) (u := u)]
            simp
  have hγ :
      Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X) u ≫
          γ.app Δ =
        truncatedStdSimplexProductHomEquivToFun hk X W γ ≫
          W.map (truncatedStdSimplexSimplexMap hk Δ u) := by
    calc
      Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X) u ≫ γ.app Δ =
        (Sigma.ι
            (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
            (objEquiv.symm (𝟙 ⦋k⦌)) ≫
          (truncatedSimplicialCopower
              ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
              ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X)).map
            (truncatedStdSimplexSimplexMap hk Δ u)) ≫
          γ.app Δ := by
            rw [htop]
            simp
      _ =
        Sigma.ι
            (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
            (objEquiv.symm (𝟙 ⦋k⦌)) ≫
          γ.app (op ⦋k, hk⦌ₙ) ≫
          W.map (truncatedStdSimplexSimplexMap hk Δ u) := by
            simpa [Category.assoc] using hγ_raw
      _ =
        truncatedStdSimplexProductHomEquivToFun hk X W γ ≫
          W.map (truncatedStdSimplexSimplexMap hk Δ u) := by
            simp [truncatedStdSimplexProductHomEquivToFun, Category.assoc]
  calc
    Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X) u ≫
        (truncatedStdSimplexProductHomEquivInv hk X W
          (truncatedStdSimplexProductHomEquivToFun hk X W γ)).app Δ =
      truncatedStdSimplexProductHomEquivToFun hk X W γ ≫
        W.map (truncatedStdSimplexSimplexMap hk Δ u) := by
          simpa [truncatedStdSimplexProductHomEquivInv, truncatedStdSimplexProductHomEquivInvApp,
            Category.assoc] using
            (Sigma.ι_desc
              (fun v : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦
                truncatedStdSimplexProductHomEquivToFun hk X W γ ≫
                  W.map (truncatedStdSimplexSimplexMap hk Δ v))
              u)
    _ = Sigma.ι (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj Δ ↦ X) u ≫
          γ.app Δ := by
          exact hγ.symm

-- Proof sketch: at each truncated degree the reconstructed map sends the summand indexed by a
-- simplex `u : [m] → [k]` to `f` followed by `W(u)`. Evaluating at the identity simplex yields `f`.
private theorem truncatedStdSimplexProductHomEquiv_right_inv
    (f : X ⟶ W _⦋k,hk⦌ₙ) :
    truncatedStdSimplexProductHomEquivToFun hk X W
        (truncatedStdSimplexProductHomEquivInv hk X W f) =
      f := by
  -- Proof comment: evaluate the reconstructed coproduct map on the summand indexed by the
  -- identity simplex and use that the corresponding truncated simplex map is the identity.
  calc
    truncatedStdSimplexProductHomEquivToFun hk X W
        (truncatedStdSimplexProductHomEquivInv hk X W f) =
      f ≫ W.map
        (truncatedStdSimplexSimplexMap hk (op ⦋k, hk⦌ₙ) (objEquiv.symm (𝟙 ⦋k⦌)) ) := by
          simpa [truncatedStdSimplexProductHomEquivToFun, truncatedStdSimplexProductHomEquivInv,
            truncatedStdSimplexProductHomEquivInvApp, Category.assoc] using
            (Sigma.ι_desc
              (fun u : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦
                f ≫ W.map (truncatedStdSimplexSimplexMap hk (op ⦋k, hk⦌ₙ) u))
              (objEquiv.symm (𝟙 ⦋k⦌)))
    _ = f := by
          rw [truncated_std_simplex_top_simplex_map_id (hk := hk)]
          simp

/-- Lemma 14.13.4 (2): for `n ≥ k`, morphisms from the direct truncated standard-simplex copower
to an `n`-truncated simplicial object `W` are canonically in bijection with morphisms from `X` to
the degree-`k` term `W_k`. This source object is the `Δ_{≤ n}`-level version of `Δ[k] × X`, so
its existence only uses coproducts in truncated degrees. -/
noncomputable def truncatedStdSimplexProductHomEquiv :
    (truncatedSimplicialCopower
        ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
        ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
      W) ≃
      (X ⟶ W _⦋k, hk⦌ₙ) :=
  { toFun := fun γ ↦
      truncatedStdSimplexProductHomEquivToFun hk X W γ
    invFun := fun f ↦
      truncatedStdSimplexProductHomEquivInv hk X W f
    left_inv := truncatedStdSimplexProductHomEquiv_left_inv hk X W
    right_inv := truncatedStdSimplexProductHomEquiv_right_inv hk X W }

-- Proof sketch: this is immediate from the definition of
-- `truncatedStdSimplexProductHomEquiv`.
/-- The truncated canonical bijection sends `γ` to the restriction of its degree-`k` component to
the coproduct summand indexed by `𝟙_[k]`. -/
theorem truncatedStdSimplexProductHomEquiv_apply
    (γ :
      truncatedSimplicialCopower
          ((SSet.truncation n).obj (Δ[k] : SSet.{w}))
          ((Functor.const (SimplexCategory.Truncated n)ᵒᵖ).obj X) ⟶
        W) :
    truncatedStdSimplexProductHomEquiv hk X W γ =
      Sigma.ι
          (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
          (objEquiv.symm (𝟙 ⦋k⦌)) ≫
        γ.app (op ⦋k, hk⦌ₙ) := by
  change truncatedStdSimplexProductHomEquivToFun hk X W γ =
    Sigma.ι
        (fun _ : ((SSet.truncation n).obj (Δ[k] : SSet.{w})).obj (op ⦋k, hk⦌ₙ) ↦ X)
        (objEquiv.symm (𝟙 ⦋k⦌)) ≫
      γ.app (op ⦋k, hk⦌ₙ)
  unfold truncatedStdSimplexProductHomEquivToFun
  simp

end TruncatedStdSimplexProduct

end CategoryTheory
