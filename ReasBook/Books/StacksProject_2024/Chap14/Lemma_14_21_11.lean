import StacksProject_2024.Chap14.Lemma_14_13_4
import StacksProject_2024.Chap14.Lemma_14_17_4
import StacksProject_2024.Chap14.Lemma_14_18_4
import StacksProject_2024.Chap14.Lemma_14_19_2
import StacksProject_2024.Chap14.Lemma_14_21_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SSet.stdSimplex
open scoped Simplicial

noncomputable section

universe w u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.21.11:
- primary domain: simplicial skeleton/coskeleton comparison and internal simplicial mapping
  objects;
- sampled owner declarations:
  `SSet.Finite`,
  `truncatedSkeletonIsoSkeleton`,
  `(coskAdj n).homEquiv`,
  `simplicialHomPresheaf_const_isRepresentable_of_eventually_degenerate`,
  `RepresentableBy.uniqueUpToIso`;
- best owner abstraction: the source-facing presheaf
  `(SimplicialObject.const C).op ⋙ simplicialHomPresheaf ((SSet.sk n).obj (Δ[n + 1])) V`,
  together with its canonical `RepresentableBy` witnesses;
- primitive data: the local left-Kan-extension bridge needed to form `sk n` under finite
  coproducts, the eventual-degeneracy instance for `skₙ Δ[n + 1]`, and the two concrete
  representing objects
  `((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌` and
  `(simplicialHom ((SSet.sk n).obj (Δ[n + 1])) V) _⦋0⦌`;
- derived API: the owner-level finiteness consequences for `skₙ Δ[n + 1]` coming from `SSet.Finite`
  via `truncatedSkeletonIsoSkeleton`, and the canonical isomorphism between the two representing
  objects, obtained by `RepresentableBy.uniqueUpToIso` rather than through the chosen witness
  `Functor.reprX`.

Source/core/bridge triage:
- `source-facing`: the comparison between the degree-`n + 1` term of `coskₙ(skₙ V)` and the
  degree-`0` term of the mapping object from `skₙ Δ[n + 1]` to `V`;
- `core/canonical`: `RepresentableBy` for the restricted product-hom presheaf;
- `bridge/view`: the two concrete representing objects and the local finite-coproduct left Kan
  extension used to expose the skeleton side without strengthening the public hypotheses. -/

/- The chapter owner `simplexTruncatedInclusionOp_hasPointwiseLeftKanExtension` only applies under
`[HasFiniteColimits C]`, but the source-facing statements here use the weaker finite-coproduct
hypothesis. This local bridge supplies just the plain left Kan extension needed to form `sk n`
without changing the public assumptions of the item. -/
private theorem simplexTruncatedInclusion_hasPointwiseLeftKanExtension_aux
    [HasFiniteCoproducts C] (n : ℕ) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension F := by
  -- TODO: reduce each costructured-arrow component to its image-factorization terminal object, so
  -- the pointwise colimit becomes a finite coproduct over image representatives.
  intro Y
  sorry

private noncomputable instance simplexTruncatedInclusion_hasPointwiseLeftKanExtension
    [HasFiniteCoproducts C] (n : ℕ) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension F :=
  simplexTruncatedInclusion_hasPointwiseLeftKanExtension_aux n F

private noncomputable instance simplexTruncatedInclusion_hasLeftKanExtension
    [HasFiniteCoproducts C] (n : ℕ) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion n).op.HasLeftKanExtension F := by
  let _ := simplexTruncatedInclusion_hasPointwiseLeftKanExtension n F
  infer_instance

/-- The simplicial set `skₙ Δ[n + 1]` has dimension at most `n`. -/
private instance sk_stdSimplex_succ_hasDimensionLE (n : ℕ) :
    ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})).HasDimensionLE n := by
  change ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})).HasDimensionLT (n + 1)
  exact
    (SSet.hasDimensionLT_iff_of_iso
      (truncatedSkeletonIsoSkeleton n (Δ[n + 1] : SSet.{w})) (n + 1)).2 inferInstance

private instance sk_stdSimplex_succ_eventuallyDegenerate_fact (n : ℕ) :
    Fact (∃ d : ℕ, ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})).HasDimensionLE d) where
  out :=
  ⟨n, inferInstance⟩

private instance sk_stdSimplex_succ_finite (n : ℕ) :
    ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})).Finite :=
  SSet.finite_of_iso (truncatedSkeletonIsoSkeleton n (Δ[n + 1] : SSet.{w})).symm

/-- The simplicial set `skₙ Δ[n + 1]` has a `0`-simplex. -/
private instance sk_stdSimplex_succ_objZero_nonempty (n : ℕ) :
    Nonempty (((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) _⦋0⦌) := by
  let x : ((Δ[n + 1] : SSet.{w}).skeleton (n + 1) : SSet.{w}) _⦋0⦌ :=
    ⟨obj₀Equiv.symm 0, by
      rw [(Δ[n + 1] : SSet.{w}).skeleton_obj_eq_top
        (Nat.lt_succ_of_le (show 0 ≤ n by simp))]
      simp⟩
  exact ⟨(truncatedSkeletonIsoSkeleton n (Δ[n + 1] : SSet.{w})).inv.app _ x⟩

section Comparison

variable [HasFiniteCoproducts C] [HasFiniteLimits C]
variable (n : ℕ) (V : SimplicialObject C)

/-- Helper for Lemma 14.21.11: the local finite-coproduct bridge already supplies the pointwise
left Kan extensions needed to form `sk n V`. -/
private theorem truncation_hasPointwiseLeftKanExtension_generatedByDegreeLE :
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension ((truncation n).obj V) :=
  simplexTruncatedInclusion_hasPointwiseLeftKanExtension_aux n ((truncation n).obj V)

/-- Helper for Lemma 14.21.11: applying `SSet.Truncated.sk n` to the `n`-truncation of the
standard simplex is definitionally the same as the ordinary simplicial `n`-skeleton. -/
private noncomputable def truncated_stdSimplex_succ_sk_iso :
    (SSet.Truncated.sk n).obj ((SSet.truncation n).obj (Δ[n + 1] : SSet.{w})) ≅
      (SSet.sk n).obj (Δ[n + 1] : SSet.{w}) :=
  Iso.refl _

/-- Helper for Lemma 14.21.11: after passing through `coskAdj n`, one can transport the target
from `truncation n ((sk n).obj V)` back to `truncation n V` using the unit isomorphism of
`skAdj n`. -/
private noncomputable def truncation_sk_target_hom_equiv (A : SimplicialObject C) :
    (((truncation n).obj A) ⟶ (truncation n).obj ((sk n).obj V)) ≃
      (((truncation n).obj A) ⟶ (truncation n).obj V) :=
  -- The source proof next transports along the skeleton unit isomorphism on `truncation n V`.
  (Iso.refl _).homCongr (asIso ((skAdj n).unit.app ((truncation n).obj V))).symm

/-- Helper for Lemma 14.21.11: the target-side transport along the `skAdj` unit isomorphism
commutes with precomposition in the source simplicial object. -/
private theorem truncation_sk_target_hom_equiv_naturality
    {A₁ A₂ : SimplicialObject C} (f : A₁ ⟶ A₂)
    (g : ((truncation n).obj A₂ ⟶ (truncation n).obj ((sk n).obj V))) :
    truncation_sk_target_hom_equiv n V A₁ ((truncation n).map f ≫ g) =
      (truncation n).map f ≫ truncation_sk_target_hom_equiv n V A₂ g := by
  -- This equivalence only changes the target by postcomposition with the fixed unit isomorphism.
  simpa [truncation_sk_target_hom_equiv] using
    Iso.homCongr_comp
      (Iso.refl ((truncation n).obj A₁))
      (Iso.refl ((truncation n).obj A₂))
      (asIso ((skAdj n).unit.app ((truncation n).obj V))).symm
      ((truncation n).map f) g

/-- Helper for Lemma 14.21.11: the verified `stdSimplexProductHomEquiv` and `coskAdj` prefix,
together with the `skAdj` target transport, identifies maps into
`((cosk n).obj ((sk n).obj V))_[n+1]` with maps from the truncated product into
`(truncation n).obj V`. -/
private noncomputable def cosk_sk_obj_succ_to_truncation_hom_equiv (X : C) :
    (X ⟶ (((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌)) ≃
      (((truncation n).obj ((Δ[n + 1] : SSet.{w}) × (const C).obj X)) ⟶
        (truncation n).obj V) :=
  -- This packages the already verified prefix of the source-proof chain into one stable bridge.
  ((stdSimplexProductHomEquiv (n + 1) X ((cosk n).obj ((sk n).obj V))).symm).trans
    (((coskAdj n).homEquiv ((Δ[n + 1] : SSet.{w}) × (const C).obj X)
      ((truncation n).obj ((sk n).obj V))).symm.trans
      (truncation_sk_target_hom_equiv n V ((Δ[n + 1] : SSet.{w}) × (const C).obj X)))

/-- Helper for Lemma 14.21.11: evaluation on the distinguished simplex of `Δ[k]` is natural in
the object variable. -/
private theorem stdSimplexProductHomEquiv_naturality
    (k : ℕ) {X Y : C} (f : X ⟶ Y) (W : SimplicialObject C)
    (γ : ((Δ[k] : SSet.{w}) × (const C).obj Y) ⟶ W) :
    stdSimplexProductHomEquiv k X W
        (simplicialCopowerHom (Δ[k] : SSet.{w}) ((const C).map f) ≫ γ) =
      f ≫ stdSimplexProductHomEquiv k Y W γ := by
  -- Evaluating at the identity simplex only inserts `f` on the selected coproduct summand.
  rw [stdSimplexProductHomEquiv_apply, stdSimplexProductHomEquiv_apply]
  simp [simplicialCopowerHom_app]

/-- Helper for Lemma 14.21.11: the verified `stdSimplexProductHomEquiv → coskAdj → skAdj`
prefix is already natural in the object variable. -/
private theorem cosk_sk_obj_succ_to_truncation_hom_equiv_naturality
    {X Y : C} (f : X ⟶ Y)
    (g : Y ⟶ (((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌)) :
    cosk_sk_obj_succ_to_truncation_hom_equiv n V X (f ≫ g) =
      (truncation n).map
          (simplicialCopowerHom (Δ[n + 1] : SSet.{w}) ((const C).map f)) ≫
        cosk_sk_obj_succ_to_truncation_hom_equiv n V Y g := by
  let A₁ : SimplicialObject C := (Δ[n + 1] : SSet.{w}) × (const C).obj X
  let A₂ : SimplicialObject C := (Δ[n + 1] : SSet.{w}) × (const C).obj Y
  let Amap : A₁ ⟶ A₂ :=
    simplicialCopowerHom (Δ[n + 1] : SSet.{w}) ((const C).map f)
  let T : SimplicialObject.Truncated C n := (truncation n).obj ((sk n).obj V)
  let e₀X :
      (X ⟶ (((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌)) ≃
        (A₁ ⟶ (cosk n).obj ((sk n).obj V)) :=
    (stdSimplexProductHomEquiv (n + 1) X ((cosk n).obj ((sk n).obj V))).symm
  let e₀Y :
      (Y ⟶ (((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌)) ≃
        (A₂ ⟶ (cosk n).obj ((sk n).obj V)) :=
    (stdSimplexProductHomEquiv (n + 1) Y ((cosk n).obj ((sk n).obj V))).symm
  let e₁X :
      (A₁ ⟶ (cosk n).obj ((sk n).obj V)) ≃ (((truncation n).obj A₁) ⟶ T) :=
    ((coskAdj n).homEquiv A₁ T).symm
  let e₁Y :
      (A₂ ⟶ (cosk n).obj ((sk n).obj V)) ≃ (((truncation n).obj A₂) ⟶ T) :=
    ((coskAdj n).homEquiv A₂ T).symm
  let e₂X :
      (((truncation n).obj A₁) ⟶ T) ≃ (((truncation n).obj A₁) ⟶ (truncation n).obj V) :=
    truncation_sk_target_hom_equiv n V A₁
  let e₂Y :
      (((truncation n).obj A₂) ⟶ T) ≃ (((truncation n).obj A₂) ⟶ (truncation n).obj V) :=
    truncation_sk_target_hom_equiv n V A₂
  -- First move `f` through evaluation at the identity simplex in degree `n + 1`.
  have h₀ : e₀X (f ≫ g) = Amap ≫ e₀Y g := by
    apply (stdSimplexProductHomEquiv (n + 1) X ((cosk n).obj ((sk n).obj V))).injective
    calc
      stdSimplexProductHomEquiv (n + 1) X ((cosk n).obj ((sk n).obj V)) (e₀X (f ≫ g)) =
          f ≫ g := by
            exact Equiv.apply_symm_apply
              (stdSimplexProductHomEquiv (n + 1) X ((cosk n).obj ((sk n).obj V))) (f ≫ g)
      _ = f ≫ stdSimplexProductHomEquiv (n + 1) Y ((cosk n).obj ((sk n).obj V)) (e₀Y g) := by
            rw [show
              stdSimplexProductHomEquiv (n + 1) Y ((cosk n).obj ((sk n).obj V)) (e₀Y g) = g by
                exact
                  Equiv.apply_symm_apply
                    (stdSimplexProductHomEquiv (n + 1) Y ((cosk n).obj ((sk n).obj V))) g]
      _ = stdSimplexProductHomEquiv (n + 1) X ((cosk n).obj ((sk n).obj V)) (Amap ≫ e₀Y g) := by
            symm
            exact stdSimplexProductHomEquiv_naturality
              (n + 1) f ((cosk n).obj ((sk n).obj V)) (e₀Y g)
  -- Then use naturality of the `coskAdj n` hom-set equivalence in the source object.
  have h₁ :
      e₁X (Amap ≫ e₀Y g) = (truncation n).map Amap ≫ e₁Y (e₀Y g) := by
    simpa [e₁X, e₁Y, Amap, T] using (coskAdj n).homEquiv_naturality_left_symm Amap (e₀Y g)
  -- Finally the target transport along the `skAdj n` unit isomorphism is source-natural.
  have h₂ :
      e₂X ((truncation n).map Amap ≫ e₁Y (e₀Y g)) =
        (truncation n).map Amap ≫ e₂Y (e₁Y (e₀Y g)) := by
    simpa [e₂X, e₂Y, Amap] using
      truncation_sk_target_hom_equiv_naturality (n := n) (V := V) Amap (e₁Y (e₀Y g))
  -- Chaining the three source-natural steps gives naturality for the whole prefix.
  calc
    cosk_sk_obj_succ_to_truncation_hom_equiv n V X (f ≫ g) = e₂X (e₁X (e₀X (f ≫ g))) := rfl
    _ = e₂X (e₁X (Amap ≫ e₀Y g)) := by rw [h₀]
    _ = e₂X ((truncation n).map Amap ≫ e₁Y (e₀Y g)) := by rw [h₁]
    _ = (truncation n).map Amap ≫ e₂Y (e₁Y (e₀Y g)) := h₂
    _ = (truncation n).map
          (simplicialCopowerHom (Δ[n + 1] : SSet.{w}) ((const C).map f)) ≫
        cosk_sk_obj_succ_to_truncation_hom_equiv n V Y g := rfl

private def constPointCopowerSectionApp (X : C) (Δ : SimplexCategoryᵒᵖ) :
    X ⟶ (((Δ[0] : SSet.{w}) × (const C).obj X).obj Δ) :=
  Sigma.ι (fun _ : (Δ[0] : SSet.{w}).obj Δ ↦ X) (SSet.stdSimplex.const 0 0 Δ)

omit [HasFiniteLimits C] in
private theorem constPointCopowerSection_naturality (X : C)
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') :
    ((const C).obj X).map f ≫ constPointCopowerSectionApp X Δ' =
      constPointCopowerSectionApp X Δ ≫ (((Δ[0] : SSet.{w}) × (const C).obj X).map f) := by
  -- The point simplicial set has a unique simplex in every degree, so both sides are the same
  -- coproduct injection indexed by that unique simplex.
  have hconst :
      (Δ[0] : SSet.{w}).map f (SSet.stdSimplex.const 0 0 Δ) = SSet.stdSimplex.const 0 0 Δ' := by
    apply SSet.stdSimplex.objEquiv.injective
    rw [SSet.stdSimplex.map_apply]
    exact Subsingleton.elim _ _
  rw [constPointCopowerSectionApp, constPointCopowerSectionApp, Functor.const_obj_map]
  simpa [hconst] using
    (Sigma.ι_comp_map' ((Δ[0] : SSet.{w}).map f) (fun _ ↦ 𝟙 X) (SSet.stdSimplex.const 0 0 Δ)).symm

private def constPointCopowerSection (X : C) :
    (const C).obj X ⟶ (Δ[0] : SSet.{w}) × (const C).obj X where
  app Δ := constPointCopowerSectionApp X Δ
  naturality := fun {_ _} f ↦ constPointCopowerSection_naturality X f

/-- Helper for Lemma 14.21.11: the point-copower section is natural in the object variable. -/
private theorem constPointCopowerSection_object_naturality
    {X Y : C} (f : X ⟶ Y) :
    (const C).map f ≫ constPointCopowerSection Y =
      constPointCopowerSection X ≫
        simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f) := by
  -- Degreewise, both composites are the unique coproduct injection followed by `f`.
  ext Δ
  simp [constPointCopowerSection, constPointCopowerSectionApp, simplicialCopowerHom_app]

private theorem constPointCopowerSection_comp_projection (X : C) :
    constPointCopowerSection X ≫ simplicialCopowerProjection ((const C).obj X) (Δ[0] : SSet.{w}) =
      𝟙 ((const C).obj X) := by
  -- Degreewise, the section lands in the unique coproduct summand and the projection is the
  -- identity on every summand.
  ext Δ
  simpa [constPointCopowerSection, constPointCopowerSectionApp] using
    (Limits.Sigma.ι_desc (fun _ : (Δ[0] : SSet.{w}).obj Δ ↦ 𝟙 X) (SSet.stdSimplex.const 0 0 Δ))

private theorem constPointCopowerProjection_comp_section (X : C) :
    simplicialCopowerProjection ((const C).obj X) (Δ[0] : SSet.{w}) ≫ constPointCopowerSection X =
      𝟙 ((Δ[0] : SSet.{w}) × (const C).obj X) := by
  -- Degreewise, maps out of the singleton-indexed coproduct are determined by the unique
  -- coproduct injection.
  ext Δ
  apply Sigma.hom_ext
  intro u
  have hu :
      SSet.stdSimplex.objEquiv u = SSet.stdSimplex.objEquiv (SSet.stdSimplex.const 0 0 Δ) := by
    exact Subsingleton.elim _ _
  have hu' : u = SSet.stdSimplex.const 0 0 Δ :=
    SSet.stdSimplex.objEquiv.injective hu
  subst hu'
  rw [NatTrans.comp_app, NatTrans.id_app, simplicialCopowerProjection_app]
  simpa [constPointCopowerSection, constPointCopowerSectionApp, Category.assoc] using
    congrArg (fun t ↦ t ≫ (constPointCopowerSection X).app Δ)
      (Limits.Sigma.ι_desc
        (fun _ : (Δ[0] : SSet.{w}).obj Δ ↦ 𝟙 (((const C).obj X).obj Δ))
        (SSet.stdSimplex.const 0 0 Δ))

private noncomputable def constPointCopowerIso (X : C) :
    (Δ[0] : SSet.{w}) × (const C).obj X ≅ (const C).obj X where
  hom := simplicialCopowerProjection ((const C).obj X) (Δ[0] : SSet.{w})
  inv := constPointCopowerSection X
  hom_inv_id := constPointCopowerProjection_comp_section X
  inv_hom_id := constPointCopowerSection_comp_projection X

/-- Helper for Lemma 14.21.11: degree-`0` evaluation on the point copower is natural in the
object variable. -/
private theorem stdSimplexProductHomEquiv_zero_naturality
    {X Y : C} (f : X ⟶ Y) (W : SimplicialObject C)
    (γ : ((Δ[0] : SSet.{w}) × (const C).obj Y) ⟶ W) :
    stdSimplexProductHomEquiv 0 X W
        (simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f) ≫ γ) =
      f ≫ stdSimplexProductHomEquiv 0 Y W γ := by
  -- This is the `k = 0` specialization of the general naturality lemma above.
  simpa using stdSimplexProductHomEquiv_naturality 0 f W γ

private noncomputable def simplicialHom_objZero_represents_const_restriction :
    (((const C).op ⋙ simplicialHomPresheaf ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) V)).RepresentableBy
      ((simplicialHom ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) V) _⦋0⦌) where
  homEquiv {X} :=
    let U : SSet.{w} := (SSet.sk n).obj (Δ[n + 1] : SSet.{w})
    let e₀ :
        ((((Δ[0] : SSet.{w}) × (const C).obj X) ⟶ simplicialHom U V) ≃
          (X ⟶ (simplicialHom U V) _⦋0⦌)) :=
      stdSimplexProductHomEquiv 0 X (simplicialHom U V)
    let e₁ :
        ((((Δ[0] : SSet.{w}) × (const C).obj X) ⟶ simplicialHom U V) ≃
          (simplicialHomPresheaf U V).obj (op (((Δ[0] : SSet.{w}) × (const C).obj X)))) :=
      (simplicialHomPresheaf U V).representableBy.homEquiv
    let e₂ :
        (simplicialHomPresheaf U V).obj (op (((Δ[0] : SSet.{w}) × (const C).obj X))) ≃
          (((const C).op ⋙ simplicialHomPresheaf U V).obj (op X)) :=
      ((simplicialHomPresheaf U V).mapIso (constPointCopowerIso X).op).toEquiv.symm
    e₀.symm.trans (e₁.trans e₂)
  homEquiv_comp := by
    intro X Y f g
    -- The composite equivalence is built from the degree-`0` standard-simplex evaluation, the
    -- owner representing equivalence for `simplicialHomPresheaf`, and transport along the point
    -- copower isomorphism; naturality is the corresponding chain of naturality statements.
    let U : SSet.{w} := (SSet.sk n).obj (Δ[n + 1] : SSet.{w})
    let ψ : ((Δ[0] : SSet.{w}) × (const C).obj Y) ⟶ simplicialHom U V :=
      (stdSimplexProductHomEquiv 0 Y (simplicialHom U V)).symm g
    -- First move `f` through the degree-`0` evaluation equivalence.
    have h₀ :
        (stdSimplexProductHomEquiv 0 X (simplicialHom U V))
            (simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f) ≫ ψ) =
          f ≫ g := by
      simpa [ψ] using stdSimplexProductHomEquiv_zero_naturality f (simplicialHom U V) ψ
    -- Next use naturality of the owner representing equivalence for `simplicialHomPresheaf U V`.
    have h₁ :
        (simplicialHomPresheaf U V).representableBy.homEquiv
            (simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f) ≫ ψ) =
          (simplicialHomPresheaf U V).map
            (simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f)).op
            ((simplicialHomPresheaf U V).representableBy.homEquiv ψ) := by
      simpa using
        ((simplicialHomPresheaf U V).representableBy.homEquiv_comp
          (simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f)) ψ)
    have hψ :
        (stdSimplexProductHomEquiv 0 X (simplicialHom U V)).symm (f ≫ g) =
          simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f) ≫ ψ := by
      apply (stdSimplexProductHomEquiv 0 X (simplicialHom U V)).injective
      simpa using (show f ≫ g =
        (stdSimplexProductHomEquiv 0 X (simplicialHom U V))
          (simplicialCopowerHom (Δ[0] : SSet.{w}) ((const C).map f) ≫ ψ) from h₀.symm)
    -- Finally identify that map with the restricted presheaf functoriality transported by the
    -- point-copower isomorphism.
    change
      (((simplicialHomPresheaf U V).mapIso (constPointCopowerIso X).op).toEquiv.symm
          ((simplicialHomPresheaf U V).representableBy.homEquiv
            ((stdSimplexProductHomEquiv 0 X (simplicialHom U V)).symm (f ≫ g)))) =
        (((const C).op ⋙ simplicialHomPresheaf U V).map f.op)
          ((((simplicialHomPresheaf U V).mapIso (constPointCopowerIso Y).op).toEquiv.symm
            ((simplicialHomPresheaf U V).representableBy.homEquiv
              ((stdSimplexProductHomEquiv 0 Y (simplicialHom U V)).symm g))))
    rw [hψ, h₁]
    -- The point-copower identifications are natural with respect to `f`.
    simpa [Functor.map_comp, ψ, Category.assoc, constPointCopowerIso] using
      congrArg
        (fun t : (const C).obj X ⟶ (Δ[0] : SSet.{w}) × (const C).obj Y ↦
          (simplicialHomPresheaf U V).map t.op
            ((simplicialHomPresheaf U V).representableBy.homEquiv
              ((stdSimplexProductHomEquiv 0 Y (simplicialHom U V)).symm g)))
        (constPointCopowerSection_object_naturality f).symm

/-- Helper for Lemma 14.21.11: the truncated product with `Δ[n + 1]` defines a presheaf on `C`
by sending `X` to maps from `truncation n (Δ[n + 1] × X)` into `truncation n V`. -/
private abbrev truncated_stdSimplex_succ_truncation_hom_presheaf :
    Cᵒᵖ ⥤ Type v :=
  ((const C ⋙ simplicialCopowerFunctor (Δ[n + 1] : SSet.{w}) ⋙ truncation n).op ⋙
    yoneda.obj ((truncation n).obj V))

/-- Helper for Lemma 14.21.11: the already verified prefix of the source proof represents the
presheaf `X ↦ Mor(truncation n (Δ[n + 1] × X), truncation n V)`. -/
private noncomputable def cosk_sk_obj_succ_represents_truncated_stdSimplex_product :
    (truncated_stdSimplex_succ_truncation_hom_presheaf.{w, u, v} (C := C) n V).RepresentableBy
      (((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌) where
  homEquiv {X} := cosk_sk_obj_succ_to_truncation_hom_equiv n V X
  homEquiv_comp := by
    intro X Y f g
    -- The only ingredients here are the already verified naturalities of the prefix chain.
    simpa [truncated_stdSimplex_succ_truncation_hom_presheaf, Functor.comp_map, Category.assoc] using
      cosk_sk_obj_succ_to_truncation_hom_equiv_naturality (n := n) (V := V) f g

/-- Helper for Lemma 14.21.11: the remaining source-side step is a natural identification between
the truncated product-hom presheaf and the restricted mapping presheaf indexed by
`skₙ Δ[n + 1]`. -/
private noncomputable def truncated_stdSimplex_succ_bridge_iso :
    truncated_stdSimplex_succ_truncation_hom_presheaf.{w, u, v} (C := C) n V ≅
      ((const C).op ⋙ simplicialHomPresheaf ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) V) :=
  -- TODO: build this natural isomorphism by the source-faithful chain
  -- `Mor(U × X, W) = Mor(U, Mor_C(X, W))`, transport across `SSet.skAdj n` on
  -- `(SSet.truncation n).obj (Δ[n + 1])`, and rewrite the source with
  -- `truncated_stdSimplex_succ_sk_iso`.
  sorry

private noncomputable def cosk_sk_obj_succ_represents_sk_stdSimplex_product
    :
    (((const C).op ⋙ simplicialHomPresheaf ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) V)).RepresentableBy
      (((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌) :=
  -- Route correction: the verified `stdSimplexProductHomEquiv → coskAdj → skAdj` prefix now
  -- stands on its own as a representability theorem. The sole remaining blocker is the
  -- source-side natural isomorphism `truncated_stdSimplex_succ_bridge_iso`.
  Functor.RepresentableBy.ofIso
    (cosk_sk_obj_succ_represents_truncated_stdSimplex_product.{w, u, v} (n := n) (V := V))
    (truncated_stdSimplex_succ_bridge_iso.{w, u, v} (C := C) (n := n) (V := V))

-- Proof sketch: by Lemma `14.19.0.1`, the object `((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌`
-- represents the functor `X ↦ Mor((truncation n).obj (X × Δ[n + 1]), (truncation n).obj V)`.
-- Lemma `14.13.4` identifies the restricted mapping presheaf with morphisms into the degree-`0`
-- term of `simplicialHom ((SSet.sk n).obj (Δ[n + 1])) V`, while Lemma `14.17.4` supplies the owner-level
-- representability of that restricted presheaf. The result is the canonical isomorphism between
-- two `RepresentableBy` witnesses for the same presheaf.
/-- Lemma 14.21.11: for a simplicial object `V` in a category with finite coproducts and finite
limits, the degree-`n + 1` term of `coskₙ(skₙ V)` is the degree-`0` term of the simplicial mapping
object from the `n`-skeleton of the standard simplex `Δ[n + 1]` to `V`. -/
noncomputable def cosk_sk_obj_succ_iso_simplicial_hom_sk_stdSimplex_obj_zero
    :
    ((cosk n).obj ((sk n).obj V)) _⦋n + 1⦌ ≅
      (simplicialHom ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) V) _⦋0⦌ :=
  Functor.RepresentableBy.uniqueUpToIso
    (cosk_sk_obj_succ_represents_sk_stdSimplex_product n V)
    (simplicialHom_objZero_represents_const_restriction n V)

end Comparison

end CategoryTheory
