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

/-- Helper for Lemma 14.21.11: the image of a simplex morphism is represented by a smaller top
simplex whose cardinality is the size of the set-theoretic image minus one. -/
private def simplex_image_card {Δ Γ : SimplexCategory} (θ : Δ ⟶ Γ) : ℕ :=
  Fintype.card (Set.range θ.toOrderHom) - 1

/-- Helper for Lemma 14.21.11: a simplex map has nonempty image, so its image cardinality records
one less than the cardinality of that image. -/
private theorem simplex_image_card_succ {Δ Γ : SimplexCategory} (θ : Δ ⟶ Γ) :
    Fintype.card (Set.range θ.toOrderHom) = simplex_image_card θ + 1 := by
  -- The domain simplex is nonempty, so the range has positive cardinality and we can normalize the
  -- predecessor/successor arithmetic exactly.
  unfold simplex_image_card
  have hnonempty : Nonempty (Set.range θ.toOrderHom) := by
    refine ⟨⟨θ.toOrderHom 0, ?_⟩⟩
    exact ⟨0, rfl⟩
  have hpos : 0 < Fintype.card (Set.range θ.toOrderHom) :=
    Fintype.card_pos_iff.mpr hnonempty
  omega

/-- Helper for Lemma 14.21.11: the set-theoretic image of a simplex map is linearly ordered, hence
canonically order-isomorphic to a top simplex of the corresponding cardinality. -/
private def simplex_image_orderIso {Δ Γ : SimplexCategory} (θ : Δ ⟶ Γ) :
    Fin (simplex_image_card θ + 1) ≃o Set.range θ.toOrderHom :=
  Fintype.orderIsoFinOfCardEq (Set.range θ.toOrderHom) (simplex_image_card_succ θ)

/-- Helper for Lemma 14.21.11: every simplex morphism factors through the top simplex on its
image by a surjective map. -/
private def simplex_epi_factor {Δ Γ : SimplexCategory} (θ : Δ ⟶ Γ) :
    Δ ⟶ SimplexCategory.mk (simplex_image_card θ) :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ (simplex_image_orderIso θ).symm ⟨θ.toOrderHom i, ⟨i, rfl⟩⟩
      monotone' := by
        intro i j hij
        exact (simplex_image_orderIso θ).symm.monotone (θ.toOrderHom.monotone hij) }

/-- Helper for Lemma 14.21.11: the image factorization also has a canonical monotone inclusion of
the image simplex into the codomain simplex. -/
private def simplex_mono_factor {Δ Γ : SimplexCategory} (θ : Δ ⟶ Γ) :
    SimplexCategory.mk (simplex_image_card θ) ⟶ Γ :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ (simplex_image_orderIso θ i).1
      monotone' := by
        intro i j hij
        exact (simplex_image_orderIso θ).monotone hij }

/-- Helper for Lemma 14.21.11: the surjective image map followed by the canonical inclusion
recovers the original simplex morphism. -/
private theorem simplex_epi_factor_comp_mono {Δ Γ : SimplexCategory} (θ : Δ ⟶ Γ) :
    simplex_epi_factor θ ≫ simplex_mono_factor θ = θ := by
  -- Both composites evaluate to the original monotone map, now viewed through the chosen image
  -- order isomorphism.
  apply SimplexCategory.Hom.ext
  ext i
  simp [simplex_epi_factor, simplex_mono_factor]

/-- Helper for Lemma 14.21.11: the first map in the image factorization is an epimorphism, because
it is surjective onto the chosen finite image simplex. -/
private instance simplex_epi_factor_epi {Δ Γ : SimplexCategory} (θ : Δ ⟶ Γ) :
    Epi (simplex_epi_factor θ) := by
  rw [SimplexCategory.epi_iff_surjective]
  intro y
  let y' : Set.range θ.toOrderHom := simplex_image_orderIso θ y
  rcases y'.2 with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply (simplex_image_orderIso θ).injective
  simp [simplex_epi_factor, y', hx]

/-- Helper for Lemma 14.21.11: the image simplex of a map into a truncated simplex still lies in
the same truncation range. -/
private theorem simplex_image_card_le_of_truncated
    {n : ℕ} {Δ : SimplexCategory} (Γ : SimplexCategory.Truncated n)
    (θ : Δ ⟶ Γ.obj) :
    simplex_image_card θ ≤ n := by
  -- The chosen image embeds into `Γ`, so its cardinality is bounded by the codomain cardinality.
  have hcard :
      Fintype.card (Set.range θ.toOrderHom) ≤ Fintype.card (Fin (Γ.obj.len + 1)) :=
    Fintype.card_le_of_injective (fun x ↦ x.1) (fun x y h ↦ Subtype.ext h)
  have hcod : Γ.obj.len ≤ n := Γ.property
  rw [simplex_image_card_succ θ, Fintype.card_fin] at hcard
  omega

/-- Helper for Lemma 14.21.11: every costructured-arrow object over `Δ` maps to the surjective
representative obtained from the image factorization of its simplex map. -/
private def simplex_costructured_arrow_image_representative
    {n : ℕ} {Δ : SimplexCategory}
    (A : CostructuredArrow (SimplexCategory.Truncated.inclusion n).op (op Δ)) :
    CostructuredArrow (SimplexCategory.Truncated.inclusion n).op (op Δ) := by
  let θ : Δ ⟶ A.left.unop.obj := by
    simpa using A.hom.unop
  let m := simplex_image_card θ
  have hm : m ≤ n := simplex_image_card_le_of_truncated A.left.unop θ
  let Tleft : SimplexCategory.Truncated n := ⟨SimplexCategory.mk m, hm⟩
  exact
    CostructuredArrow.mk
      (show (SimplexCategory.Truncated.inclusion n).op.obj (op Tleft) ⟶ op Δ from
        (simplex_epi_factor θ).op)

/-- Helper for Lemma 14.21.11: the canonical image representative comes with the evident map from
the original costructured-arrow object, induced by the mono side of the image factorization. -/
private def simplex_costructured_arrow_to_image_representative
    {n : ℕ} {Δ : SimplexCategory}
    (A : CostructuredArrow (SimplexCategory.Truncated.inclusion n).op (op Δ)) :
    A ⟶ simplex_costructured_arrow_image_representative A := by
  let θ : Δ ⟶ A.left.unop.obj := by
    simpa using A.hom.unop
  let β : SimplexCategory.mk (simplex_image_card θ) ⟶ A.left.unop.obj := simplex_mono_factor θ
  let βTr : ⟨SimplexCategory.mk (simplex_image_card θ),
      simplex_image_card_le_of_truncated A.left.unop θ⟩ ⟶ A.left.unop :=
    CategoryTheory.ObjectProperty.homMk β
  have hβ :
      (SimplexCategory.Truncated.inclusion n).op.map βTr.op ≫
          (simplex_costructured_arrow_image_representative A).hom =
        A.hom := by
    -- Opposing the image factorization identity gives exactly the commutative square required for
    -- the canonical map into the image representative.
    simpa [simplex_costructured_arrow_image_representative, θ, βTr] using
      congrArg Quiver.Hom.op (simplex_epi_factor_comp_mono θ)
  exact CostructuredArrow.homMk βTr.op hβ

/-- Helper for Lemma 14.21.11: the canonical map into the image representative is unique. This is
the first terminality-shaped fragment needed for the later componentwise colimit reduction. -/
private theorem simplex_costructured_arrow_to_image_representative_subsingleton
    {n : ℕ} {Δ : SimplexCategory}
    (A : CostructuredArrow (SimplexCategory.Truncated.inclusion n).op (op Δ)) :
    Subsingleton (A ⟶ simplex_costructured_arrow_image_representative A) := by
  let θ : Δ ⟶ A.left.unop.obj := by
    simpa using A.hom.unop
  haveI : Epi ((simplex_costructured_arrow_image_representative A).hom.unop) := by
    simpa [simplex_costructured_arrow_image_representative, θ] using
      (inferInstance : Epi (simplex_epi_factor θ))
  refine ⟨fun f g ↦ ?_⟩
  apply CostructuredArrow.hom_ext
  have hf :
      (simplex_costructured_arrow_image_representative A).hom.unop ≫
          f.left.unop.hom =
        A.hom.unop := by
    simpa using congrArg Quiver.Hom.unop (CostructuredArrow.w f)
  have hg :
      (simplex_costructured_arrow_image_representative A).hom.unop ≫
          g.left.unop.hom =
        A.hom.unop := by
    simpa using congrArg Quiver.Hom.unop (CostructuredArrow.w g)
  have hcancel :
      f.left.unop.hom = g.left.unop.hom := by
    apply (cancel_epi ((simplex_costructured_arrow_image_representative A).hom.unop)).1
    exact hf.trans hg.symm
  apply Quiver.Hom.unop_inj
  apply CategoryTheory.ObjectProperty.hom_ext
  exact hcancel

/-- Helper for Lemma 14.21.11: every costructured-arrow object over `Δ` maps to its canonical
image representative. -/
private theorem simplex_costructured_arrow_factors_to_epi_representative
    {n : ℕ} {Δ : SimplexCategory}
    (A : CostructuredArrow (SimplexCategory.Truncated.inclusion n).op (op Δ)) :
    ∃ T : CostructuredArrow (SimplexCategory.Truncated.inclusion n).op (op Δ), Nonempty (A ⟶ T) := by
  exact
    ⟨simplex_costructured_arrow_image_representative A,
      ⟨simplex_costructured_arrow_to_image_representative A⟩⟩

/-- Helper for Lemma 14.21.11: postcomposing a simplex map with an epimorphism does not change its
set-theoretic image. -/
private theorem simplex_range_comp_eq_range_of_epi
    {Δ T A : SimplexCategory} (ε : Δ ⟶ T) [Epi ε] (β : T ⟶ A) :
    Set.range (ε ≫ β).toOrderHom = Set.range β.toOrderHom := by
  have hεsurj : Function.Surjective ε.toOrderHom := by
    have hεepi : Epi ε := inferInstance
    rw [SimplexCategory.epi_iff_surjective] at hεepi
    exact hεepi
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨ε.toOrderHom x, rfl⟩
  · rintro ⟨t, rfl⟩
    rcases hεsurj t with ⟨x, rfl⟩
    exact ⟨x, rfl⟩

/-- Helper for Lemma 14.21.11: if `ε : Δ ⟶ T` is epi, then every map `β : T ⟶ A` factors through
the canonical image simplex of the composite `ε ≫ β`. -/
private theorem simplex_epi_desc_to_image_factor
    {Δ T A : SimplexCategory} (ε : Δ ⟶ T) [Epi ε] (β : T ⟶ A) :
    ∃ g : T ⟶ SimplexCategory.mk (simplex_image_card (ε ≫ β)),
      ε ≫ g = simplex_epi_factor (ε ≫ β) ∧
        g ≫ simplex_mono_factor (ε ≫ β) = β := by
  -- TODO: construct the factor map by sending `t : T` to the point of the chosen image simplex
  -- corresponding to `β t`; the remaining work is to package the resulting transport across the
  -- equality `range (ε ≫ β) = range β` without triggering the current dependent-cast timeout.
  sorry

/-- Helper for Lemma 14.21.11: every morphism from `A` to an epi target factors through the
canonical image representative of `A`. This is the source-faithful rigidity statement behind the
eventual pointwise colimit reduction. -/
private theorem simplex_costructured_arrow_image_representative_to_epi_target
    {n : ℕ} {Δ : SimplexCategory}
    (A T : CostructuredArrow (SimplexCategory.Truncated.inclusion n).op (op Δ))
    [Epi T.hom.unop] (f : A ⟶ T) :
    ∃ g : simplex_costructured_arrow_image_representative A ⟶ T,
      simplex_costructured_arrow_to_image_representative A ≫ g = f := by
  -- TODO: apply `simplex_epi_desc_to_image_factor` to the underlying simplex map
  -- `f.left.unop.hom : T.left.unop.obj ⟶ A.left.unop.obj`, then package the resulting factor map
  -- as a morphism `simplex_costructured_arrow_image_representative A ⟶ T`; the remaining blocker
  -- is the transport between the two image-card codomains after rewriting by `CostructuredArrow.w f`.
  sorry

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

/- The verified `coskAdj`/`skAdj` prefix still needs the existence of `Truncated.sk n` on the
ambient category. This helper remains a scoped placeholder while the proof is being rerouted away
from the false generic pointwise-left-Kan computation. -/
private theorem simplexTruncatedInclusion_hasPointwiseLeftKanExtension_aux
    [HasFiniteCoproducts C] (n : ℕ) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion n).op.HasPointwiseLeftKanExtension F := by
  -- TODO: the current file still uses `skAdj n` on `C`, so we retain this placeholder until the
  -- remaining source-faithful bridge eliminates the generic left-Kan dependency entirely.
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

/-- Helper for Lemma 14.21.11: finite coproducts provide the standard-simplex-indexed coproducts
needed by `stdSimplexProductHomEquiv`. -/
private instance stdSimplex_hasCoproducts [HasFiniteCoproducts C] (k : ℕ) (X : C) :
    ∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : (Δ[k] : SSet.{w}).obj Δ ↦ X) := by
  intro Δ
  letI : Nonempty ((Δ[k] : SSet.{w}).obj Δ) := ⟨SSet.stdSimplex.const k 0 Δ⟩
  infer_instance

/-- The simplicial set `skₙ Δ[n + 1]` has a `0`-simplex. -/
private instance sk_stdSimplex_succ_objZero_nonempty (n : ℕ) :
    Nonempty (((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) _⦋0⦌) := by
  let x : ((Δ[n + 1] : SSet.{w}).skeleton (n + 1) : SSet.{w}) _⦋0⦌ :=
    ⟨obj₀Equiv.symm 0, by
      rw [(Δ[n + 1] : SSet.{w}).skeleton_obj_eq_top
        (Nat.lt_succ_of_le (show 0 ≤ n by simp))]
      simp⟩
  exact ⟨(truncatedSkeletonIsoSkeleton n (Δ[n + 1] : SSet.{w})).inv.app _ x⟩

/-- Helper for Lemma 14.21.11: a finite nonempty family admits a coproduct once finite coproducts
exist in the ambient category. -/
private theorem finite_nonempty_hasCoproduct {ι : Type w} [Finite ι] [Nonempty ι] (f : ι → C)
    [HasFiniteCoproducts C] : HasCoproduct f := by
  classical
  rcases Finite.exists_equiv_fin ι with ⟨m, ⟨e⟩⟩
  cases m with
  | zero =>
      exfalso
      exact Fin.elim0 (e (Classical.choice inferInstance))
  | succ m =>
      let g : Fin (m + 1) → C := fun j ↦ f (e.symm j)
      haveI : HasCoproduct g := by
        change HasColimit (Discrete.functor g)
        letI : HasColimitsOfShape (Discrete (Fin (m + 1))) C :=
          HasFiniteCoproducts.out (C := C) (m + 1)
        infer_instance
      exact hasCoproduct_of_equiv_of_iso g f e (fun j ↦ eqToIso (by simp [g]))

/-- Helper for Lemma 14.21.11: the skeletal standard simplex carries the degreewise coproducts
needed for copowers with a constant simplicial object. -/
private instance truncated_stdSimplex_succ_sk_hasCoproducts [HasFiniteCoproducts C]
    (n : ℕ) (X : C) :
    ∀ Δ : SimplexCategoryᵒᵖ,
      HasCoproduct
        (fun _ :
          (((SSet.sk n).obj (Δ[n + 1] : SSet.{w})).obj Δ) ↦
            ((const C).obj X).obj Δ) := by
  let U : SSet.{w} := (SSet.sk n).obj (Δ[n + 1] : SSet.{w})
  -- The skeletal standard simplex is finite and has a `0`-simplex, so the generic coproduct
  -- owner for simplicial copowers applies to the constant simplicial object on `X`.
  change ∀ Δ : SimplexCategoryᵒᵖ, HasCoproduct (fun _ : U.obj Δ ↦ X)
  letI : U.Finite := sk_stdSimplex_succ_finite n
  letI : Nonempty (U _⦋0⦌) := sk_stdSimplex_succ_objZero_nonempty n
  intro Δ
  letI : Finite (U.obj Δ) := by infer_instance
  letI : Nonempty (U.obj Δ) := nonempty_obj_of_nonempty_zero U Δ
  exact finite_nonempty_hasCoproduct (C := C) (fun _ : U.obj Δ ↦ X)

section Comparison

variable [HasFiniteCoproducts C] [HasFiniteLimits C]
variable (n : ℕ) (V : SimplicialObject C)

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

/-- Helper for Lemma 14.21.11: reindexing a constant coproduct family along an equivalence of
indexing types gives the canonical coproduct isomorphism. -/
private noncomputable def coproduct_reindex_constant_hom
    {α β : Type w} (e : α ≃ β) (Y : C)
    [HasCoproduct (fun _ : α ↦ Y)]
    [HasCoproduct (fun _ : β ↦ Y)] :
    (∐ fun _ : α ↦ Y) ⟶ (∐ fun _ : β ↦ Y) :=
  Sigma.map' e (fun _ ↦ 𝟙 Y)

/-- Helper for Lemma 14.21.11: the inverse reindexing morphism for a constant coproduct family. -/
private noncomputable def coproduct_reindex_constant_inv
    {α β : Type w} (e : α ≃ β) (Y : C)
    [HasCoproduct (fun _ : α ↦ Y)]
    [HasCoproduct (fun _ : β ↦ Y)] :
    (∐ fun _ : β ↦ Y) ⟶ (∐ fun _ : α ↦ Y) :=
  Sigma.map' e.symm (fun _ ↦ 𝟙 Y)

/-- Helper for Lemma 14.21.11: reindexing along an equivalence and then back is the identity on
the source constant coproduct family. -/
private theorem coproduct_reindex_constant_hom_inv_id
    {α β : Type w} (e : α ≃ β) (Y : C)
    [HasCoproduct (fun _ : α ↦ Y)]
    [HasCoproduct (fun _ : β ↦ Y)] :
    coproduct_reindex_constant_hom (e := e) Y ≫
        coproduct_reindex_constant_inv (e := e) Y =
      𝟙 (∐ fun _ : α ↦ Y) := by
  -- Compare on each coproduct summand and use the left inverse law for `e`.
  apply Limits.Sigma.hom_ext
  intro a
  calc
    Sigma.ι (fun _ : α ↦ Y) a ≫
        coproduct_reindex_constant_hom (e := e) Y ≫
        coproduct_reindex_constant_inv (e := e) Y =
      Sigma.ι (fun _ : β ↦ Y) (e a) ≫
        coproduct_reindex_constant_inv (e := e) Y := by
          simpa [coproduct_reindex_constant_hom, Category.assoc] using
            congrArg
              (fun k ↦ k ≫ coproduct_reindex_constant_inv (e := e) Y)
              (Sigma.ι_comp_map' (p := e) (q := fun _ : α ↦ 𝟙 Y) a)
    _ = Sigma.ι (fun _ : α ↦ Y) (e.symm (e a)) := by
          simpa [coproduct_reindex_constant_inv, Category.assoc] using
            (Sigma.ι_comp_map' (p := e.symm) (q := fun _ : β ↦ 𝟙 Y) (e a))
    _ = Sigma.ι (fun _ : α ↦ Y) a ≫ 𝟙 (∐ fun _ : α ↦ Y) := by simp

/-- Helper for Lemma 14.21.11: reindexing along an equivalence and then back is the identity on
the target constant coproduct family. -/
private theorem coproduct_reindex_constant_inv_hom_id
    {α β : Type w} (e : α ≃ β) (Y : C)
    [HasCoproduct (fun _ : α ↦ Y)]
    [HasCoproduct (fun _ : β ↦ Y)] :
    coproduct_reindex_constant_inv (e := e) Y ≫
        coproduct_reindex_constant_hom (e := e) Y =
      𝟙 (∐ fun _ : β ↦ Y) := by
  -- The symmetric summandwise calculation uses the right inverse law for `e`.
  apply Limits.Sigma.hom_ext
  intro b
  calc
    Sigma.ι (fun _ : β ↦ Y) b ≫
        coproduct_reindex_constant_inv (e := e) Y ≫
        coproduct_reindex_constant_hom (e := e) Y =
      Sigma.ι (fun _ : α ↦ Y) (e.symm b) ≫
        coproduct_reindex_constant_hom (e := e) Y := by
          simpa [coproduct_reindex_constant_inv, Category.assoc] using
            congrArg
              (fun k ↦ k ≫ coproduct_reindex_constant_hom (e := e) Y)
              (Sigma.ι_comp_map' (p := e.symm) (q := fun _ : β ↦ 𝟙 Y) b)
    _ = Sigma.ι (fun _ : β ↦ Y) (e (e.symm b)) := by
          simpa [coproduct_reindex_constant_hom, Category.assoc] using
            (Sigma.ι_comp_map' (p := e) (q := fun _ : α ↦ 𝟙 Y) (e.symm b))
    _ = Sigma.ι (fun _ : β ↦ Y) b ≫ 𝟙 (∐ fun _ : β ↦ Y) := by simp

/-- Helper for Lemma 14.21.11: the canonical isomorphism between constant coproducts indexed by
equivalent types. -/
private noncomputable def coproduct_reindex_constant_iso
    {α β : Type w} (e : α ≃ β) (Y : C)
    [HasCoproduct (fun _ : α ↦ Y)]
    [HasCoproduct (fun _ : β ↦ Y)] :
    (∐ fun _ : α ↦ Y) ≅ (∐ fun _ : β ↦ Y) :=
  { hom := coproduct_reindex_constant_hom (e := e) Y
    inv := coproduct_reindex_constant_inv (e := e) Y
    hom_inv_id := coproduct_reindex_constant_hom_inv_id (e := e) Y
    inv_hom_id := coproduct_reindex_constant_inv_hom_id (e := e) Y }

/-- Helper for Lemma 14.21.11: in degrees `i ≤ n`, the counit from `skₙ Δ[n + 1]` to `Δ[n + 1]`
is an isomorphism. -/
private theorem sk_stdSimplex_succ_counit_app_isIso_of_le
    (n : ℕ) {i : ℕ} (hi : i ≤ n) :
    IsIso (((SSet.skAdj n).counit.app (Δ[n + 1] : SSet.{w})).app (op ⦋i⦌)) := by
  let ε : (SSet.sk n).obj (Δ[n + 1] : SSet.{w}) ⟶ (Δ[n + 1] : SSet.{w}) :=
    (SSet.skAdj n).counit.app (Δ[n + 1] : SSet.{w})
  let i' : SimplexCategory.Truncated n := ⟨SimplexCategory.mk i, hi⟩
  -- Truncating the counit and using the right triangle identifies it with the inverse of the
  -- unit isomorphism on the truncated standard simplex.
  haveI : IsIso ((SSet.skAdj n).unit.app ((SSet.truncation n).obj (Δ[n + 1] : SSet.{w}))) := by
    infer_instance
  haveI : IsIso ((SSet.truncation n).map ε) := by
    exact isIso_of_hom_comp_eq_id
      ((SSet.skAdj n).unit.app ((SSet.truncation n).obj (Δ[n + 1] : SSet.{w})))
      ((SSet.skAdj n).right_triangle_components (Δ[n + 1] : SSet.{w}))
  simpa [ε] using
    ((NatTrans.isIso_iff_isIso_app ((SSet.truncation n).map ε)).1 inferInstance (op i'))

/-- Helper for Lemma 14.21.11: in degree `i ≤ n`, the counit component
`(skₙ Δ[n + 1])_i ≅ Δ[n + 1]_i` yields the expected equivalence of indexing sets. -/
private theorem truncated_stdSimplex_succ_degree_equiv_exists
    {i : ℕ} (hi : i ≤ n) :
    Nonempty ((((SSet.sk n).obj (Δ[n + 1] : SSet.{w})).obj (op ⦋i⦌)) ≃
      ((Δ[n + 1] : SSet.{w}).obj (op ⦋i⦌))) := by
  let ε : (SSet.sk n).obj (Δ[n + 1] : SSet.{w}) ⟶ (Δ[n + 1] : SSet.{w}) :=
    (SSet.skAdj n).counit.app (Δ[n + 1] : SSet.{w})
  -- The degreewise counit is an isomorphism in the truncated range, so it determines an
  -- equivalence of indexing sets for the constant coproduct families.
  haveI : IsIso (ε.app (op ⦋i⦌)) := sk_stdSimplex_succ_counit_app_isIso_of_le n hi
  exact ⟨(asIso (ε.app (op ⦋i⦌))).toEquiv⟩

/-- Helper for Lemma 14.21.11: after isolating the source comparison as a natural isomorphism,
the bridge itself is the formal adjunction isomorphism from `skAdj n`, whiskered by the copower
functor in the object variable. -/
private noncomputable def truncated_stdSimplex_succ_bridge_iso :
    truncated_stdSimplex_succ_truncation_hom_presheaf.{w, u, v} (C := C) n V ≅
      ((const C).op ⋙ simplicialHomPresheaf ((SSet.sk n).obj (Δ[n + 1] : SSet.{w})) V) := by
  -- Route correction: the direct `skAdj n` bridge on `C` still lands in
  -- `skₙ(truncationₙ(skₙ Δ[n + 1] × const X))`, so one still needs a source-faithful comparison
  -- from that object to `skₙ Δ[n + 1] × const X`. The remaining blocker is to package the
  -- degreewise counit isomorphisms `sk_stdSimplex_succ_counit_app_isIso_of_le` together with
  -- `coproduct_reindex_constant_iso` into a natural simplicial-object comparison that matches the
  -- actual `simplicialCopowerIndexHom` source map.
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
