import Mathlib
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_14_19_11 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 14.19.11:
- primary domain: simplicial-object truncation/coskeleton adjunctions under weakened limit
  hypotheses;
- sampled owner declarations:
  `SimplexCategory.Truncated.initial_inclusion`,
  `Functor.final_op_of_initial`,
  `truncation`,
  `Truncated.cosk`,
  `coskAdj`;
- best owner abstraction: the source-facing remark about `cosk_k` for `k > 0` should be bridged to
  the owner-level Kan-extension instance making `Truncated.cosk k` and `coskAdj k` available under
  `[HasFiniteConnectedLimits C]`, with the connectedness of the matching-index categories supplied
  by the canonical owner `SimplexCategory.Truncated.initial_inclusion`;
- primitive data: the truncation level `k`, the positivity hypothesis `0 < k`, and the ambient
  category together with its relevant limit owner (`HasBinaryProducts` for `k = 0`,
  `HasFiniteConnectedLimits` for `k > 0`);
- derived API: the source-facing existence statement for `cosk₀`, and for `k > 0` the canonical
  owner declarations `Truncated.cosk k` and `coskAdj k`.

Source/core/bridge triage:
- `source-facing`: the source's two existence statements for `cosk₀` and `cosk_k`;
- `core/canonical`: `truncation`, `Truncated.cosk`, and `coskAdj`;
- `bridge/view`: Example 14.19.1 for `k = 0`, and the finite-connected-limit bridge below giving
  the right Kan extensions needed for `Truncated.cosk k` when `0 < k`, reusing the canonical
  matching-index owner `matchingIndex k n` from `Lemma_14_19_2` and the upstream initiality owner
  `SimplexCategory.Truncated.initial_inclusion`. -/

/-- If `k > 0` and `C` has finite connected limits, then the structured-arrow indexing categories
for the degreewise construction of `cosk_k` have limits. Hence the right Kan extensions defining
`Truncated.cosk k` exist under the weaker hypothesis `[HasFiniteConnectedLimits C]`. -/
instance simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits
    (k : ℕ) (hk : 0 < k) [HasFiniteConnectedLimits C]
    (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F := by
  intro Y
  cases Y with
  | op Y =>
      change HasLimit
        (StructuredArrow.proj (op Y) (SimplexCategory.Truncated.inclusion k).op ⋙ F)
      letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
      letI : FinCategory (matchingIndex k Y.len) := inferInstance
      letI : IsConnected (matchingIndex k Y.len) := inferInstance
      infer_instance

-- Proof sketch: Example 14.19.1 constructs `cosk₀` from the explicit self-product model
-- `X ↦ (n ↦ X^(n + 1))`. That source-facing construction is kept here as the `k = 0` companion.
/-- If `C` has binary products, then the `0`-truncation functor has a right adjoint, i.e. `cosk₀`
exists. -/
theorem truncation_zero_isLeftAdjoint_of_hasBinaryProducts [HasBinaryProducts C] :
    ((SimplicialObject.truncation 0 : SimplicialObject C ⥤ SimplicialObject.Truncated C 0)).IsLeftAdjoint := sorry

section Positive

variable (k : ℕ) (hk : 0 < k) [HasFiniteConnectedLimits C]

local instance :
    ∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
  fun F ↦ simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F

/- For `k > 0`, the weaker finite-connected-limit hypothesis now makes the canonical owner
`Truncated.cosk k` available directly. -/
#check Truncated.cosk k

/- Remark 14.19.11 for `k > 0`: under `[HasFiniteConnectedLimits C]`, the canonical adjunction
`truncation k ⊣ Truncated.cosk k` is available directly. -/
#check (coskAdj k).isLeftAdjoint

end Positive

end CategoryTheory

/-! ### Lemma_14_19_12 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}
variable [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]

/- Domain-style sampling for Lemma 14.19.12:
- primary domain: binary-product comparison morphisms for right adjoints in simplicial-object
  truncation/coskeleton theory;
- sampled owner API:
  `coskAdj`,
  `Adjunction.isRightAdjoint`,
  `PreservesLimitPair.iso`,
  `PreservesLimitPair.iso_hom`;
- best owner abstraction: the canonical comparison isomorphism is the binary-product owner
  `PreservesLimitPair.iso (Truncated.cosk n) U V`, and the source-facing comparison morphism is its
  hom, identified by `PreservesLimitPair.iso_hom`;
- source/core/bridge triage:
  `source-facing`: the map `cosk_n (U × V) ⟶ cosk_n U × cosk_n V`;
  `core/canonical`: `PreservesLimitPair.iso (Truncated.cosk n) U V`;
  `bridge/view`: the right-adjoint structure on `Truncated.cosk n` coming from `coskAdj n`.

Primitive data are only the truncated simplicial objects `U`, `V`, their binary product, and the
right Kan extension hypotheses defining `Truncated.cosk n`. The comparison map itself is derived
API from the owner isomorphism `PreservesLimitPair.iso`, so this item should recall that owner and
its canonical hom description rather than introduce a parallel local theorem. -/
noncomputable local instance :
    ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C)).IsRightAdjoint :=
  by
    simpa using (coskAdj n).isRightAdjoint

variable (U V : SimplicialObject.Truncated C n)
variable [HasBinaryProduct U V]

recall PreservesLimitPair.iso
recall PreservesLimitPair.iso_hom

/- Lemma 14.19.12: if the binary product `U × V` exists in `n`-truncated simplicial objects, then
the canonical comparison map `cosk_n (U × V) ⟶ cosk_n U × cosk_n V` is an isomorphism. The owner
object is the standard binary-product comparison isomorphism for the right adjoint
`Truncated.cosk n`, whose hom is definitionally `prodComparison (Truncated.cosk n) U V`. -/
#check PreservesLimitPair.iso (Truncated.cosk n) U V

end CategoryTheory

/-! ### Lemma_14_19_13 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}
variable [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion n).op.HasRightKanExtension F]
variable {U V W : SimplicialObject.Truncated C n}
variable (f : U ⟶ V) (g : W ⟶ V)
variable [HasPullback f g]

/- Domain-style sampling for Lemma 14.19.13:
- primary domain: pullback-comparison isomorphisms for right adjoints in simplicial-object
  truncation/coskeleton theory;
- sampled owner API:
  `Definition_14_7_1`'s use of `PreservesPullback.iso ((evaluation _ _).obj n) a b`,
  `coskAdj`,
  `PreservesPullback.iso`,
  `PreservesPullback.iso_hom`;
- best owner abstraction: the canonical comparison isomorphism is
  `PreservesPullback.iso (Truncated.cosk n) f g`, whose hom is definitionally
  `pullbackComparison (Truncated.cosk n) f g`;
- source/core/bridge triage:
  `source-facing`: the map `cosk_n (U ×[V] W) ⟶ cosk_n U ×[cosk_n V] cosk_n W`;
  `core/canonical`: `PreservesPullback.iso (Truncated.cosk n) f g`;
  `bridge/view`: the right-adjoint structure on `Truncated.cosk n` coming from `coskAdj n`.

Primitive data are only the truncated simplicial objects, the morphisms `f`, `g`, and the source
pullback assumption `[HasPullback f g]`. The target pullback is derived API from right-adjoint
preservation via `hasPullback_of_preservesPullback`, so this file should recall the canonical owner
rather than keep a parallel theorem with the same content. -/
noncomputable local instance :
    ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C)).IsRightAdjoint :=
  by
  simpa using (coskAdj n).isRightAdjoint

attribute [local instance] hasPullback_of_preservesPullback

recall PreservesPullback.iso
recall PreservesPullback.iso_hom

/- Lemma 14.19.13: if the pullback `U ×[V] W` exists in `n`-truncated simplicial objects, then the
canonical comparison map to `cosk_n U ×[cosk_n V] cosk_n W` is an isomorphism. The target
pullback exists canonically because the right adjoint `Truncated.cosk n` preserves pullbacks, so
the owner object is the standard pullback-comparison isomorphism and the source-facing comparison
map is its canonical hom. -/
#check (PreservesPullback.iso (Truncated.cosk n) f g :
  (Truncated.cosk n).obj (pullback f g) ≅
    pullback ((Truncated.cosk n).map f) ((Truncated.cosk n).map g))

#check (PreservesPullback.iso_hom (Truncated.cosk n) f g :
  (PreservesPullback.iso (Truncated.cosk n) f g).hom =
    pullbackComparison (Truncated.cosk n) f g)

end CategoryTheory

/-! ### Lemma_14_19_14 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Over

variable {X : C}

/- Domain-style sampling for Lemma 14.19.14:
- primary domain: simplicial `k`-coskeleta as right Kan extensions, and their compatibility with
  slice forgetful functors;
- sampled owner declarations:
  `Truncated.cosk`,
  `Functor.ranCompIsoOfPreserves`,
  `Over.preservesLimitsOfShape_forget_of_isConnected`,
  `simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits`;
- best owner abstraction: the canonical comparison isomorphism
  `(Over.forget X).ranCompIsoOfPreserves ((SimplexCategory.Truncated.inclusion k).op)`, with the
  source-facing finite-connected-limit and `0 < k` hypotheses supplying its Kan-extension and
  preservation instances;
- primitive data: the slice object `X`, the truncation level `k`, the positivity hypothesis
  `0 < k`, and finite connected limits in `C`;
- derived API: the pointwise right-Kan-extension comparison for `forget X`, and from it the
  owner-level preservation instance and induced natural isomorphism showing that `Over.forget X`
  commutes with `Truncated.cosk k`.

Source/core/bridge triage:
- `source-facing`: the finite-connected-limits slice-category specialization saying that forgetting
  a `k`-coskeleton over `X` agrees with taking the `k`-coskeleton after forgetting to `C`;
- `core/canonical`: `Functor.ranCompIsoOfPreserves`;
- `bridge/view`: the positive-`k` Kan-extension existence bridge from
  `Remark_14_19_11`, the induced finite-connected-limits bridge for `Over X`, and the connected
  limit preservation of `Over.forget X`. -/

section Positive

variable (X) (k : ℕ) (hk : 0 < k) [HasFiniteConnectedLimits C]

local instance : HasFiniteConnectedLimits (Over X) where
  out J := by infer_instance

private noncomputable instance hasRightKanExtensionOver
    : ∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ Over X,
        (SimplexCategory.Truncated.inclusion k).op.HasRightKanExtension F :=
  fun F ↦ by
    letI : (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
      simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F
    exact Functor.HasRightKanExtension.mk _ <|
      Functor.pointwiseRightKanExtensionCounit _ F

private noncomputable instance hasRightKanExtensionBase :
    ∀ F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ C,
      (SimplexCategory.Truncated.inclusion k).op.HasRightKanExtension F :=
  fun F ↦ by
    letI : (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
      simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F
    exact Functor.HasRightKanExtension.mk _ <|
      Functor.pointwiseRightKanExtensionCounit _ F

private noncomputable instance forgetPreservesRightKanExtensions :
    (forget X).PreservesRightKanExtensions ((SimplexCategory.Truncated.inclusion k).op) :=
  fun F ↦ by
    letI : (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F :=
      simplexTruncatedInclusion_hasPointwiseRightKanExtension_of_finite_connected_limits k hk F
    letI :
        (forget X).PreservesPointwiseRightKanExtension F
          ((SimplexCategory.Truncated.inclusion k).op) := by
      intro Y
      cases Y with
      | op Y =>
          letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
          letI : FinCategory (matchingIndex k Y.len) := inferInstance
          letI : IsConnected (matchingIndex k Y.len) := inferInstance
          letI :
              PreservesLimit
                (StructuredArrow.proj (op Y) (SimplexCategory.Truncated.inclusion k).op ⋙ F)
                (forget X) :=
            inferInstance
          infer_instance
    infer_instance

/- Lemma 14.19.14: if `C` has finite connected limits and `0 < k`, then for every `k`-truncated
simplicial object over `X`, forgetting its canonical `k`-coskeleton agrees with taking the
canonical `k`-coskeleton after forgetting to `C`. This is the componentwise source-facing bridge
obtained by applying the owner isomorphism
`(forget X).ranCompIsoOfPreserves ((SimplexCategory.Truncated.inclusion k).op)` to `U` and
rewriting `ran` as `Truncated.cosk k`. -/
#check
  (letI := hasRightKanExtensionOver X k hk
   letI := hasRightKanExtensionBase k hk
   letI := forgetPreservesRightKanExtensions X k hk
   let f :
       ∀ U : SimplicialObject.Truncated (Over X) k,
         ((Truncated.cosk k).obj U) ⋙ forget X ≅
           (Truncated.cosk k).obj (U ⋙ forget X) :=
     ((forget X).ranCompIsoOfPreserves ((SimplexCategory.Truncated.inclusion k).op)).app
   f)

end Positive

end Over

end CategoryTheory

/-! ### Lemma_14_19_15 (from Chap14) -/
open CategoryTheory Simplicial
open CategoryTheory.SimplicialObject
open Opposite

/- Domain-style sampling for Lemma 14.19.15:
- primary domain: simplicial-set skeleton/coskeleton adjunctions and coskeletal simplicial sets;
- sampled owner-style declarations:
  `SimplexCategory.Truncated.matchingIndex`,
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.isCoskeletal_iff_isIso`,
  `SimplicialObject.isoCoskOfIsCoskeletal`,
  `stdSimplex.isoNerve`;
- best owner abstraction: `SimplicialObject.IsCoskeletal 1`, with the canonical comparison map
  owned by the adjunction unit `(coskAdj 1).unit.app (Δ[n] : SSet)`;
- source/core/bridge triage:
  `source-facing`: the statement that the canonical map `Δ[n] ⟶ cosk₁ sk₁ Δ[n]` is an
  isomorphism;
  `core/canonical`: the owner predicate `(Δ[n] : SSet).IsCoskeletal 1`;
  `bridge/view`: `SimplicialObject.isCoskeletal_iff_isIso`, which converts the owner predicate to
  the source-facing unit-isomorphism statement.

Primitive data are only the standard simplex `Δ[n]`; the comparison morphism is derived from the
adjunction owner. The file should therefore expose the owner-level coskeletality statement and keep
the unit-isomorphism theorem as a thin companion. -/

namespace CategoryTheory.Nerve

open CategoryTheory.Category Limits
open Functor StructuredArrow
open SSet SSet.Truncated
open SimplexCategory.Truncated.Hom
open SimplexCategory SimplexCategory.Truncated
open SimplicialObject.Truncated

universe v u

variable (C : Type u) [Category.{v} C] [Quiver.IsThin C]

namespace Pointwise

private abbrev strArrowMk {i n : ℕ} (φ : ⦋i⦌ ⟶ ⦋n⦌) (hi : i ≤ 1 := by omega) :
    matchingIndex 1 n :=
  ⟨⟨⟨⟩⟩, op (⟨⦋i⦌, hi⟩ : SimplexCategory.Truncated 1), φ.op⟩

private def conePath {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) : (nerve C).Path n where
  vertex i := s.π.app (strArrowMk (SimplexCategory.const _ _ i)) x
  arrow i := s.π.app (strArrowMk (SimplexCategory.mkOfSucc i)) x
  arrow_src i := by
    let α : strArrowMk (SimplexCategory.mkOfSucc i) ⟶
        strArrowMk (⦋0⦌.const ⦋n⦌ i.castSucc) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 1)).op
        (Quiver.Hom.unop_inj (by ext j; fin_cases j; rfl))
    simpa using congr_fun (s.w α) x
  arrow_tgt i := by
    let α : strArrowMk (SimplexCategory.mkOfSucc i) ⟶
        strArrowMk (⦋0⦌.const ⦋n⦌ i.succ) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 0)).op
        (Quiver.Hom.unop_inj (by ext j; fin_cases j; rfl))
    simpa using congr_fun (s.w α) x

private noncomputable def lift {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) : (nerve C) _⦋n⦌ :=
  (strictSegal C).spineToSimplex (conePath C s x)

omit [Quiver.IsThin C] in
private lemma fac_zero {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) (i : Fin (n + 1)) :
    (nerve C).map (SimplexCategory.const ⦋0⦌ ⦋n⦌ i).op (lift C s x) =
      s.π.app (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) x := by
  simpa [lift, conePath] using (strictSegal C).spineToSimplex_vertex i (conePath C s x)

private lemma fac_one {n : ℕ}
    (s : Cone (proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion 1).op ⋙
      (SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C))
    (x : s.pt) (φ : ⦋1⦌ ⟶ ⦋n⦌) :
    (nerve C).map φ.op (lift C s x) = s.π.app (strArrowMk φ) x := by
  apply nerve.ext_of_isThin
  ext j
  fin_cases j
  · have hφ : SimplexCategory.δ 1 ≫ φ = SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 0) := by
      ext k
      fin_cases k
      rfl
    let α : strArrowMk φ ⟶
        strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 0)) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 1)).op
        (Quiver.Hom.unop_inj (by ext k; fin_cases k; rfl))
    have hα :
        s.π.app (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 0))) x =
          (nerve C).map (SimplexCategory.δ 1).op (s.π.app (strArrowMk φ) x) := by
      simpa using (congr_fun (s.w α) x).symm
    have hsrc :
        (nerve C).δ 1 ((nerve C).map φ.op (lift C s x)) =
          (nerve C).δ 1 (s.π.app (strArrowMk φ) x) := by
      rw [SimplicialObject.δ_def, ← FunctorToTypes.map_comp_apply, ← op_comp, hφ]
      rw [fac_zero C s x (φ.toOrderHom 0), hα]
    simpa [nerveEquiv] using congrArg nerveEquiv hsrc
  · have hφ : SimplexCategory.δ 0 ≫ φ = SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 1) := by
      ext k
      fin_cases k
      rfl
    let α : strArrowMk φ ⟶
        strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 1)) :=
      StructuredArrow.homMk (tr (SimplexCategory.δ 0)).op
        (Quiver.Hom.unop_inj (by ext k; fin_cases k; rfl))
    have hα :
        s.π.app (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ (φ.toOrderHom 1))) x =
          (nerve C).map (SimplexCategory.δ 0).op (s.π.app (strArrowMk φ) x) := by
      simpa using (congr_fun (s.w α) x).symm
    have htgt :
        (nerve C).δ 0 ((nerve C).map φ.op (lift C s x)) =
          (nerve C).δ 0 (s.π.app (strArrowMk φ) x) := by
      rw [SimplicialObject.δ_def, ← FunctorToTypes.map_comp_apply, ← op_comp, hφ]
      rw [fac_zero C s x (φ.toOrderHom 1), hα]
    simpa [nerveEquiv] using congrArg nerveEquiv htgt

end Pointwise

open Pointwise in
private noncomputable def isPointwiseRightKanExtensionAt (n : ℕ) :
    (SSet.Truncated.rightExtensionInclusion (nerve C) 1).IsPointwiseRightKanExtensionAt ⟨⦋n⦌⟩ where
  lift s x := lift C s x
  fac s j := by
    ext x
    obtain ⟨⟨i, hi⟩, ⟨f : _ ⟶ _⟩, rfl⟩ := j.mk_surjective
    obtain ⟨i, rfl⟩ : ∃ m, ⦋m⦌ = i := ⟨_, i.mk_len⟩
    dsimp at hi ⊢
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    · have hf : f = SimplexCategory.const ⦋0⦌ ⦋n⦌ (f.toOrderHom 0) := by
        ext k
        fin_cases k
        rfl
      rw [hf]
      simpa using fac_zero C s x (f.toOrderHom 0)
    · simpa using fac_one C s x f
  uniq s m hm := by
    ext x
    apply (strictSegal C).spineInjective
    change (nerve C).spine n (m x) = (nerve C).spine n (lift C s x)
    dsimp [lift, conePath]
    rw [(strictSegal C).spine_spineToSimplex_apply]
    refine SSet.Path.ext ?_ ?_
    · funext i
      exact congr_fun (hm (strArrowMk (SimplexCategory.const ⦋0⦌ ⦋n⦌ i))) x
    · funext i
      exact congr_fun (hm (strArrowMk (SimplexCategory.mkOfSucc i))) x

private noncomputable def isPointwiseRightKanExtension :
    (SSet.Truncated.rightExtensionInclusion (nerve C) 1).IsPointwiseRightKanExtension :=
  fun Δ ↦ isPointwiseRightKanExtensionAt C Δ.unop.len

private theorem isRightKanExtension :
    (nerve C).IsRightKanExtension (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ nerve C)) :=
  RightExtension.IsPointwiseRightKanExtension.isRightKanExtension
    (isPointwiseRightKanExtension C)

/-- The nerve of a thin category is `1`-coskeletal. -/
instance : SimplicialObject.IsCoskeletal (nerve C) 1 where
  isRightKanExtension := isRightKanExtension C

end CategoryTheory.Nerve

-- Proof sketch: identify maps into `Δ[n]` with monotone maps into `Fin (n + 1)` via Yoneda, show
-- that such maps are determined by their values on vertices and that monotonicity is already forced
-- by the `1`-simplices, and conclude that `Δ[n]` is the right Kan extension of its `1`-truncation.
/-- The standard simplex `Δ[n]` is `1`-coskeletal. -/
theorem stdSimplex_isCoskeletal_one (n : ℕ) :
    (Δ[n] : SSet).IsCoskeletal 1 := by
  rw [SimplicialObject.isCoskeletal_iff]
  let e := SSet.stdSimplex.isoNerve n
  let e₁ := Functor.isoWhiskerLeft (SimplexCategory.Truncated.inclusion 1).op e
  let _ : (nerve (ULift (Fin (n + 1))) : SSet).IsCoskeletal 1 :=
    inferInstance
  exact
    (Functor.isRightKanExtension_iff_of_iso₂
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ (Δ[n] : SSet)))
      (𝟙 ((SimplexCategory.Truncated.inclusion 1).op ⋙ (nerve (ULift (Fin (n + 1))) : SSet)))
      e₁
      e
      (by simp [e₁])).2 inferInstance

/- Lemma 14.19.15: the canonical map `Δ[n] ⟶ cosk₁ sk₁ Δ[n]` is an isomorphism. Once
`stdSimplex_isCoskeletal_one n` is established, this is the canonical `IsIso` instance for the
unit of `coskAdj 1`. -/
theorem stdSimplex_cosk_unit_isIso (n : ℕ) :
    IsIso ((coskAdj 1).unit.app (Δ[n] : SSet)) := by
  exact (SimplicialObject.isCoskeletal_iff_isIso (Δ[n] : SSet) 1).1
    (stdSimplex_isCoskeletal_one n)
