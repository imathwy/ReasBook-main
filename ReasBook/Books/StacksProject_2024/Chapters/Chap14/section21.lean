import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_14_21_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory SimplexCategory.Truncated
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

section

/- Domain-style sampling for Lemma 14.21.1:
- primary domain: simplicial objects obtained by pointwise left Kan extension along the truncated
  simplex inclusion;
- sampled owner declarations:
  `Truncated.sk`,
  `Functor.leftKanExtensionObjIsoColimit`,
  `Functor.ι_leftKanExtensionObjIsoColimit_inv`,
  `Functor.ι_leftKanExtensionObjIsoColimit_hom`;
- best owner abstraction: the chapter-level owner for the source notion `i_{m!} U` is
  `Truncated.sk m`; the pointwise colimit comparison and its cocone-leg formulas
  are derived API from the canonical Kan-extension owner, so this file should reuse those owners
  directly rather than keep parallel local wrappers;
- primitive data: the truncated simplicial object `U` and the simplex `Δ`;
- derived API: the value of `((Truncated.sk m).obj U)` at `Δ`, together with the
  formulas describing how each indexing simplex contributes through the simplicial transition maps.

Source/core/bridge triage:
- `source-facing`: the Chapter 14 description of `i_{m!} U` by its degree objects and the maps
  induced by simplicial operators;
- `core/canonical`: the skeleton functor owner `Truncated.sk m`;
- `bridge/view`: the specialization of the pointwise Kan-extension colimit API to that owner. -/

variable {C : Type u} [Category.{v} C]
variable (m : ℕ)
variable [HasFiniteColimits C]

/- Companion owner recall: the pointwise description of a left Kan extension as a colimit is the
canonical declaration `Functor.leftKanExtensionObjIsoColimit`. -/
recall Functor.leftKanExtensionObjIsoColimit

variable (U : SimplicialObject.Truncated C m) (Δ : SimplexCategory)

/- Lemma 14.21.1: the value of the simplicial `m`-skeleton `i_{m!} U` at `Δ` is the canonical
colimit computing the left Kan extension along the truncated simplex inclusion. -/
#check
  ((Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Δ) :
    ((Truncated.sk m).obj U).obj (op Δ) ≅
      colimit (CostructuredArrow.proj (Truncated.inclusion m).op (op Δ) ⋙ U))

variable
    (g : CostructuredArrow (SimplexCategory.Truncated.inclusion m).op (op Δ))

/- Companion bridge recall: each cocone leg into that colimit is identified by the canonical
inverse comparison formula. -/
#check
  (((Truncated.inclusion m).op.ι_leftKanExtensionObjIsoColimit_inv U (op Δ) g) :
    colimit.ι (CostructuredArrow.proj (Truncated.inclusion m).op (op Δ) ⋙ U) g ≫
      ((Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Δ)).inv =
        (((Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left) ≫
          ((Truncated.sk m).obj U).map g.hom)

/- The forward cocone-leg formula is the corresponding canonical `hom` statement. -/
#check
  (((Truncated.inclusion m).op.ι_leftKanExtensionObjIsoColimit_hom U (op Δ) g) :
    (((Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left) ≫
        ((Truncated.sk m).obj U).map g.hom ≫
          ((Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Δ)).hom =
      colimit.ι (CostructuredArrow.proj (Truncated.inclusion m).op (op Δ) ⋙ U) g)

end

end CategoryTheory

/-! ### Lemma_14_21_2 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits Opposite
open SimplexCategory
open SimplexCategory.Truncated
open scoped SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.21.2:
- primary domain: pointwise colimit formulas for truncated simplicial objects, expressed through
  costructured-arrow indexing categories with a terminal object;
- sampled owner declarations:
  `CostructuredArrow.proj`,
  `CostructuredArrow.mkIdTerminal`,
  `coconeOfDiagramTerminal`,
  `colimitOfDiagramTerminal`;
- best owner abstraction: the canonical terminal-diagram colimit API applied to
  `CostructuredArrow.proj (inclusion m).op (op (mk n)) ⋙ U`;
- primitive data: the truncated simplicial object `U`, the degree `n`, the source-facing
  indexing diagram on `([n]/Δ)≤mᵒᵖ`, and the identity costructured arrow over `[n]`;
- derived API: the terminality witness from `mkIdTerminal`, together with the induced colimit
  witness and its `desc` formula.

Source/core/bridge triage:
- `source-facing`: the cocone computing the degree-`n` value of an `m`-truncated simplicial object
  from the costructured-arrow indexing category;
- `core/canonical`: `CostructuredArrow.mkIdTerminal`, `coconeOfDiagramTerminal`,
  `colimitOfDiagramTerminal`;
- `bridge/view`: the specialization below, with no extra public wrapper around the canonical
  terminal-diagram colimit API. -/

variable {m n : ℕ} (hn : n ≤ m) (U : SimplicialObject.Truncated C m)

/- The identity costructured arrow is terminal. -/
recall CostructuredArrow.mkIdTerminal

/- The terminal-indexed cocone and its colimit witness are the owner declarations. -/
recall coconeOfDiagramTerminal
recall colimitOfDiagramTerminal

/- Lemma 14.21.2: the cocone with vertex `U_n` induced by the identity simplex `[n] ⟶ [n]` is
the canonical specialization of `colimitOfDiagramTerminal` for the terminal object in the
costructured-arrow indexing category. -/
#check
  (by
    let Δ := (Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)
    let D := CostructuredArrow.proj (Truncated.inclusion m).op Δ ⋙ U
    let T :
        IsTerminal
          (CostructuredArrow.mk (𝟙 Δ) : CostructuredArrow (Truncated.inclusion m).op Δ) :=
      CostructuredArrow.mkIdTerminal
    exact
      (colimitOfDiagramTerminal T D :
        IsColimit (coconeOfDiagramTerminal T D)))

variable
    (s :
      Cocone
        (CostructuredArrow.proj (Truncated.inclusion m).op
          ((Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)) ⋙ U))

/- Companion recall: the `desc` morphism is definitionally evaluation at the identity simplex. -/
#check
  (by
    let Δ := (Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)
    let D := CostructuredArrow.proj (Truncated.inclusion m).op Δ ⋙ U
    let T :
        IsTerminal
          (CostructuredArrow.mk (𝟙 Δ) : CostructuredArrow (Truncated.inclusion m).op Δ) :=
      CostructuredArrow.mkIdTerminal
    change
      (colimitOfDiagramTerminal T D).desc s =
        s.ι.app (CostructuredArrow.mk (𝟙 Δ))
    rfl)

end

end CategoryTheory

/-! ### Lemma_14_21_3 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory SimplexCategory.Truncated

noncomputable section

universe u v

namespace CategoryTheory

/-
Domain-style sampling for Lemma 14.21.3:
- primary domain: the skeleton/truncation adjunction for simplicial objects, expressed via left
  Kan extension along `SimplexCategory.Truncated.inclusion`;
- sampled owner declarations:
  `SimplicialObject.Truncated.sk`,
  `skAdj`,
  `SimplicialObject.Truncated.sk_coreflective`,
  `Functor.HasPointwiseLeftKanExtension`;
- best owner abstraction: the mathlib owner `skAdj m` together with the canonical instance
  `IsIso (skAdj m).unit`;
- primitive data: only the `m`-truncated simplicial object `U`;
- derived API: the source-facing statement that the unit map
  `U ⟶ truncation m ((SimplicialObject.Truncated.sk m).obj U)` is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the Chapter 14 statement that the canonical comparison map from `U` to the
  truncation of its skeleton is an isomorphism;
- `core/canonical`: the unit of `skAdj m`, whose whole natural transformation is an isomorphism;
- `bridge/view`: the finite-category pointwise-left-Kan instance below, reusing the public
  finiteness owners from `Lemma_14_19_2`, which supplies the hypotheses needed to specialize the
  canonical owner statement. -/

private instance costructuredArrow_finite (m : ℕ) (Δ : SimplexCategory) :
    Finite (CostructuredArrow (Truncated.inclusion m).op (op Δ)) := by
  let e :
      (Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
        ((Truncated.inclusion m).op.obj X ⟶ op Δ)) ≃
        CostructuredArrow (Truncated.inclusion m).op (op Δ) :=
    { toFun := fun p ↦ CostructuredArrow.mk p.2
      invFun := fun A ↦ ⟨A.left, A.hom⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro A; cases A; rfl }
  exact Finite.of_equiv _ e

private instance costructuredArrow_hom_finite (m : ℕ) (Δ : SimplexCategory)
    (A B : CostructuredArrow (Truncated.inclusion m).op (op Δ)) :
    Finite (A ⟶ B) := by
  refine Finite.of_injective (fun f ↦ f.left) ?_
  intro f g h
  exact CostructuredArrow.hom_ext f g h

private instance costructuredArrow_finCategory (m : ℕ) (Δ : SimplexCategory) :
    FinCategory (CostructuredArrow (Truncated.inclusion m).op (op Δ)) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- The opposite inclusion of the `m`-truncated simplex category admits pointwise left Kan
extensions into any category with finite colimits. -/
instance simplexTruncatedInclusionOp_hasPointwiseLeftKanExtension
    {C : Type u} [Category.{v} C] [HasFiniteColimits C] (m : ℕ)
    (F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C) :
    (Truncated.inclusion m).op.HasPointwiseLeftKanExtension F := by
  intro Y
  cases Y with
  | op Y =>
      change HasColimit (CostructuredArrow.proj (Truncated.inclusion m).op (op Y) ⋙ F)
      letI : FinCategory
          (CostructuredArrow (Truncated.inclusion m).op (op Y)) :=
        costructuredArrow_finCategory m Y
      infer_instance

section

variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
variable (m : ℕ)

recall skAdj

/- Lemma 14.21.3: for an `m`-truncated simplicial object `U` in a category with finite colimits,
the canonical map `U ⟶ truncation m ((SimplicialObject.Truncated.sk m).obj U)`, namely the unit
of `skAdj m`, is an isomorphism. Mathlib provides the stronger natural statement that the whole
unit natural transformation is an isomorphism. -/
#check (inferInstance : IsIso (skAdj m).unit)

end

end CategoryTheory

/-! ### Lemma_14_21_4 (from Chap14) -/
open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

/- Domain-style sampling for Lemma 14.21.4:
- primary domain: simplicial-set skeletons, truncated skeleton adjunctions, and simplicial-set
  dimension bounds;
- sampled owner declarations:
  `SSet.skeleton`,
  `SSet.HasDimensionLT`,
  `SSet.HasDimensionLE`,
  `SSet.hasDimensionLT_iff_of_iso`,
  `truncatedSkeletonIsoSkeleton`;
- best owner abstraction: the canonical owner layer is the dimension predicate
  `SSet.HasDimensionLE`; the chapter bridge identifying `i_{m!} U` with the owner object
  `U.skeleton (m + 1)` is `truncatedSkeletonIsoSkeleton`;
- primitive data: only the truncated simplicial set `U`;
- derived API: the transported instance
  `((SSet.Truncated.sk m).obj U).HasDimensionLE m`, and the pointwise degree-`> m` degeneracy
  statement as a thin corollary.

Source/core/bridge triage:
- `source-facing`: the textbook claim that every simplex of `i_{m!} U` in degree `> m` is
  degenerate;
- `core/canonical`: the dimension bound `((SSet.Truncated.sk m).obj U).HasDimensionLE m`;
- `bridge/view`: the canonical identification of `i_{m!} U` with the simplicial
  `(m + 1)`-skeleton, used only to transport the owner-level instance. -/

-- Proof sketch: first identify `V := (SSet.Truncated.sk m).obj U` with `(SSet.sk m).obj V` by
-- applying `SSet.Truncated.sk m` to the canonical unit isomorphism
-- `U ≅ (SSet.truncation m).obj V`. Then compose with `truncatedSkeletonIsoSkeleton m V` to obtain
-- `V ≅ V.skeleton (m + 1)`, and transport the canonical owner instance
-- `((V.skeleton (m + 1) : SSet)).HasDimensionLT (m + 1)` across that isomorphism.
/-- The simplicial set `i_{m!} U = (SSet.Truncated.sk m).obj U` has dimension at most `m`. -/
instance (m : ℕ) (U : SSet.Truncated m) :
    ((SSet.Truncated.sk m).obj U).HasDimensionLE m := by
  let V : SSet := (SSet.Truncated.sk m).obj U
  let e : V ≅ (V.skeleton (m + 1) : SSet) :=
    (by
      simpa [V] using (SSet.Truncated.sk m).mapIso (asIso ((SSet.skAdj m).unit.app U))) ≪≫
      truncatedSkeletonIsoSkeleton m V
  change V.HasDimensionLT (m + 1)
  rw [SSet.hasDimensionLT_iff_of_iso e (m + 1)]
  infer_instance

/-- Lemma 14.21.4: if `U` is an `m`-truncated simplicial set and `n > m`, then every `n`-simplex
of `i_{m!} U`, i.e. of `(SSet.Truncated.sk m).obj U`, is degenerate. -/
theorem truncatedSkeleton_mem_degenerate_of_lt
    (m : ℕ) (U : SSet.Truncated m) {n : ℕ} (h : m < n)
    (x : ((SSet.Truncated.sk m).obj U) _⦋n⦌) :
    x ∈ ((SSet.Truncated.sk m).obj U).degenerate n := by
  rw [((SSet.Truncated.sk m).obj U).degenerate_eq_top_of_hasDimensionLT (m + 1) n
    (Nat.succ_le_of_lt h)]
  exact Set.mem_univ x

/-! ### Lemma_14_21_5 (from Chap14) -/
open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

/- Domain-style sampling for Lemma 14.21.5:
- primary domain: simplicial-set skeletons and the canonical counit `((SSet.skAdj n).counit.app U)`;
- sampled owner declarations:
  `SSet.skeleton`,
  `SSet.Subcomplex.range`,
  `SSet.Subcomplex.toRange`,
  `SSet.skeleton_obj_eq_top`;
- best owner abstraction: the canonical owner is the subcomplex `U.skeleton (n + 1)`;
- primitive data: only the simplicial set `U` and its owner subcomplex `U.skeleton (n + 1)`;
- derived API: the range identification for the counit and the induced isomorphism from
  `(SSet.sk n).obj U` to that owner object.

Source/core/bridge triage:
- `source-facing`: the textbook identification of `i_{n!} sk_n U` with the simplicial subset of
  `U` generated by simplices in degrees at most `n`;
- `core/canonical`: `SSet.skeleton`;
- `bridge/view`: the equality between the counit range and `U.skeleton (n + 1)`, together with the
  resulting isomorphism of simplicial sets.

The counit mono fact below is proof support for `SSet.Subcomplex.toRange`; it is not part of the
public owner API. -/
-- Proof sketch: by Lemma 14.21.4, every nondegenerate simplex of `(SSet.sk n).obj U` has degree at
-- most `n`, and the counit is an isomorphism in those degrees by truncation-coreflection. Hence it
-- preserves nondegenerate simplices and is injective on them, so Lemma 14.18.3 gives degreewise
-- injectivity, which is equivalent to being a monomorphism in `SSet`.
private theorem counit_mono (n : ℕ) (U : SSet.{u}) :
    Mono ((SSet.skAdj n).counit.app U) := sorry

-- Proof sketch: Lemma 14.18.4 identifies the textbook sub simplicial set `U'` with
-- `U.skeleton (n + 1)`. The counit is an isomorphism in degrees `≤ n`, and Lemma 14.21.4 shows
-- that every simplex in higher degree in its source is degenerate. Using the injectivity result
-- above, the image contains exactly the simplices generated by degrees `≤ n`, i.e. the
-- `(n + 1)`-skeleton.
/-- The image of the counit from the simplicial `n`-skeleton of `U` is exactly the
`(n + 1)`-skeleton subcomplex of `U`. -/
theorem truncatedSkeletonCounit_range_eq_skeleton (n : ℕ) (U : SSet.{u}) :
    SSet.Subcomplex.range ((SSet.skAdj n).counit.app U) = U.skeleton (n + 1) := sorry

/-- Lemma 14.21.5: the canonical morphism `i_{n!} sk_n U ⟶ U`, namely the counit
`((SSet.skAdj n).counit.app U)`, identifies `i_{n!} sk_n U` with the simplicial subset of `U`
generated by simplices in degrees at most `n`, i.e. with `(U.skeleton (n + 1) : SSet)`. -/
def truncatedSkeletonIsoSkeleton (n : ℕ) (U : SSet.{u}) :
    (SSet.sk n).obj U ≅ (U.skeleton (n + 1) : SSet) :=
  let ε : (SSet.sk n).obj U ⟶ U := (SSet.skAdj n).counit.app U
  let _ : Mono ε := counit_mono n U
  asIso (SSet.Subcomplex.toRange ε) ≪≫
    SSet.Subcomplex.eqToIso (truncatedSkeletonCounit_range_eq_skeleton n U)

/-! ### Remark_14_21_6 (from Chap14) -/
open CategoryTheory

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]
variable (m : ℕ)

/- Domain-style sampling for Remark 14.21.6:
- primary domain: simplicial-object truncation, skeleton, and coskeleton functors;
- sampled owner declarations:
  `Truncated.sk`,
  `Truncated.cosk`,
  `sk`,
  `cosk`;
- best owner abstraction: the canonical endofunctor owners are `sk m` and `cosk m`;
- primitive data: only the truncation level `m` and the Kan-extension hypotheses needed to form
  those owners;
- derived API: the textbook composites `truncation m ⋙ Truncated.sk m` and
  `truncation m ⋙ Truncated.cosk m`, which here are not new constructions but merely the defining
  expressions of `sk m` and `cosk m`.

Source/core/bridge triage:
- `source-facing`: the textbook composites `Simp(C) ⥤ Simp_m(C) ⥤ Simp(C)` for skeleton and
  coskeleton;
- `core/canonical`: the owner endofunctors `sk m` and `cosk m`;
- `bridge/view`: the definitional equalities below, checked directly by `rfl`.

This remark adds no new mathematics beyond the owner API, so the refined file keeps direct
canonical recall/use instead of a local theorem shell. -/

section

variable [∀ F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion m).op.HasLeftKanExtension F]

/- Remark 14.21.6: the textbook skeleton composite
`truncation m ⋙ Truncated.sk m : SimplicialObject C ⥤ SimplicialObject C`
is exactly the canonical endofunctor `sk m`. -/
recall sk

/- In mathlib, `sk m` is definitionally the composite `truncation m ⋙ Truncated.sk m`. -/
#check (rfl : sk m = truncation m ⋙ Truncated.sk m)

/- For simplicial sets, Lemma 14.21.5 explains why this skeleton composite is the simplicial subset
generated by simplices of degree at most `m` and their degeneracies. -/

end

section

variable [∀ F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion m).op.HasRightKanExtension F]

/- The textbook coskeleton composite
`truncation m ⋙ Truncated.cosk m : SimplicialObject C ⥤ SimplicialObject C`
is exactly the canonical endofunctor `cosk m`. -/
recall cosk

/- In mathlib, `cosk m` is definitionally the composite `truncation m ⋙ Truncated.cosk m`. -/
#check (rfl : cosk m = truncation m ⋙ Truncated.cosk m)

end

end CategoryTheory.SimplicialObject

/-! ### Lemma_14_21_7 (from Chap14) -/
open CategoryTheory Limits Opposite Simplicial

universe u

namespace SSet

/- 
Domain-style sampling for Lemma 14.21.7:
- primary domain: simplicial-set inclusions obtained by adjoining a single simplex, and the
  resulting canonical pushout squares in `SSet`;
- sampled owner-style declarations:
  `SSet.Subcomplex.N`,
  `SSet.Subcomplex.ofSimplex`,
  `CategoryTheory.Subfunctor.range_ι`,
  `SSet.boundary`,
  `SSet.skeletonOfMono`,
  `SSet.Subcomplex.BicartSq.isPushout`,
  `SSet.yonedaEquiv`;
- best owner abstraction:
  `source-facing`: a new nondegenerate simplex `x : U.N` whose boundary already lands in the
    source subcomplex `U`, together with the canonical equality saying that adjoining `x.simplex`
    generates all of `V`;
  `core/canonical`: the ambient owners `Subcomplex.N`, `Subcomplex.ofSimplex`, `SSet.boundary`,
    `Subcomplex.range`, and `Subcomplex.BicartSq.isPushout`;
  `bridge/view`: the induced boundary map `∂Δ[x.dim] ⟶ U` and the canonical `IsPushout` square;
- primitive data: only the source subcomplex `U`, the new simplex `x : U.N`, the canonical
  boundary-factorization predicate `x.boundary_range_le`, and the equality
  `U ⊔ Subcomplex.ofSimplex x.simplex = ⊤`;
- derived API: the boundary map `∂Δ[x.dim] ⟶ U` induced by `x.boundary_range_le` and the
  resulting pushout square.
-/

namespace Subcomplex
namespace N

variable {V : SSet.{u}} {U : V.Subcomplex} (x : U.N)

/-- The boundary of the simplex classified by `x.simplex` lands in the source subcomplex `U`. -/
abbrev boundary_range_le : Prop :=
  Subcomplex.range (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) ≤ U

end N
end Subcomplex

/-- Lemma 14.21.7: if a subcomplex `U ⊆ V` is obtained by adjoining the new nondegenerate simplex
`x : U.N`, if the boundary of `x.simplex` already lands in `U`, and if adjoining `x.simplex`
generates all of `V`, then the square `∂Δ[x.dim] ⟶ U`, `Δ[x.dim] ⟶ V` defined by `x.simplex` is
a pushout square. -/
-- Proof sketch: the boundary of the canonical map `Δ[x.dim] ⟶ V` classified by `x.simplex`
-- factors through `U` by `hboundary`. Then identify the image of `Δ[x.dim] ⟶ V` with
-- `Subcomplex.ofSimplex x.simplex`, use `hgen` to express that adjoining this subcomplex to `U`
-- gives all of `V`, identify its intersection with `U` with the boundary, and apply
-- `SSet.Subcomplex.BicartSq.isPushout` to the resulting bicartesian square of subcomplexes.
theorem isPushout_of_subcomplex_adjoin_simplex
    {V : SSet.{u}} (U : V.Subcomplex) (x : U.N)
    (hboundary : x.boundary_range_le)
    (hgen : U ⊔ Subcomplex.ofSimplex x.simplex = ⊤) :
    IsPushout ∂Δ[x.dim].ι
      (U.lift (∂Δ[x.dim].ι ≫ yonedaEquiv.symm x.simplex) hboundary)
      (yonedaEquiv.symm x.simplex) U.ι := sorry

end SSet

/-! ### Lemma_14_21_8 (from Chap14) -/
open scoped Simplicial

universe u

namespace SSet

/- Domain-style sampling for Lemma 14.21.8:
- primary domain: finite simplicial sets and filtrations of subcomplex inclusions by successive
  single-simplex extensions;
- sampled owner-style declarations:
  `SSet.Finite`,
  `SSet.Subcomplex.N`,
  `SSet.Subcomplex.ofSimplex`,
  `RelSeries`;
- best owner abstraction:
  `source-facing`: the existence of a finite chain `U = W₀ ⊆ ⋯ ⊆ W_r = V` whose successive
  inclusions are single-simplex extensions with the boundary of the attached simplex already in
  the previous stage;
  `core/canonical`: finiteness through `SSet.Finite`, single-step extension data through
  `Subcomplex.N`, `Subcomplex.N.boundary_range_le`, and `Subcomplex.ofSimplex`, and finite chains
  through `RelSeries`;
  `bridge/view`: the anonymous adjacent-step relation on `V.Subcomplex`, used only inside the
  filtration existence theorem because it has no separate owner-level downstream role;
- primitive data:
  only the new simplex `x : U.N`, the boundary-factorization predicate `x.boundary_range_le`, and
  the equality `U ⊔ Subcomplex.ofSimplex x.simplex = W` for each step of the chain;
- derived API:
  the ambient finiteness owner `SSet.Finite` and the source-facing finite chain expressed by
  `RelSeries`.

The finite-chain owner is `RelSeries`, so the public source-facing existence statement should use
that canonical owner directly. The adjacent-step predicate is only a bridge/view used inside this
one theorem, so it should not survive as a second public owner declaration. In particular,
`SSet.Finite V` already supplies the degreewise finiteness consequences needed for the textbook
hypothesis, so the filtration theorem should consume that owner canonically as an instance rather
than as a separate named public hypothesis. -/

-- Proof sketch: convert the finiteness hypotheses on nondegenerate simplices into a finite number
-- of missing nondegenerate simplices of `V` outside `U`, and induct on that number. At each step,
-- pick one of minimal degree, adjoin all of its degeneracies to obtain the next subcomplex, verify
-- that every proper face of the chosen simplex already lies in the previous stage by minimality,
-- and iterate until reaching `V`.
/-- Lemma 14.21.8: if `U ⊆ V` is an inclusion of simplicial sets, if `V` is degreewise finite,
and if `V` has finitely many nondegenerate simplices, then there
exists a finite filtration from `U` to `V` whose successive inclusions are single-simplex
extensions in the sense of Lemma 14.21.7. Here the finite chain is expressed by the canonical
owner `RelSeries`, starting at `U` and ending at `⊤ : V.Subcomplex`; the adjacent-step predicate
is kept inline because it is only a bridge/view for this one source-facing theorem. The degreewise
finiteness of `V` is already part of the canonical owner `SSet.Finite V`, and the corresponding
finiteness data for `U` is derived by the subcomplex instance. -/
theorem exists_singleSimplexExtensionFiltration
    {V : SSet.{u}} [V.Finite] (U : V.Subcomplex) :
    ∃ s : RelSeries
      ({ p | ∃ x : p.1.N,
        x.boundary_range_le ∧ p.1 ⊔ Subcomplex.ofSimplex x.simplex = p.2 } :
        SetRel V.Subcomplex V.Subcomplex),
      s.head = U ∧ s.last = (⊤ : V.Subcomplex) := sorry

end SSet

/-! ### Lemma_14_21_9 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory SimplexCategory.Truncated
open AlgebraicTopology
open SimplicialObject.Truncated

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Domain-style sampling for Lemma 14.21.9:
- primary domain: simplicial objects in an abelian category, the skeleton/truncation left Kan
  extension, and normalized Moore subobjects;
- sampled owner declarations:
  `NormalizedMooreComplex.objX`,
  `SimplicialObject.generatedByDegreeLE`,
  `SimplicialObject.generatedByDegreeLE_app_subobject`,
  `Truncated.sk`,
  `Functor.leftKanExtensionObjIsoColimit`;
- best owner abstraction:
  `source-facing`: the vanishing of the normalized Moore subobject of `i_{m!} U` in degrees
    strictly larger than `m`;
  `core/canonical`: `NormalizedMooreComplex.objX`;
  `bridge/view`: the pointwise colimit description of `i_{m!} U`, used to show that every degree
    of `i_{m!} U` is generated by simplices from degrees `≤ m`, so the existing owner theorem
    `generatedByDegreeLE_normalizedMoore_eq_bot_of_lt` applies directly.
- primitive data: only the truncated simplicial object `U`;
- derived API: the vanishing statement for the normalized Moore subobject of its truncated
  extension. -/

private theorem truncatedExtension_generatedByDegreeLEObj_eq_top
    (m : ℕ) (U : SimplicialObject.Truncated A m) (Δ : SimplexCategory) :
    ((Truncated.sk m).obj U).generatedByDegreeLEObj m Δ = ⊤ := by
  let V : SimplicialObject A := (Truncated.sk m).obj U
  let D : CostructuredArrow (Truncated.inclusion m).op (op Δ) ⥤ A :=
    CostructuredArrow.proj (Truncated.inclusion m).op (op Δ) ⋙ U
  let P : Subobject (V.obj (op Δ)) := V.generatedByDegreeLEObj m Δ
  let e : V.obj (op Δ) ≅ colimit D :=
    (Truncated.inclusion m).op.leftKanExtensionObjIsoColimit U (op Δ)
  let s : Cocone D :=
    { pt := P
      ι :=
        { app := fun g ↦
            let i := g.left.unop
            let θ : Δ ⟶ i.obj := by
              simpa using g.hom.unop
            let hle : imageSubobject (colimit.ι D g ≫ e.inv) ≤ P := by
              haveI : IsIso
                  (((Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left) :=
                by
                  simpa [skAdj, Functor.lanAdjunction_unit] using
                    ((NatTrans.isIso_iff_isIso_app ((skAdj m).unit.app U)).1
                      inferInstance g.left)
              have hcolim :
                  colimit.ι D g ≫ e.inv =
                    (((Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left) ≫
                      V.map g.hom := by
                simpa [D, e, V] using
                  (((Truncated.inclusion m).op).ι_leftKanExtensionObjIsoColimit_inv U (op Δ) g)
              have himage :
                  imageSubobject (colimit.ι D g ≫ e.inv) = imageSubobject (V.map θ.op) := by
                simpa [hcolim, θ] using
                  (imageSubobject_iso_comp
                    (((Truncated.inclusion m).op.leftKanExtensionUnit U).app g.left)
                    (V.map g.hom))
              rw [himage]
              simpa [P] using
                imageSubobject_map_le_generatedByDegreeLEObj V m
                  (by simpa using i.property) θ
            factorThruImageSubobject (colimit.ι D g ≫ e.inv) ≫ Subobject.ofLE _ _ hle
          naturality := by
            intro g g' α
            apply Subobject.eq_of_comp_arrow_eq
            simp [Category.assoc] } }
  have hdesc : colimit.desc D s ≫ P.arrow = e.inv := by
    apply colimit.hom_ext
    intro g
    rw [colimit.ι_desc_assoc]
    simp [s, Category.assoc]
  have hsplit : (e.hom ≫ colimit.desc D s) ≫ P.arrow = 𝟙 _ := by
    simpa [Category.assoc] using congrArg (fun t ↦ e.hom ≫ t) hdesc
  letI : IsSplitEpi P.arrow :=
    IsSplitEpi.mk' { section_ := e.hom ≫ colimit.desc D s, id := hsplit }
  letI : IsIso P.arrow := isIso_of_mono_of_epi P.arrow
  simpa [P] using (Subobject.eq_top_of_isIso_arrow P)

/-- Lemma 14.21.9: if `U` is an `m`-truncated simplicial object in an abelian category, then the
degree-`n` normalized Moore subobject of `i_{m!} U = (Truncated.sk m).obj U`
vanishes for every `n > m`. -/
theorem truncatedExtension_normalizedMoore_eq_bot_of_lt
    (m : ℕ) (U : SimplicialObject.Truncated A m) {n : ℕ} (h : m < n) :
    NormalizedMooreComplex.objX ((Truncated.sk m).obj U) n = ⊥ := by
  let V : SimplicialObject A := (Truncated.sk m).obj U
  let W : SimplicialObject A := V.generatedByDegreeLE m
  let η : W ⟶ V := (V.generatedByDegreeLE m).arrow
  have hη : ∀ Δ : SimplexCategoryᵒᵖ, IsIso (η.app Δ) := by
    intro Δ
    cases Δ with
    | op Δ =>
        rw [Subobject.isIso_iff_mk_eq_top, SimplicialObject.generatedByDegreeLE_app_subobject]
        simpa [V] using truncatedExtension_generatedByDegreeLEObj_eq_top m U Δ
  haveI : IsIso η := (NatTrans.isIso_iff_isIso_app η).2 hη
  let eη : W ≅ V := asIso η
  have hgen : NormalizedMooreComplex.objX W n = ⊥ :=
    generatedByDegreeLE_normalizedMoore_eq_bot_of_lt V h
  let e₀' :
      ((normalizedMooreComplex A).obj W).X n ≅
        ((⊥ : Subobject (W.obj (op (SimplexCategory.mk n)))) : A) :=
    eqToIso (by
      change (NormalizedMooreComplex.objX W n : A) =
        ((⊥ : Subobject (W.obj (op (SimplexCategory.mk n)))) : A)
      simp [hgen])
  let e₀ := e₀' ≪≫ Subobject.botCoeIsoZero
  haveI : IsIso (((normalizedMooreComplex A).map eη.hom).f n) := by
    exact Functor.map_isIso (HomologicalComplex.eval A (ComplexShape.down ℕ) n)
      ((normalizedMooreComplex A).map eη.hom)
  let e₁ :=
    (asIso (((normalizedMooreComplex A).map eη.hom).f n)).symm ≪≫ e₀
  have hzero : (NormalizedMooreComplex.objX V n).arrow = 0 :=
    zero_of_source_iso_zero _ e₁
  simpa [V] using
    ((Subobject.mk_eq_bot_iff_zero :
      Subobject.mk (NormalizedMooreComplex.objX V n).arrow = ⊥ ↔
        (NormalizedMooreComplex.objX V n).arrow = 0)).2 hzero

end CategoryTheory

/-! ### Lemma_14_21_10 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open Opposite
open AlgebraicTopology

noncomputable section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A]

/- 
Domain-style sampling for Lemma 14.21.10:
- primary domain: simplicial-object skeleton/truncation adjunctions in an abelian category, viewed
  through the normalized Moore complex and the chapter's source-facing generated sub simplicial
  object;
- sampled owner declarations:
  `skAdj`,
  `SimplicialObject.generatedByDegreeLE`,
  `SimplicialObject.generatedByDegreeLE_app_subobject`,
  `NormalizedMooreComplex.objX`,
  `NatTrans.mono_iff_mono_app`;
- best owner abstraction:
  `source-facing`: the identification of `(sk n).obj U` with the canonical sub simplicial object
    `U.generatedByDegreeLE n ⊂ U`;
  `core/canonical`: the adjunction owner `skAdj n`, the canonical subobject
    `U.generatedByDegreeLE n : Subobject U`, its inclusion `.arrow`, and the normalized Moore
    complex functor;
  `bridge/view`: the mono proof for the counit together with the subobject comparison APIs
    `Subobject.mk_le_of_comm` and `Subobject.isoOfMkEqMk`.
- primitive data: only the simplicial object `U`, the skeleton counit, the canonical subobject
  `U.generatedByDegreeLE n`, and the normalized Moore degree subobjects;
- derived API: the counit mono companion, the equality of its image subobject with
  `U.generatedByDegreeLE n`, and the resulting isomorphism
  `(sk n).obj U ≅ U.generatedByDegreeLE n`. -/

/-- In degree `i ≤ n`, the counit `((skAdj n).counit.app U)` is an isomorphism. -/
theorem truncatedSkeleton_counit_app_isIso_of_le
    [HasFiniteColimits A]
    (n : ℕ) (U : SimplicialObject A) {i : ℕ} (hi : i ≤ n) :
    IsIso (((skAdj n).counit.app U).app (op (SimplexCategory.mk i))) := by
  let ε : (sk n).obj U ⟶ U := (skAdj n).counit.app U
  let i' : SimplexCategory.Truncated n := ⟨SimplexCategory.mk i, hi⟩
  haveI : IsIso ((skAdj n).unit.app ((truncation n).obj U)) := by infer_instance
  haveI : IsIso ((truncation n).map ε) := by
    exact isIso_of_hom_comp_eq_id ((skAdj n).unit.app ((truncation n).obj U))
      ((skAdj n).right_triangle_components U)
  simpa [ε] using
    ((NatTrans.isIso_iff_isIso_app ((truncation n).map ε)).1 inferInstance (op i'))

section

variable [Abelian A]

-- Proof sketch: by Lemma 14.21.9, the normalized Moore subobjects of `(sk n).obj U` vanish in
-- degrees `> n`, while Lemma 14.21.3 shows that the counit map is an isomorphism in degrees
-- `≤ n`. Hence the induced maps on normalized Moore complexes are monomorphisms in every degree.
-- Applying Lemma 14.18.7 gives that each simplicial degree map of the counit is mono, and
-- therefore the counit itself is a monomorphism in the functor category.
/-- Companion to Lemma 14.21.10: the counit morphism from the simplicial `n`-skeleton of `U` to
`U` is a monomorphism. -/
theorem truncatedSkeleton_counit_mono
    (n : ℕ) (U : SimplicialObject A) :
    Mono ((skAdj n).counit.app U) := by
  let ε : (sk n).obj U ⟶ U := (skAdj n).counit.app U
  exact mono_of_normalizedMooreComplex_degreewise_mono ε fun i ↦ by
    by_cases hi : n < i
    · have hbot : NormalizedMooreComplex.objX ((sk n).obj U) i = ⊥ := by
        simpa using truncatedExtension_normalizedMoore_eq_bot_of_lt n ((truncation n).obj U) hi
      let e₀' :
          ((normalizedMooreComplex A).obj ((sk n).obj U)).X i ≅
            ((⊥ : Subobject (((sk n).obj U).obj (op (SimplexCategory.mk i)))) : A) :=
        eqToIso <|
          congrArg
            (fun S : Subobject (((sk n).obj U).obj (op (SimplexCategory.mk i))) ↦ (S : A)) hbot
      let e₀ := e₀' ≪≫ Subobject.botCoeIsoZero
      exact mono_of_source_iso_zero (((normalizedMooreComplex A).map ε).f i) e₀
    · have hi' : i ≤ n := Nat.le_of_not_gt hi
      haveI : IsIso (ε.app (op (SimplexCategory.mk i))) :=
        truncatedSkeleton_counit_app_isIso_of_le n U hi'
      haveI : Mono (ε.app (op (SimplexCategory.mk i))) := by infer_instance
      haveI : Mono (NormalizedMooreComplex.objX U i).arrow := Subobject.arrow_mono _
      haveI : Mono (NormalizedMooreComplex.objX ((sk n).obj U) i).arrow := Subobject.arrow_mono _
      have hcomp :
          (((normalizedMooreComplex A).map ε).f i) ≫ (NormalizedMooreComplex.objX U i).arrow =
            (NormalizedMooreComplex.objX ((sk n).obj U) i).arrow ≫
              ε.app (op (SimplexCategory.mk i)) := by
        simpa [ε] using
          congrArg (fun φ ↦ φ.f i) ((inclusionOfMooreComplex A).naturality ε)
      have hmono :
          Mono ((((normalizedMooreComplex A).map ε).f i) ≫
            (NormalizedMooreComplex.objX U i).arrow) := by
        rw [hcomp]
        exact mono_comp' (Subobject.arrow_mono _) inferInstance
      letI :
          Mono ((((normalizedMooreComplex A).map ε).f i) ≫
            (NormalizedMooreComplex.objX U i).arrow) := hmono
      exact mono_of_mono (((normalizedMooreComplex A).map ε).f i)
        (NormalizedMooreComplex.objX U i).arrow

private theorem truncation_generatedByDegreeLE_arrow_isIso
    (n : ℕ) (U : SimplicialObject A) :
    IsIso ((truncation n).map (U.generatedByDegreeLE n).arrow) := by
  refine (NatTrans.isIso_iff_isIso_app _).2 ?_
  intro Δ
  cases Δ with
  | op Δ =>
      cases Δ with
      | mk i hi =>
          simpa using generatedByDegreeLE_arrow_app_isIso_of_le U n hi

instance (n : ℕ) (U : SimplicialObject A) : Mono ((skAdj n).counit.app U) :=
  truncatedSkeleton_counit_mono n U

-- Proof sketch: the mono theorem above turns the counit into a simplicial subobject of `U`.
-- Because the counit is an isomorphism in every degree `≤ n`, all generators used in
-- `generatedByDegreeLEObj` lie in this image, so `U.generatedByDegreeLE n` factors through the
-- counit. Conversely, truncating `(U.generatedByDegreeLE n).arrow` gives an isomorphism, and
-- applying the adjunction `skAdj n` yields a factorization of the counit through that inclusion.
/-- The subobject of `U` defined by the counit `((skAdj n).counit.app U)` is exactly the canonical
sub simplicial object of `U` generated by simplices in degrees at most `n`. -/
theorem truncatedSkeletonCounit_subobject_eq_generatedByDegreeLE
    (n : ℕ) (U : SimplicialObject A) :
    Subobject.mk ((skAdj n).counit.app U) = U.generatedByDegreeLE n := by
  let ε : (sk n).obj U ⟶ U := (skAdj n).counit.app U
  let V : SimplicialObject A := (U.generatedByDegreeLE n : SimplicialObject A)
  let η : V ⟶ U := (U.generatedByDegreeLE n).arrow
  haveI : Mono ε := truncatedSkeleton_counit_mono n U
  haveI : Mono η := Subobject.arrow_mono (U.generatedByDegreeLE n)
  haveI : IsIso ((truncation n).map η) :=
    truncation_generatedByDegreeLE_arrow_isIso n U
  let φ : (sk n).obj U ⟶ V :=
    ((skAdj n).homEquiv ((truncation n).obj U) V).symm
      (inv ((truncation n).map η))
  have hφη : φ ≫ η = ε := by
    apply ((skAdj n).homEquiv ((truncation n).obj U) U).injective
    calc
      ((skAdj n).homEquiv ((truncation n).obj U) U) (φ ≫ η) =
          ((skAdj n).homEquiv ((truncation n).obj U) V) φ ≫ (truncation n).map η := by
            simpa using (skAdj n).homEquiv_naturality_right φ η
      _ = 𝟙 _ := by simp [φ]
      _ = ((skAdj n).homEquiv ((truncation n).obj U) U) ε := by
            rw [Adjunction.homEquiv_unit]
            exact ((skAdj n).right_triangle_components U).symm
  have h₁ : Subobject.mk ε ≤ U.generatedByDegreeLE n :=
    Subobject.mk_le_of_comm φ hφη
  have hηε :
      ∀ Δ : SimplexCategoryᵒᵖ, Subobject.mk (η.app Δ) ≤ Subobject.mk (ε.app Δ) := by
    intro Δ
    cases Δ with
    | op Δ =>
        cases Δ with
        | mk m =>
            rw [generatedByDegreeLE_app_subobject]
            exact
              (generatedByDegreeLEObj_isLUB_map_images U n m).2 (by
                rintro _ ⟨i, hi, θ, rfl⟩
                haveI : IsIso (ε.app (op (SimplexCategory.mk i))) :=
                  truncatedSkeleton_counit_app_isIso_of_le n U hi
                refine imageSubobject_le_mk (ε.app (op (SimplexCategory.mk m))) (U.map θ.op)
                  (inv (ε.app (op (SimplexCategory.mk i))) ≫ ((sk n).obj U).map θ.op) ?_
                rw [Category.assoc, ε.naturality]
                simp)
  let ψ : V ⟶ (sk n).obj U :=
    { app := fun Δ ↦ Subobject.ofMkLEMk (η.app Δ) (ε.app Δ) (hηε Δ)
      naturality := by
        intro Δ Δ' f
        apply (cancel_mono (ε.app Δ')).1
        calc
          (V.map f ≫ Subobject.ofMkLEMk (η.app Δ') (ε.app Δ') (hηε Δ')) ≫ ε.app Δ' =
              V.map f ≫ η.app Δ' := by
                rw [Category.assoc, Subobject.ofMkLEMk_comp]
          _ = η.app Δ ≫ U.map f := η.naturality f
          _ = (Subobject.ofMkLEMk (η.app Δ) (ε.app Δ) (hηε Δ) ≫ ε.app Δ) ≫ U.map f := by
                rw [Subobject.ofMkLEMk_comp]
          _ = (Subobject.ofMkLEMk (η.app Δ) (ε.app Δ) (hηε Δ) ≫ ((sk n).obj U).map f) ≫
                ε.app Δ' := by
                  simp_rw [Category.assoc]
                  rw [ε.naturality] }
  have hψη : ψ ≫ ε = η := by
    ext Δ
    simp [ψ]
  have h₂ : U.generatedByDegreeLE n ≤ Subobject.mk ε := by
    let g : V ⟶ (Subobject.mk ε : SimplicialObject A) :=
      ψ ≫ (Subobject.underlyingIso ε).inv
    have hg : g ≫ (Subobject.mk ε).arrow = η := by
      ext Δ
      simpa [g] using congr_app hψη Δ
    simpa [η, V] using Subobject.mk_le_of_comm g hg
  exact le_antisymm h₁ h₂

/-- Lemma 14.21.10: the canonical simplicial `n`-skeleton `i_{n!} sk_n U` is identified with the
canonical simplicial subobject of `U` generated by simplices in degrees at most `n`, namely
`U.generatedByDegreeLE n`. -/
def truncatedSkeletonIsoGeneratedByDegreeLE
    (n : ℕ) (U : SimplicialObject A) :
    (sk n).obj U ≅ (U.generatedByDegreeLE n : SimplicialObject A) :=
  Subobject.isoOfMkEq ((skAdj n).counit.app U) (U.generatedByDegreeLE n)
    (truncatedSkeletonCounit_subobject_eq_generatedByDegreeLE n U)

end

end CategoryTheory

/-! ### Lemma_14_21_11 (from Chap14) -/
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
