import Mathlib
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_14_19_1 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

/- Domain-style sampling for Example 14.19.1:
- primary domain: simplicial objects modeling `cosk₀`, equivalently the Čech nerve of the terminal
  map out of `X`;
- sampled owner API:
  `cechNerveTerminalFrom`,
  `CechNerveTerminalFrom.iso`,
  `Truncated.cosk`,
  `coskAdj`;
- best owner abstraction: the file's main item is `source-facing`, since it constructs the explicit
  simplicial object `n ↦ X^(n + 1)` under the weaker hypothesis that only those self-products of
  `X` exist. Under stronger global finite-product hypotheses, the canonical owner is
  `cechNerveTerminalFrom X`, and when the right Kan extensions exist the further `core/canonical`
  owner is `Truncated.cosk 0`.
- source/core/bridge triage:
  `source-facing`: the explicit self-product model and its degree-zero universal property;
  `core/canonical`: `cechNerveTerminalFrom X` and `Truncated.cosk 0`;
  `bridge/view`: under `[HasFiniteProducts C]`, the canonical isomorphism
  `CechNerveTerminalFrom.iso X` together with the definitional identification below, since
  mathlib's owner `cechNerveTerminalFrom X` is the same self-product simplicial object up to the
  product-instance choices.
- primitive data: the degreewise products `∏ᶜ (fun _ : Fin (n + 1) ↦ X)` and the reindexing maps
  induced by simplex operators;
- derived API: the projection formula, the bridge to `cechNerveTerminalFrom X`, and the bijection
  with degree-zero morphisms. -/

section SelfProduct

variable {C : Type u} [Category.{v} C]
variable (X : C)
variable [∀ n : ℕ, HasProduct (fun _ : Fin (n + 1) ↦ X)]

/-- The simplicial object whose `n`-simplices are the `(n + 1)`-fold self-product of `X`. -/
noncomputable def zeroCoskeletonSelfProduct : SimplicialObject C where
  obj Δ := ∏ᶜ fun _ : Fin (Δ.unop.len + 1) ↦ X
  map f := Pi.lift fun i ↦ Pi.π _ ((f.unop).toOrderHom i)
  map_id := by
    intro Δ
    apply Pi.hom_ext
    intro i
    simpa using
      (Pi.lift_π (fun j ↦ Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) j) i)
  map_comp := by
    intro Δ₁ Δ₂ Δ₃ f g
    apply Pi.hom_ext
    intro i
    rw [Category.assoc]
    simp only [Pi.lift_π]
    simp [unop_comp, SimplexCategory.comp_toOrderHom]

-- Proof sketch: the structure map in simplicial degree `f` is defined by `Pi.lift`; composing
-- with the `i`-th target projection simply selects the source projection indexed by
-- `(f.unop).toOrderHom i`.
/-- The map on a simplex operator in `zeroCoskeletonSelfProduct X` is characterized by its effect
on the product projections. -/
@[simp, reassoc]
theorem zeroCoskeletonSelfProduct_map_π
    {Δ Δ' : SimplexCategoryᵒᵖ} (f : Δ ⟶ Δ') (i : Fin (Δ'.unop.len + 1)) :
    (zeroCoskeletonSelfProduct X).map f ≫
        Pi.π (fun _ : Fin (Δ'.unop.len + 1) ↦ X) i =
      Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) ((f.unop).toOrderHom i) := by
  simpa [zeroCoskeletonSelfProduct] using
    (Pi.lift_π (fun j ↦ Pi.π (fun _ : Fin (Δ.unop.len + 1) ↦ X) ((f.unop).toOrderHom j)) i)

-- Proof sketch: a simplicial morphism into `zeroCoskeletonSelfProduct X` is determined by its
-- degree-zero component because every higher component is forced by the projection formulas from
-- `zeroCoskeletonSelfProduct_map_π`; conversely, a map `V₀ ⟶ X` induces compatible maps
-- `Vₙ ⟶ X^{n + 1}` by precomposing with the simplicial operators `[0] ⟶ [n]`.
/-- Example 14.19.1: if the nonempty finite self-products of `X` exist, then the simplicial object
with `n`-simplices `X^(n + 1)` has the universal property of `cosk₀(X)`: for every simplicial
object `V`, taking the degree-zero component gives the canonical bijection between morphisms
`V ⟶ zeroCoskeletonSelfProduct X` and morphisms `V₀ ⟶ X`. -/
noncomputable def zeroCoskeletonSelfProductHomEquiv
    (V : SimplicialObject C) :
    (V ⟶ zeroCoskeletonSelfProduct X) ≃ (V _⦋0⦌ ⟶ X) where
  toFun f := f.app (op ⦋0⦌) ≫ Pi.π (fun _ : Fin 1 ↦ X) 0
  invFun g :=
    { app := fun Δ ↦
        Pi.lift fun i ↦ V.map (SimplexCategory.const ⦋0⦌ Δ.unop i).op ≫ g
      naturality := sorry }
  left_inv := sorry
  right_inv := sorry

end SelfProduct

section SelfProductBridge

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
variable (X : C)

local instance (n : ℕ) : HasProduct (fun _ : Fin (n + 1) ↦ X) := by
  infer_instance

/-- Under finite products, the explicit self-product model of Example 14.19.1 is canonically
isomorphic to the mathlib owner `cechNerveTerminalFrom X`. -/
noncomputable def zeroCoskeletonSelfProductIsoCechNerveTerminalFrom :
    zeroCoskeletonSelfProduct X ≅ cechNerveTerminalFrom X :=
  Iso.refl _

end SelfProductBridge

end CategoryTheory

/-! ### Lemma_14_19_2 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SimplexCategory.Truncated

/-- The structured-arrow indexing category for the degree-`n` matching diagram of `cosk_m`. -/
abbrev matchingIndex (m n : ℕ) :=
  StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op

end SimplexCategory.Truncated

/-
Domain-style sampling for Lemma 14.19.2:
- primary domain: pointwise right Kan extensions computing simplicial coskeleta;
- sampled owner declarations:
  `SimplexCategory.Truncated.matchingIndex`,
  `Truncated.cosk`,
  `Functor.ranObjObjIsoLimit`,
  `Functor.ranObjObjIsoLimit_hom_π`,
  `Functor.HasPointwiseRightKanExtension`;
- best owner abstraction: `Functor.ranObjObjIsoLimit` specialized to
  `(SimplexCategory.Truncated.inclusion m).op`, with
  `SimplexCategory.Truncated.matchingIndex m n` as the source-facing owner for the indexing
  shape;
- primitive data: the truncation inclusion, the matching-index category
  `SimplexCategory.Truncated.matchingIndex m n`, the truncated simplicial object `U`, and the
  finite-limit hypothesis on `C`;
- derived API: the `FinCategory` instance on
  `SimplexCategory.Truncated.matchingIndex m n`, the degree-`n` limit description of `coskₘ U`,
  and its projection formula.

Source/core/bridge triage:
- `source-facing`: the degree-`n` matching-object description of `coskₘ U`;
- `core/canonical`: `Functor.ranObjObjIsoLimit` and `Functor.ranObjObjIsoLimit_hom_π`;
- `bridge/view`: the finite-category construction proving that finite limits in `C` provide the
  pointwise right Kan extensions needed for `Truncated.cosk`, with the matching-index owner
  `SimplexCategory.Truncated.matchingIndex m n`.

The local infrastructure below builds the finite-category bridge needed to expose the canonical
owner theorem. The reusable finiteness support for truncated simplex categories and the resulting
structured-arrow bridge remain public, while the one-off enumeration arguments used to construct
them stay private. -/

instance simplexCategoryOp_hom_finite (X Y : SimplexCategoryᵒᵖ) : Finite (X ⟶ Y) :=
  Finite.of_equiv (Y.unop ⟶ X.unop) Quiver.Hom.opEquiv

instance truncatedSimplex_finite (m : ℕ) : Finite (SimplexCategory.Truncated m) := by
  let e : Fin (m + 1) ≃ SimplexCategory.Truncated m :=
    { toFun := fun i ↦ ⟨SimplexCategory.mk i.1, Nat.le_of_lt_succ i.2⟩
      invFun := fun X ↦ ⟨X.obj.len, Nat.lt_succ_iff.mpr X.property⟩
      left_inv := by intro i; cases i; rfl
      right_inv := by intro X; cases X; rfl }
  exact Finite.of_equiv (Fin (m + 1)) e

instance truncatedSimplex_hom_finite {m : ℕ} (X Y : SimplexCategory.Truncated m) :
    Finite (X ⟶ Y) := by
  refine Finite.of_injective (fun f ↦ f.hom) ?_
  intro f g h
  exact ObjectProperty.hom_ext _ h

private instance truncatedSimplex_finCategory (m : ℕ) : FinCategory (SimplexCategory.Truncated m)
    where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

private instance structuredArrow_finite (m n : ℕ) :
    Finite (SimplexCategory.Truncated.matchingIndex m n) := by
  let e :
      (Σ X : (SimplexCategory.Truncated m)ᵒᵖ,
        (op ⦋n⦌ ⟶ (SimplexCategory.Truncated.inclusion m).op.obj X)) ≃
        SimplexCategory.Truncated.matchingIndex m n :=
    { toFun := fun p ↦ StructuredArrow.mk p.2
      invFun := fun A ↦ ⟨A.right, A.hom⟩
      left_inv := by intro p; cases p; rfl
      right_inv := by intro A; cases A; rfl }
  exact Finite.of_equiv _ e

private instance structuredArrow_hom_finite (m n : ℕ)
    (A B : SimplexCategory.Truncated.matchingIndex m n) :
    Finite (A ⟶ B) := by
  refine Finite.of_injective (fun f ↦ f.right) ?_
  intro f g h
  exact StructuredArrow.hom_ext f g h

instance (m n : ℕ) : FinCategory (SimplexCategory.Truncated.matchingIndex m n) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

/-- Finite limits in `C` give pointwise right Kan extensions along the inclusion of
`m`-truncated simplices into all simplices. -/
instance simplexTruncatedInclusion_hasPointwiseRightKanExtension
    [HasFiniteLimits C] (m : ℕ) (F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.inclusion m).op.HasPointwiseRightKanExtension F := by
  intro Y
  cases Y with
  | op Y =>
      change HasLimit
        (StructuredArrow.proj (op Y) (SimplexCategory.Truncated.inclusion m).op ⋙ F)
      letI : FinCategory (SimplexCategory.Truncated.matchingIndex m Y.len) := inferInstance
      infer_instance

section

variable [HasFiniteLimits C] (m n : ℕ) (U : SimplicialObject.Truncated C m)

/- The owner for the coskeleton limit description is `Functor.ranObjObjIsoLimit`. -/
recall Functor.ranObjObjIsoLimit

/- Lemma 14.19.2: if `C` has finite limits, then the `m`-coskeleton of an
`m`-truncated simplicial object exists, and its degree-`n` term is canonically the limit of the
diagram of all maps `[k] ⟶ [n]` with `k ≤ m`. This is the direct specialization of the canonical
owner `Functor.ranObjObjIsoLimit`. -/
#check ((SimplexCategory.Truncated.inclusion m).op.ranObjObjIsoLimit U (op ⦋n⦌) :
  ((Truncated.cosk m).obj U) _⦋n⦌ ≅
    limit (StructuredArrow.proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op ⋙ U))

variable (f : SimplexCategory.Truncated.matchingIndex m n)

/- Its projection formula is the companion owner theorem `Functor.ranObjObjIsoLimit_hom_π`. -/
recall Functor.ranObjObjIsoLimit_hom_π

/- Companion recall: the projection formula for the limit description of `cosk_m U` is exactly
the specialized owner theorem `Functor.ranObjObjIsoLimit_hom_π`. -/
#check ((SimplexCategory.Truncated.inclusion m).op.ranObjObjIsoLimit_hom_π U (op ⦋n⦌) f :
  ((SimplexCategory.Truncated.inclusion m).op.ranObjObjIsoLimit U (op ⦋n⦌)).hom ≫
      limit.π _ f =
    ((Truncated.cosk m).obj U).map f.hom ≫
      ((SimplexCategory.Truncated.inclusion m).op.ranCounit.app U).app f.right)

end

end CategoryTheory

/-! ### Lemma_14_19_3 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.SimplicialObject.Truncated
open scoped SimplexCategory.Truncated
open scoped Simplicial

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Lemma 14.19.3:
- primary domain: limits of structured-arrow diagrams computing objectwise values over the
  truncated simplex inclusion;
- sampled owner API:
  `SimplexCategory.Truncated.matchingIndex`,
  `StructuredArrow.mkIdInitial`,
  `IsInitial.hasInitial`,
  `limitOfInitial`;
- best owner abstraction: `Limits.limitOfInitial`, after the local bridge
  `StructuredArrow.mkIdInitial.hasInitial` supplying the initial object of the indexing category;
- primitive data: the structured-arrow category
  `StructuredArrow (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op`
  together with the distinguished object `op ⦋n,hn⦌ₘ` whose image under the inclusion is
  `op ⦋n⦌`;
- derived API: the canonical isomorphism identifying the limit of the diagram with its value at
  that initial object.

Source/core/bridge triage:
- `source-facing`: the degree-`n` limit computation for the opposite truncated over-category of
  `[n]`;
- `core/canonical`: `Limits.limitOfInitial`;
- `bridge/view`: the local `HasInitial` instance supplied by
  `StructuredArrow.mkIdInitial.hasInitial`, with no separate public specialization.
-/

section

variable {m n : ℕ} (hn : n ≤ m)

variable (U : SimplicialObject.Truncated C m)

/- The canonical initial object of the truncated over-category is the identity structured arrow on
`op ⦋n,hn⦌ₘ`. -/
recall StructuredArrow.mkIdInitial

/- The limit computation itself is the canonical owner theorem `Limits.limitOfInitial`. -/
recall limitOfInitial

/- Lemma 14.19.3: for an `m`-truncated simplicial object `U` and `n ≤ m`, the limit over the
opposite truncated over-category of `[n]` is canonically isomorphic to the degree-`n` object
`U _⦋n,hn⦌ₘ`. This is exactly the canonical owner `Limits.limitOfInitial`, with the only local
bridge being the chosen `HasInitial` structure on the indexing category coming from
`StructuredArrow.mkIdInitial.hasInitial`. -/
#check
  (by
    let Y := (SimplexCategory.Truncated.inclusion m).op.obj (op ⦋n,hn⦌ₘ)
    let F := StructuredArrow.proj (op ⦋n⦌) (SimplexCategory.Truncated.inclusion m).op ⋙ U
    letI : HasInitial (SimplexCategory.Truncated.matchingIndex m n) :=
      (StructuredArrow.mkIdInitial :
        IsInitial (StructuredArrow.mk (𝟙 Y) : SimplexCategory.Truncated.matchingIndex m n)).hasInitial
    simpa [F] using
      (limitOfInitial F :
        limit F ≅ F.obj (⊥_ (SimplexCategory.Truncated.matchingIndex m n))))

end

end CategoryTheory

/-! ### Lemma_14_19_4 (from Chap14) -/
open CategoryTheory
open CategoryTheory.SimplicialObject

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {n : ℕ}
variable [∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion n).op.HasPointwiseRightKanExtension F]

/- Domain-style sampling for Lemma 14.19.4:
- primary domain: simplicial-object truncation/coskeleton adjunctions;
- sampled owner API:
  `truncation`,
  `Truncated.cosk`,
  `coskAdj`,
  `Functor.HasPointwiseRightKanExtension`;
- best owner abstraction: the source-facing comparison morphism is the counit component of the
  adjunction `truncation n ⊣ Truncated.cosk n`, and the numbered lemma is the derived statement
  that this counit is an isomorphism under the owner-level pointwise right-Kan-extension
  hypothesis;
- primitive data: the ambient category, the truncation level `n`, and the pointwise right Kan
  extensions along `(SimplexCategory.Truncated.inclusion n).op`;
- derived API: for every `n`-truncated simplicial object `U`, the canonical morphism
  `(coskAdj n).counit.app U :
    (truncation n).obj ((Truncated.cosk n).obj U) ⟶ U`
  is an isomorphism.

Source/core/bridge triage:
- `source-facing`: the canonical map `truncation n (coskₙ U) ⟶ U`;
- `core/canonical`: the counit natural transformation `(coskAdj n).counit`;
- `bridge/view`: downstream hypotheses such as finite limits or finite connected limits may be used
  elsewhere to produce the pointwise right-Kan-extension owner assumptions, but this file should
  state the canonical owner layer directly rather than importing one particular bridge.

This item adds no new mathematics beyond the owner API, so it should remain a direct canonical
recall of the counit-isomorphism instance rather than a local theorem shell. -/

recall coskAdj

variable (U : SimplicialObject.Truncated C n)

/- Lemma 14.19.4: for an `n`-truncated simplicial object `U`, whenever the pointwise right Kan
extensions defining `Truncated.cosk n` exist, the canonical morphism
`truncation n ((Truncated.cosk n).obj U) ⟶ U`, namely the counit component
`((coskAdj n).counit.app U)`, is an isomorphism. -/
#check (inferInstance : IsIso ((coskAdj n).counit.app U))

/- Mathlib also provides the stronger owner-level statement that the whole counit natural
transformation of `truncation n ⊣ Truncated.cosk n` is an isomorphism. -/
#check (inferInstance : IsIso (coskAdj n).counit)

end CategoryTheory

/-! ### Lemma_14_19_5 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.IsLimit.OfNatIso
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory.Truncated
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.19.5:
- primary domain: representable cone functors and limits of the matching diagram for truncated
  simplicial objects;
- sampled owner API:
  `Functor.ranObjObjIsoLimit` (the earlier Chapter 14 limit owner for the same structured-arrow
  matching diagram),
  `Functor.cones`,
  `IsLimit.OfNatIso.limitCone`,
  `IsLimit.ofRepresentableBy`;
- best owner abstraction: the matching diagram
  `StructuredArrow.proj (op ⦋n + 1⦌) (inclusion n).op ⋙ U` together with its cone functor
  `matchingFamilyFunctor U`;
- primitive data: the truncated simplicial object `U` and the structured-arrow diagram indexing
  `(\Delta / [n + 1])_{\le n}^{opp}`;
- derived API: the matching-family presheaf and the canonical limit-cone theorem
  `IsLimit.ofRepresentableBy` specialized to that diagram.

Source/core/bridge triage:
- `source-facing`: the matching-family functor of `U`;
- `core/canonical`: `Functor.cones`, `IsLimit.ofRepresentableBy`, and
  `IsLimit.OfNatIso.limitCone`;
- `bridge/view`: the numbered lemma is just the owner theorem
  `IsLimit.ofRepresentableBy` applied to `matchingFamilyFunctor U`, so no separate bridge theorem
  should survive.
-/

section

variable {n : ℕ}

/-- The structured-arrow indexing category for the matching diagram in degree `n + 1`. -/
abbrev matchingIndex (n : ℕ) :=
  StructuredArrow (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op

/-- The source matching-family functor of Lemma 14.19.5, expressed canonically as the cone functor
on the matching diagram. -/
abbrev matchingFamilyFunctor (U : SimplicialObject.Truncated C n) :=
  (StructuredArrow.proj (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op ⋙ U).cones

/- Lemma 14.19.5: if the matching-family functor of `U` is representable by `U_succ`, then the
canonical cone on the structured-arrow matching diagram with cone point `U_succ` is a limit cone.
This is the direct owner theorem `IsLimit.ofRepresentableBy`, specialized to the cone functor
`matchingFamilyFunctor U`. -/
recall IsLimit.ofRepresentableBy

#check (IsLimit.ofRepresentableBy :
  {U : SimplicialObject.Truncated C n} → {U_succ : C} →
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ) →
      IsLimit (limitCone hrep))

end

end CategoryTheory

/-! ### Lemma_14_19_6 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.19.6:
- primary domain: one-step right-adjoint objects for truncation of truncated simplicial objects;
- sampled owner API:
  `Functor.rightAdjointObjIsDefined`,
  `Functor.rightAdjointObjIsDefined_iff`,
  `Functor.partialRightAdjointObj`,
  `Functor.partialRightAdjointHomEquiv`;
- best owner abstraction: the one-step truncation functor
  `Truncated.trunc C (n + 1) n : SimplicialObject.Truncated C (n + 1) ⥤
    SimplicialObject.Truncated C n`
  together with the representability owner
  `((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy (eqToHom htrunc)`;
- primitive data: the truncated simplicial object `U`, the proposed top-degree object `U_succ`,
  and the matching-family representability hypothesis
  `(matchingFamilyFunctor U).RepresentableBy U_succ`;
- derived API: existence of an `(n + 1)`-truncated extension with the prescribed truncation and
  top-degree term, and the owner-level consequence that the object `U` lies in the domain of
  definition of the partial right adjoint of `Truncated.trunc C (n + 1) n` under the weaker
  hypothesis that `matchingFamilyFunctor U` is representable.

Source/core/bridge triage:
- `source-facing`: the existence of a one-step extension of `U` with top term `U_succ`;
- `core/canonical`: `Functor.rightAdjointObjIsDefined` for `Truncated.trunc C (n + 1) n`;
- `bridge/view`: the specific witness object `V : SimplicialObject.Truncated C (n + 1)` together
  with the universal element `eqToHom htrunc :
    (Truncated.trunc C (n + 1) n).obj V ⟶ U` and the representability datum
  `((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy (eqToHom htrunc)`.

The old file packaged this bridge data into a bespoke structure. The refined file keeps the
source-facing existence theorem directly, but replaces the ad hoc `homEquiv` field by the canonical
representability owner and exposes the partial-right-adjoint consequence as a separate theorem. -/

-- Proof sketch: use the representing object for `matchingFamilyFunctor U` as the new degree
-- `n + 1` term, define the extra simplicial structure maps by the universal property of the
-- matching diagram, and then identify morphisms into the extension with morphisms into `U`
-- after truncation.
/-- Lemma 14.19.6: if the matching-family functor of an `n`-truncated simplicial object `U` is
representable by an object `U_{n+1}` of `C`, then `U` extends to an `(n + 1)`-truncated
simplicial object with degree-`n + 1` term `U_{n+1}` and with the expected adjointness between
maps into the extension and maps into `U` after truncation. The adjointness part is recorded by
the canonical representability owner for the one-step truncation functor. -/
theorem exists_truncated_extension_of_matching_family_representable
    {n : ℕ} (U : SimplicialObject.Truncated C n) (U_succ : C)
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ) :
    ∃ (V : SimplicialObject.Truncated C (n + 1))
      (htrunc : (Truncated.trunc C (n + 1) n).obj V = U),
        V.obj (op ⦋n + 1⦌ₙ₊₁) = U_succ ∧
          (((Truncated.trunc C (n + 1) n).op ⋙ yoneda.obj U).IsRepresentedBy
            (eqToHom htrunc)) := by
  sorry

-- Proof sketch: unpack the source-facing existence theorem and forget the explicit witness `V`;
-- the remaining content is exactly the owner predicate `rightAdjointObjIsDefined` for the
-- one-step truncation functor, which only depends on `matchingFamilyFunctor U` being
-- representable.
/-- The extension theorem of Lemma 14.19.6 implies that `U` lies in the domain of definition of
the partial right adjoint to one-step truncation. -/
theorem trunc_succ_rightAdjointObjIsDefined_of_matching_family_representable
    {n : ℕ} (U : SimplicialObject.Truncated C n)
    (hrep : (matchingFamilyFunctor U).IsRepresentable) :
    (Truncated.trunc C (n + 1) n).rightAdjointObjIsDefined U := by
  letI := hrep
  rw [Functor.rightAdjointObjIsDefined_iff]
  rcases exists_truncated_extension_of_matching_family_representable
      U (matchingFamilyFunctor U).reprX (matchingFamilyFunctor U).representableBy with
    ⟨V, htrunc, -, hV⟩
  simpa using hV.representableBy.isRepresentable

end CategoryTheory

/-! ### Remark_14_19_7 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open SimplexCategory
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Remark 14.19.7:
- primary domain: truncated simplicial objects and the matching-family cone functor for the next
  degree;
- sampled owner-side declarations:
  `SimplexCategory.Truncated.matchingIndex`,
  `matchingFamilyFunctor`,
  `Functor.cones`,
  `StructuredArrow.mk`,
  `StructuredArrow.w`;
- best owner abstraction: the chapter owner for matching data is `matchingFamilyFunctor U`, whose
  points are cones on the structured-arrow matching diagram. This remark is a `bridge/view`: it
  gives the degeneracy family inside that owner and records that the face maps are the coordinate
  projections coming from the objects indexed by the cofaces `δ_i`;
- primitive data: an `n`-truncated simplicial object `U`, an object `T`, a morphism
  `f : T ⟶ U _⦋n⦌ₙ`, and a degeneracy index `j : Fin (n + 1)`;
- derived API: the canonical matching-family point determined by `f`, its coordinate projections,
  and in degree `0` the identification of those two coordinates with `(f, f)`.

Source/core/bridge triage:
- `source-facing`: the explicit tuple of maps obtained from the simplicial identities;
- `core/canonical`: `matchingFamilyFunctor U`;
- `bridge/view`: the remark identifies the source tuple with the owner-side matching-family point
  and exposes its coordinates through the face objects. -/

/-- The structured-arrow object corresponding to the `i`-th coface `δ_i : [n] ⟶ [n + 1]`. -/
abbrev matchingFaceObject {n : ℕ} (i : Fin (n + 2)) :
    matchingIndex n :=
  StructuredArrow.mk
    (show op ⦋n + 1⦌ ⟶
        (SimplexCategory.Truncated.inclusion n).op.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n)) from
      (SimplexCategory.δ i).op)

/-- The truncated simplex underlying a matching-diagram index object. -/
private abbrev matchingIndexSimplex {n : ℕ} (A : matchingIndex n) :
    SimplexCategory.Truncated n :=
  A.right.unop

/-- The simplex map underlying a morphism in the matching-diagram index category. -/
private abbrev matchingIndexRightHom {n : ℕ} {A B : matchingIndex n} (g : A ⟶ B) :
    matchingIndexSimplex B ⟶ matchingIndexSimplex A :=
  g.right.unop

/-- For an index object `α : [k] ⟶ [n + 1]` in the matching diagram, composing `α` with `σ_j`
gives the induced map `[k] ⟶ [n]`. -/
private abbrev matchingDegeneracyMap {n : ℕ} (j : Fin (n + 1))
    (A : matchingIndex n) :
    matchingIndexSimplex A ⟶ (⦋n⦌ₙ : SimplexCategory.Truncated n) :=
  Hom.tr (A.hom.unop ≫ SimplexCategory.σ j) (matchingIndexSimplex A).property (by simp)

private theorem matchingDegeneracyMap_naturality {n : ℕ} (j : Fin (n + 1))
    {A B : matchingIndex n} (g : A ⟶ B) :
    matchingIndexRightHom g ≫ matchingDegeneracyMap j A = matchingDegeneracyMap j B := by
  change Hom.tr ((matchingIndexRightHom g).hom ≫ A.hom.unop ≫ SimplexCategory.σ j) _ _ =
    Hom.tr (B.hom.unop ≫ SimplexCategory.σ j) _ _
  exact congrArg
    (fun k ↦ Hom.tr (k ≫ SimplexCategory.σ j) (matchingIndexSimplex B).property (by simp))
    (congrArg Quiver.Hom.unop (StructuredArrow.w g))

/-- Remark 14.19.7: the `j`-th degeneracy map on `T`-valued points of the matching-family model
for the degree-`n + 1` term is the canonical point of `matchingFamilyFunctor U` whose component at
an index object `α : [k] ⟶ [n + 1]` is obtained by precomposing `f` with `α ≫ σ_j`. -/
def matchingDegeneracyFamily {n : ℕ} (U : SimplicialObject.Truncated C n) {T : C}
    (j : Fin (n + 1)) (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    (matchingFamilyFunctor U).obj (op T) where
  app A := f ≫ U.map (matchingDegeneracyMap j A).op
  naturality := by
    intro A B g
    let h :=
      congrArg (fun k ↦ f ≫ U.map k)
        (congrArg Quiver.Hom.op (matchingDegeneracyMap_naturality j g))
    simpa [Functor.comp_map, Functor.const_obj_map, Category.assoc] using
      h.symm

/-- The `i`-th coordinate of the degeneracy family is the textbook map
`f ≫ U(δ_i ≫ σ_j)`. -/
theorem matchingDegeneracyFamily_app_matchingFaceObject {n : ℕ}
    (U : SimplicialObject.Truncated C n)
    {T : C} (i : Fin (n + 2)) (j : Fin (n + 1))
    (f : T ⟶ U.obj (op (⦋n⦌ₙ : SimplexCategory.Truncated n))) :
    (matchingDegeneracyFamily U j f).app (matchingFaceObject i) =
      f ≫ U.map (Hom.tr (SimplexCategory.δ i ≫ SimplexCategory.σ j)).op := by
  simp [matchingDegeneracyFamily, matchingDegeneracyMap, matchingFaceObject, matchingIndexSimplex]

-- Proof sketch: when `n = 0` there is only one degeneracy index `j = 0`, and both composites
-- `δ_0 ≫ σ_0` and `δ_1 ≫ σ_0` are identities by the two parts of the third simplicial identity.
/-- In degree `0`, the two face projections of the explicit degeneracy family are both `f`. -/
theorem matchingDegeneracyFamily_zero (U : SimplicialObject.Truncated C 0) {T : C}
    (f : T ⟶ U.obj (op (⦋0⦌₀ : SimplexCategory.Truncated 0))) :
    (fun i : Fin 2 ↦ (matchingDegeneracyFamily U 0 f).app (matchingFaceObject i)) =
      fun _ : Fin 2 ↦ f := by
  funext i
  fin_cases i
  · rw [matchingDegeneracyFamily_app_matchingFaceObject]
    have hδ :
        (Hom.tr (SimplexCategory.δ 0 ≫ SimplexCategory.σ 0) :
          (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀) =
          𝟙 (⦋0⦌₀ : SimplexCategory.Truncated 0) := by
      simpa using congrArg
        (fun k ↦ (Hom.tr k : (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀))
        (show SimplexCategory.δ (Fin.castSucc 0) ≫ SimplexCategory.σ 0 = 𝟙 ⦋0⦌ from
          SimplexCategory.δ_comp_σ_self)
    simpa [hδ]
  · rw [matchingDegeneracyFamily_app_matchingFaceObject]
    have hδ :
        (Hom.tr (SimplexCategory.δ 1 ≫ SimplexCategory.σ 0) :
          (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀) =
          𝟙 (⦋0⦌₀ : SimplexCategory.Truncated 0) := by
      simpa using congrArg
        (fun k ↦ (Hom.tr k : (⦋0⦌₀ : SimplexCategory.Truncated 0) ⟶ ⦋0⦌₀))
        (show SimplexCategory.δ (0 : Fin 1).succ ≫ SimplexCategory.σ 0 = 𝟙 ⦋0⦌ from
          SimplexCategory.δ_comp_σ_succ)
    simpa [hδ]

end CategoryTheory

/-! ### Remark_14_19_8 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Functor
open Opposite
open SimplexCategory
open SimplexCategory.Truncated
open scoped Simplicial
open scoped SimplexCategory.Truncated

noncomputable section

universe u

namespace CategoryTheory

/- Domain-style sampling for Remark 14.19.8:
- primary domain: one-step extensions of truncated simplicial sets, their matching objects, and
  representable presheaves on `Type`;
- sampled owner API:
  `SimplicialObject.Truncated.tilde`,
  `SimplicialObject.Truncated.tildeHomEquiv`,
  `matchingFamilyFunctor`,
  `Functor.RepresentableBy`,
  `Functor.RepresentableBy.uniqueUpToIso`,
  `Functor.ranObjObjIsoLimit`,
  `SimplexCategory.eq_comp_δ_of_not_surjective`;
- best owner abstraction: the canonical one-step extension `SimplicialObject.Truncated.tilde U`,
  whose universal property is `SimplicialObject.Truncated.tildeHomEquiv`; the explicit matching
  faces are only a source-facing top-degree model for the matching object represented by that
  extension;
- primitive data: the truncated simplicial set `U`, together with its explicit top-degree matching
  simplices;
- derived API: the inverse-to-restriction map into `tilde U`, and the explicit representability of
  the matching-family functor by the matching-face type.

Source/core/bridge triage:
- `source-facing`: the canonical `(n + 1)`-truncated simplicial set `\tilde U` and the inverse to
  restriction into it;
- `core/canonical`: `SimplicialObject.Truncated.tilde U` with
  `SimplicialObject.Truncated.tildeHomEquiv`;
- `bridge/view`: the explicit pair/subtype `simplicialMatchingFaces U`, which identifies the
  top-degree matching object represented by `\tilde U` through `matchingFamilyFunctor U`. -/

/-- The top simplex in `Δ≤n`. -/
private abbrev simplicialMatchingTopSimplex (n : ℕ) : SimplexCategory.Truncated n :=
  ⦋n⦌ₙ

/-- The predecessor simplex `[n]` regarded as an object of `Δ≤(n + 1)`. -/
private abbrev simplicialMatchingPredSimplex (n : ℕ) : SimplexCategory.Truncated (n + 1) :=
  ⟨SimplexCategory.mk n, Nat.le_succ n⟩

/-- The face map `d_i^(n + 1) : U_{n + 1} ⟶ U_n` written as a morphism in the truncated simplex
category. -/
private def simplicialMatchingFaceMap (n : ℕ) (i : Fin (n + 2)) :
    simplicialMatchingPredSimplex n ⟶ simplicialMatchingTopSimplex (n + 1) :=
  Hom.tr (SimplexCategory.δ i)

-- Proof sketch: if `i < j < n + 2`, then `i < n + 1`, so `i` determines a valid face index
-- `d_i^n`.
/-- The left-hand face index occurring in the matching-family relation. -/
private theorem simplicialMatchingLeftFaceIndex_isLt {n : ℕ} {i j : Fin (n + 2)}
    (hij : i < j) : i.1 < n + 1 := sorry

/-- The face index `i` in the relation `d_{j-1}^n(f_i) = d_i^n(f_j)`. -/
private def simplicialMatchingLeftFaceIndex {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) :
    Fin (n + 1) :=
  ⟨i.1, simplicialMatchingLeftFaceIndex_isLt hij⟩

-- Proof sketch: if `i < j < n + 2`, then `j` is positive and `j - 1 < n + 1`, so `j - 1`
-- determines the face index `d_{j-1}^n`.
/-- The right-hand face index occurring in the matching-family relation. -/
private theorem simplicialMatchingRightFaceIndex_isLt {n : ℕ} {i j : Fin (n + 2)}
    (hij : i < j) : j.1 - 1 < n + 1 := sorry

/-- The face index `j - 1` in the relation `d_{j-1}^n(f_i) = d_i^n(f_j)`. -/
private def simplicialMatchingRightFaceIndex {n : ℕ} {i j : Fin (n + 2)} (hij : i < j) :
    Fin (n + 1) :=
  ⟨j.1 - 1, simplicialMatchingRightFaceIndex_isLt hij⟩

/-- The explicit matching-face object of Remark 14.19.8: for `n = 0` it is the pair of
`0`-simplices, while for `n + 1` it is the subtype of compatible `(n + 3)`-tuples of
`(n + 1)`-simplices. -/
def simplicialMatchingFaces {n : ℕ} (U : SSet.Truncated n) : Type u :=
  match n with
  | 0 =>
      Fin 2 → U.obj (op (simplicialMatchingTopSimplex 0))
  | m + 1 =>
      { f : Fin (m + 3) → U.obj (op (simplicialMatchingTopSimplex (m + 1))) //
          ∀ {i j : Fin (m + 3)}, (hij : i < j) →
            U.map (simplicialMatchingFaceMap m (simplicialMatchingRightFaceIndex hij)).op (f i) =
              U.map
                (simplicialMatchingFaceMap m (simplicialMatchingLeftFaceIndex hij)).op
                (f j) }

private def simplicialMatchingFaceValues {n : ℕ} (U : SSet.Truncated n)
    (f : simplicialMatchingFaces U) :
    Fin (n + 2) → U.obj (op (simplicialMatchingTopSimplex n)) := by
  match n with
  | 0 =>
      exact f
  | _ + 1 =>
      exact f.1

private abbrev matchingIndexSimplex {n : ℕ} (A : matchingIndex n) :
    SimplexCategory.Truncated n :=
  A.right.unop

private abbrev matchingIndexHom {n : ℕ} (A : matchingIndex n) :=
  A.hom.unop

private structure SimplicialMatchingFaceFactorization {n : ℕ} (A : matchingIndex n) where
  face : Fin (n + 2)
  map : (matchingIndexSimplex A).obj ⟶ ⦋n⦌
  fac : matchingIndexHom A = map ≫ SimplexCategory.δ face

private theorem matchingIndex_not_surjective {n : ℕ} (A : matchingIndex n) :
    ¬ Function.Surjective (matchingIndexHom A).toOrderHom := by
  intro hsurj
  have hle : n + 1 ≤ (matchingIndexSimplex A).obj.len := by
    letI : Epi (matchingIndexHom A) := (SimplexCategory.epi_iff_surjective).2 hsurj
    simpa using (SimplexCategory.len_le_of_epi (matchingIndexHom A))
  exact Nat.not_succ_le_self n (hle.trans (matchingIndexSimplex A).property)

private noncomputable def simplicialMatchingFaceFactorization {n : ℕ} (A : matchingIndex n) :
    SimplicialMatchingFaceFactorization A := by
  classical
  let h := SimplexCategory.eq_comp_δ_of_not_surjective (matchingIndexHom A)
    (matchingIndex_not_surjective A)
  let face := Classical.choose h
  let hmap := Classical.choose_spec h
  let map := Classical.choose hmap
  let fac := Classical.choose_spec hmap
  exact ⟨face, map, fac⟩

private abbrev simplicialMatchingChosenFace {n : ℕ} (A : matchingIndex n) : Fin (n + 2) :=
  (simplicialMatchingFaceFactorization A).face

private def simplicialMatchingChosenMap {n : ℕ} (A : matchingIndex n) :
    matchingIndexSimplex A ⟶ ⦋n⦌ₙ :=
  Hom.tr (simplicialMatchingFaceFactorization A).map (matchingIndexSimplex A).property (by simp)

private def simplicialMatchingHomToMatchingFamily
    {n : ℕ} (U : SSet.Truncated n) (T : Type u) :
    (T ⟶ simplicialMatchingFaces U) → (matchingFamilyFunctor U).obj (op T) :=
  fun g ↦
      { app := fun A t ↦
          U.map (simplicialMatchingChosenMap A).op
            (simplicialMatchingFaceValues U (g t) (simplicialMatchingChosenFace A))
        naturality := by
          intro A B f
          ext t
          sorry }

private def simplicialMatchingMatchingFamilyToHom
    {n : ℕ} (U : SSet.Truncated n) (T : Type u) :
    (matchingFamilyFunctor U).obj (op T) → (T ⟶ simplicialMatchingFaces U) :=
  match n with
  | 0 =>
      fun x ↦ fun t ↦ fun i ↦ x.app (CategoryTheory.matchingFaceObject i) t
  | _ + 1 =>
      fun x ↦
        fun t ↦
          ⟨fun i ↦ x.app (CategoryTheory.matchingFaceObject i) t, fun hij ↦ by sorry⟩

/- Remark 14.19.8: the explicit pair/subtype `simplicialMatchingFaces U` is a source-facing model
for the canonical matching object of `U`; its universal property is the owner-side Hom
equivalence for `matchingFamilyFunctor U`. -/
noncomputable def simplicialMatchingFaces_homEquiv
    {n : ℕ} (U : SSet.Truncated n) (T : Type u) :
    (T ⟶ simplicialMatchingFaces U) ≃ (matchingFamilyFunctor U).obj (op T) where
  toFun := simplicialMatchingHomToMatchingFamily U T
  invFun := simplicialMatchingMatchingFamilyToHom U T
  left_inv := by
    intro g
    sorry
  right_inv := by
    intro x
    sorry

-- Proof sketch: the explicit tuple model is the source-facing presentation of the canonical
-- matching-family cone functor `matchingFamilyFunctor U`; the representability datum is obtained
-- from the universal Hom-equivalence above.
/-- The explicit matching-face object represents the canonical matching-family functor of `U`. -/
noncomputable def simplicialMatchingFaces_representableBy
    {n : ℕ} (U : SSet.Truncated n) :
    (matchingFamilyFunctor U).RepresentableBy (simplicialMatchingFaces U) where
  homEquiv := fun {X} ↦ simplicialMatchingFaces_homEquiv U X
  homEquiv_comp := by
    intro X X' f g
    sorry

private noncomputable def tildeTop_representableBy
    {n : ℕ} (U : SSet.Truncated n) :
    (matchingFamilyFunctor U).RepresentableBy
      ((SimplicialObject.Truncated.tilde U).obj
        (op (simplicialMatchingTopSimplex (n + 1)))) := by
  let Y : (SimplexCategory.Truncated (n + 1))ᵒᵖ :=
    op (simplicialMatchingTopSimplex (n + 1))
  let e :
      StructuredArrow Y (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ≌
        StructuredArrow ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
          (SimplexCategory.Truncated.inclusion n).op :=
    (StructuredArrow.post Y (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op
        (SimplexCategory.Truncated.inclusion (n + 1)).op).asEquivalence.trans
      (StructuredArrow.mapNatIso (Iso.refl _ :
        (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙
            (SimplexCategory.Truncated.inclusion (n + 1)).op ≅
          (SimplexCategory.Truncated.inclusion n).op))
  let w :
      e.functor ⋙
          StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
            (SimplexCategory.Truncated.inclusion n).op ⋙ U ≅
        StructuredArrow.proj Y (SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op ⋙
          U :=
    Iso.refl _
  let hlim :=
    Limits.limit.isLimit
      (StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
        (SimplexCategory.Truncated.inclusion n).op ⋙ U)
  let hrep := Limits.IsLimit.representableBy hlim
  let eObj :
      ((SimplicialObject.Truncated.tilde U).obj
        (op (simplicialMatchingTopSimplex (n + 1)))) ≅
        (Limits.limit.cone
          (StructuredArrow.proj ((SimplexCategory.Truncated.inclusion (n + 1)).op.obj Y)
            (SimplexCategory.Truncated.inclusion n).op ⋙ U)).pt :=
    ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.ranObjObjIsoLimit U Y) ≪≫
      Limits.HasLimit.isoOfEquivalence e w
  simpa [matchingFamilyFunctor, SimplicialObject.Truncated.tilde] using
    hrep.ofIsoObj eObj

/-- The explicit matching-face model is canonically isomorphic to the top-degree term of the
one-step extension `\tilde U`. -/
noncomputable def simplicialMatchingFacesIsoTildeTop
    {n : ℕ} (U : SSet.Truncated n) :
    simplicialMatchingFaces U ≅
      (SimplicialObject.Truncated.tilde U).obj
        (op (⦋n + 1⦌ₙ₊₁ : SimplexCategory.Truncated (n + 1))) :=
  Functor.RepresentableBy.uniqueUpToIso
    (simplicialMatchingFaces_representableBy U)
    (tildeTop_representableBy U)

section Tilde

variable {n : ℕ} (U : SSet.Truncated n) (V : SSet.Truncated (n + 1))

/- Remark 14.19.8: the canonical one-step extension `\tilde U` of an `n`-truncated simplicial set
is the owner `SimplicialObject.Truncated.tilde U`. -/
#check (SimplicialObject.Truncated.tilde U : SSet.Truncated (n + 1))

/- Its universal property is the symmetric form of the canonical Hom-set equivalence
`U.tildeHomEquiv V`, whose inverse is the source map `Mor(sk_n V, U) → Mor(V, \tilde U)`. -/
#check (U.tildeHomEquiv V).symm

end Tilde

end CategoryTheory

/-! ### Remark_14_19_9 (from Chap14) -/
open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.SimplicialObject

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable [∀ n : ℕ, ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.incl n (n + 1)).op.HasRightKanExtension F]

/- Domain-style sampling for Remark 14.19.9:
- primary domain: truncated simplicial objects, one-step coskeleton stages, and right Kan
  extensions along the inclusions `Δ≤n ↪ Δ≤(n + 1)`;
- sampled owner declarations:
  `Truncated.trunc`,
  `Functor.ran`,
  `Functor.ranAdjunction`,
  `Truncated.cosk`,
  `coskAdj`;
- best owner abstraction: the source-facing stage `U^{n + 1}` is the right Kan extension of
  `U^n` along `SimplexCategory.Truncated.incl n (n + 1)`, and the full `m`-coskeleton is the
  core canonical endpoint obtained after passing from these stages to all simplices;
- primitive data: an `m`-truncated simplicial object `U` and the one-step right Kan extensions
  along `Δ≤n ↪ Δ≤(n + 1)`;
- derived API: the one-step stage `\tilde U`, the recursive family `U^{m + k}`, the Hom-set
  equivalences expressing the universal property of each stage, and the bridge from those stages
  to the full owner `Truncated.cosk`.

Source/core/bridge triage:
- `source-facing`: the recursive stage family `U^m = U`, `U^{n + 1} = \tilde U^n`, together with
  the formulas `Mor_{Simp_{m + k}}(V, U^{m + k}) ≃ Mor_{Simp_m}(sk_m V, U)` and
  `Mor_{Simp(C)}(V, cosk_m U) ≃ Mor_{Simp_m(C)}(sk_m V, U)`;
- `core/canonical`: the generic right Kan extension owner `Functor.ran` and its adjunction
  `Functor.ranAdjunction`, plus the eventual full owner `Truncated.cosk` with adjunction
  `coskAdj`;
- `bridge/view`: the thin abbreviation `tilde`, which keeps the source surface while delegating
  all universal properties to the owner adjunctions, together with the derived comparison between
  `stage U k` and `cosk_m U` on Hom-sets. -/

namespace SimplicialObject.Truncated

/-- The one-step stage `\tilde U` of an `n`-truncated simplicial object, defined as the right Kan
extension of `U` along `Δ≤n ↪ Δ≤(n + 1)`. This is the source-facing bridge from the recursive
construction to the canonical owner `Functor.ran`. -/
abbrev tilde {n : ℕ} (U : SimplicialObject.Truncated C n) :
    SimplicialObject.Truncated C (n + 1) :=
  ((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.ran).obj U

/-- The one-step universal property of `\tilde U`: morphisms into the one-step stage correspond to
morphisms from the truncation back to `U`. This is the source-facing bridge to the canonical
Hom-set equivalence of the right Kan extension adjunction. -/
noncomputable abbrev tildeHomEquiv {n : ℕ} (U : SimplicialObject.Truncated C n)
    (V : SimplicialObject.Truncated C (n + 1)) :
    (V ⟶ tilde U) ≃ ((Truncated.trunc C (n + 1) n (Nat.le_succ n)).obj V ⟶ U) :=
  (((SimplexCategory.Truncated.incl n (n + 1) (Nat.le_succ n)).op.ranAdjunction C).homEquiv
    V U).symm

section OneStep

variable {n : ℕ} (U : SimplicialObject.Truncated C n) (V : SimplicialObject.Truncated C (n + 1))

/- Remark 14.19.9, one-step universal property: morphisms from an `(n + 1)`-truncated simplicial
object `V` to `\tilde U` are naturally equivalent to morphisms from the `n`-truncation of `V` to
`U`. This is the symmetric form of the canonical Hom-set equivalence of the right Kan extension
adjunction along `Δ≤n ↪ Δ≤(n + 1)`. -/
#check (tildeHomEquiv U V :
  (V ⟶ tilde U) ≃ ((Truncated.trunc C (n + 1) n (Nat.le_succ n)).obj V ⟶ U))

end OneStep

/-- The recursive stages of Remark 14.19.9. Here `stage U k` is the source's object
`U^{m + k}` when `U : SimplicialObject.Truncated C m`. -/
def stage {m : ℕ} (U : SimplicialObject.Truncated C m) (k : ℕ) :
    SimplicialObject.Truncated C (m + k) :=
  match k with
  | 0 => U
  | k + 1 => tilde (stage U k)

@[simp] theorem stage_zero {m : ℕ} (U : SimplicialObject.Truncated C m) :
    stage U 0 = U := rfl

@[simp] theorem stage_succ {m : ℕ} (U : SimplicialObject.Truncated C m) (k : ℕ) :
    stage U (k + 1) = tilde (stage U k) := rfl

/-- Remark 14.19.9, recursive universal formula: for every `k`, morphisms in `Simp_{m + k}` into
the stage `U^{m + k}` are naturally equivalent to morphisms from the `m`-truncation to `U`. This
is the source's all-`n` statement, written in the exact canonical equivalent form `n = m + k`. -/
noncomputable def stageHomEquiv {m : ℕ} (U : SimplicialObject.Truncated C m) (k : ℕ)
    (V : SimplicialObject.Truncated C (m + k)) :
    (V ⟶ stage U k) ≃ ((Truncated.trunc C (m + k) m (Nat.le_add_right m k)).obj V ⟶ U) :=
  match k with
  | 0 => by
      simpa [stage] using Equiv.refl (V ⟶ U)
  | k + 1 => by
      simpa [stage] using (tildeHomEquiv (stage U k) V).trans (stageHomEquiv U k _)

section CoskeletonBridge

variable {m : ℕ}
variable [∀ F : (SimplexCategory.Truncated m)ᵒᵖ ⥤ C,
  (SimplexCategory.Truncated.inclusion m).op.HasRightKanExtension F]

/-- Remark 14.19.9, bridge from the recursive stage `U^{m + k}` to the canonical full owner
`cosk_m U`: for any simplicial object `V`, maps `V ⟶ cosk_m U` are naturally equivalent to maps
from the `(m + k)`-truncation of `V` to the recursive stage `U^{m + k}`. -/
noncomputable def homEquivStage (U : SimplicialObject.Truncated C m) (k : ℕ)
    (V : SimplicialObject C) :
    (V ⟶ (Truncated.cosk m).obj U) ≃ ((truncation (m + k)).obj V ⟶ stage U k) := by
  simpa using
    (((coskAdj m).homEquiv V U).symm.trans (stageHomEquiv U k ((truncation (m + k)).obj V)).symm)

/- Remark 14.19.9 also recalls the endpoint `k = 0`, namely the canonical Hom-set equivalence of
the adjunction `truncation m ⊣ Truncated.cosk m`. -/
variable (U : SimplicialObject.Truncated C m) (V : SimplicialObject C)

#check ((((coskAdj m).homEquiv V U).symm :
  (V ⟶ (Truncated.cosk m).obj U) ≃ ((truncation m).obj V ⟶ U)))

end CoskeletonBridge

end SimplicialObject.Truncated

end CategoryTheory

/-! ### Lemma_14_19_10 (from Chap14) -/
open Opposite
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.SimplicialObject
open SimplexCategory.Truncated (incl inclCompInclusion)

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Lemma 14.19.10:
- primary domain: simplicial-object truncation/coskeleton adjunctions and coskeletality;
- sampled owner declarations:
  `truncation`,
  `Truncated.trunc`,
  `Functor.ranAdjunction`,
  `coskAdj`,
  `SimplicialObject.IsCoskeletal`,
  `SimplicialObject.isCoskeletal_iff_isIso`;
- best owner abstraction: `coskAdj n` for part (1), the generic right Kan extension adjunction
  `((SimplexCategory.Truncated.incl n m h).op.ranAdjunction C)` together with the owner-scoped
  source-facing bridge `SimplicialObject.Truncated.trunc.adj`, whose internal comparison is
  `((SimplexCategory.Truncated.incl n m h).op.ran) ≅ Truncated.cosk n ⋙ truncation m`
  for part (2), and the owner predicate `SimplicialObject.IsCoskeletal n` for the monotonicity
  statement behind parts (3) and (4);
- primitive data: the truncation functors, the inclusion `Δ≤n ↪ Δ≤m`, and the right Kan
  extensions defining the relevant coskeleta;
- derived API: the adjunctions for truncation and further truncation, plus the unit-isomorphism
  consequences phrased via `isCoskeletal_iff_isIso`.

Source/core/bridge triage:
- `source-facing`: the textbook adjunction for further truncation, whose right adjoint is the
  `m`-truncation of the `n`-coskeleton, together with the unit-isomorphism statements
  `U ⟶ cosk_n sk_n U` and their monotonicity in `n`;
- `core/canonical`: `coskAdj`, `Functor.ranAdjunction`, and `SimplicialObject.IsCoskeletal`;
- `bridge/view`: `SimplicialObject.isCoskeletal_iff_isIso`, which converts the owner predicate to
  the source-facing unit-isomorphism form, together with the finite-limit bridge supplying the
  right Kan extensions along `SimplexCategory.Truncated.incl`.

The file should therefore reuse `coskAdj` directly for part (1), expose the source-facing right
adjoint `Truncated.cosk n ⋙ truncation m` for part (2) through the owner-scoped bridge
`SimplicialObject.Truncated.trunc.adj`, and keep the unit-isomorphism lemmas as thin companions to
the owner-level coskeletality statements. -/

-- Proof sketch: finite limits give the pointwise right Kan extensions along
-- `(SimplexCategory.Truncated.inclusion n).op` needed to construct the right Kan extension functor,
-- and hence the right adjoint to `truncation n`.
section

variable (n : ℕ)
variable [HasFiniteLimits C]

recall coskAdj

/- Lemma 14.19.10 (1): if `C` has finite limits, then the `n`-truncation functor
`truncation n : SimplicialObject C ⥤ SimplicialObject.Truncated C n` is a left adjoint, with right
adjoint given by the `n`-coskeleton functor. This is direct owner-level API from the adjunction
`coskAdj n : truncation n ⊣ Truncated.cosk n`. -/
#check (coskAdj n :
  (truncation n : SimplicialObject C ⥤ SimplicialObject.Truncated C n) ⊣ Truncated.cosk n)

end

private noncomputable def truncInclStructuredArrowEquiv (n m : ℕ) (h : n ≤ m)
    (Y : (SimplexCategory.Truncated m)ᵒᵖ) :
    StructuredArrow Y (incl n m h).op ≌
      StructuredArrow ((SimplexCategory.Truncated.inclusion m).op.obj Y)
        (SimplexCategory.Truncated.inclusion n).op :=
  (StructuredArrow.post Y (incl n m h).op (SimplexCategory.Truncated.inclusion m).op).asEquivalence.trans
    (StructuredArrow.mapNatIso
      ((Functor.opComp (incl n m h) (SimplexCategory.Truncated.inclusion m)).symm ≪≫
        NatIso.op (inclCompInclusion h).symm))

/- Internal bridge: along `Δ≤n ↪ Δ≤m`, the right Kan extensions needed for the generic
`ranAdjunction` are pointwise because the corresponding structured-arrow indexing category is
canonically equivalent to the one already handled by Lemma `14.19.2` for `Δ≤n ↪ Δ`. This supports
only the source-facing adjunction `SimplicialObject.Truncated.trunc.adj`. -/
private instance truncIncl_hasPointwiseRightKanExtension (n m : ℕ) (h : n ≤ m)
    [HasFiniteLimits C] (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (incl n m h).op.HasPointwiseRightKanExtension F := by
  intro Y
  let e := truncInclStructuredArrowEquiv n m h Y
  change HasLimit
    (e.functor ⋙
      StructuredArrow.proj ((SimplexCategory.Truncated.inclusion m).op.obj Y)
        (SimplexCategory.Truncated.inclusion n).op ⋙ F)
  infer_instance

section Coskeleton

variable {n m : ℕ}

namespace SimplicialObject.Truncated

section

variable [HasFiniteLimits C]

/-- Helper for Lemma 14.19.10: after passing to opposites, the inclusion
`Δ≤n ↪ Δ≤m ↪ Δ` identifies with the standard inclusion `Δ≤n ↪ Δ`. -/
private noncomputable def inclCompInclusionOpIso {n m : ℕ} (h : n ≤ m) :
    (SimplexCategory.Truncated.incl n m h).op ⋙
      (SimplexCategory.Truncated.inclusion m).op ≅
    (SimplexCategory.Truncated.inclusion n).op :=
  Functor.opComp (SimplexCategory.Truncated.incl n m h)
      (SimplexCategory.Truncated.inclusion m) ≪≫
    NatIso.op (inclCompInclusion h)

/-- Helper for Lemma 14.19.10: the counit of `truncation n ⊣ Truncated.cosk n` should be an
isomorphism on every `n`-truncated simplicial object, using only fully faithfulness of
`(SimplexCategory.Truncated.inclusion n).op` and the universal property of the right Kan
extension. -/
private theorem cosk_counit_app_isIso (U : SimplicialObject.Truncated C n) :
    IsIso ((coskAdj n).counit.app U) := by
  -- Finite limits supply the pointwise right Kan extensions behind `Truncated.cosk`,
  -- so the generic counit of `coskAdj n` is already an isomorphism.
  infer_instance

omit [HasFiniteLimits C] in
/-- Helper for Lemma 14.19.10: coskeletality is preserved under isomorphism. -/
private theorem isCoskeletal_of_iso_aux {k : ℕ} {X Y : SimplicialObject C} (e : X ≅ Y)
    (hX : X.IsCoskeletal k) :
    Y.IsCoskeletal k := by
  -- Rewrite both sides as right Kan extension statements and transport along the object isomorphism.
  rw [SimplicialObject.isCoskeletal_iff] at hX ⊢
  exact (Functor.isRightKanExtension_iff_of_iso₂
    (𝟙 ((SimplexCategory.Truncated.inclusion k).op ⋙ X))
    (𝟙 ((SimplexCategory.Truncated.inclusion k).op ⋙ Y))
    (Functor.isoWhiskerLeft (SimplexCategory.Truncated.inclusion k).op e) e
    (by simp [Functor.isoWhiskerLeft_hom])).1 hX

/-- The canonical `n`-coskeleton of an `n`-truncated simplicial object is canonically
`n`-coskeletal. This is the owner-level instance form of the fact that the unit of
`truncation n ⊣ Truncated.cosk n` is an isomorphism on the image of `Truncated.cosk n`. -/
instance instIsCoskeletalCosk (U : SimplicialObject.Truncated C n) :
    ((Truncated.cosk n).obj U).IsCoskeletal n := by
  -- Transport the canonical counit-based right Kan extension of `coskₙ U`
  -- across the counit isomorphism so that the comparison map becomes the identity.
  letI : IsIso ((coskAdj n).counit.app U) := cosk_counit_app_isIso U
  rw [SimplicialObject.isCoskeletal_iff]
  let e :
      U ≅ (truncation n).obj ((Truncated.cosk n).obj U) :=
    (asIso ((coskAdj n).counit.app U)).symm
  let α :
      (SimplexCategory.Truncated.inclusion n).op ⋙ (Truncated.cosk n).obj U ⟶ U :=
    (coskAdj n).counit.app U
  let α' :
      (SimplexCategory.Truncated.inclusion n).op ⋙ (Truncated.cosk n).obj U ⟶
        (truncation n).obj ((Truncated.cosk n).obj U) :=
    𝟙 _
  -- The counit is already universal, and the target isomorphism turns it into the identity map.
  exact
    (Functor.isRightKanExtension_iff_of_iso₂ α α' e (Iso.refl _)
      (by
        ext i
        have hi :
            𝟙 (((Truncated.cosk n).obj U).obj (op (unop i).obj)) =
              ((coskAdj n).counit.app U).app i ≫ e.hom.app i := by
          rw [show e.hom.app i = (asIso ((coskAdj n).counit.app U)).inv.app i by rfl]
          exact ((asIso ((coskAdj n).counit.app U)).hom_inv_id_app i).symm
        simpa [α, α'] using hi))
      |>.1 (by
        -- Unfold the `Truncated.cosk` and `coskAdj` abbreviations to recover the generic
        -- `ranCounit` right-Kan-extension instance.
        change (((SimplexCategory.Truncated.inclusion n).op.ran).obj U).IsRightKanExtension
          (((SimplexCategory.Truncated.inclusion n).op.ranAdjunction C).counit.app U)
        rw [Functor.ranAdjunction_counit]
        infer_instance)

end

section

variable [HasFiniteLimits C]

/-- Helper for Lemma 14.19.10: the generic right Kan extension along `Δ≤n ↪ Δ≤m` exists as soon
as the standard inclusion `Δ≤n ↪ Δ` admits right Kan extensions for all diagrams. -/
private instance incl_hasRightKanExtension_of_inclusion (h : n ≤ m)
    (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C) :
    (SimplexCategory.Truncated.incl n m h).op.HasRightKanExtension F := by
  -- Finite limits give pointwise right Kan extensions along `Δ≤n ↪ Δ≤m`,
  -- and the chosen right Kan extension follows from that pointwise construction.
  infer_instance

/-- Helper for Lemma 14.19.10: composing the right Kan extension along `Δ≤n ↪ Δ≤m` with the
`m`-coskeleton recovers the `n`-coskeleton. This is the right-adjoint-uniqueness comparison
needed for monotonicity of coskeletality. -/
private noncomputable def ran_comp_cosk_iso_of_le (h : n ≤ m) :
    (((SimplexCategory.Truncated.incl n m h).op.ran :
        SimplicialObject.Truncated C n ⥤ SimplicialObject.Truncated C m) ⋙
      Truncated.cosk m) ≅
    Truncated.cosk n := by
  -- The composed left adjoint is still `truncation n`, so uniqueness of right adjoints identifies
  -- the two candidate right adjoints.
  let adj :=
    ((coskAdj m).comp ((SimplexCategory.Truncated.incl n m h).op.ranAdjunction C)).ofNatIsoLeft
      (truncationCompTrunc h)
  exact Adjunction.rightAdjointUniq adj (coskAdj n)

-- Proof sketch: the canonical `n`-coskeleton is `n`-coskeletal by the previous instance, and the
-- ambient monotonicity theorem upgrades `n`-coskeletality to `m`-coskeletality when `n ≤ m`.
/-- Lemma 14.19.10 (3): if `n ≤ m`, then for every `n`-truncated simplicial object `U`, its
canonical `n`-coskeleton is also `m`-coskeletal. This is the owner-level form of the identity
`cosk_m sk_m cosk_n U = cosk_n U`. -/
theorem isCoskeletal_of_le (h : n ≤ m) (U : SimplicialObject.Truncated C n) :
    ((Truncated.cosk n).obj U).IsCoskeletal m := by
  -- Route correction: instead of identifying `truncation m (coskₙ U)` directly, compare right
  -- adjoints to `truncation n` and transport `m`-coskeletality across the resulting component.
  exact isCoskeletal_of_iso_aux
    ((ran_comp_cosk_iso_of_le h).app U)
    (instIsCoskeletalCosk (((SimplexCategory.Truncated.incl n m h).op.ran).obj U))

/-- Companion to Lemma 14.19.10 (3): the canonical unit map exhibiting
`(Truncated.cosk n).obj U` as recovered from its `m`-truncation is an isomorphism. -/
theorem cosk_unit_app_isIso_of_le (h : n ≤ m) (U : SimplicialObject.Truncated C n) :
    IsIso ((coskAdj m).unit.app ((Truncated.cosk n).obj U)) := by
  rw [← SimplicialObject.isCoskeletal_iff_isIso]
  exact isCoskeletal_of_le h U

end

end SimplicialObject.Truncated

namespace SimplicialObject

/-- Coskeletality is invariant under isomorphism. -/
theorem isCoskeletal_of_iso {X Y : SimplicialObject C} (e : X ≅ Y) (hX : X.IsCoskeletal n) :
    Y.IsCoskeletal n := by
  rw [isCoskeletal_iff] at hX ⊢
  exact (Functor.isRightKanExtension_iff_of_iso₂
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ X))
    (𝟙 ((SimplexCategory.Truncated.inclusion n).op ⋙ Y))
    (Functor.isoWhiskerLeft (SimplexCategory.Truncated.inclusion n).op e) e
    (by simp [Functor.isoWhiskerLeft_hom])).1 hX

section

variable [HasFiniteLimits C]

-- Proof sketch: identify `U` with its canonical `n`-coskeleton, apply the previous truncated
-- owner-level statement there, and transport the resulting `m`-coskeletality back across the
-- canonical isomorphism.
/-- Lemma 14.19.10 (4): if `U` is `n`-coskeletal and `n ≤ m`, then `U` is also `m`-coskeletal. -/
theorem isCoskeletal_of_le {U : SimplicialObject C} (h : n ≤ m) (hU : U.IsCoskeletal n) :
    U.IsCoskeletal m := by
  letI : U.IsCoskeletal n := hU
  have hcosk : ((cosk n).obj U).IsCoskeletal m := by
    change ((Truncated.cosk n).obj ((truncation n).obj U)).IsCoskeletal m
    exact SimplicialObject.Truncated.isCoskeletal_of_le h ((truncation n).obj U)
  have e : U ≅ (cosk n).obj U := U.isoCoskOfIsCoskeletal n
  exact isCoskeletal_of_iso e.symm hcosk

/-- Companion to Lemma 14.19.10 (4): if `U ⟶ cosk_n sk_n U` is an isomorphism and `n ≤ m`, then
`U ⟶ cosk_m sk_m U` is also an isomorphism. -/
theorem cosk_unit_app_isIso_of_le {U : SimplicialObject C} (h : n ≤ m)
    (hn : IsIso ((coskAdj n).unit.app U)) :
    IsIso ((coskAdj m).unit.app U) := by
  rw [← isCoskeletal_iff_isIso]
  exact isCoskeletal_of_le h ((isCoskeletal_iff_isIso U n).2 hn)

end

end SimplicialObject

end Coskeleton

namespace SimplicialObject.Truncated

section FurtherTruncationBridge

variable [HasFiniteLimits C]

namespace trunc

/- Internal bridge: compare the right adjoint to further truncation after composing with the
fully faithful right adjoint `Truncated.cosk m`. This uses only canonical owner-level adjunction
operations: compose the generic `ranAdjunction` with `coskAdj m`, transport the left adjoint via
`truncationCompTrunc h`, and identify the resulting right adjoint with `Truncated.cosk n` by
uniqueness of right adjoints. -/
private noncomputable def truncAdjCompIso (n m : ℕ) (h : n ≤ m) :
    ((incl n m h).op.ran) ⋙ (Truncated.cosk m : SimplicialObject.Truncated C m ⥤
      SimplicialObject C) ≅
      Truncated.cosk n := by
  let adj :=
    ((coskAdj m).comp ((incl n m h).op.ranAdjunction C)).ofNatIsoLeft
      (truncationCompTrunc h)
  exact Adjunction.rightAdjointUniq adj (coskAdj n)

private noncomputable def coskTruncCompIso (n m : ℕ) (h : n ≤ m) :
    ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙ truncation m) ⋙
      (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) ≅
    Truncated.cosk n := by
  let unitIso :
      (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ≅
        ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
          truncation m) ⋙
            (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) :=
    NatIso.ofComponents
      (fun U ↦ by
        let f := (coskAdj m).unit.app ((Truncated.cosk n).obj U)
        let hf := SimplicialObject.Truncated.cosk_unit_app_isIso_of_le h U
        let g := Classical.choose hf.out
        exact ⟨f, g, (Classical.choose_spec hf.out).left, (Classical.choose_spec hf.out).right⟩)
      (fun f ↦ by
        simpa using (coskAdj m).unit.naturality ((Truncated.cosk n).map f))
  exact unitIso.symm

/- Internal comparison used to transport the generic `ranAdjunction` to the source-facing
right adjoint of Lemma 14.19.10 (2). After composing both candidate right adjoints with the
fully faithful functor `Truncated.cosk m`, they identify canonically, so we cancel on the right. -/
private noncomputable def truncAdjRightIso (n m : ℕ) (h : n ≤ m) :
    ((incl n m h).op.ran) ≅
      (Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙ truncation m := by
  let compIso :
      ((incl n m h).op.ran) ⋙
          (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) ≅
        ((Truncated.cosk n : SimplicialObject.Truncated C n ⥤ SimplicialObject C) ⋙
            truncation m) ⋙
          (Truncated.cosk m : SimplicialObject.Truncated C m ⥤ SimplicialObject C) :=
    truncAdjCompIso n m h ≪≫
      (coskTruncCompIso n m h).symm
  exact Functor.fullyFaithfulCancelRight (Truncated.cosk m) compIso

/-- Lemma 14.19.10 (2): the further truncation functor has right adjoint given by the
`m`-truncation of the `n`-coskeleton. This is obtained by transporting the generic right Kan
extension adjunction along an internal comparison with `Truncated.cosk n ⋙ truncation m`. -/
noncomputable def adj (n m : ℕ) (h : n ≤ m) :
    Truncated.trunc C m n h ⊣ Truncated.cosk n ⋙ truncation m :=
  ((incl n m h).op.ranAdjunction C).ofNatIsoRight (truncAdjRightIso n m h)

end trunc

end FurtherTruncationBridge

end SimplicialObject.Truncated

variable {m : ℕ} (h : n ≤ m)

/- Lemma 14.19.10 (2): if `C` has finite limits and `n ≤ m`, then the further truncation functor
`Truncated.trunc C m n h` is left adjoint to the `m`-truncation of the `n`-coskeleton. The file
keeps the generic right Kan extension owner only as internal support for this adjunction. -/
section

variable [HasFiniteLimits C]

#check (Truncated.trunc.adj n m h :
  Truncated.trunc C m n h ⊣ Truncated.cosk n ⋙ truncation m)

end

end CategoryTheory
