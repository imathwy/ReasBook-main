import Mathlib
import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Construction_3_6_2 (from Chap03) -/
universe u v

open CategoryTheory

variable {B : Type u} [Groupoid.{v} B]

/-- The vertex group at `b` acts on the star of arrows with source `b` by precomposition with
inverse loops. This is the same canonical `MulAction.ofEndHom` owner pattern used for vertex-group
actions elsewhere in the chapter. -/
instance orbitCoveringHomMulAction (b x : B) : MulAction (End b) (b ⟶ x) :=
  MulAction.ofEndHom
    { toFun := fun g ↦ fun f ↦ g⁻¹ ≫ f
      map_one' := by
        funext f
        simp [Function.End.one_def]
      map_mul' := by
        intro g h
        funext f
        simp [Function.End.mul_def, Category.assoc] }

/-- The orbit-covering action evaluates a loop by precomposing with its inverse. -/
@[simp] theorem orbitCoveringHomMulAction_smul (b x : B) (g : End b) (f : b ⟶ x) :
    g • f = g⁻¹ ≫ f :=
  rfl

/-- Construction 3.6.2: the objects of the covering attached to `H ≤ π(B,b)` are the right
`H`-cosets of arrows in the star of `b`; concretely, over each object `x : B` they are the
quotient of `b ⟶ x` by the precomposition action of `H`. -/
abbrev orbitCoveringObj (b : B) (H : Subgroup (End b)) : Type (max u v) :=
  Σ x : B, MulAction.orbitRel.Quotient H (b ⟶ x)

/-- The first component of an object of the orbit covering is its image in the base groupoid. -/
@[simp] theorem orbitCoveringObj_fst (b : B) (H : Subgroup (End b))
    (x : B) (q : MulAction.orbitRel.Quotient H (b ⟶ x)) :
    Sigma.fst ((⟨x, q⟩ : orbitCoveringObj b H)) = x :=
  rfl

/-- The object of the covering represented by the right coset of an arrow `f : b ⟶ x`. -/
abbrev orbitCoveringObjOfHom (b : B) (H : Subgroup (End b)) {x : B} (f : b ⟶ x) :
    orbitCoveringObj b H :=
  ⟨x, Quotient.mk'' f⟩

/-- The projection from the source-facing object set of `E(G/H)` to the base groupoid remembers
the target of the represented arrow. -/
abbrev orbitCoveringProjection (b : B) (H : Subgroup (End b)) :
    orbitCoveringObj b H → B :=
  Sigma.fst

/-- The projection of the coset represented by `f` is the target of `f`. -/
@[simp] theorem orbitCoveringProjection_ofHom (b : B) (H : Subgroup (End b))
    {x : B} (f : b ⟶ x) :
    orbitCoveringProjection b H (orbitCoveringObjOfHom b H f) = x := rfl

/-! ### Construction_3_6_3 (from Chap03) -/
universe u v

open CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]

/-- The source-facing object `fH` of `E(G/H)`, represented by an arrow `f : b ⟶ x`, viewed inside
the canonical owner `CategoryOfElements (associatedAction b (End b ⧸ H))`. -/
abbrev orbitSubgroupCoveringObjOfHom (b : B) (H : Subgroup (End b)) {x : B} (f : b ⟶ x) :
    (associatedAction b (End b ⧸ H)).Elements :=
  ⟨x, Quotient.mk'' (f, ((1 : End b) : End b ⧸ H))⟩

/-- Construction 3.6.3: an element `h ∈ H` defines the corresponding morphism `fH ⟶ f'H` in the
orbit covering, realized in the canonical category-of-elements owner. -/
noncomputable def orbitSubgroupCoveringHomOfSubgroup (b : B) (H : Subgroup (End b))
    {x x' : B} (f : b ⟶ x) (f' : b ⟶ x') (h : H) :
    orbitSubgroupCoveringObjOfHom b H f ⟶ orbitSubgroupCoveringObjOfHom b H f' :=
  CategoryOfElements.homMk _ _ (inv f ≫ h.1 ≫ f') <| by
    change Quotient.mk'' (f ≫ inv f ≫ h.1 ≫ f', ((1 : End b) : End b ⧸ H)) =
      Quotient.mk'' (f', ((1 : End b) : End b ⧸ H))
    apply Quotient.sound
    change MulAction.orbitRel (End b) ((b ⟶ x') × (End b ⧸ H))
      (f ≫ inv f ≫ h.1 ≫ f', ((1 : End b) : End b ⧸ H)) (f', ((1 : End b) : End b ⧸ H))
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
    refine ⟨(h : End b), ?_⟩
    ext
    · change (h : End b) • (f ≫ inv f ≫ h.1 ≫ f') = f'
      rw [orbitCoveringHomMulAction_smul]
      simp
    · change (h : End b) • ((1 : End b) : End b ⧸ H) = ((1 : End b) : End b ⧸ H)
      apply QuotientGroup.eq.mpr
      simp [h.2]

/-- The canonical projection from `E(G/H)` to `B` sends the morphism determined by `h ∈ H` to the
base-groupoid arrow `f⁻¹ ≫ h ≫ f'`. -/
@[simp] theorem orbitSubgroupCoveringProjection_map_homOfSubgroup (b : B)
    (H : Subgroup (End b)) {x x' : B} (f : b ⟶ x) (f' : b ⟶ x') (h : H) :
    (CategoryOfElements.π (associatedAction b (End b ⧸ H))).map
        (orbitSubgroupCoveringHomOfSubgroup b H f f' h) =
      inv f ≫ h.1 ≫ f' :=
  rfl

/-- A base-groupoid arrow `g : x ⟶ x'` occurs as a morphism `fH ⟶ f'H` in `E(G/H)` exactly when
it has the form `f⁻¹ ≫ h ≫ f'` for some `h ∈ H`. -/
theorem exists_orbitSubgroupCoveringHom_iff (b : B) (H : Subgroup (End b))
    {x x' : B} (f : b ⟶ x) (f' : b ⟶ x') (g : x ⟶ x') :
    (∃ α : orbitSubgroupCoveringObjOfHom b H f ⟶ orbitSubgroupCoveringObjOfHom b H f',
      (CategoryOfElements.π (associatedAction b (End b ⧸ H))).map α = g) ↔
        ∃ h : H, g = inv f ≫ h.1 ≫ f' := by
  constructor
  · rintro ⟨α, rfl⟩
    have hα := CategoryOfElements.map_snd α
    change Quotient.mk'' (f ≫ α.1, ((1 : End b) : End b ⧸ H)) =
      Quotient.mk'' (f', ((1 : End b) : End b ⧸ H)) at hα
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_symm] at hα
    rcases hα with ⟨k, hk⟩
    have hk_fst : (k : End b) • (f ≫ α.1) = f' := by
      simpa using congrArg Prod.fst hk
    have hk_snd : (k : End b) • ((1 : End b) : End b ⧸ H) = ((1 : End b) : End b ⧸ H) := by
      simpa using congrArg Prod.snd hk
    have hk_mem : (k : End b) ∈ H := by
      have hk' : ((k : End b) : End b ⧸ H) = ((1 : End b) : End b ⧸ H) := by
        simpa using hk_snd
      rw [QuotientGroup.eq] at hk'
      simpa using H.inv_mem hk'
    have hk_fst' : f ≫ α.1 = (k : End b) ≫ f' := by
      calc
        f ≫ α.1 = (k : End b) ≫ ((k : End b)⁻¹ ≫ (f ≫ α.1)) := by simp
        _ = (k : End b) ≫ f' := by
          rw [orbitCoveringHomMulAction_smul] at hk_fst
          simpa [Category.assoc] using congrArg ((· ≫ ·) (k : End b)) hk_fst
    refine ⟨⟨k, hk_mem⟩, ?_⟩
    calc
      α.1 = inv f ≫ (f ≫ α.1) := by simp
      _ = inv f ≫ ((k : End b) ≫ f') := by rw [hk_fst']
      _ = inv f ≫ (k : End b) ≫ f' := by simp
  · rintro ⟨h, rfl⟩
    exact ⟨orbitSubgroupCoveringHomOfSubgroup b H f f' h, rfl⟩

/-! ### Lemma_3_6_4 (from Chap03) -/
universe u v

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]

/- Lemma 3.6.4 (1): the canonical projection
`CategoryOfElements.π (associatedAction b (End b ⧸ H)) : E(G/H) ⥤ B`
is a covering functor. -/
recall orbitCategoryAssociatedAction_elements_isCovering
    (b : B) [CategoryTheory.IsConnected B] (H : O(End b)) :
    Functor.IsCovering (CategoryOfElements.π (associatedAction b (End b ⧸ H)))

/-- Lemma 3.6.4 (2): at the canonical object `e = H`, a loop at `b` lies in the image subgroup
of the vertex group under the covering projection exactly when it lies in `H`. -/
theorem orbitCategoryAssociatedAction_basepoint_mem_mapVertexGroup_range_iff_mem (b : B)
    (H : O(End b)) (γ : End b) :
    γ ∈ (CategoryTheory.Functor.mapVertexGroup
      (CategoryOfElements.π (associatedAction b (End b ⧸ H)))
      (orbitSubgroupCoveringObjOfHom b (H : Subgroup (End b)) (𝟙 b))).range ↔ γ ∈ H := by
  simpa [MonoidHom.mem_range] using
    (exists_orbitSubgroupCoveringHom_iff b (H : Subgroup (End b)) (𝟙 b) (𝟙 b) γ)

/-! ### Construction_3_6_5 (from Chap03) -/
universe u v

open CategoryTheory
open QuotientGroup

variable {B : Type u} [Groupoid.{v} B]
variable [IsConnected B]

section

variable (b : B) {H K : O(End b)} (α : H ⟶ K)

/- Construction 3.6.5: a morphism `α : H ⟶ K` in the orbit category induces the canonical
morphism `((orbitCategoryToConnectedCovering b).map α)` between the associated connected
coverings over `B`; its commutative-triangle relation over `B` is the field
`((orbitCategoryToConnectedCovering b).map α).hom.comm`. -/
#check ((orbitCategoryToConnectedCovering b).map α)

end

/-- If `α (eH) = γK`, then the canonical covering morphism induced by `α : H ⟶ K` sends the
source-facing object `fH` of `E(G/H)` to the source-facing object `(γ ≫ f)K` of `E(G/K)`. -/
-- Proof sketch: on category-of-elements representatives the induced functor fixes the arrow `f`
-- and applies `α` to the quotient coordinate, so `fH` goes to the class of `(f, γK)`. That class
-- is exactly the source-facing object `(γ ≫ f)K`, since the diagonal `π(B,b)`-action identifies
-- `(γ ≫ f, K)` with `(f, γK)`.
theorem orbitCategoryToConnectedCovering_map_objOfHom_of_apply_one (b : B)
    {H K : O(End b)} (α : H ⟶ K)
    {γ : End b}
    (hα : (Subgroup.orbitCategoryHomEvalOne H K α : End b ⧸ K) = (γ : End b ⧸ K))
    {x : B} (f : b ⟶ x) :
    (((orbitCategoryToConnectedCovering b).map α).hom.left).obj
      (orbitSubgroupCoveringObjOfHom b (H : Subgroup (End b)) f) =
        orbitSubgroupCoveringObjOfHom b (K : Subgroup (End b)) (γ ≫ f) := by
  change
    (⟨x, Quotient.mk'' (f, α.toFun ((1 : End b) : End b ⧸ H))⟩ :
      (associatedAction b (End b ⧸ K)).Elements) =
      ⟨x, Quotient.mk'' (γ ≫ f, ((1 : End b) : End b ⧸ K))⟩
  rw [show α.toFun ((1 : End b) : End b ⧸ H) = (γ : End b ⧸ K) by simpa using hα]
  congr 1
  apply Quotient.sound
  change
    MulAction.orbitRel (End b) ((b ⟶ x) × (End b ⧸ K))
      (f, (γ : End b ⧸ K)) (γ ≫ f, ((1 : End b) : End b ⧸ K))
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
  refine ⟨γ⁻¹, ?_⟩
  change ((γ⁻¹ : End b) • f, (γ⁻¹ : End b) • (γ : End b ⧸ K)) =
      (γ ≫ f, ((1 : End b) : End b ⧸ K))
  ext
  · change (γ⁻¹ : End b) • f = γ ≫ f
    rw [orbitCoveringHomMulAction_smul]
    exact congrArg (fun η : End b ↦ η ≫ f) (inv_inv γ)
  · change (((γ⁻¹ : End b) * γ : End b) : End b ⧸ K) = ((1 : End b) : End b ⧸ K)
    simp

/-! ### Remark_3_6_6 (from Chap03) -/
universe u₁ u₂ v

open CategoryTheory

variable {G : Type u₁} [Groupoid.{v} G]
variable {B : Type u₂} [Groupoid.{v} B]
variable {ι : G ⥤ B}

namespace MulAction

/-- Transport transitivity across a compatible equivalence of acting groups and underlying sets. -/
theorem IsTransitive.of_mulEquiv
    {H : Type*} [Group H] {K : Type*} [Group K]
    {X : Type*} [MulAction H X] {Y : Type*} [MulAction K Y]
    (eH : H ≃* K) (eX : X ≃ Y)
    (hcompat : ∀ g x, eX (g • x) = eH g • eX x)
    (h : IsTransitive H X) :
    IsTransitive K Y := by
  rcases h with ⟨hX, hpre⟩
  let f : X →ₑ[eH] Y :=
    { toFun := eX
      map_smul' := hcompat }
  have hf : Function.Bijective f := eX.bijective
  refine ⟨hX.map eX, ?_⟩
  exact (MulAction.isPretransitive_congr eH.surjective hf).mp hpre

/-- Transitivity is invariant under a compatible equivalence of acting groups and underlying
sets. -/
theorem isTransitive_iff_of_mulEquiv
    {H : Type*} [Group H] {K : Type*} [Group K]
    {X : Type*} [MulAction H X] {Y : Type*} [MulAction K Y]
    (eH : H ≃* K) (eX : X ≃ Y)
    (hcompat : ∀ g x, eX (g • x) = eH g • eX x) :
    IsTransitive H X ↔ IsTransitive K Y := by
  constructor
  · exact IsTransitive.of_mulEquiv eH eX hcompat
  · intro h
    refine IsTransitive.of_mulEquiv eH.symm eX.symm ?_ h
    intro k y
    apply eX.injective
    simpa using (hcompat (eH.symm k) (eX.symm y)).symm

end MulAction

namespace CategoryTheory.Functor

/-- Restriction along an equivalence of groupoids preserves and reflects transitivity of set-valued
functors. -/
theorem isTransitive_iff_comp_of_isEquivalence
    {C : Type*} [Groupoid C] {D : Type*} [Groupoid D]
    (F : C ⥤ D) [F.IsEquivalence] (T : D ⥤ Type v) :
    IsTransitive T ↔ IsTransitive (F ⋙ T) := by
  rw [Functor.isTransitive_iff_forall_vertexGroupMulAction_isTransitive,
    Functor.isTransitive_iff_forall_vertexGroupMulAction_isTransitive]
  let e := F.asEquivalence
  let hF : F.FullyFaithful := .ofFullyFaithful F
  constructor
  · intro hT c
    letI := vertexGroupMulAction (F ⋙ T) c
    letI := vertexGroupMulAction T (F.obj c)
    let eEnd := hF.mulEquivEnd c
    rcases hT (F.obj c) with ⟨hx, hpre⟩
    let f : (F ⋙ T).obj c →ₑ[eEnd] T.obj (F.obj c) :=
      { toFun := id
        map_smul' := fun g x ↦ by
          simpa [eEnd, vertexGroupMulAction_smul_eq_map] using
            (vertexGroupMulAction_smul_eq_map (F ⋙ T) c g x) }
    have hf : Function.Bijective f := Function.bijective_id
    exact ⟨hx, (MulAction.isPretransitive_congr eEnd.surjective hf).mpr hpre⟩
  · intro hFT d
    let c := e.inverse.obj d
    let i : F.obj c ≅ d := e.counitIso.app d
    letI := vertexGroupMulAction (F ⋙ T) c
    letI : MulAction (End c) (T.obj (F.obj c)) := vertexGroupMulAction (F ⋙ T) c
    letI := vertexGroupMulAction T d
    let eEnd := (hF.mulEquivEnd c).trans i.conj
    have hc : MulAction.IsTransitive (End c) (T.obj (F.obj c)) := hFT c
    exact (MulAction.isTransitive_iff_of_mulEquiv eEnd (T.mapIso i).toEquiv fun g x ↦ by
      simp only [Iso.toEquiv_fun, Functor.mapIso_hom]
      rw [vertexGroupMulAction_smul_eq_map (F ⋙ T) c g x,
          vertexGroupMulAction_smul_eq_map T d (eEnd g)]
      simp only [eEnd, MulEquiv.trans_apply, Iso.conj_apply, Functor.comp_map,
        ← Functor.map_comp_apply, Iso.hom_inv_id_assoc]
      congr 1).mp hc

end CategoryTheory.Functor

/-- Remark 3.6.6: restriction along a skeleton inclusion `ι : G ⥤ B` identifies `B`-sets with
`G`-sets by making precomposition with `ι` an equivalence of functor categories. -/
-- Proof sketch: a skeleton inclusion is an equivalence by `hι.eqv`, and precomposition with an
-- equivalence is again an equivalence by the standard `whiskeringLeft` functor-category API.
theorem restrictionAlongSkeleton_isEquivalence (hι : IsSkeletonOf B G ι) :
    Functor.IsEquivalence ((Functor.whiskeringLeft G B (Type v)).obj ι) := by
  letI : ι.IsEquivalence := hι.eqv
  infer_instance

/-- Restriction along a skeleton inclusion preserves and reflects transitivity of groupoid actions
on sets. -/
-- Proof sketch: use a quasi-inverse to the skeleton inclusion to transport points and loops
-- between `G` and `B`; the orbit condition on each fiber is unchanged under these identifications.
theorem isTransitive_iff_comp_of_isSkeletonOf
    (hι : IsSkeletonOf B G ι) (T : B ⥤ Type v) :
    Functor.IsTransitive T ↔ Functor.IsTransitive (ι ⋙ T) := by
  letI : ι.IsEquivalence := hι.eqv
  simpa using Functor.isTransitive_iff_comp_of_isEquivalence ι T

/-! ### Remark_3_6_7 (from Chap03) -/
universe u

open CategoryTheory
open QuotientGroup

variable (G : Type u) [Group G]

/-- The orbit category maps canonically to bundled `G`-actions by sending `H` to the quotient
action on `G ⧸ H`. -/
private def orbitCategoryToAction : O(G) ⥤ Action (Type u) G where
  obj H := Action.ofMulAction G (G ⧸ H)
  map {H K} f :=
    { hom := TypeCat.ofHom f.toFun
      comm := fun g ↦ by
        ext x
        simpa [Action.ofMulAction_apply] using f.map_smul' g x }
  map_id H := by
    apply Action.hom_ext
    ext x
    rfl
  map_comp f g := by
    apply Action.hom_ext
    ext x
    rfl

/-- The canonical functor from the orbit category to bundled transitive `G`-sets. -/
abbrev orbitCategoryToTransitiveGSet :
    O(G) ⥤ ObjectProperty.FullSubcategory
      (fun A : Action (Type u) G ↦ MulAction.IsTransitive G (ToType A)) :=
  ObjectProperty.lift
    (fun A : Action (Type u) G ↦ MulAction.IsTransitive G (ToType A))
    (orbitCategoryToAction G)
    (fun H ↦ orbitCategory_obj_isTransitive G H)

/-- Helper for Remark 3.6.7: an equivariant map between quotient actions is already a morphism in
the orbit category. -/
private def action_hom_to_orbit_morphism {H K : O(G)}
    (φ : Action.ofMulAction G (G ⧸ H) ⟶ Action.ofMulAction G (G ⧸ K)) : H ⟶ K where
  toFun := φ.hom
  map_smul' g x := by
    have h := ConcreteCategory.congr_hom (φ.comm g) x
    simpa [Action.ofMulAction_apply] using h

/-- Helper for Remark 3.6.7: a transitive bundled `G`-action is isomorphic to the quotient by the
stabilizer of any chosen point. -/
private noncomputable def quotient_stabilizer_action_iso
    {A : Action (Type u) G} (a : ToType A) [MulAction.IsPretransitive G (ToType A)] :
    Action.ofMulAction G (G ⧸ MulAction.stabilizer G a) ≅ A := by
  -- Lemma 3.4.3 gives the underlying equivariant bijection `G / G_a ≃ A`.
  refine Action.mkIso
    (quotientStabilizerEquivOfIsPretransitive (G := G) (S := ToType A) a).toIso ?_
  intro g
  ext x
  -- The equivariance statement becomes the commutativity condition for `Action.mkIso`.
  simpa using
    quotientStabilizerEquivOfIsPretransitive_equivariant (G := G) (S := ToType A) a g x

/-- Helper for Remark 3.6.7: every bundled transitive `G`-set is represented by some quotient
`G ⧸ H` in the orbit category. -/
private theorem transitive_action_iso_quotient_stabilizer
    (A : ObjectProperty.FullSubcategory
      (fun X : Action (Type u) G ↦ MulAction.IsTransitive G (ToType X))) :
    ∃ H : O(G), Nonempty ((orbitCategoryToTransitiveGSet G).obj H ≅ A) := by
  rcases A.2 with ⟨ha, hpre⟩
  rcases ha with ⟨a⟩
  let H : O(G) := ⟨MulAction.stabilizer G a⟩
  let _ : MulAction.IsPretransitive G (ToType A.1) := hpre
  refine ⟨H, ⟨?_⟩⟩
  -- Lift the quotient-stabilizer isomorphism into the full subcategory of transitive actions.
  refine ObjectProperty.isoMk _ ?_
  simpa [orbitCategoryToTransitiveGSet, orbitCategoryToAction, H] using
    (quotient_stabilizer_action_iso (G := G) (A := A.1) a)

/-- Remark 3.6.7: the orbit category `O(G)` is equivalent to the full subcategory of transitive
`G`-sets. A skeleton of that category arises only after choosing one subgroup from each conjugacy
class, whereas `O(G)` itself keeps every quotient `G ⧸ H`. -/
-- Proof sketch: every object of `O(G)` is already a transitive quotient `G ⧸ H`, so the displayed
-- functor lands in the full subcategory of transitive `G`-sets. Essential surjectivity is the
-- quotient-stabilizer description of transitive actions, and full faithfulness identifies maps of
-- transitive `G`-sets with equivariant maps between the corresponding quotients.
theorem orbitCategoryToTransitiveGSet_isEquivalence :
    Functor.IsEquivalence (orbitCategoryToTransitiveGSet G) := by
  let _ : (orbitCategoryToAction G).Faithful :=
    { map_injective := by
        intro H K f g hfg
        apply MulActionHom.ext
        intro x
        exact ConcreteCategory.congr_hom (congrArg Action.Hom.hom hfg) x }
  let _ : (orbitCategoryToAction G).Full :=
    { map_surjective := by
        intro H K φ
        refine ⟨action_hom_to_orbit_morphism (G := G) φ, ?_⟩
        apply Action.hom_ext
        ext x
        simp [action_hom_to_orbit_morphism, orbitCategoryToAction] }
  let _ : (orbitCategoryToTransitiveGSet G).EssSurj :=
    { mem_essImage := by
        intro A
        -- Choose a point in the transitive action and identify it with the corresponding quotient.
        rcases transitive_action_iso_quotient_stabilizer (G := G) A with ⟨H, ⟨e⟩⟩
        exact ⟨H, ⟨e⟩⟩ }
  -- The lifted functor is therefore faithful, full, and essentially surjective.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
