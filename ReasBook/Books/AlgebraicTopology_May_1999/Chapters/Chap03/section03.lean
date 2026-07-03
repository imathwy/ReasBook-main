import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_3_1 (from Chap03) -/
universe u v

open CategoryTheory

variable {T : Type u} [Category.{v} T] {X Y : T}
variable (C : Type u) [Category.{v} C] (x : C)

/- Definition 3.3.1: the under-category `x\C` is the canonical category `Under x`, whose
objects are morphisms with source `x` and whose morphisms are commutative triangles over `x`. -/
#check Under x

/- An object of the under-category `Under x` is given by a morphism `x ⟶ y`. -/
recall Under.mk (f : X ⟶ Y) : Under X

/- A morphism in `Under x` is a map between codomains whose triangle with the structure maps
commutes. -/
recall Under.homMk {U V : Under X} (γ : U.right ⟶ V.right)
    (hγ : U.hom ≫ γ = V.hom) : U ⟶ V

/- Every morphism in the under-category satisfies the defining commutative-triangle relation. -/
recall Under.w {U V : Under X} (γ : U ⟶ V) : U.hom ≫ γ.right = V.hom

/- The under-category inherits its category structure from the canonical mathlib instance. -/
#check (inferInstance : Category (Under x))

/-! ### Definition_3_3_2 (from Chap03) -/
universe u v

open CategoryTheory

namespace CategoryTheory.Groupoid

variable (C : Type u) [Category.{v} C] (x : C)

/- Definition 3.3.2 (1): the star `St_C(x)` is the canonical under-category `Under x`, whose
objects are morphisms of `C` with source `x`. -/
#check Under x

variable [Groupoid.{v} C]

/- Definition 3.3.2 (2): `π(C, x)` is the vertex group at `x`, i.e. the group structure on the
loop type `x ⟶ x` whose multiplication is categorical composition in the groupoid `C`. -/
#check Groupoid.vertexGroup x

end CategoryTheory.Groupoid

/-! ### Definition_3_3_3 (from Chap03) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Functor

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]

/-- Definition 3.3.3: a covering functor of groupoids is surjective on objects and induces a
bijection from each star `Under e` to the star `Under (p.obj e)` via the canonical functor
`Under.post p`. -/
class IsCovering (p : E ⥤ B) : Prop where
  /-- A covering functor is surjective on objects. -/
  obj_surjective : Function.Surjective p.obj
  /-- A covering functor is bijective on the canonical star map at every object. -/
  star_bijective (e : E) : Function.Bijective ((Under.post p : Under e ⥤ Under (p.obj e)).obj)

/-- The identity functor on a groupoid is a covering functor. -/
instance (C : Type u₁) [Groupoid.{v₁} C] : IsCovering (𝟭 C) where
  obj_surjective c := ⟨c, rfl⟩
  star_bijective e := by
    simpa [Under.post] using (Function.bijective_id : Function.Bijective (id : Under e → Under e))

end Functor

end CategoryTheory

/-! ### Proposition_3_3_4 (from Chap03) -/
universe u v

open CategoryTheory FundamentalGroupoid

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- The functor on fundamental groupoids induced by a path-connected covering map. -/
noncomputable abbrev fundamentalGroupoidMap (hp : IsPathConnectedCoveringMap p) :
    FundamentalGroupoid E ⥤ FundamentalGroupoid B :=
  FundamentalGroupoid.map ⟨p, hp.isCoveringMap.continuous⟩

private theorem fundamentalGroupoidMap_obj_eq (hp : IsPathConnectedCoveringMap p) {b : B}
    (e : p ⁻¹' {b}) : hp.fundamentalGroupoidMap.obj (mk e.1) = mk b := by
  rcases e with ⟨e, he⟩
  change p e = b at he
  subst he
  rfl

/-- The fiber of the induced functor on fundamental groupoids over `mk b` identifies with the
ordinary fiber of the covering map over `b`. -/
noncomputable def fundamentalGroupoidMapFiberEquiv (hp : IsPathConnectedCoveringMap p) (b : B) :
    hp.fundamentalGroupoidMap.Fiber (mk b) ≃ p ⁻¹' {b} where
  toFun x := ⟨x.1.as, by
    change p x.1.as = b
    simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap] using
      congrArg FundamentalGroupoid.as x.2⟩
  invFun e := ⟨mk e.1, fundamentalGroupoidMap_obj_eq hp e⟩
  left_inv x := by
    rcases x with ⟨x, hx⟩
    apply Subtype.ext
    ext
    rfl
  right_inv e := by
    apply Subtype.ext
    rfl

/-- Helper for Proposition 3.3.4: once the endpoint is fixed, the induced map on fundamental-
groupoid morphisms is injective. -/
private theorem fundamentalGroupoidMap_hom_injective (hp : IsPathConnectedCoveringMap p) (e y : E) :
    Function.Injective fun f : mk e ⟶ mk y => hp.fundamentalGroupoidMap.map f := by
  -- This is Theorem 3.2.3 in the fundamental-groupoid language.
  simpa [IsPathConnectedCoveringMap.fundamentalGroupoidMap, FundamentalGroupoid.map_eq] using
    hp.isCoveringMap.injective_path_homotopic_map e y

/-- Helper for Proposition 3.3.4: the endpoint of the lifted representative path lies over the
target endpoint of the base path. -/
private theorem liftPath_endpoint_eq_target (hp : IsPathConnectedCoveringMap p) {b : B}
    (e : E) (γ : Path (p e) b) :
    p (hp.isCoveringMap.liftPath γ e γ.source 1) = b := by
  -- Evaluate the projection of the lifted path at the endpoint.
  simpa using (congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target

/-- Helper for Proposition 3.3.4: projecting the chosen lifted path back to the base recovers the
original representative path after the canonical endpoint cast. -/
private theorem liftPath_projection_eq_path (hp : IsPathConnectedCoveringMap p) {b : B}
    (e : E) (γ : Path (p e) b) :
    ((Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl).map hp.isCoveringMap.continuous).cast rfl
      (liftPath_endpoint_eq_target hp e γ).symm = γ := by
  -- The lifted path was defined so that its projection agrees pointwise with `γ`.
  ext t
  simpa using congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) t

/-- Helper for Proposition 3.3.4: transport of a path-homotopy class along an endpoint equality
agrees with the explicit `Path.Homotopic.Quotient.cast`. -/
private theorem quotient_cast_eq {x y z : B} (q : Path.Homotopic.Quotient x z) (h : y = z) :
    cast (congrArg (Path.Homotopic.Quotient x) h.symm) q = q.cast rfl h := by
  -- Both sides are the same transport; only the packaging differs.
  apply eq_of_heq
  cases h
  simp

/-- Helper for Proposition 3.3.4: changing the endpoint of a path class by an equality only
changes the codomain bookkeeping of the corresponding star object. -/
private theorem under_mk_fromPath_cast_eq {x y z : B} (q : Path.Homotopic.Quotient x z)
    (h : y = z) :
    (Under.mk (fromPath q) : Under (mk x)) = Under.mk (fromPath (q.cast rfl h)) := by
  -- After identifying the endpoints, the cast is trivial.
  cases h
  simp

/-- Helper for Proposition 3.3.4: every arrow in the star of `mk (p e)` has a preimage obtained by
lifting a representative path from `e`. -/
private theorem fundamentalGroupoidMap_star_surjective (hp : IsPathConnectedCoveringMap p) (e : E) :
    Function.Surjective
      ((Under.post hp.fundamentalGroupoidMap : Under (mk e) ⥤ Under (mk (p e))).obj) := by
  intro y
  -- Reduce the target star object to a single representative path in the base.
  obtain ⟨⟨b⟩, f, rfl⟩ := Under.mk_surjective y
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  let δ : Path e (hp.isCoveringMap.liftPath γ e γ.source 1) :=
    Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl
  refine ⟨Under.mk (fromPath ⟦δ⟧), ?_⟩
  have hproj_eq :
      ((Path.Homotopic.Quotient.mk δ).map
          ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
        (liftPath_endpoint_eq_target hp e γ).symm =
        Path.Homotopic.Quotient.mk γ := by
    -- Move the map through the quotient and use the pointwise projection identity.
    change Path.Homotopic.Quotient.mk
        (((Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
          (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl).map
            hp.isCoveringMap.continuous).cast rfl
          (liftPath_endpoint_eq_target hp e γ).symm) =
      Path.Homotopic.Quotient.mk γ
    exact congrArg Path.Homotopic.Quotient.mk (liftPath_projection_eq_path hp e γ)
  have hleft :
      Under.mk (fromPath ((Path.Homotopic.Quotient.mk δ).map
        ⟨p, hp.isCoveringMap.continuous⟩)) =
        Under.mk (fromPath (((Path.Homotopic.Quotient.mk δ).map
          ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
            (liftPath_endpoint_eq_target hp e γ).symm)) :=
    -- Replace the literal codomain by the endpoint identified from the lifted path.
    under_mk_fromPath_cast_eq _ (liftPath_endpoint_eq_target hp e γ).symm
  -- The chosen lifted representative maps back to the original base-star object.
  exact (by
    simpa [Under.post, FundamentalGroupoid.fromPath] using
      hleft.trans (congrArg Under.mk (congrArg fromPath hproj_eq)))

/-- Helper for Proposition 3.3.4: uniqueness of lifted representatives makes the induced star map
injective. -/
private theorem fundamentalGroupoidMap_star_injective (hp : IsPathConnectedCoveringMap p) (e : E) :
    Function.Injective
      ((Under.post hp.fundamentalGroupoidMap : Under (mk e) ⥤ Under (mk (p e))).obj) := by
  intro u v h
  -- Write both star objects as actual path classes starting at `e`.
  obtain ⟨⟨e₁⟩, fu, rfl⟩ := Under.mk_surjective u
  obtain ⟨⟨e₂⟩, fv, rfl⟩ := Under.mk_surjective v
  obtain ⟨γu, rfl⟩ := Path.Homotopic.Quotient.mk_surjective fu
  obtain ⟨γv, rfl⟩ := Path.Homotopic.Quotient.mk_surjective fv
  have hs :
      Under.mk (fromPath ((Path.Homotopic.Quotient.mk γu).map
        ⟨p, hp.isCoveringMap.continuous⟩)) =
        Under.mk (fromPath ((Path.Homotopic.Quotient.mk γv).map
          ⟨p, hp.isCoveringMap.continuous⟩)) := by
    simpa only [Under.post, fundamentalGroupoidMap] using h
  injections hs
  rename_i hmap hb
  let hβα : Path.Homotopic.Quotient (p e) (p e₂) = Path.Homotopic.Quotient (p e) (p e₁) :=
    congrArg (Path.Homotopic.Quotient (p e)) hb.symm
  have htype :
      type_eq_of_heq hmap.symm = congrArg (fun y ↦ mk (p e) ⟶ mk y) hb.symm := by
    apply Subsingleton.elim
  have hEq :
      fromPath ((Path.Homotopic.Quotient.mk γu).map
        ⟨p, hp.isCoveringMap.continuous⟩) =
        cast (congrArg (fun y ↦ mk (p e) ⟶ mk y) hb.symm)
          (fromPath ((Path.Homotopic.Quotient.mk γv).map
            ⟨p, hp.isCoveringMap.continuous⟩)) := by
    -- Convert the heterogeneous equality from `injections` into an ordinary equality with cast.
    rw [← htype]
    exact (eq_cast_iff_heq).2 hmap
  have hproj_eq0 :
      Path.Homotopic.Quotient.mk (γu.map hp.isCoveringMap.continuous) =
        cast hβα (Path.Homotopic.Quotient.mk (γv.map hp.isCoveringMap.continuous)) := by
    simpa [FundamentalGroupoid.fromPath, hβα, Path.Homotopic.Quotient.mk_map] using hEq
  have hproj_eq :
      Path.Homotopic.Quotient.mk (γu.map hp.isCoveringMap.continuous) =
        (Path.Homotopic.Quotient.mk (γv.map hp.isCoveringMap.continuous)).cast rfl hb := by
    -- Replace the generic transport by the explicit quotient cast.
    exact hproj_eq0.trans (quotient_cast_eq _ hb)
  have hproj_hom :
      (γu.map hp.isCoveringMap.continuous).Homotopic
        ((γv.map hp.isCoveringMap.continuous).cast rfl hb) := by
    -- Equal projected path classes are homotopic representatives.
    exact (Path.Homotopic.Quotient.eq).1 hproj_eq
  have hγu :
      γu.toContinuousMap =
        hp.isCoveringMap.liftPath (γu.map hp.isCoveringMap.continuous) e
          (γu.map hp.isCoveringMap.continuous).source := by
    -- `γu` is itself the canonical lift of its projection starting at `e`.
    exact (hp.isCoveringMap.eq_liftPath_iff'
      (γu.map hp.isCoveringMap.continuous).source).2 ⟨rfl, γu.source⟩
  have hγv_cast :
      γv.toContinuousMap =
        hp.isCoveringMap.liftPath ((γv.map hp.isCoveringMap.continuous).cast rfl hb) e
          ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source := by
    -- The same uniqueness statement applies to the recast projection of `γv`.
    refine (hp.isCoveringMap.eq_liftPath_iff'
      ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source).2 ?_
    constructor
    · ext t
      simp [Path.cast]
    · exact γv.source
  have hend : e₁ = e₂ := by
    have hγu1 :
        e₁ =
          hp.isCoveringMap.liftPath (γu.map hp.isCoveringMap.continuous) e
            (γu.map hp.isCoveringMap.continuous).source 1 := by
      simpa using congrArg (fun f : C(↑unitInterval, E) => f 1) hγu
    have hγv1 :
        hp.isCoveringMap.liftPath ((γv.map hp.isCoveringMap.continuous).cast rfl hb) e
            ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source 1 = e₂ := by
      simpa using congrArg (fun f : C(↑unitInterval, E) => f 1) hγv_cast.symm
    -- Theorem 3.2.2 identifies the endpoints of the two lifted representatives.
    calc
      e₁ =
          hp.isCoveringMap.liftPath (γu.map hp.isCoveringMap.continuous) e
            (γu.map hp.isCoveringMap.continuous).source 1 := hγu1
      _ =
          hp.isCoveringMap.liftPath ((γv.map hp.isCoveringMap.continuous).cast rfl hb) e
            ((γv.map hp.isCoveringMap.continuous).cast rfl hb).source 1 := by
          exact hp.isCoveringMap.liftPath_apply_one_eq_of_homotopic hproj_hom e rfl
      _ = e₂ := hγv1
  subst e₁
  have hmap_eq_same :
      fromPath ((Path.Homotopic.Quotient.mk γu).map
        ⟨p, hp.isCoveringMap.continuous⟩) =
        fromPath ((Path.Homotopic.Quotient.mk γv).map
          ⟨p, hp.isCoveringMap.continuous⟩) := by
    -- Once the endpoints coincide, the heterogeneous image equality becomes ordinary equality.
    exact eq_of_heq hmap
  have horig :
      fromPath (Path.Homotopic.Quotient.mk γu) =
        fromPath (Path.Homotopic.Quotient.mk γv) :=
    fundamentalGroupoidMap_hom_injective hp e e₂ hmap_eq_same
  -- Injectivity on the fixed-endpoint Hom-set recovers equality in the original star.
  exact congrArg Under.mk horig

/-- Proposition 3.3.4: a covering space `p : E → B` induces a covering functor
`hp.fundamentalGroupoidMap : Π(E) ⥤ Π(B)` of fundamental groupoids. -/
-- Proof sketch: surjectivity on objects comes from `hp.surjective`. For each `e : E`, unique path
-- lifting gives existence and uniqueness of lifts of arrows in the star of `p e`, while
-- homotopy-invariance of lifted endpoints makes the lifted star map well defined on fundamental
-- groupoid morphisms.
theorem fundamentalGroupoidMap_isCovering (hp : IsPathConnectedCoveringMap p) :
    Functor.IsCovering hp.fundamentalGroupoidMap := by
  classical
  refine ⟨?_, ?_⟩
  · -- Surjectivity on objects comes directly from surjectivity of the covering map.
    intro y
    rcases y with ⟨b⟩
    obtain ⟨e, rfl⟩ := hp.surjective b
    exact ⟨mk e, rfl⟩
  · -- For a fixed source point, the star map encodes unique lifting of path classes.
    rintro ⟨e⟩
    -- Route correction: prove bijectivity on the star by separate surjectivity and injectivity,
    -- avoiding the older transport-heavy attempt to construct a global inverse on `Under`.
    exact ⟨fundamentalGroupoidMap_star_injective hp e, fundamentalGroupoidMap_star_surjective hp e⟩

end IsPathConnectedCoveringMap

/-! ### Proposition_3_3_5 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Proposition 3.3.5: for a covering functor of groupoids `p : E ⥤ B`, the induced map on the
vertex group at `e` is injective. -/
-- Proof sketch: if two loops at `e` have the same image in the vertex group at `p.obj e`, view
-- them as objects of the star `Under e`. The induced star map `Under.post p` sends these two
-- objects to the same object of `Under (p.obj e)`, so injectivity from `hp.star_bijective e`
-- forces the original loops to agree.
theorem mapVertexGroup_injective (hp : Functor.IsCovering p) (e : E) :
    Function.Injective (Functor.mapVertexGroup p e) := by
  intro γ δ hγδ
  have hUnder :
      (Under.post p).obj (Under.mk γ) = (Under.post p).obj (Under.mk δ) :=
    congrArg Under.mk hγδ
  have hEq : Under.mk γ = Under.mk δ := (hp.star_bijective e).injective hUnder
  cases hEq
  rfl

end CategoryTheory.Functor.IsCovering

/-! ### Proposition_3_3_6 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open scoped Pointwise

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Helper for Proposition 3.3.6: the transported image of the vertex group at a fiber point
coincides with the stabilizer of that point under fiber translation. -/
private theorem mapVertexGroup_range_eq_stabilizer (hp : Functor.IsCovering p) {b : B}
    (e : p.Fiber b) :
    by
      let hact : MulAction (b ⟶ b) (p.Fiber b) := by
        simpa using CategoryTheory.Functor.vertexGroupAction (fiberTranslationFunctor hp) b
      letI := hact
      exact e.2 ▸ (Functor.mapVertexGroup p e.1).range =
        MulAction.stabilizer (b ⟶ b) e := by
  rcases e with ⟨e, rfl⟩
  -- Reduce to the distinguished basepoint of the fiber, where Lemma 3.4.11 gives the exact
  -- stabilizer computation.
  simpa [fiberTranslationMulAction] using
    (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm

/-- Proposition 3.3.6: every conjugate of the subgroup `p(π(E,e))` attached to a chosen fiber
point `e` is the corresponding subgroup for another point of the same fiber. -/
-- Proof sketch: equip the fiber with the canonical owner action
-- `Functor.vertexGroupAction (fiberTranslationFunctor hp) b`. The
-- translated point has
-- stabilizer `MulAut.conj g • MulAction.stabilizer _ e` by
-- `MulAction.stabilizer_smul_eq_stabilizer_map_conj`, and the basepoint isotropy theorem
-- `fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range` identifies these stabilizers
-- with
-- the source-facing transported image subgroups.
theorem exists_fiberPoint_mapVertexGroup_range_eq_conjugate (hp : Functor.IsCovering p) {b : B}
    (e : p.Fiber b) (g : b ⟶ b) :
    ∃ e' : p.Fiber b,
      e'.2 ▸ (Functor.mapVertexGroup p e'.1).range =
        MulAut.conj g • (e.2 ▸ (Functor.mapVertexGroup p e.1).range) := by
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  -- Follow the source proof: translate the chosen fiber point by the loop `g`.
  refine ⟨g • e, ?_⟩
  calc
    (g • e).2 ▸ (Functor.mapVertexGroup p (g • e).1).range
        = MulAction.stabilizer (b ⟶ b) (g • e) := by
          -- Rewrite the subgroup attached to the translated point as its stabilizer.
          simpa using mapVertexGroup_range_eq_stabilizer hp (g • e)
    _ = (MulAction.stabilizer (b ⟶ b) e).map (MulAut.conj g).toMonoidHom := by
          -- Translating a point conjugates its stabilizer inside the loop group.
          simpa using MulAction.stabilizer_smul_eq_stabilizer_map_conj g e
    _ = MulAut.conj g • MulAction.stabilizer (b ⟶ b) e := by
          rfl
    _ = MulAut.conj g • (e.2 ▸ (Functor.mapVertexGroup p e.1).range) := by
          -- Rewrite the original subgroup back from the stabilizer description.
          rw [mapVertexGroup_range_eq_stabilizer hp e]

end CategoryTheory.Functor.IsCovering

/-! ### Definition_3_3_7 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- The canonical equivalence on stars induced by a covering functor at an object. -/
noncomputable def starEquiv (hp : Functor.IsCovering p) (e : E) :
    Under e ≃ Under (p.obj e) :=
  Equiv.ofBijective ((Under.post p : Under e ⥤ Under (p.obj e)).obj) (hp.star_bijective e)

/-- The lifted star object over a base arrow starting at a chosen point of the fiber. -/
noncomputable def starLift (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b')
    (x : p.Fiber b) : Under x.1 :=
  (starEquiv hp x.1).symm (x.2.symm ▸ (Under.mk f : Under b))

/-- Helper for Definition 3.3.7: transporting the base arrow into the corresponding under object
over a chosen fiber point yields the expected `Under.mk` term. -/
lemma fiber_transport_under_mk {b b' : B} (f : b ⟶ b') (x : p.Fiber b) :
    x.2.symm ▸ (Under.mk f : Under b) = Under.mk (eqToHom x.2 ≫ f) := by
  -- Normalize the fiber witness so the transport becomes the identity transport.
  rcases x with ⟨e, h⟩
  subst h
  simp

/-- Helper for Definition 3.3.7: applying `Under.post p` to the chosen lift recovers the transported
base arrow in the target star. -/
lemma starLift_post_eq (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') (x : p.Fiber b) :
    (Under.post p).obj (starLift hp f x) = x.2.symm ▸ (Under.mk f : Under b) := by
  -- `starLift` was defined by applying the inverse star equivalence to this transported arrow.
  change (starEquiv hp x.1) (starLift hp f x) = x.2.symm ▸ (Under.mk f : Under b)
  rw [starLift]
  exact (starEquiv hp x.1).apply_symm_apply _

/-- The target of the chosen lifted star object lies over the codomain of the base arrow. -/
-- Proof sketch: apply `(starEquiv hp x.1).apply_symm_apply` to the transported object
-- `Under.mk f`, then read off the equality of right endpoints after transporting along `x.2`.
theorem starLift_obj (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b')
    (x : p.Fiber b) : p.obj (starLift hp f x).right = b' := by
  -- Reduce to the basepoint case so the transport on the under object disappears.
  rcases x with ⟨e, rfl⟩
  have h := starLift_post_eq hp f ⟨e, rfl⟩
  simp [Under.post] at h
  -- The right endpoint of the lifted star object is the codomain of `f`.
  simpa using congrArg Comma.right h

/-- Helper for Definition 3.3.7: the chosen lift of an identity arrow from a basepoint is the
identity star object. -/
lemma starLift_id_eq (hp : Functor.IsCovering p) (e : E) :
    starLift hp (𝟙 (p.obj e)) ⟨e, rfl⟩ = Under.mk (𝟙 e) := by
  -- Compare the two candidates after applying the injective star map.
  apply (hp.star_bijective e).injective
  calc
    (Under.post p).obj (starLift hp (𝟙 (p.obj e)) ⟨e, rfl⟩) =
        Under.mk (𝟙 (p.obj e)) := by
      simpa using starLift_post_eq hp (𝟙 (p.obj e)) ⟨e, rfl⟩
    _ = (Under.post p).obj (Under.mk (𝟙 e)) := by
      simp [Under.post]

/-- Helper for Definition 3.3.7: the image of the chosen lift under `p` is the original base
arrow, with the source and target adjusted by the fiber witnesses. -/
lemma starLift_hom_over (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') (x : p.Fiber b) :
    p.map (starLift hp f x).hom =
      eqToHom x.2 ≫ f ≫ eqToHom (starLift_obj hp f x).symm := by
  -- Route correction: expose the hom-level content of `starLift_post_eq` before comparing
  -- composite lifts, so the dependent transport is handled by `conj_eqToHom_iff_heq`.
  have h := starLift_post_eq hp f x
  rw [fiber_transport_under_mk] at h
  -- `Under.mk` equality gives the lifted hom as a heterogeneous copy of the base arrow.
  injection h with _ _ hh
  have hh' : p.map (starLift hp f x).hom ≍ f := by
    simpa using hh
  -- Convert the heterogeneous equality into the explicit `eqToHom`-conjugated formula.
  exact (conj_eqToHom_iff_heq _ _ x.2 (starLift_obj hp f x)).2 hh'

/-- Helper for Definition 3.3.7: postcomposing a morphism in an under category with the
`eqToHom` coming from a codomain equality does not change the corresponding under object. -/
lemma under_mk_comp_eqToHom {X Y Z : B} (m : X ⟶ Y) (h : Y = Z) :
    Under.mk (m ≫ eqToHom h) = Under.mk m := by
  -- Collapse the codomain transport by reducing to the reflexive case.
  cases h
  simp

/-- Helper for Definition 3.3.7: lifting a composite from a basepoint lands at the same endpoint
as first lifting the first arrow and then lifting the second from the intermediate endpoint. -/
lemma starLift_comp_endpoint_eq (hp : Functor.IsCovering p) {e : E} {b₂ b₃ : B}
    (f : p.obj e ⟶ b₂) (g : b₂ ⟶ b₃) :
    (starLift hp (f ≫ g) ⟨e, rfl⟩).right =
      (starLift hp g ⟨(starLift hp f ⟨e, rfl⟩).right, starLift_obj hp f ⟨e, rfl⟩⟩).right := by
  let u := starLift hp f ⟨e, rfl⟩
  let v := starLift hp g ⟨u.right, starLift_obj hp f ⟨e, rfl⟩⟩
  let a : p.obj u.right = b₂ := by
    simpa [u] using starLift_obj hp f ⟨e, rfl⟩
  let b : p.obj v.right = b₃ := by
    simpa [u, v] using starLift_obj hp g ⟨u.right, a⟩
  have hu : p.map u.hom = f ≫ eqToHom a.symm := by
    -- Normalize the first chosen lift to the base arrow `f`.
    simpa [u, a] using starLift_hom_over hp f ⟨e, rfl⟩
  have hv : p.map v.hom = eqToHom a ≫ g ≫ eqToHom b.symm := by
    -- Normalize the second chosen lift to the base arrow `g`.
    simpa [u, v, a, b] using starLift_hom_over hp g ⟨u.right, a⟩
  have hmorph : p.map u.hom ≫ p.map v.hom = f ≫ g ≫ eqToHom b.symm := by
    -- Compose the normalized lifts and cancel the middle transport.
    rw [hu]
    calc
      (f ≫ eqToHom a.symm) ≫ p.map v.hom =
          (f ≫ eqToHom a.symm) ≫ (eqToHom a ≫ g ≫ eqToHom b.symm) := by
        exact congrArg (fun k ↦ (f ≫ eqToHom a.symm) ≫ k) hv
      _ = f ≫ g ≫ eqToHom b.symm := by
        simp [Category.assoc]
  have hpost_explicit : (Under.post p).obj (Under.mk (u.hom ≫ v.hom)) = Under.mk (f ≫ g) := by
    -- The explicit composite lift maps to the same transported under object as `f ≫ g`.
    calc
      (Under.post p).obj (Under.mk (u.hom ≫ v.hom)) =
          Under.mk (p.map u.hom ≫ p.map v.hom) := by
        simp [Under.post]
      _ = Under.mk (f ≫ g ≫ eqToHom b.symm) := by
        exact congrArg Under.mk hmorph
      _ = Under.mk (f ≫ g) := by
        simpa [Category.assoc] using under_mk_comp_eqToHom (f ≫ g) b.symm
  have hpost_lift : (Under.post p).obj (starLift hp (f ≫ g) ⟨e, rfl⟩) = Under.mk (f ≫ g) := by
    -- The chosen lift of `f ≫ g` maps to the same under object by construction.
    simpa using starLift_post_eq hp (f ≫ g) ⟨e, rfl⟩
  have hstar : starLift hp (f ≫ g) ⟨e, rfl⟩ = Under.mk (u.hom ≫ v.hom) := by
    -- Injectivity of the star map identifies the chosen composite lift with the explicit one.
    apply (hp.star_bijective e).injective
    exact hpost_lift.trans hpost_explicit.symm
  -- Project the equality of lifts to their endpoints.
  simpa [u, v] using congrArg Comma.right hstar

/-- Definition 3.3.7: the fiber translation functor of a covering functor sends each object to its
fiber and each morphism to the target map of the unique lifted arrow starting at each point of that
fiber. -/
noncomputable def fiberTranslationFunctor (hp : Functor.IsCovering p) : B ⥤ Type u₁ where
  obj b := p.Fiber b
  map f := TypeCat.ofHom fun x => ⟨(starLift hp f x).right, starLift_obj hp f x⟩
  map_id b := by
    ext x
    rcases x with ⟨e, rfl⟩
    apply Subtype.ext
    simpa using congrArg Comma.right (starLift_id_eq hp e)
  map_comp f g := by
    ext x
    rcases x with ⟨e, rfl⟩
    apply Subtype.ext
    simpa using starLift_comp_endpoint_eq hp f g

/-- Fiber translation along a base morphism sends a point to the endpoint of its lifted arrow. -/
noncomputable def fiberTranslationMap (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    p.Fiber b → p.Fiber b' :=
  (fiberTranslationFunctor hp).map f

/-- The canonical vertex-group action on a fiber induced by fiber translation. -/
@[reducible]
noncomputable def fiberTranslationMulAction (hp : Functor.IsCovering p) (b : B) :
    MulAction (b ⟶ b) (p.Fiber b) :=
  Functor.vertexGroupAction (fiberTranslationFunctor hp) b

namespace fiberTranslationMulAction

/-- The fiber-translation action is pretransitive. -/
abbrev IsPretransitive (hp : Functor.IsCovering p) (b : B) : Prop :=
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  MulAction.IsPretransitive (b ⟶ b) (p.Fiber b)

/-- The fiber-translation action is transitive. -/
abbrev IsTransitive (hp : Functor.IsCovering p) (b : B) : Prop :=
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  MulAction.IsTransitive (b ⟶ b) (p.Fiber b)

/-- The fiber-translation action is free. -/
abbrev IsFree (hp : Functor.IsCovering p) (b : B) : Prop :=
  letI : MulAction (b ⟶ b) (p.Fiber b) := fiberTranslationMulAction hp b
  IsCancelSMul (b ⟶ b) (p.Fiber b)

end fiberTranslationMulAction

/-- Fiber translation along an identity arrow is the identity map on the fiber. -/
theorem fiberTranslationMap_id (hp : Functor.IsCovering p) (b : B) :
    fiberTranslationMap hp (𝟙 b) = id := by
  funext x
  have h := ConcreteCategory.congr_hom ((fiberTranslationFunctor hp).map_id b) x
  simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at h
  exact h

/-- Fiber translation along a composite is the composite of the corresponding fiber maps. -/
theorem fiberTranslationMap_comp (hp : Functor.IsCovering p) {b₁ b₂ b₃ : B} (f : b₁ ⟶ b₂)
    (g : b₂ ⟶ b₃) :
    fiberTranslationMap hp (f ≫ g) =
      fiberTranslationMap hp g ∘ fiberTranslationMap hp f := by
  funext x
  have h := ConcreteCategory.congr_hom ((fiberTranslationFunctor hp).map_comp f g) x
  simp only [CategoryTheory.comp_apply] at h
  exact h

/-- The fiber translation functor sends an object of the base groupoid to its fiber. -/
@[simp] theorem fiberTranslationFunctor_obj (hp : Functor.IsCovering p) (b : B) :
    (fiberTranslationFunctor hp).obj b = p.Fiber b := rfl

/-- The fiber translation functor acts on a morphism by fiber translation along that morphism. -/
theorem fiberTranslationFunctor_map (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b')
    (x : p.Fiber b) :
    (fiberTranslationFunctor hp).map f x = fiberTranslationMap hp f x := rfl

/-- The fiber translation functor applies to a point of the fiber by the corresponding fiber
translation map. -/
theorem fiberTranslationFunctor_map_apply (hp : Functor.IsCovering p) {b b' : B}
    (f : b ⟶ b') (x : p.Fiber b) :
    (fiberTranslationFunctor hp).map f x = fiberTranslationMap hp f x := rfl

end CategoryTheory.Functor.IsCovering

/-! ### Lemma_3_3_8 (from Chap03) -/
universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/- Lemma 3.3.8: the fiber translation assignment `T(p)` of Definition 3.3.7 is the canonical
functor sending each object of the base groupoid to its fiber and each morphism to the induced
translation map between fibers. -/
recall fiberTranslationFunctor (hp : Functor.IsCovering p) : B ⥤ Type u₁

end CategoryTheory.Functor.IsCovering

/-! ### Example_3_3_9 (from Chap03) -/
universe u v

open CategoryTheory FundamentalGroupoid

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- Fiber translation on ordinary fibers, obtained by transporting the categorical fiber
translation for `hp.fundamentalGroupoidMap` across the canonical fiber equivalences of
Proposition 3.3.4. -/
noncomputable abbrev fiberTranslationMap (hp : IsPathConnectedCoveringMap p) {b₀ b₁ : B}
    (f : mk b₀ ⟶ mk b₁) : p ⁻¹' {b₀} → p ⁻¹' {b₁} :=
  hp.fundamentalGroupoidMapFiberEquiv b₁ ∘
    Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering f ∘
    (hp.fundamentalGroupoidMapFiberEquiv b₀).symm

@[simp] theorem fiberTranslationMap_apply (hp : IsPathConnectedCoveringMap p) {b₀ b₁ : B}
    (f : mk b₀ ⟶ mk b₁) (e : p ⁻¹' {b₀}) :
    hp.fiberTranslationMap f e =
      hp.fundamentalGroupoidMapFiberEquiv b₁
        (Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering f
          ((hp.fundamentalGroupoidMapFiberEquiv b₀).symm e)) :=
  rfl

/-- Helper for Example 3.3.9: changing the endpoint of a path class only changes the codomain
bookkeeping of the corresponding `Under.mk` object. -/
private theorem under_mk_fromPath_cast_eq {x y z : B} (q : Path.Homotopic.Quotient x z)
    (h : y = z) :
    (Under.mk (fromPath q) : Under (mk x)) = Under.mk (fromPath (q.cast rfl h)) := by
  -- Collapse the endpoint transport to the reflexive case.
  cases h
  simp

/-- Helper for Example 3.3.9: the projected class of the canonical lifted path is the original
base path class after the endpoint cast coming from `liftPath_lifts`. -/
private theorem lifted_path_projects_to_base_class (hp : IsPathConnectedCoveringMap p)
    {e : E} {b : B} (γ : Path (p e) b) :
    ((Path.Homotopic.Quotient.mk
        (Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
          (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl)).map
      ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
      ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target).symm =
        Path.Homotopic.Quotient.mk γ := by
  -- Rewrite the quotient statement back to an equality of actual paths.
  change Path.Homotopic.Quotient.mk
      (((Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
        (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl).map
          hp.isCoveringMap.continuous).cast rfl
        ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target).symm) =
      Path.Homotopic.Quotient.mk γ
  -- The covering projection of the lifted path agrees pointwise with `γ`.
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simpa using congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) t

/-- Helper for Example 3.3.9: the categorical star lift of a path class is the under-object
represented by the actual lifted path starting at the chosen point. -/
private theorem starLift_fromPath_eq_lifted_under (hp : IsPathConnectedCoveringMap p)
    {e : E} {b : B} (γ : Path (p e) b) :
    Functor.IsCovering.starLift hp.fundamentalGroupoidMap_isCovering
      (fromPath (.mk γ)) ⟨mk e, rfl⟩ =
      Under.mk
        (fromPath
          (Path.Homotopic.Quotient.mk
            (Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
              (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl))) := by
  let δ : Path e (hp.isCoveringMap.liftPath γ e γ.source 1) :=
    Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl
  suffices htarget :
      Functor.IsCovering.starLift hp.fundamentalGroupoidMap_isCovering
        (fromPath (.mk γ)) ⟨mk e, rfl⟩ =
        Under.mk (fromPath (Path.Homotopic.Quotient.mk δ)) by
    simpa [δ] using htarget
  have hpost_explicit :
      (Under.post hp.fundamentalGroupoidMap).obj
          (Under.mk (fromPath (Path.Homotopic.Quotient.mk δ))) =
        (Under.mk
          (fromPath ((Path.Homotopic.Quotient.mk δ).map ⟨p, hp.isCoveringMap.continuous⟩)) :
            Under (mk (p e))) := by
    -- Applying `Under.post` to the explicit lifted path unfolds directly to the projected class.
    rfl
  have hpost_target :
      Under.mk (fromPath (.mk γ)) =
        (Under.post hp.fundamentalGroupoidMap).obj
          (Under.mk (fromPath (Path.Homotopic.Quotient.mk δ))) := by
    -- The projected lifted path represents the same base class as `γ`, up to the endpoint cast.
    calc
      Under.mk (fromPath (.mk γ)) = Under.mk
          (fromPath
            (((Path.Homotopic.Quotient.mk δ).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
              ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans
                γ.target).symm)) := by
        symm
        exact congrArg Under.mk
          (congrArg fromPath (lifted_path_projects_to_base_class hp γ))
      _ = Under.mk
            (fromPath ((Path.Homotopic.Quotient.mk δ).map ⟨p, hp.isCoveringMap.continuous⟩)) := by
        symm
        exact under_mk_fromPath_cast_eq _
          ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target).symm
      _ = (Under.post hp.fundamentalGroupoidMap).obj
            (Under.mk (fromPath (Path.Homotopic.Quotient.mk δ))) := by
        exact hpost_explicit.symm
  -- Compare the chosen star lift with the explicit lifted path after applying `Under.post`.
  apply (hp.fundamentalGroupoidMap_isCovering.star_bijective (mk e)).injective
  exact
    (Functor.IsCovering.starLift_post_eq hp.fundamentalGroupoidMap_isCovering
      (fromPath (.mk γ)) ⟨mk e, rfl⟩).trans hpost_target

/-- Helper for Example 3.3.9: fiber translation along a represented path class lands at the
endpoint of the corresponding lifted path. -/
private theorem fiberTranslationMap_fromPath_eq_endpoint (hp : IsPathConnectedCoveringMap p)
    {e : E} {b : B} (γ : Path (p e) b) :
    hp.fiberTranslationMap (fromPath (.mk γ)) ⟨e, rfl⟩ =
      ⟨hp.isCoveringMap.liftPath γ e γ.source 1,
        (congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target⟩ := by
  let δ : Path e (hp.isCoveringMap.liftPath γ e γ.source 1) :=
    Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl
  -- Transport the claim into the categorical fiber, where the star-lift description is explicit.
  apply (hp.fundamentalGroupoidMapFiberEquiv b).symm.injective
  apply Subtype.ext
  -- Equality of lifted under-objects identifies the endpoint object in the fundamental groupoid.
  simpa [IsPathConnectedCoveringMap.fiberTranslationMap, δ] using
    congrArg Comma.right (starLift_fromPath_eq_lifted_under hp γ)

/-- Example 3.3.9: for a covering space, the fiber-translation map along a path class agrees with
the monodromy map sending a chosen lift of the starting point to the endpoint of the lifted path
class. -/
-- Proof sketch: transport the categorical fiber of `hp.fundamentalGroupoidMap` to the ordinary
-- fiber `p ⁻¹' {b}` via `fundamentalGroupoidMapFiberEquiv`, then compare the resulting map with the
-- canonical monodromy functor of `hp.isCoveringMap`; both send a starting point in the fiber to
-- the endpoint of the unique lifted path class.
theorem fiberTranslationMap_eq_monodromy (hp : IsPathConnectedCoveringMap p)
    {b₀ b₁ : B} (f : mk b₀ ⟶ mk b₁) :
    hp.fiberTranslationMap f = hp.isCoveringMap.monodromy f := by
  funext x
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  rcases x with ⟨e, rfl⟩
  -- Compare both maps on a literal basepoint fiber by the explicit lifted-path formula.
  rw [fiberTranslationMap_fromPath_eq_endpoint hp γ]
  rfl

/-- Evaluating fiber translation on the homotopy class of a path gives the endpoint of the lifted
representative path starting at the chosen point of the fiber. -/
-- Proof sketch: specialize `fiberTranslationMap_eq_monodromy` to the morphism
-- `fromPath (.mk γ)` and then apply mathlib's endpoint formula
-- `hp.isCoveringMap.monodromy_map (.mk γ)`.
theorem fiberTranslationMap_fromPath_eq_liftPath_endpoint
    (hp : IsPathConnectedCoveringMap p) {b₀ b₁ : B} (γ : Path b₀ b₁) (e : p ⁻¹' {b₀}) :
    hp.fiberTranslationMap (fromPath (.mk γ)) e =
      ⟨hp.isCoveringMap.liftPath γ e.1 (γ.source.trans e.2.symm) 1,
        (congr_fun (hp.isCoveringMap.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) 1).trans
          γ.target⟩ := by
  rcases e with ⟨e, rfl⟩
  -- After normalizing the fiber point to `⟨e, rfl⟩`, the private path-level helper applies.
  simpa using fiberTranslationMap_fromPath_eq_endpoint hp γ

end IsPathConnectedCoveringMap

/-! ### Proposition_3_3_10 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open FundamentalGroupoid
open Path.Homotopic.Quotient
open CategoryTheory.Functor.IsCovering
open scoped Cardinal

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Fiber translation along a morphism of the base groupoid is a bijection between the
corresponding fibers. -/
-- Proof sketch: `fiberTranslationFunctor hp` sends the isomorphism `asIso f` in the base groupoid
-- to an isomorphism of fibers in `Type`, whose underlying equivalence is bijective.
theorem fiberTranslationMap_bijective (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    Function.Bijective (fiberTranslationMap hp f) := by
  simpa using ((fiberTranslationFunctor hp).mapIso (asIso f)).toEquiv.bijective

/-- Proposition 3.3.10: fibers over base objects connected by a morphism in a covering functor of
groupoids have the same cardinality, and hence so do the corresponding fibers of a covering space
after passing to fundamental groupoids. -/
-- Proof sketch: apply `Cardinal.mk_congr` to the equivalence of fibers induced by
-- `fiberTranslationFunctor hp` on the isomorphism `asIso f`.
theorem fiber_cardinal_eq_of_hom (hp : Functor.IsCovering p) {b b' : B} (f : b ⟶ b') :
    #(p.Fiber b) = #(p.Fiber b') := by
  simpa using Cardinal.mk_congr (((fiberTranslationFunctor hp).mapIso (asIso f)).toEquiv)

/-- Proposition 3.3.10: for a covering functor of groupoids over a connected base groupoid,
any two fibers have the same cardinality. -/
-- Proof sketch: in a connected groupoid there exists a morphism between any two objects, so the
-- explicit-arrow case `fiber_cardinal_eq_of_hom` applies.
theorem fiber_cardinal_eq [CategoryTheory.IsConnected B] (hp : Functor.IsCovering p) (b b' : B) :
    #(p.Fiber b) = #(p.Fiber b') := by
  let ⟨f⟩ := (inferInstance : Nonempty (b ⟶ b'))
  exact fiber_cardinal_eq_of_hom hp f

end CategoryTheory.Functor.IsCovering

namespace IsPathConnectedCoveringMap

variable {E : Type u₁} {B : Type u₂} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B}

/-- The covering-space form of Proposition 3.3.10: over a path-connected base, any two fibers of a
path-connected covering map have the same cardinality. -/
-- Proof sketch: apply the connected-groupoid statement to the induced covering functor on
-- fundamental groupoids and transport its fibers back to ordinary fibers via
-- `fundamentalGroupoidMapFiberEquiv`.
theorem fiber_cardinal_eq (hp : IsPathConnectedCoveringMap p) [PathConnectedSpace B] (b b' : B) :
    #(p ⁻¹' {b}) = #(p ⁻¹' {b'}) := by
  let f : mk b ⟶ mk b' :=
    fromPath (mk (PathConnectedSpace.somePath b b'))
  calc
    #(p ⁻¹' {b}) = #(hp.fundamentalGroupoidMap.Fiber (mk b)) := by
      simpa using Cardinal.mk_congr (hp.fundamentalGroupoidMapFiberEquiv b).symm
    _ = #(hp.fundamentalGroupoidMap.Fiber (mk b')) := by
      exact fiber_cardinal_eq_of_hom hp.fundamentalGroupoidMap_isCovering f
    _ = #(p ⁻¹' {b'}) := by
      simpa using Cardinal.mk_congr (hp.fundamentalGroupoidMapFiberEquiv b')

end IsPathConnectedCoveringMap

/-! ### Definition_3_3_11 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]

/-- Definition 3.3.11 (1): a covering functor of groupoids is regular at `e` if the image of the
induced map on the vertex group at `e` is a normal subgroup of the vertex group at `p.obj e`. -/
def IsRegularCovering (p : E ⥤ B) (e : E) : Prop :=
  Functor.IsCovering p ∧ (Functor.mapVertexGroup p e).range.Normal

namespace IsRegularCovering

variable {p : E ⥤ B} {e : E}

/-- A regular covering functor is, in particular, a covering functor. -/
theorem isCovering (hp : IsRegularCovering p e) : Functor.IsCovering p :=
  hp.1

/-- In a regular covering functor, the image of the induced map on vertex groups at `e` is
normal. -/
theorem normal_mapVertexGroup_range (hp : IsRegularCovering p e) :
    (Functor.mapVertexGroup p e).range.Normal :=
  hp.2

instance (hp : IsRegularCovering p e) : Functor.IsCovering p :=
  hp.isCovering

end IsRegularCovering

/-- Definition 3.3.11 (2): a covering functor of groupoids is universal at `e` if the image of
the induced map on the vertex group at `e` is the trivial subgroup of the vertex group at
`p.obj e`. -/
def IsUniversalCovering (p : E ⥤ B) (e : E) : Prop :=
  Functor.IsCovering p ∧ (Functor.mapVertexGroup p e).range = ⊥

namespace IsUniversalCovering

variable {p : E ⥤ B} {e : E}

/-- A universal covering functor is, in particular, a covering functor. -/
theorem isCovering (hp : IsUniversalCovering p e) : Functor.IsCovering p :=
  hp.1

/-- In a universal covering functor, the image of the induced map on vertex groups at `e` is
trivial. -/
theorem mapVertexGroup_range_eq_bot (hp : IsUniversalCovering p e) :
    (Functor.mapVertexGroup p e).range = ⊥ :=
  hp.2

instance (hp : IsUniversalCovering p e) : Functor.IsCovering p :=
  hp.isCovering

/-- A universal covering functor is regular at the chosen base object. -/
-- Proof sketch: the trivial subgroup is normal, so the triviality condition on the image of the
-- induced vertex-group map implies the normality condition required for regularity.
theorem isRegularCovering (hp : IsUniversalCovering p e) : IsRegularCovering p e := by
  refine ⟨hp.isCovering, ?_⟩
  rw [hp.mapVertexGroup_range_eq_bot]
  exact (Subgroup.normal_bot : (⊥ : Subgroup (p.obj e ⟶ p.obj e)).Normal)

instance (hp : IsUniversalCovering p e) : IsRegularCovering p e :=
  hp.isRegularCovering

end IsUniversalCovering

end CategoryTheory.Functor

/-! ### Lemma_3_3_12 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Helper for Lemma 3.3.12: the isotropy subgroup of the distinguished fiber point `⟨e, rfl⟩`
under fiber translation is exactly the image of the vertex group at `e`. -/
private theorem basepoint_stabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) (e : E) :
    let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
    letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
      fiberTranslationMulAction hp (p.obj e)
    MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ =
      (Functor.mapVertexGroup p e).range := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  ext γ
  constructor
  · intro hγ
    rw [MulAction.mem_stabilizer_iff] at hγ
    change fiberTranslationMap hp γ⁻¹ x₀ = x₀ at hγ
    let u := starLift hp γ⁻¹ x₀
    -- The chosen lift of `γ⁻¹` ends again at `e`, so it closes up to a loop at `e`.
    have hright : u.right = e := by
      exact congrArg Subtype.val hγ
    have hobj : starLift_obj hp γ⁻¹ x₀ = congrArg p.obj hright := by
      apply Subsingleton.elim
    have hloop : p.map (u.hom ≫ eqToHom hright) = γ⁻¹ := by
      -- Normalize the image of the chosen lift and cancel the endpoint transport.
      have hmap : p.map u.hom = γ⁻¹ ≫ eqToHom (congrArg p.obj hright).symm := by
        simpa [u, x₀, hobj] using starLift_hom_over hp γ⁻¹ x₀
      have hmapEqToHom : p.map (eqToHom hright) = eqToHom (congrArg p.obj hright) := by
        simpa using eqToHom_map p hright
      have hcancel :
          eqToHom (congrArg p.obj hright).symm ≫ p.map (eqToHom hright) = 𝟙 (p.obj e) := by
        rw [hmapEqToHom]
        simp
      calc
        p.map (u.hom ≫ eqToHom hright) = p.map u.hom ≫ p.map (eqToHom hright) := by
          simp
        _ = (γ⁻¹ ≫ eqToHom (congrArg p.obj hright).symm) ≫ p.map (eqToHom hright) := by
          exact congrArg (fun k ↦ k ≫ p.map (eqToHom hright)) hmap
        _ = γ⁻¹ ≫ (eqToHom (congrArg p.obj hright).symm ≫ p.map (eqToHom hright)) := by
          simp [Category.assoc]
        _ = γ⁻¹ := by
          rw [hcancel]
          simp
    have hmem_inv : γ⁻¹ ∈ (Functor.mapVertexGroup p e).range := by
      refine ⟨u.hom ≫ eqToHom hright, ?_⟩
      exact hloop
    simpa using Subgroup.inv_mem (Functor.mapVertexGroup p e).range hmem_inv
  · rintro ⟨δ, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    -- Compare the chosen lift of `p.map δ⁻¹` with the actual inverse loop `δ⁻¹`.
    have hstar : starLift hp ((Functor.mapVertexGroup p e) δ)⁻¹ x₀ = Under.mk δ⁻¹ := by
      apply (hp.star_bijective e).injective
      calc
        (Under.post p).obj (starLift hp ((Functor.mapVertexGroup p e) δ)⁻¹ x₀) =
            Under.mk (((Functor.mapVertexGroup p e) δ)⁻¹) := by
          simpa [x₀] using starLift_post_eq hp (((Functor.mapVertexGroup p e) δ)⁻¹) x₀
        _ = (Under.post p).obj (Under.mk δ⁻¹) := by
          simp [Under.post]
    apply Subtype.ext
    -- Equality of the lifted under-objects identifies their endpoints.
    change (starLift hp ((Functor.mapVertexGroup p e) δ)⁻¹ x₀).right = e
    simpa [x₀] using congrArg Comma.right hstar

/-- Helper for Lemma 3.3.12: universality is equivalent to triviality of the stabilizer of the
distinguished fiber point. -/
private theorem isUniversalCovering_iff_basepoint_stabilizer_eq_bot
    (hp : Functor.IsCovering p) (e : E) :
    let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
    letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
      fiberTranslationMulAction hp (p.obj e)
    Functor.IsUniversalCovering p e ↔
      MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ = ⊥ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · rintro ⟨_, hbot⟩
    -- Rewrite the vertex-group image subgroup as the basepoint stabilizer.
    simpa [basepoint_stabilizer_eq_mapVertexGroup_range hp e] using hbot
  · intro hbot
    -- The covering hypothesis is already fixed, so only the subgroup equality remains.
    exact ⟨hp, by simpa [basepoint_stabilizer_eq_mapVertexGroup_range hp e] using hbot⟩

/-- Helper for Lemma 3.3.12: in a pretransitive action, freeness is equivalent to triviality of
the stabilizer of one chosen point. -/
private theorem isCancelSMul_iff_stabilizer_eq_bot_of_isPretransitive
    {G : Type u₁} {S : Type u₂} [Group G] [MulAction G S] [MulAction.IsPretransitive G S]
    (s : S) : IsCancelSMul G S ↔ MulAction.stabilizer G s = ⊥ := by
  constructor
  · intro hfree
    letI : IsCancelSMul G S := hfree
    -- A free action has trivial stabilizer at every point, in particular at `s`.
    exact IsCancelSMul.stabilizer_eq_bot s
  · intro hs
    -- Pretransitivity makes every stabilizer a conjugate of the chosen one.
    rw [isCancelSMul_iff_stabilizer_eq_bot]
    intro t
    rcases (MulAction.isPretransitive_iff_base s).mp ‹MulAction.IsPretransitive G S› t with
      ⟨g, rfl⟩
    simpa [hs] using MulAction.stabilizer_smul_eq_stabilizer_map_conj g s

/-- Lemma 3.3.12: if the fiber-translation action on the fiber over `p.obj e` is pretransitive,
then a covering functor is universal at `e` exactly when that action is free. -/
-- Proof sketch: identify universality with triviality of the image subgroup
-- `Functor.mapVertexGroup p e`. By the basepoint-stabilizer computation from Lemma 3.4.11, this
-- is the triviality of the stabilizer of `⟨e, rfl⟩`. Under pretransitivity every fiber point is a
-- translate of `⟨e, rfl⟩`, so all stabilizers are conjugate to the basepoint stabilizer, hence all
-- are trivial exactly when the action is free.
theorem isUniversalCovering_iff_fiberTranslation_isFree_of_isPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (hpre : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    Functor.IsUniversalCovering p e ↔ fiberTranslationMulAction.IsFree hp (p.obj e) := by
  letI := fiberTranslationMulAction hp (p.obj e)
  change Functor.IsUniversalCovering p e ↔ IsCancelSMul (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e))
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  -- First rewrite universality as triviality of the isotropy subgroup at the base fiber point.
  have hbase :
      Functor.IsUniversalCovering p e ↔
        MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ = ⊥ :=
    isUniversalCovering_iff_basepoint_stabilizer_eq_bot hp e
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := hpre
  -- Then pretransitivity upgrades triviality of one stabilizer to freeness of the action.
  have hfree :
      IsCancelSMul (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) ↔
        MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ = ⊥ :=
    isCancelSMul_iff_stabilizer_eq_bot_of_isPretransitive x₀
  exact hbase.trans hfree.symm

end CategoryTheory.Functor.IsCovering

/-! ### Remark_3_3_13 (from Chap03) -/
universe u₁ u₂ v₁ v₂

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E : Type u₁} {B : Type u₂} [Groupoid.{v₁} E] [Groupoid.{v₂} B]
variable {p : E ⥤ B}

/-- Membership in `p(π(E, e))` is equivalent to fixing the distinguished point `⟨e, rfl⟩` under
direct fiber translation. -/
private theorem mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq
    (hp : Functor.IsCovering p) (e : E) (γ : p.obj e ⟶ p.obj e) :
    γ ∈ (Functor.mapVertexGroup p e).range ↔
      fiberTranslationMap hp γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  constructor
  · intro hγ
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e]
    change fiberTranslationMap hp γ⁻¹ x₀ = x₀ at hstab
    calc
      fiberTranslationMap hp γ x₀ = fiberTranslationMap hp γ (fiberTranslationMap hp γ⁻¹ x₀) := by
        rw [hstab]
      _ = x₀ := by
        change (fiberTranslationFunctor hp).map γ ((fiberTranslationFunctor hp).map γ⁻¹ x₀) = x₀
        rw [← Functor.map_comp_apply]
        simp [show γ⁻¹ ≫ γ = 𝟙 _ from Groupoid.inv_comp γ]
        rfl
  · intro hγ
    have hinv : fiberTranslationMap hp γ⁻¹ x₀ = x₀ := by
      calc
        fiberTranslationMap hp γ⁻¹ x₀ =
            fiberTranslationMap hp γ⁻¹ (fiberTranslationMap hp γ x₀) := by
          rw [hγ]
        _ = x₀ := by
          change (fiberTranslationFunctor hp).map γ⁻¹ ((fiberTranslationFunctor hp).map γ x₀) = x₀
          rw [← Functor.map_comp_apply]
          simp [show γ ≫ γ⁻¹ = 𝟙 _ from Groupoid.comp_inv γ]
          rfl
    have hstab : γ ∈ MulAction.stabilizer (p.obj e ⟶ p.obj e) x₀ := by
      change fiberTranslationMap hp γ⁻¹ x₀ = x₀
      exact hinv
    rwa [fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e] at hstab

/-- Helper for Remark 3.3.13: the direct endpoint map on the fiber is visibly compatible with the
right-coset relation attached to `p(π(E,e))`. -/
private theorem fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range_rightRel
    (hp : Functor.IsCovering p) (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e)
    (hγ : γ₂ * γ₁⁻¹ ∈ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp γ₁ ⟨e, rfl⟩ = fiberTranslationMap hp γ₂ ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  -- First note that the subgroup element appended on the left fixes the base fiber point.
  have hfix : fiberTranslationMap hp (γ₂ * γ₁⁻¹) x₀ = x₀ := by
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e
      (γ₂ * γ₁⁻¹)).mp hγ
  -- Then rewrite `γ₂` as `(γ₂ * γ₁⁻¹) * γ₁` and collapse the fixed-point factor.
  calc
    fiberTranslationMap hp γ₁ x₀ =
        fiberTranslationMap hp γ₁ (fiberTranslationMap hp (γ₂ * γ₁⁻¹) x₀) := by
      rw [hfix]
    _ = fiberTranslationMap hp ((γ₂ * γ₁⁻¹) * γ₁) x₀ := by
      symm
      simpa [mul_assoc] using
        congrArg (fun m ↦ m x₀)
          (fiberTranslationMap_comp hp (γ₂ * γ₁⁻¹) γ₁)
    _ = fiberTranslationMap hp γ₂ x₀ := by
      simp

/-- If two loops differ on the right by an element of `p(π(E, e))`, then they determine the same
endpoint in the distinguished fiber over `p.obj e`. -/
-- Proof sketch: this is exactly the right-coset compatibility already verified for direct fiber
-- translation at the chosen basepoint.
theorem fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range (hp : Functor.IsCovering p)
    (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e)
    (hγ : γ₂ * γ₁⁻¹ ∈ (Functor.mapVertexGroup p e).range) :
    fiberTranslationMap hp γ₁ ⟨e, rfl⟩ = fiberTranslationMap hp γ₂ ⟨e, rfl⟩ := by
  -- Route correction: the public helper now records the right-coset compatibility that matches
  -- the direct endpoint geometry, instead of the false left-coset variant.
  exact fiberTranslation_basepoint_eq_of_mem_mapVertexGroup_range_rightRel hp e γ₁ γ₂ hγ

/-- The canonical map from `π(B, p.obj e) / p(π(E, e))` to the fiber over `p.obj e`. -/
noncomputable def quotientMapVertexGroupRangeToFiber (hp : Functor.IsCovering p) (e : E) :
    (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range → p.Fiber (p.obj e) :=
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  (MulAction.ofQuotientStabilizer (p.obj e ⟶ p.obj e) x₀) ∘
    Subgroup.quotientEquivOfEq
      (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm

/-- Helper for Remark 3.3.13: on a representative, the quotient-to-fiber map acts by inverse-loop
fiber translation from the distinguished basepoint. -/
@[simp] theorem quotientMapVertexGroupRangeToFiber_mk (hp : Functor.IsCovering p) (e : E)
    (γ : p.obj e ⟶ p.obj e) :
    quotientMapVertexGroupRangeToFiber hp e (QuotientGroup.mk γ) =
      fiberTranslationMap hp γ⁻¹ ⟨e, rfl⟩ := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  -- Unfold the stabilizer identification and evaluate both quotient maps on the representative.
  change
    MulAction.ofQuotientStabilizer (p.obj e ⟶ p.obj e) x₀
        (Subgroup.quotientEquivOfEq
          (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm
          (QuotientGroup.mk γ)) =
      fiberTranslationMap hp γ⁻¹ x₀
  rw [Subgroup.quotientEquivOfEq_mk, MulAction.ofQuotientStabilizer_mk]
  rfl

/-- Helper for Remark 3.3.13: the subgroup `p(π(E,e))` viewed inside the reversed endomorphism
group `End (p.obj e)`. -/
private def mapVertexGroupRangeEnd (p : E ⥤ B) (e : E) :
    Subgroup (CategoryTheory.End (p.obj e)) where
  carrier := (Functor.mapVertexGroup p e).range.carrier
  one_mem' := by
    simpa using (Functor.mapVertexGroup p e).range.one_mem
  mul_mem' ha hb := by
    simpa [CategoryTheory.End.mul_def] using (Functor.mapVertexGroup p e).range.mul_mem hb ha
  inv_mem' ha := by
    rcases ha with ⟨δ, rfl⟩
    refine ⟨δ⁻¹, ?_⟩
    exact _root_.map_inv (Functor.mapVertexGroup p e) δ

/-- Helper for Remark 3.3.13: the left-coset relation for the reversed `End` group is the
ordinary right-coset relation for `p(π(E,e))`. -/
private theorem leftRel_mapVertexGroupRangeEnd_iff_rightRel_mapVertexGroup_range
    (e : E) (γ₁ γ₂ : p.obj e ⟶ p.obj e) :
    QuotientGroup.leftRel (mapVertexGroupRangeEnd p e) γ₁ γ₂ ↔
      QuotientGroup.rightRel ((Functor.mapVertexGroup p e).range) γ₁ γ₂ := by
  -- Unfold both quotient relations; the reversed multiplication on `End` turns left cosets into
  -- the original right-coset relation.
  rw [QuotientGroup.leftRel_apply, QuotientGroup.rightRel_apply]
  rfl

/-- Helper for Remark 3.3.13: for the direct `End`-action on the fiber over `p.obj e`, the
stabilizer of the distinguished point is exactly `p(π(E,e))`. -/
theorem vertexGroupMulAction_basepoint_stabilizer_eq_mapVertexGroup_range
    (hp : Functor.IsCovering p) (e : E) :
    let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
    letI : MulAction (CategoryTheory.End (p.obj e)) (p.Fiber (p.obj e)) :=
      CategoryTheory.Functor.vertexGroupMulAction (fiberTranslationFunctor hp) (p.obj e)
    MulAction.stabilizer (CategoryTheory.End (p.obj e)) x₀ =
      mapVertexGroupRangeEnd p e := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (CategoryTheory.End (p.obj e)) (p.Fiber (p.obj e)) :=
    CategoryTheory.Functor.vertexGroupMulAction (fiberTranslationFunctor hp) (p.obj e)
  ext γ
  constructor
  · intro hγ
    -- Rewrite stabilizer membership as a fixed-point statement for direct fiber translation.
    change fiberTranslationMap hp γ x₀ = x₀ at hγ
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e γ).mpr hγ
  · intro hγ
    -- The explicit `End`-subgroup has the same carrier as the image subgroup in the loop group.
    change fiberTranslationMap hp γ x₀ = x₀
    exact (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hp e γ).mp hγ

/-- Remark 3.3.13: if the fiber-translation action of `π(B, p.obj e)` on the fiber over `p.obj e`
is pretransitive, then the canonical map from `π(B, p.obj e) / p(π(E, e))` to that fiber is
bijective. -/
-- Proof sketch: identify `p(π(E, e))` with the stabilizer of the distinguished fiber point
-- `⟨e, rfl⟩`, then apply the quotient-stabilizer equivalence for the pretransitive
-- fiber-translation action.
theorem quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    Function.Bijective (quotientMapVertexGroupRangeToFiber hp e) := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  letI : MulAction (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) :=
    fiberTranslationMulAction hp (p.obj e)
  letI : MulAction.IsPretransitive (p.obj e ⟶ p.obj e) (p.Fiber (p.obj e)) := htrans
  -- Route correction: work on Lean's actual left quotient by first identifying the subgroup with
  -- the stabilizer of `x₀`, then apply the standard orbit-stabilizer bijection.
  exact
    (ofQuotientStabilizer_bijective_of_isPretransitive (G := p.obj e ⟶ p.obj e)
      (S := p.Fiber (p.obj e)) x₀).comp
      (Subgroup.quotientEquivOfEq
        (fiberTranslation_basepoint_stabilizer_eq_mapVertexGroup_range hp e).symm).bijective

noncomputable def quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e)) :
    (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range ≃ p.Fiber (p.obj e) :=
  Equiv.ofBijective
    (quotientMapVertexGroupRangeToFiber hp e)
    (quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive hp e htrans)

@[simp] theorem quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive_apply
    (hp : Functor.IsCovering p) (e : E)
    (htrans : fiberTranslationMulAction.IsPretransitive hp (p.obj e))
    (q : (p.obj e ⟶ p.obj e) ⧸ (Functor.mapVertexGroup p e).range) :
    quotientMapVertexGroupRangeToFiberEquivOfIsPretransitive hp e htrans q =
      quotientMapVertexGroupRangeToFiber hp e q := rfl

/-- The underlying orbit map of the regular `π(B, p.obj e)`-set equivalence is bijective. -/
-- Proof sketch: specialize the quotient-stabilizer description to the trivial subgroup
-- `p(π(E, e)) = ⊥`, and identify `π(B, p.obj e) / ⊥` with `π(B, p.obj e)`.
theorem vertexGroupToFiber_bijectiveOfIsUniversalCovering (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e)) :
    Function.Bijective
      (fun γ : p.obj e ⟶ p.obj e ↦
        fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩) := by
  let x₀ : p.Fiber (p.obj e) := ⟨e, rfl⟩
  let quotientToFiber :
      (p.obj e ⟶ p.obj e) ⧸ (⊥ : Subgroup (p.obj e ⟶ p.obj e)) → p.Fiber (p.obj e) :=
    quotientMapVertexGroupRangeToFiber hp.isCovering e ∘
      Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm
  have hquotientToFiber : Function.Bijective quotientToFiber := by
    -- First identify the quotient by `p(π(E,e))` with the quotient by `⊥`.
    exact
      (quotientMapVertexGroupRangeToFiber_bijectiveOfIsPretransitive hp.isCovering e htrans).comp
        (Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm).bijective
  let inverseVertexToFiber : (p.obj e ⟶ p.obj e) → p.Fiber (p.obj e) :=
    quotientToFiber ∘ QuotientGroup.quotientBot.symm
  have hinverseVertexToFiber : Function.Bijective inverseVertexToFiber := by
    -- Then use the canonical identification `π(B,p.obj e) / ⊥ ≃ π(B,p.obj e)`.
    exact hquotientToFiber.comp QuotientGroup.quotientBot.symm.bijective
  have hinverseVertexToFiber_eq :
      inverseVertexToFiber =
        (fun γ : p.obj e ⟶ p.obj e ↦
          fiberTranslationMap hp.isCovering γ⁻¹ x₀) := by
    funext γ
    -- On representatives, the quotient map uses the inverse-loop action from `x₀`.
    show quotientToFiber (QuotientGroup.quotientBot.symm γ) =
      fiberTranslationMap hp.isCovering γ⁻¹ x₀
    show quotientMapVertexGroupRangeToFiber hp.isCovering e
        ((Subgroup.quotientEquivOfEq hp.mapVertexGroup_range_eq_bot.symm)
          (QuotientGroup.quotientBot.symm γ)) =
      fiberTranslationMap hp.isCovering γ⁻¹ x₀
    rw [QuotientGroup.quotientBot_symm_apply, Subgroup.quotientEquivOfEq_mk]
    exact quotientMapVertexGroupRangeToFiber_mk hp.isCovering e γ
  rw [hinverseVertexToFiber_eq] at hinverseVertexToFiber
  have hdirect_eq :
      (fun γ : p.obj e ⟶ p.obj e ↦
        fiberTranslationMap hp.isCovering γ x₀) =
        (fun γ : p.obj e ⟶ p.obj e ↦
          fiberTranslationMap hp.isCovering γ⁻¹ x₀) ∘ fun γ : p.obj e ⟶ p.obj e ↦ γ⁻¹ := by
    funext γ
    -- Precomposing the inverse-representative orbit map with inversion recovers the textbook map.
    change fiberTranslationMap hp.isCovering γ x₀ =
      fiberTranslationMap hp.isCovering ((γ⁻¹)⁻¹) x₀
    simp
  have hinv : Function.Bijective (fun γ : p.obj e ⟶ p.obj e ↦ CategoryTheory.inv γ) := by
    constructor
    · intro γ₁ γ₂ hγ
      simpa using congrArg (fun δ : p.obj e ⟶ p.obj e ↦ CategoryTheory.inv δ) hγ
    · intro γ
      refine ⟨CategoryTheory.inv γ, ?_⟩
      simp
  -- Compose the inverse-representative bijection with inversion on the vertex group.
  simpa [x₀, hdirect_eq] using
    hinverseVertexToFiber.comp hinv

/-- For a universal covering with pretransitive fiber translation, the fiber over `p.obj e` is
canonically equivalent to the regular `π(B, p.obj e)`-set. -/
noncomputable def vertexGroupToFiberEquivOfIsUniversalCovering
    (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e)) :
    (p.obj e ⟶ p.obj e) ≃ p.Fiber (p.obj e) :=
  Equiv.ofBijective
    (fun γ : p.obj e ⟶ p.obj e ↦ fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩)
    (vertexGroupToFiber_bijectiveOfIsUniversalCovering hp htrans)

@[simp] theorem vertexGroupToFiberEquivOfIsUniversalCovering_apply
    (hp : Functor.IsUniversalCovering p e)
    (htrans : fiberTranslationMulAction.IsPretransitive hp.isCovering (p.obj e))
    (γ : p.obj e ⟶ p.obj e) :
    vertexGroupToFiberEquivOfIsUniversalCovering hp htrans γ =
      fiberTranslationMap hp.isCovering γ ⟨e, rfl⟩ := rfl

end CategoryTheory.Functor.IsCovering
