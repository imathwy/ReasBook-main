import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_2_4_1 (from Chap02) -/
open CategoryTheory Limits

variable (X : TopCat)

/- Definition 2.4.1: the category `T` of based spaces is the under category of the terminal
topological space, so its objects are spaces equipped with chosen basepoints and its morphisms are
continuous maps preserving those basepoints. -/
#check Under (⊤_ TopCat)

/- A based space with underlying space `X` is given primitively by a map from the one-point space
into `X`, equivalently by a chosen basepoint of `X`. -/
#check (Under.mk : (⊤_ TopCat ⟶ X) → Under (⊤_ TopCat))

/- The categorical structure on based spaces is the inherited category structure on this under
category. -/
#check (inferInstance : Category (Under (⊤_ TopCat)))

/-! ### Lemma_2_4_2 (from Chap02) -/
open CategoryTheory Limits

noncomputable section

/-- The chosen basepoint of a based space in `Under (⊤_ TopCat)`. -/
noncomputable def underTopBasepoint (X : Under (⊤_ TopCat)) : X.right :=
  X.hom (TopCat.terminalIsoPUnit.inv PUnit.unit)

/-- A morphism of based spaces sends the chosen basepoint to the chosen basepoint. -/
-- Proof sketch: evaluate the commutative triangle `X.hom ≫ f.right = Y.hom` at the unique point
-- of the terminal space, namely `TopCat.terminalIsoPUnit.inv PUnit.unit`.
theorem fundamentalGroupFunctorMap_basepoint {X Y : Under (⊤_ TopCat)} (f : X ⟶ Y) :
    f.right.hom (underTopBasepoint X) = underTopBasepoint Y := by
  simp only [underTopBasepoint, ← TopCat.comp_app]
  congr 1
  exact congrArg ConcreteCategory.hom (CategoryTheory.Under.w f)

/-- The induced homomorphism on fundamental groups respects identity morphisms. -/
-- Proof sketch: the identity map of a based space induces the identity endomorphism on its
-- vertex group in the fundamental groupoid, and `mapOfEq` uses the trivial basepoint equality.
theorem fundamentalGroupFunctor_map_id (X : Under (⊤_ TopCat)) :
    GrpCat.ofHom
        (FundamentalGroup.mapOfEq (𝟙 X : X ⟶ X).right.hom
          (fundamentalGroupFunctorMap_basepoint (𝟙 X : X ⟶ X))) =
      𝟙 (GrpCat.of (FundamentalGroup X.right (underTopBasepoint X))) := by
  have hhom :
      FundamentalGroup.mapOfEq (𝟙 X : X ⟶ X).right.hom
        (fundamentalGroupFunctorMap_basepoint (𝟙 X : X ⟶ X)) =
      MonoidHom.id (FundamentalGroup X.right (underTopBasepoint X)) := by
    ext γ
    refine Quotient.inductionOn γ ?_
    intro p
    -- On a representative loop, `mapOfEq` for the identity morphism returns the same loop class.
    have hmap :=
      FundamentalGroup.mapOfEq_apply
        (f := (𝟙 X : X ⟶ X).right.hom)
        (h := fundamentalGroupFunctorMap_basepoint (𝟙 X : X ⟶ X))
        (p := p)
    simpa using hmap
  -- Convert the equality of group homomorphisms into equality in `GrpCat`.
  simpa using congrArg GrpCat.ofHom hhom

/-- The induced homomorphism on fundamental groups respects composition. -/
-- Proof sketch: functoriality follows from the corresponding composition law for
-- `FundamentalGroup.mapOfEq`, together with compatibility of the basepoint equalities under
-- composition of based maps.
theorem fundamentalGroupFunctor_map_comp {X Y Z : Under (⊤_ TopCat)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    GrpCat.ofHom
        (FundamentalGroup.mapOfEq (f ≫ g).right.hom
          (fundamentalGroupFunctorMap_basepoint (f ≫ g))) =
      GrpCat.ofHom
          (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)) ≫
        GrpCat.ofHom
          (FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g)) := by
  have hhom :
      FundamentalGroup.mapOfEq (f ≫ g).right.hom
        (fundamentalGroupFunctorMap_basepoint (f ≫ g)) =
      (FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g)).comp
        (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)) := by
    ext γ
    refine Quotient.inductionOn γ ?_
    intro p
    let pf : Path (underTopBasepoint Y) (underTopBasepoint Y) :=
      (p.map f.right.hom.continuous).cast
        (fundamentalGroupFunctorMap_basepoint f).symm
        (fundamentalGroupFunctorMap_basepoint f).symm
    -- Rewrite both sides on the representative loop `p` using the explicit `mapOfEq_apply`
    -- formula, so the statement reduces to the standard path-level composition.
    have hfg :=
      FundamentalGroup.mapOfEq_apply
        (f := (f ≫ g).right.hom)
        (h := fundamentalGroupFunctorMap_basepoint (f ≫ g))
        (p := p)
    have hf :=
      FundamentalGroup.mapOfEq_apply
        (f := f.right.hom)
        (h := fundamentalGroupFunctorMap_basepoint f)
        (p := p)
    have hg :=
      FundamentalGroup.mapOfEq_apply
        (f := g.right.hom)
        (h := fundamentalGroupFunctorMap_basepoint g)
        (p := pf)
    change
      FundamentalGroup.mapOfEq (f ≫ g).right.hom (fundamentalGroupFunctorMap_basepoint (f ≫ g))
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) =
        ((FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g)).comp
          (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)))
            (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p))
    rw [hfg]
    simp only [MonoidHom.comp_apply]
    rw [hf, hg]
    -- After the explicit rewrites, the two quotient classes coincide definitionally.
    congr 1
  -- Convert the equality of underlying homomorphisms into equality in `GrpCat`.
  simpa using congrArg GrpCat.ofHom hhom

/-- Lemma 2.4.2: the fundamental group defines a functor from based spaces to groups. -/
noncomputable def fundamentalGroupFunctor : Under (⊤_ TopCat) ⥤ GrpCat where
  obj X := GrpCat.of (FundamentalGroup X.right (underTopBasepoint X))
  map f :=
    GrpCat.ofHom (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f))
  map_id := fundamentalGroupFunctor_map_id
  map_comp := fundamentalGroupFunctor_map_comp

/-- The morphism part of `fundamentalGroupFunctor` is the induced map on fundamental groups. -/
-- Proof sketch: unfold `fundamentalGroupFunctor`; its `map` field was defined to be
-- `GrpCat.ofHom (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f))`.
theorem fundamentalGroupFunctor_map_eq {X Y : Under (⊤_ TopCat)} (f : X ⟶ Y) :
    fundamentalGroupFunctor.map f =
      GrpCat.ofHom
        (FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f)) :=
  rfl

/-! ### Definition_2_4_3 (from Chap02) -/
universe u v

/- Definition 2.4.3: given a homotopy relation on a category `C`, the homotopy category `hC`
is realized by the quotient category `CategoryTheory.Quotient r`, which has the same objects as
`C` and morphisms given by homotopy classes of maps. -/
recall CategoryTheory.Quotient (C : Type u) [CategoryTheory.Category.{v} C] (r : HomRel C) :
  Type u

/-! ### Lemma_2_4_4 (from Chap02) -/
noncomputable section

open CategoryTheory ContinuousMap CategoryTheory.Quotient

/-- Based homotopy relation on morphisms of based spaces, i.e. homotopy relative to the chosen
basepoint. -/
def basedHomotopyRel : HomRel (Under (⊤_ TopCat)) := fun X _ f g ↦
  Nonempty (HomotopyRel f.right.hom g.right.hom ({underTopBasepoint X} : Set X.right))

/-- Helper for Lemma 2.4.4: a homotopy relative to a singleton moves that point along the constant
path after transporting the endpoints to a common basepoint. -/
theorem homotopyRel_evalAt_singleton_cast_eq_refl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {x : X} {y : Y}
    (H : f.HomotopyRel g ({x} : Set X)) (hf : f x = y) (hg : g x = y) :
    (H.evalAt x).cast hf.symm hg.symm = Path.refl y := by
  -- The relative condition says the entire track of `x` stays at the initial endpoint.
  have hx : x ∈ ({x} : Set X) := by
    simp
  ext t
  simp [ContinuousMap.HomotopyRel.eq_fst, hx, hf]

/-- Helper for Lemma 2.4.4: if a homotopy is relative to a singleton, then the induced maps on
fundamental groups agree after identifying both endpoints with a common basepoint. -/
theorem fundamentalGroup_mapOfEq_eq_of_homotopyRel_singleton
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {x : X} {y : Y}
    (H : f.HomotopyRel g ({x} : Set X)) (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- First identify the track of the fixed point with the constant path at the chosen basepoint.
  have htrack : (H.evalAt x).cast hf.symm hg.symm = Path.refl y :=
    homotopyRel_evalAt_singleton_cast_eq_refl H hf hg
  let eP : FundamentalGroupoid.mk (f x) ≅ FundamentalGroupoid.mk (g x) :=
    (Groupoid.isoEquivHom _ _).symm ⟦H.evalAt x⟧
  let eHf : FundamentalGroupoid.mk (f x) ≅ FundamentalGroupoid.mk y :=
    eqToIso (congr_arg FundamentalGroupoid.mk hf)
  let eHg : FundamentalGroupoid.mk (g x) ≅ FundamentalGroupoid.mk y :=
    eqToIso (congr_arg FundamentalGroupoid.mk hg)
  -- The casted track is trivial, so composing the track with the endpoint identifications gives
  -- exactly the equality isomorphism from `f x` to `y`.
  have htrans_hom : eP.hom ≫ eHg.hom = eHf.hom := by
    have hcast_hom :
        eqToHom (congr_arg FundamentalGroupoid.mk hf.symm) ≫ eP.hom ≫ eHg.hom = 𝟙 _ := by
      simpa [eP, eHg, htrack] using
        (FundamentalGroupoid.conj_eqToHom (p := H.evalAt x) hf.symm hg.symm)
    simpa [eHf, Category.assoc] using
      congrArg (fun k ↦ eHf.hom ≫ k) hcast_hom
  have htrans_iso : eP ≪≫ eHg = eHf := by
    ext
    exact htrans_hom
  ext α
  -- Proposition 1.4.4 gives the homotopy-commutation relation before the endpoint transport.
  have hcomm : eP.conj (FundamentalGroup.map f x α) = FundamentalGroup.map g x α := by
    simpa [eP] using
      congrArg (fun k ↦ k α) (fundamental_group_map_homotopy_commutes f g H.toHomotopy x)
  -- Transporting that relation to the common basepoint turns it into equality of `mapOfEq`.
  have hconj :
      eHg.conj (eP.conj (FundamentalGroup.map f x α)) =
        eHf.conj (FundamentalGroup.map f x α) := by
    simpa [htrans_iso] using
      (eP.trans_conj eHg (FundamentalGroup.map f x α)).symm
  change eHf.conj (FundamentalGroup.map f x α) = eHg.conj (FundamentalGroup.map g x α)
  rw [← hconj, hcomm]

/-- Helper for Lemma 2.4.4: a based homotopy induces the same basepoint-preserving map on
fundamental groups. -/
theorem based_homotopy_mapOfEq_eq
    {X Y : Under (⊤_ TopCat)} {f g : X ⟶ Y} (H : basedHomotopyRel f g) :
    FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f) =
      FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g) := by
  -- Unpack the based homotopy and specialize the singleton-relative statement at the chosen
  -- basepoint.
  obtain ⟨Hfg⟩ := H
  exact fundamentalGroup_mapOfEq_eq_of_homotopyRel_singleton Hfg
    (fundamentalGroupFunctorMap_basepoint f) (fundamentalGroupFunctorMap_basepoint g)

/-- The fundamental-group functor sends based-homotopic maps to the same homomorphism. -/
-- Proof sketch: a based homotopy is fixed on the chosen basepoint, so the basepoint track in
-- Proposition 1.4.4 is the constant path. The resulting basepoint-change automorphism is the
-- identity, and the induced maps on fundamental groups therefore agree.
theorem fundamentalGroupFunctor_map_eq_of_based_homotopy
    {X Y : Under (⊤_ TopCat)} {f g : X ⟶ Y} (H : basedHomotopyRel f g) :
    fundamentalGroupFunctor.map f = fundamentalGroupFunctor.map g := by
  -- Rewrite the functorial morphisms into their `mapOfEq` descriptions and use the based-homotopy
  -- equality proved above.
  simpa [fundamentalGroupFunctor_map_eq] using
    congrArg GrpCat.ofHom (based_homotopy_mapOfEq_eq H)

/-- Lemma 2.4.4: the fundamental-group functor on based spaces is homotopy invariant and therefore
factors through the homotopy category of based spaces, realized as the quotient by based
homotopy. -/
def fundamentalGroupFunctorDesc : CategoryTheory.Quotient basedHomotopyRel ⥤ GrpCat :=
  lift basedHomotopyRel fundamentalGroupFunctor
    (fun _ _ _ _ h ↦ fundamentalGroupFunctor_map_eq_of_based_homotopy h)

/-! ### Definition_2_4_5 (from Chap02) -/
universe u v

open CategoryTheory

namespace CategoryTheory.HomRel

variable {C : Type u} [Category.{v} C] (r : HomRel C)

/-- Definition 2.4.5: a morphism is a homotopy equivalence if it admits a two-sided inverse up to
the homotopy relation `r`. This always becomes an isomorphism after passing to the quotient
category `CategoryTheory.Quotient r`, and the converse holds when `r` is a congruence. -/
def IsHomotopyEquivalence {X Y : C} (f : X ⟶ Y) : Prop :=
  ∃ g : Y ⟶ X, r (g ≫ f) (𝟙 Y) ∧ r (f ≫ g) (𝟙 X)

namespace IsHomotopyEquivalence

-- Proof sketch: if `g` is a homotopy inverse for `f`, then `Quotient.sound` turns the relations
-- `g ≫ f ∼ 𝟙` and `f ≫ g ∼ 𝟙` into equalities in `CategoryTheory.Quotient r`, so the images of
-- `f` and `g` are inverse morphisms there.
/-- A homotopy equivalence becomes an isomorphism in the quotient category. -/
theorem isIso_map {X Y : C} {f : X ⟶ Y} (hf : IsHomotopyEquivalence r f) :
    IsIso ((Quotient.functor r).map f) := by
  rcases hf with ⟨g, hgf, hfg⟩
  refine IsIso.mk' ⟨(Quotient.functor r).map g, ?_, ?_⟩
  · calc
      (Quotient.functor r).map g ≫ (Quotient.functor r).map f
          = (Quotient.functor r).map (g ≫ f) := by simp
      _ = (Quotient.functor r).map (𝟙 Y) := by
        simpa using CategoryTheory.Quotient.sound r hgf
      _ = 𝟙 _ := by simp
  · calc
      (Quotient.functor r).map f ≫ (Quotient.functor r).map g
          = (Quotient.functor r).map (f ≫ g) := by simp
      _ = (Quotient.functor r).map (𝟙 X) := by
        simpa using CategoryTheory.Quotient.sound r hfg
      _ = 𝟙 _ := by simp

/-- If `r` is a congruence, any morphism whose image in the quotient is invertible is already a
homotopy equivalence for `r`. -/
theorem of_isIso_map [Congruence r] {X Y : C} {f : X ⟶ Y}
    (hf : IsIso ((Quotient.functor r).map f)) :
    IsHomotopyEquivalence r f := by
  obtain ⟨g, hg : (Quotient.functor r).map g = inv ((Quotient.functor r).map f)⟩ :=
    (Quotient.functor r).map_surjective (inv ((Quotient.functor r).map f))
  refine ⟨g, ?_, ?_⟩
  · rw [← Quotient.functor_map_eq_iff r (g ≫ f) (𝟙 Y)]
    calc
      (Quotient.functor r).map (g ≫ f)
          = (Quotient.functor r).map g ≫ (Quotient.functor r).map f := by simp
      _ = inv ((Quotient.functor r).map f) ≫ (Quotient.functor r).map f := by simp [hg]
      _ = 𝟙 _ := by simp
      _ = (Quotient.functor r).map (𝟙 Y) := by simp
  · rw [← Quotient.functor_map_eq_iff r (f ≫ g) (𝟙 X)]
    calc
      (Quotient.functor r).map (f ≫ g)
          = (Quotient.functor r).map f ≫ (Quotient.functor r).map g := by simp
      _ = (Quotient.functor r).map f ≫ inv ((Quotient.functor r).map f) := by simp [hg]
      _ = 𝟙 _ := by simp
      _ = (Quotient.functor r).map (𝟙 X) := by simp

/-- For a congruence relation, homotopy equivalences are exactly the morphisms that become
isomorphisms in the quotient category. -/
theorem iff_isIso_map [Congruence r] {X Y : C} {f : X ⟶ Y} :
    IsHomotopyEquivalence r f ↔ IsIso ((Quotient.functor r).map f) :=
  ⟨isIso_map r, of_isIso_map r⟩

end IsHomotopyEquivalence

end CategoryTheory.HomRel

/-! ### Proposition_2_4_6 (from Chap02) -/
universe u v

open CategoryTheory
open scoped ContinuousMap

noncomputable section

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]

/-- Proposition 2.4.6: if `e : X ≃ₕ Y` is an unbased homotopy equivalence, then for every
basepoint `x : X` the induced map `e_* : π₁(X, x) → π₁(Y, e x)` is an isomorphism of groups. -/
-- Proof sketch: the equivalence of fundamental groupoids induced by `e` is fully faithful, so
-- on the vertex group at `x` it induces the corresponding multiplicative equivalence on
-- endomorphism groups.
def fundamentalGroupMulEquivOfHomotopyEquiv
    (e : X ≃ₕ Y)
    (x : X) :
    FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  let F := (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).functor
  let hF : F.FullyFaithful := .ofFullyFaithful F
  hF.mulEquivEnd (FundamentalGroupoid.mk x)

/-- The underlying homomorphism of `fundamentalGroupMulEquivOfHomotopyEquiv` is the usual map on
fundamental groups induced by the forward map of the homotopy equivalence. -/
@[simp] theorem fundamentalGroupMulEquivOfHomotopyEquiv_toMonoidHom
    (e : X ≃ₕ Y)
    (x : X) :
    (fundamentalGroupMulEquivOfHomotopyEquiv e x).toMonoidHom = FundamentalGroup.map e.toFun x :=
  rfl

/-! ### Corollary_2_4_7 (from Chap02) -/
universe u

variable {X : Type u} [TopologicalSpace X] [ContractibleSpace X]

/-- Corollary 2.4.7: a contractible space has trivial fundamental group at every basepoint. -/
-- Proof sketch: use the homotopy equivalence from a contractible space to `Unit`, transport the
-- fundamental group along Proposition 2.4.6, and then use that the point has trivial
-- fundamental group.
theorem fundamentalGroup_subsingleton_of_contractible (x : X) :
    Subsingleton (FundamentalGroup X x) := by
  -- Use the canonical homotopy equivalence from a contractible space to the point.
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  -- Transport the fundamental group at `x` across the homotopy equivalence.
  let h := fundamentalGroupMulEquivOfHomotopyEquiv e x
  -- The point is simply connected, so its fundamental group is trivial.
  let _ : Subsingleton (FundamentalGroup Unit (e x)) := by
    let _ : SimplyConnectedSpace Unit := inferInstance
    change Subsingleton (Path.Homotopic.Quotient (e x) (e x))
    infer_instance
  -- Pull the subsingleton structure back along the induced equivalence.
  exact h.injective.subsingleton
