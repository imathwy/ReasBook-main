import Mathlib.CategoryTheory.Action.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Groupoid.VertexGroup
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Construction_3_6_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_3_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_4_7
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Definition_3_4_10
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Lemma_3_4_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Proposition_3_3_6
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Remark_3_3_13
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap03.Theorem_3_5_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory
open CategoryTheory.Groupoid.CategoryTheory
open QuotientGroup
open CategoryTheory.Functor.IsCovering

variable {B : Type u} [Groupoid.{v} B]

/-- Groupoid functors over `B`, with varying total groupoid and fixed codomain `B`. This is a
universe-stable owner for the source-facing over-category of groupoid functors to `B`; unlike the
bundled over-category `Over (Grpd.of B)`, it allows the total groupoid to live in
`Type (max u v)` while the base groupoid stays in `Type u`. -/
structure GroupoidFunctorOver (B : Type u) [Groupoid.{v} B] : Type (max u v + 1) where
  left : Type (max u v)
  groupoid_left : Groupoid.{v} left
  hom : left ⥤ B

attribute [instance] GroupoidFunctorOver.groupoid_left

namespace GroupoidFunctorOver

/-- Morphisms over `B` are functors between total groupoids commuting with the structure maps to
`B`. -/
@[ext] structure Hom (X Y : GroupoidFunctorOver B) where
  left : X.left ⥤ Y.left
  comm : left ⋙ Y.hom = X.hom

/-- Constructor for morphisms over `B`. -/
abbrev homMk {X Y : GroupoidFunctorOver B} (F : X.left ⥤ Y.left)
    (hF : F ⋙ Y.hom = X.hom) : Hom X Y :=
  ⟨F, hF⟩

instance : Quiver (GroupoidFunctorOver B) where
  Hom X Y := Hom X Y

instance : Category (GroupoidFunctorOver B) where
  id X := ⟨𝟭 X.left, rfl⟩
  comp {X Y Z} f g := ⟨f.left ⋙ g.left, by
    calc
      (f.left ⋙ g.left) ⋙ Z.hom = f.left ⋙ (g.left ⋙ Z.hom) := rfl
      _ = f.left ⋙ Y.hom := by rw [g.comm]
      _ = X.hom := f.comm⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

end GroupoidFunctorOver

/-- The category `Cov(B)` of connected covering functors over the groupoid `B`, realized as the
full subcategory of groupoid functors over `B` on covering functors with connected total
groupoid. -/
abbrev ConnectedCovering (B : Type u) [Groupoid.{v} B] : Type (max u v + 1) :=
  ObjectProperty.FullSubcategory
    (fun X : GroupoidFunctorOver B ↦ Functor.IsCovering X.hom ∧ IsConnected X.left)

namespace ConnectedCovering

/-- The fiber of a connected covering over an object `b : B`. -/
abbrev Fiber (X : ConnectedCovering B) (b : B) :=
  Functor.Fiber X.obj.hom b

/-- The underlying functor of an object of `Cov(B)` is a covering functor over `B`. -/
instance instIsCovering (X : ConnectedCovering B) :
    Functor.IsCovering X.obj.hom :=
  X.2.1

/-- The total groupoid of an object of `Cov(B)` is connected. -/
instance instIsConnected (X : ConnectedCovering B) :
    IsConnected X.obj.left :=
  X.2.2

/-- The underlying functor of an object of `Cov(B)` is a covering functor over `B`. -/
theorem isCovering (X : ConnectedCovering B) :
    Functor.IsCovering X.obj.hom :=
  inferInstance

/-- The total groupoid of an object of `Cov(B)` is connected. -/
theorem isConnected (X : ConnectedCovering B) :
    IsConnected X.obj.left :=
  inferInstance

end ConnectedCovering

open ConnectedCovering

variable (b : B)

variable (S : Type v) [MulAction (End b) S]

/-- The fiber over `x` associated to a `π(B,b)`-set is the orbit quotient of pairs
`(b ⟶ x, s)` for the diagonal action of `π(B,b)`. -/
abbrev associatedActionObj (x : B) : Type v :=
  MulAction.orbitRel.Quotient (End b) ((b ⟶ x) × S)

/-- Transport in the associated `B`-action is induced by postcomposition on the arrow component. -/
noncomputable def associatedActionMap {x y : B} (f : x ⟶ y) :
    associatedActionObj b S x → associatedActionObj b S y :=
  Quotient.map' (fun p : (b ⟶ x) × S ↦ (p.1 ≫ f, p.2)) <| by
    intro p q hp
    rw [MulAction.orbitRel_apply] at hp ⊢
    rcases hp with ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    ext
    · simp [CategoryTheory.Groupoid.homMulAction_smul, Category.assoc]
    · rfl

/-- The `B`-action associated to a `π(B,b)`-set by the standard twisted-product construction. -/
noncomputable def associatedAction : B ⥤ Type v where
  obj := associatedActionObj b S
  map := associatedActionMap b S
  map_id x := by
    funext q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1 ≫ 𝟙 x, p.2) = Quotient.mk'' p
    simp
  map_comp f g := by
    funext q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1 ≫ (f ≫ g), p.2) = Quotient.mk'' ((p.1 ≫ f) ≫ g, p.2)
    simp [Category.assoc]

/-- A `π(B,b)`-equivariant map induces a natural transformation of the associated `B`-actions. -/
noncomputable def associatedActionHom {S T : Type v} [MulAction (End b) S] [MulAction (End b) T]
    (φ : S →[End b] T) :
    associatedAction b S ⟶ associatedAction b T where
  app x := Quotient.map' (fun p : (b ⟶ x) × S ↦ (p.1, φ p.2)) <| by
    intro p q hp
    rw [MulAction.orbitRel_apply] at hp ⊢
    rcases hp with ⟨g, rfl⟩
    refine ⟨g, ?_⟩
    ext
    · rfl
    · simp [map_smul]
  naturality {x} {y} f := by
    funext q
    refine Quotient.inductionOn' q ?_
    intro p
    rfl

variable {S}

/-- Helper for Theorem 3.6.1: evaluating the base fiber class `[γ, s]` by the original
`π(B,b)`-action produces a well-defined point of `S`. -/
private abbrev associatedAction_base_eval
    (b : B) (S : Type v) [MulAction (End b) S] (p : (b ⟶ b) × S) : S :=
  (show End b from p.1) • p.2

/-- Helper for Theorem 3.6.1: evaluating the base fiber class `[γ, s]` by the original
`π(B,b)`-action produces a well-defined point of `S`. -/
private theorem associatedAction_base_map_wellDefined
    (b : B) (S : Type v) [MulAction (End b) S] :
    ∀ p q : (b ⟶ b) × S,
      MulAction.orbitRel (End b) ((b ⟶ b) × S) p q →
        associatedAction_base_eval b S p = associatedAction_base_eval b S q := by
  intro p q hp
  rw [MulAction.orbitRel_apply] at hp
  rcases hp with ⟨g, rfl⟩
  -- The diagonal orbit relation exactly preserves the evaluated point `γ • s`.
  simp [associatedAction_base_eval, CategoryTheory.Groupoid.homMulAction_smul,
    smul_smul, CategoryTheory.End.mul_def]

/-- Helper for Theorem 3.6.1: the base fiber of the associated action maps to the original
`π(B,b)`-set by evaluation. -/
private noncomputable def associatedAction_base_map
    (b : B) (S : Type v) [MulAction (End b) S] :
    associatedActionObj b S b → S :=
  Quotient.lift (associatedAction_base_eval b S)
    (associatedAction_base_map_wellDefined b S)

/-- Helper for Theorem 3.6.1: evaluating the class of a representative `(γ, s)` in the base
fiber gives `γ • s`. -/
private theorem associatedAction_base_map_mk
    (b : B) (S : Type v) [MulAction (End b) S] (p : (b ⟶ b) × S) :
    associatedAction_base_map b S (Quotient.mk'' p) = associatedAction_base_eval b S p :=
  rfl

/-- Helper for Theorem 3.6.1: the evaluation map identifies the base fiber of the associated
action with the original `π(B,b)`-set. -/
private theorem associatedAction_base_map_bijective
    (b : B) (S : Type v) [MulAction (End b) S] :
    Function.Bijective (associatedAction_base_map b S) := by
  constructor
  · intro q₁ q₂ hq
    -- Each quotient class is represented by an identity-arrow class over its evaluated point.
    have hrepr :
        ∀ q : associatedActionObj b S b,
          Quotient.mk'' (𝟙 b, associatedAction_base_map b S q) = q := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro p
      change Quotient.mk'' (𝟙 b, associatedAction_base_eval b S p) = Quotient.mk'' p
      apply Quotient.sound
      change MulAction.orbitRel (End b) ((b ⟶ b) × S) (𝟙 b, associatedAction_base_eval b S p) p
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
      refine ⟨p.1⁻¹, ?_⟩
      ext
      · change ((p.1⁻¹ : End b) • (𝟙 b : b ⟶ b)) = p.1
        rw [CategoryTheory.Groupoid.homMulAction_smul]
        rw [Category.comp_id]
        have hinv : inv p.1⁻¹ = (p.1⁻¹ : End b)⁻¹ := by
          symm
          exact CategoryTheory.Groupoid.inv_eq_inv _
        have hloop : (p.1⁻¹ : End b)⁻¹ = p.1 := inv_inv p.1
        exact hinv.trans hloop
      · simp
    calc
      q₁ = Quotient.mk'' (𝟙 b, associatedAction_base_map b S q₁) := (hrepr q₁).symm
      _ = Quotient.mk'' (𝟙 b, associatedAction_base_map b S q₂) := by rw [hq]
      _ = q₂ := hrepr q₂
  · intro s
    -- The identity arrow gives a canonical class mapping to the chosen point.
    refine ⟨Quotient.mk'' (𝟙 b, s), ?_⟩
    change (show End b from 𝟙 b) • s = s
    simpa using (one_smul (End b) s)

/-- Helper for Theorem 3.6.1: the base fiber of the associated action is canonically equivalent
to the original `π(B,b)`-set. -/
private noncomputable def associatedAction_base_equiv
    (b : B) (S : Type v) [MulAction (End b) S] :
    associatedActionObj b S b ≃ S :=
  Equiv.ofBijective (associatedAction_base_map b S)
    (associatedAction_base_map_bijective b S)

/-- Helper for Theorem 3.6.1: the base-fiber equivalence intertwines the direct `End b`-action on
the associated action with the original action on `S`. -/
private theorem associatedAction_base_equiv_smul
    (b : B) (S : Type v) [MulAction (End b) S] (g : End b)
    (q : associatedActionObj b S b) :
    associatedAction_base_equiv b S ((associatedAction b S).map g q) =
      g • associatedAction_base_equiv b S q := by
  -- Compare both sides on representatives of the quotient.
  refine Quotient.inductionOn' q ?_
  intro p
  simpa [associatedAction_base_equiv, associatedAction_base_map,
    CategoryTheory.End.mul_def, Category.assoc] using
    (smul_smul g p.1 p.2).symm

/-- The associated `B`-action of a transitive `π(B,b)`-set is transitive when `B` is
connected. -/
-- Proof sketch: use connectedness of `B` to move any point of a fiber to the base object `b`,
-- reduce there to the original `π(B,b)`-action, and transport both a chosen point and the orbit
-- relation back to the target fiber.
theorem associatedAction_isTransitive
    (b : B) (S : Type v) [MulAction (End b) S] [IsConnected B]
    (hS : MulAction.IsTransitive (End b) S) :
    Functor.IsTransitive (associatedAction b S) := by
  -- Reduce global transitivity to the base object, then transport the orbit condition through the
  -- canonical base-fiber equivalence.
  refine (Functor.isTransitive_iff_at_object (associatedAction b S) b).2 ?_
  refine (Functor.vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive
    (associatedAction b S) b).2 ?_
  let e : associatedActionObj b S b ≃ S := associatedAction_base_equiv b S
  letI : MulAction (End b) (associatedActionObj b S b) :=
    Functor.vertexGroupMulAction (associatedAction b S) b
  rcases hS with ⟨hs, hpre⟩
  refine ⟨hs.map e.symm, ?_⟩
  obtain ⟨s₀⟩ := hs
  refine (MulAction.isPretransitive_iff_base (e.symm s₀)).2 ?_
  intro q
  rcases (MulAction.isPretransitive_iff_base s₀).1 hpre (e q) with ⟨g, hg⟩
  refine ⟨g, e.injective ?_⟩
  calc
    e (g • e.symm s₀) = g • e (e.symm s₀) := by
      simpa [e] using associatedAction_base_equiv_smul b S g (e.symm s₀)
    _ = e q := by simpa using hg

/-- The associated action of an orbit-category object is transitive over a connected base
groupoid. -/
-- Proof sketch: combine the general transitivity theorem for associated actions with the
-- transitivity of the orbit `π(B,b) / H`.
theorem orbitCategoryAssociatedAction_isTransitive [IsConnected B]
    (H : O(End b)) :
    Functor.IsTransitive (associatedAction b (End b ⧸ H)) := by
  -- The orbit object `π(B,b) / H` is already a transitive `π(B,b)`-set.
  exact associatedAction_isTransitive b (End b ⧸ H) inferInstance

/-- Passing to categories of elements turns a `B`-action into a groupoid functor over `B`. -/
abbrev elementsFunctorOver (T : B ⥤ Type v) : GroupoidFunctorOver B :=
  { left := T.Elements
    groupoid_left := inferInstance
    hom := CategoryOfElements.π T }

/-- A natural transformation induces the corresponding morphism between the associated objects in
`GroupoidFunctorOver B`. -/
abbrev elementsFunctorOverMap {T U : B ⥤ Type v} (α : T ⟶ U) :
    elementsFunctorOver T ⟶ elementsFunctorOver U :=
  GroupoidFunctorOver.homMk (CategoryOfElements.map α) (CategoryOfElements.map_π α)

/-- Helper for Theorem 3.6.1: if two lifts out of a fixed element have the same image in the base
star, then they define the same object of the source star. -/
private theorem underMk_eq_of_post_eq
    {T : B ⥤ Type v} {e : T.Elements} {y z : T.Elements}
    (f : e ⟶ y) (g : e ⟶ z)
    (h : (Under.mk f.1 : Under e.1) = Under.mk g.1) :
    (Under.mk f : Under e) = Under.mk g := by
  have hy : y.1 = z.1 := congrArg Comma.right h
  have hval' : f.1 ≫ eqToHom hy = g.1 := by
    simpa [Under.eqToHom_right] using Under.w (eqToHom h)
  have hval : f.1 = g.1 ≫ eqToHom hy.symm := by
    exact (CategoryTheory.comp_eqToHom_iff hy f.1 g.1).mp hval'
  have hzy : z = y := by
    have hz :
        T.map (eqToHom hy.symm) z.2 =
          T.map (eqToHom hy.symm) (T.map g.1 e.2) := by
      exact congrArg (T.map (eqToHom hy.symm)) g.2.symm
    refine Functor.Elements.ext z y hy.symm ?_
    calc
      T.map (eqToHom hy.symm) z.2 =
          T.map (eqToHom hy.symm) (T.map g.1 e.2) := hz
      _ = T.map (g.1 ≫ eqToHom hy.symm) e.2 := by
          simp [FunctorToTypes.map_comp_apply]
      _ = y.2 := by
          simpa [hval] using f.2
  -- After transporting the codomain element object, the two lifts have the same underlying arrow.
  cases hzy
  apply congrArg Under.mk
  apply CategoryOfElements.ext T
  simpa using hval

/-- If every vertex-group action of `T` is transitive, then the projection from its category of
elements to `B` is a covering functor. -/
-- Proof sketch: transitivity makes every fiber nonempty, so the projection is surjective on
-- objects. Morphisms in the category of elements are determined uniquely by their image in `B`,
-- which yields the required bijection on stars.
theorem transitiveAction_elements_isCovering
    (T : B ⥤ Type v) (hT : Functor.IsTransitive T) :
    Functor.IsCovering (CategoryOfElements.π T) := by
  classical
  refine ⟨?_, ?_⟩
  · intro x
    -- Transitivity at `x` gives a point of the fiber, hence an object of the category of elements
    -- mapping to `x`.
    obtain ⟨t⟩ := (hT x).nonempty
    exact ⟨⟨x, t⟩, rfl⟩
  · intro e
    let starMap : Under e → Under e.1 := (Under.post (CategoryOfElements.π T)).obj
    let liftUnder : Under e.1 → Under e := fun u ↦
      Under.mk <|
        CategoryOfElements.homMk e ⟨u.right, T.map u.hom e.2⟩ u.hom rfl
    have hright : Function.RightInverse liftUnder starMap := by
      intro u
      obtain ⟨y, f, rfl⟩ := Under.mk_surjective u
      -- The chosen lift of a base arrow lands at the canonical element `T.map f e.2`.
      simp [starMap, liftUnder]
    refine ⟨?_, hright.surjective⟩
    intro u v huv
    obtain ⟨y, f, rfl⟩ := Under.mk_surjective u
    obtain ⟨z, g, rfl⟩ := Under.mk_surjective v
    -- The element component of a lift is forced by the base arrow, so the source-star objects
    -- coincide once their images in `Under e.1` agree.
    exact underMk_eq_of_post_eq f g (by simpa [starMap] using huv)

/-- For a connected base groupoid, the category of elements of a transitive `B`-action is
connected. -/
-- Proof sketch: choose an arrow in `B` joining the underlying base objects and then use
-- transitivity in the target fiber to connect the transported element to the chosen target point.
theorem transitiveAction_elements_isConnected
    [IsConnected B] (T : B ⥤ Type v) (hT : Functor.IsTransitive T) :
    IsConnected T.Elements := by
  classical
  let b₀ : B := Classical.choice (inferInstance : Nonempty B)
  obtain ⟨t₀⟩ := (hT b₀).nonempty
  letI : Nonempty T.Elements := ⟨⟨b₀, t₀⟩⟩
  refine IsConnected.of_constant_of_preserves_morphisms ?_
  intro α F hF x y
  let g : x.1 ⟶ y.1 :=
    Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid x.1 y.1)
  -- First move `x.2` to the target fiber, then correct the endpoint by a loop at `y.1`.
  rcases (MulAction.isPretransitive_iff_base (T.map g x.2)).1 (hT y.1).2 y.2 with ⟨γ, hγ⟩
  let f : x ⟶ y :=
    CategoryOfElements.homMk x y (g ≫ γ⁻¹) <| by
      calc
        T.map (g ≫ γ⁻¹) x.2 = T.map γ⁻¹ (T.map g x.2) := by
          simp [FunctorToTypes.map_comp_apply]
        _ = γ • T.map g x.2 := by
          simp [Functor.vertexGroupAction_smul_eq_map_inv]
        _ = y.2 := hγ
  exact hF f

/-- The orbit category functor sending `H ≤ π(B,b)` to the transitive `B`-action associated to the
orbit `π(B,b) / H`. -/
noncomputable def orbitCategoryToTransitiveGroupoidAction [IsConnected B] :
    O(End b) ⥤
      CategoryTheory.ObjectProperty.FullSubcategory
        (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v)) where
  obj H :=
    ⟨associatedAction b (End b ⧸ H),
      orbitCategoryAssociatedAction_isTransitive b H⟩
  map {H K : O(End b)} φ := ObjectProperty.homMk <|
    (associatedActionHom b φ : associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K))
  map_id H := by
    apply ObjectProperty.hom_ext
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    rfl
  map_comp φ ψ := by
    apply ObjectProperty.hom_ext
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    rfl

/-- The category-of-elements bridge identifying transitive `B`-actions with connected covering
functors over `B`. -/
noncomputable def transitiveGroupoidActionToConnectedCovering [IsConnected B] :
    ObjectProperty.FullSubcategory
      (Functor.IsTransitive : ObjectProperty (B ⥤ Type v)) ⥤
        ConnectedCovering B where
  obj T :=
    ⟨elementsFunctorOver T.1,
      ⟨transitiveAction_elements_isCovering T.1 T.2,
        transitiveAction_elements_isConnected T.1 T.2⟩⟩
  map {T U} α := ObjectProperty.homMk <| elementsFunctorOverMap α.1
  map_id T := by
    apply ObjectProperty.hom_ext
    rfl
  map_comp α β := by
    apply ObjectProperty.hom_ext
    rfl

/-- The source-facing functor `E(-) : O(π(B,b)) ⥤ Cov(B)` sending an orbit `π(B,b) / H` to its
associated connected covering over `B`. -/
noncomputable abbrev orbitCategoryToConnectedCovering [IsConnected B] :
    O(End b) ⥤ ConnectedCovering B :=
  orbitCategoryToTransitiveGroupoidAction b ⋙ transitiveGroupoidActionToConnectedCovering

/-- The category of elements of the associated action of `π(B,b) / H` projects to `B` as a
covering functor. -/
-- Proof sketch: the projection from the category of elements is surjective on objects because `B`
-- is connected and the orbit action is transitive, while morphisms in the element category are
-- uniquely determined by their image in `B`, giving the required star bijections.
theorem orbitCategoryAssociatedAction_elements_isCovering
    [IsConnected B] (H : O(End b)) :
    Functor.IsCovering (CategoryOfElements.π (associatedAction b (End b ⧸ H))) := by
  simpa using transitiveAction_elements_isCovering
    (associatedAction b (End b ⧸ H))
    (orbitCategoryAssociatedAction_isTransitive b H)

/-- The total groupoid of the associated action of `π(B,b) / H` is connected. -/
-- Proof sketch: transitivity of `associatedAction b (End b ⧸ H)`
-- identifies any two
-- objects in the category of elements by a zigzag over a morphism of `B`; since `B` is a
-- groupoid, these zigzags upgrade to actual isomorphisms, yielding connectedness.
theorem orbitCategoryAssociatedAction_elements_isConnected
    [IsConnected B] (H : O(End b)) :
    IsConnected (Functor.Elements (associatedAction b (End b ⧸ H))) := by
  simpa using transitiveAction_elements_isConnected
    (associatedAction b (End b ⧸ H))
    (orbitCategoryAssociatedAction_isTransitive b H)

/-- Helper for Theorem 3.6.1: a natural transformation between associated actions is already
determined by its component on the base fiber. -/
private noncomputable def associated_action_to_orbit_morphism
    {H K : O(End b)}
    (η : associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K)) :
    H ⟶ K where
  toFun x :=
    associatedAction_base_equiv b (End b ⧸ K)
      (η.app b ((associatedAction_base_equiv b (End b ⧸ H)).symm x))
  map_smul' g x := by
    let eH := associatedAction_base_equiv b (End b ⧸ H)
    let eK := associatedAction_base_equiv b (End b ⧸ K)
    have hsource :
        eH.symm (g • x) = (associatedAction b (End b ⧸ H)).map g (eH.symm x) := by
      apply eH.injective
      simpa [eH, associatedAction_base_equiv_smul] using
        (associatedAction_base_equiv_smul b (End b ⧸ H) g (eH.symm x))
    -- Naturality at the loop `g` identifies the base component with the orbit-side action.
    calc
      eK (η.app b (eH.symm (g • x))) = eK (η.app b ((associatedAction b (End b ⧸ H)).map g (eH.symm x))) := by
        rw [hsource]
      _ = eK ((associatedAction b (End b ⧸ K)).map g (η.app b (eH.symm x))) := by
        simpa using congrFun (η.naturality g) (eH.symm x)
      _ = g • eK (η.app b (eH.symm x)) := by
        rw [associatedAction_base_equiv_smul]

/-- Helper for Theorem 3.6.1: passing from orbit morphisms to natural transformations of
associated actions is injective. -/
private theorem associatedAction_hom_injective
    (H K : O(End b)) :
    Function.Injective
      (fun φ : H ⟶ K ↦
        (associatedActionHom b φ :
          associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K))) := by
  let recover :
      (associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K)) → (H ⟶ K) :=
    associated_action_to_orbit_morphism (b := b)
  have hrecover :
      Function.LeftInverse recover
        (fun φ : H ⟶ K ↦
          (associatedActionHom b φ :
            associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K))) := by
    intro φ
    have hbase (x : End b ⧸ H) :
        (associatedAction_base_equiv b (End b ⧸ H)).symm x =
          Quotient.mk'' (𝟙 b, x) := by
      apply (associatedAction_base_equiv b (End b ⧸ H)).injective
      calc
        associatedAction_base_equiv b (End b ⧸ H)
            ((associatedAction_base_equiv b (End b ⧸ H)).symm x) = x := by
              simp
        _ = associatedAction_base_equiv b (End b ⧸ H) (Quotient.mk'' (𝟙 b, x)) := by
              change x = (show End b from 𝟙 b) • x
              simpa using (one_smul (End b) x).symm
    apply MulActionHom.ext
    intro x
    -- Evaluating on the identity-arrow class in the base fiber recovers the original orbit map.
    change
      associatedAction_base_equiv b (End b ⧸ K)
        ((associatedActionHom b φ).app b ((associatedAction_base_equiv b (End b ⧸ H)).symm x)) =
          φ.toFun x
    rw [show (associatedAction_base_equiv b (End b ⧸ H)).symm x =
      Quotient.mk'' (𝟙 b, x) from hbase x]
    change associatedAction_base_equiv b (End b ⧸ K) (Quotient.mk'' (𝟙 b, φ.toFun x)) =
      φ.toFun x
    change (show End b from 𝟙 b) • φ.toFun x = φ.toFun x
    simpa using (one_smul (End b) (φ.toFun x))
  -- A left inverse on hom-sets makes the associated-action construction faithful.
  exact hrecover.injective

/-- Helper for Theorem 3.6.1: recovering an orbit morphism from a natural transformation between
associated actions reproduces the original natural transformation. -/
private theorem associatedAction_hom_recover
    {H K : O(End b)}
    (η : associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K)) :
    associatedActionHom b (associated_action_to_orbit_morphism (b := b) η) = η := by
  let ψ : H ⟶ K := associated_action_to_orbit_morphism (b := b) η
  have hsource (s : End b ⧸ H) :
      (associatedAction_base_equiv b (End b ⧸ H)).symm s =
        Quotient.mk'' (𝟙 b, s) := by
    apply (associatedAction_base_equiv b (End b ⧸ H)).injective
    calc
      associatedAction_base_equiv b (End b ⧸ H)
          ((associatedAction_base_equiv b (End b ⧸ H)).symm s) = s := by
            simp
      _ = associatedAction_base_equiv b (End b ⧸ H) (Quotient.mk'' (𝟙 b, s)) := by
            change s = (show End b from 𝟙 b) • s
            simpa using (one_smul (End b) s).symm
  have htarget (t : End b ⧸ K) :
      (associatedAction_base_equiv b (End b ⧸ K)).symm t =
        Quotient.mk'' (𝟙 b, t) := by
    apply (associatedAction_base_equiv b (End b ⧸ K)).injective
    calc
      associatedAction_base_equiv b (End b ⧸ K)
          ((associatedAction_base_equiv b (End b ⧸ K)).symm t) = t := by
            simp
      _ = associatedAction_base_equiv b (End b ⧸ K) (Quotient.mk'' (𝟙 b, t)) := by
            change t = (show End b from 𝟙 b) • t
            simpa using (one_smul (End b) t).symm
  ext x q
  refine Quotient.inductionOn' q ?_
  rintro ⟨f, s⟩
  have hbase :
      η.app b (Quotient.mk'' (𝟙 b, s)) =
        Quotient.mk'' (𝟙 b, ψ.toFun s) := by
    -- First rewrite the source point into the canonical base-fiber normal form, then do the same
    -- on the target after applying `η`.
    calc
      η.app b (Quotient.mk'' (𝟙 b, s)) =
          η.app b ((associatedAction_base_equiv b (End b ⧸ H)).symm s) := by
            rw [← hsource s]
      _ =
          (associatedAction_base_equiv b (End b ⧸ K)).symm
            ((associatedAction_base_equiv b (End b ⧸ K))
              (η.app b ((associatedAction_base_equiv b (End b ⧸ H)).symm s))) := by
            simp
      _ = Quotient.mk'' (𝟙 b, ψ.toFun s) := by
            change (associatedAction_base_equiv b (End b ⧸ K)).symm (ψ.toFun s) =
              Quotient.mk'' (𝟙 b, ψ.toFun s)
            exact htarget (ψ.toFun s)
  have hnat :
      associatedActionMap b (End b ⧸ K) f (η.app b (Quotient.mk'' (𝟙 b, s))) =
        η.app x (associatedActionMap b (End b ⧸ H) f (Quotient.mk'' (𝟙 b, s))) := by
    -- Naturality at `f` propagates the recovered base-fiber value to the fiber over `x`.
    simpa using (congrFun (η.naturality f) (Quotient.mk'' (𝟙 b, s))).symm
  have h1 :
      (associatedActionHom b ψ).app x (Quotient.mk'' (f, s)) =
        Quotient.mk'' (f, ψ.toFun s) := by
    rfl
  have h2 :
      Quotient.mk'' (f, ψ.toFun s) =
        associatedActionMap b (End b ⧸ K) f (Quotient.mk'' (𝟙 b, ψ.toFun s)) := by
    change Quotient.mk'' (f, ψ.toFun s) = Quotient.mk'' ((𝟙 b) ≫ f, ψ.toFun s)
    simp
  have h3 :
      associatedActionMap b (End b ⧸ K) f (Quotient.mk'' (𝟙 b, ψ.toFun s)) =
        associatedActionMap b (End b ⧸ K) f (η.app b (Quotient.mk'' (𝟙 b, s))) := by
    rw [hbase]
  have h4 :
      η.app x (associatedActionMap b (End b ⧸ H) f (Quotient.mk'' (𝟙 b, s))) =
        η.app x (Quotient.mk'' (f, s)) := by
    change η.app x (Quotient.mk'' ((𝟙 b) ≫ f, s)) = η.app x (Quotient.mk'' (f, s))
    simp
  exact h1.trans (h2.trans (h3.trans (hnat.trans h4)))

/-- Helper for Theorem 3.6.1: the inverse base-fiber equivalence sends a point of the base fiber
to the identity-arrow class representing it. -/
private theorem associatedAction_base_symm_eq_id_class
    (b : B) (S : Type v) [MulAction (End b) S] (s : S) :
    (associatedAction_base_equiv b S).symm s = Quotient.mk'' (𝟙 b, s) := by
  apply (associatedAction_base_equiv b S).injective
  -- The identity-arrow representative evaluates to the original point.
  calc
    associatedAction_base_equiv b S ((associatedAction_base_equiv b S).symm s) = s := by
      simp
    _ = associatedAction_base_equiv b S (Quotient.mk'' (𝟙 b, s)) := by
      change s = (show End b from 𝟙 b) • s
      simpa using (one_smul (End b) s).symm

/-- Helper for Theorem 3.6.1: transporting the identity-arrow class along `f` produces the class
represented by `f` and the same orbit element. -/
private theorem associatedActionMap_idClass
    (b : B) (S : Type v) [MulAction (End b) S] {x : B} (f : b ⟶ x) (s : S) :
    associatedActionMap b S f (Quotient.mk'' (𝟙 b, s)) = Quotient.mk'' (f, s) := by
  -- The associated-action transport only postcomposes the arrow component of a representative.
  change Quotient.mk'' ((𝟙 b) ≫ f, s) = Quotient.mk'' (f, s)
  simp

/-- Helper for Theorem 3.6.1: normalizing a representative with a chosen path leaves its orbit
class unchanged. -/
private theorem associatedAction_chosen_path_class_eq
    (T : B ⥤ Type v) (a : ∀ x : B, b ⟶ x) {x : B} (f : b ⟶ x) (s : T.obj b) :
    (Quotient.mk'' (a x, T.map (inv (a x)) (T.map f s)) :
      associatedActionObj b (T.obj b) x) =
      Quotient.mk'' (f, s) := by
  letI := Functor.vertexGroupMulAction T b
  -- Compare the two representatives by the loop sending `a x` back to `f`.
  apply Quotient.sound
  change
    MulAction.orbitRel (End b) ((b ⟶ x) × T.obj b)
      (a x, T.map (inv (a x)) (T.map f s)) (f, s)
  rw [MulAction.orbitRel_apply]
  refine ⟨show End b from f ≫ inv (a x), ?_⟩
  ext
  · simp [Category.assoc]
  · simp [FunctorToTypes.map_comp_apply]

/-- Helper for Theorem 3.6.1: over a connected base groupoid, an action is reconstructed from its
base fiber and the corresponding `π(B,b)`-action. -/
private theorem associatedAction_of_vertexGroupMulAction_iso
    [IsConnected B] (T : B ⥤ Type v) :
    Nonempty (associatedAction b (T.obj b) ≅ T) := by
  classical
  letI : MulAction (End b) (T.obj b) := Functor.vertexGroupMulAction T b
  let a : ∀ x : B, b ⟶ x := fun x ↦
    Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid b x)
  let hom : associatedAction b (T.obj b) ⟶ T :=
    { app := fun x ↦
        Quotient.lift (fun p : (b ⟶ x) × T.obj b ↦ T.map p.1 p.2) <| by
          intro p q hp
          change MulAction.orbitRel (End b) ((b ⟶ x) × T.obj b) p q at hp
          rw [MulAction.orbitRel_apply] at hp
          rcases hp with ⟨g, rfl⟩
          -- The diagonal orbit relation preserves the corresponding point of `T.obj x`.
          have hg :
              T.map (inv g) (T.map g q.2) = q.2 := by
            simpa using FunctorToTypes.map_inv_map_hom_apply T (asIso g) q.2
          calc
            T.map (inv g ≫ q.1) (g • q.2) = T.map q.1 (T.map (inv g) (T.map g q.2)) := by
              simp [CategoryTheory.Groupoid.homMulAction_smul,
                Functor.vertexGroupMulAction_smul_eq_map, FunctorToTypes.map_comp_apply]
            _ = T.map q.1 q.2 := by rw [hg]
      naturality := by
        intro x y f
        funext q
        refine Quotient.inductionOn' q ?_
        intro p
        change T.map (p.1 ≫ f) p.2 = T.map f (T.map p.1 p.2)
        simp [FunctorToTypes.map_comp_apply] }
  let inv : T ⟶ associatedAction b (T.obj b) :=
    { app := fun x t ↦ Quotient.mk'' (a x, T.map (inv (a x)) t)
      naturality := by
        intro x y f
        funext t
        -- Normalize the transported representative using the chosen path family `a`.
        change
          Quotient.mk'' (a y, T.map (inv (a y)) (T.map f t)) =
            Quotient.mk'' (a x ≫ f, T.map (inv (a x)) t)
        have hx :
            T.map (a x) (T.map (inv (a x)) t) = t := by
          simpa using FunctorToTypes.map_hom_map_inv_apply T (asIso (a x)) t
        have hmid :
            T.map f (T.map (a x) (T.map (inv (a x)) t)) = T.map f t := by
          exact congrArg (T.map f) hx
        have hnorm :
            T.map (a x ≫ f) (T.map (inv (a x)) t) = T.map f t := by
          simpa [FunctorToTypes.map_comp_apply] using hmid
        have hchosen :=
          associatedAction_chosen_path_class_eq (b := b) T a
            (f := a x ≫ f) (s := T.map (inv (a x)) t)
        rw [hnorm] at hchosen
        simpa [FunctorToTypes.map_comp_apply, Category.assoc] using hchosen }
  refine ⟨{ hom := hom, inv := inv, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    -- The chosen path representative collapses back to the original class.
    simpa [hom, inv, FunctorToTypes.map_comp_apply] using
      (associatedAction_chosen_path_class_eq (b := b) T a (f := p.1) (s := p.2))
  · ext x t
    -- The chosen path followed by its inverse acts trivially in the groupoid.
    simpa [hom, inv] using
      (FunctorToTypes.map_hom_map_inv_apply T (asIso (a x)) t)

/-- Helper for Theorem 3.6.1: an equivariant equivalence of `π(B,b)`-sets induces an isomorphism
between the corresponding associated `B`-actions. -/
private noncomputable def associatedAction_iso_of_equivariant_equiv
    {S T : Type v} [MulAction (End b) S] [MulAction (End b) T]
    (e : S ≃ T) (he : ∀ (g : End b) x, e (g • x) = g • e x) :
    associatedAction b S ≅ associatedAction b T where
  hom := associatedActionHom b
    { toFun := e
      map_smul' := he }
  inv := associatedActionHom b
    { toFun := e.symm
      map_smul' := by
        intro g x
        apply e.injective
        simpa [he] using he g (e.symm x) }
  hom_inv_id := by
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1, e.symm (e p.2)) = Quotient.mk'' p
    simp
  inv_hom_id := by
    ext x q
    refine Quotient.inductionOn' q ?_
    intro p
    change Quotient.mk'' (p.1, e (e.symm p.2)) = Quotient.mk'' p
    simp

/-- Helper for Theorem 3.6.1: every transitive `B`-action is represented by the orbit of the
stabilizer of a chosen point in the base fiber. -/
private theorem transitive_groupoid_action_iso_quotient_stabilizer
    [IsConnected B]
    (T : CategoryTheory.ObjectProperty.FullSubcategory
      (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v))) :
    ∃ H : O(End b), Nonempty ((orbitCategoryToTransitiveGroupoidAction b).obj H ≅ T) := by
  letI : MulAction (End b) (T.1.obj b) := Functor.vertexGroupMulAction T.1 b
  have hTb : MulAction.IsTransitive (End b) (T.1.obj b) :=
    (Functor.vertexGroupAction_isTransitive_iff_vertexGroupMulAction_isTransitive T.1 b).mp
      (T.2 b)
  letI : MulAction.IsPretransitive (End b) (T.1.obj b) := hTb.isPretransitive
  obtain ⟨t⟩ := hTb.nonempty
  let H : O(End b) := ⟨MulAction.stabilizer (End b) t⟩
  rcases associatedAction_of_vertexGroupMulAction_iso (b := b) T.1 with ⟨i⟩
  let e : associatedAction b (End b ⧸ H) ≅ associatedAction b (T.1.obj b) :=
    associatedAction_iso_of_equivariant_equiv (b := b)
      (quotientStabilizerEquivOfIsPretransitive t)
      (fun g x ↦ quotientStabilizerEquivOfIsPretransitive_equivariant t g x)
  refine ⟨H, ⟨?_⟩⟩
  -- First identify the base fiber with the quotient by the stabilizer, then reconstruct `T`.
  exact
    CategoryTheory.ObjectProperty.isoMk
      (P := (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v)))
      (X := (orbitCategoryToTransitiveGroupoidAction b).obj H)
      (Y := T) (e ≪≫ i)

/-- Helper for Theorem 3.6.1: an over-morphism between categories of elements determines a
natural transformation of the underlying functors. -/
-- The commutativity condition over `B` pins down the first component of each image object, so the
-- second component can be read off as the desired value of the natural transformation.
private theorem elementsFunctorOver_obj_fst_eq
    {T U : B ⥤ Type v} (F : elementsFunctorOver T ⟶ elementsFunctorOver U)
    (x : T.Elements) :
    (F.left.obj x).1 = x.1 := by
  simpa using congrArg (fun G ↦ G.obj x) F.comm

/-- Helper for Theorem 3.6.1: the underlying base arrow of an `eqToHom` in the category of
elements is the corresponding `eqToHom` between base objects. -/
private theorem elements_eqToHom_val
    {T : B ⥤ Type v} {x y : T.Elements} (h : x = y) :
    ((eqToHom h : x ⟶ y).1) = eqToHom (congrArg Sigma.fst h) := by
  cases h
  rfl

/-- Helper for Theorem 3.6.1: an over-morphism of categories of elements transports each element
morphism by the corresponding base-object equalities. -/
private theorem elementsFunctorOver_map_val_eq
    {T U : B ⥤ Type v} (F : elementsFunctorOver T ⟶ elementsFunctorOver U)
    {x y : T.Elements} (f : x ⟶ y) :
    (F.left.map f).1 =
      eqToHom (elementsFunctorOver_obj_fst_eq F x) ≫ f.1 ≫
        eqToHom (elementsFunctorOver_obj_fst_eq F y).symm := by
  -- The commuting triangle over `B` determines the underlying base arrow of `F.left.map f`.
  simpa using Functor.congr_hom F.comm f

/-- Helper for Theorem 3.6.1: an over-morphism of categories of elements preserves the base
object of every element, so its second component defines a natural transformation. -/
private noncomputable def elementsFunctorOver_natTrans_of_over_hom
    {T U : B ⥤ Type v} (F : elementsFunctorOver T ⟶ elementsFunctorOver U) :
    T ⟶ U where
  app x t :=
    let h := elementsFunctorOver_obj_fst_eq F ⟨x, t⟩
    U.map (eqToHom h) (F.left.obj ⟨x, t⟩).2
  naturality {x} {y} f := by
    funext t
    let x' : T.Elements := ⟨x, t⟩
    let y' : T.Elements := ⟨y, T.map f t⟩
    let hx : (F.left.obj x').1 = x := elementsFunctorOver_obj_fst_eq F x'
    let hy : (F.left.obj y').1 = y := elementsFunctorOver_obj_fst_eq F y'
    let f' : x' ⟶ y' := CategoryOfElements.homMk x' y' f rfl
    have hmap :
        U.map (eqToHom hx ≫ f ≫ eqToHom hy.symm) (F.left.obj x').2 =
          (F.left.obj y').2 := by
      -- Read off the endpoint equation from the image of the canonical element morphism.
      simpa [x', y', hx, hy, f', elementsFunctorOver_map_val_eq,
        FunctorToTypes.map_comp_apply] using
        (CategoryOfElements.map_snd (F.left.map f'))
    have hmap' :
        U.map (eqToHom hy.symm) (U.map (eqToHom hx ≫ f) (F.left.obj x').2) =
          (F.left.obj y').2 := by
      simpa [FunctorToTypes.map_comp_apply, Category.assoc] using hmap
    -- Postcompose with the target-side transport to isolate the naturality square.
    simpa [x', y', hx, hy, FunctorToTypes.map_comp_apply, Category.assoc] using
      (congrArg (U.map (eqToHom hy)) hmap').symm

/-- Helper for Theorem 3.6.1: reconstructing an over-morphism from the recovered natural
transformation gives back the original over-morphism. -/
-- Compare the two functors on objects and then on morphisms; both comparisons reduce to the fact
-- that `F` already lies over `B`.
private theorem elementsFunctorOver_natTrans_of_over_hom_spec
    {T U : B ⥤ Type v} (F : elementsFunctorOver T ⟶ elementsFunctorOver U) :
    elementsFunctorOverMap (elementsFunctorOver_natTrans_of_over_hom F) = F := by
  apply GroupoidFunctorOver.Hom.ext
  -- Compare the underlying functors on objects and morphisms in the category of elements.
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro x
    rcases x with ⟨x, t⟩
    let h : (F.left.obj ⟨x, t⟩).1 = x := elementsFunctorOver_obj_fst_eq F ⟨x, t⟩
    -- The recovered component lands in the same element object as `F.left.obj ⟨x, t⟩`.
    refine Functor.Elements.ext _ _ h.symm ?_
    simpa [elementsFunctorOver_natTrans_of_over_hom, h, FunctorToTypes.map_comp_apply]
  · intro x y f
    -- After transporting source and target objects through the object equalities above, both
    -- morphisms have the same underlying base arrow.
    apply CategoryOfElements.ext U
    simp [elementsFunctorOverMap, elementsFunctorOver_natTrans_of_over_hom,
      elementsFunctorOver_map_val_eq, elementsFunctorOver_obj_fst_eq, elements_eqToHom_val,
      Category.assoc]

/-- Helper for Theorem 3.6.1: the category-of-elements construction is faithful on morphisms of
transitive actions. -/
-- Once an over-morphism is reconstructed uniquely from its category-of-elements image, equality of
-- those images forces equality of the original natural transformations objectwise.
private theorem elementsFunctorOver_hom_injective
    (T U : B ⥤ Type v) :
    Function.Injective
      (fun α : T ⟶ U ↦
        (elementsFunctorOverMap α : elementsFunctorOver T ⟶ elementsFunctorOver U)) := by
  intro α β hαβ
  apply NatTrans.ext
  funext x
  funext t
  -- Equality of the induced functors on categories of elements already agrees on the literal
  -- element object `⟨x, t⟩`.
  have hobj :
      (CategoryOfElements.map α).obj ⟨x, t⟩ = (CategoryOfElements.map β).obj ⟨x, t⟩ := by
    exact congrArg (fun F : T.Elements ⥤ U.Elements ↦ F.obj ⟨x, t⟩) (congrArg (fun h ↦ h.left) hαβ)
  simpa using (Sigma.mk.inj_iff.mp hobj).2

/-- Helper for Theorem 3.6.1: the fiber of the projection `CategoryOfElements.π T` over `b`
identifies with the ordinary fiber `T.obj b`. -/
-- A point of the fiber is precisely an element `t : T.obj x` together with an equality `x = b`,
-- so transporting along that equality gives the desired point of `T.obj b`.
private noncomputable def elementsProjectionFiberEquiv
    (T : B ⥤ Type v) (b : B) :
    (CategoryOfElements.π T).Fiber b ≃ T.obj b where
  toFun x := x.2 ▸ x.1.2
  invFun t := ⟨⟨b, t⟩, rfl⟩
  left_inv x := by
    rcases x with ⟨⟨x, t⟩, hx⟩
    subst hx
    rfl
  right_inv t := by
    rfl

/-- Helper for Theorem 3.6.1: translating a point in the fiber of `CategoryOfElements.π T`
along a base morphism simply applies `T.map` to its chosen element. -/
private theorem elementsProjectionFiberEquiv_fiberTranslationMap
    (T : B ⥤ Type v) {b b' : B} (hp : Functor.IsCovering (CategoryOfElements.π T))
    (f : b ⟶ b') (x : (CategoryOfElements.π T).Fiber b) :
    elementsProjectionFiberEquiv T b' (fiberTranslationMap hp f x) =
      T.map f (elementsProjectionFiberEquiv T b x) := by
  rcases x with ⟨⟨x, t⟩, hx⟩
  cases hx
  let x0 : T.Elements := ⟨x, t⟩
  let y : T.Elements := ⟨b', T.map f t⟩
  let m : x0 ⟶ y := CategoryOfElements.homMk x0 y f rfl
  have hstar :
      starLift hp f (⟨x0, rfl⟩ : (CategoryOfElements.π T).Fiber x) = Under.mk m := by
    -- Route correction: compare the chosen lift against the explicit element morphism after
    -- applying the injective star map, instead of normalizing `Under` endpoints by hand.
    apply (hp.star_bijective x0).injective
    calc
      (Under.post (CategoryOfElements.π T)).obj
          (starLift hp f (⟨x0, rfl⟩ : (CategoryOfElements.π T).Fiber x)) =
          Under.mk f := by
        simpa using starLift_post_eq hp f (⟨x0, rfl⟩ : (CategoryOfElements.π T).Fiber x)
      _ = (Under.post (CategoryOfElements.π T)).obj (Under.mk m) := by
        rfl
  have hfiber :
      fiberTranslationMap hp f (⟨x0, rfl⟩ : (CategoryOfElements.π T).Fiber x) = ⟨y, rfl⟩ := by
    -- Equality of the lifted under-objects identifies the translated fiber point.
    apply Subtype.ext
    change (starLift hp f (⟨x0, rfl⟩ : (CategoryOfElements.π T).Fiber x)).right = y
    exact congrArg Comma.right hstar
  -- The target fiber point literally carries the transported element `T.map f t`.
  calc
    elementsProjectionFiberEquiv T b'
        (fiberTranslationMap hp f (⟨x0, rfl⟩ : (CategoryOfElements.π T).Fiber x)) =
        elementsProjectionFiberEquiv T b' ⟨y, rfl⟩ := by
          exact congrArg (elementsProjectionFiberEquiv T b') hfiber
    _ = T.map f t := by
      rfl

/-- Helper for Theorem 3.6.1: the canonical identification of the fiber of
`CategoryOfElements.π T` with `T.obj b` is equivariant for the loop action at `b`. -/
-- In the category of elements, the chosen lift of `γ⁻¹` from `(b,t)` is the explicit morphism
-- whose endpoint is `(b, T.map γ⁻¹ t)`, so the fiber action matches the usual vertex-group
-- action on `T.obj b`.
private theorem elementsProjectionFiberEquiv_smul
    (T : B ⥤ Type v) (b : B) (hp : Functor.IsCovering (CategoryOfElements.π T))
    (γ : b ⟶ b) (x : (CategoryOfElements.π T).Fiber b) :
    elementsProjectionFiberEquiv T b (γ • x) =
      γ • elementsProjectionFiberEquiv T b x := by
  -- Rewrite the fiber action as fiber translation, then evaluate it through the explicit
  -- identification of the fiber with `T.obj b`.
  rw [fiberTranslationMulAction_smul_eq_map_inv,
    elementsProjectionFiberEquiv_fiberTranslationMap]
  simpa using
    (Functor.vertexGroupAction_smul_eq_map_inv T b γ
      (elementsProjectionFiberEquiv T b x)).symm

/-- Helper for Theorem 3.6.1: the above fiber identification carries the stabilizer of the
distinguished point in the category-of-elements fiber to the stabilizer of the chosen element in
the original fiber. -/
-- The preceding equivariance lemma identifies the fixed-point equations on both sides, so the two
-- stabilizer subgroups coincide elementwise.
private theorem elementsProjectionFiberEquiv_stabilizer
    (T : B ⥤ Type v) (b : B) (hp : Functor.IsCovering (CategoryOfElements.π T))
    (t : T.obj b) :
    MulAction.stabilizer (b ⟶ b) ((elementsProjectionFiberEquiv T b).symm t) =
      MulAction.stabilizer (b ⟶ b) t := by
  ext γ
  constructor
  · intro hγ
    change γ • (elementsProjectionFiberEquiv T b).symm t =
      (elementsProjectionFiberEquiv T b).symm t at hγ
    -- Apply the fiber equivalence to the fixed-point equation and simplify via equivariance.
    have hγ' := congrArg (elementsProjectionFiberEquiv T b) hγ
    simpa [elementsProjectionFiberEquiv_smul, hp] using hγ'
  · intro hγ
    change γ • (elementsProjectionFiberEquiv T b).symm t =
      (elementsProjectionFiberEquiv T b).symm t
    -- The equivalence is injective, so it suffices to compare the corresponding elements of `T`.
    apply (elementsProjectionFiberEquiv T b).injective
    simpa [elementsProjectionFiberEquiv_smul, hp] using hγ

/-- Helper for Theorem 3.6.1: the canonical point of the orbit covering over the base object `b`
is represented by the identity arrow and the identity coset. -/
private noncomputable abbrev orbitCategoryAssociatedAction_basepoint
    (b : B) (H : O(End b)) :
    (CategoryOfElements.π (associatedAction b (End b ⧸ H))).Fiber b :=
  ⟨⟨b, Quotient.mk'' (𝟙 b, (((1 : End b) : End b ⧸ H)))⟩, rfl⟩

/-- Helper for Theorem 3.6.1: every morphism of connected orbit coverings comes from a unique
orbit-category morphism. -/
-- The category-of-elements owner already lets us reconstruct the underlying natural
-- transformation of associated actions, and the orbit-side classifier then upgrades it back to an
-- actual orbit morphism.
private theorem orbitCategoryToConnectedCovering_map_surjective
    [IsConnected B]
    {H K : O(End b)}
    (F : (orbitCategoryToConnectedCovering b).obj H ⟶
      (orbitCategoryToConnectedCovering b).obj K) :
    ∃ φ : H ⟶ K, (orbitCategoryToConnectedCovering b).map φ = F := by
  let η :
      associatedAction b (End b ⧸ H) ⟶ associatedAction b (End b ⧸ K) :=
    elementsFunctorOver_natTrans_of_over_hom F.hom
  refine ⟨associated_action_to_orbit_morphism (b := b) η, ?_⟩
  apply ObjectProperty.hom_ext
  -- Recover the natural transformation from the over-morphism and then push it back to the orbit
  -- category using the already proved associated-action classifier.
  change
    elementsFunctorOverMap
        (associatedActionHom b (associated_action_to_orbit_morphism (b := b) η)) =
      F.hom
  calc
    elementsFunctorOverMap
        (associatedActionHom b (associated_action_to_orbit_morphism (b := b) η)) =
        elementsFunctorOverMap η := by
          rw [associatedAction_hom_recover (b := b) η]
    _ = F.hom := elementsFunctorOver_natTrans_of_over_hom_spec F.hom

/-- Helper for Theorem 3.6.1: the orbit-category-to-transitive-action functor is an equivalence. -/
private theorem orbitCategoryToTransitiveGroupoidAction_isEquivalence_aux
    [IsConnected B]
    (b : B) :
    Functor.IsEquivalence (orbitCategoryToTransitiveGroupoidAction b) := by
  let _ : (orbitCategoryToTransitiveGroupoidAction b).Faithful :=
    { map_injective := by
        intro H K φ ψ hφψ
        -- Faithfulness reduces to injectivity of `associatedActionHom` on the underlying orbit
        -- morphisms.
        exact associatedAction_hom_injective (b := b) H K
          (congrArg (fun h ↦ h.hom) hφψ) }
  let _ : (orbitCategoryToTransitiveGroupoidAction b).Full :=
    { map_surjective := by
        intro H K η
        -- Fullness is exactly the base-fiber recovery statement for natural transformations.
        refine ⟨associated_action_to_orbit_morphism (b := b) η.hom, ?_⟩
        apply ObjectProperty.hom_ext
        exact associatedAction_hom_recover (b := b) η.hom }
  let _ : (orbitCategoryToTransitiveGroupoidAction b).EssSurj :=
    { mem_essImage := by
        intro T
        -- Every transitive action is represented by the orbit of the stabilizer of a base-fiber
        -- point.
        rcases transitive_groupoid_action_iso_quotient_stabilizer (b := b) T with ⟨H, ⟨e⟩⟩
        exact ⟨H, ⟨e⟩⟩ }
  -- Route correction: finish the first factor by the standard faithful/full/essentially-surjective
  -- criterion instead of the abandoned direct-composite covering branch.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- Helper for Theorem 3.6.1: transporting a subgroup inclusion from the literal source and target
objects to the common base object `b` is equivalent to transporting both subgroups separately. -/
private theorem subgroup_transport_le_iff
    {x y : B} (hx : x = b) (hy : y = b)
    (A : Subgroup (x ⟶ x)) (C : Subgroup (y ⟶ y)) :
    A ≤ hy.trans hx.symm ▸ C ↔ hx ▸ A ≤ hy ▸ C := by
  cases hx
  cases hy
  simp

/-- Helper for Theorem 3.6.1: a morphism in `GroupoidFunctorOver B` is an isomorphism exactly
when it identifies the corresponding basepoint subgroups in `π(B,b)`. -/
private theorem groupoidFunctorOver_isIso_iff_mapVertexGroup_range_eq_large
    {X Y : GroupoidFunctorOver B}
    [IsConnected X.left] [IsPreconnected Y.left]
    (hx : Functor.IsCovering X.hom) (hy : Functor.IsCovering Y.hom)
    (e : X.hom.Fiber b) (e' : Y.hom.Fiber b)
    (h : X ⟶ Y) (hh : h.left.obj e.1 = e'.1) :
    IsIso h ↔
      e.2 ▸ (Functor.mapVertexGroup X.hom e.1).range =
        e'.2 ▸ (Functor.mapVertexGroup Y.hom e'.1).range := by
  constructor
  · intro hIso
    letI := hIso
    let hF : X.left ⥤ Y.left := h.left
    let gF : Y.left ⥤ X.left := (CategoryTheory.inv h).left
    have hhF : hF.obj e.1 = e'.1 := by
      simpa [hF] using hh
    -- The inverse morphism sends the chosen target point back to the chosen source point.
    have hgF : gF.obj e'.1 = e.1 := by
      have hcomp : h ≫ CategoryTheory.inv h = 𝟙 _ := by
        simp
      have hpoint : gF.obj (hF.obj e.1) = e.1 := by
        exact congrArg
          (fun k : X ⟶ X ↦
            let kF : X.left ⥤ X.left := k.left
            kF.obj e.1) hcomp
      simpa [hF, gF, hhF] using hpoint
    have hle₀ :
        (Functor.mapVertexGroup X.hom e.1).range ≤
          (e'.2.trans e.2.symm) ▸ (Functor.mapVertexGroup Y.hom e'.1).range := by
      -- Apply the lift criterion to the underlying inverse-free functor `h.left`.
      exact Functor.mapVertexGroup_range_le_of_lift e.1 ⟨e'.1, e'.2.trans e.2.symm⟩ h.comm hhF
    have hle :
        e.2 ▸ (Functor.mapVertexGroup X.hom e.1).range ≤
          e'.2 ▸ (Functor.mapVertexGroup Y.hom e'.1).range := by
      exact (subgroup_transport_le_iff (b := b) e.2 e'.2 _ _).mp hle₀
    have hgOver : gF ⋙ X.hom = Y.hom := by
      simpa [gF] using (CategoryTheory.inv h).comm
    have hle'₀ :
        (Functor.mapVertexGroup Y.hom e'.1).range ≤
          (e.2.trans e'.2.symm) ▸ (Functor.mapVertexGroup X.hom e.1).range := by
      -- Apply the same lift criterion to the inverse morphism.
      exact
        Functor.mapVertexGroup_range_le_of_lift e'.1 ⟨e.1, e.2.trans e'.2.symm⟩ hgOver hgF
    have hle' :
        e'.2 ▸ (Functor.mapVertexGroup Y.hom e'.1).range ≤
          e.2 ▸ (Functor.mapVertexGroup X.hom e.1).range := by
      exact (subgroup_transport_le_iff (b := b) e'.2 e.2 _ _).mp hle'₀
    exact le_antisymm hle hle'
  · intro hEq
    -- Local instance justification (connectedness): `existsUnique_lift_iff_mapVertexGroup_range_le`
    -- needs a connected source, and `e'.1` upgrades the preconnected total groupoid `Y.left`.
    letI : Nonempty Y.left := ⟨e'.1⟩
    -- Local instance justification (connectedness): combine the chosen point with the existing
    -- preconnectedness hypothesis to apply the lift uniqueness theorem on `Y.left`.
    letI : IsConnected Y.left := { toIsPreconnected := inferInstance }
    have hsub :
        (Functor.mapVertexGroup Y.hom e'.1).range ≤
          (e.2.trans e'.2.symm) ▸ (Functor.mapVertexGroup X.hom e.1).range := by
      exact (subgroup_transport_le_iff (b := b) e'.2 e.2 _ _).mpr hEq.symm.le
    obtain ⟨gF, hgF, huniqg⟩ :=
      (existsUnique_lift_iff_mapVertexGroup_range_le
        (p := X.hom) hx e'.1 ⟨e.1, e.2.trans e'.2.symm⟩).2 hsub
    let g : Y ⟶ X := GroupoidFunctorOver.homMk gF hgF.1
    have hhF : h.left.obj e.1 = e'.1 := by
      simpa using hh
    have hgPoint : g.left.obj e'.1 = e.1 := by
      simpa [g] using hgF.2
    let hgFcomp : X.left ⥤ X.left := (h ≫ g).left
    have hhg : hgFcomp.obj e.1 = e.1 := by
      change g.left.obj (h.left.obj e.1) = e.1
      simpa [hhF] using hgPoint
    obtain ⟨_, _, huniqk⟩ :=
      (existsUnique_lift_iff_mapVertexGroup_range_le
        (p := X.hom) hx e.1 ⟨e.1, rfl⟩).2 le_rfl
    have h_comp_g_left : (h ≫ g).left = 𝟭 X.left := by
      exact
        (huniqk (h ≫ g).left
          ⟨by simpa [hgFcomp, g] using (h ≫ g).comm, by simpa [hgFcomp] using hhg⟩).trans
          (huniqk (𝟭 X.left) ⟨rfl, rfl⟩).symm
    have h_comp_g : h ≫ g = 𝟙 _ := by
      exact GroupoidFunctorOver.Hom.ext h_comp_g_left
    let ghFcomp : Y.left ⥤ Y.left := (g ≫ h).left
    have hgh : ghFcomp.obj e'.1 = e'.1 := by
      change h.left.obj (g.left.obj e'.1) = e'.1
      simpa [hgPoint] using hhF
    obtain ⟨_, _, huniqk'⟩ :=
      (existsUnique_lift_iff_mapVertexGroup_range_le
        (p := Y.hom) hy e'.1 ⟨e'.1, rfl⟩).2 le_rfl
    have g_comp_h_left : (g ≫ h).left = 𝟭 Y.left := by
      exact
        (huniqk' (g ≫ h).left
          ⟨by simpa [ghFcomp, g] using (g ≫ h).comm, by simpa [ghFcomp] using hgh⟩).trans
          (huniqk' (𝟭 Y.left) ⟨rfl, rfl⟩).symm
    have g_comp_h : g ≫ h = 𝟙 _ := by
      exact GroupoidFunctorOver.Hom.ext g_comp_h_left
    exact ⟨⟨g, h_comp_g, g_comp_h⟩⟩

/-- Helper for Theorem 3.6.1: the identity coset in `π(B,b) / H` has stabilizer exactly `H`. -/
private theorem identity_coset_stabilizer_eq_subgroup
    (H : O(End b)) :
    MulAction.stabilizer (End b) (((1 : End b) : End b ⧸ H)) = H := by
  -- The quotient action fixes the identity coset exactly along the subgroup itself.
  simpa using MulAction.stabilizer_quotient (H : Subgroup (End b))

/-- Helper for Theorem 3.6.1: the canonical basepoint of the orbit cover, viewed in the packaged
connected-covering object, is still the literal identity-class point. -/
private noncomputable def orbitCategoryAssociatedAction_packaged_basepoint
    [IsConnected B]
    (H : O(End b)) :
    let Ycov : ConnectedCovering B := (orbitCategoryToConnectedCovering b).obj H
    let Y : GroupoidFunctorOver B := Ycov.obj
    Y.hom.Fiber b :=
  orbitCategoryAssociatedAction_basepoint b H

/-- Helper for Theorem 3.6.1: the orbit-model covering realizes the subgroup `H` at the
canonical identity-class basepoint when its image subgroup is read in `End b`. -/
private theorem orbitCategoryAssociatedAction_basepointEndSubgroup_eq
    [IsConnected B] (H : O(End b)) :
    let Ycov : ConnectedCovering B := (orbitCategoryToConnectedCovering b).obj H
    let Y : GroupoidFunctorOver B := Ycov.obj
    let y0 : Y.hom.Fiber b := orbitCategoryAssociatedAction_packaged_basepoint (b := b) H
    loopSubgroupToEndSubgroup
      (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.hom y0.1).range) =
        (H : Subgroup (End b)) := by
  let Ycov : ConnectedCovering B := (orbitCategoryToConnectedCovering b).obj H
  let Y : GroupoidFunctorOver B := Ycov.obj
  let y0 : Y.hom.Fiber b := orbitCategoryAssociatedAction_packaged_basepoint (b := b) H
  let q : (associatedAction b (End b ⧸ H)).obj b :=
    Quotient.mk'' (𝟙 b, (((1 : End b) : End b ⧸ H)))
  let hpY : Functor.IsCovering Y.hom := inferInstance
  apply Subgroup.ext
  intro γ
  change (γ : b ⟶ b) ∈ (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.hom y0.1).range) ↔
      γ ∈ H
  have hmem :
      (γ : b ⟶ b) ∈ (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.hom y0.1).range) ↔
        fiberTranslationMap hpY γ y0 = y0 := by
    -- Membership in the image subgroup is equivalent to fixing the canonical fiber point.
    simpa [Ycov, Y, y0, orbitCategoryAssociatedAction_packaged_basepoint,
      orbitCategoryAssociatedAction_basepoint] using
      (mem_mapVertexGroup_range_iff_fiberTranslationMap_basepoint_eq hpY y0.1 γ)
  constructor
  · intro hγ
    have hy0 :
        elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b y0 = q := by
      rfl
    have hfix : fiberTranslationMap hpY γ y0 = y0 := hmem.mp hγ
    have hqfix :
        (associatedAction b (End b ⧸ H)).map γ q = q := by
      calc
        (associatedAction b (End b ⧸ H)).map γ q =
            (associatedAction b (End b ⧸ H)).map γ
              (elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b y0) := by
                rw [hy0]
        _ =
            elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b
              (fiberTranslationMap hpY γ y0) := by
                symm
                exact elementsProjectionFiberEquiv_fiberTranslationMap
                  (associatedAction b (End b ⧸ H)) hpY γ y0
        _ = q := by rw [hfix, hy0]
    change Quotient.mk'' ((𝟙 b) ≫ γ, (((1 : End b) : End b ⧸ H))) =
      Quotient.mk'' (𝟙 b, (((1 : End b) : End b ⧸ H))) at hqfix
    rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_symm] at hqfix
    rcases hqfix with ⟨k, hk⟩
    have hk_eq : (k : End b) = γ := by
      symm
      simpa [CategoryTheory.Groupoid.homMulAction_smul] using congrArg Prod.fst hk
    have hk_mem : (k : End b) ∈ (H : Subgroup (End b)) := by
      have hk_snd : (k : End b) • (((1 : End b) : End b ⧸ H)) = (((1 : End b) : End b ⧸ H)) := by
        simpa using congrArg Prod.snd hk
      have hk_quot : ((k : End b) : End b ⧸ H) = (((1 : End b) : End b ⧸ H)) := by
        simpa using hk_snd
      rw [QuotientGroup.eq] at hk_quot
      simpa using (H : Subgroup (End b)).inv_mem hk_quot
    simpa [hk_eq] using hk_mem
  · intro hγ
    have hy0 :
        elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b y0 = q := by
      rfl
    have hqfix :
        (associatedAction b (End b ⧸ H)).map γ q = q := by
      apply Quotient.sound
      change MulAction.orbitRel (End b) ((b ⟶ b) × (End b ⧸ H))
        ((𝟙 b) ≫ γ, (((1 : End b) : End b ⧸ H))) (𝟙 b, (((1 : End b) : End b ⧸ H)))
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_symm]
      refine ⟨γ, ?_⟩
      ext
      · simp [CategoryTheory.Groupoid.homMulAction_smul]
      · apply QuotientGroup.eq.mpr
        simpa using hγ
    have hfix :
        fiberTranslationMap hpY γ y0 = y0 := by
      apply (elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b).injective
      calc
        elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b
            (fiberTranslationMap hpY γ y0) =
            (associatedAction b (End b ⧸ H)).map γ
              (elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b y0) := by
                exact elementsProjectionFiberEquiv_fiberTranslationMap
                  (associatedAction b (End b ⧸ H)) hpY γ y0
        _ = q := by rw [hy0, hqfix]
        _ = elementsProjectionFiberEquiv (associatedAction b (End b ⧸ H)) b y0 := by
              rw [hy0]
    exact hmem.mpr hfix

/-- Helper for Theorem 3.6.1: the subgroup carried by the packaged orbit-cover basepoint is the
original subgroup `H`. -/
private theorem orbitCategoryAssociatedAction_packagedBasepointSubgroup_eq
    [IsConnected B] (H : O(End b)) :
    let Ycov : ConnectedCovering B := (orbitCategoryToConnectedCovering b).obj H
    let Y : GroupoidFunctorOver B := Ycov.obj
    let y0 : Y.hom.Fiber b := orbitCategoryAssociatedAction_packaged_basepoint (b := b) H
    loopSubgroupToEndSubgroup
      (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.hom y0.1).range) =
        (H : Subgroup (End b)) := by
  exact orbitCategoryAssociatedAction_basepointEndSubgroup_eq (b := b) H

/-- Helper for Theorem 3.6.1: every connected covering is isomorphic to the orbit cover attached
to the subgroup carried by a chosen point in the fiber over `b`. -/
private theorem orbit_covering_iso_of_connected_covering
    [IsConnected B]
    (X : ConnectedCovering B) (x0 : Fiber X b) :
    ∃ H : O(End b), Nonempty (((orbitCategoryToConnectedCovering b).obj H) ≅ X) := by
  let H : O(End b) := ⟨loopSubgroupToEndSubgroup (show Subgroup (b ⟶ b) from
    x0.2 ▸ (Functor.mapVertexGroup X.obj.hom x0.1).range)⟩
  let Y : ConnectedCovering B := (orbitCategoryToConnectedCovering b).obj H
  let y0 : Y.obj.hom.Fiber b := orbitCategoryAssociatedAction_packaged_basepoint (b := b) H
  have hEqEnd :
      loopSubgroupToEndSubgroup
        (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.obj.hom y0.1).range) =
      loopSubgroupToEndSubgroup
        (show Subgroup (b ⟶ b) from x0.2 ▸ (Functor.mapVertexGroup X.obj.hom x0.1).range) := by
    simpa [H] using orbitCategoryAssociatedAction_packagedBasepointSubgroup_eq (b := b) H
  have hEqSub :
      (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.obj.hom y0.1).range) =
        (show Subgroup (b ⟶ b) from x0.2 ▸ (Functor.mapVertexGroup X.obj.hom x0.1).range) := by
    exact loopSubgroupToEndSubgroup_injective hEqEnd
  have hsub :
      (Functor.mapVertexGroup Y.obj.hom y0.1).range ≤
        (x0.2.trans y0.2.symm) ▸ (Functor.mapVertexGroup X.obj.hom x0.1).range := by
    -- The chosen orbit cover is defined from the same subgroup carried by `x0`.
    refine (subgroup_transport_le_iff (b := b) y0.2 x0.2 _ _).mpr ?_
    change
      (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.obj.hom y0.1).range) ≤
        (show Subgroup (b ⟶ b) from x0.2 ▸ (Functor.mapVertexGroup X.obj.hom x0.1).range)
    exact hEqSub.le
  obtain ⟨fF, hfF, _⟩ :=
    (existsUnique_lift_iff_mapVertexGroup_range_le
      (p := X.obj.hom) (ConnectedCovering.isCovering X) y0.1
      ⟨x0.1, x0.2.trans y0.2.symm⟩).2 hsub
  let f : Y.obj ⟶ X.obj := GroupoidFunctorOver.homMk fF hfF.1
  have hfPoint : f.left.obj y0.1 = x0.1 := by
    simpa [f] using hfF.2
  have hfIso : IsIso f := by
    refine
      (groupoidFunctorOver_isIso_iff_mapVertexGroup_range_eq_large
        (b := b) (X := Y.obj) (Y := X.obj) (ConnectedCovering.isCovering Y)
        (ConnectedCovering.isCovering X) y0 x0 f hfPoint).2 ?_
    -- The orbit-cover basepoint and the chosen point in `X` carry the same subgroup.
    change
      (show Subgroup (b ⟶ b) from y0.2 ▸ (Functor.mapVertexGroup Y.obj.hom y0.1).range) =
        (show Subgroup (b ⟶ b) from x0.2 ▸ (Functor.mapVertexGroup X.obj.hom x0.1).range)
    exact hEqSub
  refine ⟨H, ⟨?_⟩⟩
  -- Lift the underlying isomorphism of covering functors into the full subcategory `Cov(B)`.
  letI := hfIso
  exact
    ObjectProperty.isoMk
      (P := fun Z : GroupoidFunctorOver B ↦ Functor.IsCovering Z.hom ∧ IsConnected Z.left)
      (X := Y) (Y := X) (e := asIso f)

/-- Helper for Theorem 3.6.1: the source-facing functor `E(-)` is essentially surjective because
Theorem 3.5.6 reconstructs every connected covering from the subgroup carried by a basepoint. -/
private theorem orbitCategoryToConnectedCovering_isEquivalence_aux [IsConnected B] :
    Functor.IsEquivalence (orbitCategoryToConnectedCovering b) := by
  let _ : (orbitCategoryToConnectedCovering b).Faithful :=
    { map_injective := by
        intro H K φ ψ hφψ
        have hAssoc :
            associatedActionHom b φ = associatedActionHom b ψ := by
          exact
            elementsFunctorOver_hom_injective
              (associatedAction b (End b ⧸ H))
              (associatedAction b (End b ⧸ K))
              (congrArg (fun h ↦ h.hom) hφψ)
        exact associatedAction_hom_injective (b := b) H K hAssoc }
  let _ : (orbitCategoryToConnectedCovering b).Full :=
    { map_surjective := by
        intro H K F
        exact orbitCategoryToConnectedCovering_map_surjective (b := b) F }
  let _ : (orbitCategoryToConnectedCovering b).EssSurj :=
    { mem_essImage := by
        intro X
        obtain ⟨x, hx⟩ := (ConnectedCovering.isCovering X).obj_surjective b
        rcases orbit_covering_iso_of_connected_covering (b := b) X ⟨x, hx⟩ with ⟨H, ⟨e⟩⟩
        exact ⟨H, ⟨e⟩⟩ }
  -- The composite orbit-cover functor is now certified by its standard faithful/full/essSurj data.
  exact
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }

/-- The category-of-elements bridge from transitive `B`-actions to connected coverings is an
equivalence. -/
-- Proof sketch: the inverse is the fiber-translation functor of a connected covering. Theorem
-- 3.5.6 and Theorem 3.5.8 identify maps of coverings with equivariant maps of the corresponding
-- fibers, while connectedness supplies the transitivity needed to reconstruct the covering from
-- its fiber action.
theorem transitiveGroupoidActionToConnectedCovering_isEquivalence [IsConnected B] :
    Functor.IsEquivalence
      (transitiveGroupoidActionToConnectedCovering :
        CategoryTheory.ObjectProperty.FullSubcategory
          (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v)) ⥤
            ConnectedCovering B) := by
  classical
  let b : B := Classical.choice (show Nonempty B from inferInstance)
  let _ :
      Functor.IsEquivalence
        (orbitCategoryToTransitiveGroupoidAction b) :=
    orbitCategoryToTransitiveGroupoidAction_isEquivalence_aux b
  let _ :
      Functor.IsEquivalence
        (((orbitCategoryToTransitiveGroupoidAction b) ⋙
            transitiveGroupoidActionToConnectedCovering :
              O(End b) ⥤ ConnectedCovering B)) :=
    orbitCategoryToConnectedCovering_isEquivalence_aux (b := b)
  -- Route correction: cancel the already-proved orbit-category equivalence on the left of the
  -- composite `orbitCategoryToConnectedCovering b`.
  simpa [orbitCategoryToConnectedCovering] using
    (Functor.isEquivalence_of_comp_left
      (orbitCategoryToTransitiveGroupoidAction b)
      (transitiveGroupoidActionToConnectedCovering :
        CategoryTheory.ObjectProperty.FullSubcategory
          (Functor.IsTransitive : CategoryTheory.ObjectProperty (B ⥤ Type v)) ⥤
            ConnectedCovering B) :
      Functor.IsEquivalence transitiveGroupoidActionToConnectedCovering)

/-- The orbit-category-to-transitive-action functor is the core bridge used in the proof of
Theorem 3.6.1. -/
-- Proof sketch: full faithfulness and essential surjectivity reduce to the quotient-stabilizer
-- description of transitive vertex-group actions on a connected groupoid.
theorem orbitCategoryToTransitiveGroupoidAction_isEquivalence [IsConnected B] :
    Functor.IsEquivalence (orbitCategoryToTransitiveGroupoidAction b) := by
  exact orbitCategoryToTransitiveGroupoidAction_isEquivalence_aux b

/-- Theorem 3.6.1: for a connected groupoid `B` with base object `b`, the source-facing functor
`E(-) : O(π(B,b)) ⥤ Cov(B)` sending `π(B,b) / H` to the associated connected covering over `B`
is an equivalence of categories, realizing conjugacy classes of subgroups by connected coverings.
-/
-- Proof sketch: factor `E(-)` through the core bridge `O(π(B,b)) ⥤` transitive `B`-actions and
-- then through the category-of-elements bridge to `Cov(B)`. The first factor is the orbit-action
-- classification, and the second identifies a transitive action with its connected covering of
-- elements.
theorem orbitCategoryToConnectedCovering_isEquivalence [IsConnected B] :
    Functor.IsEquivalence (orbitCategoryToConnectedCovering b) := by
  exact orbitCategoryToConnectedCovering_isEquivalence_aux b
