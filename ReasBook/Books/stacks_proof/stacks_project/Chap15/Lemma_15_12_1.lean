import Mathlib
import stacks_proof.stacks_project.Chap10.Lemma_10_151_4
import stacks_proof.stacks_project.Chap10.Lemma_10_151_2
import stacks_proof.stacks_project.Chap15.Lemma_15_9_5
import stacks_proof.stacks_project.Chap15.Lemma_15_10_2
import stacks_proof.stacks_project.Chap15.Lemma_15_11_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

section

/-- The category of pairs `(A, I)`, realized by a commutative ring together with an ideal. -/
structure RingPairCat where
  ring : CommRingCat.{u}
  ideal : Ideal ring

namespace RingPairCat

/-- The quotient arrow `A → A ⧸ I` attached to a ring pair `(A, I)`. -/
def quotientArrow (X : RingPairCat.{u}) : Arrow CommRingCat.{u} :=
  Arrow.mk
    (show X.ring ⟶ CommRingCat.of (X.ring ⧸ X.ideal) from
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal))

/-- The category structure on ring pairs induced from the arrow category of quotient maps. -/
instance : Category RingPairCat.{u} :=
  inferInstanceAs (Category (InducedCategory (Arrow CommRingCat.{u}) quotientArrow))

/-- The underlying ring hom of a morphism of ring pairs. -/
abbrev ringHom {X Y : RingPairCat.{u}} (f : X ⟶ Y) : X.ring →+* Y.ring :=
  f.hom.left.hom

/-- The object property cutting out the full subcategory of henselian pairs. -/
def henselianPairProperty : ObjectProperty RingPairCat.{u} :=
  fun X ↦ HenselianRing X.ring X.ideal

/-- The category of henselian pairs as the full subcategory of `RingPairCat` defined by
`HenselianRing`. -/
abbrev HenselianPairCat :=
  henselianPairProperty.FullSubcategory

/-- The inclusion functor from henselian pairs to all pairs. -/
abbrev henselianPairInclusion : HenselianPairCat.{u} ⥤ RingPairCat.{u} :=
  henselianPairProperty.ι

/-- The chosen henselization object of a ring pair, obtained from the left adjoint of the
inclusion of henselian pairs. -/
abbrev henselization (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    HenselianPairCat.{u} :=
  henselianPairInclusion.leftAdjoint.obj X

/-- The underlying ring pair of the chosen henselization of `X`. -/
abbrev henselizationPair (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    RingPairCat.{u} :=
  henselianPairInclusion.obj (henselization X)

/-- The underlying commutative ring of the chosen henselization of `X`. -/
abbrev henselizationRing (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    CommRingCat.{u} :=
  (henselizationPair X).ring

/-- The distinguished ideal of the chosen henselization of `X`. -/
abbrev henselizationIdeal (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    Ideal (henselizationRing X) :=
  (henselizationPair X).ideal

/-- The canonical ring map from a ring pair to its chosen henselization. -/
abbrev toHenselization (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    X.ring →+* henselizationRing X :=
  ((Adjunction.ofIsRightAdjoint henselianPairInclusion).unit.app X).hom.left.hom

/-- The map of chosen henselizations induced by a morphism of ring pairs. -/
abbrev henselizationMap {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    henselization X ⟶ henselization Y :=
  henselianPairInclusion.leftAdjoint.map f

/-- The underlying ring map on chosen henselization rings induced by a morphism of ring pairs. -/
abbrev henselizationRingMap {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    henselizationRing X →+* henselizationRing Y :=
  ringHom <| henselianPairInclusion.map (henselizationMap f)

/-- Naturality of the canonical map to chosen henselization on underlying rings. -/
lemma toHenselization_naturality {X Y : RingPairCat.{u}} (f : X ⟶ Y)
    [henselianPairInclusion.IsRightAdjoint] :
    (toHenselization Y).comp (ringHom f) =
      (henselizationRingMap f).comp (toHenselization X) := by
  -- Proof comment: apply naturality of the adjunction unit in `RingPairCat` and then read off the
  -- left component of the induced arrow morphism on underlying rings.
  simpa [toHenselization, henselizationRingMap, ringHom] using
    congrArg (fun k : X ⟶ henselianPairInclusion.obj (henselization Y) ↦ k.hom.left.hom)
      ((Adjunction.ofIsRightAdjoint henselianPairInclusion).unit.naturality f)

/-- The chosen henselization ring of a pair carries its canonical `X.ring`-algebra structure. -/
instance henselizationRing_algebra (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint] :
    Algebra X.ring (henselizationRing X) :=
  (toHenselization X).toAlgebra

/-- The ring pair attached to an ideal of a commutative ring. -/
abbrev pairOfIdeal {A : Type u} [CommRing A] (I : Ideal A) : RingPairCat.{u} :=
  RingPairCat.mk (CommRingCat.of A) I

/-- The chosen henselization ring of the pair `(A, I)` carries its canonical `A`-algebra
structure via the unit map of the pair-henselization adjunction. -/
instance pairOfIdeal_henselizationRing_algebra {A : Type u} [CommRing A] (I : Ideal A)
    [henselianPairInclusion.IsRightAdjoint] :
    Algebra A (henselizationRing (pairOfIdeal I)) :=
  (toHenselization (pairOfIdeal I)).toAlgebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (J : Ideal B)

-- Proof sketch: the quotient map `A ⧸ I → B ⧸ J` is induced by the universal property of the
-- quotient because `I` maps into `J`; the defining square then commutes by construction.
/-- The quotient maps associated to a morphism of pairs form a commutative square in
`CommRingCat`. -/
lemma pairOfIdeal_hom_square (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    CommRingCat.ofHom (algebraMap A B) ≫
        CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ) := by
  -- Proof comment: both composites are the quotient map induced by `algebraMap A B`; evaluate on a
  -- representative and use the defining formula for `Ideal.quotientMap`.
  ext a
  rfl

/-- Helper for Lemma 15.12.1: any ring homomorphism carrying `I` into `J` induces the canonical
commutative square on quotients. -/
lemma pairOfIdeal_hom_square_of_ringHom {A B : Type u} [CommRing A] [CommRing B]
    (I : Ideal A) (J : Ideal B) (f : A →+* B) (hIJ : I ≤ Ideal.comap f J) :
    CommRingCat.ofHom f ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) =
      CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
        CommRingCat.ofHom (Ideal.quotientMap J f hIJ) := by
  -- Proof comment: both composites are the quotient map induced by `f`, so they agree on each
  -- representative.
  ext a
  rfl

/-- The map of pairs induced by an `A`-algebra map carrying `I` into `J`. -/
abbrev pairOfIdealMap (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    pairOfIdeal I ⟶ pairOfIdeal J :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ))
      (pairOfIdeal_hom_square I J hIJ)

/-- Helper for Lemma 15.12.1: a morphism of ring pairs is determined by its underlying ring
homomorphism. -/
lemma hom_ext {X Y : RingPairCat.{u}} {f g : X ⟶ Y}
    (hfg : ringHom f = ringHom g) :
    f = g := by
  -- Proof comment: morphisms in `RingPairCat` are arrow morphisms between quotient arrows, so it
  -- suffices to identify both components of the underlying square.
  apply InducedCategory.hom_ext
  refine Arrow.hom_ext _ _ ?_ ?_
  · -- Proof comment: the left component is exactly the underlying ring map.
    exact CommRingCat.hom_ext hfg
  · -- Proof comment: the right component is forced by commutativity with the quotient maps.
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext x
    change f.hom.right.hom ((Ideal.Quotient.mk X.ideal) x) =
      g.hom.right.hom ((Ideal.Quotient.mk X.ideal) x)
    have hwf' :
        f.hom.right.hom ((Ideal.Quotient.mk X.ideal) x) =
          (Ideal.Quotient.mk Y.ideal) ((ringHom f) x) := by
      simpa [ringHom, quotientArrow] using
        (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp f.hom.w) x).symm
    have hwg' :
        g.hom.right.hom ((Ideal.Quotient.mk X.ideal) x) =
          (Ideal.Quotient.mk Y.ideal) ((ringHom g) x) := by
      simpa [ringHom, quotientArrow] using
        (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp g.hom.w) x).symm
    exact hwf'.trans <| by simpa [hfg] using hwg'.symm

/-- Helper for Lemma 15.12.1: every morphism of ring pairs carries the distinguished ideal of the
source into the distinguished ideal of the target. -/
lemma ringHom_ideal_le_comap {X Y : RingPairCat.{u}} (f : X ⟶ Y) :
    X.ideal ≤ Ideal.comap (ringHom f) Y.ideal := by
  -- Proof comment: the quotient square attached to `f` sends every source-ideal element to zero in
  -- the target quotient, which exactly means that its image lies in the target ideal.
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  calc
    Ideal.Quotient.mk Y.ideal ((ringHom f) x) =
        f.hom.right.hom (Ideal.Quotient.mk X.ideal x) := by
          simpa [ringHom, quotientArrow] using
            (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp f.hom.w) x).symm
    _ = 0 := by
          simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]

-- Proof sketch: for a pair `(A, I)`, take the filtered colimit of the category of étale
-- neighborhoods of `(A, I)` inducing an isomorphism modulo `I`, as in the source.
-- Route correction: the source-faithful argument proves henselianity of the colimit pair via the
-- étale lifting criterion from Lemma `15.11.6`; the earlier placeholder reference to
-- `15.11.13` is not the right closure statement for this construction.
/-- Helper for Lemma 15.12.1: a packaged universal henselian pair over `X`. -/
structure PairHenselizationData (X : RingPairCat.{u}) where
  obj : HenselianPairCat.{u}
  unit : X ⟶ henselianPairInclusion.obj obj
  universal :
    ∀ Z : HenselianPairCat.{u},
      Function.Bijective fun f : obj ⟶ Z ↦ unit ≫ henselianPairInclusion.map f

/-- Helper for Lemma 15.12.1: a universal henselian pair over `X` puts `X` in the domain of
definition of the partial left adjoint to the inclusion. -/
lemma PairHenselizationData.leftAdjointObjIsDefined {X : RingPairCat.{u}}
    (data : PairHenselizationData X) :
    henselianPairInclusion.leftAdjointObjIsDefined X := by
  classical
  rw [Functor.leftAdjointObjIsDefined_iff]
  refine ⟨data.obj, ⟨?_⟩⟩
  refine
    { homEquiv := ?_
      homEquiv_comp := ?_ }
  · intro Z
    -- Proof comment: the universal arrow `data.unit` provides the corepresenting bijection on
    -- morphisms into any henselian target `Z`.
    refine
      { toFun := fun f ↦ data.unit ≫ henselianPairInclusion.map f
        invFun := fun g ↦ Classical.choose ((data.universal Z).surjective g)
        left_inv := ?_
        right_inv := ?_ }
    · intro f
      -- Proof comment: injectivity of the universal map recovers the original morphism.
      exact (data.universal Z).injective <|
        Classical.choose_spec ((data.universal Z).surjective
          (data.unit ≫ henselianPairInclusion.map f))
    · intro g
      -- Proof comment: surjectivity of the universal map gives the desired preimage.
      exact Classical.choose_spec ((data.universal Z).surjective g)
  · intro Y Y' g f
    -- Proof comment: naturality is just reassociation in the ambient category of pairs.
    change (fun f' : data.obj ⟶ Y' => data.unit ≫ henselianPairInclusion.map f') (f ≫ g) =
      (henselianPairInclusion ⋙ coyoneda.obj (Opposite.op X)).map g
        ((fun f' : data.obj ⟶ Y => data.unit ≫ henselianPairInclusion.map f') f)
    simp [Category.assoc]

/-- Helper for Lemma 15.12.1: an étale neighborhood stage of a ring pair `(A, I)` is an étale
`A`-algebra whose closed fiber over `A / I` is unchanged. -/
structure EtaleNeighborhood (X : RingPairCat.{u}) where
  carrier : Type u
  [commRing : CommRing carrier]
  [algebra : Algebra X.ring carrier]
  [etale : Algebra.Etale X.ring carrier]
  closedFiberBijective :
    Function.Bijective
      (Ideal.quotientMap
        (Ideal.map (algebraMap X.ring carrier) X.ideal)
        (algebraMap X.ring carrier)
        Ideal.le_comap_map)

attribute [instance] EtaleNeighborhood.commRing
attribute [instance] EtaleNeighborhood.algebra
attribute [instance] EtaleNeighborhood.etale

/-- Helper for Lemma 15.12.1: the distinguished ideal on an étale neighborhood stage is the image
of the source ideal. -/
abbrev EtaleNeighborhood.stageIdeal {X : RingPairCat.{u}} (Y : EtaleNeighborhood X) :
    Ideal Y.carrier :=
  Ideal.map (algebraMap X.ring Y.carrier) X.ideal

/-- Helper for Lemma 15.12.1: each étale neighborhood stage determines a ring pair. -/
abbrev EtaleNeighborhood.toPair {X : RingPairCat.{u}} (Y : EtaleNeighborhood X) :
    RingPairCat.{u} :=
  pairOfIdeal Y.stageIdeal

/-- Helper for Lemma 15.12.1: the source pair maps canonically to every étale neighborhood stage. -/
abbrev EtaleNeighborhood.homFromSource {X : RingPairCat.{u}} (Y : EtaleNeighborhood X) :
    X ⟶ Y.toPair :=
  pairOfIdealMap X.ideal Y.stageIdeal Ideal.le_comap_map

/-- Helper for Lemma 15.12.1: morphisms of étale neighborhoods are `X.ring`-algebra maps between
their stage rings. -/
instance EtaleNeighborhood.instCategory (X : RingPairCat.{u}) :
    Category (EtaleNeighborhood X) where
  Hom Y₁ Y₂ := Y₁.carrier →ₐ[X.ring] Y₂.carrier
  id Y := AlgHom.id X.ring Y.carrier
  comp f g := g.comp f
  id_comp := by
    intro Y₁ Y₂ φ
    -- Proof comment: composition with the identity algebra map fixes every element.
    ext y
    rfl
  comp_id := by
    intro Y₁ Y₂ φ
    -- Proof comment: postcomposing with the identity algebra map likewise leaves the map
    -- unchanged.
    ext y
    rfl
  assoc := by
    intro Y₁ Y₂ Y₃ Y₄ φ ψ χ
    -- Proof comment: algebra-map composition is associative on the nose.
    ext y
    rfl

/-- Helper for Lemma 15.12.1: an algebra map between étale neighborhood stages carries the source
stage ideal into the target stage ideal. -/
lemma EtaleNeighborhood.stageIdeal_le_comap_of_hom {X : RingPairCat.{u}}
    {Y₁ Y₂ : EtaleNeighborhood X} (φ : Y₁ ⟶ Y₂) :
    Y₁.stageIdeal ≤ Ideal.comap φ.toRingHom Y₂.stageIdeal := by
  -- Proof comment: after rewriting the source ideal as an image ideal, the required containment is
  -- exactly functoriality of `Ideal.comap` together with `φ` commuting with the `X.ring`-algebra
  -- structures.
  rw [EtaleNeighborhood.stageIdeal, EtaleNeighborhood.stageIdeal, Ideal.map_le_iff_le_comap]
  have hcomp :
      φ.toRingHom.comp (algebraMap X.ring Y₁.carrier) =
        algebraMap X.ring Y₂.carrier := by
    ext x
    exact φ.commutes x
  simpa [Ideal.comap_comap, hcomp] using
    (Ideal.le_comap_map :
      X.ideal ≤
        Ideal.comap (algebraMap X.ring Y₂.carrier)
          (Ideal.map (algebraMap X.ring Y₂.carrier) X.ideal))

/-- Helper for Lemma 15.12.1: a morphism of étale neighborhoods induces the corresponding morphism
of ring pairs. -/
abbrev EtaleNeighborhood.toPairMap {X : RingPairCat.{u}} {Y₁ Y₂ : EtaleNeighborhood X}
    (φ : Y₁ ⟶ Y₂) :
    Y₁.toPair ⟶ Y₂.toPair :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom φ.toRingHom)
      (CommRingCat.ofHom <|
        Ideal.quotientMap
          Y₂.stageIdeal
          φ.toRingHom
          (EtaleNeighborhood.stageIdeal_le_comap_of_hom φ))
      (pairOfIdeal_hom_square_of_ringHom
        Y₁.stageIdeal Y₂.stageIdeal φ.toRingHom
        (EtaleNeighborhood.stageIdeal_le_comap_of_hom φ))

/-- Helper for Lemma 15.12.1: the canonical source map into an étale neighborhood stage is natural
with respect to neighborhood morphisms. -/
lemma EtaleNeighborhood.homFromSource_naturality {X : RingPairCat.{u}}
    {Y₁ Y₂ : EtaleNeighborhood X} (φ : Y₁ ⟶ Y₂) :
    Y₁.homFromSource ≫ Y₁.toPairMap φ = Y₂.homFromSource := by
  -- Proof comment: both pair morphisms have the same underlying ring map
  -- `X.ring → Y₂.carrier`, namely the structural algebra map.
  apply hom_ext
  ext x
  exact φ.commutes x

/-- Helper for Lemma 15.12.1: the étale neighborhoods of `X` form the source diagram used in the
filtered-colimit construction of the henselization pair. -/
abbrev EtaleNeighborhood.toRingPairFunctor (X : RingPairCat.{u}) :
    EtaleNeighborhood X ⥤ RingPairCat.{u} where
  obj Y := Y.toPair
  map φ := EtaleNeighborhood.toPairMap φ
  map_id := by
    intro Y
    -- Proof comment: the induced pair map of the identity algebra map is the identity pair map.
    apply hom_ext
    rfl
  map_comp := by
    intro Y₁ Y₂ Y₃ φ ψ
    -- Proof comment: the induced pair maps compose by composition of the underlying algebra maps.
    apply hom_ext
    rfl

/-- Helper for Lemma 15.12.1: for the identity neighborhood, the closed-fiber comparison map is
the canonical quotient equivalence. -/
lemma etaleNeighborhood_self_closedFiber_bijective (X : RingPairCat.{u}) :
    Function.Bijective
      (Ideal.quotientMap
        (Ideal.map (algebraMap X.ring X.ring) X.ideal)
        (algebraMap X.ring X.ring)
        Ideal.le_comap_map) := by
  let hmap : X.ideal = Ideal.map (algebraMap X.ring X.ring) X.ideal := by
    -- Proof comment: the source ideal is unchanged by the identity algebra map.
    simpa using (Ideal.map_id X.ideal).symm
  let e :
      (X.ring ⧸ X.ideal) ≃ₐ[X.ring]
        (X.ring ⧸ Ideal.map (algebraMap X.ring X.ring) X.ideal) :=
    Ideal.quotientEquivAlgOfEq X.ring hmap
  have he :
      e.toRingHom =
        Ideal.quotientMap
          (Ideal.map (algebraMap X.ring X.ring) X.ideal)
          (algebraMap X.ring X.ring)
          Ideal.le_comap_map := by
    -- Proof comment: both maps are induced by the identity map on representatives.
    apply Ideal.Quotient.ringHom_ext
    ext a
    change
      (Ideal.quotientEquivAlgOfEq X.ring hmap) (Ideal.Quotient.mk X.ideal a) =
        Ideal.quotientMap
          (Ideal.map (algebraMap X.ring X.ring) X.ideal)
          (algebraMap X.ring X.ring)
          Ideal.le_comap_map
          (Ideal.Quotient.mk X.ideal a)
    rw [Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientMap_mk]
    simp
  simpa [he] using e.bijective

/-- Helper for Lemma 15.12.1: the identity algebra of a ring is étale, so the source pair itself
is an étale neighborhood stage. -/
lemma etaleNeighborhood_self_etale (X : RingPairCat.{u}) :
    Algebra.Etale X.ring X.ring := by
  -- Proof comment: the identity ring hom is bijective, hence étale.
  exact RingHom.Etale.of_bijective (by simpa using (RingEquiv.refl X.ring).bijective)

/-- Helper for Lemma 15.12.1: the identity map on `X` is the initial étale neighborhood stage used
to start the filtered system from the source proof. -/
abbrev EtaleNeighborhood.self (X : RingPairCat.{u}) : EtaleNeighborhood X :=
  { carrier := X.ring
    commRing := inferInstance
    algebra := (algebraMap X.ring X.ring).toAlgebra
    etale := etaleNeighborhood_self_etale X
    closedFiberBijective := etaleNeighborhood_self_closedFiber_bijective X }

attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Helper for Lemma 15.12.1: the closed-fiber comparison map of a neighborhood stage is an
algebra equivalence onto the stage quotient. -/
noncomputable def EtaleNeighborhood.closedFiberAlgEquiv {X : RingPairCat.{u}}
    (Y : EtaleNeighborhood X) :
    (X.ring ⧸ X.ideal) ≃ₐ[X.ring ⧸ X.ideal] (Y.carrier ⧸ Y.stageIdeal) :=
  let e : (X.ring ⧸ X.ideal) ≃+* (Y.carrier ⧸ Y.stageIdeal) :=
    RingEquiv.ofBijective
      (algebraMap (X.ring ⧸ X.ideal) (Y.carrier ⧸ Y.stageIdeal))
      (by
        -- Proof comment: the quotient-algebra structure map is exactly the closed-fiber
        -- comparison stored in the neighborhood data.
        simpa using Y.closedFiberBijective)
  AlgEquiv.ofRingEquiv (f := e) fun x ↦ rfl

/-- Helper for Lemma 15.12.1: the tensor product of two étale neighborhood stages is again étale
over the source ring. -/
lemma EtaleNeighborhood.tensor_upper_bound_etale {X : RingPairCat.{u}}
    (Y₁ Y₂ : EtaleNeighborhood X) :
    Algebra.Etale X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier) := by
  -- Proof comment: base change the étale algebra `Y₂` along `X.ring → Y₁`, then compose with the
  -- étale structural map `X.ring → Y₁`.
  let _ : Algebra.Etale Y₁.carrier (Y₁.carrier ⊗[X.ring] Y₂.carrier) :=
    Algebra.Etale.baseChange X.ring Y₂.carrier Y₁.carrier
  exact Algebra.Etale.comp X.ring Y₁.carrier (Y₁.carrier ⊗[X.ring] Y₂.carrier)

/-- Helper for Lemma 15.12.1: the closed fiber of `Y₁ ⊗[X] Y₂` normalizes to the tensor product
of the first closed fiber with the second stage. -/
private noncomputable def EtaleNeighborhood.tensor_closedFiber_normalization
    {X : RingPairCat.{u}} (Y₁ Y₂ : EtaleNeighborhood X) :
    ((Y₁.carrier ⊗[X.ring] Y₂.carrier) ⧸
        Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal) ≃ₐ[X.ring ⧸ X.ideal]
      ((Y₁.carrier ⧸ Y₁.stageIdeal) ⊗[X.ring] Y₂.carrier) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (Y₁.carrier ⊗[X.ring] Y₂.carrier) X.ideal).trans <|
    (Algebra.TensorProduct.assoc
      X.ring X.ring (X.ring ⧸ X.ideal) (X.ring ⧸ X.ideal) Y₁.carrier Y₂.carrier).symm.trans <|
      Algebra.TensorProduct.congr
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y₁.carrier X.ideal).symm
        (AlgEquiv.refl : Y₂.carrier ≃ₐ[X.ring] Y₂.carrier)

/-- Helper for Lemma 15.12.1: after identifying the first closed fiber with `X / I`, the tensor
stage closed fiber is canonically the closed fiber of the right stage. -/
private noncomputable def EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient
    {X : RingPairCat.{u}} (Y₁ Y₂ : EtaleNeighborhood X) :
    ((Y₁.carrier ⊗[X.ring] Y₂.carrier) ⧸
        Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal) ≃ₐ[X.ring ⧸ X.ideal]
      (Y₂.carrier ⧸ Y₂.stageIdeal) :=
  (EtaleNeighborhood.tensor_closedFiber_normalization Y₁ Y₂).trans <|
    (Algebra.TensorProduct.congr
      (EtaleNeighborhood.closedFiberAlgEquiv Y₁).symm
      (AlgEquiv.refl : Y₂.carrier ≃ₐ[X.ring] Y₂.carrier)).trans <|
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y₂.carrier X.ideal).symm

/-- Helper for Lemma 15.12.1: the canonical closed-fiber comparison of the tensor stage becomes
the right-stage closed-fiber map under the quotient normalizations. -/
private theorem EtaleNeighborhood.closedFiberAlgEquiv_symm_mk
    {X : RingPairCat.{u}} (Y : EtaleNeighborhood X) (a : X.ring) :
    (EtaleNeighborhood.closedFiberAlgEquiv Y).symm
      (Ideal.Quotient.mk Y.stageIdeal (algebraMap X.ring Y.carrier a)) =
      Ideal.Quotient.mk X.ideal a := by
  -- Proof comment: this is the inverse computation for the closed-fiber equivalence on source
  -- generators.
  apply (EtaleNeighborhood.closedFiberAlgEquiv Y).injective
  simp [EtaleNeighborhood.closedFiberAlgEquiv]

/-- Helper for Lemma 15.12.1: the inverse quotient-tensor comparison on the right stage sends the
pure tensor coming from `a` back to the quotient class of `a`. -/
private theorem EtaleNeighborhood.rightStageQuotient_symm_tmul_one
    {X : RingPairCat.{u}} (Y : EtaleNeighborhood X) (a : X.ring) :
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y.carrier X.ideal).symm
      ((Ideal.Quotient.mk X.ideal a) ⊗ₜ[X.ring] (1 : Y.carrier)) =
      Ideal.Quotient.mk Y.stageIdeal (algebraMap X.ring Y.carrier a) := by
  -- Proof comment: this is the inverse pure-tensor computation on the right-stage quotient.
  apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y.carrier X.ideal).injective
  rw [AlgEquiv.apply_symm_apply]
  calc
    (Ideal.Quotient.mk X.ideal a) ⊗ₜ[X.ring] (1 : Y.carrier) =
        (1 : X.ring ⧸ X.ideal) ⊗ₜ[X.ring] (algebraMap X.ring Y.carrier a) := by
          simpa using
            (Algebra.TensorProduct.tmul_one_eq_one_tmul
              (R := X.ring) (A := X.ring ⧸ X.ideal) (B := Y.carrier) a)
    _ =
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y.carrier X.ideal)
          ((algebraMap X.ring (Y.carrier ⧸ Y.stageIdeal)) a) := by
            simpa using
              (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk
                (A := X.ring) (B := Y.carrier) (I := X.ideal)
                (algebraMap X.ring Y.carrier a)).symm

/-- Helper for Lemma 15.12.1: the canonical closed-fiber comparison of the tensor stage becomes
the right-stage closed-fiber map under the quotient normalizations. -/
private theorem EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient_mk
    {X : RingPairCat.{u}} (Y₁ Y₂ : EtaleNeighborhood X) (a : X.ring) :
    EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient Y₁ Y₂
      (Ideal.Quotient.mk
        (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
        (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier) a)) =
      Ideal.Quotient.mk Y₂.stageIdeal (algebraMap X.ring Y₂.carrier a) := by
  -- Proof comment: this computes the tensor closed-fiber comparison on generators from `X.ring`.
  have h_tensor :
      algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier) a =
        (algebraMap X.ring Y₁.carrier a) ⊗ₜ[X.ring] (1 : Y₂.carrier) := by
    rfl
  simp only [EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient,
    EtaleNeighborhood.tensor_closedFiber_normalization, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, h_tensor, Algebra.TensorProduct.map_tmul,
    Algebra.TensorProduct.assoc_symm_tmul,
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  have hstage :
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y₁.carrier X.ideal).symm
        (1 ⊗ₜ[X.ring] (algebraMap X.ring Y₁.carrier a)) =
        Ideal.Quotient.mk Y₁.stageIdeal (algebraMap X.ring Y₁.carrier a) := by
    -- Proof comment: invert the canonical quotient-tensor computation for the left stage.
    apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Y₁.carrier X.ideal).injective
    rw [AlgEquiv.apply_symm_apply]
    simpa using
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk
        (A := X.ring) (B := Y₁.carrier) (I := X.ideal)
        (algebraMap X.ring Y₁.carrier a))
  simpa [hstage, EtaleNeighborhood.closedFiberAlgEquiv_symm_mk] using
    EtaleNeighborhood.rightStageQuotient_symm_tmul_one (Y := Y₂) a

/-- Helper for Lemma 15.12.1: the canonical closed-fiber comparison of the tensor stage becomes
the right-stage closed-fiber map under the quotient normalizations. -/
private theorem EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient_comp
    {X : RingPairCat.{u}} (Y₁ Y₂ : EtaleNeighborhood X) :
    (EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient Y₁ Y₂).toRingHom.comp
      (Ideal.quotientMap
        (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
        (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier))
        Ideal.le_comap_map) =
    Ideal.quotientMap Y₂.stageIdeal (algebraMap X.ring Y₂.carrier) Ideal.le_comap_map := by
  -- Proof comment: pointwise on representatives, this is the generator computation above.
  ext a
  simpa [RingHom.comp_apply, Ideal.quotientMap_mk] using
    EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient_mk Y₁ Y₂ a

/-- Helper for Lemma 15.12.1: the tensor product of two neighborhood stages again has unchanged
closed fiber over the source pair. -/
lemma EtaleNeighborhood.tensor_upper_bound_closedFiber_bijective {X : RingPairCat.{u}}
    (Y₁ Y₂ : EtaleNeighborhood X) :
    Function.Bijective
      (Ideal.quotientMap
        (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
        (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier))
        Ideal.le_comap_map) := by
  -- Proof comment: this follows by transporting the right-stage quotient bijectivity through the
  -- tensor closed-fiber equivalence.
  let e := EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient Y₁ Y₂
  have hcomp := EtaleNeighborhood.tensor_closedFiber_to_rightStageQuotient_comp Y₁ Y₂
  refine ⟨?_, ?_⟩
  · intro a b hab
    -- Proof comment: after applying `e`, the equality lands in the right-stage quotient.
    have hleft : e
        ((Ideal.quotientMap
          (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
          (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier))
          Ideal.le_comap_map) a) =
        e ((Ideal.quotientMap
          (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
          (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier))
          Ideal.le_comap_map) b) := congrArg e hab
    let g :
        (X.ring ⧸ X.ideal) →+* (Y₂.carrier ⧸ Y₂.stageIdeal) :=
      Ideal.quotientMap Y₂.stageIdeal (algebraMap X.ring Y₂.carrier) Ideal.le_comap_map
    have hcomp_a :
        e
          ((Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
            (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier))
            Ideal.le_comap_map) a) =
          g a := by
      simpa [g, RingHom.comp_apply] using
        congrArg (fun k : (X.ring ⧸ X.ideal) →+* (Y₂.carrier ⧸ Y₂.stageIdeal) ↦ k a) hcomp
    have hcomp_b :
        e
          ((Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
            (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier))
            Ideal.le_comap_map) b) =
          g b := by
      simpa [g, RingHom.comp_apply] using
        congrArg (fun k : (X.ring ⧸ X.ideal) →+* (Y₂.carrier ⧸ Y₂.stageIdeal) ↦ k b) hcomp
    have hright :
        g a = g b := hcomp_a.symm.trans <| hleft.trans hcomp_b
    exact Y₂.closedFiberBijective.1 hright
  · intro y
    -- Proof comment: surjectivity is pulled back from the right-stage quotient through `e`.
    rcases Y₂.closedFiberBijective.2 (e y) with ⟨x, hx⟩
    refine ⟨x, e.injective ?_⟩
    let g :
        (X.ring ⧸ X.ideal) →+* (Y₂.carrier ⧸ Y₂.stageIdeal) :=
      Ideal.quotientMap Y₂.stageIdeal (algebraMap X.ring Y₂.carrier) Ideal.le_comap_map
    have hcomp_x :
        e
          ((Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier)) X.ideal)
            (algebraMap X.ring (Y₁.carrier ⊗[X.ring] Y₂.carrier))
            Ideal.le_comap_map) x) =
          g x := by
      simpa [g, RingHom.comp_apply] using
        congrArg (fun k : (X.ring ⧸ X.ideal) →+* (Y₂.carrier ⧸ Y₂.stageIdeal) ↦ k x) hcomp
    exact hcomp_x.trans hx

/-- Helper for Lemma 15.12.1: two étale neighborhood stages admit the textbook tensor-product
common successor. -/
abbrev EtaleNeighborhood.tensor_upper_bound {X : RingPairCat.{u}}
    (Y₁ Y₂ : EtaleNeighborhood X) :
    EtaleNeighborhood X :=
  { carrier := Y₁.carrier ⊗[X.ring] Y₂.carrier
    commRing := inferInstance
    algebra := inferInstance
    etale := EtaleNeighborhood.tensor_upper_bound_etale Y₁ Y₂
    closedFiberBijective := EtaleNeighborhood.tensor_upper_bound_closedFiber_bijective Y₁ Y₂ }

/-- Helper for Lemma 15.12.1: the left tensor inclusion exhibits the first stage as mapping into
the tensor-product common successor. -/
abbrev EtaleNeighborhood.to_tensor_upper_bound_left {X : RingPairCat.{u}}
    (Y₁ Y₂ : EtaleNeighborhood X) :
    Y₁ ⟶ Y₁.tensor_upper_bound Y₂ :=
  Algebra.TensorProduct.includeLeft

/-- Helper for Lemma 15.12.1: the right tensor inclusion exhibits the second stage as mapping into
the tensor-product common successor. -/
abbrev EtaleNeighborhood.to_tensor_upper_bound_right {X : RingPairCat.{u}}
    (Y₁ Y₂ : EtaleNeighborhood X) :
    Y₂ ⟶ Y₁.tensor_upper_bound Y₂ :=
  Algebra.TensorProduct.includeRight

/-- Helper for Lemma 15.12.1: in a henselian pair, an idempotent whose image in the quotient
vanishes must already be zero. -/
private theorem idempotent_eq_zero_of_quotient_eq_zero_of_henselianRing
    {R : Type u} [CommRing R] {J : Ideal R} [HenselianRing R J] {e : R}
    (he : IsIdempotentElem e) (hzero : Ideal.Quotient.mk J e = 0) :
    e = 0 := by
  let q :
      {x : R // IsIdempotentElem x} →
        {x : R ⧸ J // IsIdempotentElem x} :=
    (Ideal.Quotient.mk J).idempotentMap
  have hbij : Function.Bijective q :=
    Ideal.quotientMk_bijective_idempotentMap_of_henselianRing (A := R) J
  have hq :
      q ⟨e, he⟩ = ⟨0, by simpa [IsIdempotentElem]⟩ := by
    -- Proof comment: the quotient hypothesis identifies the idempotent class of `e` with the
    -- zero idempotent downstairs.
    apply Subtype.ext
    simpa using hzero
  have hEq :
      (⟨e, he⟩ : {x : R // IsIdempotentElem x}) =
        ⟨0, by simpa [IsIdempotentElem]⟩ := by
    exact hbij.1 (show q ⟨e, he⟩ = q ⟨0, by simpa [IsIdempotentElem]⟩ from hq)
  exact congrArg Subtype.val hEq

/-- Helper for Lemma 15.12.1: two maps from an étale algebra into a henselian target are equal
once their reductions modulo the henselian ideal agree. -/
private theorem eq_of_equal_reductions_between_etale_algebras_of_henselianRing
    {A : Type u} {B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.Etale A B]
    {J : Ideal C} [HenselianRing C J] {f g : B →ₐ[A] C}
    (hfg :
      (Ideal.Quotient.mkₐ A J).comp f =
        (Ideal.Quotient.mkₐ A J).comp g) :
    f = g := by
  let _ : Algebra.Unramified A B := inferInstance
  let _ : Algebra (B ⊗[A] B) B := (Algebra.TensorProduct.lmul' A).toRingHom.toAlgebra
  obtain ⟨e, he, hloc⟩ :=
    exists_idempotent_tensorProduct_self_isLocalization_of_unramified (R := A) (S := B)
  have hker :
      RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom =
        Ideal.span ({1 - e} : Set (B ⊗[A] B)) := by
    -- Proof comment: the unramified tensor square has diagonal kernel generated by the
    -- complementary idempotent `1 - e`.
    simpa using
      Algebra.descended_localization_kernel_eq_span_one_sub
        (R := B ⊗[A] B) (S := B) he hloc
  let q : C →ₐ[A] C ⧸ J := Ideal.Quotient.mkₐ A J
  let τ : B ⊗[A] B →ₐ[A] C := Algebra.TensorProduct.productMap f g
  have hcomp :
      q.comp τ = ((q.comp f).comp (Algebra.TensorProduct.lmul' A)) := by
    ext x y
    have hy :
        q (g y) = q (f y) := by
      simpa using congrArg (fun φ : B →ₐ[A] C ⧸ J ↦ φ y) hfg
    -- Proof comment: modulo `J`, the product map factors through multiplication because the two
    -- reductions coincide.
    calc
      q (τ (x ⊗ₜ[A] y)) = q (f x * g y) := by
        simp [τ, Algebra.TensorProduct.productMap_apply_tmul]
      _ = q (f x) * q (g y) := by
        simp
      _ = q (f x) * q (f y) := by
        rw [hy]
      _ = q (f (x * y)) := by
        simp
      _ = (((q.comp f).comp (Algebra.TensorProduct.lmul' A)) (x ⊗ₜ[A] y)) := by
        simp [Algebra.TensorProduct.lmul'_apply_tmul]
  have hτ_one_sub_mem : τ (1 - e) ∈ J := by
    have hkermem :
        (1 - e : B ⊗[A] B) ∈ RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom := by
      rw [hker]
      exact Ideal.subset_span (by simp)
    have hzero : q (τ (1 - e)) = 0 := by
      calc
        q (τ (1 - e)) = (q.comp τ) (1 - e) := rfl
        _ = (((q.comp f).comp (Algebra.TensorProduct.lmul' A)) (1 - e)) := by
          simpa using congrArg (fun φ : B ⊗[A] B →ₐ[A] C ⧸ J ↦ φ (1 - e)) hcomp
        _ = 0 := by
          rw [RingHom.mem_ker.mp hkermem]
          simp
    exact Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have hτ_one_sub_zero : τ (1 - e) = 0 := by
    -- Proof comment: `τ (1 - e)` is idempotent and vanishes modulo `J`, so henselianity forces
    -- it to vanish already in `C`.
    refine idempotent_eq_zero_of_quotient_eq_zero_of_henselianRing
      (J := J) (he := he.one_sub.map τ) ?_
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hτ_one_sub_mem
  ext b
  have hdiff_mem :
      (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b : B ⊗[A] B) ∈
        RingHom.ker (Algebra.TensorProduct.lmul' A).toRingHom := by
    -- Proof comment: every diagonal tensor difference lies in the multiplication kernel.
    apply RingHom.mem_ker.mpr
    simp [Algebra.TensorProduct.lmul'_apply_tmul]
  have hspan :
      (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b : B ⊗[A] B) ∈
        Ideal.span ({1 - e} : Set (B ⊗[A] B)) := by
    rwa [hker] at hdiff_mem
  rw [Ideal.mem_span_singleton] at hspan
  rcases hspan with ⟨r, hr⟩
  have hτdiff : τ (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b) = 0 := by
    -- Proof comment: once `τ (1 - e)` vanishes, the kernel description kills each diagonal
    -- difference after factoring through the generator `1 - e`.
    calc
      τ (b ⊗ₜ[A] (1 : B) - 1 ⊗ₜ[A] b) = τ ((1 - e) * r) := by
        rw [hr]
      _ = τ (1 - e) * τ r := by
        simp
      _ = 0 := by
        simp [hτ_one_sub_zero]
  simpa [τ, Algebra.TensorProduct.productMap_apply_tmul] using hτdiff

/-- Helper for Lemma 15.12.1: a morphism from an étale neighborhood stage into a henselian target
is uniquely determined by its restriction to the source pair. -/
lemma EtaleNeighborhood.hom_ext_into_henselian_target {X : RingPairCat.{u}}
    (Y : EtaleNeighborhood X) {Z : HenselianPairCat.{u}}
    {τ₁ τ₂ : Y.toPair ⟶ henselianPairInclusion.obj Z}
    (hτ : Y.homFromSource ≫ τ₁ = Y.homFromSource ≫ τ₂) :
    τ₁ = τ₂ := by
  let _ : HenselianRing Z.1.ring Z.1.ideal := Z.2
  let AtoZ : X.ring →+* Z.1.ring := ringHom (Y.homFromSource ≫ τ₁)
  let _ : Algebra X.ring Z.1.ring := AtoZ.toAlgebra
  let f₁ : Y.carrier →ₐ[X.ring] Z.1.ring :=
    { toRingHom := ringHom τ₁
      commutes' := by
        -- Proof comment: the target `X.ring`-algebra structure is chosen from the common
        -- restriction along `Y.homFromSource`, so the first map is algebra-linear by definition.
        intro a
        rfl }
  let f₂ : Y.carrier →ₐ[X.ring] Z.1.ring :=
    { toRingHom := ringHom τ₂
      commutes' := by
        -- Proof comment: the restriction hypothesis identifies the two composites from `X.ring`
        -- to the target, so the second map is algebra-linear for the same chosen structure.
        intro a
        exact RingHom.congr_fun (congrArg ringHom hτ) a }
  have hclosedFiberComp :
      τ₁.hom.right.hom.comp
          (Ideal.quotientMap Y.stageIdeal (algebraMap X.ring Y.carrier) Ideal.le_comap_map) =
        τ₂.hom.right.hom.comp
          (Ideal.quotientMap Y.stageIdeal (algebraMap X.ring Y.carrier) Ideal.le_comap_map) := by
    -- Proof comment: equality on the source pair already gives equality on the closed-fiber maps
    -- after composing with the canonical source-to-stage quotient comparison.
    simpa [EtaleNeighborhood.homFromSource, EtaleNeighborhood.toPair, pairOfIdealMap,
      quotientArrow] using
      congrArg (fun f : X ⟶ henselianPairInclusion.obj Z ↦ f.hom.right.hom) hτ
  have hright :
      τ₁.hom.right.hom = τ₂.hom.right.hom := by
    -- Proof comment: the closed-fiber comparison of a neighborhood stage is bijective, so
    -- equality after precomposition with it already determines the quotient map.
    ext y
    rcases Y.closedFiberBijective.2 y with ⟨x, rfl⟩
    exact congrArg
      (fun φ : (X.ring ⧸ X.ideal) →+* (Z.1.ring ⧸ Z.1.ideal) ↦ φ x)
      hclosedFiberComp
  have hreductions :
      (Ideal.Quotient.mk Z.1.ideal).comp (ringHom τ₁) =
        (Ideal.Quotient.mk Z.1.ideal).comp (ringHom τ₂) := by
    -- Proof comment: each pair morphism satisfies the quotient square, so equality of the
    -- quotient-side maps yields equality of the reductions of the underlying ring maps.
    ext y
    have hτ₁sq :
        τ₁.hom.right.hom (Ideal.Quotient.mk Y.stageIdeal y) =
          (Ideal.Quotient.mk Z.1.ideal) ((ringHom τ₁) y) := by
      simpa [EtaleNeighborhood.toPair, ringHom, quotientArrow] using
        (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp τ₁.hom.w) y).symm
    have hτ₂sq :
        τ₂.hom.right.hom (Ideal.Quotient.mk Y.stageIdeal y) =
          (Ideal.Quotient.mk Z.1.ideal) ((ringHom τ₂) y) := by
      simpa [EtaleNeighborhood.toPair, ringHom, quotientArrow] using
        (RingHom.congr_fun (CommRingCat.hom_ext_iff.mp τ₂.hom.w) y).symm
    have hrightAt :
        τ₁.hom.right.hom (Ideal.Quotient.mk Y.stageIdeal y) =
          τ₂.hom.right.hom (Ideal.Quotient.mk Y.stageIdeal y) := by
      exact congrArg
        (fun φ : (Y.carrier ⧸ Y.stageIdeal) →+* (Z.1.ring ⧸ Z.1.ideal) ↦
          φ (Ideal.Quotient.mk Y.stageIdeal y))
        hright
    exact hτ₁sq.symm.trans <| hrightAt.trans hτ₂sq
  have hreductions_alg :
      (Ideal.Quotient.mkₐ X.ring Z.1.ideal).comp f₁ =
        (Ideal.Quotient.mkₐ X.ring Z.1.ideal).comp f₂ := by
    -- Proof comment: the quotient reductions agree as algebra maps because their underlying ring
    -- homomorphisms agree on every element.
    ext y
    exact RingHom.congr_fun hreductions y
  have hf : f₁ = f₂ := by
    -- Proof comment: the henselian uniqueness bridge upgrades equality modulo `Z.1.ideal` to
    -- equality of the stage maps themselves.
    exact eq_of_equal_reductions_between_etale_algebras_of_henselianRing hreductions_alg
  exact hom_ext (congrArg AlgHom.toRingHom hf)

/-- Helper for Lemma 15.12.1: the ideal of a henselian pair satisfies the étale lifting property
from Lemma `15.11.6`. -/
private theorem henselianPair_hasEtaleLiftProperty (Z : HenselianPairCat.{u}) :
    Z.1.ideal.HasEtaleLiftProperty := by
  let Q : Ideal Z.1.ring → Prop := Ideal.HasFiniteAlgebraIdempotentLifting.{u, u}
  let P : Ideal Z.1.ring → Prop := Ideal.HasIntegralAlgebraIdempotentLifting.{u, u}
  let T (J : Ideal Z.1.ring) : List Prop :=
    [ HenselianRing Z.1.ring J
    , J.HasEtaleLiftProperty
    , Q J
    , P J
    , J.SatisfiesGabberRootCriterion
    ]
  have hTfae : List.TFAE (T Z.1.ideal) := by
    -- Proof comment: rewrite the chapter TFAE in the local five-clause notation specialized to
    -- the target ring of the henselian pair.
    simpa [T, Q, P] using
      Ideal.henselianRing_tfae_etaleLift_idempotents_gabberCriterion
        (A := Z.1.ring) Z.1.ideal
  have hiff : HenselianRing Z.1.ring Z.1.ideal ↔ Z.1.ideal.HasEtaleLiftProperty := by
    -- Proof comment: clause `(1) ↔ (2)` is exactly the bridge from henselianity to the lifting
    -- property used in the source proof.
    simpa [T] using hTfae.out 0 1
  exact hiff.mp Z.2

/-- Helper for Lemma 15.12.1: every étale neighborhood stage of `X` maps to a henselian target
lying over `X`. -/
lemma EtaleNeighborhood.exists_to_henselian_target {X : RingPairCat.{u}}
    (Y : EtaleNeighborhood X) {Z : HenselianPairCat.{u}}
    (u : X ⟶ henselianPairInclusion.obj Z) :
    ∃ τ : Y.toPair ⟶ henselianPairInclusion.obj Z, Y.homFromSource ≫ τ = u := by
  let _ : Algebra X.ring Z.1.ring := (ringHom u).toAlgebra
  let _ : Algebra X.ring (Z.1.ring ⧸ Z.1.ideal) :=
    ((Ideal.Quotient.mkₐ X.ring Z.1.ideal).toRingHom).toAlgebra
  have huIdeal : X.ideal ≤ Ideal.comap (ringHom u) Z.1.ideal :=
    ringHom_ideal_le_comap u
  let uClosedFiber : X.ring ⧸ X.ideal →ₐ[X.ring] Z.1.ring ⧸ Z.1.ideal :=
    Ideal.quotientMapₐ Z.1.ideal (ringHom u) huIdeal
  let stageToClosedFiber : Y.carrier →ₐ[X.ring] Z.1.ring ⧸ Z.1.ideal :=
    (uClosedFiber.comp
        ((EtaleNeighborhood.closedFiberAlgEquiv Y).symm.toAlgHom.restrictScalars X.ring)).comp
      (Ideal.Quotient.mkₐ X.ring Y.stageIdeal)
  let baseRing := Z.1.ring ⊗[X.ring] Y.carrier
  let _ : CommRing baseRing := inferInstance
  let _ : Algebra Z.1.ring baseRing := inferInstance
  let _ : Algebra.Etale Z.1.ring baseRing :=
    Algebra.Etale.baseChange X.ring Y.carrier Z.1.ring
  have hbaseToClosedFiberComm :
      ∀ z : Z.1.ring,
        (Algebra.TensorProduct.productMap (Ideal.Quotient.mkₐ X.ring Z.1.ideal)
            stageToClosedFiber)
          ((algebraMap Z.1.ring baseRing) z) =
        algebraMap Z.1.ring (Z.1.ring ⧸ Z.1.ideal) z := by
    -- Proof comment: on the left tensor factor, the product map is the quotient map of the
    -- henselian target.
    intro z
    simp [baseRing, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.includeLeft_apply]
  let baseToClosedFiber : baseRing →ₐ[Z.1.ring] Z.1.ring ⧸ Z.1.ideal :=
    { toRingHom := (Algebra.TensorProduct.productMap (Ideal.Quotient.mkₐ X.ring Z.1.ideal)
        stageToClosedFiber).toRingHom
      commutes' := hbaseToClosedFiberComm }
  obtain ⟨baseLift, _hbaseLift⟩ :=
    henselianPair_hasEtaleLiftProperty Z baseToClosedFiber
  let liftedStageMap : Y.carrier →ₐ[X.ring] Z.1.ring :=
    (baseLift.restrictScalars X.ring).comp (Algebra.TensorProduct.includeRight : Y.carrier →ₐ[X.ring] baseRing)
  have hliftedStageMapComp :
      liftedStageMap.toRingHom.comp (algebraMap X.ring Y.carrier) = ringHom u := by
    -- Proof comment: the lifted stage map still restricts to the given source map because
    -- `includeRight` and `baseLift` are both `X.ring`-algebra maps over `u`.
    ext x
    change
      (baseLift.restrictScalars X.ring)
        ((Algebra.TensorProduct.includeRight : Y.carrier →ₐ[X.ring] baseRing)
          ((algebraMap X.ring Y.carrier) x)) =
        ringHom u x
    rw [(Algebra.TensorProduct.includeRight : Y.carrier →ₐ[X.ring] baseRing).commutes x]
    exact (baseLift.restrictScalars X.ring).commutes x
  let _ : Algebra Y.carrier Z.1.ring := liftedStageMap.toRingHom.toAlgebra
  have hstageIdeal :
      Y.stageIdeal ≤ Ideal.comap liftedStageMap.toRingHom Z.1.ideal := by
    -- Proof comment: `Y.stageIdeal` is generated from `X.ideal`, and the previous restriction
    -- identity reduces the containment to the source pair map `u`.
    rw [EtaleNeighborhood.stageIdeal, Ideal.map_le_iff_le_comap]
    simpa [Ideal.comap_comap, hliftedStageMapComp] using huIdeal
  let τ : Y.toPair ⟶ henselianPairInclusion.obj Z :=
    pairOfIdealMap Y.stageIdeal Z.1.ideal hstageIdeal
  refine ⟨τ, ?_⟩
  -- Proof comment: after packaging the lifted stage map as a pair morphism, equality over `X`
  -- follows from the restriction identity proved above.
  apply hom_ext
  exact hliftedStageMapComp

/-- Helper for Lemma 15.12.1: the source-faithful filtered-colimit construction yields a
universal henselian pair over every ring pair. -/
lemma exists_pairHenselizationData (X : RingPairCat.{u}) :
    Nonempty (PairHenselizationData X) := by
  let Y : EtaleNeighborhood X := EtaleNeighborhood.self X
  have hY : Nonempty (EtaleNeighborhood X) := ⟨Y⟩
  let stageDiagram : EtaleNeighborhood X ⥤ RingPairCat.{u} :=
    EtaleNeighborhood.toRingPairFunctor X
  let stageMap : X ⟶ Y.toPair := Y.homFromSource
  -- Proof comment: the source route is now stabilized through the concrete owner
  -- `EtaleNeighborhood X`, the source diagram `stageDiagram`, its base object
  -- `EtaleNeighborhood.self X`, and the canonical stage map `stageMap : X ⟶ Y.toPair`.
  -- Route correction: the stagewise factorization into henselian targets is now available in both
  -- directions, with existence packaged by `EtaleNeighborhood.exists_to_henselian_target` and
  -- uniqueness by `EtaleNeighborhood.hom_ext_into_henselian_target`; the remaining blocker is the
  -- filtered-colimit packaging of all stages.
  -- TODO: endow `EtaleNeighborhood X` with its filtered category structure, form the colimit of
  -- the canonical diagram of stage rings, prove the resulting closed-fiber map is bijective,
  -- verify henselianity via `Ideal.HasEtaleLiftProperty` and Lemma `15.11.6`, and then assemble
  -- the universal bijection by `IsColimit.desc` using the now-established stagewise existence and
  -- uniqueness arguments over henselian targets.
  sorry

/-- Helper for Lemma 15.12.1: every ring pair lies in the objectwise domain of definition of the
left adjoint to the inclusion of henselian pairs. -/
lemma henselianPair_leftAdjointObjIsDefined (X : RingPairCat.{u}) :
    henselianPairInclusion.leftAdjointObjIsDefined X := by
  classical
  -- Proof comment: once the universal henselian pair is available, the corepresentability
  -- criterion for `leftAdjointObjIsDefined` is exactly the previous lemma.
  rcases exists_pairHenselizationData X with ⟨data⟩
  exact data.leftAdjointObjIsDefined

/-- Helper for Lemma 15.12.1: the partial-left-adjoint domain of the henselian-pair inclusion is
all ring pairs. -/
lemma henselianPair_leftAdjointObjIsDefined_eq_top :
    henselianPairInclusion.leftAdjointObjIsDefined = ⊤ := by
  ext X
  constructor
  · intro _
    trivial
  · intro _
    -- Proof comment: the previous objectwise construction supplies the required universal arrow.
    exact henselianPair_leftAdjointObjIsDefined X

/-- Lemma 15.12.1: the inclusion functor from the category of henselian pairs to the category of
pairs is a right adjoint; equivalently, henselization of pairs gives a left adjoint to this
inclusion. -/
@[stacks 0A02]
theorem henselianPairInclusion_isRightAdjoint :
    henselianPairInclusion.IsRightAdjoint := by
  -- Proof comment: after isolating the source construction in
  -- `exists_pairHenselizationData`, the categorical finish is the standard right-adjoint criterion
  -- from the equality `leftAdjointObjIsDefined = ⊤`.
  exact Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    henselianPair_leftAdjointObjIsDefined_eq_top

end

end RingPairCat

end
