import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_15_12_1 (from Chap15) -/
open CategoryTheory

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
  sorry

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
        CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ) := sorry

/-- The map of pairs induced by an `A`-algebra map carrying `I` into `J`. -/
abbrev pairOfIdealMap (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    pairOfIdeal I ⟶ pairOfIdeal J :=
  InducedCategory.homMk <|
    Arrow.homMk'
      (CommRingCat.ofHom (algebraMap A B))
      (CommRingCat.ofHom (Ideal.quotientMap J (algebraMap A B) hIJ))
      (pairOfIdeal_hom_square I J hIJ)

end

-- Proof sketch: for a pair `(A, I)`, take the filtered colimit of the category of étale
-- neighborhoods of `(A, I)` inducing an isomorphism modulo `I`, as in the source. Lemma
-- `15.11.13` gives henselianity of the resulting pair, and the universal mapping property proved
-- in the text identifies morphisms from this henselian pair to any henselian target pair with
-- morphisms from `(A, I)` to that target.
/-- Lemma 15.12.1: the inclusion functor from the category of henselian pairs to the category of
pairs is a right adjoint; equivalently, henselization of pairs gives a left adjoint to this
inclusion. -/
theorem henselianPairInclusion_isRightAdjoint :
    henselianPairInclusion.IsRightAdjoint := sorry

end RingPairCat

end

/-! ### Lemma_15_12_2 (from Chap15) -/
universe u

noncomputable section

namespace RingPairCat

section

variable (X : RingPairCat.{u}) [henselianPairInclusion.IsRightAdjoint]

/-
Domain-style sampling:
- primary domain: henselization of commutative ring pairs `(A, I)` and its canonical algebraic
  consequences on ideals and quotient rings;
- sampled owner declarations of the same kind:
  `toHenselization`,
  `henselizationIdeal`,
  `RingHom.Flat`,
  `Ideal.quotientMap`;
- best owner abstraction: this file is `source-facing` for the basic properties of the canonical
  map `(A, I) → (A^h, I^h)`, while the quotient comparison itself is already owned by
  `Ideal.quotientMap` and should be stated on the source-facing ideal owner `henselizationIdeal`;
- primitive data: the chosen henselization owner from `Lemma_15_12_1`;
- derived API: flatness of `toHenselization X`, identification of `I^h` with the mapped ideal,
  and bijectivity of the induced quotient map; the power-identification transport needed to build
  the quotient comparison is implementation-level and not kept as a parallel public theorem.

Source/core/bridge triage:
- `source-facing`: `toHenselization_flat`, `henselizationIdeal_eq_map`,
  `quotientPowToHenselization_bijective`;
- `core/canonical`: `toHenselization`, `henselizationIdeal`, `RingHom.Flat`, `Ideal.map`,
  `Ideal.quotientMap`;
- `bridge/view`: the quotient comparison is transported across the canonical equality
  `(henselizationIdeal X) ^ n = Ideal.map (toHenselization X) (X.ideal ^ n)` coming from
  `henselizationIdeal_eq_map` and `Ideal.map_pow`, rather than exposed as a second public
  owner-level theorem.
-/

-- Proof sketch: in Lemma `15.12.1`, the henselization pair is constructed as a filtered colimit
-- of étale neighborhoods of `(A, I)` with unchanged special fiber. Étale morphisms are flat, and
-- filtered colimits of flat algebras remain flat.
/-- Lemma 15.12.2 (1): for a pair `X = (A, I)`, the canonical map from `A` to its henselization
`A^h` is flat. -/
theorem toHenselization_flat :
    RingHom.Flat (toHenselization X) := sorry

-- Proof sketch: each stage in the filtered system used to construct the henselization has ideal
-- equal to the extension of `I`, and this equality is preserved when passing to the colimit.
/-- Lemma 15.12.2 (2): for a pair `X = (A, I)`, the distinguished ideal `I^h` of the henselization
is exactly the extension of `I` along the canonical map `A → A^h`. -/
theorem henselizationIdeal_eq_map :
    henselizationIdeal X = Ideal.map (toHenselization X) X.ideal := sorry

-- Proof sketch: the étale neighborhoods in the construction of `A^h` are flat over `A`, hence
-- reduction modulo `I ^ n` is unchanged at every stage. Passing to the filtered colimit gives a
-- bijection on the quotient rings, written directly on the source-facing henselization quotient
-- `A^h / (I^h)^n`; the mapped-ideal quotient presentation is recovered from
-- `henselizationIdeal_eq_map` together with `Ideal.map_pow`.
/-- Lemma 15.12.2 (3): for every `n`, the canonical map `A / I^n → A^h / (I^h)^n` is bijective. -/
theorem quotientPowToHenselization_bijective (n : ℕ) :
    Function.Bijective
      (Ideal.quotientMap
        ((henselizationIdeal X) ^ n)
        (toHenselization X)
        (by
          simpa [henselizationIdeal_eq_map X, ← Ideal.map_pow] using
            (Ideal.le_comap_map :
              X.ideal ^ n ≤
                Ideal.comap (toHenselization X)
                  (Ideal.map (toHenselization X) (X.ideal ^ n))))) := sorry

end

end RingPairCat

/-! ### Lemma_15_12_3 (from Chap15) -/
open IsLocalRing
open RingPairCat

universe u

noncomputable section

section

variable (A : Type u) [CommRing A] [IsLocalRing A]

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

-- Proof sketch: the henselization pair `(A, maximalIdeal A)` is henselian by construction. Lemma
-- `15.12.2` identifies its distinguished ideal with the image of `maximalIdeal A`, so the target
-- has the expected maximal ideal and residue field, and the filtered-colimit-of-etale condition is
-- the same one appearing in the pair-henselization construction of Lemma `15.12.1`.
/-- Lemma 15.12.3: the pair-henselization functor sends a local ring `A`, viewed as the pair
`(A, maximalIdeal A)`, to a henselization of `A` as a local ring. -/
theorem localRing_henselization_isHenselizationOf :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) := sorry

/-- The pair-henselization of a local ring is available to typeclass search as a henselization. -/
instance localRing_henselization.instIsHenselizationOf :
    IsHenselizationOf A (henselizationRing (pairOfIdeal (maximalIdeal A))) :=
  localRing_henselization_isHenselizationOf A

end

/-! ### Lemma_15_12_4 (from Chap15) -/
open CategoryTheory

universe u

noncomputable section

namespace RingPairCat

section

/- Domain-style sampling for Lemma 15.12.4:
- primary domain: henselization of ring pairs and the canonical comparison from henselization to
  adic completion in Noetherian commutative algebra;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `RingPairCat.toHenselization`,
  `RingPairCat.henselizationRing`,
  `AdicCompletion.map`;
- best owner abstraction: the source-facing map to adic completion is derived from the canonical
  pair-henselization adjunction of Lemma `15.12.1`, not from any new local wrapper or additional
  public adjunction data;
- primitive data: a ring pair `X` and the Noetherian hypothesis on `X.ring`;
- derived API: the comparison map `A^h → A^∧` and the flatness / faithful-flatness statements
  attached to it.

Source/core/bridge triage:
- `source-facing`: the canonical map from the henselization of `(A, I)` to its `I`-adic
  completion and its properties in Lemma `15.12.4`;
- `core/canonical`: the adjunction owner `henselianPairInclusion` from Lemma `15.12.1`;
- `bridge/view`: the comparison morphism obtained by applying the adjunction universal property to
  the henselian completion pair. -/

variable (X : RingPairCat.{u})
variable [IsNoetherianRing X.ring]

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

-- Proof sketch: both composites are induced by the same ring map `X.ring → AdicCompletion X.ideal
-- X.ring`, and the lower horizontal arrow is exactly the quotient map obtained from that ring map
-- by functoriality of quotients.
/-- The quotient square defining the canonical morphism from `X` to its adic completion pair. -/
private lemma toAdicCompletionPair_w :
    CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)) ≫
        CommRingCat.ofHom
          (Ideal.Quotient.mk
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)) =
      CommRingCat.ofHom (Ideal.Quotient.mk X.ideal) ≫
        CommRingCat.ofHom
          (Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
            (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map) := sorry

-- Proof sketch: the completion ring is complete for the extended ideal, hence henselian by the
-- canonical complete-pair instance. The Noetherian hypothesis ensures the completion is complete
-- for that extended ideal in the ring-theoretic sense used by `HenselianRing`.
/-- The `I`-adic completion pair of a Noetherian pair is henselian. -/
private theorem adicCompletion_henselian :
    HenselianRing
      (AdicCompletion X.ideal X.ring)
      (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal) := by
  let hComplete :
      IsAdicComplete
        (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
        (AdicCompletion X.ideal X.ring) := by
    exact
      (IsAdicComplete.map_algebraMap_iff X.ideal (AdicCompletion X.ideal X.ring)).2
        (AdicCompletion.isAdicComplete (Ideal.fg_of_isNoetherianRing X.ideal))
  letI :
      IsAdicComplete
        (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
        (AdicCompletion X.ideal X.ring) := hComplete
  exact
    @IsAdicComplete.henselianRing
      (AdicCompletion X.ideal X.ring)
      inferInstance
      (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
      hComplete

/-- The canonical ring map from the henselization ring `A^h` to the `I`-adic completion `A^∧`. -/
def henselizationToAdicCompletion :
    henselizationRing X →+* AdicCompletion X.ideal X.ring :=
  let completionMap :
      X ⟶ pairOfIdeal (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal) :=
    InducedCategory.homMk <|
      Arrow.homMk
        (CommRingCat.ofHom (algebraMap X.ring (AdicCompletion X.ideal X.ring)))
        (CommRingCat.ofHom
          (Ideal.quotientMap
            (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal)
            (algebraMap X.ring (AdicCompletion X.ideal X.ring)) Ideal.le_comap_map))
        (toAdicCompletionPair_w X)
  let comparison :=
    ((Adjunction.ofIsRightAdjoint henselianPairInclusion).homEquiv X
      ⟨pairOfIdeal (Ideal.map (algebraMap X.ring (AdicCompletion X.ideal X.ring)) X.ideal),
        adicCompletion_henselian X⟩).symm
      completionMap
  ringHom comparison.hom

-- Proof sketch: Lemma `15.12.2` identifies every quotient
-- `X.ring ⧸ X.ideal ^ n → henselizationRing X ⧸ (X.ideal)^n henselizationRing X` as a bijection.
-- Passing to inverse limits gives a bijection on the induced map of `X.ideal`-adic completions.
/-- Lemma 15.12.4 (1): the map on `I`-adic completions induced by `A → A^h`, formalized as the
map from the `I`-adic completion of `A` to the `I`-adic completion of the `A`-module `A^h`, is
bijective. -/
theorem adicCompletion_map_toHenselization_bijective :
    Function.Bijective
      (AdicCompletion.map X.ideal (Algebra.linearMap X.ring (henselizationRing X))) := sorry

-- Proof sketch: once `A^h → A^∧` is known faithfully flat and `A^∧` is Noetherian by the standard
-- noetherianity theorem for adic completions of Noetherian rings, Noetherianity descends along
-- faithfully flat maps.
/-- Lemma 15.12.4 (2): the henselization ring `A^h` of a Noetherian pair `(A, I)` is Noetherian. -/
theorem henselizationRing_isNoetherian :
    IsNoetherianRing (henselizationRing X) := sorry

-- Proof sketch: this is exactly Lemma `15.12.2 (1)` recalled in the Noetherian setting.
/- Lemma 15.12.4 (3): the canonical map `A → A^h` is flat. -/
recall toHenselization_flat

-- Proof sketch: the completion map `A → A^∧` is flat for Noetherian rings, and the canonical map
-- `A^h → A^∧` is the comparison morphism from the henselization into that flat completion target.
-- Flatness follows from the quotientwise identification with the completion of `A`.
/-- Lemma 15.12.4 (4): the canonical map from the henselization `A^h` to the `I`-adic completion
`A^∧` is flat. -/
theorem henselizationToAdicCompletion_flat :
    RingHom.Flat (henselizationToAdicCompletion X) := sorry

-- Proof sketch: `I^h = IA^h` lies in the Jacobson radical of the henselization pair, and the map
-- `A^h → A^∧` induces the identity on the special fiber `A^h / I^h ≅ A / I`. Together with the
-- previous flatness statement, the standard Jacobson-radical criterion upgrades flatness to
-- faithful flatness.
/-- Lemma 15.12.4 (5): the canonical map from the henselization `A^h` to the `I`-adic completion
`A^∧` is faithfully flat. -/
theorem henselizationToAdicCompletion_faithfullyFlat :
    RingHom.FaithfullyFlat (henselizationToAdicCompletion X) := sorry

end

end RingPairCat

/-! ### Lemma_15_12_5 (from Chap15) -/
open CategoryTheory
open CategoryTheory.Limits

universe u

namespace RingPairCat

/- Domain-style sampling for Lemma 15.12.5:
- primary domain: category theory of adjunctions and filtered-colimit preservation;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`,
  `CategoryTheory.Limits.PreservesFilteredColimits`,
  `RingPairCat.henselianPairInclusion.leftAdjoint`;
- best owner abstraction: the pair-henselization functor is the canonical left adjoint
  `henselianPairInclusion.leftAdjoint` coming from Lemma `15.12.1`, and filtered-colimit
  preservation is derived from the generic adjunction owner theorem;
- primitive data: the right-adjoint structure on `henselianPairInclusion`, supplied upstream by
  `henselianPairInclusion_isRightAdjoint`;
- derived API: the filtered-colimit preservation instance on the left adjoint.

Source/core/bridge triage:
- `source-facing`: pair henselization commutes with filtered colimits;
- `core/canonical`: `Adjunction.leftAdjoint_preservesColimits`;
- `bridge/view`: the specialization from the generic left-adjoint owner to
  `henselianPairInclusion.leftAdjoint`.
-/

section

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

-- Proof sketch: Lemma `15.12.1` identifies pair henselization with the left adjoint of the
-- inclusion `HenselianPairCat ⥤ RingPairCat`. Left adjoints preserve all small colimits, hence in
-- particular filtered colimits.
/-- Lemma 15.12.5: the pair-henselization functor from Lemma `15.12.1` preserves filtered
colimits. -/
theorem pairHenselization_preservesFilteredColimits :
    PreservesFilteredColimits henselianPairInclusion.leftAdjoint := by
  letI : PreservesColimits henselianPairInclusion.leftAdjoint :=
    (Adjunction.ofIsRightAdjoint henselianPairInclusion).leftAdjoint_preservesColimits
  infer_instance

end

end RingPairCat

/-! ### Lemma_15_12_6 (from Chap15) -/
open PrimeSpectrum
open RingPairCat
open scoped PrimeSpectrum

universe u

noncomputable section

section

variable {A : Type u} [CommRing A]
variable [RingPairCat.henselianPairInclusion.IsRightAdjoint]

-- Proof sketch: Lemma `15.11.7` shows that `V(I) = V(J)` makes `(A, I)` henselian exactly when
-- `(A, J)` is henselian. Applying the universal property of the left adjoint from Lemma `15.12.1`
-- to the two henselization pairs gives unique `A`-algebra maps in both directions, and the same
-- uniqueness forces the composites to be identities.
/-- Lemma 15.12.6: if two ideals of `A` have the same zero locus in `Spec A`, then the chosen
pair-henselization functor yields canonically isomorphic `A`-algebras for the pairs `(A, I)` and
`(A, J)`. -/
theorem henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq (I J : Ideal A)
    (hV : V((I : Set A)) = V((J : Set A))) :
    ∃! e : henselizationRing (pairOfIdeal I) ≃ₐ[A] henselizationRing (pairOfIdeal J),
      e.toRingHom.comp
        (toHenselization (pairOfIdeal I)) =
      toHenselization (pairOfIdeal J) := sorry

end

/-! ### Lemma_15_12_7 (from Chap15) -/
open CategoryTheory
open PrimeSpectrum
open RingPairCat
open scoped PrimeSpectrum
open scoped TensorProduct

universe u

noncomputable section

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (J : Ideal B)

/- Domain-style sampling for Lemma 15.12.7:
- primary domain: pair henselization and its canonical base-change comparison map along a morphism
  of ring pairs;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `RingPairCat.henselizationRingMap`,
  `RingPairCat.toHenselization_naturality`,
  `RingPairCat.pairOfIdealMap`;
- owner abstraction: the core owner is the pair-henselization adjunction for
  `henselianPairInclusion`, already supplied by Lemma `15.12.1`;
- primitive data: a map of pairs `(A, I) → (B, J)` and the chosen henselization rings attached to
  that adjunction;
- derived API: the induced map on henselization rings, the tensor-product comparison map, and the
  bijectivity/algebra-equivalence statements.

Source/core/bridge triage:
- `source-facing`: the canonical comparison map `A^h ⊗[A] B → B^h` and its bijectivity under the
  hypotheses of Lemma 15.12.7;
- `core/canonical`: `henselianPairInclusion` together with its chosen left adjoint from
  `henselianPairInclusion_isRightAdjoint`;
- `bridge/view`: the tensor-product comparison map derived from the source pair morphism and the
  adjunction unit naturality. -/

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- The henselization ring of `(B, J)` inherits its `A`-algebra structure by composition with the
map `A → B`. -/
instance pairOfIdeal_henselizationRing_comp_algebra :
    Algebra A (henselizationRing (pairOfIdeal J)) :=
  (RingHom.comp (toHenselization (pairOfIdeal J)) (algebraMap A B)).toAlgebra

/-- The composed `A`- and `B`-algebra structures on the henselization ring of `(B, J)` form a
scalar tower. -/
instance pairOfIdeal_henselizationRing_isScalarTower :
    IsScalarTower A B (henselizationRing (pairOfIdeal J)) := sorry

-- Proof sketch: apply naturality of the adjunction unit for pair henselization to the morphism
-- `(A, I) → (B, J)`; on underlying rings this says the induced henselization map commutes with
-- the original `A`-algebra maps.
/-- The induced map on henselization rings is compatible with the `A`-algebra structures coming
from the original map `A → B`. -/
lemma henselizationRingMap_commutes (hIJ : I ≤ Ideal.comap (algebraMap A B) J) (a : A) :
    henselizationRingMap (pairOfIdealMap I J hIJ)
        (algebraMap A (henselizationRing (pairOfIdeal I)) a) =
      algebraMap A (henselizationRing (pairOfIdeal J)) a := sorry

/-- The comparison map `A^h ⊗[A] B → B^h` induced by the map of pairs `(A, I) → (B, J)`. -/
abbrev henselizationBaseChangeComparison (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    (henselizationRing (pairOfIdeal I) ⊗[A] B) →ₐ[A] henselizationRing (pairOfIdeal J) :=
  Algebra.TensorProduct.productMap
    { toRingHom := henselizationRingMap (pairOfIdealMap I J hIJ)
      commutes' := henselizationRingMap_commutes I J hIJ }
    ((Algebra.ofId B (henselizationRing (pairOfIdeal J))).restrictScalars A)

-- Proof sketch: use Lemma `15.12.6` to replace `J` by `IB`, then apply Lemma `15.11.8` to see
-- that `(A^h ⊗[A] B, I^h (A^h ⊗[A] B))` is henselian. The universal property of the henselization
-- of `(B, J)` yields a map in the opposite direction, and the two comparison maps are inverse by
-- uniqueness in the henselization adjunction.
/-- Lemma 15.12.7: for a map of pairs `(A, I) → (B, J)` with `V(J) = V(IB)` and integral ring map
`A → B`, the canonical comparison map `A^h ⊗[A] B → B^h` on chosen pair-henselization rings is
bijective. -/
theorem henselizationBaseChangeComparison_bijective_of_isIntegral
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    Function.Bijective (henselizationBaseChangeComparison I J hIJ) := sorry

/-- The canonical algebra equivalence induced by Lemma 15.12.7. -/
noncomputable def henselizationBaseChangeAlgEquiv_of_isIntegral
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    (henselizationRing (pairOfIdeal I) ⊗[A] B) ≃ₐ[A] henselizationRing (pairOfIdeal J) :=
  AlgEquiv.ofBijective (henselizationBaseChangeComparison I J hIJ)
    (henselizationBaseChangeComparison_bijective_of_isIntegral I J hIJ hV)

/-- The algebra equivalence of Lemma 15.12.7 is the canonical comparison map equipped with its
inverse. -/
theorem henselizationBaseChangeAlgEquiv_of_isIntegral_toAlgHom
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    (henselizationBaseChangeAlgEquiv_of_isIntegral I J hIJ hV).toAlgHom =
      henselizationBaseChangeComparison I J hIJ := rfl

end

/-! ### Lemma_15_12_8 (from Chap15) -/
open CategoryTheory
open RingPairCat

universe u v

noncomputable section

section

variable {A : Type u} [CommRing A]
variable {ι : Type v}
variable [RingPairCat.henselianPairInclusion.IsRightAdjoint]

/-
Domain-style sampling:
- primary domain: pair henselization in Chapter 15, with owner surface
  `henselizationRing (pairOfIdeal I)` and functoriality via `henselizationRingMap`;
- sampled same-kind declarations:
  `henselizationRing`,
  `toHenselization`,
  `henselizationRingMap`,
  `henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq`;
- best owner abstraction: the canonical chosen henselization owner from `Lemma_15_12_1`, not a
  fresh public parameter for an arbitrary left adjoint to `henselianPairInclusion`;
- primitive data: `henselizationRing (pairOfIdeal I)`;
- derived API: the comparison map from the henselization of an intersection to the product of the
  henselizations of the components, and its bijectivity under pairwise comaximality.

Source/core/bridge triage:
- `source-facing`: `henselizationIntersectionToPi` and its bijectivity theorem;
- `core/canonical`: `henselizationRing`, `pairOfIdeal`, `toHenselization`, and
  `henselizationRingMap`;
- `bridge/view`: the product comparison map assembled from the canonical maps
  `henselizationRingMap (pairOfIdealMap (⨅ j, I j) (I i) (iInf_le I i))`.
-/

/-- The natural comparison map from the henselization ring of the intersection pair to the
product of the henselization rings of the component pairs. -/
def henselizationIntersectionToPi (I : ι → Ideal A) :
    henselizationRing (pairOfIdeal (⨅ j, I j)) →+*
      ∀ i : ι, henselizationRing (pairOfIdeal (I i)) :=
  Pi.ringHom fun i ↦
    henselizationRingMap (pairOfIdealMap (⨅ j, I j) (I i) (iInf_le I i))

-- Proof sketch: argue by induction on the finite index set, reducing to the case of two ideals by
-- grouping all but one ideal into their intersection. For two pairwise comaximal ideals, the
-- Chinese remainder theorem identifies the special fibres, and the universal property of pair
-- henselization upgrades that decomposition to an isomorphism of henselizations.
/-- Lemma 15.12.8: for a finite nonempty family of pairwise comaximal ideals in `A`, the chosen
henselization of the intersection pair `(A, ⋂ i, I i)` has a natural comparison map to the
product of the henselizations of `(A, I i)`, and that map is bijective. -/
theorem henselizationIntersectionToPi_bijective [Finite ι] [Nonempty ι]
    (I : ι → Ideal A) (hI : Pairwise fun i j ↦ IsCoprime (I i) (I j)) :
    Function.Bijective (henselizationIntersectionToPi I) := sorry

end
