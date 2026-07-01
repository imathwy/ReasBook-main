import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite

noncomputable section

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasSheafify J AddCommGrpCat.{w}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]
variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The underlying sheaf of sets of an abelian sheaf on a site. -/
abbrev underlyingAbelianSheaf (H : Sheaf J AddCommGrpCat.{w}) : Sheaf J (Type w) :=
  (sheafForget J).obj H

/-- An `H`-torsor on a site is a sheaf of sets with restriction-compatible torsor translation and
difference operations by the abelian sheaf `H`, together with local inhabitation on a covering
sieve. -/
structure AbelianSheafTorsor (H : Sheaf J AddCommGrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  carrier : Sheaf J (Type w)
  /-- Translation by a section of `H`. -/
  vadd (U : C) :
    H.1.obj (op U) → carrier.1.obj (op U) → carrier.1.obj (op U)
  /-- Difference of two sections of the torsor. -/
  vsub (U : C) :
    carrier.1.obj (op U) → carrier.1.obj (op U) → H.1.obj (op U)
  /-- Torsor subtraction followed by translation recovers the first point. -/
  vsub_vadd' :
    ∀ (U : C) (x y : carrier.1.obj (op U)),
      vadd U (vsub U x y) y = x
  /-- Torsor translation followed by subtraction recovers the translating section. -/
  vadd_vsub' :
    ∀ (U : C) (h : H.1.obj (op U)) (x : carrier.1.obj (op U)),
      vsub U (vadd U h x) x = h
  /-- Restriction commutes with translation. -/
  map_vadd' :
    ∀ {U V : C} (f : V ⟶ U) (h : H.1.obj (op U)) (x : carrier.1.obj (op U)),
      carrier.1.map f.op (vadd U h x) =
        vadd V (H.1.map f.op h) (carrier.1.map f.op x)
  /-- Restriction commutes with taking differences. -/
  map_vsub' :
    ∀ {U V : C} (f : V ⟶ U) (x y : carrier.1.obj (op U)),
      H.1.map f.op (vsub U x y) =
        vsub V (carrier.1.map f.op x) (carrier.1.map f.op y)
  /-- The torsor has local sections on some covering sieve of every object. -/
  locallyInhabited :
    ∀ U : C, ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f → Nonempty (carrier.1.obj (op V))

namespace AbelianSheafTorsor

variable {H : Sheaf J AddCommGrpCat.{w}}

/-- The sections of an abelian sheaf torsor over an object of the site. -/
abbrev Sections (P : AbelianSheafTorsor H) (U : C) : Type w :=
  P.carrier.1.obj (op U)

/-- The value on `U` of a morphism between the underlying sheaves of two torsors. -/
abbrev app {P Q : AbelianSheafTorsor H} (f : P.carrier ⟶ Q.carrier) (U : C) :
    Sections P U → Sections Q U :=
  f.hom.app (op U)

/-- A morphism of `H`-torsors is a morphism of the underlying sheaves of sets compatible with
translation by sections of `H`. -/
structure Hom (P Q : AbelianSheafTorsor H) where
  /-- The underlying morphism of sheaves of sets. -/
  hom : P.carrier ⟶ Q.carrier
  /-- Compatibility with the torsor translation. -/
  map_vadd' : ∀ (U : C) (h : H.1.obj (op U)) (x : Sections P U),
      app hom U (P.vadd U h x) = Q.vadd U h (app hom U x)

/-- The identity morphism of an `H`-torsor. -/
abbrev id (P : AbelianSheafTorsor H) : Hom P P where
  hom := 𝟙 P.carrier
  map_vadd' := fun _ _ _ ↦ rfl

/-- Composition of morphisms of `H`-torsors. -/
abbrev comp {P Q R : AbelianSheafTorsor H} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  map_vadd' := fun U h x ↦
    Eq.trans
      (congrArg (app g.hom U) (f.map_vadd' U h x))
      (g.map_vadd' U h (app f.hom U x))

/-- `H`-torsors form a category via morphisms of the underlying sheaves commuting with translation.
-/
instance : Category (AbelianSheafTorsor H) where
  Hom P Q := Hom P Q
  id := id
  comp f g := comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The type of isomorphism classes of `H`-torsors. -/
abbrev IsoClasses (H : Sheaf J AddCommGrpCat.{w}) :=
  _root_.Quotient (CategoryTheory.isIsomorphicSetoid (AbelianSheafTorsor H))

end AbelianSheafTorsor

-- Proof sketch: identify an `H`-torsor with the extension class obtained from the exact sequence
-- attached to `ℤ[ℱ] → ℤ`, then use the boundary map to obtain an element of `H^1(C, H)`;
-- conversely, represent a cohomology class by a section of an injective quotient and take the
-- sheaf-theoretic fibre over that section, checking that these constructions are inverse up to
-- torsor isomorphism.
/-- Lemma 21.4.3: the isomorphism classes of `H`-torsors on the site `(C, J)` are in canonical
bijection with the first sheaf cohomology group `H^1(C, H)`. -/
theorem abelianSheafTorsor_isoClasses_equiv_H1
    (H : Sheaf J AddCommGrpCat.{w}) :
    Nonempty (AbelianSheafTorsor.IsoClasses H ≃ H.H 1) := sorry

end CategoryTheory
