import Mathlib
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Whiskering

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_21_4_1 (from Chap21) -/
noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Definition 21.4.1: a pseudo `\mathcal G`-torsor on a site is a sheaf of sets endowed with a
left action of the sheaf of groups `\mathcal G` whose sections over every object form a simply
transitive action whenever they are nonempty. -/
structure PseudoTorsor (G : Sheaf J GrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  carrier : Sheaf J (Type w)
  /-- The objectwise left action of `G` on the underlying sheaf of sets. -/
  mulAction : ∀ U : Cᵒᵖ, MulAction (G.obj.obj U) (carrier.obj.obj U)
  /-- Restriction maps are equivariant with respect to the action. -/
  act_naturality :
    ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U) (x : carrier.obj.obj U),
      carrier.obj.map f (g • x) =
        (G.obj.map f g) • carrier.obj.map f x
  /-- For every section `x`, left multiplication by elements of `G(U)` is a bijection onto
  `carrier(U)`, expressing simple transitivity on each nonempty fiber. -/
  simplyTransitive :
    ∀ (U : Cᵒᵖ) (x : carrier.obj.obj U),
      Function.Bijective (fun g : G.obj.obj U ↦ g • x)

namespace PseudoTorsor

variable {G : Sheaf J GrpCat.{w}}

/-- A pseudo torsor is canonically viewed as its underlying sheaf of sets. -/
instance : CoeOut (PseudoTorsor G) (Sheaf J (Type w)) where
  coe P := P.carrier

/-- The sections of a pseudo torsor over an object of the site. -/
abbrev Sections (P : PseudoTorsor G) (U : Cᵒᵖ) : Type w :=
  P.carrier.obj.obj U

instance instMulAction (P : PseudoTorsor G) (U : Cᵒᵖ) :
    MulAction (G.obj.obj U) (Sections P U) :=
  P.mulAction U

/-- The objectwise action map of a pseudo torsor. -/
abbrev act (P : PseudoTorsor G) (U : Cᵒᵖ) (g : G.obj.obj U) (x : Sections P U) :
    Sections P U :=
  g • x

@[simp] theorem one_act (P : PseudoTorsor G) (U : Cᵒᵖ) (x : Sections P U) :
    P.act U 1 x = x :=
  one_smul _ _

@[simp] theorem mul_act (P : PseudoTorsor G) (U : Cᵒᵖ) (g h : G.obj.obj U) (x : Sections P U) :
    P.act U (g * h) x = P.act U g (P.act U h x) :=
  mul_smul _ _ _

/-- The value on `U` of a morphism between the underlying sheaves of two pseudo torsors. -/
abbrev app {P Q : PseudoTorsor G} (f : P.carrier ⟶ Q.carrier) (U : Cᵒᵖ) :
    Sections P U → Sections Q U :=
  f.1.app U

/-- A morphism of pseudo torsors is a morphism of the underlying sheaves of sets that intertwines
 the given `G`-actions. -/
structure Hom (P Q : PseudoTorsor G) where
  /-- The underlying morphism of sheaves of sets. -/
  hom : P.carrier ⟶ Q.carrier
  /-- The underlying sheaf map is equivariant for the `G`-actions. -/
  comm :
    ∀ (U : Cᵒᵖ) (g : G.1.obj U) (x : Sections P U),
      app hom U (g • x) = g • app hom U x

end PseudoTorsor

/-- A `G`-torsor is a pseudo `G`-torsor whose underlying sheaf is locally nonempty on the site. -/
structure Torsor (G : Sheaf J GrpCat.{w}) extends PseudoTorsor G where
  /-- Every object admits a covering sieve on which the torsor has sections. -/
  locallyNonempty :
    ∀ U : C,
      ∃ S : Sieve U, S ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
          Nonempty (carrier.obj.obj (op V))

namespace Torsor

variable {G : Sheaf J GrpCat.{w}}

/-- A morphism of torsors is a morphism of the underlying pseudo torsors. -/
abbrev Hom (P Q : Torsor G) :=
  PseudoTorsor.Hom P.toPseudoTorsor Q.toPseudoTorsor

/-- An isomorphism of `G`-torsors is an equivariant morphism with an equivariant inverse. -/
structure Iso (P Q : Torsor G) where
  /-- The forward equivariant map of torsors. -/
  hom : P.Hom Q
  /-- The inverse equivariant map of torsors. -/
  inv : Q.Hom P
  /-- The two maps compose to the identity on the source torsor. -/
  hom_inv_id : hom.hom ≫ inv.hom = 𝟙 P.carrier
  /-- The two maps compose to the identity on the target torsor. -/
  inv_hom_id : inv.hom ≫ hom.hom = 𝟙 Q.carrier

private instance instTrivialMulAction (G : Sheaf J GrpCat.{w}) (U : Cᵒᵖ) :
    MulAction (G.obj.obj U) (((sheafForget J).obj G).obj.obj U) := by
  simpa using (inferInstance : MulAction (G.obj.obj U) (G.obj.obj U))

-- Proof sketch: restriction maps in a sheaf of groups are group homomorphisms, so they preserve
-- multiplication and therefore commute with the left multiplication action.
/-- Restriction maps of the trivial torsor are equivariant for left multiplication. -/
private theorem trivial_act_naturality (G : Sheaf J GrpCat.{w})
    {U V : Cᵒᵖ} (f : U ⟶ V) (g : G.obj.obj U)
    (x : ((sheafForget J).obj G).obj.obj U) :
    ((sheafForget J).obj G).obj.map f (g • x) =
      (G.obj.map f g) • ((sheafForget J).obj G).obj.map f x := sorry

-- Proof sketch: for a fixed `x ∈ G(U)`, the map `g ↦ g * x` is bijective with inverse
-- `y ↦ y * x⁻¹`, so the action of `G(U)` on itself by left multiplication is simply transitive.
/-- The trivial torsor is simply transitive on every object of the site. -/
private theorem trivial_simplyTransitive (G : Sheaf J GrpCat.{w})
    (U : Cᵒᵖ) (x : ((sheafForget J).obj G).obj.obj U) :
    Function.Bijective (fun g : G.obj.obj U ↦ g • x) := sorry

-- Proof sketch: take the maximal sieve on `U`; every restriction object has a distinguished
-- section given by the identity element of the corresponding group.
/-- The trivial torsor is locally nonempty on every covering sieve. -/
private theorem trivial_locallyNonempty (G : Sheaf J GrpCat.{w}) (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
        Nonempty (((sheafForget J).obj G).obj.obj (op V)) := sorry

/-- The trivial torsor associated to `G`, given by `G` acting on itself by left multiplication. -/
noncomputable def trivial (G : Sheaf J GrpCat.{w}) : Torsor G where
  carrier := (sheafForget J).obj G
  mulAction U := instTrivialMulAction G U
  act_naturality := trivial_act_naturality G
  simplyTransitive := trivial_simplyTransitive G
  locallyNonempty := trivial_locallyNonempty G

/-- A `G`-torsor is trivial when it admits an equivariant isomorphism to the trivial torsor. -/
abbrev IsTrivial (P : Torsor G) : Prop :=
  Nonempty (Iso P (trivial G))

end Torsor

end Sheaf
end CategoryTheory

/-! ### Lemma_21_4_2 (from Chap21) -/
open CategoryTheory Opposite

noncomputable section

universe u v w

namespace CategoryTheory
namespace Sheaf
namespace Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}}

/- Domain-style sampling for Lemma 21.4.2:
- primary domain: torsors under a sheaf of groups on a site;
- sampled owner declarations:
  `CategoryTheory.Sheaf.PseudoTorsor`,
  `CategoryTheory.Sheaf.Torsor`,
  `CategoryTheory.Sheaf.Torsor.Hom`,
  `CategoryTheory.Sheaf.Torsor.trivial`,
  `TopCat.SheafOfGroups.Torsor.toSiteTorsor`;
- best owner abstraction: `CategoryTheory.Sheaf.Torsor` is the source-facing site-level owner;
  the primitive comparison object is an equivariant isomorphism of torsors, and triviality should
  be expressed as existence of such an isomorphism to `Torsor.trivial` rather than through a
  special-purpose wrapper dedicated only to the trivial target;
- primitive data: torsors `P Q : CategoryTheory.Sheaf.Torsor G` together with morphisms
  `P.Hom Q` and `Q.Hom P`;
- derived API: `Torsor.Iso`, `Torsor.IsTrivial`, and the global-sections characterization below.

Source/core/bridge triage:
- `source-facing`: `CategoryTheory.Sheaf.Torsor G`;
- `core/canonical`: `CategoryTheory.Sheaf.Torsor.Hom`, `CategoryTheory.Sheaf.Torsor.Iso`,
  `CategoryTheory.Sheaf.Torsor.trivial`, and `CategoryTheory.Sheaf.Torsor.IsTrivial`;
- `bridge/view`: the Chapter 20 specialization through `TopCat.SheafOfGroups.Torsor.toSiteTorsor`.
-/

variable [HasWeakSheafify J (Type w)]
variable [HasGlobalSectionsFunctor J (Type w)]

-- Proof sketch: a trivialization sends a global section of the torsor to a global section of the
-- trivial torsor, and the identity section of `G` pulls back along the inverse trivialization to a
-- global section of `P`. Conversely, a chosen global section of `P` identifies each local section
-- with the unique group element carrying the chosen section to it; the torsor axioms make this
-- assignment natural in the site variable and hence produce an equivariant isomorphism with the
-- trivial torsor.
/-- Lemma 21.4.2: a `G`-torsor on a site is trivial if and only if its sheaf of sections has a
nonempty set of global sections. -/
lemma isTrivial_iff_nonempty_globalSections (P : Torsor G) :
    P.IsTrivial ↔ Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier) := sorry

end Torsor
end Sheaf
end CategoryTheory

/-! ### Lemma_21_4_3 (from Chap21) -/
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
