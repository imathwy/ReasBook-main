import Mathlib
import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.Grp.Limits

-- Declarations for this item will be appended below by the statement pipeline.

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
