import Mathlib.CategoryTheory.Sites.CoversTop
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.GroupTheory.GroupAction.Transitive

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory
namespace Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Definition 21.4.1: a pseudo `G`-torsor on a site is a sheaf of sets endowed with a
left action of the sheaf of groups `G` whose sections over every object form a simply
transitive action whenever they are nonempty. -/
@[stacks 03AH]
structure PseudoTorsor (G : Sheaf J GrpCat.{w}) where
  /-- The underlying sheaf of sets. -/
  carrier : Sheaf J (Type w)
  /-- The objectwise left action of `G` on the underlying sheaf of sets. -/
  mulAction (U : C) : MulAction (G.1.obj (op U)) (carrier.1.obj (op U))
  /-- Restriction maps are equivariant with respect to the action. -/
  act_naturality {U V : C} (f : V ⟶ U) (g : G.1.obj (op U)) (x : carrier.1.obj (op U)) :
    carrier.1.map f.op (g • x) =
      (G.1.map f.op g) • carrier.1.map f.op x
  /-- Over each object of the site, the `G(U)`-action on sections is pretransitive. -/
  isPretransitive (U : C) : MulAction.IsPretransitive (G.1.obj (op U)) (carrier.1.obj (op U))
  /-- Over each object of the site, the `G(U)`-action on sections is free. -/
  isCancelSMul (U : C) : IsCancelSMul (G.1.obj (op U)) (carrier.1.obj (op U))

namespace PseudoTorsor

variable {G : Sheaf J GrpCat.{w}}

/-- A pseudo torsor is canonically viewed as its underlying sheaf of sets. -/
instance : CoeOut (PseudoTorsor G) (Sheaf J (Type w)) where
  coe P := P.carrier

/-- The sections of a pseudo torsor over an object of the site. -/
abbrev Sections (P : PseudoTorsor G) (U : C) : Type w :=
  P.carrier.1.obj (op U)

/-- Restriction of sections of a pseudo torsor along a morphism in the site. -/
abbrev res (P : PseudoTorsor G) {U V : C} (f : V ⟶ U) : Sections P U → Sections P V :=
  P.carrier.1.map f.op

instance instMulAction (P : PseudoTorsor G) (U : C) :
    MulAction (G.1.obj (op U)) (Sections P U) :=
  P.mulAction U

instance instIsPretransitive (P : PseudoTorsor G) (U : C) :
    MulAction.IsPretransitive (G.1.obj (op U)) (Sections P U) :=
  P.isPretransitive U

instance instIsCancelSMul (P : PseudoTorsor G) (U : C) :
    IsCancelSMul (G.1.obj (op U)) (Sections P U) :=
  P.isCancelSMul U

instance instMulActionOp (P : PseudoTorsor G) (U : Cᵒᵖ) :
    MulAction (G.1.obj U) (P.carrier.1.obj U) := by
  simpa [Sections] using instMulAction P (unop U)

instance instIsPretransitiveOp (P : PseudoTorsor G) (U : Cᵒᵖ) :
    MulAction.IsPretransitive (G.1.obj U) (P.carrier.1.obj U) := by
  simpa [Sections] using instIsPretransitive P (unop U)

instance instIsCancelSMulOp (P : PseudoTorsor G) (U : Cᵒᵖ) :
    IsCancelSMul (G.1.obj U) (P.carrier.1.obj U) := by
  simpa [Sections] using instIsCancelSMul P (unop U)

/-- Restriction maps of a pseudo torsor preserve the given group action. -/
@[simp] theorem res_smul (P : PseudoTorsor G) {U V : C} (f : V ⟶ U)
    (g : G.1.obj (op U)) (x : Sections P U) :
    P.res f (g • x) = G.1.map f.op g • P.res f x :=
  P.act_naturality f g x

/-- Simple transitivity over a chosen section, derived from the canonical transitivity and freeness
axioms of the action. -/
theorem simplyTransitive (P : PseudoTorsor G) (U : C) (x : Sections P U) :
    Function.Bijective (fun g : G.1.obj (op U) ↦ g • x) := by
  constructor
  · intro g h hgh
    exact IsCancelSMul.right_cancel g h x hgh
  · intro y
    exact MulAction.exists_smul_eq (G.1.obj (op U)) x y

/-- A morphism of pseudo torsors is a morphism of the underlying sheaves of sets that intertwines
the given `G`-actions. -/
structure Hom (P Q : PseudoTorsor G) where
  /-- The underlying morphism of sheaves of sets. -/
  hom : P.carrier ⟶ Q.carrier
  /-- The underlying sheaf map is equivariant for the `G`-actions. -/
  comm (U : C) (g : G.1.obj (op U)) (x : Sections P U) :
    hom.1.app (op U) (g • x) = g • hom.1.app (op U) x

namespace Hom

/-- The value on `U` of a morphism of pseudo torsors. -/
abbrev app {P Q : PseudoTorsor G} (f : Hom P Q) (U : C) :
    Sections P U → Sections Q U :=
  f.hom.1.app (op U)

/-- Morphisms of pseudo torsors commute with the group action on sections. -/
@[simp] theorem app_smul {P Q : PseudoTorsor G} (f : Hom P Q) (U : C)
    (g : G.1.obj (op U)) (x : Sections P U) :
    f.app U (g • x) = g • f.app U x :=
  f.comm U g x

end Hom

/-- Two morphisms of pseudo torsors are equal once their underlying sheaf maps are equal. -/
theorem Hom.ext_hom {P Q : PseudoTorsor G} {f g : Hom P Q} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  simp

/-- Extensionality for morphisms of pseudo torsors by objectwise equality on sections. -/
@[ext] theorem Hom.ext {P Q : PseudoTorsor G} {f g : Hom P Q}
    (h : ∀ U : C, ∀ x : Sections P U, f.app U x = g.app U x) : f = g := by
  apply Hom.ext_hom
  ext U x
  exact h (unop U) x

/-- The identity morphism of a pseudo torsor. -/
abbrev id (P : PseudoTorsor G) : Hom P P where
  hom := 𝟙 P.carrier
  comm := fun _ _ _ ↦ rfl

/-- Composition of morphisms of pseudo torsors. -/
abbrev comp {P Q R : PseudoTorsor G} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  hom := f.hom ≫ g.hom
  comm := fun U h x ↦
    Eq.trans
      (congrArg (g.app U) (f.comm U h x))
      (g.comm U h (f.app U x))

/-- Pseudo torsors form a category via equivariant morphisms of the underlying sheaves. -/
instance : Category (PseudoTorsor G) where
  Hom P Q := Hom P Q
  id := id
  comp f g := comp f g
  id_comp := by
    intro P Q f
    refine Hom.ext ?_
    intro U x
    rfl
  comp_id := by
    intro P Q f
    refine Hom.ext ?_
    intro U x
    rfl
  assoc := by
    intro P Q R S f g h
    refine Hom.ext ?_
    intro U x
    rfl

end PseudoTorsor

/-- A `G`-torsor is a pseudo `G`-torsor whose underlying sheaf is locally nonempty on the site. -/
@[stacks 03AH]
structure Torsor (G : Sheaf J GrpCat.{w}) extends PseudoTorsor G where
  /-- Every object admits a covering sieve on which the torsor has sections. -/
  locallyNonempty :
    ∀ U : C,
      ∃ S : Sieve U, S ∈ J U ∧
        ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
          Nonempty (carrier.1.obj (op V))

namespace Torsor

variable {G : Sheaf J GrpCat.{w}}

/-- The sections of a torsor over an object of the site. -/
abbrev Sections (P : Torsor G) (U : C) : Type w :=
  P.toPseudoTorsor.Sections U

/-- Restriction of sections of a torsor along a morphism in the site. -/
abbrev res (P : Torsor G) {U V : C} (f : V ⟶ U) : Sections P U → Sections P V :=
  P.toPseudoTorsor.res f

instance instMulAction (P : Torsor G) (U : C) :
    MulAction (G.1.obj (op U)) (Sections P U) :=
  P.mulAction U

instance instIsPretransitive (P : Torsor G) (U : C) :
    MulAction.IsPretransitive (G.1.obj (op U)) (Sections P U) :=
  P.isPretransitive U

instance instIsCancelSMul (P : Torsor G) (U : C) :
    IsCancelSMul (G.1.obj (op U)) (Sections P U) :=
  P.isCancelSMul U

instance instMulActionOp (P : Torsor G) (U : Cᵒᵖ) :
    MulAction (G.1.obj U) (P.carrier.1.obj U) := by
  simpa [Sections] using instMulAction P (unop U)

instance instIsPretransitiveOp (P : Torsor G) (U : Cᵒᵖ) :
    MulAction.IsPretransitive (G.1.obj U) (P.carrier.1.obj U) := by
  simpa [Sections] using instIsPretransitive P (unop U)

instance instIsCancelSMulOp (P : Torsor G) (U : Cᵒᵖ) :
    IsCancelSMul (G.1.obj U) (P.carrier.1.obj U) := by
  simpa [Sections] using instIsCancelSMul P (unop U)

/-- A morphism of torsors is a morphism of the underlying pseudo torsors. -/
abbrev Hom (P Q : Torsor G) :=
  PseudoTorsor.Hom P.toPseudoTorsor Q.toPseudoTorsor

/-- Restriction maps of a torsor preserve the given group action. -/
@[simp] theorem res_smul (P : Torsor G) {U V : C} (f : V ⟶ U)
    (g : G.1.obj (op U)) (x : Sections P U) :
    P.res f (g • x) = G.1.map f.op g • P.res f x :=
  P.act_naturality f g x

/-- Translation by any chosen section identifies the acting group with the torsor fiber. -/
theorem simplyTransitive (P : Torsor G) (U : C) (x : Sections P U) :
    Function.Bijective (fun g : G.1.obj (op U) ↦ g • x) :=
  P.toPseudoTorsor.simplyTransitive U x

/-- `G`-torsors form a category via equivariant morphisms of the underlying sheaves. -/
instance : Category (Torsor G) where
  Hom P Q := Hom P Q
  id P := PseudoTorsor.id P.toPseudoTorsor
  comp f g := PseudoTorsor.comp f g
  id_comp := by
    intro P Q f
    refine PseudoTorsor.Hom.ext ?_
    intro U x
    rfl
  comp_id := by
    intro P Q f
    refine PseudoTorsor.Hom.ext ?_
    intro U x
    rfl
  assoc := by
    intro P Q R S f g h
    refine PseudoTorsor.Hom.ext ?_
    intro U x
    rfl

private instance instTrivialMulAction (G : Sheaf J GrpCat.{w}) (U : C) :
    MulAction (G.1.obj (op U)) (((sheafForget J).obj G).1.obj (op U)) := by
  simpa using (inferInstance : MulAction (G.1.obj (op U)) (G.1.obj (op U)))

-- Proof sketch: restriction maps in a sheaf of groups are group homomorphisms, so they preserve
-- multiplication and therefore commute with the left multiplication action.
/-- Restriction maps of the trivial torsor are equivariant for left multiplication. -/
private theorem trivial_act_naturality (G : Sheaf J GrpCat.{w})
    {U V : C} (f : V ⟶ U) (g : G.1.obj (op U))
    (x : ((sheafForget J).obj G).1.obj (op U)) :
    ((sheafForget J).obj G).1.map f.op (g • x) =
      (G.1.map f.op g) • ((sheafForget J).obj G).1.map f.op x := by
  change (ConcreteCategory.hom (G.1.map f.op)) (g * (show G.1.obj (op U) from x)) =
    (ConcreteCategory.hom (G.1.map f.op)) g *
      (ConcreteCategory.hom (G.1.map f.op)) (show G.1.obj (op U) from x)
  exact map_mul (ConcreteCategory.hom (G.1.map f.op)) g (show G.1.obj (op U) from x)

-- Proof sketch: the action of a group on itself by left multiplication is the canonical regular
-- action, hence objectwise pretransitive.
/-- The trivial torsor is pretransitive on every object of the site. -/
private theorem trivial_isPretransitive (G : Sheaf J GrpCat.{w}) (U : C) :
    MulAction.IsPretransitive (G.1.obj (op U)) (((sheafForget J).obj G).1.obj (op U)) := by
  simpa using
    (inferInstance : MulAction.IsPretransitive (G.1.obj (op U)) (G.1.obj (op U)))

-- Proof sketch: the regular action of a group on itself is free by cancellation.
/-- The trivial torsor is free on every object of the site. -/
private theorem trivial_isCancelSMul (G : Sheaf J GrpCat.{w}) (U : C) :
    IsCancelSMul (G.1.obj (op U)) (((sheafForget J).obj G).1.obj (op U)) := by
  simpa using (inferInstance : IsCancelSMul (G.1.obj (op U)) (G.1.obj (op U)))

-- Proof sketch: take the maximal sieve on `U`; every restriction object has a distinguished
-- section given by the identity element of the corresponding group.
/-- The trivial torsor is locally nonempty on every covering sieve. -/
private theorem trivial_locallyNonempty (G : Sheaf J GrpCat.{w}) (U : C) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ ⦃V : C⦄ (f : V ⟶ U), S f →
        Nonempty (((sheafForget J).obj G).1.obj (op V)) := by
  refine ⟨⊤, J.top_mem U, ?_⟩
  intro V f hf
  exact ⟨(1 : G.1.obj (op V))⟩

/-- The trivial torsor associated to `G`, given by `G` acting on itself by left multiplication. -/
noncomputable def trivial (G : Sheaf J GrpCat.{w}) : Torsor G where
  carrier := (sheafForget J).obj G
  mulAction U := instTrivialMulAction G U
  act_naturality := trivial_act_naturality G
  isPretransitive := trivial_isPretransitive G
  isCancelSMul := trivial_isCancelSMul G
  locallyNonempty := trivial_locallyNonempty G

/-- A `G`-torsor is trivial when it admits an equivariant isomorphism to the trivial torsor. -/
abbrev IsTrivial (P : Torsor G) : Prop :=
  Nonempty (P ≅ trivial G)

end Torsor

end Sheaf
end CategoryTheory
