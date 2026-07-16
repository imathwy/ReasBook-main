import Mathlib.CategoryTheory.Sites.GlobalSections
import StacksProject_2024.stacks_project.Chap21.Definition_21_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open Limits

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
  triviality should be expressed through the owner predicate `Torsor.IsTrivial`, i.e. existence
  of a categorical isomorphism `P ≅ Torsor.trivial G`, rather than through a special-purpose
  wrapper dedicated only to the trivial target;
- primitive data: torsors `P : CategoryTheory.Sheaf.Torsor G`;
- derived API: `P ≅ Q`, `Torsor.IsTrivial`, the underlying sheaf field `P.carrier`, and the
  global-sections characterization below.

Source/core/bridge triage:
- `source-facing`: `CategoryTheory.Sheaf.Torsor G`;
- `core/canonical`: `CategoryTheory.Sheaf.Torsor.Hom`, the categorical isomorphism type
  `P ≅ Q`, `CategoryTheory.Sheaf.Torsor.trivial`, and `CategoryTheory.Sheaf.Torsor.IsTrivial`;
- `bridge/view`: the Chapter 20 specialization through `TopCat.SheafOfGroups.Torsor.toSiteTorsor`.
-/

variable [HasWeakSheafify J (Type w)]
variable [HasGlobalSectionsFunctor J (Type w)]

/-- Helper for Lemma 21.4.2: the constant singleton sheaf is canonically the terminal sheaf. -/
private noncomputable def constantSheafPUnitIsoTerminalSheaf :
    (constantSheaf J (Type w)).obj PUnit.{w + 1} ≅
      Sheaf.terminal J Types.isTerminalPUnit := by
  simpa [constantSheaf, Sheaf.terminal] using
    (sheafificationIso (Sheaf.terminal J Types.isTerminalPUnit)).symm

/-- Helper for Lemma 21.4.2: global sections are morphisms out of the terminal singleton sheaf. -/
private noncomputable def globalSectionsEquivTerminalSheafHom
    (F : Sheaf J (Type w)) :
    (Sheaf.Γ J (Type w)).obj F ≃ (Sheaf.terminal J Types.isTerminalPUnit ⟶ F) :=
  (ΓObjEquivHom J F PUnit.{w + 1}).trans
    (constantSheafPUnitIsoTerminalSheaf.homCongr (Iso.refl F))

omit [HasWeakSheafify J (Type w)] [HasGlobalSectionsFunctor J (Type w)] in
/-- Helper for Lemma 21.4.2: the constant `1` section of the trivial torsor is natural in the
site variable. -/
private theorem trivialGlobalSectionTerminalHom_naturality
    (G : Sheaf J GrpCat.{w}) :
    ∀ ⦃U V : Cᵒᵖ⦄ (f : U ⟶ V),
      (Sheaf.terminal J Types.isTerminalPUnit).obj.map f ≫
          (fun _ : (Sheaf.terminal J Types.isTerminalPUnit).obj.obj V ↦
            (show (Torsor.trivial G).carrier.obj.obj V from (1 : G.1.obj V))) =
        (fun _ : (Sheaf.terminal J Types.isTerminalPUnit).obj.obj U ↦
            (show (Torsor.trivial G).carrier.obj.obj U from (1 : G.1.obj U))) ≫
          (Torsor.trivial G).res f.unop := by
  intro U V f
  funext x
  cases x
  -- Restriction maps in a sheaf of groups preserve the identity element.
  simpa [Torsor.trivial, Torsor.res, PseudoTorsor.res] using map_one (G.1.map f)

/-- Helper for Lemma 21.4.2: the trivial torsor carries the canonical everywhere-identity section
coming from the terminal singleton sheaf. -/
private noncomputable def trivialGlobalSectionTerminalHom
    (G : Sheaf J GrpCat.{w}) :
    Sheaf.terminal J Types.isTerminalPUnit ⟶ (Torsor.trivial G).carrier :=
  ObjectProperty.homMk <|
    NatTrans.mk
      (fun U _ ↦ (show (Torsor.trivial G).carrier.obj.obj U from (1 : G.1.obj U)))
      (trivialGlobalSectionTerminalHom_naturality G)

/-- Helper for Lemma 21.4.2: the trivial torsor has a canonical global section given objectwise by
the identity element of the acting group. -/
private noncomputable def trivialGlobalSection
    (G : Sheaf J GrpCat.{w}) :
    (Sheaf.Γ J (Type w)).obj (Torsor.trivial G).carrier :=
  (globalSectionsEquivTerminalSheafHom (Torsor.trivial G).carrier).symm
    (trivialGlobalSectionTerminalHom G)

/-- Helper for Lemma 21.4.2: a chosen global section gives an objectwise translation equivalence
between the acting group and the torsor fiber. -/
private noncomputable def translationEquivOfGlobalSection
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier) (U : C) :
    G.1.obj (op U) ≃ P.Sections U :=
  Equiv.ofBijective
    (fun g ↦ g • ΓRes P.carrier (op U) s)
    (PseudoTorsor.simplyTransitive P.toPseudoTorsor U (ΓRes P.carrier (op U) s))

/-- Helper for Lemma 21.4.2: the translation equivalence induced by a global section commutes with
restriction maps. -/
private theorem translationEquivOfGlobalSection_naturality
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier)
    {U V : C} (f : V ⟶ U) (g : G.1.obj (op U)) :
    P.res f (translationEquivOfGlobalSection P s U g) =
      translationEquivOfGlobalSection P s V (G.1.map f.op g) := by
  -- We first move the action through restriction, then identify the restricted basepoint.
  change P.res f (g • ΓRes P.carrier (op U) s) =
    (G.1.map f.op g) • ΓRes P.carrier (op V) s
  rw [P.res_smul]
  congr 1
  have hres :
      P.res f (ΓRes P.carrier (op U) s) =
        ΓRes P.carrier (op V) s := by
    simpa [Torsor.res, PseudoTorsor.res, coneΓ_π_app] using
      (congr_fun (P.carrier.coneΓ.π.naturality f.op) s).symm
  exact hres

/-- Helper for Lemma 21.4.2: the inverse translation map is natural under restriction. -/
private theorem translationEquivOfGlobalSection_symm_naturality
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier)
    {U V : C} (f : V ⟶ U) (y : P.Sections U) :
    (translationEquivOfGlobalSection P s V).symm (P.res f y) =
      G.1.map f.op ((translationEquivOfGlobalSection P s U).symm y) := by
  -- Applying the forward equivalence reduces the claim to the already proved forward naturality.
  apply (translationEquivOfGlobalSection P s V).injective
  simpa using
    (translationEquivOfGlobalSection_naturality P s f
      ((translationEquivOfGlobalSection P s U).symm y))

/-- Helper for Lemma 21.4.2: the inverse translation map is equivariant for the torsor action. -/
private theorem translationEquivOfGlobalSection_symm_smul
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier)
    (U : C) (g : G.1.obj (op U)) (y : P.Sections U) :
    (translationEquivOfGlobalSection P s U).symm (g • y) =
      g * (translationEquivOfGlobalSection P s U).symm y := by
  -- We apply the forward translation equivalence and simplify both sides to the same action.
  apply (translationEquivOfGlobalSection P s U).injective
  rw [(translationEquivOfGlobalSection P s U).apply_symm_apply]
  change g • y =
    (g * (translationEquivOfGlobalSection P s U).symm y) • ΓRes P.carrier (op U) s
  rw [mul_smul]
  exact congrArg (fun z ↦ g • z)
    ((translationEquivOfGlobalSection P s U).apply_symm_apply y).symm

/-- Helper for Lemma 21.4.2: a global section yields the canonical torsor morphism from the
trivial torsor to the given torsor by translation from that section. -/
private noncomputable def homOfGlobalSection
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier) :
    Torsor.trivial G ⟶ P where
  hom :=
    ObjectProperty.homMk <|
      NatTrans.mk
        (fun U ↦ (translationEquivOfGlobalSection P s U.unop).toFun)
        (fun U V f ↦ by
          funext g
          simpa using
            (translationEquivOfGlobalSection_naturality P s f.unop g).symm)
  comm U g x := by
    change
      (g * (show G.1.obj (op U) from x)) • ΓRes P.carrier (op U) s =
        g • ((show G.1.obj (op U) from x) • ΓRes P.carrier (op U) s)
    rw [mul_smul]

/-- Helper for Lemma 21.4.2: the inverse torsor morphism reads off the unique transporter sending
the chosen global section to a given local section. -/
private noncomputable def invOfGlobalSection
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier) :
    P ⟶ Torsor.trivial G where
  hom :=
    ObjectProperty.homMk <|
      NatTrans.mk
        (fun U ↦ (translationEquivOfGlobalSection P s U.unop).symm.toFun)
        (fun U V f ↦ by
          funext y
          simpa [Torsor.trivial] using
            (translationEquivOfGlobalSection_symm_naturality P s f.unop y))
  comm U g x := by
    simpa using translationEquivOfGlobalSection_symm_smul P s U g x

/-- Helper for Lemma 21.4.2: the translation morphisms built from a global section are inverse on
the original torsor. -/
private theorem invOfGlobalSection_homOfGlobalSection
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier) :
    invOfGlobalSection P s ≫ homOfGlobalSection P s = 𝟙 P := by
  -- Objectwise, the composite is `equiv ∘ equiv.symm`.
  refine PseudoTorsor.Hom.ext ?_
  intro U y
  change
    translationEquivOfGlobalSection P s U
      ((translationEquivOfGlobalSection P s U).symm y) = y
  exact (translationEquivOfGlobalSection P s U).apply_symm_apply y

/-- Helper for Lemma 21.4.2: the translation morphisms built from a global section are inverse on
the trivial torsor. -/
private theorem homOfGlobalSection_invOfGlobalSection
    (P : Torsor G) (s : (Sheaf.Γ J (Type w)).obj P.carrier) :
    homOfGlobalSection P s ≫ invOfGlobalSection P s =
      𝟙 (Torsor.trivial G) := by
  -- Objectwise, the composite is `equiv.symm ∘ equiv`.
  refine PseudoTorsor.Hom.ext ?_
  intro U g
  change
    (translationEquivOfGlobalSection P s U).symm
      (translationEquivOfGlobalSection P s U g) = g
  exact (translationEquivOfGlobalSection P s U).symm_apply_apply g

/-- A global section of a torsor produces the canonical trivialization by objectwise translation
from that section. -/
theorem isTrivial_of_nonempty_globalSections
    (P : Torsor G) (hs : Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier)) : P.IsTrivial := by
  rcases hs with ⟨s⟩
  -- The forward and inverse translation morphisms assemble into a torsor isomorphism.
  exact ⟨
    { hom := invOfGlobalSection P s
      inv := homOfGlobalSection P s
      hom_inv_id := invOfGlobalSection_homOfGlobalSection P s
      inv_hom_id := homOfGlobalSection_invOfGlobalSection P s }⟩

/-- A trivial torsor has a global section, obtained by transporting the canonical identity section
of the trivial torsor across an inverse trivialization. -/
theorem nonempty_globalSections_of_isTrivial (P : Torsor G)
    (hP : P.IsTrivial) : Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier) := by
  rcases hP with ⟨e⟩
  exact ⟨(Sheaf.Γ J (Type w)).map e.inv.hom (trivialGlobalSection G)⟩

-- Proof sketch: a trivialization sends a global section of the torsor to a global section of the
-- trivial torsor, and the identity section of `G` pulls back along the inverse trivialization to a
-- global section of `P`. Conversely, a chosen global section of `P` identifies each local section
-- with the unique group element carrying the chosen section to it; the torsor axioms make this
-- assignment natural in the site variable and hence produce an equivariant isomorphism with the
-- trivial torsor.
/-- Lemma 21.4.2: a `G`-torsor on a site is trivial if and only if its sheaf of sections has a
nonempty set of global sections. -/
@[stacks 03AI]
theorem isTrivial_iff_nonempty_globalSections (P : Torsor G) :
    P.IsTrivial ↔ Nonempty ((Sheaf.Γ J (Type w)).obj P.carrier) := by
  constructor
  · exact nonempty_globalSections_of_isTrivial P
  · -- A chosen global section supplies the source-faithful translation trivialization.
    exact isTrivial_of_nonempty_globalSections P

end Torsor
end Sheaf
end CategoryTheory
