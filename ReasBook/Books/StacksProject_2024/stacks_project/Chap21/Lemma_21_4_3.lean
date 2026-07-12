import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.GlobalSections
import StacksProject_2024.Chap12.Lemma_12_6_3
import StacksProject_2024.Chap06.Lemma_6_15_2
import StacksProject_2024.Chap18.Lemma_18_5_2
import StacksProject_2024.Chap18.Lemma_18_3_1
import StacksProject_2024.Chap21.Definition_21_4_1

open CategoryTheory Opposite Limits
open Sheaf.PseudoTorsor
noncomputable section

universe w' w v u uι

namespace CategoryTheory

/- Domain-style sampling for Lemma 21.4.3:
- primary domain: torsors under a sheaf of groups on a site and their classification by first
  sheaf cohomology;
- sampled owner declarations:
  `Sheaf.Torsor`,
  `Sheaf.Torsor.IsoClasses`,
  `Sheaf.Torsor.IsoClasses.IsTrivialOnCover`,
  `ExtensionClass.toExt`,
  `ExtensionClass.toExt_bijective`,
  `Sheaf.H`,
  `commGroupAddCommGroupEquivalence`;
- best owner abstraction:
  `source-facing`: the classification of isomorphism classes of torsors under the sheaf of groups
    attached to an abelian sheaf;
  `core/canonical`: `Sheaf.Torsor`, `Sheaf.Torsor.IsoClasses`, the source-facing extension-class
    owner `ExtensionClass`, and the cohomology owner `H.H 1`;
  `bridge/view`: the canonical additive-to-multiplicative passage `Sheaf.toSheafOfGroups`,
    built from `AddCommGrpCat.toCommGrp` and `commGroupAddCommGroupEquivalence.symm`, together
    with the canonical bridge `ExtensionClass.toExt : ExtensionClass H ℤ → Ext¹(ℤ, H)`.
- primitive data: a torsor `P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)` and the canonical
  cohomology owner `H.H 1 = Abelian.Ext ((constantSheaf J AddCommGrpCat).obj (AddCommGrpCat.of
  (ULift ℤ))) H 1`;
- derived API: the quotient owner `Sheaf.Torsor.IsoClasses`, cover-triviality on those quotient
  classes, the extension-to-torsor bridge/view, and the theorem-level classification of torsor
  classes by `H.H 1`.

Primitive-vs-derived split:
- primitive data are the site-level torsor owner `Sheaf.Torsor (Sheaf.toSheafOfGroups H)` and the
  cohomology owner `H.H 1`;
- the local `AbelianSheafTorsor.IsoClasses` and `AbelianSheafTorsor.IsoClasses.IsTrivialOnCover`
  aliases are only duplicate derived surface over those owners, so they should be deleted rather
  than preserved as a parallel wrapper layer;
- the public owner in this file should therefore be the source-facing comparison map from torsor
  isomorphism classes to `H.H 1`, together with its normalization and bijectivity companions,
  while the extension-class presentation stays the internal bridge/view implementing that map.
-/

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf
namespace Torsor

variable {G : Sheaf J GrpCat}

/-- The type of isomorphism classes of `G`-torsors. -/
abbrev IsoClasses (G : Sheaf J GrpCat) :=
  _root_.Quotient (CategoryTheory.isIsomorphicSetoid (Torsor G))

-- Proof sketch: evaluate the underlying sheaf isomorphism at `U`; its inverse transports any
-- section back, so section-existence is preserved under torsor isomorphism.
/-- An isomorphism of torsors preserves the existence of a section over any object of the site. -/
theorem nonempty_sections_iff_of_iso {P Q : Torsor G} (e : P ≅ Q) (U : C) :
    Nonempty (P.Sections U) ↔ Nonempty (Q.Sections U) := by
  constructor
  · rintro ⟨x⟩
    exact ⟨e.hom.app U x⟩
  · rintro ⟨x⟩
    exact ⟨e.inv.app U x⟩

namespace IsoClasses

variable {ι : Type uι} (V : ι → C)

/-- An isomorphism class of torsors is trivial on the covering family `V` if any representative
admits a section over every object `V i`. -/
abbrev IsTrivialOnCover (c : Torsor.IsoClasses G) : Prop :=
  _root_.Quotient.liftOn c
    (fun P : Torsor G ↦ ∀ i : ι, Nonempty (P.Sections (V i)))
    (fun _ _ hPQ ↦ propext <|
      hPQ.elim fun e ↦
        forall_congr' fun i ↦ nonempty_sections_iff_of_iso e (V i))

-- Proof sketch: this is immediate from the quotient-lift definition of `IsTrivialOnCover`.
/-- A representative torsor is trivial on `V` exactly when its isomorphism class is. -/
@[simp] theorem isTrivialOnCover_quot_mk_iff (P : Torsor G) :
    IsoClasses.IsTrivialOnCover V (_root_.Quotient.mk'' P : Torsor.IsoClasses G) ↔
      ∀ i : ι, Nonempty (P.Sections (V i)) := by
  rfl

end IsoClasses
end Torsor
end Sheaf

variable [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]

local instance : AddCommGrpCat.toCommGrp.IsEquivalence :=
  commGroupAddCommGroupEquivalence.symm.isEquivalence_functor

namespace Sheaf

/-- The canonical bridge/view of an abelian sheaf as a sheaf of groups via the additive-to-
multiplicative equivalence. -/
abbrev toSheafOfGroups (H : Sheaf J AddCommGrpCat.{max u v}) :
    Sheaf J GrpCat.{max u v} :=
  ((sheafCompose J AddCommGrpCat.toCommGrp) ⋙ sheafCompose J (forget₂ CommGrpCat GrpCat)).obj H

end Sheaf

variable [HasSheafify J AddCommGrpCat.{max u v}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max u v})]

local instance : HasWeakSheafify J AddCommGrpCat.{max u v} :=
  HasSheafify.isRightAdjoint

local instance : HasCokernels (Sheaf J AddCommGrpCat.{max u v}) :=
  Abelian.has_cokernels

private abbrev constantIntegerSheaf :
    Sheaf J AddCommGrpCat.{max u v} :=
  (constantSheaf J AddCommGrpCat.{max u v}).obj (AddCommGrpCat.of (ULift ℤ))

private noncomputable def constantIntegerSheafGlobalSection :
    (Sheaf.Γ J AddCommGrpCat.{max u v}).obj
      ((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v}) :=
  (((constantSheafΓAdj J AddCommGrpCat.{max u v}).unit.app
      (AddCommGrpCat.of (ULift ℤ))).hom)
    (ULift.up (1 : ℤ))

private noncomputable def constantIntegerSheafOne (U : Cᵒᵖ) :
    (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.obj U :=
  Sheaf.ΓRes
    (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v}))
    U
    constantIntegerSheafGlobalSection

/-- Helper for Lemma 21.4.3: the distinguished global section `1` of the constant integer sheaf
restricts to the distinguished local section on every object. -/
private theorem constantIntegerSheafOne_naturality {U V : Cᵒᵖ} (f : U ⟶ V) :
    (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.map f
        (constantIntegerSheafOne U) =
      constantIntegerSheafOne V := by
  -- Restriction of global sections is natural in the object of the site.
  change
    AddCommGrpCat.Hom.hom
        (((constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v}).ΓRes U) ≫
          ((constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v})).1.map f)
        constantIntegerSheafGlobalSection =
      AddCommGrpCat.Hom.hom
        ((constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v}).ΓRes V)
        constantIntegerSheafGlobalSection
  exact ConcreteCategory.congr_hom
    (Sheaf.ΓRes_map
      ((constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v})) f)
    constantIntegerSheafGlobalSection

/-- Helper for Lemma 21.4.3: restricting a lift of `1` along a morphism of the site still lands in
the fiber over `1`. -/
private theorem extensionLiftCarrier_map_mem
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    {U V : Cᵒᵖ} (f : U ⟶ V)
    (t : {x : S.E.1.obj U // S.g.1.app U x = constantIntegerSheafOne U}) :
    S.g.1.app V (S.E.1.map f t.1) = constantIntegerSheafOne V := by
  -- First move the lift condition across the naturality square for `S.g`.
  calc
    S.g.1.app V (S.E.1.map f t.1) =
        (((constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v})).1.map f)
          (S.g.1.app U t.1) := by
          simpa using congr_fun (S.g.1.naturality f) t.1
    _ =
        (((constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v})).1.map f)
          (constantIntegerSheafOne U) := by rw [t.2]
    _ = constantIntegerSheafOne V := constantIntegerSheafOne_naturality f

/-- Helper for Lemma 21.4.3: the fixed-fiber lift construction is functorial on identity maps. -/
private theorem extensionLiftCarrier_map_id
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf) :
    ∀ U : Cᵒᵖ,
      (fun t :
          {x : S.E.1.obj U // S.g.1.app U x = constantIntegerSheafOne U} ↦
        ((⟨S.E.1.map (𝟙 U) t.1, extensionLiftCarrier_map_mem H S (𝟙 U) t⟩ :
          {x : S.E.1.obj U // S.g.1.app U x = constantIntegerSheafOne U}))) =
      (id :
        {x : S.E.1.obj U // S.g.1.app U x = constantIntegerSheafOne U} →
          {x : S.E.1.obj U // S.g.1.app U x = constantIntegerSheafOne U}) := by
  intro U
  funext t
  -- The underlying restriction map of a presheaf is the identity on an identity arrow.
  apply Subtype.ext
  simp

/-- Helper for Lemma 21.4.3: the fixed-fiber lift construction is functorial on composites. -/
private theorem extensionLiftCarrier_map_comp
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf) :
    ∀ {U V W : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W),
      (fun t :
          {x : S.E.1.obj U // S.g.1.app U x = constantIntegerSheafOne U} ↦
        ((⟨S.E.1.map g (S.E.1.map f t.1),
          extensionLiftCarrier_map_mem H S g
            ⟨S.E.1.map f t.1, extensionLiftCarrier_map_mem H S f t⟩⟩ :
          {x : S.E.1.obj W // S.g.1.app W x = constantIntegerSheafOne W}))) =
      fun t :
          {x : S.E.1.obj U // S.g.1.app U x = constantIntegerSheafOne U} ↦
        ((⟨S.E.1.map (f ≫ g) t.1, extensionLiftCarrier_map_mem H S (f ≫ g) t⟩ :
          {x : S.E.1.obj W // S.g.1.app W x = constantIntegerSheafOne W})) := by
  intro U V W f g
  funext t
  -- The underlying presheaf map already satisfies the composition law.
  apply Subtype.ext
  simp

/-- Helper for Lemma 21.4.3: the local lifts of the distinguished section form a presheaf. -/
private noncomputable def extensionLiftCarrierPresheaf
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf) :
    Cᵒᵖ ⥤ Type (max u v) where
  obj U := { t : S.E.1.obj U // S.g.1.app U t = constantIntegerSheafOne U }
  map f t := ⟨S.E.1.map f t.1, extensionLiftCarrier_map_mem H S f t⟩
  map_id := extensionLiftCarrier_map_id H S
  map_comp := fun f g ↦ (extensionLiftCarrier_map_comp H S f g).symm

/-- Helper for Lemma 21.4.3: two sections of the constant integer sheaf are equal once their
restrictions agree on every arrow of a fixed cover. -/
private theorem constantIntegerSheaf_equal_of_cover_restrictions
    (U : C) (T : J.Cover U)
    (a b : (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.obj (op U))
    (h :
      ∀ I : T.Arrow,
        (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.map I.f.op a =
          (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.map I.f.op b) :
    a = b := by
  -- Use separatedness of the constant sheaf to recover equality from equality on a cover.
  exact
    (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).2.isSeparated
      U T.1 T.2 a b (fun Y f hf ↦ h ⟨Y, f, hf⟩)

/-- Helper for Lemma 21.4.3: if a section of the middle sheaf glues the projected family of lifts,
then its image in the constant sheaf is still the distinguished section `1`. -/
private theorem extensionLiftCarrier_amalgamation_mem
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C) (T : J.Cover U)
    (x : ∀ I : T.Arrow, (extensionLiftCarrierPresheaf H S).obj (op I.Y))
    (σE : S.E.1.obj (op U))
    (hσE : ∀ I : T.Arrow, S.E.1.map I.f.op σE = (x I).1) :
    S.g.1.app (op U) σE = constantIntegerSheafOne (op U) := by
  -- Compare both sections after restriction to every arrow of the chosen cover.
  apply constantIntegerSheaf_equal_of_cover_restrictions U T
  intro I
  calc
    (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.map I.f.op
        (S.g.1.app (op U) σE) =
      S.g.1.app (op I.Y) (S.E.1.map I.f.op σE) := by
        simpa using (congrFun (S.g.1.naturality I.f.op) σE).symm
    _ = S.g.1.app (op I.Y) (x I).1 := by rw [hσE I]
    _ = constantIntegerSheafOne (op I.Y) := (x I).2
    _ =
      (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.map I.f.op
        (constantIntegerSheafOne (op U)) := by
        symm
        exact constantIntegerSheafOne_naturality I.f.op

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.4.3: the quotient map in the extension is locally surjective because it
is an epimorphism of sheaves. -/
private theorem extension_quotient_isLocallySurjective
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf) :
    Sheaf.IsLocallySurjective S.g := by
  let Sseq : ShortComplex (Sheaf J AddCommGrpCat.{max u v}) :=
    ShortComplex.cokernelSequence S.g
  have hloc :
      ∀ (U : C)
        (s : (((constantIntegerSheaf) : Sheaf J AddCommGrpCat.{max u v})).1.obj (op U)),
        Sseq.g.hom.app (op U) s = 0 →
          ∃ T : J.Cover U, ∀ I : T.Arrow,
            ∃ t : S.E.1.obj (op I.Y), S.g.1.app (op I.Y) t = Sseq.X₂.obj.map I.f.op s :=
    (ShortComplex.exact_iff_locally_surjective_sections (J := J) (S := Sseq)).1 <|
      by simpa [Sseq] using (ShortComplex.cokernelSequence_exact S.g)
  change Presheaf.IsLocallySurjective J S.g.hom
  refine ⟨?_⟩
  intro U s
  let _ : HasCokernel S.g := Limits.HasCokernels.has_colimit S.g
  obtain ⟨T, hT⟩ := hloc U s (by
    simpa [Sseq] using
      congrArg
        (fun k : constantIntegerSheaf ⟶ cokernel S.g ↦ k.1.app (op U) s)
        (cokernel.π_of_epi S.g))
  refine J.superset_covering ?_ T.condition
  intro V f hf
  let I : T.Arrow := ⟨V, f, hf⟩
  rcases hT I with ⟨t, ht⟩
  exact ⟨t, by simpa [Sseq] using ht⟩

/-- Helper for Lemma 21.4.3: the distinguished section `1` admits local lifts along the
epimorphism `S.g`. -/
private theorem extensionLiftCarrier_locallyNonempty_cover
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C) :
    ∃ T : J.Cover U, ∀ I : T.Arrow,
      Nonempty ((extensionLiftCarrierPresheaf H S).obj (op I.Y)) := by
  let _ : Sheaf.IsLocallySurjective S.g := extension_quotient_isLocallySurjective H S
  have hImage :
      Presheaf.imageSieve S.g.hom (constantIntegerSheafOne (op U)) ∈ J U :=
    Presheaf.imageSieve_mem J S.g.hom (constantIntegerSheafOne (op U))
  let T : J.Cover U :=
    ⟨Presheaf.imageSieve S.g.hom (constantIntegerSheafOne (op U)), hImage⟩
  -- Use the image-sieve cover of the distinguished section `1`; each arrow comes with a chosen
  -- local preimage, and `app_localPreimage` identifies its image with the restricted section.
  refine ⟨T, ?_⟩
  intro I
  refine ⟨⟨Presheaf.localPreimage S.g.hom (constantIntegerSheafOne (op U)) I.f I.hf, ?_⟩⟩
  simpa [constantIntegerSheafOne_naturality I.f.op] using
    Presheaf.app_localPreimage S.g.hom (constantIntegerSheafOne (op U)) I.f I.hf

/-- Helper for Lemma 21.4.3: the fixed fiber of `S.g` over the distinguished section `1`
inherits the sheaf condition from the middle term of the extension. -/
private theorem extensionLiftCarrier_isSheaf
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf) :
    Presheaf.IsSheaf J (extensionLiftCarrierPresheaf H S) := by
  -- Route correction: instead of fighting the low-level `Presheaf.IsSheaf` interface directly on
  -- the subtype presheaf, move to the equivalent `Type`-valued sheaf condition and glue the
  -- underlying family in the middle sheaf `S.E`.
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.IsSeparated.isSheaf ?_ ?_
  · intro U T hT x y z hy hz
    -- Separatedness descends from the underlying sheaf of sections of `S.E`.
    apply Subtype.ext
    exact
      ((((sheafForget J).obj S.E).2.isSheafFor T hT).isSeparatedFor.ext
        (fun Y f hf ↦
          (congrArg Subtype.val (hy f hf)).trans (congrArg Subtype.val (hz f hf)).symm))
  · intro U T hT x hx
    let xE : Presieve.FamilyOfElements (((sheafForget J).obj S.E).1) T.arrows :=
      fun Y f hf ↦ (x f hf).1
    have hxE : xE.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomp
      exact congrArg Subtype.val (hx g₁ g₂ hf₁ hf₂ hcomp)
    rcases (((sheafForget J).obj S.E).2.isSheafFor T hT) xE hxE with ⟨σE, hσE, -⟩
    refine ⟨⟨σE, ?_⟩, ?_⟩
    · -- The glued underlying section still maps to the distinguished quotient section `1`.
      exact
        extensionLiftCarrier_amalgamation_mem H S U ⟨T, hT⟩ (fun I ↦ x I.f I.hf) σE
          (fun I ↦ by simpa [xE] using hσE I.f I.hf)
    · intro Y f hf
      -- The subtype amalgamation is inherited from the underlying amalgamation in `S.E`.
      apply Subtype.ext
      simpa [xE] using hσE f hf

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.4.3: evaluating the extension sequence on an object gives an exact
sequence of section groups. -/
private theorem extension_shortExact_app
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C) :
    (((S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})).map
        ((sheafToPresheaf J AddCommGrpCat.{max u v}) ⋙
          (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)))).Exact := by
  let G :=
    (sheafToPresheaf J AddCommGrpCat.{max u v}) ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  let T := ((S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})).map G)
  have hKernel : IsLimit (KernelFork.ofι T.f T.zero) := by
    -- Route correction: first move the sheaf kernel through forgetting and evaluation.
    simpa [G, T] using KernelFork.mapIsLimit _ S.shortExact.fIsKernel G
  exact T.exact_of_f_is_kernel hKernel

private noncomputable def extensionLiftCarrier
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf) :
    Sheaf J (Type (max u v)) :=
  ⟨extensionLiftCarrierPresheaf H S, extensionLiftCarrier_isSheaf H S⟩

omit [J.HasSheafCompose (forget AddCommGrpCat.{max u v})]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{max u v})] in
/-- Helper for Lemma 21.4.3: two sections of the middle term with the same image differ by a
unique section of the left term. -/
theorem Extension.section_transporter_existsUnique
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C)
    (t t' : S.E.1.obj (op U))
    (hEq : S.g.1.app (op U) t = S.g.1.app (op U) t') :
    ∃! h : H.1.obj (op U), S.f.1.app (op U) h + t' = t := by
  let G :=
    (sheafToPresheaf J AddCommGrpCat.{max u v}) ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{max u v}).obj (op U)
  let T := ((S : ShortComplex (Sheaf J AddCommGrpCat.{max u v})).map G)
  have hExact : T.Exact := by
    simpa [G, T] using extension_shortExact_app H S U
  let gHom := T.g.hom
  have hKer : t - t' ∈ gHom.ker := by
    -- The difference of two lifts of the same quotient section lies in the kernel of `S.g(U)`.
    change gHom (t - t') = 0
    have hEq' : gHom t = gHom t' := by
      simpa [G, T] using hEq
    calc
      gHom (t - t') = gHom t - gHom t' := by
        exact map_sub gHom t t'
      _ = 0 := by rw [hEq', sub_self]
  rw [← hExact.ab_range_eq_ker] at hKer
  rcases hKer with ⟨h, hh⟩
  refine ⟨h, ?_, ?_⟩
  · -- Rewrite the range witness as the desired transporter equation.
    have hh' : S.f.1.app (op U) h = t - t' := by
      simpa [G, T] using hh
    exact (eq_sub_iff_add_eq).mp hh'
  · intro h' hh'
    -- Injectivity of `S.f(U)` upgrades equality of differences to uniqueness of the transporter.
    have hinj : Function.Injective (S.f.1.app (op U)) :=
      (Sheaf.mono_iff_app_injective S.f).1 inferInstance U
    have hh₀ : S.f.1.app (op U) h = t - t' := by
      simpa [G, T] using hh
    have hh₁ : S.f.1.app (op U) h' = t - t' := (eq_sub_iff_add_eq).2 hh'
    exact hinj (hh₁.trans hh₀.symm)

/-- Helper for Lemma 21.4.3: adding an image section from `H` to a chosen lift stays in the fiber
over the distinguished section `1`. -/
private theorem extensionLiftTorsor_smul_mem
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C)
    (g : (Sheaf.toSheafOfGroups H).1.obj (op U))
    (t : (extensionLiftCarrier H S).1.obj (op U)) :
    S.g.1.app (op U) (S.f.1.app (op U) (show H.1.obj (op U) from g) + t.1) =
      constantIntegerSheafOne (op U) := by
  -- Apply `S.g` to the translated lift and use that `S.f ≫ S.g = 0`.
  have hz :
      S.g.1.app (op U) (S.f.1.app (op U) (show H.1.obj (op U) from g)) = 0 := by
    simpa using
      congrArg
        (fun k : H ⟶ constantIntegerSheaf ↦
          k.1.app (op U) (show H.1.obj (op U) from g))
        S.zero
  calc
    S.g.1.app (op U) (S.f.1.app (op U) (show H.1.obj (op U) from g) + t.1) =
        S.g.1.app (op U) (S.f.1.app (op U) (show H.1.obj (op U) from g)) +
          S.g.1.app (op U) t.1 := by
          simpa using
            (map_add (S.g.1.app (op U))
              (S.f.1.app (op U) (show H.1.obj (op U) from g)) t.1)
    _ = 0 + constantIntegerSheafOne (op U) := by rw [hz, t.2]
    _ = constantIntegerSheafOne (op U) := by simp

/-- Helper for Lemma 21.4.3: translating a chosen lift by a section of `H` produces the new lift
used in the extension-to-torsor construction. -/
private noncomputable def extensionLiftTranslate
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C)
    (g : (Sheaf.toSheafOfGroups H).1.obj (op U))
    (t : (extensionLiftCarrier H S).1.obj (op U)) :
    (extensionLiftCarrier H S).1.obj (op U) :=
  ⟨S.f.1.app (op U) (show H.1.obj (op U) from g) + t.1,
    extensionLiftTorsor_smul_mem H S U g t⟩

/-- Helper for Lemma 21.4.3: the lift action has the expected identity law. -/
private theorem extensionLiftTorsor_one_smul
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C)
    (t : (extensionLiftCarrier H S).1.obj (op U)) :
    extensionLiftTranslate H S U (1 : (Sheaf.toSheafOfGroups H).1.obj (op U)) t = t := by
  -- The multiplicative identity on the transported group is the additive zero of `H(U)`.
  apply Subtype.ext
  change S.f.1.app (op U) (0 : H.1.obj (op U)) + t.1 = t.1
  simp

/-- Helper for Lemma 21.4.3: the lift action is compatible with multiplication in the acting
group. -/
private theorem extensionLiftTorsor_mul_smul
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C)
    (g h : (Sheaf.toSheafOfGroups H).1.obj (op U))
    (t : (extensionLiftCarrier H S).1.obj (op U)) :
    extensionLiftTranslate H S U (g * h) t =
      extensionLiftTranslate H S U g (extensionLiftTranslate H S U h t) := by
  -- Both sides are the same after expanding the action to addition in the middle term.
  apply Subtype.ext
  change
    S.f.1.app (op U)
        ((show H.1.obj (op U) from g) + (show H.1.obj (op U) from h)) + t.1 =
      S.f.1.app (op U) (show H.1.obj (op U) from g) +
        (S.f.1.app (op U) (show H.1.obj (op U) from h) + t.1)
  simpa [map_add, add_assoc]

/-- Helper for Lemma 21.4.3: restriction maps commute with the lift action. -/
private theorem extensionLiftTorsor_act_naturality
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    {U V : C} (f : V ⟶ U)
    (g : (Sheaf.toSheafOfGroups H).1.obj (op U))
    (t : (extensionLiftCarrier H S).1.obj (op U)) :
    (extensionLiftCarrier H S).1.map f.op (extensionLiftTranslate H S U g t) =
      extensionLiftTranslate H S V ((Sheaf.toSheafOfGroups H).1.map f.op g)
        ((extensionLiftCarrier H S).1.map f.op t) := by
  -- Compare the two lifted sections after expanding the action to the middle sheaf.
  apply Subtype.ext
  change
    S.E.1.map f.op
        (S.f.1.app (op U) (show H.1.obj (op U) from g) + t.1) =
      S.f.1.app (op V) (H.1.map f.op (show H.1.obj (op U) from g)) +
        S.E.1.map f.op t.1
  calc
    S.E.1.map f.op
        (S.f.1.app (op U) (show H.1.obj (op U) from g) + t.1) =
      S.E.1.map f.op (S.f.1.app (op U) (show H.1.obj (op U) from g)) +
        S.E.1.map f.op t.1 := by
          simp
    _ =
      S.f.1.app (op V) (H.1.map f.op (show H.1.obj (op U) from g)) +
        S.E.1.map f.op t.1 := by
          rw [show S.E.1.map f.op (S.f.1.app (op U) (show H.1.obj (op U) from g)) =
              S.f.1.app (op V) (H.1.map f.op (show H.1.obj (op U) from g)) by
                exact
                  (ConcreteCategory.congr_hom (S.f.1.naturality f.op)
                    (show H.1.obj (op U) from g)).symm]

/-- Helper for Lemma 21.4.3: the translated lift determines its transporter uniquely because `S.f`
is monic. -/
private theorem extensionLiftTranslate_left_cancel
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf)
    (U : C)
    (g h : (Sheaf.toSheafOfGroups H).1.obj (op U))
    (t : (extensionLiftCarrier H S).1.obj (op U))
    (hEq : extensionLiftTranslate H S U g t = extensionLiftTranslate H S U h t) :
    g = h := by
  -- Forget the subtype equality, cancel the common lift, and use injectivity of `S.f(U)`.
  change (show H.1.obj (op U) from g) = (show H.1.obj (op U) from h)
  have hinj : Function.Injective (S.f.1.app (op U)) :=
    (Sheaf.mono_iff_app_injective S.f).1 inferInstance U
  have hval :
      S.f.1.app (op U) (show H.1.obj (op U) from g) + t.1 =
        S.f.1.app (op U) (show H.1.obj (op U) from h) + t.1 := by
    simpa [extensionLiftTranslate] using congrArg Subtype.val hEq
  apply hinj
  exact add_right_cancel hval

private noncomputable def extensionLiftTorsor
    (H : Sheaf J AddCommGrpCat.{max u v})
    (S : Extension H constantIntegerSheaf) :
    Sheaf.Torsor (Sheaf.toSheafOfGroups H) where
  carrier := extensionLiftCarrier H S
  mulAction U :=
    { smul := fun g t ↦ extensionLiftTranslate H S U g t
      one_smul := extensionLiftTorsor_one_smul H S U
      mul_smul := extensionLiftTorsor_mul_smul H S U }
  act_naturality := by
    intro U V f g t
    simpa using extensionLiftTorsor_act_naturality H S f g t
  isPretransitive := by
    intro U
    letI : MulAction ((Sheaf.toSheafOfGroups H).1.obj (op U))
        ((extensionLiftCarrier H S).1.obj (op U)) :=
      { smul := fun g t ↦ extensionLiftTranslate H S U g t
        one_smul := extensionLiftTorsor_one_smul H S U
        mul_smul := extensionLiftTorsor_mul_smul H S U }
    refine MulAction.IsPretransitive.mk ?_
    intro x y
    -- The unique difference between two lifts gives the group element carrying `x` to `y`.
    rcases Extension.section_transporter_existsUnique H S U y.1 x.1
        (y.2.trans x.2.symm) with ⟨h, hh, -⟩
    refine ⟨show (Sheaf.toSheafOfGroups H).1.obj (op U) from h, ?_⟩
    apply Subtype.ext
    simpa [extensionLiftTranslate] using hh
  isCancelSMul := by
    intro U
    letI : MulAction ((Sheaf.toSheafOfGroups H).1.obj (op U))
        ((extensionLiftCarrier H S).1.obj (op U)) :=
      { smul := fun g t ↦ extensionLiftTranslate H S U g t
        one_smul := extensionLiftTorsor_one_smul H S U
        mul_smul := extensionLiftTorsor_mul_smul H S U }
    refine IsCancelSMul.mk ?_
    intro g h t hEq
    exact extensionLiftTranslate_left_cancel H S U g h t hEq
  locallyNonempty := by
    intro U
    -- Use the source-faithful image-sieve cover of the distinguished section `1`.
    rcases extensionLiftCarrier_locallyNonempty_cover H S U with ⟨T, hT⟩
    refine ⟨T.1, T.2, ?_⟩
    intro V f hf
    let I : T.Arrow := ⟨V, f, hf⟩
    exact hT I

/-- Helper for Lemma 21.4.3: an endpoint-fixing isomorphism of extensions carries a chosen local
lift of `1` in `S` to a chosen local lift of `1` in `T`. -/
private theorem extensionLiftCarrier_transport_mem_of_extensionIso
    (H : Sheaf J AddCommGrpCat.{max u v})
    {S T : Extension H constantIntegerSheaf}
    (e : S.E ≅ T.E)
    (hg : e.hom ≫ T.g = S.g)
    (U : Cᵒᵖ)
    (t : (extensionLiftCarrier H S).1.obj U) :
    T.g.1.app U (e.hom.1.app U t.1) = constantIntegerSheafOne U := by
  -- Evaluate the endpoint compatibility `e.hom ≫ T.g = S.g` on the chosen lift and then use the
  -- defining fiber condition of `t`.
  have hcomp :
      T.g.1.app U (e.hom.1.app U t.1) = S.g.1.app U t.1 := by
    simpa using congrArg (fun k : S.E ⟶ constantIntegerSheaf ↦ k.1.app U t.1) hg
  exact hcomp.trans t.2

/-- Helper for Lemma 21.4.3: an endpoint-fixing isomorphism of extensions induces an isomorphism
of the fixed-fiber torsors of local lifts of `1`. -/
private theorem extensionLiftTorsor_isomorphic_of_isomorphic
    (H : Sheaf J AddCommGrpCat.{max u v})
    {S T : Extension H constantIntegerSheaf}
    (h : Extension.Isomorphic S T) :
    Nonempty (extensionLiftTorsor H S ≅ extensionLiftTorsor H T) := by
  classical
  rcases h with ⟨e, hf, hg⟩
  have hf_symm : T.f ≫ e.inv = S.f := by
    have hf' := congrArg (fun k ↦ k ≫ e.inv) hf
    simpa [Category.assoc] using hf'.symm
  have hg_symm : e.inv ≫ S.g = T.g := by
    have hg' := congrArg (fun k ↦ e.inv ≫ k) hg
    simpa [Category.assoc] using hg'.symm
  refine ⟨{ hom := ?_, inv := ?_, hom_inv_id := ?_, inv_hom_id := ?_ }⟩
  · -- Route correction: transport the fixed fiber across the middle-term isomorphism itself,
    -- rather than working only at the quotient `Nonempty` level.
    refine
      { hom :=
          ObjectProperty.homMk <|
            NatTrans.mk
              (fun U t ↦
                ⟨e.hom.1.app U t.1,
                  extensionLiftCarrier_transport_mem_of_extensionIso H e hg U t⟩)
              (fun U V f ↦ by
                funext t
                -- Naturality is exactly the naturality of the middle-term sheaf isomorphism.
                apply Subtype.ext
                change
                  e.hom.1.app V (S.E.1.map f t.1) =
                    T.E.1.map f (e.hom.1.app U t.1)
                simpa using ConcreteCategory.congr_hom (e.hom.1.naturality f) t.1)
        comm := ?_ }
    intro U g t
    -- Expand the translated lift and move the `H`-summand across `e.hom` using
    -- `S.f ≫ e.hom = T.f`.
    apply Subtype.ext
    have hf_app :
        e.hom.1.app (op U) (S.f.1.app (op U) (show H.1.obj (op U) from g)) =
          T.f.1.app (op U) (show H.1.obj (op U) from g) := by
      simpa using
        congrArg
          (fun k : H ⟶ T.E ↦
            k.1.app (op U) (show H.1.obj (op U) from g))
          hf
    calc
      e.hom.1.app (op U)
          (S.f.1.app (op U) (show H.1.obj (op U) from g) + t.1) =
        e.hom.1.app (op U) (S.f.1.app (op U) (show H.1.obj (op U) from g)) +
          e.hom.1.app (op U) t.1 := by
            simpa using
              map_add (e.hom.1.app (op U))
                (S.f.1.app (op U) (show H.1.obj (op U) from g)) t.1
      _ = T.f.1.app (op U) (show H.1.obj (op U) from g) + e.hom.1.app (op U) t.1 := by
        rw [hf_app]
  · refine
      { hom :=
          ObjectProperty.homMk <|
            NatTrans.mk
              (fun U t ↦
                ⟨e.inv.1.app U t.1,
                  extensionLiftCarrier_transport_mem_of_extensionIso H e.symm
                    hg_symm U t⟩)
              (fun U V f ↦ by
                funext t
                -- Naturality is again inherited from the inverse middle-term isomorphism.
                apply Subtype.ext
                change
                  e.inv.1.app V (T.E.1.map f t.1) =
                    S.E.1.map f (e.inv.1.app U t.1)
                simpa using ConcreteCategory.congr_hom (e.inv.1.naturality f) t.1)
        comm := ?_ }
    intro U g t
    apply Subtype.ext
    have hf_inv :
        e.inv.1.app (op U) (T.f.1.app (op U) (show H.1.obj (op U) from g)) =
          S.f.1.app (op U) (show H.1.obj (op U) from g) := by
      simpa using
        congrArg
          (fun k : H ⟶ S.E ↦
            k.1.app (op U) (show H.1.obj (op U) from g))
          hf_symm
    calc
      e.inv.1.app (op U)
          (T.f.1.app (op U) (show H.1.obj (op U) from g) + t.1) =
        e.inv.1.app (op U) (T.f.1.app (op U) (show H.1.obj (op U) from g)) +
          e.inv.1.app (op U) t.1 := by
            simpa using
              map_add (e.inv.1.app (op U))
                (T.f.1.app (op U) (show H.1.obj (op U) from g)) t.1
      _ = S.f.1.app (op U) (show H.1.obj (op U) from g) + e.inv.1.app (op U) t.1 := by
        rw [hf_inv]
  · -- The objectwise composites are identity maps because `e.inv.app ∘ e.hom.app = id`.
    refine Hom.ext ?_
    intro U t
    apply Subtype.ext
    change e.inv.1.app (op U) (e.hom.1.app (op U) t.1) = t.1
    -- Evaluate the middle-term identity `e.hom ≫ e.inv = 𝟙` on the chosen lift.
    have happ :
        (e.hom ≫ e.inv).1.app (op U) =
          (show S.E ⟶ S.E from 𝟙 S.E).1.app (op U) := by
      exact congrArg (fun k : S.E ⟶ S.E ↦ k.1.app (op U)) e.hom_inv_id
    change (ConcreteCategory.hom ((e.hom ≫ e.inv).1.app (op U))) t.1 =
      (ConcreteCategory.hom ((show S.E ⟶ S.E from 𝟙 S.E).1.app (op U))) t.1
    exact ConcreteCategory.congr_hom happ t.1
  · -- The dual objectwise composite is also the identity.
    refine Hom.ext ?_
    intro U t
    apply Subtype.ext
    change e.hom.1.app (op U) (e.inv.1.app (op U) t.1) = t.1
    -- Evaluate the middle-term identity `e.inv ≫ e.hom = 𝟙` on the chosen lift.
    have happ :
        (e.inv ≫ e.hom).1.app (op U) =
          (show T.E ⟶ T.E from 𝟙 T.E).1.app (op U) := by
      exact congrArg (fun k : T.E ⟶ T.E ↦ k.1.app (op U)) e.inv_hom_id
    change (ConcreteCategory.hom ((e.inv ≫ e.hom).1.app (op U))) t.1 =
      (ConcreteCategory.hom ((show T.E ⟶ T.E from 𝟙 T.E).1.app (op U))) t.1
    exact ConcreteCategory.congr_hom happ t.1

private abbrev underlyingAddTypeSheaf
    (H : Sheaf J AddCommGrpCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafForget J).obj H

private abbrev freeAbelianSheaf
    (𝒢 : Sheaf J (Type (max u v))) :
    Sheaf J AddCommGrpCat.{max u v} :=
  (Sheaf.composeAndSheafify J AddCommGrpCat.free).obj 𝒢

private noncomputable def freeAbelianSheafLift
    {𝒢 : Sheaf J (Type (max u v))}
    {𝒜 : Sheaf J AddCommGrpCat.{max u v}}
    (f : 𝒢 ⟶ (sheafForget J).obj 𝒜) :
    freeAbelianSheaf 𝒢 ⟶ 𝒜 :=
  ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv 𝒢 𝒜).symm f

/-- Helper for Lemma 21.4.3: the product presheaf of sections of `H` and local torsor sections is
a sheaf of types. -/
private theorem torsorRelationSource_isSheaf
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    Presheaf.IsSheaf J
      { obj := fun U ↦ H.1.obj U × P.carrier.1.obj U
        map := fun f x ↦ (H.1.map f x.1, P.carrier.1.map f x.2)
        map_id := by
          intro U
          funext x
          cases x
          simp
        map_comp := by
          intro U V W f g
          funext x
          cases x
          simp } := by
  -- Route correction: prove the product sheaf condition componentwise instead of keeping an
  -- inline proof field inside the `torsorRelationSource` definition.
  rw [isSheaf_iff_isSheaf_of_type]
  refine Presieve.IsSeparated.isSheaf ?_ ?_
  · intro U T hT x y z hy hz
    ext
    · exact
        ((((underlyingAddTypeSheaf H).2.isSheafFor T hT).isSeparatedFor.ext
          (fun Y f hf ↦
            (congrArg (fun p ↦ p.1) (hy f hf)).trans
              (congrArg (fun p ↦ p.1) (hz f hf)).symm)))
    · exact
        ((((P.carrier).2.isSheafFor T hT).isSeparatedFor.ext
          (fun Y f hf ↦
            (congrArg (fun p ↦ p.2) (hy f hf)).trans
              (congrArg (fun p ↦ p.2) (hz f hf)).symm)))
  · intro U T hT x hx
    let xH : Presieve.FamilyOfElements (underlyingAddTypeSheaf H).1 T.arrows :=
      fun Y f hf ↦ (x f hf).1
    let xP : Presieve.FamilyOfElements P.carrier.1 T.arrows :=
      fun Y f hf ↦ (x f hf).2
    have hxH : xH.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomp
      exact congrArg (fun p ↦ p.1) (hx g₁ g₂ hf₁ hf₂ hcomp)
    have hxP : xP.Compatible := by
      intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ hcomp
      exact congrArg (fun p ↦ p.2) (hx g₁ g₂ hf₁ hf₂ hcomp)
    rcases ((underlyingAddTypeSheaf H).2.isSheafFor T hT) xH hxH with ⟨σH, hσH, -⟩
    rcases ((P.carrier).2.isSheafFor T hT) xP hxP with ⟨σP, hσP, -⟩
    refine ⟨(σH, σP), ?_⟩
    intro Y f hf
    ext
    · simpa [xH] using hσH f hf
    · simpa [xP] using hσP f hf

private abbrev torsorRelationSource
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    Sheaf J (Type (max u v)) :=
  ⟨{ obj := fun U ↦ H.1.obj U × P.carrier.1.obj U
     map := fun f x ↦ (H.1.map f x.1, P.carrier.1.map f x.2)
     map_id := by
       intro U
       funext x
       cases x
       simp
     map_comp := by
       intro U V W f g
       funext x
       cases x
       simp },
    torsorRelationSource_isSheaf H P⟩

private def torsorRelationFst
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    torsorRelationSource H P ⟶ underlyingAddTypeSheaf H :=
  { hom :=
      { app := fun U x ↦ x.1
        naturality := by
          intro U V f
          funext x
          rfl } }

private def torsorRelationSnd
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    torsorRelationSource H P ⟶ P.carrier :=
  { hom :=
      { app := fun U x ↦ x.2
        naturality := by
          intro U V f
          funext x
          rfl } }

private noncomputable def torsorActionUnderlying
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    torsorRelationSource H P ⟶ P.carrier :=
  { hom :=
      { app := fun U x ↦
          let g : (Sheaf.toSheafOfGroups H).1.obj U :=
            show H.1.obj U from (torsorRelationFst H P).hom.app U x
          let p : P.Sections (unop U) :=
            (torsorRelationSnd H P).hom.app U x
          show P.carrier.1.obj U from g • p
        naturality := by
          intro U V f
          ext x
          have hfst :
              (torsorRelationFst H P).hom.app V
                  ((torsorRelationSource H P).obj.map f x) =
                H.1.map f
                  ((torsorRelationFst H P).hom.app U x) := by
            rfl
          have hsnd :
              (torsorRelationSnd H P).hom.app V
                  ((torsorRelationSource H P).obj.map f x) =
                P.carrier.1.map f
                  ((torsorRelationSnd H P).hom.app U x) := by
            rfl
          dsimp
          rw [hfst, hsnd]
          simpa using
            (P.act_naturality f.unop
              (show (Sheaf.toSheafOfGroups H).1.obj U from
                (torsorRelationFst H P).hom.app U x)
              ((torsorRelationSnd H P).hom.app U x)).symm } }

private noncomputable def torsorToConstantIntegerUnderlying
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    P.carrier ⟶ (sheafForget J).obj (constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v}) :=
  { hom := {
      app := fun U _ ↦ constantIntegerSheafOne U
      naturality := by
        intro U V f
        ext x
        simpa using (constantIntegerSheafOne_naturality f).symm
    } }

private noncomputable def torsorLinearization
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    Sheaf J AddCommGrpCat.{max u v} :=
  freeAbelianSheaf P.carrier

private noncomputable def torsorRelation
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    freeAbelianSheaf (torsorRelationSource H P) ⟶
      H ⊞ torsorLinearization H P :=
  freeAbelianSheafLift (torsorRelationFst H P) ≫ biprod.inl +
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map
        (torsorRelationSnd H P) ≫
      biprod.inr -
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorActionUnderlying H P) ≫
      biprod.inr

private noncomputable def torsorLinearizationAugmentation
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    torsorLinearization H P ⟶ constantIntegerSheaf :=
  freeAbelianSheafLift (torsorToConstantIntegerUnderlying H P)

private theorem torsorToConstantIntegerUnderlying_comp_eq
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    torsorRelationSnd H P ≫ torsorToConstantIntegerUnderlying H P =
      torsorActionUnderlying H P ≫ torsorToConstantIntegerUnderlying H P := by
  ext U x
  rfl

private theorem torsorLinearization_relation_eq
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorRelationSnd H P) ≫
        torsorLinearizationAugmentation H P =
      (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorActionUnderlying H P) ≫
        torsorLinearizationAugmentation H P := by
  rw [torsorLinearizationAugmentation, freeAbelianSheafLift]
  rw [← (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv_naturality_left_symm
      (torsorRelationSnd H P) (torsorToConstantIntegerUnderlying H P)]
  rw [← (Sheaf.adjunction J AddCommGrpCat.adj).homEquiv_naturality_left_symm
      (torsorActionUnderlying H P) (torsorToConstantIntegerUnderlying H P)]
  exact congrArg
    (fun k ↦
      ((Sheaf.adjunction J AddCommGrpCat.adj).homEquiv
        (torsorRelationSource H P)
        (constantIntegerSheaf : Sheaf J AddCommGrpCat.{max u v})).symm k)
    (torsorToConstantIntegerUnderlying_comp_eq H P)

private theorem torsorRelation_comp_desc_zero
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    torsorRelation H P ≫ biprod.desc 0 (torsorLinearizationAugmentation H P) = 0 := by
  unfold torsorRelation
  let a : freeAbelianSheaf (torsorRelationSource H P) ⟶ H ⊞ torsorLinearization H P :=
    freeAbelianSheafLift (torsorRelationFst H P) ≫ biprod.inl
  let b : freeAbelianSheaf (torsorRelationSource H P) ⟶ H ⊞ torsorLinearization H P :=
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorRelationSnd H P) ≫ biprod.inr
  let c : freeAbelianSheaf (torsorRelationSource H P) ⟶ H ⊞ torsorLinearization H P :=
    (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorActionUnderlying H P) ≫ biprod.inr
  change (a + b - c) ≫ biprod.desc 0 (torsorLinearizationAugmentation H P) = 0
  rw [sub_eq_add_neg, Preadditive.add_comp, Preadditive.add_comp, Preadditive.neg_comp]
  have ha : a ≫ biprod.desc 0 (torsorLinearizationAugmentation H P) = 0 := by
    dsimp [a]
    simp [Category.assoc]
    rfl
  have hbc : b ≫ biprod.desc 0 (torsorLinearizationAugmentation H P) =
      c ≫ biprod.desc 0 (torsorLinearizationAugmentation H P) := by
    dsimp [b, c]
    calc
      (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorRelationSnd H P) ≫
          biprod.inr ≫ biprod.desc 0 (torsorLinearizationAugmentation H P) =
        (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorRelationSnd H P) ≫
          torsorLinearizationAugmentation H P := by
            simp
      _ =
        (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorActionUnderlying H P) ≫
          torsorLinearizationAugmentation H P := torsorLinearization_relation_eq H P
      _ =
        (Sheaf.composeAndSheafify J AddCommGrpCat.free).map (torsorActionUnderlying H P) ≫
          biprod.inr ≫ biprod.desc 0 (torsorLinearizationAugmentation H P) := by
            simp
  rw [ha, hbc]
  rw [zero_add]
  rw [← sub_eq_add_neg]
  exact sub_self (c ≫ biprod.desc 0 (torsorLinearizationAugmentation H P))

/-- Helper for Lemma 21.4.3: the cokernel-desc map defining `torsorExtension` kills the image of
the left summand because `biprod.desc 0 _` vanishes on `biprod.inl`. -/
private theorem torsorExtensionZero
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H))
    [HasCokernel (torsorRelation H P)] :
    (biprod.inl : H ⟶ H ⊞ torsorLinearization H P) ≫
        cokernel.π (torsorRelation H P) ≫
        cokernel.desc (torsorRelation H P)
          (biprod.desc 0 (torsorLinearizationAugmentation H P))
          (torsorRelation_comp_desc_zero H P) =
      0 := by
  -- Push the composite through `cokernel.desc`; the remaining left-summand composite is
  -- definitionally zero for the chosen biproduct descendant.
  have hdesc :
      (biprod.inl : H ⟶ H ⊞ torsorLinearization H P) ≫
          (cokernel.π (torsorRelation H P) ≫
            cokernel.desc (torsorRelation H P)
              (biprod.desc 0 (torsorLinearizationAugmentation H P))
              (torsorRelation_comp_desc_zero H P)) =
        (biprod.inl : H ⟶ H ⊞ torsorLinearization H P) ≫
          biprod.desc 0 (torsorLinearizationAugmentation H P) := by
    simpa using
      congrArg
        (fun k ↦ (biprod.inl : H ⟶ H ⊞ torsorLinearization H P) ≫ k)
        (cokernel.π_desc (torsorRelation H P)
          (biprod.desc 0 (torsorLinearizationAugmentation H P))
          (torsorRelation_comp_desc_zero H P))
  calc
    (biprod.inl : H ⟶ H ⊞ torsorLinearization H P) ≫
        cokernel.π (torsorRelation H P) ≫
        cokernel.desc (torsorRelation H P)
          (biprod.desc 0 (torsorLinearizationAugmentation H P))
          (torsorRelation_comp_desc_zero H P) =
      (biprod.inl : H ⟶ H ⊞ torsorLinearization H P) ≫
        biprod.desc 0 (torsorLinearizationAugmentation H P) := by
          simpa [Category.assoc] using hdesc
    _ = 0 := by simp

/-- Helper for Lemma 21.4.3: the presentation attached to a torsor is short exact once local
kernel sections of the augmentation are rewritten as torsor-relation generators. -/
private theorem torsorExtensionShortExact
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H))
    [HasCokernel (torsorRelation H P)] :
    (ShortComplex.mk
      (biprod.inl ≫ cokernel.π (torsorRelation H P))
      (cokernel.desc (torsorRelation H P)
        (biprod.desc 0 (torsorLinearizationAugmentation H P))
        (torsorRelation_comp_desc_zero H P))
      (torsorExtensionZero H P)).ShortExact := by
  admit

private noncomputable def torsorExtension
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    Extension H constantIntegerSheaf :=
  let r : freeAbelianSheaf (torsorRelationSource H P) ⟶ H ⊞ torsorLinearization H P :=
    torsorRelation H P
  let q : H ⊞ torsorLinearization H P ⟶ constantIntegerSheaf :=
    biprod.desc 0 (torsorLinearizationAugmentation H P)
  letI : HasCokernel r := Limits.HasCokernels.has_colimit r
  { E := cokernel r
    f := biprod.inl ≫ cokernel.π r
    g :=
      cokernel.desc r q
        (torsorRelation_comp_desc_zero H P)
    zero := by
      -- The zero field is exactly the normalization proved once in `torsorExtensionZero`.
      simpa [r, q] using torsorExtensionZero H P
    shortExact := by
      -- Delegate the real exactness argument to the named helper lemma.
      simpa [r, q] using torsorExtensionShortExact H P }

private theorem torsorExtension_isomorphic_of_iso
    (H : Sheaf J AddCommGrpCat.{max u v})
    {P Q : Sheaf.Torsor (Sheaf.toSheafOfGroups H)} (e : P ≅ Q) :
    Extension.Isomorphic (torsorExtension H P) (torsorExtension H Q) := by
  admit

/-- Helper for Lemma 21.4.3: the canonical comparison map from isomorphism classes of
`H`-torsors on `(C, J)` to `H¹(C, H)`, defined by the extension class attached to a torsor. -/
@[stacks 03AJ]
noncomputable def abelianSheafTorsor_isoClasses_to_H1
    (H : Sheaf J AddCommGrpCat.{max u v}) :
    Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups H) → H.H 1 :=
  _root_.Quotient.lift
    (fun P : Sheaf.Torsor (Sheaf.toSheafOfGroups H) ↦
      ExtensionClass.toExt (⟦torsorExtension H P⟧ : ExtensionClass H constantIntegerSheaf))
    (fun P Q hPQ ↦
      hPQ.elim fun e ↦ by
        change
          ExtensionClass.toExt (⟦torsorExtension H P⟧ : ExtensionClass H constantIntegerSheaf) =
            ExtensionClass.toExt (⟦torsorExtension H Q⟧ : ExtensionClass H constantIntegerSheaf)
        exact congrArg ExtensionClass.toExt
          (ExtensionClass.mk_eq_mk_of_isomorphic (torsorExtension_isomorphic_of_iso H e)))

/-- On a representative torsor, the comparison map is the `Ext¹` class of the associated
extension of the constant integer sheaf by `H`. -/
@[simp] theorem abelianSheafTorsor_isoClasses_to_H1_apply_mk
    (H : Sheaf J AddCommGrpCat.{max u v})
    (P : Sheaf.Torsor (Sheaf.toSheafOfGroups H)) :
    abelianSheafTorsor_isoClasses_to_H1 H (_root_.Quotient.mk'' P) =
      ExtensionClass.toExt (⟦torsorExtension H P⟧ : ExtensionClass H constantIntegerSheaf) :=
  rfl

/-- The canonical comparison sends the trivial torsor class to `0 ∈ H¹(C, H)`. -/
@[simp] theorem abelianSheafTorsor_isoClasses_to_H1_trivial
    (H : Sheaf J AddCommGrpCat.{max u v}) :
    abelianSheafTorsor_isoClasses_to_H1 H
        (_root_.Quotient.mk'' (Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups H))) = 0 := by
  admit

/-- Lemma 21.4.3: the canonical comparison from `H`-torsor classes on `(C, J)` to `H¹(C, H)` is
a bijection. -/
@[stacks 03AJ]
theorem abelianSheafTorsor_isoClasses_to_H1_bijective
    (H : Sheaf J AddCommGrpCat.{max u v}) :
    Function.Bijective (abelianSheafTorsor_isoClasses_to_H1 H) := by
  admit

/-- Lemma 21.4.3, equivalence form: there exists an equivalence between isomorphism classes of
`H`-torsors and `H¹(C, H)` carrying the trivial torsor class to `0`. This remains theorem-level so
the public data owner is the canonical comparison map itself. -/
@[stacks 03AJ]
theorem abelianSheafTorsor_isoClasses_equiv_H1
    (H : Sheaf J AddCommGrpCat.{max u v}) :
    ∃ e : Sheaf.Torsor.IsoClasses (Sheaf.toSheafOfGroups H) ≃ H.H 1,
      e (_root_.Quotient.mk'' (Sheaf.Torsor.trivial (Sheaf.toSheafOfGroups H))) = 0 := by
  refine ⟨Equiv.ofBijective (abelianSheafTorsor_isoClasses_to_H1 H)
      (abelianSheafTorsor_isoClasses_to_H1_bijective H), ?_⟩
  exact abelianSheafTorsor_isoClasses_to_H1_trivial H

end CategoryTheory
