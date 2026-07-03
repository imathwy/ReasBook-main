import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_17_5_1 (from Chap17) -/
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry

section

variable {X : TopCat.{u}}
variable {U : Opens X}

/-- The support of a local section of an abelian sheaf over an open set `U` is the set of points
of `U` where the germ is nonzero. -/
def abelianSheafSectionSupport (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op U)) :
    Set U :=
  { x | ℱ.presheaf.germ U x.1 x.2 s ≠ 0 }

/-- Membership in the support of a local section of an abelian sheaf is nonvanishing of its germ.
-/
@[simp] theorem mem_abelianSheafSectionSupport_iff
    (ℱ : X.Sheaf AddCommGrpCat.{u}) (s : ℱ.presheaf.obj (op U)) (x : U) :
    x ∈ abelianSheafSectionSupport ℱ s ↔ ℱ.presheaf.germ U x.1 x.2 s ≠ 0 := by
  rfl

/-- Definition 17.5.1: the support of an abelian sheaf on `X` is the set of points where the
stalk is nonzero. This is the canonical support owner; module support below is its specialization
along `SheafOfModules.toSheaf`. -/
def abelianSheafSupport (ℱ : X.Sheaf AddCommGrpCat.{u}) : Set X :=
  { x | ¬ IsZero (ℱ.presheaf.stalk x) }

/-- Membership in the support of an abelian sheaf is nonvanishing of the stalk. -/
@[simp] theorem mem_abelianSheafSupport_iff (ℱ : X.Sheaf AddCommGrpCat.{u}) (x : X) :
    x ∈ abelianSheafSupport ℱ ↔ ¬ IsZero (ℱ.presheaf.stalk x) := by
  rfl

end

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}

/-- Definition 17.5.1: the support of a sheaf of rings on `X` is the support of its canonical
underlying additive sheaf. -/
abbrev ringSheafSupport (ℱ : X.Sheaf RingCat.{u}) : Set X :=
  abelianSheafSupport
    ((sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj ℱ)

end

end TopCat.Sheaf

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}} {U : Opens X}

/-- The support of a local section of the structure sheaf is the set of points where its germ in
the stalk is nonzero. -/
def ringSectionSupport (f : X.presheaf.obj (op U)) : Set U :=
  { x | X.presheaf.germ U x.1 x.2 f ≠ 0 }

/-- Membership in the support of a local ring section is nonvanishing of its germ. -/
@[simp] theorem mem_ringSectionSupport_iff (f : X.presheaf.obj (op U)) (x : U) :
    x ∈ ringSectionSupport f ↔ X.presheaf.germ U x.1 x.2 f ≠ 0 := by
  rfl

end

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

section

variable {X : RingedSpace.{u}}
variable {ℱ : X.Modules}
variable {U : Opens X}

/-- Definition 17.5.1: the support of a section of an `\mathcal O_X`-module over an open set `U`
is the specialization of `abelianSheafSectionSupport` along
`SheafOfModules.toSheaf`. -/
abbrev moduleSectionSupport (s : ℱ.val.obj (op U)) : Set U :=
  abelianSheafSectionSupport ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) s

/-- Membership in the support of a local section is nonvanishing of its germ. -/
@[simp] theorem mem_moduleSectionSupport_iff (s : ℱ.val.obj (op U)) (x : U) :
    x ∈ moduleSectionSupport s ↔
      TopCat.Presheaf.germ (PresheafOfModules.presheaf ℱ.val) U x.1 x.2 s ≠ 0 := by
  rfl

/-- Definition 17.5.1: the support of an `\mathcal O_X`-module is the set of points where the
stalk is nonzero. This is the support of its canonical underlying additive sheaf. -/
abbrev moduleSupport (ℱ : X.Modules) : Set X :=
  abelianSheafSupport ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ)

/-- Membership in the support of an `\mathcal O_X`-module is existence of a nonzero stalk
element. -/
@[simp] theorem mem_moduleSupport_iff
    (ℱ : X.Modules) (x : X) :
    x ∈ moduleSupport ℱ ↔ ∃ m : ↑(RingedSpace.stalkModuleCat ℱ x), m ≠ 0 := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ
  have hmem :
      x ∈ moduleSupport ℱ ↔
        ¬ IsZero (TopCat.Presheaf.stalk (PresheafOfModules.presheaf ℱ.val) x) := by
    change x ∈ abelianSheafSupport F ↔
      ¬ IsZero (TopCat.Presheaf.stalk (TopCat.Sheaf.presheaf F) x)
    exact mem_abelianSheafSupport_iff F x
  rw [hmem]
  rw [AddCommGrpCat.isZero_iff_subsingleton, not_subsingleton_iff_nontrivial]
  change Nontrivial ↑(RingedSpace.stalkModuleCat ℱ x) ↔
    ∃ m : ↑(RingedSpace.stalkModuleCat ℱ x), m ≠ 0
  rw [nontrivial_iff_exists_ne (0 : ↑(RingedSpace.stalkModuleCat ℱ x))]

end

end AlgebraicGeometry

/-! ### Lemma_17_5_2 (from Chap17) -/
open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X : TopCat.{u}}
variable {ℱ 𝒢 : X.Sheaf AddCommGrpCat.{u}}
variable {U : Opens X}

local notation "F" => ℱ.presheaf
local notation "G" => 𝒢.presheaf

/- Domain-style sampling for Lemma 17.5.2:
- primary domain: support of local sections and of sheaves, detected stalkwise by germs in the
  underlying additive sheaf;
- sampled owner declarations:
  `abelianSheafSectionSupport`,
  `abelianSheafSupport`,
  `moduleSectionSupport`,
  `moduleSupport`;
- best owner abstraction: clauses `(1)`, `(3)`, `(4)`, and `(5)` belong to the additive-sheaf
  owners `abelianSheafSectionSupport` and `abelianSheafSupport`; the module notions are their
  specializations from `Definition_17_5_1`;
- primitive data: an abelian sheaf `ℱ`, a local section `s`, and a sheaf morphism `φ : ℱ ⟶ 𝒢`;
- derived API: closedness of section support, compatibility with addition and morphisms, and the
  union description of sheaf support.

Source/core/bridge triage:
- `source-facing`: the five support properties in Lemma 17.5.2;
- `core/canonical`: `abelianSheafSectionSupport` and `abelianSheafSupport`;
- `bridge/view`: the module specializations `moduleSectionSupport` and `moduleSupport`, with the
  scalar-support clause `(2)` staying at that genuinely module-specific layer. -/

-- Proof sketch: if the germ of `s` vanishes at `x`, then by the stalk criterion there is an open
-- neighbourhood inside `U` on which `s` restricts to zero. Hence the complement of the support is
-- open in `U`, so the support is closed in the subspace topology.
/-- Lemma 17.5.2 (1): the support of a section of an abelian sheaf over an open set `U` is closed
in `U`. The module statement is its specialization to the underlying additive sheaf. -/
theorem isClosed_abelianSheafSectionSupport (s : ℱ.presheaf.obj (op U)) :
    IsClosed (abelianSheafSectionSupport ℱ s) := by
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.2 fun x hx ↦ ?_
  have hx_not_mem : x ∉ abelianSheafSectionSupport ℱ s := by
    simpa [Set.mem_compl_iff] using hx
  have hx0' : germ F U x.1 x.2 s = 0 := by
    simpa using hx_not_mem
  have hx0 :
      germ F U x.1 x.2 s =
        germ F U x.1 x.2 0 := by
    calc
      germ F U x.1 x.2 s = 0 := hx0'
      _ = germ F U x.1 x.2 0 := by
        exact ((germ F U x.1 x.2).hom.map_zero).symm
  obtain ⟨V, hxV, i₁, i₂, hsV⟩ :=
    germ_eq F x.1 x.2 x.2 s 0 hx0
  have hi : i₂ = i₁ := Subsingleton.elim _ _
  have hsV' : ℱ.presheaf.map i₁.op s = 0 := by
    rw [hi] at hsV
    calc
      ℱ.presheaf.map i₁.op s = ℱ.presheaf.map i₁.op 0 := hsV
      _ = 0 := by
        exact (ℱ.presheaf.map i₁.op).hom.map_zero
  refine Filter.mem_of_superset ((V.2.preimage continuous_subtype_val).mem_nhds hxV) ?_
  intro y hy
  have hy0 : germ F U y.1 y.2 s = 0 := by
    calc
      germ F U y.1 y.2 s =
          germ F V y.1 hy (ℱ.presheaf.map i₁.op s) := by
            symm
            exact germ_res_apply F i₁ y.1 hy s
      _ = germ F V y.1 hy 0 := by rw [hsV']
      _ = 0 := by simp
  have hy_not_mem : y ∉ abelianSheafSectionSupport ℱ s := by
    simpa using hy0
  simpa [Set.mem_compl_iff] using hy_not_mem

-- Proof sketch: taking germs commutes with addition. If both germs of `s` and `s'` vanish at a
-- point, then the germ of `s + s'` also vanishes there, so any point of the support of `s + s'`
-- must lie in the support of `s` or in the support of `s'`.
/-- Lemma 17.5.2 (3): the support of `s + s'` is contained in the union of the supports of `s`
and `s'`. -/
theorem add_abelianSheafSectionSupport_subset_union
    (s s' : ℱ.presheaf.obj (op U)) :
    abelianSheafSectionSupport ℱ (s + s') ⊆
      abelianSheafSectionSupport ℱ s ∪ abelianSheafSectionSupport ℱ s' := by
  intro x hx
  by_cases hs : x ∈ abelianSheafSectionSupport ℱ s
  · exact Or.inl hs
  · right
    by_contra hs'
    have hs0 : germ F U x.1 x.2 s = 0 := by
      simpa using hs
    have hs'0 : germ F U x.1 x.2 s' = 0 := by
      simpa using hs'
    apply hx
    simp [hs0, hs'0]

-- Proof sketch: a point is in the sheaf support exactly when its stalk contains a nonzero germ,
-- and every stalk element is represented by a local section on some neighbourhood. Therefore the
-- support is exactly the union of the supports of all local sections.
/-- Lemma 17.5.2 (4): the support of an abelian sheaf is the union of the supports of all its
local sections. The module statement is the specialization along `SheafOfModules.toSheaf`. -/
theorem abelianSheafSupport_eq_iUnion_abelianSheafSectionSupport :
    abelianSheafSupport ℱ =
      ⋃ (U : Opens X) (s : ℱ.presheaf.obj (op U)),
        Subtype.val '' abelianSheafSectionSupport ℱ s := by
  ext x
  constructor
  · intro hx
    rw [mem_abelianSheafSupport_iff, AddCommGrpCat.isZero_iff_subsingleton,
      not_subsingleton_iff_nontrivial,
      nontrivial_iff_exists_ne (0 : ℱ.presheaf.stalk x)] at hx
    obtain ⟨t, ht⟩ := hx
    obtain ⟨U, hxU, s, rfl⟩ := ℱ.presheaf.germ_exist x t
    refine Set.mem_iUnion.2 ⟨U, Set.mem_iUnion.2 ⟨s, ?_⟩⟩
    refine ⟨⟨x, hxU⟩, ?_, rfl⟩
    simpa using ht
  · intro hx
    rcases Set.mem_iUnion.1 hx with ⟨U, hx⟩
    rcases Set.mem_iUnion.1 hx with ⟨s, hx⟩
    rcases hx with ⟨y, hy, rfl⟩
    rw [mem_abelianSheafSupport_iff, AddCommGrpCat.isZero_iff_subsingleton]
    intro hsub
    letI : Subsingleton ↑(ℱ.presheaf.stalk y.1) := hsub
    exact (mem_abelianSheafSectionSupport_iff ℱ s y).1 hy (Subsingleton.elim _ _)

-- Proof sketch: the germ of `φ(s)` is the image of the germ of `s` under the induced map on
-- stalks. A zero germ maps to zero, so nonvanishing of `φ(s)` can only occur where the germ of
-- `s` is already nonzero.
/-- Lemma 17.5.2 (5): for a morphism of abelian sheaves, the support of the image section is
contained in the support of the original section. The module statement is its specialization to the
underlying additive sheaves. -/
theorem abelianSheafSectionSupport_map_subset
    (φ : ℱ ⟶ 𝒢) (s : ℱ.presheaf.obj (op U)) :
    abelianSheafSectionSupport 𝒢 (φ.1.app (op U) s) ⊆ abelianSheafSectionSupport ℱ s := by
  intro x hx
  rw [mem_abelianSheafSectionSupport_iff] at hx ⊢
  by_contra hs
  have hmap :
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x.1).map φ.1
        (germ F U x.1 x.2 s) = 0 := by
    rw [hs]
    exact map_zero _
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply U x.1 x.2 φ.1 s] at hmap
  exact hx hmap

end

section

variable {X : RingedSpace.{u}}
variable {ℱ : X.Modules}
variable {U : Opens X}

local notation "F" => ℱ.val.presheaf

-- Proof sketch: if the germ of `f • s` at a point is nonzero, then the germ of `s` is nonzero;
-- otherwise `germ(f • s) = germ(f) • germ(s)` would vanish. Likewise the germ of `f` must be
-- nonzero. Thus the support of `f • s` lies in the intersection of the two supports.
/-- Lemma 17.5.2 (2): the support of `f • s` is contained in the intersection of the supports of
`f` and `s`. This is the genuinely module-specific bridge clause of the lemma. -/
theorem smul_moduleSectionSupport_subset_inter
    (f : X.presheaf.obj (op U)) (s : ℱ.val.obj (op U)) :
    moduleSectionSupport (f • s) ⊆ RingedSpace.ringSectionSupport f ∩ moduleSectionSupport s := by
  intro x hx
  rw [mem_moduleSectionSupport_iff] at hx
  have hsmul :
      germ F U x.1 x.2 (f • s) =
        X.presheaf.germ U x.1 x.2 f • germ F U x.1 x.2 s := by
    simpa using PresheafOfModules.germ_smul ℱ.val x.1 U x.2 f s
  have hx' :
      X.presheaf.germ U x.1 x.2 f • germ F U x.1 x.2 s ≠ 0 := by
    intro hzero
    apply hx
    rw [hsmul]
    exact hzero
  constructor
  · by_contra hf
    have hf0 : X.presheaf.germ U x.1 x.2 f = 0 := by
      simpa using hf
    exact hx' <| by
      rw [hf0, zero_smul]
  · by_contra hs
    have hs0 : germ F U x.1 x.2 s = 0 := by
      simpa using hs
    exact hx' <| by
      rw [hs0, smul_zero]

end

end AlgebraicGeometry

/-! ### Lemma_17_5_3 (from Chap17) -/
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TopCat

noncomputable section

universe u

namespace TopCat.Sheaf

section

variable {X : TopCat.{u}}

/- Domain-style sampling for Lemma 17.5.3:
- primary domain: support of sheaves of rings on a topological space, detected stalkwise by the
  germ of the global unit section;
- sampled owner declarations:
  `ringSheafSupport`,
  `abelianSheafSupport`,
  `mem_abelianSheafSupport_iff`,
  `TopCat.Presheaf.stalk`,
  `TopCat.Presheaf.Γgerm`;
- best owner abstraction:
  the source-facing owner is `ringSheafSupport`, the thin ring-sheaf bridge to the chapter’s core
  additive owner `abelianSheafSupport`;
- primitive data:
  a sheaf of rings `ℱ` on `X`;
- derived API:
  the unit-germ criterion for membership in `ringSheafSupport ℱ` and the resulting closedness
  statement.

Source/core/bridge triage:
- `source-facing`: `ringSheafSupport` and Lemma 17.5.3 for a sheaf of rings;
- `core/canonical`: `abelianSheafSupport`;
- `bridge/view`: the forgetful additive sheaf `ringToAddSheaf ℱ` and the stalk comparison induced
  by `forget₂ RingCat AddCommGrpCat`. -/

private abbrev ringToAddSheaf (ℱ : X.Sheaf RingCat.{u}) : X.Sheaf AddCommGrpCat.{u} :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat AddCommGrpCat)).obj ℱ

private abbrev ringToAddPresheaf (ℱ : X.Sheaf RingCat.{u}) : X.Presheaf AddCommGrpCat.{u} :=
  ℱ.presheaf ⋙ forget₂ RingCat AddCommGrpCat

private noncomputable abbrev ringStalkAddIso (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x ≅
      (forget₂ RingCat AddCommGrpCat).obj (TopCat.Presheaf.stalk ℱ.presheaf x) := by
  change TopCat.Presheaf.stalk (ℱ.presheaf ⋙ forget₂ RingCat AddCommGrpCat) x ≅ _
  exact Limits.colimit.isoColimitCocone
    ⟨_, Limits.isColimitOfPreserves
      (forget₂ RingCat AddCommGrpCat)
      (Limits.colimit.isColimit ((OpenNhds.inclusion x).op ⋙ ℱ.presheaf))⟩

-- Proof sketch: the support owner is `abelianSheafSupport` of the underlying additive sheaf. Its
-- stalk is nonzero exactly when the stalk of rings is nontrivial, which is equivalent to the germ
-- of the global unit section being nonzero.
/-- For a sheaf of rings, membership in `ringSheafSupport` is equivalent to nonvanishing of the
germ of the global unit section. -/
theorem mem_ringSheafSupport_iff_one_germ_ne_zero
    (ℱ : X.Sheaf RingCat.{u}) (x : X) :
    x ∈ ringSheafSupport ℱ ↔
      ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) ≠ 0 := by
  change x ∈ abelianSheafSupport (ringToAddSheaf ℱ) ↔ _
  rw [mem_abelianSheafSupport_iff]
  change ¬ IsZero (TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x) ↔
    ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) ≠ 0
  constructor
  · intro hx hzero
    have hsubRing : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) :=
      subsingleton_of_zero_eq_one (show (0 : ↑(TopCat.Presheaf.stalk ℱ.presheaf x)) = 1 by
        simpa using hzero.symm)
    have hsubAdd : Subsingleton ↑(TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x) := by
      let e := (ringStalkAddIso ℱ x).addCommGroupIsoToAddEquiv.toEquiv
      letI : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) := hsubRing
      exact e.subsingleton
    exact hx ((AddCommGrpCat.isZero_iff_subsingleton).2 hsubAdd)
  · intro hx
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    intro hsub
    have hsubRing : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) := by
      let e := (ringStalkAddIso ℱ x).addCommGroupIsoToAddEquiv.toEquiv
      letI : Subsingleton ↑(TopCat.Presheaf.stalk (ringToAddPresheaf ℱ) x) := hsub
      exact e.symm.subsingleton
    exact hx <| by
      letI : Subsingleton ↑(TopCat.Presheaf.stalk ℱ.presheaf x) := hsubRing
      exact Subsingleton.elim _ _

-- Proof sketch: if the unit germ vanishes at `x`, then by the stalk criterion there is an open
-- neighbourhood on which the unit section restricts to zero. Hence the unit germ vanishes at every
-- point of that neighbourhood, so the complement of the support is open.
/-- Lemma 17.5.3: for a topological space `X`, the support of a sheaf of rings on `X` is closed. -/
theorem isClosed_ringSheafSupport
    (ℱ : X.Sheaf RingCat.{u}) :
    IsClosed (ringSheafSupport ℱ) := by
  change IsClosed (abelianSheafSupport (ringToAddSheaf ℱ))
  rw [← isOpen_compl_iff]
  refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  have hzero : ℱ.presheaf.Γgerm x (1 : ℱ.presheaf.obj (op ⊤)) = 0 := by
    by_contra h
    exact hx ((mem_ringSheafSupport_iff_one_germ_ne_zero ℱ x).2 h)
  have hzero' :
      ℱ.presheaf.germ ⊤ x True.intro (1 : ℱ.presheaf.obj (op ⊤)) =
        ℱ.presheaf.germ ⊤ x True.intro 0 := by
    simpa [TopCat.Presheaf.Γgerm] using hzero
  obtain ⟨W, hxW, iW, iTop, hW⟩ := ℱ.presheaf.germ_eq x
    (show x ∈ (⊤ : Opens X) from True.intro)
    (show x ∈ (⊤ : Opens X) from True.intro)
    (1 : ℱ.presheaf.obj (op ⊤)) 0 hzero'
  have hWzero : ℱ.presheaf.map iW.op (1 : ℱ.presheaf.obj (op ⊤)) = 0 := by
    simpa using hW
  refine Filter.mem_of_superset (IsOpen.mem_nhds W.2 hxW) fun y hyW hySupport ↦ ?_
  have hyZero : ℱ.presheaf.Γgerm y (1 : ℱ.presheaf.obj (op ⊤)) = 0 := by
    have hΓ :
        ℱ.presheaf.germ W y hyW (ℱ.presheaf.map iW.op (1 : ℱ.presheaf.obj (op ⊤))) =
          ℱ.presheaf.Γgerm y (1 : ℱ.presheaf.obj (op ⊤)) := by
      change ℱ.presheaf.germ W y hyW (ℱ.presheaf.map iW.op (1 : ℱ.presheaf.obj (op ⊤))) =
        ℱ.presheaf.germ ⊤ y True.intro (1 : ℱ.presheaf.obj (op ⊤))
      exact ℱ.presheaf.germ_res_apply iW y hyW (1 : ℱ.presheaf.obj (op ⊤))
    rw [← hΓ, hWzero]
    exact map_zero _
  exact (mem_ringSheafSupport_iff_one_germ_ne_zero ℱ y).1 hySupport hyZero

end

end TopCat.Sheaf
