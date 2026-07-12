import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w w'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace Sheaf

/- Domain-style sampling for Definition 18.43.1:
- primary domain: locally constant sheaves on a site and finite locally constant sheaves of sets
  and groups.
- sampled owner-level declarations:
  `CategoryTheory.Sheaf.IsConstant`,
  `CategoryTheory.constantSheaf`,
  `GrothendieckTopology.over`,
  `GrothendieckTopology.overPullback`.
- best owner abstraction: `Sheaf.IsLocallyConstant`, built from the canonical restriction
  functors `F.over` and the owner predicate `Sheaf.IsConstant` on slice sites.
- primitive data: for each `U : C`, a covering in `J.over U` on which the restricted sheaf is
  constant.
- derived API: finite locally constant variants, obtained by adjoining finiteness conditions on
  the local constant models.

Source/core/bridge triage:
- `source-facing`: `Sheaf.IsLocallyConstant`, `Sheaf.IsFiniteLocallyConstant`,
  `Sheaf.IsFiniteLocallyConstantGrp`.
- `core/canonical`: `Sheaf.IsConstant`, `constantSheaf`, and sheaf restriction to slice sites.
- `bridge/view`: the constant-sheaf instances, plus the auxiliary abelian-group and module
  specializations used later in the chapter. -/

section Constant

variable {D : Type w} [Category.{w'} D] [HasWeakSheafify J D]

/- Constant sheaf recall: for a sheaf of sets, groups, abelian groups, rings, modules, and
similar algebraic objects on a site `(C, J)`, being a constant sheaf is the canonical mathlib
predicate `Sheaf.IsConstant`, meaning that the sheaf lies in the essential image of the constant
sheaf functor. -/
#check IsConstant

end Constant

section LocallyConstant

variable {D : Type w} [Category.{w'} D]
variable [HasWeakSheafify J D]
variable [∀ U : C, HasWeakSheafify (J.over U) D]

/-- Definition 18.43.1 (1): a sheaf on a site is locally constant if, after restricting to the
localized site above any object `U`, there is a covering family of `U` on which the further
restrictions become constant sheaves. -/
@[stacks 093Q]
class IsLocallyConstant (F : Sheaf J D) : Prop where
  /-- Every object admits a covering on which the restriction of `F` is constant. -/
  exists_constant_cover (U : C) :
    ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
      ∀ i : I, IsConstant (J.over (X i).left) (F.over (X i).left)

/-- Helper for Definition 18.43.1: the singleton family given by the identity of `U` is a cover
in the slice site `(C/U, J.over U)`. -/
lemma identity_singleton_coversTop_over (U : C) :
    (J.over U).CoversTop (fun _ : PUnit => Over.mk (𝟙 U)) := by
  -- The slice terminal object is `Over.mk (𝟙 U)`, so a family containing it covers the top.
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal (J := J.over U) (X := Over.mk (𝟙 U))
    (hX := Over.mkIdTerminal)]
  rw [GrothendieckTopology.mem_over_iff]
  have htop :
      (Sieve.overEquiv (Over.mk (𝟙 U)))
        (Sieve.ofObjects (fun _ : PUnit => Over.mk (𝟙 U)) (Over.mk (𝟙 U))) = ⊤ := by
    ext Z g
    constructor
    · intro _
      trivial
    · intro _
      rw [Sieve.overEquiv_iff]
      exact ⟨PUnit.unit, ⟨Over.homMk g⟩⟩
  rw [htop]
  exact J.top_mem U

/-- Helper for Definition 18.43.1: if a sheaf is locally modeled by explicit constant sheaves on
each member of a covering family, then it is locally constant. -/
theorem isLocallyConstant_of_explicit_constant_models {F : Sheaf J D}
    (hF : ∀ U : C,
      ∃ (I : Type (max u v)) (X : I → Over U), (J.over U).CoversTop X ∧
        ∀ i : I,
          ∃ E : D,
            Nonempty (F.over (X i).left ≅ (constantSheaf (J.over (X i).left) D).obj E)) :
    IsLocallyConstant F := by
  refine ⟨?_⟩
  intro U
  -- We keep the given covering family and convert each explicit local model into `IsConstant`.
  obtain ⟨I, X, hX, hconst⟩ := hF U
  refine ⟨I, X, hX, ?_⟩
  intro i
  obtain ⟨E, ⟨e⟩⟩ := hconst i
  exact Sheaf.isConstant_of_iso (J := J.over (X i).left) e

/-- Helper for Definition 18.43.1: the whiskered sheafification unit compares the slice constant
presheaf with the restriction of the ambient constant sheaf. -/
noncomputable def constant_presheaf_over_comparison (U : C) (E : D) :
    ((Functor.const (Over U)ᵒᵖ).obj E) ⟶ (((constantSheaf J D).obj E).over U).obj :=
  Functor.whiskerLeft (Over.forget U).op (toSheafify J ((Functor.const Cᵒᵖ).obj E))

/-- Helper for Definition 18.43.1: the presheaf comparison from the slice constant presheaf to the
restricted ambient constant sheaf is a `W`-morphism on the slice site. -/
theorem constant_presheaf_over_comparison_is_W
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (U : C) (E : D) :
    (J.over U).W (constant_presheaf_over_comparison (J := J) (D := D) U E) := by
  -- The ambient sheafification unit is locally bijective in concrete categories.
  letI : Presheaf.IsLocallyInjective J (toSheafify J ((Functor.const Cᵒᵖ).obj E)) :=
    GrothendieckTopology.W.isLocallyInjective (J := J) (A := D) (FA := FD) (CA := CD)
      (f := toSheafify J ((Functor.const Cᵒᵖ).obj E))
      (J.W_toSheafify (A := D) ((Functor.const Cᵒᵖ).obj E))
  letI : Presheaf.IsLocallySurjective J (toSheafify J ((Functor.const Cᵒᵖ).obj E)) :=
    GrothendieckTopology.W.isLocallySurjective (J := J) (A := D) (FA := FD) (CA := CD)
      (f := toSheafify J ((Functor.const Cᵒᵖ).obj E))
      (J.W_toSheafify (A := D) ((Functor.const Cᵒᵖ).obj E))
  -- Pulling back along `Over.forget U` preserves those local bijectivity properties.
  letI : Presheaf.IsLocallyInjective (J.over U)
      (constant_presheaf_over_comparison (J := J) (D := D) U E) := by
    simpa [constant_presheaf_over_comparison] using
      (Presheaf.isLocallyInjective_whisker (J := J.over U) (K := J) (H := Over.forget U)
        (A := D) (FA := FD) (CA := CD)
        (f := toSheafify J ((Functor.const Cᵒᵖ).obj E)))
  letI : Presheaf.IsLocallySurjective (J.over U)
      (constant_presheaf_over_comparison (J := J) (D := D) U E) := by
    simpa [constant_presheaf_over_comparison] using
      (Presheaf.isLocallySurjective_whisker (J := J.over U) (K := J) (H := Over.forget U)
        (A := D) (FA := FD) (CA := CD)
        (f := toSheafify J ((Functor.const Cᵒᵖ).obj E)))
  exact GrothendieckTopology.W_of_isLocallyBijective (J := J.over U)
    (A := D) (f := constant_presheaf_over_comparison (J := J) (D := D) U E)

/-- Helper for Definition 18.43.1: restricting a constant sheaf to a slice site is canonically
isomorphic to the constant sheaf with the same value on that slice site. -/
noncomputable def constantSheafOverObjIso
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (U : C) (E : D) :
    ((constantSheaf J D).obj E).over U ≅ (constantSheaf (J.over U) D).obj E := by
  -- Route correction: avoid the unavailable right-Kan comparison and instead sheafify the
  -- explicit slice presheaf comparison proved to lie in `W`.
  have hW : (J.over U).W (constant_presheaf_over_comparison (J := J) (D := D) U E) :=
    constant_presheaf_over_comparison_is_W (J := J) (D := D) (FD := FD) (CD := CD) U E
  -- Sheafifying the comparison gives the source-side constant sheaf on the slice site.
  let e₁ : (constantSheaf (J.over U) D).obj E ≅
      (presheafToSheaf (J.over U) D).obj ((((constantSheaf J D).obj E).over U).obj) := by
    have hIso : IsIso ((presheafToSheaf (J.over U) D).map
        (constant_presheaf_over_comparison (J := J) (D := D) U E)) :=
      ((J.over U).W_iff (A := D)
        (constant_presheaf_over_comparison (J := J) (D := D) U E)).mp hW
    exact @asIso _ _ _ _
      ((presheafToSheaf (J.over U) D).map
        (constant_presheaf_over_comparison (J := J) (D := D) U E)) hIso
  -- The restricted constant sheaf is already a sheaf, so it identifies with the sheafification of
  -- its underlying presheaf.
  let e₂ : ((constantSheaf J D).obj E).over U ≅
      (presheafToSheaf (J.over U) D).obj ((((constantSheaf J D).obj E).over U).obj) :=
    (fullyFaithfulSheafToPresheaf (J.over U) D).preimageIso
      (isoSheafify (J.over U) (((constantSheaf J D).obj E).over U).property)
  exact e₂ ≪≫ e₁.symm

/-- Helper for Definition 18.43.1: restricting a constant sheaf to a slice site is isomorphic to
the constant sheaf with the same value on that slice site. -/
theorem constant_sheaf_over_nonempty_iso
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (U : C) (E : D) :
    Nonempty (((constantSheaf J D).obj E).over U ≅ (constantSheaf (J.over U) D).obj E) := by
  exact ⟨constantSheafOverObjIso (J := J) (D := D) U E⟩

/-- Helper for Definition 18.43.1: the restriction of a constant sheaf to a slice site is again
constant. -/
theorem constant_sheaf_over_isConstant
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (U : C) (E : D) :
    IsConstant (J.over U) (((constantSheaf J D).obj E).over U) := by
  -- The explicit slice-site model from `constant_sheaf_over_nonempty_iso` gives the owner
  -- predicate immediately.
  exact Sheaf.isConstant_of_iso (J := J.over U)
    (constantSheafOverObjIso (J := J) (D := D) U E)

/-- Local constancy is invariant under isomorphism. -/
theorem isLocallyConstant_of_iso
    {F G : Sheaf J D} (e : F ≅ G) [IsLocallyConstant F] :
    IsLocallyConstant G := by
  refine ⟨?_⟩
  intro U
  -- We reuse the same cover and transport each local constant witness across restriction of `e`.
  obtain ⟨I, X, hX, hconst⟩ := IsLocallyConstant.exists_constant_cover (F := F) U
  refine ⟨I, X, hX, ?_⟩
  intro i
  simpa [Sheaf.over] using
    (Sheaf.isConstant_congr (J := J.over (X i).left)
      ((J.overPullback D (X i).left).mapIso e))

-- Proof sketch: for each object `U`, use the singleton covering of `U` by the identity
-- `𝟙_U : U ⟶ U`; the restriction of a constant sheaf to `U` is again constant by functoriality
-- of `constantSheaf` with respect to localization.
/-- A constant sheaf is locally constant. -/
theorem isLocallyConstant_of_isConstant
    {FD : D → D → Type*} {CD : D → Type*}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory D FD]
    [J.WEqualsLocallyBijective D]
    [∀ U : C, (J.over U).WEqualsLocallyBijective D]
    (F : Sheaf J D) [IsConstant J F] :
    IsLocallyConstant F := by
  -- We first choose a global constant model for `F`.
  obtain ⟨E, ⟨e⟩⟩ := Sheaf.mem_essImage_of_isConstant (J := J) F
  letI : IsLocallyConstant ((constantSheaf J D).obj E) := by
    -- On each object, the singleton identity cover trivializes the constant sheaf.
    refine isLocallyConstant_of_explicit_constant_models (J := J) (D := D) ?_
    intro U
    refine ⟨PUnit, fun _ ↦ Over.mk (𝟙 U), identity_singleton_coversTop_over (J := J) U, ?_⟩
    intro i
    exact ⟨E, ⟨constantSheafOverObjIso (J := J) (D := D) U E⟩⟩
  -- Then we transport local constancy across the chosen isomorphism.
  exact isLocallyConstant_of_iso (J := J) e

end LocallyConstant

-- The finiteness-enriched variants from Definition 18.43.1 are split into the companion file
-- `Definition_18_43_1_Finite.lean` so downstream results that only use the locally constant core
-- do not need to elaborate the later auxiliary API.

end Sheaf

end CategoryTheory
