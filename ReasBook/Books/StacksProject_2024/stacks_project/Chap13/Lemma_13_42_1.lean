import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_22_2
import StacksProject_2024.stacks_project.Chap04.Lemma_4_22_13
import StacksProject_2024.stacks_project.Chap04.Lemma_4_22_3
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_11

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe uI vD uD

namespace CategoryTheory

/- Domain-style sampling for Lemma 13.42.1:
- primary domain: essentially constant cofiltered diagrams in pretriangulated categories, expressed by
  an eventual tailwise biproduct decomposition.
- sampled owner-level declarations:
  * `IsEssentiallyConstantCofilteredDiagram` in `Chap04/Definition_4_22_2`
  * `IsEssentiallyConstantCofilteredCone` in `Chap04/Definition_4_22_1`
  * `Functor.tail` and `Functor.mapLE` below for the canonical tail restriction and cofiltered
    transition-map surface on preorder-indexed inverse systems
  * `Pretriangulated.binaryBiproductData` in mathlib's pretriangulated API
  * `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang` in mathlib
- best owner abstraction:
  * `core/canonical`: `IsEssentiallyConstantCofilteredDiagram F`
  * `source-facing`: `HasTailDirectSumDecomposition F`, the explicit tailwise biproduct
    decomposition criterion
  * `bridge/view`: the equivalence theorem below, specialized to the pretriangulated setting

Primitive-vs-derived split:
- primitive source-facing data: a tail index, a fixed summand `A`, a complementary tail diagram
  `Z : OrderDual (Set.Ici i) ⥤ D`, a functor-level biproduct decomposition
  `F.tail i ≅ (Functor.const _).obj A ⊞ Z`, and eventual vanishing of the complementary transition
  maps along the cofiltered tail.
- derived API: the stagewise isomorphisms and their compatibility with the transition maps, both
  obtained by evaluating that natural isomorphism, together with the equivalence with the chapter
  owner `IsEssentiallyConstantCofilteredDiagram`. -/

namespace Functor

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D]

/-- The restriction of a cofiltered preorder-indexed diagram to the tail `Set.Ici i`. -/
abbrev tail (F : OrderDual I ⥤ D) (i : I) : OrderDual (Set.Ici i) ⥤ D :=
  (OrderHom.Subtype.val (Set.Ici i)).dual.toFunctor ⋙ F

/-- The transition map in a cofiltered preorder-indexed diagram attached to an inequality
`j ≤ j'`. -/
abbrev mapLE {J : Type*} [Preorder J] (F : OrderDual J ⥤ D) {j j' : J} (h : j ≤ j') :
    F.obj j' ⟶ F.obj j :=
  F.map (homOfLE h)

end

end Functor

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasBinaryBiproducts D]

/-- Evaluating a tailwise biproduct decomposition at a transition map recovers the expected
stagewise compatibility equation. -/
@[reassoc]
theorem tailDirectSumIso_hom_naturality {F : OrderDual I ⥤ D} {i : I} {A : D}
    {Z : OrderDual (Set.Ici i) ⥤ D}
    (e : F.tail i ≅ (Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z)
    {j j' : Set.Ici i} (hjj' : j ≤ j') :
    (F.tail i).mapLE hjj' ≫ (e.app j).hom =
      (e.app j').hom ≫ (((Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z).mapLE hjj') := by
  simpa [Functor.mapLE] using e.hom.naturality (homOfLE hjj')

/-- Lemma 13.42.1 source-facing criterion: after some stage, the inverse system `F` splits as a
fixed summand `A` together with a complementary tail diagram whose transition maps are eventually
zero, and the transition maps of `F` act as the identity on `A`. -/
def HasTailDirectSumDecomposition (F : OrderDual I ⥤ D) : Prop :=
  ∃ i : I,
    ∃ A : D,
      ∃ Z : OrderDual (Set.Ici i) ⥤ D,
        ∃ _e : F.tail i ≅ (Functor.const (OrderDual (Set.Ici i))).obj A ⊞ Z,
          ∀ j : Set.Ici i, ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0

/-- Helper for Lemma 13.42.1: transition morphisms in a cofiltered preorder-indexed diagram
factor through every intermediate stage. -/
private theorem mapLE_comp
    {J : Type*} [Preorder J] {F : OrderDual J ⥤ D}
    {j j' j'' : J} (hjj' : j ≤ j') (hj'j'' : j' ≤ j'') :
    F.mapLE (show j ≤ j'' from le_trans hjj' hj'j'') =
      F.mapLE hj'j'' ≫ F.mapLE hjj' := by
  simpa [Functor.mapLE] using
    F.map_comp (homOfLE hj'j'').op (homOfLE hjj').op

end

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
variable [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Helper for Lemma 13.42.1: a morphism with a chosen right inverse identifies its source with
the fixed summand plus a complementary object. -/
private theorem split_stage_iso_of_retraction {A X : D} (ι : A ⟶ X) (ρ : X ⟶ A)
    (hρι : ι ≫ ρ = 𝟙 A) :
    ∃ Z : D, ∃ e : X ≅ A ⊞ Z, ι ≫ e.hom = biprod.inl ∧ e.hom ≫ biprod.fst = ρ := by
  -- Proof comment: split the distinguished triangle on `ρ`; the chosen section `ι` becomes the
  -- right biproduct inclusion after transporting across the canonical braiding isomorphism.
  obtain ⟨Z, g, δ, hT⟩ := CategoryTheory.Pretriangulated.distinguished_cocone_triangle₁ ρ
  have hIso : IsIso (biprod.desc g ι) := by
    exact isIso_biprod_desc_of_distinguished_right_inverse hT ι hρι
  let e₀ : X ≅ Z ⊞ A := (asIso (biprod.desc g ι)).symm
  let e : X ≅ A ⊞ Z := e₀ ≪≫ biprod.braiding Z A
  have hιe₀ : ι ≫ e₀.hom = biprod.inr := by
    apply (cancel_mono e₀.inv).1
    simpa [Category.assoc, e₀] using
      (show (ι ≫ e₀.hom) ≫ e₀.inv = biprod.inr ≫ e₀.inv by simp [Category.assoc, e₀])
  have hgρ : g ≫ ρ = 0 := by
    simpa [Triangle.mk] using comp_distTriang_mor_zero₁₂ (Triangle.mk g ρ δ) hT
  refine ⟨Z, e, ?_, ?_⟩
  · -- Postcompose with the inverse splitting map to read the chosen section as `biprod.inl`.
    calc
      ι ≫ e.hom = (ι ≫ e₀.hom) ≫ (biprod.braiding Z A).hom := by
        simp [e, Category.assoc]
      _ = biprod.inr ≫ (biprod.braiding Z A).hom := by rw [hιe₀]
      _ = biprod.inl := by simp
  · -- The cone relation `g ≫ ρ = 0` and the chosen right inverse identify the first projection.
    have hsnd : e₀.inv ≫ ρ = biprod.snd := by
      apply biprod.hom_ext'
      · simpa [e₀, Category.assoc] using hgρ
      · simpa [e₀, Category.assoc] using hρι
    calc
      e.hom ≫ biprod.fst = e₀.hom ≫ (biprod.braiding Z A).hom ≫ biprod.fst := by
        simp [e, Category.assoc]
      _ = e₀.hom ≫ biprod.snd := by simp
      _ = ρ := by
        simpa [Category.assoc] using (congrArg (fun f ↦ e₀.hom ≫ f) hsnd).symm

/-- Helper for Lemma 13.42.1: after conjugating by the stagewise splitting isomorphisms, any
transition morphism preserving the fixed summand becomes block diagonal with identity on that
summand. -/
private theorem split_morphism_block_form
    {A X' X Z' Z : D} {ι' : A ⟶ X'} {ρ' : X' ⟶ A} {ι : A ⟶ X} {ρ : X ⟶ A}
    (e' : X' ≅ A ⊞ Z') (e : X ≅ A ⊞ Z)
    (hι'e' : ι' ≫ e'.hom = biprod.inl) (he'ρ' : e'.hom ≫ biprod.fst = ρ')
    (hιe : ι ≫ e.hom = biprod.inl) (heρ : e.hom ≫ biprod.fst = ρ)
    (f : X' ⟶ X) (hιf : ι' ≫ f = ι) (hfρ : f ≫ ρ = ρ') :
    let z : Z' ⟶ Z := biprod.inr ≫ e'.inv ≫ f ≫ e.hom ≫ biprod.snd
    ; f ≫ e.hom = e'.hom ≫ biprod.map (𝟙 A) z := by
  let z : Z' ⟶ Z := biprod.inr ≫ e'.inv ≫ f ≫ e.hom ≫ biprod.snd
  have hι'inv : biprod.inl ≫ e'.inv = ι' := by
    have h := congrArg (fun t ↦ t ≫ e'.inv) hι'e'
    simpa [Category.assoc] using h.symm
  have hρ'inv : e'.inv ≫ ρ' = biprod.fst := by
    have h := congrArg (fun t ↦ e'.inv ≫ t) he'ρ'
    simpa [Category.assoc] using h.symm
  have hconj : e'.inv ≫ f ≫ e.hom = biprod.map (𝟙 A) z := by
    apply biprod.hom_ext'
    · -- The fixed summand is preserved, so the left block is the identity.
      calc
        biprod.inl ≫ e'.inv ≫ f ≫ e.hom = ι' ≫ f ≫ e.hom := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ f ≫ e.hom) hι'inv
        _ = ι ≫ e.hom := by
          simpa [Category.assoc] using congrArg (fun t ↦ t ≫ e.hom) hιf
        _ = biprod.inl := hιe
        _ = biprod.inl ≫ biprod.map (𝟙 A) z := by simp
    · -- The complementary block is exactly the chosen lower-right coordinate `z`.
      apply biprod.hom_ext
      · calc
          (biprod.inr ≫ e'.inv ≫ f ≫ e.hom) ≫ biprod.fst =
              biprod.inr ≫ e'.inv ≫ f ≫ ρ := by
            simpa [Category.assoc] using congrArg (fun t ↦ biprod.inr ≫ e'.inv ≫ f ≫ t) heρ
          _ = biprod.inr ≫ e'.inv ≫ ρ' := by
            simpa [Category.assoc] using congrArg (fun t ↦ biprod.inr ≫ e'.inv ≫ t) hfρ
          _ = biprod.inr ≫ biprod.fst := by rw [hρ'inv]
          _ = 0 := by simp
          _ = (biprod.inr ≫ biprod.map (𝟙 A) z) ≫ biprod.fst := by simp [Category.assoc]
      · calc
          (biprod.inr ≫ e'.inv ≫ f ≫ e.hom) ≫ biprod.snd = z := by rfl
          _ = (biprod.inr ≫ biprod.map (𝟙 A) z) ≫ biprod.snd := by
            simp [z, Category.assoc]
  -- Proof comment: undo the conjugation on the source side by composing with `e'.hom`.
  calc
    f ≫ e.hom = e'.hom ≫ e'.inv ≫ f ≫ e.hom := by simp [Category.assoc]
    _ = e'.hom ≫ biprod.map (𝟙 A) z := by rw [hconj]

/-- Helper for Lemma 13.42.1: a morphism factoring through the fixed summand has zero
complementary block after conjugating by the stagewise splitting isomorphisms. -/
private theorem zero_complement_of_factorization_through_fixed_summand
    {A X' X Z' Z : D} {ι' : A ⟶ X'} {ρ' : X' ⟶ A} {ι : A ⟶ X} {ρ : X ⟶ A}
    (e' : X' ≅ A ⊞ Z') (e : X ≅ A ⊞ Z)
    (hι'e' : ι' ≫ e'.hom = biprod.inl) (he'ρ' : e'.hom ≫ biprod.fst = ρ')
    (hιe : ι ≫ e.hom = biprod.inl) (f : X' ⟶ X) (hfactor : f = ρ' ≫ ι) :
    biprod.inr ≫ e'.inv ≫ f ≫ e.hom ≫ biprod.snd = 0 := by
  have hρ'inv : e'.inv ≫ ρ' = biprod.fst := by
    have h := congrArg (fun t ↦ e'.inv ≫ t) he'ρ'
    simpa [Category.assoc] using h.symm
  have hιe_snd : ι ≫ e.hom ≫ biprod.snd = 0 := by
    simpa [Category.assoc] using congrArg (fun t ↦ t ≫ biprod.snd) hιe
  -- Proof comment: both factors of the fixed summand are visible in coordinates, so the
  -- complementary block collapses to `biprod.inr ≫ biprod.fst ≫ biprod.inl ≫ biprod.snd = 0`.
  calc
    biprod.inr ≫ e'.inv ≫ f ≫ e.hom ≫ biprod.snd =
        biprod.inr ≫ e'.inv ≫ (ρ' ≫ ι) ≫ e.hom ≫ biprod.snd := by rw [hfactor]
    _ = biprod.inr ≫ e'.inv ≫ ρ' ≫ ι ≫ e.hom ≫ biprod.snd := by simp [Category.assoc]
    _ = (biprod.inr : Z' ⟶ A ⊞ Z') ≫ biprod.fst ≫ (ι ≫ e.hom ≫ biprod.snd) := by
      rw [hρ'inv]
      simp [Category.assoc]
    _ = 0 := by simp [hιe_snd, Category.assoc]

/-- Helper for Lemma 13.42.1: transporting the retraction from the distinguished stage `i` to any
later stage of the tail still retracts the corresponding cone leg. -/
theorem tail_retraction_section {F : OrderDual I ⥤ D} {c : Cone F} {i : I}
    (σ : SplitMono (c.π.app i)) (j : Set.Ici i) :
    c.π.app j.1 ≫
        (F.tail i).mapLE (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j from j.2) ≫
        σ.retraction =
      𝟙 c.pt := by
  -- Cone naturality rewrites the tail leg through the distinguished stage `i`, and the chosen
  -- retraction then closes the identity.
  have hw :=
    c.w
      (homOfLE (show (j.1 : OrderDual I) ≤ i from j.2) : (j.1 : OrderDual I) ⟶ i)
  simpa [Functor.tail, Functor.mapLE, Category.assoc] using
    congrArg (fun g ↦ g ≫ σ.retraction) hw

/-- Helper for Lemma 13.42.1: the factorization clause from Definition 4.22.1 already produces a
later index inside the tail together with the same factorization formula. -/
theorem eventual_tail_factorization {F : OrderDual I ⥤ D} {c : Cone F} {i : I}
    (σ : SplitMono (c.π.app i))
    (hσ : ∀ j : OrderDual I, ∃ k : OrderDual I, ∃ ki : k ⟶ i, ∃ kj : k ⟶ j,
      F.map kj = F.map ki ≫ σ.retraction ≫ c.π.app j)
    (j : Set.Ici i) :
    ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j',
      (F.tail i).mapLE hjj' =
        (F.tail i).mapLE (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j' from j'.2) ≫
          σ.retraction ≫ c.π.app j.1 := by
  rcases hσ (j.1 : OrderDual I) with ⟨k, ki, kj, hk⟩
  let j' : Set.Ici i := ⟨k, show i ≤ (k : I) from leOfHom ki⟩
  refine ⟨j', show j ≤ j' from leOfHom kj, ?_⟩
  simpa [Functor.tail, Functor.mapLE] using hk

/-- Helper for Lemma 13.42.1: postcomposing an essentially constant cofiltered cone along a
natural isomorphism preserves essential constancy. -/
private theorem cofilteredCone_postcompose_iso
    {J : Type*} [Category J] {M N : J ⥤ D} {c : Cone M}
    (hc : IsEssentiallyConstantCofilteredCone c) (e : M ≅ N) :
    IsEssentiallyConstantCofilteredCone ((Cone.postcompose e.hom).obj c) := by
  -- Proof comment: transport both the chosen split mono and its eventual factorization across the
  -- componentwise isomorphisms of the diagram isomorphism `e`.
  rw [isEssentiallyConstantCofilteredCone_iff] at hc ⊢
  rcases hc with ⟨i, σ, hσ⟩
  let σ' : SplitMono (((Cone.postcompose e.hom).obj c).π.app i) := by
    refine ⟨(e.inv.app i) ≫ σ.retraction, ?_⟩
    simp [Category.assoc]
  refine ⟨i, σ', ?_⟩
  intro j
  rcases hσ j with ⟨k, ki, kj, hkj⟩
  refine ⟨k, ki, kj, ?_⟩
  -- Proof comment: rewrite the transported transition map using naturality of `e.inv`.
  calc
    N.map kj = N.map kj ≫ e.inv.app j ≫ e.hom.app j := by
      simp
    _ = e.inv.app k ≫ M.map kj ≫ e.hom.app j := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ t ≫ e.hom.app j) (e.inv.naturality kj)
    _ = e.inv.app k ≫ (M.map ki ≫ σ.retraction ≫ c.π.app j) ≫ e.hom.app j := by
      rw [hkj]
    _ = (N.map ki ≫ e.inv.app i) ≫ σ.retraction ≫ c.π.app j ≫ e.hom.app j := by
      simpa [Category.assoc] using
        congrArg (fun t ↦ t ≫ σ.retraction ≫ c.π.app j ≫ e.hom.app j)
          (e.inv.naturality ki).symm
    _ = N.map ki ≫ σ'.retraction ≫ (((Cone.postcompose e.hom).obj c).π.app j) := by
      simp [σ', Category.assoc]

/-- Helper for Lemma 13.42.1: if the complementary tail transition maps are eventually zero, then
the standard biproduct tail is essentially constant. -/
private theorem essentiallyConstant_biprod_tail_of_eventual_zero
    {i : I} {A : D} {Z : OrderDual (Set.Ici i) ⥤ D}
    (hzero : ∀ j : Set.Ici i, ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0) :
    IsEssentiallyConstantCofilteredDiagram
      (((Functor.const (OrderDual (Set.Ici i))).obj A) ⊞ Z) := by
  let π :
      (Functor.const (OrderDual (Set.Ici i))).obj A ⟶
        (((Functor.const (OrderDual (Set.Ici i))).obj A) ⊞ Z) :=
    { app := fun j ↦
        (biprod.inl :
          ((Functor.const (OrderDual (Set.Ici i))).obj A).obj j ⟶
            (((Functor.const (OrderDual (Set.Ici i))).obj A) ⊞ Z).obj j)
      naturality := fun j j' f ↦ by
        -- Proof comment: the constant summand is fixed by every transition map in the tail.
        simp }
  refine ⟨Cone.mk A π, ?_⟩
  rw [isEssentiallyConstantCofilteredCone_iff]
  refine ⟨⟨i, le_rfl⟩, ?_, ?_⟩
  · refine ⟨(biprod.fst :
      (((Functor.const (OrderDual (Set.Ici i))).obj A) ⊞ Z).obj ⟨i, le_rfl⟩ ⟶
        ((Functor.const (OrderDual (Set.Ici i))).obj A).obj ⟨i, le_rfl⟩), by simp [π]⟩
  intro j
  rcases hzero j with ⟨j', hjj', hz⟩
  refine ⟨j',
    homOfLE (show (j' : OrderDual (Set.Ici i)) ≤ ⟨i, le_rfl⟩ from j'.2),
    homOfLE (show (j' : OrderDual (Set.Ici i)) ≤ j from hjj'), ?_⟩
  -- Proof comment: the chosen later map is the identity on the fixed summand and zero on the
  -- complementary summand, so it factors through `biprod.fst ≫ biprod.inl`.
  apply biprod.hom_ext
  · simp [Functor.mapLE, hz, Category.assoc]
  · simp [Functor.mapLE, hz, Category.assoc]

-- Proof sketch: starting from an essentially constant cone, choose the eventual retraction from
-- Definition 4.22.1 and transport it to the whole tail. The pretriangulated splitting lemmas then
-- identify the whole tail functor with a biproduct `(Functor.const _).obj A ⊞ Z`, whose evaluated
-- components recover the stagewise isomorphisms `Fⱼ ≅ A ⊞ Zⱼ`; the factorization data assembles
-- the complementary summands into a tail inverse system whose transition maps become zero far
-- enough out.
-- Conversely, such a tailwise split decomposition directly reconstructs the retraction and
-- eventual factorization criterion in Definition 4.22.1.
/-- Lemma 13.42.1: a directed inverse system in a pretriangulated category is essentially constant
if and only if, after some index, every stage is isomorphic to a fixed summand `A` plus a
complementary inverse system `Z`, the transition maps `Fⱼ' ⟶ Fⱼ` act as the identity on `A`, and
the complementary transition maps are eventually zero. -/
theorem isEssentiallyConstantCofilteredDiagram_iff_hasEventuallyConstantDirectSumDecomposition
    [IsDirectedOrder I] (F : OrderDual I ⥤ D) :
    IsEssentiallyConstantCofilteredDiagram F ↔ HasTailDirectSumDecomposition F := by
  classical
  constructor
  · intro hF
    rcases essentiallyConstantCofilteredDiagram_exists_essentiallyConstant_limitCone F hF with
      ⟨c, hc⟩
    rcases (isEssentiallyConstantCofilteredCone_iff c.cone).1 hc with ⟨i₀, σ, hσ⟩
    let i : I := i₀
    let ι : (Functor.const (OrderDual (Set.Ici i))).obj c.cone.pt ⟶ F.tail i :=
      { app := fun j ↦ c.cone.π.app j.1
        naturality := fun j j' f ↦ by
          -- Proof comment: these are exactly the cone maps of the chosen limit cone.
          simpa [Functor.tail] using
            c.cone.w (((OrderHom.Subtype.val (Set.Ici i)).dual.toFunctor).map f) }
    let ρ : F.tail i ⟶ (Functor.const (OrderDual (Set.Ici i))).obj c.cone.pt :=
      { app := fun j ↦
          (F.tail i).mapLE (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j from j.2) ≫ σ.retraction
        naturality := fun j j' f ↦ by
          -- Proof comment: the tail transition map into the distinguished stage `i` factors
          -- through any farther transition map by functoriality.
          have hcomp :
              (F.tail i).mapLE
                  (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j from j.2) =
                (F.tail i).mapLE (leOfHom f) ≫
                  (F.tail i).mapLE
                    (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j' from j'.2) := by
            simpa using
              (mapLE_comp
                (F := F.tail i)
                (hjj' := show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j' from j'.2)
                (hj'j'' := leOfHom f)).symm
          simpa [hcomp, Category.assoc] }
    have hsection :
        ∀ j : Set.Ici i,
          c.cone.π.app j.1 ≫
              (F.tail i).mapLE (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j from j.2) ≫
              σ.retraction =
            𝟙 c.cone.pt := by
      intro j
      simpa using tail_retraction_section (F := F) (c := c.cone) σ j
    have htailFactor :
        ∀ j : Set.Ici i,
          ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j',
            (F.tail i).mapLE hjj' =
              (F.tail i).mapLE
                  (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j' from j'.2) ≫
                σ.retraction ≫ c.cone.π.app j.1 := by
      intro j
      simpa using eventual_tail_factorization (F := F) (c := c.cone) σ hσ j
    choose Zobj e hιe hρe using
      fun j : Set.Ici i =>
        split_stage_iso_of_retraction (ι.app j) (ρ.app j) (by
          simpa [ι, ρ, Category.assoc] using hsection j)
    have hblock :
        ∀ {j j' : Set.Ici i} (hjj' : j ≤ j'),
          let z : Zobj j' ⟶ Zobj j :=
            biprod.inr ≫ (e j').inv ≫ (F.tail i).mapLE hjj' ≫ (e j).hom ≫ biprod.snd
          ;
            (F.tail i).mapLE hjj' ≫ (e j).hom =
              (e j').hom ≫ biprod.map (𝟙 c.cone.pt) z := by
      intro j j' hjj'
      -- Proof comment: conjugate the tail transition by the stagewise splittings; cone
      -- naturality and the transported retractions pin down the `A`-block as the identity.
      refine split_morphism_block_form (e' := e j') (e := e j) (ι' := ι.app j') (ρ' := ρ.app j')
        (ι := ι.app j) (ρ := ρ.app j) (hι'e' := hιe j') (he'ρ' := hρe j')
        (hιe := hιe j) (heρ := hρe j) ((F.tail i).mapLE hjj') ?_ ?_
      · simpa [ι, Functor.tail] using
          c.cone.w
            (homOfLE
              (show (j'.1 : OrderDual I) ≤ (j.1 : OrderDual I) from hjj'))
      · have hcomp :
            (F.tail i).mapLE
                (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j from j.2) =
              (F.tail i).mapLE hjj' ≫
                (F.tail i).mapLE
                  (show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j' from j'.2) := by
          simpa using
            (mapLE_comp
              (F := F.tail i)
              (hjj' := show (⟨i, le_rfl⟩ : Set.Ici i) ≤ j' from j'.2)
              (hj'j'' := hjj')).symm
        simpa [ρ, hcomp, Category.assoc]
    have hzero_block :
        ∀ j : Set.Ici i,
          ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j',
            biprod.inr ≫ (e j').inv ≫ (F.tail i).mapLE hjj' ≫ (e j).hom ≫ biprod.snd = 0 := by
      intro j
      rcases htailFactor j with ⟨j', hjj', hfact⟩
      refine ⟨j', hjj', ?_⟩
      -- Proof comment: the eventual factorization through the fixed summand kills the
      -- complementary block after conjugating by the chosen stagewise splittings.
      refine zero_complement_of_factorization_through_fixed_summand
        (e' := e j') (e := e j) (ι' := ι.app j') (ρ' := ρ.app j')
        (ι := ι.app j) (ρ := ρ.app j) (hι'e' := hιe j') (he'ρ' := hρe j')
        (hιe := hιe j) ((F.tail i).mapLE hjj') ?_
      simpa [ι, ρ, Category.assoc] using hfact
    -- Route correction: follow the source proof stagewise. The stabilized frontier is now the
    -- pointwise split `e j` together with the block-form compatibility `hblock` and the eventual
    -- vanishing of the complementary block `hzero_block`. The remaining work is to assemble the
    -- complements `Zobj j` and these block maps into a tail functor `Z`, package `e` as a
    -- natural isomorphism `F.tail i ≅ (Functor.const _).obj c.cone.pt ⊞ Z`, and feed the
    -- resulting eventual-zero statement into the converse half already proved below.
    let zmap {j j' : Set.Ici i} (hjj' : j ≤ j') : Zobj j' ⟶ Zobj j :=
      biprod.inr ≫ (e j').inv ≫ (F.tail i).mapLE hjj' ≫ (e j).hom ≫ biprod.snd
    have hzmap_id : ∀ j : Set.Ici i, zmap (j := j) (j' := j) le_rfl = 𝟙 (Zobj j) := by
      intro j
      -- Proof comment: the diagonal block equation for `hblock le_rfl` reduces to the identity
      -- because the tail transition map at `le_rfl` is the identity.
      have hdiag := hblock (j := j) (j' := j) le_rfl
      have hdiag' :
          biprod.inr ≫ (e j).inv ≫ ((F.tail i).mapLE (j := j) (j' := j) le_rfl ≫ (e j).hom) ≫
              biprod.snd =
            biprod.inr ≫ (e j).inv ≫
                ((e j).hom ≫
                  biprod.map (𝟙 c.cone.pt) (zmap (j := j) (j' := j) le_rfl)) ≫
              biprod.snd := by
        exact congrArg (fun f ↦ biprod.inr ≫ (e j).inv ≫ f ≫ biprod.snd) hdiag
      calc
        zmap (j := j) (j' := j) le_rfl =
            biprod.inr ≫ (e j).inv ≫
              ((F.tail i).mapLE (j := j) (j' := j) le_rfl ≫ (e j).hom) ≫
                biprod.snd := by
          simp [zmap, Category.assoc]
        _ = biprod.inr ≫ (e j).inv ≫
              ((e j).hom ≫ biprod.map (𝟙 c.cone.pt) (zmap (j := j) (j' := j) le_rfl)) ≫
                biprod.snd := hdiag'
        _ = 𝟙 (Zobj j) := by
          simp [Functor.mapLE, zmap, Category.assoc]
    have hzmap_comp :
        ∀ {j₁ j₂ j₃ : Set.Ici i} (h12 : j₁ ≤ j₂) (h23 : j₂ ≤ j₃),
          zmap (j := j₁) (j' := j₃) (h12.trans h23) =
            zmap (j := j₂) (j' := j₃) h23 ≫ zmap (j := j₁) (j' := j₂) h12 := by
      intro j₁ j₂ j₃ h12 h23
      -- Proof comment: compose the two block-form identities and read off the lower-right block.
      have hbiprod_map_comp :
          biprod.map (𝟙 c.cone.pt) (zmap (j := j₂) (j' := j₃) h23) ≫
              biprod.map (𝟙 c.cone.pt) (zmap (j := j₁) (j' := j₂) h12) =
            biprod.map (𝟙 c.cone.pt)
              (zmap (j := j₂) (j' := j₃) h23 ≫ zmap (j := j₁) (j' := j₂) h12) := by
        apply biprod.hom_ext
        · simp [Category.assoc]
        · simp [Category.assoc]
      have hcomp :
          (F.tail i).mapLE (h12.trans h23) ≫ (e j₁).hom =
            (e j₃).hom ≫
              biprod.map (𝟙 c.cone.pt)
                (zmap (j := j₂) (j' := j₃) h23 ≫ zmap (j := j₁) (j' := j₂) h12) := by
        calc
          (F.tail i).mapLE (h12.trans h23) ≫ (e j₁).hom =
              (F.tail i).mapLE h23 ≫ (F.tail i).mapLE h12 ≫ (e j₁).hom := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ t ≫ (e j₁).hom) (mapLE_comp (F := F.tail i) h12 h23).symm
          _ = (F.tail i).mapLE h23 ≫
                ((e j₂).hom ≫ biprod.map (𝟙 c.cone.pt) (zmap (j := j₁) (j' := j₂) h12)) := by
            simpa [zmap] using
              congrArg (fun t ↦ (F.tail i).mapLE h23 ≫ t) (hblock (j := j₁) (j' := j₂) h12)
          _ = ((F.tail i).mapLE h23 ≫ (e j₂).hom) ≫
                biprod.map (𝟙 c.cone.pt) (zmap (j := j₁) (j' := j₂) h12) := by
            simp [Category.assoc]
          _ = ((e j₃).hom ≫ biprod.map (𝟙 c.cone.pt) (zmap (j := j₂) (j' := j₃) h23)) ≫
                biprod.map (𝟙 c.cone.pt) (zmap (j := j₁) (j' := j₂) h12) := by
            simpa [zmap] using
              congrArg
                (fun t ↦ t ≫ biprod.map (𝟙 c.cone.pt) (zmap (j := j₁) (j' := j₂) h12))
                (hblock (j := j₂) (j' := j₃) h23)
          _ = (e j₃).hom ≫
                biprod.map (𝟙 c.cone.pt) (zmap (j := j₂) (j' := j₃) h23) ≫
                  biprod.map (𝟙 c.cone.pt) (zmap (j := j₁) (j' := j₂) h12) := by
            simp [Category.assoc]
          _ = (e j₃).hom ≫
                biprod.map (𝟙 c.cone.pt)
                  (zmap (j := j₂) (j' := j₃) h23 ≫ zmap (j := j₁) (j' := j₂) h12) := by
            simpa [Category.assoc] using
              congrArg (fun t ↦ (e j₃).hom ≫ t) hbiprod_map_comp
      have hcomp' :
          biprod.inr ≫ (e j₃).inv ≫ ((F.tail i).mapLE (h12.trans h23) ≫ (e j₁).hom) ≫
              biprod.snd =
            biprod.inr ≫ (e j₃).inv ≫
                ((e j₃).hom ≫
                  biprod.map (𝟙 c.cone.pt)
                    (zmap (j := j₂) (j' := j₃) h23 ≫ zmap (j := j₁) (j' := j₂) h12)) ≫
              biprod.snd := by
        exact congrArg (fun f ↦ biprod.inr ≫ (e j₃).inv ≫ f ≫ biprod.snd) hcomp
      calc
        zmap (j := j₁) (j' := j₃) (h12.trans h23) =
            biprod.inr ≫ (e j₃).inv ≫
              ((F.tail i).mapLE (h12.trans h23) ≫ (e j₁).hom) ≫
                biprod.snd := by
          simp [zmap, Category.assoc]
        _ = biprod.inr ≫ (e j₃).inv ≫
              ((e j₃).hom ≫
                biprod.map (𝟙 c.cone.pt)
                  (zmap (j := j₂) (j' := j₃) h23 ≫ zmap (j := j₁) (j' := j₂) h12)) ≫
                biprod.snd := hcomp'
        _ = zmap (j := j₂) (j' := j₃) h23 ≫ zmap (j := j₁) (j' := j₂) h12 := by
          simp [zmap, Category.assoc]
    have hZ_map_id :
        ∀ j : OrderDual (Set.Ici i), (zmap (j := j) (j' := j) (leOfHom (𝟙 j))) = 𝟙 (Zobj j) := by
      intro j
      simpa using hzmap_id j
    have hZ_map_comp :
        ∀ {j₁ j₂ j₃ : OrderDual (Set.Ici i)} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃),
          zmap (j := j₃) (j' := j₁) (leOfHom (f ≫ g)) =
            zmap (j := j₂) (j' := j₁) (leOfHom f) ≫ zmap (j := j₃) (j' := j₂) (leOfHom g) := by
      intro j₁ j₂ j₃ f g
      have hle : leOfHom (f ≫ g) = (leOfHom g).trans (leOfHom f) := by
        apply Subsingleton.elim
      simpa [hle] using
        (show
            zmap (j := j₃) (j' := j₁) ((leOfHom g).trans (leOfHom f)) =
              zmap (j := j₂) (j' := j₁) (leOfHom f) ≫ zmap (j := j₃) (j' := j₂) (leOfHom g) from
            hzmap_comp (j₁ := j₃) (j₂ := j₂) (j₃ := j₁) (h12 := leOfHom g) (h23 := leOfHom f))
    let Z : OrderDual (Set.Ici i) ⥤ D where
      obj j := Zobj j
      map := fun {j j'} f ↦ zmap (j := j') (j' := j) (leOfHom f)
      map_id j := by
        -- Proof comment: the complementary block of the identity transition is the identity.
        simpa using hZ_map_id j
      map_comp f g := by
        -- Proof comment: the complementary blocks compose because `hblock` is compatible with
        -- tail composition and we already isolated that block calculus in `hZ_map_comp`.
        simpa using hZ_map_comp f g
    have eNat : F.tail i ≅ (Functor.const (OrderDual (Set.Ici i))).obj c.cone.pt ⊞ Z := by
      refine NatIso.ofComponents (fun j ↦ e j) ?_
      intro j j' f
      -- Proof comment: `hblock` is exactly the naturality equation after rewriting the target map
      -- of the biproduct functor to `biprod.map (𝟙 _) (Z.map f)`.
      simpa [Z, zmap, Functor.mapLE] using
        hblock (j := j') (j' := j) (leOfHom f)
    have hzeroZ :
        ∀ j : Set.Ici i, ∃ j' : Set.Ici i, ∃ hjj' : j ≤ j', Z.mapLE hjj' = 0 := by
      intro j
      rcases hzero_block j with ⟨j', hjj', hz⟩
      refine ⟨j', hjj', ?_⟩
      -- Proof comment: by definition, the complementary tail transition is the lower-right block
      -- extracted from the conjugated stage transition.
      simpa [Z, zmap, Functor.mapLE] using hz
    exact ⟨i, c.cone.pt, Z, eNat, hzeroZ⟩
  · rintro ⟨i, A, Z, e, hzero⟩
    have htailBiprod :
        IsEssentiallyConstantCofilteredDiagram
          (((Functor.const (OrderDual (Set.Ici i))).obj A) ⊞ Z) := by
      -- Proof comment: this is exactly the standard tail cone from the omitted converse in the
      -- source proof.
      exact essentiallyConstant_biprod_tail_of_eventual_zero (i := i) (A := A) hzero
    have htail :
        IsEssentiallyConstantCofilteredDiagram (F.tail i) := by
      rcases htailBiprod with ⟨c, hc⟩
      -- Proof comment: transport the explicit essentially constant cone across the given tail
      -- decomposition `e`.
      exact ⟨(Cone.postcompose e.inv).obj c, cofilteredCone_postcompose_iso hc e.symm⟩
    -- Proof comment: the tail inclusion is initial, so essential constancy on the tail is
    -- equivalent to essential constancy of the original inverse system.
    exact
      (essentiallyConstantCofilteredDiagram_iff_comp_initial
        (H := (OrderHom.Subtype.val (Set.Ici i)).dual.toFunctor) F).2 htail

end

end CategoryTheory
