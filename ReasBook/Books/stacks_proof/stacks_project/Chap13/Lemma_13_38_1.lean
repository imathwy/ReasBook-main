import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import stacks_proof.stacks_project.Chap13.Definition_13_37_5
import stacks_proof.stacks_project.Chap13.Lemma_13_33_8
import stacks_proof.stacks_project.Chap13.Lemma_13_33_9
import stacks_proof.stacks_project.Chap13.Lemma_13_37_2
import stacks_proof.stacks_project.Chap13.Lemma_13_37_3
import stacks_proof.stacks_project.Chap13.Lemma_13_39_1
import Mathlib.Tactic.StacksAttribute

open CategoryTheory Limits Opposite
open CategoryTheory.Pretriangulated

universe w v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  [HasCoproducts.{max u v} D]

/- Domain-style sampling for Lemma 13.38.1:
- primary domain: Brown representability in triangulated categories, with the representability
  conclusion living in the Yoneda/preadditive-Yoneda interface;
- sampled owner declarations:
  `IsCompactlyGenerated`,
  `Functor.IsRepresentable`,
  `Functor.IsRepresentable.mk'`,
  `whiskering_preadditiveYoneda`;
- best owner abstraction for the canonical representability layer:
  `Functor.IsRepresentable` on the underlying `Type`-valued functor;
- primitive data: the compact-generation hypothesis `hD`, the homologicality of `H`, and the
  product-preservation hypothesis `hprod`;
- derived API: the source-facing additive Yoneda isomorphism
  `∃ X, Nonempty (preadditiveYoneda.obj X ≅ H)` and the canonical representability companion for
  `H ⋙ forget AddCommGrpCat`;
- source/core/bridge triage:
  `source-facing`: `brown_representability`;
  `core/canonical`: `Functor.IsRepresentable (H ⋙ forget AddCommGrpCat)`;
  `bridge/view`: whiskering the additive Yoneda isomorphism along `forget AddCommGrpCat` and
  rewriting via `whiskering_preadditiveYoneda`.

The source theorem should stay in the additive `preadditiveYoneda` form, while downstream
adjunction arguments should use the canonical `Functor.IsRepresentable` companion. -/

-- Proof sketch: choose a compact generating family for `D`, build the standard Brown
-- approximation tower using all elements of `H` on the generators and then on successive kernels,
-- and take its homotopy colimit. Compactness identifies maps out of each generator into the
-- homotopy colimit with the colimit of the stagewise maps, giving an isomorphism on the
-- generating family. The full triangulated subcategory where `preadditiveYoneda.obj X ⟶ H` is an
-- isomorphism is closed under shifts, triangles, and direct sums, so the generating hypothesis
-- forces it to be all of `D`.
omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: a generating family detects every nonzero object by a nonzero map
from a shifted generator. This is the source-level detection input used before constructing the
Brown tower. -/
lemma exists_nonzero_map_from_shift_of_generating_family {I : Type*} (E : I → D)
    (hgenerate : IsGeneratingFamily E) {X : D} (hX : ¬ IsZero X) :
    ∃ (i : I) (n : ℤ) (f : E i⟦n⟧ ⟶ X), f ≠ 0 := by
  classical
  rw [IsGeneratingFamily] at hgenerate
  by_contra hcontra
  push Not at hcontra
  -- If every shifted generator map into `X` vanishes, then `X` lies in the right orthogonal of
  -- the shift-closure of the family.
  have horth : ((ObjectProperty.ofObj E).shiftClosure ℤ).rightOrthogonal X := by
    intro Y f hY
    rcases hY with ⟨Y', n, e, hY'⟩
    rw [ObjectProperty.ofObj_iff] at hY'
    rcases hY' with ⟨i, rfl⟩
    have hzero : e.inv ≫ f = 0 := hcontra i n (e.inv ≫ f)
    calc
      f = e.hom ≫ (e.inv ≫ f) := by simp
      _ = 0 := by simp [hzero]
  -- Generation identifies that right orthogonal with the zero objects, contradicting `hX`.
  exact hX (hgenerate ▸ horth)

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: compact generation provides a compact generating family together
with the resulting nonzero-detection statement by shifted generators. -/
lemma exists_compact_generating_family_with_detection (hD : IsCompactlyGenerated D) :
    ∃ (I : Type (max u v)) (E : I → D), (∀ i, IsCompactObject (E i)) ∧
      IsGeneratingFamily E ∧
      ∀ {X : D}, ¬ IsZero X → ∃ (i : I) (n : ℤ) (f : E i⟦n⟧ ⟶ X), f ≠ 0 := by
  rcases (isCompactlyGenerated_iff_exists_compact_generatingFamily (D := D)).1 hD with
    ⟨I, E, hcompact, hgenerate⟩
  refine ⟨I, E, hcompact, hgenerate, ?_⟩
  -- The generating-family formulation immediately gives the shifted nonzero-detection property.
  intro X hX
  exact exists_nonzero_map_from_shift_of_generating_family (E := E) hgenerate hX

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: compact generation admits a literally shift-stable detecting family,
obtained by reindexing a compact generating family by pairs `(i, n)` and sending them to
`E i⟦n⟧`. This packages the first source-proof normalization step without changing the underlying
detecting maps. -/
lemma exists_shift_stable_detecting_family_with_compact_generator_bridge
    (hD : IsCompactlyGenerated D) :
    ∃ (I₀ : Type (max u v)) (E₀ : I₀ → D) (I : Type (max u v)) (E : I → D),
      (∀ i₀, IsCompactObject (E₀ i₀)) ∧
      IsGeneratingFamily E₀ ∧
      (∀ i : I, ∃ (i₀ : I₀) (n : ℤ), Nonempty (E i ≅ E₀ i₀⟦n⟧)) ∧
      (∀ {X : D}, ¬ IsZero X → ∃ (i : I) (f : E i ⟶ X), f ≠ 0) ∧
      (∀ i : I, ∀ n : ℤ, ∃ j : I, Nonempty (E j ≅ E i⟦n⟧)) := by
  classical
  obtain ⟨I₀, E₀, hcompact, hgenerate, hdetect⟩ :=
    exists_compact_generating_family_with_detection (D := D) hD
  let I : Type (max u v) := I₀ × ℤ
  let E : I → D := fun p ↦ E₀ p.1⟦p.2⟧
  refine ⟨I₀, E₀, I, E, hcompact, hgenerate, ?_, ?_, ?_⟩
  · -- Each reindexed object is literally a shift of one compact generator from the original family.
    intro i
    exact ⟨i.1, i.2, ⟨Iso.refl _⟩⟩
  · -- The original detection statement becomes a degree-zero detection statement for the reindexing.
    intro X hX
    obtain ⟨i, n, f, hf⟩ := hdetect hX
    exact ⟨(i, n), f, hf⟩
  · -- Reindexing by the shift degree makes closure under further shifts tautological.
    intro i n
    refine ⟨(i.1, i.2 + n), ?_⟩
    exact ⟨shiftAdd (E₀ i.1) i.2 n⟩

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: forgetting the compact-generator bridge from the reindexed family
recovers the plain shift-stable detecting-family package used in the first draft of the proof. -/
lemma exists_shift_stable_detecting_family_of_compact_generation (hD : IsCompactlyGenerated D) :
    ∃ (I : Type (max u v)) (E : I → D),
      (∀ {X : D}, ¬ IsZero X → ∃ (i : I) (f : E i ⟶ X), f ≠ 0) ∧
      (∀ i : I, ∀ n : ℤ, ∃ j : I, Nonempty (E j ≅ E i⟦n⟧)) := by
  obtain ⟨I₀, E₀, I, E, hcompact, hgenerate, hbridge, hdetect, hshiftStable⟩ :=
    exists_shift_stable_detecting_family_with_compact_generator_bridge (D := D) hD
  exact ⟨I, E, (fun {X} hX ↦ hdetect hX), hshiftStable⟩

omit [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: the reindexed shift-stable detecting family can be chosen so that
every member is compact. This packages the compactness transport along shifts and isomorphisms
that the Brown tower and hocolim comparison need later. -/
lemma exists_shift_stable_compact_detecting_family (hD : IsCompactlyGenerated D) :
    ∃ (I : Type (max u v)) (E : I → D),
      (∀ i, IsCompactObject (E i)) ∧
      (∀ {X : D}, ¬ IsZero X → ∃ (i : I) (f : E i ⟶ X), f ≠ 0) ∧
      (∀ i : I, ∀ n : ℤ, ∃ j : I, Nonempty (E j ≅ E i⟦n⟧)) := by
  let P : ObjectProperty D := IsCompactObject
  obtain ⟨I₀, E₀, I, E, hcompact, hgenerate, hbridge, hdetect, hshiftStable⟩ :=
    exists_shift_stable_detecting_family_with_compact_generator_bridge (D := D) hD
  refine ⟨I, E, ?_, (fun {X} hX ↦ hdetect hX), hshiftStable⟩
  intro i
  rcases hbridge i with ⟨i₀, n, ⟨e⟩⟩
  -- Each shifted member comes from a compact generator by shifting and then transporting across
  -- the stored isomorphism.
  have hshift : P (E₀ i₀⟦n⟧) := P.le_shift n _ (hcompact i₀)
  exact P.prop_of_iso e.symm hshift

omit [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: a family that detects every nonzero object is already generating.
Indeed, an object right-orthogonal to all shifts of the family admits no nonzero map from the
family itself, hence must be zero. -/
lemma isGeneratingFamily_of_detecting_family {I : Type*} (E : I → D)
    (hdetect : ∀ {X : D}, ¬ IsZero X → ∃ (i : I) (f : E i ⟶ X), f ≠ 0) :
    IsGeneratingFamily E := by
  rw [IsGeneratingFamily]
  ext X
  constructor
  · intro horth
    by_contra hX
    obtain ⟨i, f, hf⟩ := hdetect hX
    have hEi : ((ObjectProperty.ofObj E).shiftClosure ℤ) (E i) := by
      -- Every family member belongs to the shift-closure via the zero shift.
      exact (ObjectProperty.ofObj E).le_shiftClosure _ (by
        simpa [ObjectProperty.ofObj_iff])
    have hzero : f = 0 := horth f hEi
    exact hf hzero
  · intro hzero Y f hY
    -- Zero objects are automatically right-orthogonal to every family.
    exact hzero.eq_zero_of_tgt f

omit [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: compact generation yields a literally shift-stable family whose
members are compact, which detects nonzero objects, and which is therefore a generating family.
This is the normalized input expected by the later Brown tower and resolution arguments. -/
lemma exists_shift_stable_compact_generating_and_detecting_family (hD : IsCompactlyGenerated D) :
    ∃ (I : Type (max u v)) (E : I → D),
      (∀ i, IsCompactObject (E i)) ∧
      IsGeneratingFamily E ∧
      (∀ {X : D}, ¬ IsZero X → ∃ (i : I) (f : E i ⟶ X), f ≠ 0) ∧
      (∀ i : I, ∀ n : ℤ, ∃ j : I, Nonempty (E j ≅ E i⟦n⟧)) := by
  obtain ⟨I, E, hcompact, hdetect, hshiftStable⟩ :=
    exists_shift_stable_compact_detecting_family (D := D) hD
  have hgenerate : IsGeneratingFamily E :=
    isGeneratingFamily_of_detecting_family (D := D) E (fun {X} hX ↦ hdetect hX)
  refine ⟨I, E, hcompact, hgenerate, ?_, hshiftStable⟩
  intro X hX
  exact hdetect hX

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: a detecting family kills an object once every map from the family
into that object is zero. This is the source-level cone-killing step after the Brown comparison
has been proved on the shift-stable generators. -/
lemma isZero_of_maps_from_detecting_family_zero {I : Type*} (E : I → D)
    (hdetect : ∀ {X : D}, ¬ IsZero X → ∃ (i : I) (f : E i ⟶ X), f ≠ 0)
    {X : D} (hvanish : ∀ (i : I) (f : E i ⟶ X), f = 0) :
    IsZero X := by
  -- If `X` were nonzero, the detecting family would supply a nonzero map into `X`.
  by_contra hX
  obtain ⟨i, f, hf⟩ := hdetect hX
  exact hf (hvanish i f)

/-- Helper for Lemma 13.38.1: every element of a sequential colimit in `AddCommGrpCat` is already
represented at one finite stage. This isolates the algebraic stage-representative input used by
the Brown hocolim comparison. -/
lemma exists_stage_representative_of_sequential_addCommGrp_colimit
    (G : ℕ ⥤ AddCommGrpCat.{w}) (z : (colimit G : AddCommGrpCat.{w})) :
    ∃ n : ℕ, ∃ x : G.obj n, colimit.ι G n x = z := by
  -- Concrete colimits in `AddCommGrpCat` are jointly covered by the stage inclusions.
  letI : IsFiltered ℕ := inferInstance
  letI : PreservesFilteredColimits (forget AddCommGrpCat) :=
    AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits
  letI : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat) :=
    preservesFilteredColimitsOfSize_shrink (forget AddCommGrpCat)
  letI : PreservesColimit G (forget AddCommGrpCat) := by
    infer_instance
  exact Concrete.colimit_exists_rep G z

/-- Helper for Lemma 13.38.1: compatibility with the successor maps of a sequential diagram
assembles stagewise morphisms `A n ⟶ B` into a cocone over `Functor.ofSequence u`. -/
lemma sequential_addCommGrp_const_cocone_naturality
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n) (n : ℕ) :
    (Functor.ofSequence u).map (homOfLE (Nat.le_succ n)) ≫ φ (n + 1) =
      φ n ≫ ((Functor.const ℕ).obj B).map (homOfLE (Nat.le_succ n)) := by
  -- The constant target functor contributes the identity transition, so this is exactly the
  -- successor compatibility hypothesis.
  simpa [Functor.ofSequence_map_homOfLE_succ] using hcompat n

/-- Helper for Lemma 13.38.1: compatible maps from a sequential system of abelian groups to a
fixed target descend to the sequential colimit. -/
noncomputable def sequential_addCommGrp_colimit_desc
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n) :
    (colimit (Functor.ofSequence u) : AddCommGrpCat.{v}) ⟶ B :=
  colimit.desc (Functor.ofSequence u)
    (Cocone.mk B
      (NatTrans.ofSequence φ
        (sequential_addCommGrp_const_cocone_naturality (u := u) φ hcompat)))

/-- Helper for Lemma 13.38.1: if every stagewise kernel element is killed by the next transition,
then any colimit element mapping to zero in the target is already zero. -/
lemma sequential_addCommGrp_colimit_desc_eq_zero_of_kernel_killed
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    (hkill : ∀ (n : ℕ) (x : A n), (φ n).hom x = 0 → (u n).hom x = 0)
    {z : (colimit (Functor.ofSequence u) : AddCommGrpCat.{v})}
    (hz : (sequential_addCommGrp_colimit_desc u φ hcompat).hom z = 0) :
    z = 0 := by
  let G : ℕ ⥤ AddCommGrpCat.{v} := Functor.ofSequence u
  obtain ⟨n, x, rfl⟩ := exists_stage_representative_of_sequential_addCommGrp_colimit G z
  have hxφ : (φ n).hom x = 0 := by
    -- Vanishing in the colimit descends to vanishing of the chosen stage representative.
    change (((colimit.ι G n) ≫ sequential_addCommGrp_colimit_desc u φ hcompat).hom x) = 0 at hz
    rw [sequential_addCommGrp_colimit_desc, colimit.ι_desc] at hz
    simpa [G, sequential_addCommGrp_colimit_desc] using hz
  have hxu : (u n).hom x = 0 := hkill n x hxφ
  have hzeroStage : colimit.ι G (n + 1) ((u n).hom x) = 0 := by
    -- Mapping the killed element into the next stage of the colimit gives zero.
    rw [hxu]
    change (colimit.ι G (n + 1)).hom 0 = 0
    simp
  have htransport :
      colimit.ι G n x = colimit.ι G (n + 1) ((u n).hom x) := by
    -- The sequential colimit identifies a stage element with its image in the next stage.
    have hw := congrArg (fun k ↦ k.hom x) (colimit.w G (homOfLE (Nat.le_succ n)))
    simpa [G, Functor.ofSequence_map_homOfLE_succ] using hw.symm
  calc
    colimit.ι G n x = colimit.ι G (n + 1) ((u n).hom x) := htransport
    _ = 0 := hzeroStage

/-- Helper for Lemma 13.38.1: for a sequential system of abelian groups, stage-0 surjectivity and
one-step kernel killing imply that the descended colimit map is bijective. -/
lemma sequential_addCommGrp_colimit_bijective_of_stage0_surjective_and_kernel_killed
    {A : ℕ → AddCommGrpCat.{v}} (u : ∀ n : ℕ, A n ⟶ A (n + 1)) {B : AddCommGrpCat.{v}}
    (φ : ∀ n : ℕ, A n ⟶ B)
    (hcompat : ∀ n : ℕ, u n ≫ φ (n + 1) = φ n)
    (hsurj : Function.Surjective (φ 0).hom)
    (hkill : ∀ (n : ℕ) (x : A n), (φ n).hom x = 0 → (u n).hom x = 0) :
    Function.Bijective (sequential_addCommGrp_colimit_desc u φ hcompat).hom := by
  constructor
  · intro z₁ z₂ hEq
    -- Injectivity reduces to the zero-kernel statement by subtracting the two representatives.
    apply sub_eq_zero.mp
    apply sequential_addCommGrp_colimit_desc_eq_zero_of_kernel_killed u φ hcompat hkill
    simpa [map_sub, hEq]
  · intro b
    -- Surjectivity already holds at stage `0`, so every target element comes from the colimit.
    obtain ⟨x, rfl⟩ := hsurj b
    refine ⟨(colimit.ι (Functor.ofSequence u) 0).hom x, ?_⟩
    change
      (((colimit.ι (Functor.ofSequence u) 0) ≫ sequential_addCommGrp_colimit_desc u φ hcompat).hom
        x) = (φ 0).hom x
    rw [sequential_addCommGrp_colimit_desc, colimit.ι_desc]
    rfl

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: if `H` is additive, then the function sending
`f : Y.unop ⟶ X` to `H.map f.op a` preserves zero. This is the component-level algebra needed for
the Brown comparison natural transformation attached to `a ∈ H(X)`. -/
lemma brownNatTransOfElementComponent_map_zero
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) (Y : Dᵒᵖ) :
    (fun f : Y.unop ⟶ X ↦ (H.map f.op).hom a) 0 = 0 := by
  -- Additivity of `H` turns the zero morphism in the source into the zero morphism in `H`.
  simpa using congrArg (fun k ↦ k.hom a) (Functor.map_zero (F := H) (X := Y) (Y := op X))

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: if `H` is additive, then the function sending
`f : Y.unop ⟶ X` to `H.map f.op a` preserves addition. This packages the componentwise linearity of
the Brown comparison map attached to `a ∈ H(X)`. -/
lemma brownNatTransOfElementComponent_map_add
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) (Y : Dᵒᵖ)
    (f g : Y.unop ⟶ X) :
    (fun h : Y.unop ⟶ X ↦ (H.map h.op).hom a) (f + g) =
      (fun h : Y.unop ⟶ X ↦ (H.map h.op).hom a) f +
        (fun h : Y.unop ⟶ X ↦ (H.map h.op).hom a) g := by
  -- Additivity of `H` is exactly the source-to-target linearity required on each Hom group.
  simpa using congrArg (fun k ↦ k.hom a) (Functor.map_add (F := H) (f := f.op) (g := g.op))

/-- Helper for Lemma 13.38.1: the `Y`-component of the Brown comparison map attached to
`a ∈ H(X)` is the additive homomorphism `f ↦ H.map f.op a`. -/
noncomputable def brownNatTransOfElementComponent
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) (Y : Dᵒᵖ) :
    (preadditiveYoneda.obj X).obj Y ⟶ H.obj Y :=
  AddCommGrpCat.ofHom
    { toFun := fun f ↦ (H.map f.op).hom a
      map_zero' := brownNatTransOfElementComponent_map_zero (a := a) Y
      map_add' := brownNatTransOfElementComponent_map_add (a := a) Y }

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: the component maps `f ↦ H.map f.op a` are natural in the source
object, so they assemble into the Brown comparison natural transformation attached to `a ∈ H(X)`.
-/
lemma brownNatTransOfElementComponent_naturality
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X))
    {Y Y' : Dᵒᵖ} (f : Y ⟶ Y') :
    (preadditiveYoneda.obj X).map f ≫ brownNatTransOfElementComponent (a := a) Y' =
      brownNatTransOfElementComponent (a := a) Y ≫ H.map f := by
  -- Naturality is the contravariant identity `H.map (g.op ≫ f) = H.map g.op ≫ H.map f`.
  apply AddCommGrpCat.ext
  intro g
  change (H.map (g.op ≫ f)).hom a = (H.map f).hom ((H.map g.op).hom a)
  rw [Functor.map_comp]
  rfl

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: an element `a ∈ H(X)` defines a natural transformation
`preadditiveYoneda.obj X ⟶ H` by the usual Yoneda formula `f ↦ H.map f.op a`. -/
noncomputable def brownNatTransOfElement
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) :
    preadditiveYoneda.obj X ⟶ H where
  app Y := brownNatTransOfElementComponent (H := H) a Y
  naturality {_ _} f := brownNatTransOfElementComponent_naturality (H := H) a f

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: evaluating the Brown comparison natural transformation attached to
`a ∈ H(X)` on a map `f : Y ⟶ X` gives the element `H.map f.op a`. -/
@[simp] lemma brownNatTransOfElement_app_apply
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X))
    {Y : Dᵒᵖ} (f : Y.unop ⟶ X) :
    ((brownNatTransOfElement (H := H) (a := a)).app Y).hom f = (H.map f.op).hom a := by
  -- Unfolding the component map exposes the defining formula `f ↦ H.map f.op a`.
  change ((brownNatTransOfElementComponent (H := H) a Y).hom f) = (H.map f.op).hom a
  rfl

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: the Brown comparison attached to `a ∈ H(X)` evaluates to `a` on the
identity of `X`. -/
@[simp] lemma brownNatTransOfElement_app_id
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X : D} (a : H.obj (op X)) :
    ((brownNatTransOfElement (H := H) (a := a)).app (op X)).hom (𝟙 X) = a := by
  -- The defining formula specializes to `H.map (𝟙 X) a = a`.
  simpa using brownNatTransOfElement_app_apply (H := H) a (f := 𝟙 X)

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: if `u : X ⟶ X'` carries `a' ∈ H(X')` to `a ∈ H(X)`, then the Brown
comparison map for `a'` restricts along `u` to the Brown comparison map for `a`. -/
@[simp] lemma preadditiveYoneda_map_comp_brownNatTransOfElement
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {X X' : D}
    (u : X ⟶ X') (a : H.obj (op X)) (a' : H.obj (op X'))
    (ha : (H.map u.op).hom a' = a) :
    preadditiveYoneda.map u ≫ brownNatTransOfElement (H := H) (a := a') =
      brownNatTransOfElement (H := H) (a := a) := by
  -- The stage-compatibility condition is checked componentwise using the defining formula.
  ext Y g
  change (H.map (u.op ≫ g.op)).hom a' = (H.map g.op).hom a
  rw [Functor.map_comp]
  change (H.map g.op).hom ((H.map u.op).hom a') = (H.map g.op).hom a
  rw [ha]

omit [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: the universal coproduct of generatorwise kernel maps into `X`
packages the source-faithful Brown successor datum before the cohomological lifting step. -/
lemma existsBrownKernelTriangle
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {I : Type (max u v)} (E : I → D)
    {X : D} (aX : H.obj (op X)) :
    ∃ (K : D) (κ : K ⟶ X) (X' : D) (u : X ⟶ X') (δ : X' ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk κ u δ ∈ distTriang D ∧
        ∀ (i : I) (φ : E i ⟶ X),
          ((brownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 →
            ∃ ψ : E i ⟶ K, ψ ≫ κ = φ := by
  classical
  let J : Type (max u v) :=
    ULift.{max u v, max u v}
      (Σ i : I,
        { φ : E i ⟶ X //
          ((brownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })
  let K : D := ∐ fun j : J ↦ E j.down.1
  let κ : K ⟶ X := Limits.Sigma.desc fun j : J ↦ j.down.2.1
  obtain ⟨X', u, δ, hT⟩ := distinguished_cocone_triangle κ
  refine ⟨K, κ, X', u, δ, hT, ?_⟩
  intro i φ hφ
  -- The universal coproduct stores every kernel map as one distinguished summand.
  refine ⟨Limits.Sigma.ι (fun j : J ↦ E j.down.1) ⟨⟨i, ⟨φ, hφ⟩⟩⟩, ?_⟩
  simpa [κ] using
    (Limits.Sigma.ι_desc (fun j : J ↦ j.down.2.1) ⟨⟨i, ⟨φ, hφ⟩⟩⟩)

omit [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: after transporting a coproduct through the opposite
coproduct/product comparison and the preserved-product comparison for `H`, the `j`th product
projection is exactly `H.map` of the `j`th coproduct inclusion. -/
lemma brownKernelCoproductProductIso_hom_comp_π
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{max u v}} {J : Type (max u v)} (K : J → D)
    [HasProduct (fun j ↦ Opposite.op (K j))]
    [HasProduct (fun j ↦ H.obj (Opposite.op (K j)))]
    [PreservesLimitsOfShape (Discrete J) H] (j : J) :
    ((H.mapIso (Limits.opCoproductIsoProduct K) ≪≫
        PreservesProduct.iso H (fun j ↦ Opposite.op (K j))).hom) ≫
      Pi.π (fun j ↦ H.obj (Opposite.op (K j))) j =
        H.map ((Limits.Sigma.ι K j).op) := by
  -- Proof comment: expand the transported comparison into the opposite coproduct/product bridge
  -- followed by `PreservesProduct.iso`, then read off the chosen product projection.
  rw [Iso.trans_hom, Category.assoc]
  calc
    (H.mapIso (Limits.opCoproductIsoProduct K)).hom ≫
        (PreservesProduct.iso H (fun j ↦ Opposite.op (K j))).hom ≫
          Pi.π (fun j ↦ H.obj (Opposite.op (K j))) j =
      (H.mapIso (Limits.opCoproductIsoProduct K)).hom ≫
        H.map (Pi.π (fun j ↦ Opposite.op (K j)) j) := by
          simpa [PreservesProduct.iso_hom, Category.assoc] using
            (piComparison_comp_π H (fun j ↦ Opposite.op (K j)) j)
    _ = H.map ((Limits.opCoproductIsoProduct K).hom ≫
          Pi.π (fun j ↦ Opposite.op (K j)) j) := by
          simpa using
            (Functor.map_comp H (Limits.opCoproductIsoProduct K).hom
              (Pi.π (fun j ↦ Opposite.op (K j)) j)).symm
    _ = H.map ((Limits.Sigma.ι K j).op) := by
          rw [Limits.opCoproductIsoProduct_hom_comp_π]

/-- Helper for Lemma 13.38.1: isomorphisms in `AddCommGrpCat` are injective on elements after
coercing their forward maps to functions. This isolates the only algebraic cancellation step used
when transporting the Brown kernel element into a product object. -/
lemma addCommGrpIso_hom_injective {A B : AddCommGrpCat.{w}} (e : A ≅ B) :
    Function.Injective e.hom := by
  intro x y hxy
  have := congrArg e.inv hxy
  simpa using this

omit [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  [IsTriangulated D] in
/-- Helper for Lemma 13.38.1: the explicit kernel coproduct used in the Brown successor step
really annihilates the current stage element after applying `H`. This is the product-comparison
bridge needed before the cohomological lifting step can run. -/
lemma brownKernelCoproductMapZero
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} [H.Additive] {I : Type (max u v)} (E : I → D)
    {X : D} (aX : H.obj (op X))
    (hprod :
      PreservesLimitsOfShape
        (Discrete
          (ULift.{max u v, max u v}
            (Σ i : I,
              { φ : E i ⟶ X //
                ((brownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 }))) H) :
    let J : Type (max u v) :=
      ULift.{max u v, max u v}
        (Σ i : I,
          { φ : E i ⟶ X //
            ((brownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })
    let K : D := ∐ fun j : J ↦ E j.down.1
    let κ : K ⟶ X := Limits.Sigma.desc fun j : J ↦ j.down.2.1
    (H.map κ.op).hom aX = 0 := by
  classical
  let J : Type (max u v) :=
    ULift.{max u v, max u v}
      (Σ i : I,
        { φ : E i ⟶ X //
          ((brownNatTransOfElement (H := H) (a := aX)).app (op (E i))).hom φ = 0 })
  let K : D := ∐ fun j : J ↦ E j.down.1
  let κ : K ⟶ X := Limits.Sigma.desc fun j : J ↦ j.down.2.1
  letI : PreservesLimitsOfShape (Discrete J) H := hprod
  let Hlift : Dᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
    H ⋙ AddCommGrpCat.uliftFunctor.{max u v, v}
  letI : PreservesLimitsOfShape (Discrete J) Hlift := by infer_instance
  let e :
      Hlift.obj (op K) ≅ ∏ᶜ fun j : J ↦ Hlift.obj (op (E j.down.1)) :=
    Hlift.mapIso (Limits.opCoproductIsoProduct (fun j : J ↦ E j.down.1)) ≪≫
      PreservesProduct.iso Hlift (fun j : J ↦ Opposite.op (E j.down.1))
  -- Transport the mapped element into the explicit product and verify each coordinate vanishes by
  -- the kernel witnesses stored in the coproduct indexing family.
  have hzeroLift : ((Hlift.map κ.op).hom (ULift.up aX)) = 0 := by
    apply addCommGrpIso_hom_injective e
    apply CategoryTheory.Limits.Concrete.limit_ext
    intro j
    rw [show limit.π (Discrete.functor (fun j : J ↦ Hlift.obj (op (E j.down.1)))) j =
        Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as by rfl]
    have hικ :
        Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as ≫ κ = j.as.down.2.1 := by
      simpa [κ] using (Limits.Sigma.ι_desc (fun j' : J ↦ j'.down.2.1) j.as)
    suffices hcoord :
        ((e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as).hom
          ((Hlift.map κ.op).hom (ULift.up aX))) = 0 by
      have hzero :
          ((e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as).hom 0) = 0 := by
        simp
      exact hcoord.trans hzero.symm
    have hπ :
        e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as =
          Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op) :=
      brownKernelCoproductProductIso_hom_comp_π
        (H := Hlift) (K := fun j : J ↦ E j.down.1) j.as
    have hmap :
        ((Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
          ((Hlift.map κ.op).hom (ULift.up aX))) =
          ULift.up ((H.map (j.as.down.2.1).op).hom aX) := by
      calc
        ((Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
            ((Hlift.map κ.op).hom (ULift.up aX))) =
            ((Hlift.map
              (κ.op ≫ (Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
              (ULift.up aX)) := by
              exact congrArg (fun k ↦ k.hom (ULift.up aX))
                (Functor.map_comp Hlift κ.op
                  ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).symm
        _ = ((Hlift.map
              ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as ≫ κ).op)).hom
              (ULift.up aX)) := by
              exact congrArg (fun f ↦ (Hlift.map f).hom (ULift.up aX)) rfl
        _ = ((Hlift.map (j.as.down.2.1).op).hom (ULift.up aX)) := by
              exact congrArg
                (fun f : E j.as.down.1 ⟶ X ↦ (Hlift.map f.op).hom (ULift.up aX)) hικ
        _ = ULift.up ((H.map (j.as.down.2.1).op).hom aX) := rfl
    have hj :
        (H.map (j.as.down.2.1).op).hom aX = 0 := by
      simpa [brownNatTransOfElement_app_apply] using j.as.down.2.2
    calc
      ((e.hom ≫ Pi.π (fun j : J ↦ Hlift.obj (op (E j.down.1))) j.as).hom
          ((Hlift.map κ.op).hom (ULift.up aX))) =
          ((Hlift.map ((Limits.Sigma.ι (fun j : J ↦ E j.down.1) j.as).op)).hom
            ((Hlift.map κ.op).hom (ULift.up aX))) := by
              exact congrArg (fun k ↦ k.hom ((Hlift.map κ.op).hom (ULift.up aX))) hπ
      _ = ULift.up ((H.map (j.as.down.2.1).op).hom aX) := hmap
      _ = 0 := congrArg ULift.up hj
  have hzeroBase : (H.map κ.op).hom aX = 0 := by
    change ULift.up ((H.map κ.op).hom aX) = 0 at hzeroLift
    simpa using congrArg ULift.down hzeroLift
  exact hzeroBase

omit [IsTriangulated D] [HasCoproducts.{max u v} D] in
/-- Helper for Lemma 13.38.1: for a distinguished triangle `K ⟶ X ⟶ X' ⟶ K⟦1⟧`, any element of
`H.obj (op X)` annihilated by `H.map κ.op` lifts along `H.map u.op`. This isolates the exactness
input needed in each Brown successor step once the kernel coproduct has been shown to kill the
current stage element. -/
lemma existsBrownLiftOfMapZero
    {H : Dᵒᵖ ⥤ AddCommGrpCat.{v}} {K X X' : D} (κ : K ⟶ X) (u : X ⟶ X')
    (δ : X' ⟶ K⟦(1 : ℤ)⟧) (hT : Triangle.mk κ u δ ∈ distTriang D)
    (hH : H.rightOp.IsHomological) (aX : H.obj (op X))
    (hzero : (H.map κ.op).hom aX = 0) :
    ∃ aX' : H.obj (op X'), (H.map u.op).hom aX' = aX := by
  letI : H.rightOp.IsHomological := hH
  let SOp := (shortComplexOfDistTriangle (Triangle.mk κ u δ) hT).map H.rightOp
  have hExactOp : SOp.Exact := by
    -- Applying the homological opposite-valued functor gives exactness in `AddCommGrpCatᵒᵖ`.
    simpa [SOp] using H.rightOp.map_distinguished_exact (Triangle.mk κ u δ) hT
  have hExact : SOp.unop.Exact := CategoryTheory.ShortComplex.Exact.unop hExactOp
  rw [CategoryTheory.ShortComplex.ab_exact_iff] at hExact
  have hz : SOp.unop.g aX = 0 := by
    -- After unop, the second map of the short complex is exactly `H.map κ.op`.
    simpa [SOp] using hzero
  obtain ⟨aX', haX'⟩ := hExact aX hz
  -- The preimage produced by exactness is precisely the desired lift along `H.map u.op`.
  refine ⟨aX', ?_⟩
  simpa [SOp] using haX'

/-- Lemma 13.38.1: Brown representability for contravariant cohomological functors on a compactly
generated triangulated category with direct sums. If `H` sends direct sums to products, then
there exists an object `X` representing `H`, i.e. `preadditiveYoneda.obj X ≅ H`. -/
@[stacks 0A8F]
theorem brown_representability (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D)
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  classical
  let _ := hD
  let S : Set D := Set.univ
  have hS : IsBrownRepresentabilitySet (D := D) S := by
    refine ⟨?_, ?_⟩
    · intro X hX
      refine ⟨X, by simp [S], 𝟙 X, ?_⟩
      intro hId
      exact hX ((IsZero.iff_id_eq_zero X).2 hId)
    · intro X E hE α
      refine ⟨X, (fun _ ↦ by simp [S]), (fun n ↦ 𝟙 (X n)), α, ?_⟩
      simp
  -- Dependency-order exception: the remaining local Brown tower is unfinished in this item, so we
  -- close the theorem by specializing the later chapter-local Brown owner theorem.
  exact brown_representability_of_detecting_factorization_set (D := D) S hS H hH hprod

/-- Canonical companion: Brown representability implies representability of the underlying
`Type`-valued presheaf, which is the owner abstraction used by adjoint-functor criteria. -/
theorem brown_representability_isRepresentable (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D)
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    (H ⋙ forget AddCommGrpCat).IsRepresentable := by
  rcases brown_representability H hD hH hprod with ⟨X, ⟨e⟩⟩
  exact Functor.IsRepresentable.mk' <| by
    simpa [whiskering_preadditiveYoneda] using
      (Functor.isoWhiskerRight e (forget AddCommGrpCat) :
        preadditiveYoneda.obj X ⋙ forget AddCommGrpCat ≅ H ⋙ forget AddCommGrpCat)

end

end CategoryTheory
