import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import StacksProject_2024.stacks_project.Chap13.Definition_13_37_5
import StacksProject_2024.stacks_project.Chap13.Lemma_13_37_2

open CategoryTheory Limits Opposite

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

/-- Helper for Lemma 13.38.1: forgetting the compact-generator bridge from the reindexed family
recovers the plain shift-stable detecting-family package used in the first draft of the proof. -/
lemma exists_shift_stable_detecting_family_of_compact_generation (hD : IsCompactlyGenerated D) :
    ∃ (I : Type (max u v)) (E : I → D),
      (∀ {X : D}, ¬ IsZero X → ∃ (i : I) (f : E i ⟶ X), f ≠ 0) ∧
      (∀ i : I, ∀ n : ℤ, ∃ j : I, Nonempty (E j ≅ E i⟦n⟧)) := by
  obtain ⟨I₀, E₀, I, E, hcompact, hgenerate, hbridge, hdetect, hshiftStable⟩ :=
    exists_shift_stable_detecting_family_with_compact_generator_bridge (D := D) hD
  exact ⟨I, E, (fun {X} hX ↦ hdetect hX), hshiftStable⟩

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
  · intro hzero
    -- Zero objects are automatically right-orthogonal to every family.
    intro Y f hY
    exact hzero.eq_zero_of_tgt f

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

/-- Lemma 13.38.1: Brown representability for contravariant cohomological functors on a compactly
generated triangulated category with direct sums. If `H` sends direct sums to products, then
there exists an object `X` representing `H`, i.e. `preadditiveYoneda.obj X ≅ H`. -/
theorem brown_representability (H : Dᵒᵖ ⥤ AddCommGrpCat.{v})
    (hD : IsCompactlyGenerated D)
    (hH : H.rightOp.IsHomological)
    (hprod : ∀ J : Type (max u v), PreservesLimitsOfShape (Discrete J) H) :
    ∃ X : D, Nonempty (preadditiveYoneda.obj X ≅ H) := by
  classical
  obtain ⟨I, E, hcompact, hgenerate, hdetect, hshiftStable⟩ :=
    exists_shift_stable_compact_generating_and_detecting_family (D := D) hD
  -- Route correction: the source proof needs the normalized family only in the form actually used
  -- later, namely compactness, generation, nonzero detection, and literal shift-stability.
  -- The new helper above packages exactly that data, so the remaining blocker is no longer about
  -- normalizing generators; it is the Brown tower/hocolim comparison built on this family.
  -- At this point the final globalization route is ready to invoke
  -- `exists_generating_family_resolution (E := E) hcompact hgenerate` once the comparison map on
  -- the shift-stable generators has been constructed.
  -- TODO: construct the Brown tower from the values of `H` on the shifted generators `E i⟦n⟧`,
  -- pass to its homotopy colimit, prove the resulting comparison is an isomorphism on the
  -- shift-stable family using compactness and the one-step kernel-killing property, and then
  -- globalize from `hgenerate` together with `hdetect`.
  sorry

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
