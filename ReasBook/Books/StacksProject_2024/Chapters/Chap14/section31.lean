import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_14_31_1 (from Chap14) -/
open CategoryTheory HomotopicalAlgebra Simplicial

open scoped SSet.modelCategoryQuillen

universe u v

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Definition 14.31.1:
- primary domain: simplicial-set fibrations and fibrant objects in the Quillen model structure;
- inspected owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `HomotopicalAlgebra.isFibrant_iff`,
  `SSet.KanComplex`;
- best owner abstractions:
  `Fibration f` for Kan fibrations, and `KanComplex X` for Kan complexes;
- primitive-vs-derived split:
  primitive data: none beyond the owner predicates themselves;
  derived API: the horn-inclusion lifting characterization of `Fibration`, and the terminal-map
  characterization of `KanComplex` via `IsFibrant`.

Source/core/bridge triage:
- `source-facing`: the textbook notions of Kan fibration and Kan complex for simplicial sets;
- `core/canonical`: `Fibration` on morphisms and `KanComplex`/`IsFibrant` on objects;
- `bridge/view`: the horn-filling reformulation for fibrations and the terminal-map reformulation
  for fibrant objects.

This item introduces no new simplicial-set data, so the correct refinement is to reuse the owner
predicates directly and keep only the genuinely source-facing reformulation as a local theorem. -/

/- Definition 14.31.1 (1): for a morphism `f : X ⟶ Y` of simplicial sets, the Stacks notion of
a Kan fibration is the canonical predicate `HomotopicalAlgebra.Fibration f`; in `SSet`, this is
the right lifting property with respect to all horn inclusions `Λ[n + 1, i].ι`. -/
recall HomotopicalAlgebra.Fibration

/- Bridge/view companion to Definition 14.31.1 (1): in simplicial sets, the canonical owner
`Fibration f` is exactly the horn-inclusion right lifting property. -/
theorem fibration_iff_has_horn_lifting_property :
    Fibration f ↔ ∀ ⦃n : ℕ⦄ (i : Fin (n + 2)), HasLiftingProperty (Λ[n + 1, i].ι) f := by
  rw [fibration_iff]
  constructor
  · intro hf n i
    exact hf _ (horn_ι_mem_J n i)
  · intro hf A B g hg
    rw [J, CategoryTheory.MorphismProperty.iSup_iff] at hg
    rcases hg with ⟨n, hg⟩
    cases hg with
    | mk i => simpa using hf i

/- Definition 14.31.1 (2): a Kan complex is the canonical predicate `SSet.KanComplex X`,
meaning that the terminal morphism `X ⟶ ⊤_ SSet` is a Kan fibration. -/
recall SSet.KanComplex
recall HomotopicalAlgebra.isFibrant_iff

end SSet

/-! ### Lemma_14_31_2 (from Chap14) -/
open CategoryTheory Simplicial
open CategoryTheory.Limits
open HomotopicalAlgebra
open SSet.modelCategoryQuillen

open scoped SSet.modelCategoryQuillen

universe u

section

variable {X Y Y' : SSet.{u}}
variable {f : X ⟶ Y} {g : Y' ⟶ Y}

/- Domain-style sampling for Lemma 14.31.2:
- primary domain: simplicial-set fibrations in the Quillen model structure;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  the generic base-change instance
  `[CategoryWithFibrations C] [(fibrations C).IsStableUnderBaseChange]
    [Fibration f] : Fibration (pullback.snd f g)`,
  `CategoryTheory.MorphismProperty.rlp_isStableUnderBaseChange`.
- best owner abstraction: the canonical predicate `Fibration`, with base-change closure supplied by
  the ambient owner morphism property `fibrations SSet`;
- primitive data: the morphism `f` together with the owner property `Fibration f`;
- derived API: the pulled-back fibration statement on `pullback.snd f g`.

Source/core/bridge triage:
- `source-facing`: the statement that a base change of a Kan fibration is again a Kan fibration;
- `core/canonical`: the generic base-change instance for `Fibration`;
- `bridge/view`: the horn-filling identification `SSet.modelCategoryQuillen.fibration_iff`.

This item introduces no new source-facing data beyond the owner property `Fibration f`, so the
correct refinement is to reuse the generic `Fibration` pullback instance directly. In `SSet`,
the needed owner-property stability is already synthesized from mathlib's model-category
infrastructure, so the public statement needs no parallel local instance and no extra
`[HasPullback f g]` binder. -/

variable [Fibration f]

/- Lemma 14.31.2: the base change of a Kan fibration of simplicial sets is again a Kan
fibration. Canonically, this is the generic pullback instance for `Fibration`. -/
#check (inferInstance : Fibration (pullback.snd f g))

end

/-! ### Lemma_14_31_3 (from Chap14) -/
open CategoryTheory HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

section

variable {X Y Z : SSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/- Domain-style sampling for Lemma 14.31.3:
- primary domain: simplicial-set fibrations in the Quillen model structure;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  the generic composition instance
  `[CategoryWithFibrations C] [(fibrations C).IsStableUnderComposition]
    [Fibration f] [Fibration g] : Fibration (f ≫ g)`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `MorphismProperty.rlp_isMultiplicative`;
- best owner abstraction: the canonical predicate `Fibration`, with composition supplied by the
  ambient owner morphism property `fibrations SSet`;
- primitive data: the instance assumptions `[Fibration f]` and `[Fibration g]`;
- derived API: the source-facing conclusion `Fibration (f ≫ g)`.

Source/core/bridge triage:
- `source-facing`: the statement that a composite of two Kan fibrations is again a Kan fibration;
- `core/canonical`: the generic composition instance for `Fibration`;
- `bridge/view`: the horn-filling characterization `SSet.modelCategoryQuillen.fibration_iff`.

This item adds no new simplicial-set primitive data, so the correct refinement is reuse of the
existing `Fibration` composition instance directly. The needed owner-property stability is already
supplied by mathlib's model-category infrastructure, so no parallel local copy is part of the
public API. -/

variable [Fibration f] [Fibration g]

/- Lemma 14.31.3: the composition of two Kan fibrations is again a Kan fibration.
Canonically, this is the generic composition instance for `Fibration`. -/
#synth Fibration (f ≫ g)

end

/-! ### Lemma_14_31_4 (from Chap14) -/
open CategoryTheory Limits Opposite HomotopicalAlgebra SSet.modelCategoryQuillen
open scoped SSet.modelCategoryQuillen

universe u

section

variable {X : ℕ → SSet.{u}}
variable (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
variable [∀ n : ℕ, Fibration (f n)]

/-
Domain-style sampling for Lemma 14.31.4:
- primary domain: simplicial-set fibrations in the Quillen model structure, together with
  categorical inverse limits of countable towers;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `CategoryTheory.MorphismProperty.rlp_limitProjection_ofSequence`,
  `CategoryTheory.Functor.ofOpSequence`,
  `CategoryTheory.Limits.limit.π`;
- best owner abstraction: the canonical predicate `Fibration`, with the inverse-limit projection
  expressed directly as a theorem on the canonical morphism `limit.π (Functor.ofOpSequence f)
  (op 0)`, using the owner theorem `J.rlp_limitProjection_ofSequence` together with
  the canonical owner identification `SSet.modelCategoryQuillen.fibration_iff`;
- primitive-vs-derived split:
  primitive data: the tower maps `f n : X (n + 1) ⟶ X n` and the owner instances
    `[∀ n, Fibration (f n)]`;
  derived API: the source-facing recall that the canonical projection from the inverse limit of the
    tower to `X 0` is again a Kan fibration.

Source/core/bridge triage:
- `source-facing`: the textbook statement about inverse limits of Kan fibrations;
- `core/canonical`: the owner predicate `Fibration`;
- `bridge/view`: the owner equivalence `SSet.modelCategoryQuillen.fibration_iff`;
- owner theorem reused by the proof:
  `J.rlp_limitProjection_ofSequence`.

This item is `source-facing`, but it is not the owner of new simplicial-set data or a new bridge.
Unlike the pullback, composition, and product cases nearby, the exact inverse-limit statement is
not exposed upstream as an instance, so the correct refinement is a thin theorem stated directly in
the canonical owner predicate `Fibration`, not a fake `#synth` recall and not a second local
horn-lifting wrapper.
-/

/- Lemma 14.31.4: for a countable inverse sequence of Kan fibrations of simplicial sets, the
canonical projection from the inverse limit of the sequence to the initial term is again a Kan
fibration. The public statement stays on the owner predicate `Fibration` for the canonical
projection `limit.π (Functor.ofOpSequence f) (op 0)`. -/
theorem fibration_limitProjection_ofSequence :
    Fibration (limit.π (Functor.ofOpSequence f) (op 0)) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  exact J.rlp_limitProjection_ofSequence f fun m ↦
    (SSet.modelCategoryQuillen.fibration_iff (f m)).1 (inferInstance : Fibration (f m))

end

/-! ### Lemma_14_31_5 (from Chap14) -/
open CategoryTheory Limits HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped SSet.modelCategoryQuillen

universe u v

section

variable {ι : Type v} {X Y : ι → SSet.{u}} (f : ∀ i, X i ⟶ Y i)
variable [HasProduct X] [HasProduct Y]
variable [∀ i, Fibration (f i)]

/- Domain-style sampling for Lemma 14.31.5:
- primary domain: simplicial-set fibrations in the Quillen model structure, together with their
  stability under products;
- sampled owner declarations:
  `HomotopicalAlgebra.Fibration`,
  `SSet.modelCategoryQuillen.fibration_iff`,
  `CategoryTheory.MorphismProperty.limMap`,
  the abstract product instance for `Fibration (Limits.Pi.map f)` in
    `Mathlib.AlgebraicTopology.ModelCategory.Instances`;
- best owner abstraction: `Fibration (Limits.Pi.map f)`;
- primitive data: the family `f`, the product hypotheses `[HasProduct X] [HasProduct Y]`, and the
  componentwise fibrations as owner instances `[∀ i, Fibration (f i)]`;
- derived API: the source-facing theorem that the induced product map again has the owner
  predicate `Fibration`.

Source/core/bridge triage:
- `source-facing`: the textbook statement that a product of Kan fibrations of simplicial sets is a
  Kan fibration;
- `core/canonical`: the owner predicate `Fibration`;
- `bridge/view`: the horn-filling reformulation
  `SSet.modelCategoryQuillen.fibration_iff`.

This item is `source-facing`, but it adds no new source-defined data beyond the existing owner
predicate `Fibration`. There is an abstract upstream product instance, but it assumes the ambient
weak-factorization-system package for a model category, and that instance is not inferable here
from the scoped simplicial-set Quillen structure alone. By the semantic-priority rule, the main
lemma should stay at the weaker source-faithful simplicial-set assumptions and use only the thin
bridge from `Fibration` to `J.rlp`, `MorphismProperty.limMap`, and back.
-/

/-- Lemma 14.31.5: if each `f i : X i ⟶ Y i` is a Kan fibration of simplicial sets, then the
induced product map `Limits.Pi.map f : ∏ᶜ X ⟶ ∏ᶜ Y` is also a Kan fibration. This is exactly the
canonical owner-level product statement, expressed through `Fibration`. -/
theorem fibration_piMap : Fibration (Limits.Pi.map f) := by
  -- Rewrite fibrations as the horn-inclusion lifting property and apply product stability.
  rw [SSet.modelCategoryQuillen.fibration_iff]
  exact MorphismProperty.limMap _ fun ⟨i⟩ ↦
    (SSet.modelCategoryQuillen.fibration_iff (f i)).1 inferInstance

end

/-! ### Lemma_14_31_6 (from Chap14) -/
open CategoryTheory

/- Domain-style sampling for Lemma 14.31.6:
- primary domain: simplicial sets as fibrant objects in the Quillen model structure, viewed through
  the forgetful functor from simplicial groups;
- sampled owner declarations:
  `SSet.KanComplex`,
  `HomotopicalAlgebra.isFibrant_iff`,
  `SSet.KanComplex.hornFilling`,
  `SSet.modelCategoryQuillen.fibration_iff`;
- best owner abstraction: `SSet.KanComplex` as the canonical owner on the underlying simplicial
  set of a simplicial group;
- primitive-vs-derived split:
  primitive data: the simplicial group `X : SimplicialObject GrpCat`;
  derived API: the source-facing theorem `simplicialGroup_kanComplex X`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that the underlying simplicial set of a simplicial group is a
  Kan complex;
- `core/canonical`: the owner predicate `SSet.KanComplex`;
- `bridge/view`: the horn-filling and terminal-map characterizations of `KanComplex`.

This item is `source-facing`, but its exact owner-level interface is already available upstream as
the predicate `SSet.KanComplex`. There is no exact upstream theorem for simplicial groups, so the
correct refinement is to state the lemma directly with target `SSet.KanComplex`, rather than
pretending that a recall-style instance already exists. -/

instance instKanComplexUnderlyingSimplicialGroup (X : SimplicialObject GrpCat) :
    SSet.KanComplex (X ⋙ forget GrpCat) := by
  sorry

/- Lemma 14.31.6: the underlying simplicial set of a simplicial group is a Kan complex.
The canonical owner is `SSet.KanComplex`, so the public statement should land directly in that
predicate. -/
theorem simplicialGroup_kanComplex (X : SimplicialObject GrpCat) :
    SSet.KanComplex (X ⋙ forget GrpCat) :=
  instKanComplexUnderlyingSimplicialGroup X

/-! ### Lemma_14_31_7 (from Chap14) -/
open CategoryTheory Opposite Simplicial HomotopicalAlgebra

open scoped SSet.modelCategoryQuillen Simplicial

universe u

section

variable {X Y : SimplicialObject GrpCat.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Lemma 14.31.7:
- primary domain: simplicial groups as functor-category objects, together with the Quillen
  fibration predicate on the underlying simplicial-set map;
- sampled owner declarations:
  `NatTrans.epi_iff_epi_app'`,
  `GrpCat.epi_iff_surjective`,
  `HomotopicalAlgebra.Fibration`,
  the source-facing owner theorem `simplicialGroup_kanComplex X`;
- best owner abstraction: the canonical owner bridge from `[Epi f]` to
  `Fibration (Functor.whiskerRight f (forget GrpCat))`, with termwise surjectivity obtained as the
  source-facing bridge to `Epi f`;
- primitive-vs-derived split:
  primitive data: the morphism `f : X ⟶ Y`;
  derived API: the owner hypothesis `[Epi f]`, the induced `Fibration` instance on the underlying
  simplicial-set map, and the termwise-surjectivity bridge to that instance.

Source/core/bridge triage:
- `source-facing`: termwise-surjective morphisms of simplicial groups;
- `core/canonical`: the owner instance
  `[Epi f] : Fibration (Functor.whiskerRight f (forget GrpCat))`;
- `bridge/view`: `NatTrans.epi_iff_epi_app'` together with `GrpCat.epi_iff_surjective`.

The simplicial-abelian-group statements below are only a specialization layer for downstream use;
they are not a second owner abstraction. -/
-- Proof sketch: choose a degreewise preimage of any simplex in `Y`, divide it out to reduce the
-- lifting problem to the kernel simplicial group of `f`, and then apply the canonical
-- Kan-complex theorem from Lemma 14.31.6 to the underlying simplicial set of that simplicial
-- group.
instance [Epi f] :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := sorry

/-- Lemma 14.31.7: a termwise surjective morphism of simplicial groups induces a Kan fibration on
the underlying simplicial sets. -/
theorem simplicialGroup_fibration_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget GrpCat)) := by
  letI : Epi f := by
    rw [NatTrans.epi_iff_epi_app']
    intro n
    exact (GrpCat.epi_iff_surjective (f.app n)).2 (hsurj n)
  infer_instance

end

section

variable {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)

/-- Specialization of Lemma 14.31.7 to simplicial abelian groups. -/
theorem simplicialAbelianGroup_fibration_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n)) :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  let g :=
    Functor.whiskerRight
      (Functor.whiskerRight f AddCommGrpCat.toCommGrp)
      (forget₂ CommGrpCat GrpCat)
  have hsurj' :
      ∀ n : SimplexCategoryᵒᵖ,
        Function.Surjective (g.app n) := by
    simpa [g] using hsurj
  simpa [g] using simplicialGroup_fibration_of_termwise_surjective g hsurj'

instance [Epi f] :
    Fibration (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  have hf : ∀ n : SimplexCategoryᵒᵖ, Epi (f.app n) := by
    rw [← NatTrans.epi_iff_epi_app']
    infer_instance
  apply simplicialAbelianGroup_fibration_of_termwise_surjective f
  intro n
  exact (AddCommGrpCat.epi_iff_surjective (f.app n)).1 (hf n)

end

/-! ### Lemma_14_31_8 (from Chap14) -/
open CategoryTheory CategoryTheory.Limits Opposite Simplicial AlgebraicTopology
open AlgebraicTopology.DoldKan
open SSet.modelCategoryQuillen

universe u

section

variable {X Y : SimplicialObject AddCommGrpCat.{u}} (f : X ⟶ Y)

/- Domain-style sampling for Lemma 14.31.8:
- primary domain: simplicial abelian groups, the normalized Moore complex, and the simplicial-set
  owner predicate for trivial Kan fibrations.
- sampled same-kind declarations:
  `SSet.modelCategoryQuillen.I.rlp`,
  `simplicialAbelianGroup_fibration_of_termwise_surjective`,
  `QuasiIso`,
  `normalizedMooreComplex`.
- best owner abstractions:
  the source-facing conclusion should remain the canonical simplicial-set predicate `I.rlp` on the
  underlying map, while the chain-level hypothesis is already canonically expressed by
  `QuasiIso ((normalizedMooreComplex AddCommGrpCat).map f)`.
- primitive-vs-derived split:
  primitive data: the morphism `f`, termwise surjectivity, and the normalized-Moore-complex
  quasi-isomorphism hypothesis;
  derived API: the intermediate Kan-fibration statement from
  `simplicialAbelianGroup_fibration_of_termwise_surjective`, and the resulting trivial Kan
  fibration on the underlying simplicial sets.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a termwise-surjective quasi-isomorphism of simplicial
  abelian groups is a trivial Kan fibration on underlying simplicial sets;
- `core/canonical`: `I.rlp` and `QuasiIso`;
- `bridge/view`: Lemma 14.31.7 supplies the fibration half of the conclusion, while the proof
  reduces the remaining boundary-filling problem to the acyclic kernel simplicial abelian group.

There is no exact upstream theorem to recall directly here. The refinement is therefore to keep the
source-facing theorem, but land its conclusion and hypotheses directly in the established owner
predicates instead of introducing any parallel wrapper notion of “trivial Kan fibration”. -/

-- Proof sketch: use Lemma 14.31.7 to reduce the claim to the boundary-filling property for the
-- underlying simplicial-set map. For a boundary lifting problem, choose a degreewise lift using
-- termwise surjectivity and subtract it to reduce to the kernel simplicial abelian group of `f`.
-- The quasi-isomorphism hypothesis makes the normalized Moore complex of that kernel acyclic via
-- the long exact sequence in homology, and Lemma 14.31.6 gives the Kan fillers needed to solve the
-- reduced problem.
/-- Helper for Lemma 14.31.8: a quasi-isomorphism on normalized Moore complexes is also a
quasi-isomorphism on alternating face map complexes. -/
lemma alternatingFaceMapComplex_map_quasiIso_of_normalizedMooreComplex_quasiIso
    (hqis : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)) :
    QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := by
  let _ : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f) := hqis
  let eX :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj X)
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj X) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  let eY :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj Y)
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj Y) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  let _ : QuasiIso (inclusionOfMooreComplexMap X) := by
    simpa [eX] using (show QuasiIso eX.hom from inferInstance)
  let _ : QuasiIso (inclusionOfMooreComplexMap Y) := by
    simpa [eY] using (show QuasiIso eY.hom from inferInstance)
  -- Compare the normalized and alternating maps through the naturality square of the inclusion.
  have hnat :
      ((normalizedMooreComplex AddCommGrpCat).map f) ≫ inclusionOfMooreComplexMap Y =
        inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex AddCommGrpCat.{u}).map f := by
    simpa using (inclusionOfMooreComplex AddCommGrpCat).naturality f
  have hcomp :
      QuasiIso
        (inclusionOfMooreComplexMap X ≫
          (alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := by
    have hcomp' :
        QuasiIso
          (((normalizedMooreComplex AddCommGrpCat).map f) ≫
            inclusionOfMooreComplexMap Y) := by
      infer_instance
    -- Rewrite the composite using naturality of `inclusionOfMooreComplexMap`.
    rw [← hnat]
    exact hcomp'
  let _ :
      QuasiIso
        (inclusionOfMooreComplexMap X ≫
          (alternatingFaceMapComplex AddCommGrpCat.{u}).map f) := hcomp
  exact
    quasiIso_of_comp_left
      (inclusionOfMooreComplexMap X)
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f)

/-- Helper for Lemma 14.31.8: termwise surjectivity makes every degree of the alternating face
map complex morphism epimorphic. -/
lemma alternatingFaceMapComplex_map_epi_of_termwise_surjective
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (n : ℕ) :
    Epi (((alternatingFaceMapComplex AddCommGrpCat.{u}).map f).f n) := by
  -- Each chain-group component is just the degree-`n` map of simplicial abelian groups.
  rw [alternatingFaceMapComplex_map_f]
  exact (AddCommGrpCat.epi_iff_surjective _).2 (hsurj (op ⦋n⦌))

/-- Helper for Lemma 14.31.8: the kernel of a termwise epimorphic quasi-isomorphism of
chain complexes indexed by `ℕ` is acyclic. -/
lemma chainComplex_kernel_acyclic_of_termwise_epi_quasiIso
    {K L : ChainComplex AddCommGrpCat.{u} ℕ} (α : K ⟶ L) [QuasiIso α]
    (hα : ∀ n : ℕ, Epi (α.f n)) :
    (kernel α).Acyclic := by
  -- The canonical short exact row `0 ⟶ kernel α ⟶ K ⟶ L` detects vanishing homology of the
  -- kernel from the quasi-isomorphism hypothesis on `α`.
  rw [HomologicalComplex.acyclic_iff]
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  let S := ShortComplex.kernelSequence α
  have hS : S.ShortExact := by
    refine ShortComplex.ShortExact.mk' ?_ inferInstance
      (HomologicalComplex.epi_of_epi_f α hα)
    exact ShortComplex.kernelSequence_exact α
  refine ((hS.homology_exact₁ (n + 1) n (by simp)).isZero_X₂ ?_ ?_)
  · rw [← (hS.homology_exact₃ (n + 1) n (by simp)).epi_f_iff]
    have : Epi (HomologicalComplex.homologyMap α (n + 1)) := by
      infer_instance
    simpa [S] using this
  · rw [← (hS.homology_exact₂ n).mono_g_iff]
    have : Mono (HomologicalComplex.homologyMap α n) := by
      infer_instance
    simpa [S] using this

/-- Helper for Lemma 14.31.8: the alternating face map complex of the simplicial kernel is
acyclic once the induced alternating-face map is a termwise epimorphic quasi-isomorphism. -/
lemma alternatingFaceMapComplex_kernel_acyclic
    (hAlt : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f))
    (hEpi : ∀ m : ℕ, Epi (((alternatingFaceMapComplex AddCommGrpCat.{u}).map f).f m)) :
    ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f)).Acyclic := by
  -- Exactness of `alternatingFaceMapComplex` identifies the simplicial kernel with the kernel of
  -- the induced chain map, so the generic kernel-acyclicity argument applies verbatim.
  let hpres : PreservesFiniteLimits (alternatingFaceMapComplex AddCommGrpCat.{u}) :=
    (exactFunctor_iff (alternatingFaceMapComplex AddCommGrpCat.{u})).1
      alternatingFaceMapComplex_exact |>.1
  letI : PreservesFiniteLimits (alternatingFaceMapComplex AddCommGrpCat.{u}) := hpres
  letI : PreservesLimitsOfShape WalkingParallelPair
      (alternatingFaceMapComplex AddCommGrpCat.{u}) :=
    by infer_instance
  letI : PreservesLimit (parallelPair f 0) (alternatingFaceMapComplex AddCommGrpCat.{u}) := by
    exact PreservesLimitsOfShape.preservesLimit
  let g :
      (alternatingFaceMapComplex AddCommGrpCat.{u}).obj X ⟶
        (alternatingFaceMapComplex AddCommGrpCat.{u}).obj Y :=
    (alternatingFaceMapComplex AddCommGrpCat.{u}).map f
  letI : QuasiIso g := hAlt
  have hKernel : (kernel g).Acyclic :=
    chainComplex_kernel_acyclic_of_termwise_epi_quasiIso g hEpi
  let e :
      (alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f) ≅ kernel g :=
    PreservesKernel.iso (alternatingFaceMapComplex AddCommGrpCat.{u}) f
  -- Transport acyclicity across the exact-functor comparison isomorphism.
  intro n
  exact HomologicalComplex.ExactAt.of_iso (hKernel n) e.symm

/-- Helper for Lemma 14.31.8: the normalized Moore complex of the simplicial kernel is acyclic
under the same quasi-isomorphism and termwise-surjectivity hypotheses. -/
lemma normalizedMooreComplex_kernel_acyclic
    (hAlt : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f))
    (hEpi : ∀ m : ℕ, Epi (((alternatingFaceMapComplex AddCommGrpCat.{u}).map f).f m)) :
    ((normalizedMooreComplex AddCommGrpCat.{u}).obj (kernel f)).Acyclic := by
  have hKernelAlt :
      ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f)).Acyclic :=
    alternatingFaceMapComplex_kernel_acyclic (f := f) hAlt hEpi
  let e :
      HomotopyEquiv
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj (kernel f))
        ((alternatingFaceMapComplex AddCommGrpCat.{u}).obj (kernel f)) :=
    homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
  -- The Dold-Kan comparison is a quasi-isomorphism, so exactness transfers degreewise.
  intro n
  exact (exactAt_iff_of_quasiIsoAt e.hom n).2 (hKernelAlt n)

/-- Helper for Lemma 14.31.8: each codimension-one face of `Δ[n + 1]` factors through its
boundary. -/
lemma stdSimplex_face_le_boundary (n : ℕ) (j : Fin (n + 2)) :
    SSet.stdSimplex.face {j}ᶜ ≤ SSet.boundary (n + 1) := by
  -- The boundary is the supremum of all codimension-one faces, so each individual face
  -- includes into it.
  rw [SSet.boundary_eq_iSup]
  exact le_iSup (fun i : Fin (n + 2) ↦ SSet.stdSimplex.face {i}ᶜ) j

/-- Helper for Lemma 14.31.8: the `j`-th codimension-one face of the boundary simplex
`∂Δ[n + 1]`. -/
def boundary_face (n : ℕ) (j : Fin (n + 2)) :
    Δ[n] ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  Subfunctor.lift (SSet.stdSimplex.δ j) (by
    simpa [SSet.stdSimplex.range_δ] using stdSimplex_face_le_boundary n j)

/-- Helper for Lemma 14.31.8: composing the boundary face inclusion with the boundary embedding
recovers the standard face map. -/
@[simp, reassoc]
lemma boundary_face_ι (n : ℕ) (j : Fin (n + 2)) :
    boundary_face n j ≫ (∂Δ[n + 1]).ι = SSet.stdSimplex.δ j := by
  -- The lifted face map is defined precisely by factoring `stdSimplex.δ j` through the
  -- boundary subcomplex.
  simp [boundary_face]

/-- Helper for Lemma 14.31.8: morphisms out of a boundary simplex are determined by their
restrictions to the codimension-one faces. -/
lemma boundary_hom_ext {n : ℕ} {S : SSet.{u}} (σ₁ σ₂ : (∂Δ[n + 1] : SSet.{u}) ⟶ S)
    (h :
      ∀ j : Fin (n + 2),
        boundary_face n j ≫ σ₁ = boundary_face n j ≫ σ₂) :
    σ₁ = σ₂ := by
  -- As in the horn case, it suffices to check equality on the face subcomplexes generating
  -- the boundary.
  rw [← Subfunctor.equalizer_eq_iff]
  refine le_antisymm (Subfunctor.equalizer_le σ₁ σ₂) ?_
  simpa [SSet.boundary_eq_iSup] using
    (show (⨆ j : Fin (n + 2), SSet.stdSimplex.face {j}ᶜ) ≤ Subfunctor.equalizer σ₁ σ₂ from by
      simp only [iSup_le_iff]
      intro j
      rw [← SSet.stdSimplex.ofSimplex_yonedaEquiv_δ]
      rw [SSet.Subcomplex.ofSimplex_le_iff]
      refine (Subfunctor.mem_equalizer_iff σ₁ σ₂ (SSet.yonedaEquiv (boundary_face n j))).2 ?_
      -- Convert equality of maps `Δ[n] ⟶ S` into equality of the corresponding `n`-simplices.
      simpa [SSet.yonedaEquiv_comp] using congrArg SSet.yonedaEquiv (h j))

/-- Helper for Lemma 14.31.8: the zero map into the underlying simplicial set of a simplicial
abelian group. -/
def zero_hom {S : SSet.{u}} (K : SimplicialObject AddCommGrpCat.{u}) :
    S ⟶ K ⋙ forget AddCommGrpCat where
  app n _ := 0
  naturality n m φ := by
    ext x
    show (0 : K.obj m) = (K.map φ) (0 : K.obj n)
    simp

/-- Helper for Lemma 14.31.8: pointwise subtraction of morphisms into the underlying simplicial
set of a simplicial abelian group. -/
def sub_hom {S : SSet.{u}} {K : SimplicialObject AddCommGrpCat.{u}}
    (σ τ : S ⟶ K ⋙ forget AddCommGrpCat) :
    S ⟶ K ⋙ forget AddCommGrpCat where
  app n x := σ.app n x - τ.app n x
  naturality n m φ := by
    ext x
    have hσ :=
      (FunctorToTypes.naturality S (K ⋙ forget AddCommGrpCat) σ φ x :
        σ.app m (S.map φ x) =
          (K ⋙ forget AddCommGrpCat).map φ (σ.app n x))
    have hτ :=
      (FunctorToTypes.naturality S (K ⋙ forget AddCommGrpCat) τ φ x :
        τ.app m (S.map φ x) =
          (K ⋙ forget AddCommGrpCat).map φ (τ.app n x))
    dsimp at hσ hτ ⊢
    rw [hσ, hτ]
    simpa using
      (map_sub (ConcreteCategory.hom (K.map φ)) (σ.app n x) (τ.app n x)).symm

/-- Helper for Lemma 14.31.8: a simplicial map into `X` whose image under `f` vanishes
pointwise factors through the underlying simplicial set of the simplicial kernel of `f`. -/
lemma kernel_underlying_lift_of_zero {S : SSet.{u}} (σ : S ⟶ X ⋙ forget AddCommGrpCat)
    (hσ : ∀ n : SimplexCategoryᵒᵖ, ∀ x : S.obj n, f.app n (σ.app n x) = 0) :
    ∃ σK : S ⟶ (kernel f) ⋙ forget AddCommGrpCat,
      σK ≫ Functor.whiskerRight (kernel.ι f) (forget AddCommGrpCat) = σ := by
  let liftApp :
      ∀ n : SimplexCategoryᵒᵖ, S.obj n → (kernel f).obj n := fun n x =>
    (PreservesKernel.iso ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat).obj n) f).inv
      ((AddCommGrpCat.kernelIsoKer (f.app n)).inv ⟨σ.app n x, by simpa using hσ n x⟩)
  have hcomp :
      ∀ n : SimplexCategoryᵒᵖ, ∀ x : S.obj n,
        ((kernel.ι f).app n) (liftApp n x) =
          σ.app n x := by
    intro n x
    have h₁ :=
      ConcreteCategory.congr_hom
        (PreservesKernel.iso_inv_ι ((evaluation SimplexCategoryᵒᵖ AddCommGrpCat).obj n) f)
        ((AddCommGrpCat.kernelIsoKer (f.app n)).inv ⟨σ.app n x, by simpa using hσ n x⟩)
    have h₂ :=
      ConcreteCategory.congr_hom (AddCommGrpCat.kernelIsoKer_inv_comp_ι (f.app n))
        ⟨σ.app n x, by simpa using hσ n x⟩
    exact h₁.trans h₂
  refine ⟨
    { app := liftApp
      naturality := ?_ }, ?_⟩
  · intro n m φ
    funext x
    -- Compare after composing with the kernel inclusion, which is monic in `AddCommGrpCat`.
    apply (AddCommGrpCat.mono_iff_injective ((kernel.ι f).app m)).1 inferInstance
    -- The pointwise kernel description reduces the claim to naturality of `σ`.
    change ((kernel.ι f).app m) (liftApp m (S.map φ x)) =
      ((kernel.ι f).app m) (((kernel f).map φ) (liftApp n x))
    rw [hcomp m (S.map φ x)]
    rw [FunctorToTypes.naturality S (X ⋙ forget AddCommGrpCat) σ φ x]
    rw [← hcomp n x]
    exact (FunctorToTypes.naturality ((kernel f) ⋙ forget AddCommGrpCat)
      (X ⋙ forget AddCommGrpCat)
      (Functor.whiskerRight (kernel.ι f) (forget AddCommGrpCat)) φ (liftApp n x)).symm
  · -- Each component was chosen precisely to map back to the original simplex of `X`.
    ext n x
    exact hcomp n x

/-- Helper for Lemma 14.31.8: a simplex with vanishing positive faces determines a normalized
Moore element in the same degree. -/
lemma normalized_moore_element_of_vanishing_positive_faces
    (K : SimplicialObject AddCommGrpCat.{u}) (m : ℕ) (w : K _⦋m + 1⦌)
    (hw : ∀ j : Fin (m + 1), ConcreteCategory.hom (K.δ j.succ) w = 0) :
    ∃ wN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1),
      (NormalizedMooreComplex.objX K (m + 1)).arrow wN = w := by
  let wHom : AddCommGrpCat.of (ULift.{u} ℤ) ⟶ K _⦋m + 1⦌ :=
    AddCommGrpCat.ofHom ((uliftZMultiplesHom (K _⦋m + 1⦌)) w)
  have hwFactors :
      (NormalizedMooreComplex.objX K (m + 1)).Factors wHom := by
    -- The universal intersection description of `objX` packages the vanishing of all positive
    -- faces into a single factorization statement.
    rw [NormalizedMooreComplex.objX_add_one, Subobject.finset_inf_factors]
    intro j _
    apply kernelSubobject_factors
    ext z
    simp [wHom, hw j]
  refine ⟨(NormalizedMooreComplex.objX K (m + 1)).factorThru wHom hwFactors ⟨1⟩, ?_⟩
  -- Evaluating the factored `ℤ`-multiple map at `1` recovers the original simplex `w`.
  rw [← ConcreteCategory.comp_apply, Subobject.factorThru_arrow]
  change ((uliftZMultiplesHom (K _⦋m + 1⦌)) w) ⟨1⟩ = w
  change (1 : ℤ) • w = w
  exact one_zsmul w

/-- Helper for Lemma 14.31.8: exactness in degree `m + 1` of a chain complex of abelian groups
produces a boundary preimage for any cycle in that degree. -/
lemma normalized_short_complex_boundary_preimage
    {N : ChainComplex AddCommGrpCat.{u} ℕ} (m : ℕ) (hExact : N.ExactAt (m + 1))
    (wN : N.X (m + 1)) (hwN : N.d (m + 1) m wN = 0) :
    ∃ cN : N.X (m + 2), N.d (m + 2) (m + 1) cN = wN := by
  let S : ShortComplex AddCommGrpCat.{u} := N.sc' (m + 2) (m + 1) m
  have hSExact : S.Exact := hExact
  rw [N.exactAt_iff' (i := m + 2) (k := m) (by simp) (by simp)] at hSExact
  -- Rewrite exactness of the short complex into the concrete lifting property in abelian groups.
  rw [ShortComplex.ab_exact_iff] at hSExact
  have hwS : S.g wN = 0 := by
    simpa [S] using hwN
  rcases hSExact wN hwS with ⟨cN, hcN⟩
  -- Unfolding `S` identifies the short-complex differential with the chain differential.
  refine ⟨cN, ?_⟩
  simpa [S] using hcN

/-- Helper for Lemma 14.31.8: reading a normalized Moore element back as a simplex computes its
zero face via the normalized differential and forces all positive faces to vanish. -/
lemma normalized_simplex_of_normalized_preimage
    (K : SimplicialObject AddCommGrpCat.{u}) (m : ℕ)
    (cN : ((normalizedMooreComplex AddCommGrpCat).obj K).X (m + 1)) :
    ConcreteCategory.hom (K.δ (0 : Fin (m + 2)))
        ((NormalizedMooreComplex.objX K (m + 1)).arrow cN) =
      (NormalizedMooreComplex.objX K m).arrow
        ((((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) cN) ∧
      ∀ j : Fin (m + 1),
        ConcreteCategory.hom (K.δ j.succ)
          ((NormalizedMooreComplex.objX K (m + 1)).arrow cN) = 0 := by
  constructor
  · -- The zero face is exactly the normalized Moore differential, viewed in the ambient simplex.
    have hcomp :
        (NormalizedMooreComplex.objX K (m + 1)).arrow ≫ K.δ (0 : Fin (m + 2)) =
          (((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) ≫
            (NormalizedMooreComplex.objX K m).arrow := by
      rw [normalizedMooreComplex_objD]
      rcases m with _ | m
      · simp [NormalizedMooreComplex.objD]
      · simp [NormalizedMooreComplex.objD, Subobject.factorThru_arrow_assoc]
    exact ConcreteCategory.congr_hom hcomp cN
  · intro j
    -- Membership in the normalized Moore subobject kills every positive face.
    have hcomp :
        (NormalizedMooreComplex.objX K (m + 1)).arrow ≫ K.δ j.succ = 0 := by
      rw [NormalizedMooreComplex.objX_add_one]
      rw [← Subobject.factorThru_arrow _ _ (finset_inf_arrow_factors Finset.univ _ j (by simp)),
        Category.assoc, kernelSubobject_arrow_comp_assoc, zero_comp, comp_zero]
    rw [← ConcreteCategory.comp_apply, hcomp]
    simp

/-- Helper for Lemma 14.31.8: exactness of the normalized Moore complex turns a normalized cycle
into an actual simplicial boundary with all positive faces still vanishing. -/
lemma normalized_boundary_lift_of_exact
    (K : SimplicialObject AddCommGrpCat.{u}) (m : ℕ)
    (hExact : ((normalizedMooreComplex AddCommGrpCat).obj K).ExactAt (m + 1))
    (w : K _⦋m + 1⦌) (hw0 : ConcreteCategory.hom (K.δ (0 : Fin (m + 2))) w = 0)
    (hw : ∀ j : Fin (m + 1), ConcreteCategory.hom (K.δ j.succ) w = 0) :
    ∃ c : K _⦋m + 2⦌,
      ConcreteCategory.hom (K.δ (0 : Fin (m + 3))) c = w ∧
        ∀ j : Fin (m + 2), ConcreteCategory.hom (K.δ j.succ) c = 0 := by
  rcases normalized_moore_element_of_vanishing_positive_faces K m w hw with ⟨wN, hwN⟩
  have hwN_faces :
      ConcreteCategory.hom (K.δ (0 : Fin (m + 2)))
          ((NormalizedMooreComplex.objX K (m + 1)).arrow wN) =
        (NormalizedMooreComplex.objX K m).arrow
          ((((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) wN) :=
    (normalized_simplex_of_normalized_preimage K m wN).1
  have hwN_cycle :
      (((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) wN = 0 := by
    -- Apply the mono inclusion of the normalized Moore subobject to compare with the given
    -- vanishing zero face of `w`.
    apply (AddCommGrpCat.mono_iff_injective ((NormalizedMooreComplex.objX K m).arrow)).1
    infer_instance
    have hzero_face :
        (ConcreteCategory.hom (NormalizedMooreComplex.objX K m).arrow)
            ((((normalizedMooreComplex AddCommGrpCat).obj K).d (m + 1) m) wN) = 0 := by
      rw [← hwN_faces, hwN, hw0]
    simpa using hzero_face
  rcases normalized_short_complex_boundary_preimage m hExact wN hwN_cycle with ⟨cN, hcN⟩
  let c : K _⦋m + 2⦌ := (NormalizedMooreComplex.objX K (m + 2)).arrow cN
  have hc_faces := normalized_simplex_of_normalized_preimage K (m + 1) cN
  refine ⟨c, ?_, ?_⟩
  · -- The zero face is the original cycle `w`, because `cN` maps to `wN`.
    change
      ConcreteCategory.hom (K.δ (0 : Fin (m + 3)))
          ((NormalizedMooreComplex.objX K (m + 2)).arrow cN) = w
    rw [hc_faces.1, hcN, hwN]
  · intro j
    -- Positive faces still vanish because `c` lies in the normalized Moore subobject.
    exact hc_faces.2 j

/-- Helper for Lemma 14.31.8: the first horn is contained in the boundary of the standard
simplex. -/
lemma first_horn_le_boundary (n : ℕ) :
    SSet.horn (n + 1) (0 : Fin (n + 2)) ≤ SSet.boundary (n + 1) := by
  -- Both subcomplexes are unions of codimension-one faces, and the first horn omits only the
  -- face indexed by `0`.
  rw [SSet.horn_eq_iSup, SSet.boundary_eq_iSup]
  refine iSup_le ?_
  intro j
  exact le_iSup (fun i : Fin (n + 2) ↦ SSet.stdSimplex.face {i}ᶜ) j.1

/-- Helper for Lemma 14.31.8: the canonical inclusion of the first horn into the boundary. -/
def first_horn_to_boundary (n : ℕ) :
    (Λ[n + 1, 0] : SSet.{u}) ⟶ (∂Δ[n + 1] : SSet.{u}) :=
  SSet.Subcomplex.homOfLE (first_horn_le_boundary n)

/-- Helper for Lemma 14.31.8: composing the first-horn inclusion with the boundary embedding
recovers the horn embedding in the ambient simplex. -/
@[simp, reassoc]
lemma first_horn_to_boundary_ι (n : ℕ) :
    first_horn_to_boundary n ≫ (∂Δ[n + 1]).ι = Λ[n + 1, 0].ι := by
  -- This is the defining property of `Subcomplex.homOfLE`.
  simp [first_horn_to_boundary]

/-- Helper for Lemma 14.31.8: each nonzero horn face lands in the corresponding boundary face. -/
@[simp, reassoc]
lemma horn_face_first_horn_to_boundary (n : ℕ) (j : Fin (n + 2)) (hj : j ≠ 0) :
    SSet.horn.ι (0 : Fin (n + 2)) j hj ≫ first_horn_to_boundary n = boundary_face n j := by
  -- Both maps factor the same standard face `Δ[n] ⟶ Δ[n + 1]` through the boundary.
  apply (cancel_mono (∂Δ[n + 1]).ι).1
  simp [boundary_face]

/-- Helper for Lemma 14.31.8: the underlying simplicial set of a simplicial abelian group is a
Kan complex. -/
lemma simplicialAbelianGroup_kanComplex (K : SimplicialObject AddCommGrpCat.{u}) :
    SSet.KanComplex (K ⋙ forget AddCommGrpCat) := by
  -- Forgetting from abelian groups to groups preserves the underlying simplicial set, so we may
  -- apply the simplicial-group Kan-complex theorem.
  let G : SimplicialObject GrpCat.{u} :=
    K ⋙ AddCommGrpCat.toCommGrp ⋙ forget₂ CommGrpCat GrpCat
  simpa [G] using simplicialGroup_kanComplex G

/-- Lemma 14.31.8: if a morphism of simplicial abelian groups is termwise surjective and induces a
quasi-isomorphism on the associated normalized Moore complexes, then the underlying map of
simplicial sets is a trivial Kan fibration, canonically expressed by `I.rlp`. -/
theorem simplicialAbelianGroup_trivialKanFibration_of_termwise_surjective_of_normalizedMooreComplex_quasiIso
    (hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (f.app n))
    (hqis : QuasiIso ((normalizedMooreComplex AddCommGrpCat.{u}).map f)) :
    I.rlp (Functor.whiskerRight f (forget AddCommGrpCat)) := by
  -- Reconstruct the boundary lifting property from degree-zero surjectivity and positive fillers.
  apply boundaryInclusions_rlp_of_zero_surjective_and_boundary_lifting
  · simpa using hsurj (op ⦋0⦌)
  · intro n
    have hAlt :
        QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map f) :=
      alternatingFaceMapComplex_map_quasiIso_of_normalizedMooreComplex_quasiIso
        (f := f) hqis
    have hEpi :
        ∀ m : ℕ, Epi (((alternatingFaceMapComplex AddCommGrpCat.{u}).map f).f m) :=
      alternatingFaceMapComplex_map_epi_of_termwise_surjective (f := f) hsurj
    let _ :=
      simplicialAbelianGroup_fibration_of_termwise_surjective (f := f) hsurj
    have hKernelNormalized :
        ((normalizedMooreComplex AddCommGrpCat.{u}).obj (kernel f)).Acyclic :=
      normalizedMooreComplex_kernel_acyclic (f := f) hAlt hEpi
    -- Route correction: the chain-level acyclicity reduction is already in place. The remaining
    -- work is now concentrated in two owner-level transports:
    -- 1. build the adjusted boundary map into the simplicial kernel using `sub_hom`,
    --    then restrict it along `first_horn_to_boundary` and apply Kan filling;
    -- 2. convert the residual `d₀`-cycle in the kernel to a normalized Moore boundary using
    --    the acyclicity witness `hKernelNormalized`.
    -- TODO: implement the explicit kernel-valued restriction of the adjusted boundary map and the
    -- normalized-cycle correction term. The horn-side gluing blocker has been replaced by the
    -- canonical inclusion `first_horn_to_boundary`, so the remaining open work is the
    -- kernel-subobject transport plus the exactness-based lift in the normalized Moore complex.
    sorry

end

/-! ### Lemma_14_31_9 (from Chap14) -/
open CategoryTheory HomologicalComplex
open AlgebraicTopology

noncomputable section

namespace CategoryTheory.SimplicialObject

variable {X Y : SimplicialObject AddCommGrpCat} {f : X ⟶ Y}

/-
Domain-style sampling for Lemma 14.31.9:
- primary domain: simplicial homotopy equivalences of underlying simplicial sets and the induced
  quasi-isomorphism statement for normalized Moore complexes of simplicial abelian groups;
- sampled same-kind declarations:
  `CategoryTheory.SimplicialObject.HomotopyEquiv`,
  `CategoryTheory.SimplicialObject.IsHomotopyEquivalence`,
  `CategoryTheory.SimplicialObject.normalizedMooreComplex_map_isHomotopyEquivalence`,
  `CategoryTheory.SimplicialObject.Homotopic.whiskerRight`,
  `HomologicalComplex.homotopyEquivalences`,
  `homotopyEquivalences_le_quasiIso`,
  `HomologicalComplex.mem_quasiIso_iff`;
- best owner abstraction: the source-facing hypothesis is the simplicial homotopy-equivalence
  predicate on the underlying simplicial-set map `Functor.whiskerRight f (forget AddCommGrpCat)`,
  while the target-side canonical owner is the morphism property
  `HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)` and its
  `QuasiIso` consequence;
- primitive-vs-derived split:
  primitive data are only the morphism `f` and the homotopy-equivalence hypothesis on the
  underlying simplicial-set map;
  derived API is the induced homotopy-equivalence statement for the free-abelian-group simplicial
  objects after whiskering by `AddCommGrpCat.free`, and then the canonical bridge from homotopy
  equivalences of chain complexes to quasi-isomorphisms.

Source/core/bridge triage:
- `source-facing`: the Stacks hypothesis that the underlying simplicial-set map of `f` is a
  simplicial homotopy equivalence;
- `core/canonical`: `IsHomotopyEquivalence` and `QuasiIso`;
- `bridge/view`: the free-abelian-group square from the Stacks proof, where Lemma 14.28.4 turns
  the underlying simplicial-set homotopy equivalence into a simplicial homotopy equivalence after
  applying `AddCommGrpCat.free`, and Lemma 14.27.2 then yields the quasi-isomorphism input on the
  free simplicial abelian groups. The direct additive homotopy-equivalence hypothesis is only a
  stronger companion hypothesis, and the chain-level implication
  `homotopyEquivalences_le_quasiIso` is the canonical owner-side bridge rather than a separate
  local theorem.
-/

-- Proof sketch: let `ℤ[X]` and `ℤ[Y]` be the simplicial abelian groups obtained by applying
-- `AddCommGrpCat.free` degreewise to the underlying simplicial sets of `X` and `Y`. By Lemma
-- 14.28.4, the induced map `ℤ[X] ⟶ ℤ[Y]` is a simplicial homotopy equivalence, so Lemma 14.27.2
-- makes its normalized Moore complex map a homotopy equivalence and hence a quasi-isomorphism.
-- The Stacks proof then compares the resulting homology isomorphism on `ℤ[X]` and `ℤ[Y]` with the
-- canonical augmentation maps `ℤ[X] ⟶ X` and `ℤ[Y] ⟶ Y` to deduce that `N(f)` is a
-- quasi-isomorphism.
/-- Lemma 14.31.9: if the underlying simplicial-set map of a morphism of simplicial abelian groups
is a simplicial homotopy equivalence, then the induced map on normalized Moore complexes is a
quasi-isomorphism. -/
theorem normalizedMooreComplex_map_quasiIso_of_homotopyEquivalence
    (hf : IsHomotopyEquivalence (Functor.whiskerRight f (forget AddCommGrpCat))) :
    QuasiIso ((normalizedMooreComplex AddCommGrpCat).map f) := by
  rcases hf with ⟨e, he⟩
  let eFree :
      CategoryTheory.SimplicialObject.HomotopyEquiv
        ((X ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free)
        ((Y ⋙ forget AddCommGrpCat) ⋙ AddCommGrpCat.free) :=
    { hom := Functor.whiskerRight e.hom AddCommGrpCat.free
      inv := Functor.whiskerRight e.inv AddCommGrpCat.free
      homotopyHomInvId := by
        simpa using Homotopic.whiskerRight e.homotopyHomInvId AddCommGrpCat.free
      homotopyInvHomId := by
        simpa using Homotopic.whiskerRight e.homotopyInvHomId AddCommGrpCat.free }
  have hfree :
      QuasiIso
        ((normalizedMooreComplex AddCommGrpCat).map
          (Functor.whiskerRight e.hom AddCommGrpCat.free)) := by
    rcases eFree.normalizedMooreComplex_map_isHomotopyEquivalence with ⟨h, hh⟩
    simpa [hh, eFree] using (show QuasiIso h.hom from inferInstance)
  -- Compare the quasi-isomorphism on the free simplicial abelian groups with the canonical
  -- counit maps `ℤ[X] ⟶ X` and `ℤ[Y] ⟶ Y`.
  clear he hfree eFree
  sorry

end CategoryTheory.SimplicialObject
