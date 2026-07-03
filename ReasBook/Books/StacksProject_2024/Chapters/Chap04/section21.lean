import Mathlib
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Presentable.Directed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_4_21_1 (from Chap04) -/
universe u

/- Domain-style sampling for Definition 4.21.1:
- primary domain: order-theoretic indexing objects used later as filtered preorder categories;
- relevant owner declarations inspected:
  `Preorder`,
  `PartialOrder`,
  `IsDirectedOrder`,
  `CategoryTheory.isFiltered_of_directed_le_nonempty`;
- best owner abstraction:
  - `source-facing`: a directed set is a preordered type equipped with `Nonempty I` and
    `IsDirectedOrder I`;
  - `core/canonical`: the owner typeclasses `Preorder`, `PartialOrder`, and `IsDirectedOrder`;
  - `bridge/view`: a nonempty directed preorder is canonically a filtered category via
    `CategoryTheory.isFiltered_of_directed_le_nonempty`;
- primitive data: the preorder relation, its reflexive/transitive structure, optional antisymmetry,
  and the directed-upper-bound condition;
- derived API: upper-bound witnesses from `exists_ge_ge` and the induced filtered-category
  structure on the associated thin category. -/

/- Source/core/bridge triage for Definition 4.21.1:
- `source-facing`: preordered sets, directed sets, partially ordered sets, and directed partially
  ordered sets.
- `core/canonical`: `Preorder`, `PartialOrder`, and `IsDirectedOrder`.
- `bridge/view`: `CategoryTheory.isFiltered_of_directed_le_nonempty` when the preorder is viewed
  as a category. -/

/- Definition 4.21.1 (1) and (2): a preorder on `I`, hence a preordered set, is the canonical
typeclass `Preorder I`. -/
recall Preorder

variable (I : Type u)

/- Definition 4.21.1 (3): on a preordered type `I`, directedness is the canonical owner
typeclass `IsDirectedOrder I`; together with `Nonempty I`, this is exactly the source notion of a
directed set. -/
section

variable [Preorder I]

#check Nonempty I
recall IsDirectedOrder

end

/- Definition 4.21.1 (4) and (5): a partial order on `I`, hence a partially ordered set, is the
canonical typeclass `PartialOrder I`. -/
recall PartialOrder

/- Definition 4.21.1 (6): since `PartialOrder I` extends `Preorder I`, a directed partially
ordered set has the same additional source data already recalled above, namely `Nonempty I` and
`IsDirectedOrder I`; no new owner declaration is needed here. -/

/-! ### Definition_4_21_2 (from Chap04) -/
universe u v w

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category.{w} C]

/- Domain-style sampling for Definition 4.21.2:
- primary domain: preorder-indexed diagrams in category theory;
- inspected owner declarations:
  - `Preorder` in `Definition_4_21_1`,
  - the functor category expression `I ⥤ C`,
  - the order-dual indexing expression `Iᵒᵈ ⥤ C`,
  - the downstream inverse-limit owner API
    `nonempty_sections_of_finite_inverse_system : (Jᵒᵖ ⥤ Type v) → _` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`;
- best owner abstraction:
  - `source-facing`: direct systems as `I ⥤ C`, inverse systems as `Iᵒᵈ ⥤ C`,
  - `core/canonical`: the same functor type expressions on the thin category of a preorder and on
    its order dual,
  - `bridge/view`: the opposite-category presentation `Iᵒᵖ ⥤ C` used by some downstream limit
    APIs;
- primitive data: stage objects together with transition morphisms for comparable indices;
- derived API: identity and composition compatibilities from the functor laws.

Source/core/bridge triage for Definition 4.21.2:
- `source-facing`: systems and inverse systems on a preordered set.
- `core/canonical`: functors out of the preorder category and its order dual.
- `bridge/view`: the equivalent opposite-category presentation for inverse systems. -/

/- Definition 4.21.2 (1): a system over a preordered set `I` in a category `C` is exactly a
functor `I ⥤ C`, where `I` is viewed as the thin category attached to the preorder. The primitive
data are the stage objects `F.obj i` and transition morphisms `F.map (homOfLE hij)`, while the
compatibilities are derived from the functor laws. -/
#check (I ⥤ C)

/- Definition 4.21.2 (2): an inverse system over a preordered set `I` in a category `C` is
exactly a functor `Iᵒᵈ ⥤ C`. This keeps the source indices on the original preorder while
reversing the transition direction without extra `op`/`unop` bookkeeping. The equivalent
contravariant presentation `Iᵒᵖ ⥤ C` is a bridge view for opposite-category limit APIs, not a
second owner. -/
#check (Iᵒᵈ ⥤ C)

end CategoryTheory

/-! ### Remark_4_21_3 (from Chap04) -/
open CategoryTheory
open CategoryTheory.Limits

universe u v w

variable {I : Type u} [Preorder I]

/- Domain-style sampling for Remark 4.21.3:
- primary domain: preorder categories, antisymmetrization, and the induced equivalences of direct
  and inverse system categories.
- inspected owner declarations:
  `toAntisymmetrization_le_toAntisymmetrization_iff`,
  `ofAntisymmetrization`,
  `Functor.IsEquivalence`,
  `Functor.asEquivalence`,
  `CategoryTheory.Equivalence.congrLeft`.
- owner abstraction: the quotient functor
  `toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)` endowed with
  `Functor.IsEquivalence`, then the induced functor-category equivalences from
  `Functor.asEquivalence.congrLeft`, and finally `Functor.Final` / `Functor.Initial` for colimit/limit
  comparison.
- primitive data: the quotient map `toAntisymmetrization`, the order comparison theorem
  `toAntisymmetrization_le_toAntisymmetrization_iff`, and the chosen section
  `ofAntisymmetrization`.
- derived API: the category equivalences for systems and inverse systems, plus the resulting
  colimit/limit comparison theorems.

Source/core/bridge triage:
- `source-facing`: the quotient map `π`, its order characterization, the chosen section, and the
  induced equivalences between direct and inverse system categories.
- `core/canonical`: `Functor.IsEquivalence`, `Equivalence.congrLeft`,
  `Functor.Final.hasColimit_comp_iff`, `Functor.Final.colimitIso`,
  `Functor.Initial.hasLimit_comp_iff`, and `Functor.Initial.limitIso`.
- `bridge/view`: `toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)`.
-/

section

variable (i j : I)

/- The quotient order on the antisymmetrization is exactly the canonical owner
theorem `toAntisymmetrization_le_toAntisymmetrization_iff`. -/
#check (by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  exact (toAntisymmetrization_le_toAntisymmetrization_iff :
    toAntisymmetrization (· ≤ ·) i ≤ toAntisymmetrization (· ≤ ·) j ↔ i ≤ j))

end

/- The chosen representative map from the antisymmetrization back to the preorder
is exactly the canonical section `ofAntisymmetrization`. -/
#check (by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  exact (ofAntisymmetrization (· ≤ ·) : Antisymmetrization I (· ≤ ·) → I))

/- The quotient map followed by the chosen representative is canonically the
identity on the antisymmetrization. -/
recall toAntisymmetrization_ofAntisymmetrization

private theorem toAntisymmetrization_obj_hom (i : I) :
    i ≤ (OrderEmbedding.ofAntisymmetrization I) (toAntisymmetrization (· ≤ ·) i) := by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  change i ≤ ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i)
  rw [← toAntisymmetrization_le_toAntisymmetrization_iff,
    toAntisymmetrization_ofAntisymmetrization (· ≤ ·)]

private theorem toAntisymmetrization_obj_inv (i : I) :
    (OrderEmbedding.ofAntisymmetrization I) (toAntisymmetrization (· ≤ ·) i) ≤ i := by
  let _ : IsPreorder I (· ≤ ·) := inferInstance
  change ofAntisymmetrization (· ≤ ·) (toAntisymmetrization (· ≤ ·) i) ≤ i
  rw [← toAntisymmetrization_le_toAntisymmetrization_iff,
    toAntisymmetrization_ofAntisymmetrization (· ≤ ·)]

private noncomputable def toAntisymmetrizationFunctorUnitIso :
    𝟭 I ≅
      (toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)) ⋙
        (OrderEmbedding.ofAntisymmetrization I).toOrderHom.toFunctor := by
  refine NatIso.ofComponents (fun i ↦ ?_) fun {_ _} _ ↦ Subsingleton.elim _ _
  refine ⟨(toAntisymmetrization_obj_hom i).hom, (toAntisymmetrization_obj_inv i).hom, ?_, ?_⟩ <;>
    exact Subsingleton.elim _ _

/-- Remark 4.21.3: the canonical quotient functor from a preorder to its antisymmetrization is an
equivalence of categories. -/
noncomputable instance antisymmetrizationFunctor_isEquivalence :
    Functor.IsEquivalence (toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)) :=
  Functor.IsEquivalence.mk'
    (OrderEmbedding.ofAntisymmetrization I).toOrderHom.toFunctor
    toAntisymmetrizationFunctorUnitIso
    (NatIso.ofComponents
      (fun q ↦ eqToIso (toAntisymmetrization_ofAntisymmetrization (· ≤ ·) q))
      fun {_ _} _ ↦ Subsingleton.elim _ _)

/-- Directedness descends from a preorder to its antisymmetrization. -/
instance [IsDirectedOrder I] :
    IsDirectedOrder (Antisymmetrization I (· ≤ ·)) := by
  refine ⟨fun a b ↦ ?_⟩
  refine Quotient.inductionOn₂' a b ?_
  intro i j
  rcases (toAntisymmetrization_mono.directed_le i j) with ⟨k, hik, hjk⟩
  exact ⟨toAntisymmetrization (· ≤ ·) k, hik, hjk⟩

section

variable {C : Type v} [Category.{w} C]

/- Direct systems: precomposition along the quotient equivalence yields the
canonical equivalence between systems indexed by `I` and systems indexed by its
antisymmetrization. -/
#check ((toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)).asEquivalence.congrLeft :
  (I ⥤ C) ≌ (Antisymmetrization I (· ≤ ·) ⥤ C))

/- Direct systems: the colimit-existence comparison is exactly the specialized
owner theorem `Functor.Final.hasColimit_comp_iff`; the needed `Functor.Final` instance is derived
canonically from the equivalence instance above. -/
variable (F : Antisymmetrization I (· ≤ ·) ⥤ C)

#check (Functor.Final.hasColimit_comp_iff toAntisymmetrization_mono.functor :
  HasColimit (toAntisymmetrization_mono.functor ⋙ F) ↔ HasColimit F)

/- Direct systems: the resulting colimit comparison isomorphism is exactly the
specialized owner theorem `Functor.Final.colimitIso`. -/
variable [HasColimit F]

#check (Functor.Final.colimitIso toAntisymmetrization_mono.functor F :
  colimit (toAntisymmetrization_mono.functor ⋙ F) ≅ colimit F)

end

section

variable {C : Type v} [Category.{w} C]

/- Inverse systems: precomposition along the quotient equivalence for the order dual
gives the canonical equivalence between inverse systems indexed by `I` and by its
antisymmetrization; `OrderIso.dualAntisymmetrization` is the canonical bridge from the
antisymmetrization of the order dual to the order dual of the antisymmetrization. -/
#check (((toAntisymmetrization_mono.functor :
    Iᵒᵈ ⥤ Antisymmetrization Iᵒᵈ (· ≤ ·)).asEquivalence.congrLeft).trans
  (OrderIso.dualAntisymmetrization I).equivalence.congrLeft.symm :
    (Iᵒᵈ ⥤ C) ≌ ((Antisymmetrization I (· ≤ ·))ᵒᵈ ⥤ C))

/- Inverse systems: the limit-existence comparison is exactly the specialized owner
theorem `Functor.Initial.hasLimit_comp_iff`; the needed `Functor.Initial` instance is derived
canonically from the finality of `toAntisymmetrization_mono.functor`. -/
variable (F : (Antisymmetrization I (· ≤ ·))ᵒᵖ ⥤ C)

#check (Functor.Initial.hasLimit_comp_iff toAntisymmetrization_mono.functor.op :
  HasLimit (toAntisymmetrization_mono.functor.op ⋙ F) ↔ HasLimit F)

/- Inverse systems: the resulting limit comparison isomorphism is exactly the
specialized owner theorem `Functor.Initial.limitIso`. -/
variable [HasLimit F]

#check (Functor.Initial.limitIso toAntisymmetrization_mono.functor.op F :
  limit (toAntisymmetrization_mono.functor.op ⋙ F) ≅ limit F)

end

/-! ### Definition_4_21_4 (from Chap04) -/
universe u v w

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category.{w} C]

/- Domain-style sampling for Definition 4.21.4:
- primary domain: directed diagrams and inverse diagrams in category theory, indexed by directed
  preorders;
- inspected owner declarations:
  - `IsDirectedOrder` and `CategoryTheory.isFiltered_of_directed_le_nonempty`,
  - the system-owner expressions `I ⥤ C` and `Iᵒᵈ ⥤ C` from `Definition_4_21_2`,
  - `nonempty_sections_of_finite_inverse_system` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`;
- best owner abstraction:
  - `source-facing`: directed systems and directed inverse systems on a directed set,
  - `core/canonical`: functors from the preorder category `I` and its order dual `Iᵒᵈ`,
  - `bridge/view`: the filtered/cofiltered structure induced on the preorder category by
    `[Nonempty I]` and `[IsDirectedOrder I]`;
- primitive data: exactly the stage objects and transition morphisms already carried by a functor
  `I ⥤ C` or `Iᵒᵈ ⥤ C`;
- derived API: the filtered/cofiltered comparison lemmas and limit/colimit theorems obtained from
  the directedness hypotheses on the index type.

Source/core/bridge triage for Definition 4.21.4:
- `source-facing`: systems and inverse systems indexed by a directed set.
- `core/canonical`: the functor type expressions `I ⥤ C` and `Iᵒᵈ ⥤ C`.
- `bridge/view`: the filtered/cofiltered structure induced by `[Nonempty I]` and
  `[IsDirectedOrder I]`. -/

/- Definition 4.21.4 (1): for a directed set `I`, meaning a preorder equipped with `[Nonempty I]`
and `[IsDirectedOrder I]` as in Definition 4.21.1, a directed system in `C` is still exactly the
canonical owner object `I ⥤ C`; directedness only specializes the index shape from Definition
4.21.2 and adds no new primitive data, so the checked owner expression itself lives under the
minimal preorder assumptions. -/
#check (I ⥤ C)

/- Definition 4.21.4 (2): likewise, for a directed set `I`, a directed inverse system in `C` is
exactly the canonical owner object `Iᵒᵈ ⥤ C`; directedness only specializes the inverse-system
owner of Definition 4.21.2, so the checked canonical type expression again needs only the
underlying preorder structure. -/
#check (Iᵒᵈ ⥤ C)

section

variable [Nonempty I] [IsDirectedOrder I]

/- Companion bridge: once the preorder index is nonempty and directed, its thin category is
canonically filtered via the owner instance
`CategoryTheory.isFiltered_of_directed_le_nonempty`. -/
recall CategoryTheory.isFiltered_of_directed_le_nonempty

/- Companion bridge: dually, the thin category on the order dual of a nonempty directed preorder is
canonically cofiltered. -/
#check (inferInstance : IsCofiltered Iᵒᵈ)

end

end CategoryTheory

/-! ### Lemma_4_21_5 (from Chap04) -/
universe w v u

namespace CategoryTheory

variable {𝓘 : Type u} [Category.{v} 𝓘]

/- Domain-style sampling for Lemma 4.21.5:
- primary domain: filtered/cofiltered diagram comparison via final and initial functors, together
  with directed-poset presentations of filtered categories;
- sampled owner API:
  `FinallySmall.exists_of_isFiltered`,
  `IsFiltered.exists_directed`,
  `IsDirectedOrder`,
  `Functor.Final.hasColimit_of_comp`,
  `Functor.Final.colimit_pre_isIso`,
  `Functor.Initial.hasLimit_of_comp`,
  `Functor.Initial.limit_pre_isIso`;
- owner abstraction: the canonical small filtered approximation theorem
  `FinallySmall.exists_of_isFiltered` for a filtered finally small category, together with
  transport of colimits and limits along final and initial functors;
- primitive data: a filtered category together with the finally-small owner structure needed to
  produce a small filtered category mapping finally into it;
- derived API: the directed-set presentation obtained from the small filtered model, expressed
  using the canonical owner class `IsDirectedOrder`, and the colimit/limit transfer and
  comparison isomorphisms induced by the resulting final functor. -/

/- Source/core/bridge triage for Lemma 4.21.5:
- `source-facing`: `exists_final_from_directed`, giving a directed-set presentation for a
  filtered category without collapsing the statement to the small-category theorem;
- `core/canonical`: `FinallySmall.exists_of_isFiltered`, `IsFiltered.exists_directed`,
  `Functor.Final.hasColimit_of_comp`,
  `Functor.Final.colimit_pre_isIso`, `Functor.Initial.hasLimit_of_comp`, and
  `Functor.Initial.limit_pre_isIso`;
- `bridge/view`: compose the final functor from a directed poset to the small filtered category
  produced by `FinallySmall.exists_of_isFiltered` with the final functor from that category to the
  original category; the limit half is the opposite-side initial-functor view of the same
  comparison. -/

/-- Helper for Lemma 4.21.5: a final functor out of a small filtered category transports the
directed-poset presentation produced by `IsFiltered.exists_directed` to the target category. -/
lemma exists_final_from_directed_of_final {J : Type w} [SmallCategory J] [IsFiltered J]
    (y : J ⥤ 𝓘) [y.Final] :
    ∃ (I : Type w) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (x : I ⥤ 𝓘), x.Final := by
  -- First replace the small filtered source category by its canonical directed-poset model.
  obtain ⟨I, hIord, hIdir, hInonempty, x, hx⟩ := IsFiltered.exists_directed J
  let _ : PartialOrder I := hIord
  let _ : Nonempty I := hInonempty
  let _ : IsDirectedOrder I := hIdir
  let _ : x.Final := hx
  -- Then compose the two final functors to obtain the directed presentation of the target.
  exact ⟨I, inferInstance, inferInstance, inferInstance, x ⋙ y, inferInstance⟩

/-- Lemma 4.21.5: a filtered, locally small, finally small category admits a final functor from a
nonempty directed partially ordered set. This keeps the source-facing statement at the general
category level, while expressing directedness through the canonical owner class
`IsDirectedOrder` from Definition 4.21.1 and using the owner theorems
`FinallySmall.exists_of_isFiltered` and `IsFiltered.exists_directed` only to build the canonical
bridge to a directed poset. -/
theorem exists_final_from_directed (𝓘 : Type u) [Category.{v} 𝓘] [IsFiltered 𝓘]
    [LocallySmall.{w} 𝓘] [FinallySmall.{w} 𝓘] :
    ∃ (I : Type w) (_ : PartialOrder I) (_ : Nonempty I) (_ : IsDirectedOrder I)
      (x : I ⥤ 𝓘), x.Final := by
  -- First pass to the canonical small filtered model supplied by final smallness.
  obtain ⟨J, hJ, hJfilt, y, hy⟩ := FinallySmall.exists_of_isFiltered.{w} 𝓘
  let _ : SmallCategory J := hJ
  let _ : IsFiltered J := hJfilt
  let _ : y.Final := hy
  -- The helper packages the directed presentation of the small model and the final composition.
  exact exists_final_from_directed_of_final y

/- Small-model core used in the proof of `exists_final_from_directed`: for a small filtered
category, the directed-set presentation is exactly `IsFiltered.exists_directed`. -/
recall IsFiltered.exists_directed

/- Lemma 4.21.5 (1): if `x : I ⥤ 𝓘` is final, then any colimit of `x ⋙ M` induces a colimit of
`M`. This is exactly the canonical theorem `Functor.Final.hasColimit_of_comp`. -/
recall Functor.Final.hasColimit_of_comp

/- Lemma 4.21.5 (1), comparison morphism: for a final functor `x : I ⥤ 𝓘`, the canonical map
`colimit.pre M x` is an isomorphism whenever `M` has a colimit. This is exactly the canonical
instance `Functor.Final.colimit_pre_isIso`. -/
recall Functor.Final.colimit_pre_isIso

/- Lemma 4.21.5 (2): dually, if `x : I ⥤ 𝓘` is final, then any limit of `x.op ⋙ M` induces a
limit of `M`. This is exactly the canonical theorem `Functor.Initial.hasLimit_of_comp`. -/
recall Functor.Initial.hasLimit_of_comp

/- Lemma 4.21.5 (2), comparison morphism: for a final functor `x : I ⥤ 𝓘`, the canonical map
`limit.pre M x.op` is an isomorphism whenever `M` has a limit. This is exactly the canonical
instance `Functor.Initial.limit_pre_isIso`. -/
recall Functor.Initial.limit_pre_isIso

end CategoryTheory

/-! ### Remark_4_21_6 (from Chap04) -/
open CategoryTheory CategoryTheory.Limits

universe u v w

/- Domain-style sampling for Remark 4.21.6:
- primary domain: filtered colimits in category theory, specialized to preorder indexing categories
  and single-object diagrams in `Type`;
- sampled owner API:
  `Finite.exists_le`,
  `IsTop`,
  `Preorder.isTerminalTop`,
  `isIso_ι_of_isTerminal`,
  `SingleObj.functor`,
  `CategoryTheory.Limits.Types.Image`,
  `Set.rangeFactorization`;
- best owner abstraction: the source-facing Boolean idempotent diagram built via
  `SingleObj.functor`, together with the canonical order-theoretic owner `IsTop`, the colimit
  comparison from a terminal object in a preorder category, and the canonical `Type`-image owner
  for the colimit vertex of the Boolean example;
- primitive data: an idempotent endomorphism `f : End X`;
- derived API: the Boolean single-object diagram, its image cocone, the colimit proof for that
  cocone, and the finite-directed/top-stage colimit consequences. -/

/- Source/core/bridge triage for Remark 4.21.6:
- `source-facing`: finite directed preorders have a greatest element, and the Boolean filtered
  diagram attached to an idempotent endomorphism has colimit the image of that endomorphism.
- `core/canonical`: `IsDirectedOrder`, `Finite.exists_le`, `IsTop`, `Preorder.isTerminalTop`,
  `isIso_ι_of_isTerminal`, `SingleObj.functor`, `CategoryTheory.Limits.Types.Image`, and
  `Set.rangeFactorization`.
- `bridge/view`: the canonical cocone from the Boolean idempotent diagram to
  `CategoryTheory.Limits.Types.Image f`, its colimit proof, and the induced `HasColimit` instance
  used by the counterexample.
-/

section BoolIdempotent

variable {X : Type u}

/-- Auxiliary multiplication rule for the Boolean action associated to an idempotent endomorphism. -/
-- Proof sketch: split on the two Boolean values and reduce the nontrivial case to the idempotence
-- relation `f ≫ f = f`.
private lemma bool_idempotent_end_hom_map_mul (f : End X) (hf : f ≫ f = f) (a b : Bool) :
    (cond (a * b) (1 : End X) f : End X) = (cond a (1 : End X) f) * cond b (1 : End X) f := by
  cases a <;> cases b
  · have h : false * false = false := by decide
    simp [h, hf]
  · have h : false * true = false := by decide
    simp [h]
  · have h : true * false = false := by decide
    simp [h]
  · have h : true * true = true := by decide
    simp [h]

private def bool_idempotent_end_hom (f : End X) (hf : f ≫ f = f) : Bool →* End X where
  toFun a := cond a (𝟙 X) f
  map_one' := rfl
  map_mul' := bool_idempotent_end_hom_map_mul f hf

/-- The `SingleObj Bool` diagram attached to an idempotent endomorphism `f`, sending `true` to
`𝟙` and `false` to `f`. This is the source-facing owner object for the Boolean-idempotent clause
of Remark 4.21.6. -/
def bool_idempotent_diagram (f : End X) (hf : f ≫ f = f) :
    SingleObj Bool ⥤ Type u :=
  SingleObj.functor (bool_idempotent_end_hom f hf)

private lemma bool_idempotent_rangeFactorization_naturality (f : End X) (hf : f ≫ f = f)
    (a : Bool) :
    (cond a (1 : End X) f : End X) ≫ Set.rangeFactorization f = Set.rangeFactorization f := by
  cases a
  · ext x
    change f (f x) = f x
    simpa using congrFun hf x
  · rfl

/-- The cocone on the Boolean idempotent diagram with vertex `Set.range f`. -/
private def bool_idempotent_diagram_image_cocone (f : End X) (hf : f ≫ f = f) :
    Cocone (bool_idempotent_diagram f hf) where
  pt := Limits.Types.Image f
  ι :=
    { app := fun _ ↦ Set.rangeFactorization f
      naturality := fun _ _ a ↦ bool_idempotent_rangeFactorization_naturality f hf a }

private lemma bool_idempotent_mem_range_fixed (f : End X) (hf : f ≫ f = f)
    (x : Limits.Types.Image f) : f x.1 = x.1 := by
  rcases x with ⟨x, hx⟩
  rcases hx with ⟨y, rfl⟩
  exact congrFun hf y

/- Remark 4.21.6 (order-theoretic ingredient): with Lean's `≤`-oriented convention for directed
preorders, the existence of a greatest element in a finite directed preorder is the specialization
of `Finite.exists_le` to the identity map. -/
recall Finite.exists_le

/- Remark 4.21.6 (colimit ingredient): if a preorder index has a top element, then that top object
is terminal via `Preorder.isTerminalTop`, and `isIso_ι_of_isTerminal` identifies the colimit with
the top stage. -/
recall Preorder.isTerminalTop

/- Companion recall for the terminal-stage colimit identification used above. -/
recall isIso_ι_of_isTerminal

section FiniteDirectedPreorder

variable {I : Type u} [Preorder I]

section

variable [Finite I] [Nonempty I] [IsDirectedOrder I]

/-- A finite directed preorder has a greatest element. -/
theorem exists_isTop_of_finite_directed : ∃ top : I, IsTop top := by
  obtain ⟨top, htop⟩ := Finite.exists_le (fun i : I ↦ i)
  exact ⟨top, htop⟩

end

variable {C : Type v} [Category.{w} C]

/-- If `top` is greatest in a preorder index category, then any colimit over that preorder is
already the stage at `top`. -/
theorem isIso_ι_of_isTop {top : I} (htop : IsTop top) (F : I ⥤ C) [HasColimit F] :
    IsIso (colimit.ι F top) := by
  refine IsTop.rec (fun [OrderTop I] ↦ ?_) top htop
  simpa using
    (isIso_ι_of_isTerminal (Preorder.isTerminalTop I) F : IsIso (colimit.ι F (⊤ : I)))

section

variable [Finite I] [Nonempty I] [IsDirectedOrder I]

/-- In a finite directed preorder, any colimit is canonically the top stage. -/
theorem exists_topStage_of_finite_directed (F : I ⥤ C) [HasColimit F] :
    ∃ top : I, IsTop top ∧ IsIso (colimit.ι F top) := by
  obtain ⟨top, htop⟩ : ∃ top : I, IsTop top := exists_isTop_of_finite_directed
  exact ⟨top, htop, isIso_ι_of_isTop htop F⟩

end

end FiniteDirectedPreorder

/-- The single-object Boolean category is a finite filtered category. -/
instance singleObjBool_isFiltered : IsFiltered (SingleObj Bool) where
  cocone_objs _ _ := ⟨SingleObj.star Bool, 𝟙 _, 𝟙 _, trivial⟩
  cocone_maps := by
    intro X Y f g
    cases X
    cases Y
    refine ⟨SingleObj.star Bool, false, ?_⟩
    change Bool at f
    change Bool at g
    cases f <;> cases g <;> rfl
  nonempty := ⟨SingleObj.star Bool⟩

/-- For the single-object Boolean diagram of an idempotent endomorphism, the colimit is captured by
its image. -/
-- Proof sketch: the cocone leg is `x ↦ f x`, and every cocone on the Boolean diagram is constant
-- along `f`; this makes the image cocone universal.
private def bool_idempotent_diagram_isColimit_image (f : End X) (hf : f ≫ f = f) :
    IsColimit (bool_idempotent_diagram_image_cocone f hf) where
  desc s x := s.ι.app (SingleObj.star Bool) x.1
  fac s j := by
    cases j
    ext x
    simpa using congrFun (s.w false) x
  uniq s m hm := by
    ext x
    have hx : Set.rangeFactorization f x.1 = x := by
      ext
      exact bool_idempotent_mem_range_fixed f hf x
    simpa [bool_idempotent_diagram_image_cocone, hx] using
      congrFun (hm (SingleObj.star Bool)) x.1

/-- The canonical colimit cocone for the Boolean idempotent diagram, with vertex the image of the
idempotent endomorphism. -/
private def bool_idempotent_diagram_colimitCocone (f : End X) (hf : f ≫ f = f) :
    ColimitCocone (bool_idempotent_diagram f hf) where
  cocone := bool_idempotent_diagram_image_cocone f hf
  isColimit := bool_idempotent_diagram_isColimit_image f hf

instance bool_idempotent_diagram_hasColimit (f : End X) (hf : f ≫ f = f) :
    HasColimit (bool_idempotent_diagram f hf) :=
  HasColimit.mk (bool_idempotent_diagram_colimitCocone f hf)

/-- The colimit of the Boolean idempotent diagram is canonically the image of the idempotent
endomorphism. -/
noncomputable def bool_idempotent_diagram_colimitIsoImage (f : End X) (hf : f ≫ f = f) :
    colimit (bool_idempotent_diagram f hf) ≅ Limits.Types.Image f :=
  colimit.isoColimitCocone (bool_idempotent_diagram_colimitCocone f hf)

@[simp] theorem bool_idempotent_diagram_colimitIsoImage_hom_ι (f : End X) (hf : f ≫ f = f) :
    colimit.ι (bool_idempotent_diagram f hf) (SingleObj.star Bool) ≫
        (bool_idempotent_diagram_colimitIsoImage f hf).hom =
      Set.rangeFactorization f := by
  exact colimit.isoColimitCocone_ι_hom (bool_idempotent_diagram_colimitCocone f hf)
    (SingleObj.star Bool)

/-- The constant-false idempotent endomorphism of `Bool`. -/
def bool_constant_false_end : End Bool := fun _ ↦ false

theorem bool_constant_false_end_idempotent :
    bool_constant_false_end ≫ bool_constant_false_end = bool_constant_false_end := by
  ext b
  rfl

/-- The constant-false Boolean example shows that a finite filtered colimit in `Type` need not be a
trivial stage value. -/
-- Proof sketch: the chosen colimit cocone has singleton point `Set.range (fun _ ↦ false)`,
-- and its unique cocone leg identifies both elements of `Bool`.
theorem bool_constant_false_diagram_colimit_iota_not_iso :
    ¬ IsIso
      (colimit.ι
        (bool_idempotent_diagram bool_constant_false_end bool_constant_false_end_idempotent)
        (SingleObj.star Bool)) := by
  intro h
  letI := h
  have himage :
      IsIso
        ((bool_idempotent_diagram_image_cocone bool_constant_false_end
          bool_constant_false_end_idempotent).ι.app (SingleObj.star Bool)) := by
    simpa using
      (show IsIso
        (colimit.ι
            (bool_idempotent_diagram bool_constant_false_end
              bool_constant_false_end_idempotent)
            (SingleObj.star Bool) ≫
          (bool_idempotent_diagram_colimitIsoImage bool_constant_false_end
            bool_constant_false_end_idempotent).hom) by
        infer_instance)
  have hbijective : Function.Bijective (Set.rangeFactorization bool_constant_false_end) := by
    change Function.Bijective
      (((bool_idempotent_diagram_image_cocone bool_constant_false_end
          bool_constant_false_end_idempotent).ι.app (SingleObj.star Bool)))
    exact (isIso_iff_bijective _).1 himage
  have hfactorization_not_injective :
      ¬ Function.Injective (Set.rangeFactorization bool_constant_false_end) := by
    rw [Set.rangeFactorization_injective]
    intro h_injective
    exact Bool.false_ne_true (h_injective rfl)
  exact hfactorization_not_injective hbijective.1

end BoolIdempotent

/-! ### Lemma_4_21_7 (from Chap04) -/
/-
Domain-style sampling for Lemma 4.21.7:
- primary domain: cofiltered and inverse systems of finite nonempty types, expressed through
  sections of `Type`-valued diagrams;
- relevant owner declarations inspected:
  - `nonempty_sections_of_finite_cofiltered_system.init` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`,
  - `nonempty_sections_of_finite_cofiltered_system` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`,
  - `nonempty_sections_of_finite_inverse_system` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`,
  - the chapter-level inverse-system owner expression `Iᵒᵈ ⥤ C` in `Definition_4_21_4`.
- best owner abstraction:
  - `source-facing`: the inverse-limit nonemptiness statement for a directed inverse system,
  - `core/canonical`: `nonempty_sections_of_finite_inverse_system`,
  - `bridge/view`: `nonempty_sections_of_finite_cofiltered_system` as the more general cofiltered
    owner theorem specialized to thin categories of directed preorders.
- primitive data: a diagram `F : Jᵒᵖ ⥤ Type v` together with the instance assumptions that each
  stage is finite and nonempty;
- derived API: the proposition `F.sections.Nonempty` and the cofiltered generalization. -/

/-
Source/core/bridge triage for Lemma 4.21.7:
- `source-facing`: a directed inverse system of finite nonempty sets has a nonempty inverse limit.
- `core/canonical`: `nonempty_sections_of_finite_inverse_system`, with
  `nonempty_sections_of_finite_cofiltered_system` as the general cofiltered owner theorem.
- `bridge/view`: the inverse-system statement is the preorder-specialized companion of the
  cofiltered theorem from `Mathlib.CategoryTheory.CofilteredSystem`.
-/

/- Lemma 4.21.7: a directed inverse system of finite nonempty sets has a nonempty inverse limit.
This is exactly the canonical mathlib theorem `nonempty_sections_of_finite_inverse_system`. -/
recall nonempty_sections_of_finite_inverse_system

/- General companion: the same statement for an arbitrary cofiltered diagram of finite nonempty
sets is exactly the canonical theorem `nonempty_sections_of_finite_cofiltered_system`. -/
recall nonempty_sections_of_finite_cofiltered_system
