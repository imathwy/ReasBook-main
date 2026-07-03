import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_19_11_1 (from Chap19) -/
open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {U X : C}

/- Domain-style sampling for Lemma 19.11.1:
- primary domain: the ordered type `Subobject X` in an abelian category, with size controlled by a
  separator `U` through the hom-set `U ⟶ X`;
- core/canonical owners: `Subobject X`, `IsSeparator U`, and the ambient chain-condition owners
  `IsNoetherianObject X` / `IsArtinianObject X`;
- primitive data: the objects `U` and `X`, the generator hypothesis `IsSeparator U`, and the
  canonical cardinal comparison involving `Cardinal.mk (U ⟶ X)`;
- derived API: the source-facing prohibitions on strict chains, the stabilization of monotone or
  antitone ordinal-indexed chains, and the cardinal bound on `Subobject X`.

Source/core/bridge triage:
- `source-facing`: the five lemmas below are the Stacks-project cardinal consequences for
  subobject chains;
- `core/canonical`: the underlying owner abstractions are `Subobject X` and the usual
  noetherian/artinian chain conditions on that order;
- no new `bridge/view` owner is introduced here, since the source statements add the explicit
  hom-cardinality bounds rather than merely recalling the owner notions.
-/

/-- Lemma 19.11.1 (1): if `U` is a generator of the abelian category and
`#(U ⟶ X) < κ'`, then there is no strictly increasing chain of subobjects of `X`
indexed by `κ'`. -/
-- Proof sketch: for each strict step in the chain, use that `U` is a generator to choose a
-- morphism `U ⟶ X` factoring through the larger subobject but not the smaller one; these
-- morphisms are pairwise distinct, contradicting the cardinality bound `#(U ⟶ X) < κ'`.
lemma no_strictly_increasing_subobject_chain_of_gt_hom_card
    (hU : IsSeparator U) (κ' : Cardinal.{v}) (hκ' : Cardinal.mk (U ⟶ X) < κ') :
    ¬ ∃ A : κ'.ord.ToType → Subobject X, StrictMono A := sorry

/-- Lemma 19.11.1 (2): if `U` is a generator of the abelian category and
`#(U ⟶ X) < κ'`, then there is no strictly decreasing chain of subobjects of `X`
indexed by `κ'`. -/
-- Proof sketch: pass to the opposite abelian category, where subobjects of `X` become
-- subobjects of `op X` with the order reversed, and apply the increasing-chain statement there.
lemma no_strictly_decreasing_subobject_chain_of_gt_hom_card
    (hU : IsSeparator U) (κ' : Cardinal.{v}) (hκ' : Cardinal.mk (U ⟶ X) < κ') :
    ¬ ∃ A : κ'.ord.ToType → Subobject X, StrictAnti A := sorry

/-- Lemma 19.11.1 (3): if `U` is a generator of the abelian category,
and `α` has cofinality greater than `#(U ⟶ X)`, then every increasing
`α`-indexed sequence of subobjects of `X` is eventually constant. -/
-- Proof sketch: if the sequence were not eventually constant, one extracts a cofinal strictly
-- increasing subsequence indexed by a set of cardinality at most `α.cof`, contradicting the
-- preceding no-chain result when `#(U ⟶ X) < α.cof`.
lemma monotone_subobject_sequence_eventually_constant_of_cof_gt_hom_card
    (hU : IsSeparator U) (α : Ordinal.{v}) (hα : Cardinal.mk (U ⟶ X) < α.cof)
    (A : α.ToType → Subobject X) (hA : Monotone A) :
    ∃ a₀ : α.ToType, ∀ b : α.ToType, a₀ ≤ b → A b = A a₀ := sorry

/-- Lemma 19.11.1 (4): if `U` is a generator of the abelian category,
and `α` has cofinality greater than `#(U ⟶ X)`, then every decreasing
`α`-indexed sequence of subobjects of `X` is eventually constant. -/
-- Proof sketch: apply the increasing-sequence statement in the opposite abelian category, where
-- decreasing chains of subobjects become increasing chains.
lemma antitone_subobject_sequence_eventually_constant_of_cof_gt_hom_card
    (hU : IsSeparator U) (α : Ordinal.{v}) (hα : Cardinal.mk (U ⟶ X) < α.cof)
    (A : α.ToType → Subobject X) (hA : Antitone A) :
    ∃ a₀ : α.ToType, ∀ b : α.ToType, a₀ ≤ b → A b = A a₀ := sorry

/-- Lemma 19.11.1 (5): if `U` is a generator of the abelian category, then the set of
subobjects of `X` has cardinality at most `2 ^ #(U ⟶ X)`. -/
-- Proof sketch: send a subobject `Y ≤ X` to the set of morphisms `U ⟶ X` factoring through `Y`;
-- the generator hypothesis makes this assignment injective, so `Subobject X` embeds into the
-- power set of `Hom(U, X)`.
lemma mk_subobject_le_two_pow_lift_hom_card
    (hU : IsSeparator U) :
    Cardinal.mk (Subobject X) ≤ 2 ^ Cardinal.lift (Cardinal.mk (U ⟶ X)) := sorry

/-! ### Definition_19_11_2 (from Chap19) -/
open CategoryTheory

universe v u

section

variable {C : Type u} [Category.{v} C]
variable (M : C)

/- Domain-style sampling for Definition 19.11.2:
- primary domain: subobject posets in a category, measured by cardinality;
- sampled owner API:
  `Subobject`,
  `Cardinal.mk`,
  `mk_subobject_le_two_pow_lift_hom_card`,
  `is_alpha_small_wrt_monomorphisms_of_subobject_cardinal_lt_cof`;
- best owner abstraction: the canonical type `Subobject M`; the source notion "the size of `M`" is
  derived data, namely the cardinal `Cardinal.mk (Subobject M)`;
- primitive data: the object `M` and its canonical subobject type `Subobject M`;
- derived API: the chapter's later size comparisons and smallness bounds, which specialize this
  same canonical expression under stronger Grothendieck abelian hypotheses.

Source/core/bridge triage:
- `source-facing`: the Stacks definition names the size of `M` as the number of its subobjects;
- `core/canonical`: `Subobject M` together with `Cardinal.mk`;
- `bridge/view`: none.

This file therefore targets the `core/canonical` layer: no local `subobject_size` owner should sit
in parallel with the canonical expression already used downstream.
-/

/- Definition 19.11.2: the size of an object `M` is the cardinality of its type of subobjects.
In the Grothendieck abelian setting of the Stacks chapter, Lean expresses this by the same
canonical formula, which already makes sense in any category. -/
#check Cardinal.mk (Subobject M)

end

/-! ### Lemma_19_11_3 (from Chap19) -/
open CategoryTheory
open Limits

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {S : ShortComplex C}

/-- Lemma 19.11.3 (1): in a short exact sequence in an abelian category,
`#(Subobject M') ≤ #(Subobject M)`. -/
-- Proof sketch: a subobject of `M'` is also a subobject of `M` by composing with the mono
-- `M' ⟶ M`, giving an injection `Subobject M' ↪ Subobject M` and hence the desired cardinal
-- inequality.
lemma subobject_cardinal_subobject_le_of_shortExact (hS : S.ShortExact) :
    Cardinal.mk (Subobject S.X₁) ≤ Cardinal.mk (Subobject S.X₂) := by
  letI := hS.mono_f
  exact Cardinal.mk_le_of_injective (Subobject.map_obj_injective S.f)

/-- Lemma 19.11.3 (2): in a short exact sequence in an abelian category,
`#(Subobject M'') ≤ #(Subobject M)`. -/
-- Proof sketch: pull back subobjects of `M''` along the epimorphism `M ⟶ M''`; this gives an
-- injection `Subobject M'' ↪ Subobject M`, so the cardinality of `Subobject M''` is bounded by
-- that of `Subobject M`.
lemma subobject_cardinal_quotient_le_of_shortExact (hS : S.ShortExact) :
    Cardinal.mk (Subobject S.X₃) ≤ Cardinal.mk (Subobject S.X₂) := by
  letI := hS.epi_g
  let pull : Subobject S.X₃ → Subobject S.X₂ := fun A ↦ (Subobject.pullback S.g).obj A
  have h_pullback : Function.Injective pull := by
    change ∀ A B, pull A = pull B → A = B
    intro A B hAB
    have h_exists_pullback (A : Subobject S.X₃) :
        (Subobject.exists S.g).obj (pull A) = A := by
      have hImage : imageSubobject ((pull A).arrow ≫ S.g) = A := by
        rw [← (Subobject.isPullback S.g A).w]
        haveI : Epi (Subobject.pullbackπ S.g A) :=
          Abelian.epi_fst_of_isLimit A.arrow S.g (Subobject.isPullback S.g A).isLimit
        have hle :
            imageSubobject (Subobject.pullbackπ S.g A ≫ A.arrow) ≤ imageSubobject A.arrow :=
          imageSubobject_comp_le (Subobject.pullbackπ S.g A) A.arrow
        haveI : Epi (Subobject.ofLE _ _ hle) :=
          imageSubobject_comp_le_epi_of_epi (Subobject.pullbackπ S.g A) A.arrow
        haveI : IsIso (Subobject.ofLE _ _ hle) := isIso_of_mono_of_epi (Subobject.ofLE _ _ hle)
        have hEq :
            imageSubobject (Subobject.pullbackπ S.g A ≫ A.arrow) = imageSubobject A.arrow :=
          Subobject.eq_of_comm (asIso (Subobject.ofLE _ _ hle)) (by simp)
        simpa [imageSubobject_mono] using hEq
      apply Subobject.eq_of_comm
        (Subobject.existsIsoImage S.g (pull A) ≪≫
          (imageSubobjectIso _).symm ≪≫
            Subobject.isoOfEq _ _ hImage)
      calc
        ((Subobject.existsIsoImage S.g (pull A)).hom ≫
            (imageSubobjectIso ((pull A).arrow ≫ S.g)).inv ≫
            (Subobject.isoOfEq _ _ hImage).hom) ≫
            A.arrow
            = (Subobject.existsIsoImage S.g (pull A)).hom ≫
                image.ι ((pull A).arrow ≫ S.g) := by
                  simp [Category.assoc]
        _ = ((Subobject.exists S.g).obj (pull A)).arrow := by
              simpa [MonoOver.exists] using
                Over.w ((Subobject.existsCompRepresentativeIso S.g).app (pull A)).hom.hom
    calc
      A = (Subobject.exists S.g).obj (pull A) :=
        (h_exists_pullback A).symm
      _ = (Subobject.exists S.g).obj (pull B) := by simp [hAB]
      _ = B := h_exists_pullback B
  exact Cardinal.mk_le_of_injective h_pullback

end CategoryTheory

/-! ### Lemma_19_11_4 (from Chap19) -/
open CategoryTheory Limits

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
variable {U M : C}

/- Domain-style sampling for Lemma 19.11.4:
- primary domain: generators/separators and smallness of object properties in Grothendieck abelian
  categories;
- sampled owner declarations:
  `isSeparator_iff_exists_not_factors_subobject`,
  `Cardinal.mk (Subobject M)`,
  `ObjectProperty.EssentiallySmall`,
  the derived instance `EssentiallySmall P.FullSubcategory`;
- best owner abstractions: `IsSeparator U` for the generator hypothesis in part (1), and
  `ObjectProperty.EssentiallySmall` for the bounded-size class of objects in part (2);
- primitive data: the separator hypothesis `IsSeparator U`, the object `M`, and the bound
  `Cardinal.mk (Subobject M) ≤ κ`;
- derived API: the existential bounded-coproduct presentation in part (1), and the full-subcategory
  essential-smallness statement in part (2).

Source/core/bridge triage:
- `source-facing`: the existential quotient statement by a coproduct of at most `κ` copies of `U`;
- `core/canonical`: the owner notions `IsSeparator`, `Cardinal.mk (Subobject M)`, and
  `ObjectProperty.EssentiallySmall`;
- `bridge/view`: the formulation of part (2) as essential smallness of the full subcategory, which
  is derived from the owner-level object-property smallness instance.
-/

-- Proof sketch: for each proper subobject `N ⊊ M`, use
-- `isSeparator_iff_exists_not_factors_subobject` to choose a morphism `f_N : U ⟶ M` which does
-- not factor through `N`. Assemble these maps into a single morphism
-- `∐ fun _ : Shrink.{w} (Subobject M) ↦ U ⟶ M`. If its image were a proper subobject, the chosen
-- map attached to that image would factor through it via the coproduct inclusion, a contradiction.
-- Hence this map is epi, and the resulting index set has cardinal at most `κ` after the necessary
-- universe lift from `Type w` to the ambient subobject-cardinality universe.
/-- Lemma 19.11.4 (1): if `U` is a generator of a Grothendieck abelian category and
`|M| = #(Subobject M) ≤ κ`, then `M` is a quotient of a coproduct of at most `κ` copies of `U`. -/
lemma exists_epi_from_coproduct_of_generator_of_subobject_cardinal_le
    (hU : IsSeparator U) (κ : Cardinal) (hM : Cardinal.mk (Subobject M) ≤ κ) :
    ∃ (ι : Type w)
      (_ : Cardinal.lift (Cardinal.mk ι) ≤ Cardinal.lift.{w} κ)
      (f : (∐ fun _ : ι ↦ U) ⟶ M), Epi f := sorry

-- Proof sketch: by part (1), every bounded object is a quotient of a coproduct of at most `κ`
-- copies of the chosen generator, using an index type in `Type w`. Quotients of all such
-- `w`-small coproducts are classified by a set via the corresponding subobject lattices, so the
-- resulting object property is essentially small; the source-facing full-subcategory statement is
-- then the canonical derived instance.
/-- The object property `M ↦ Cardinal.mk (Subobject M) ≤ κ` is essentially small. -/
instance subobjectCardinalLE_essentiallySmall (κ : Cardinal) :
    ObjectProperty.EssentiallySmall.{w}
      (fun M : C ↦ Cardinal.mk (Subobject M) ≤ κ) := by
  sorry

variable (κ : Cardinal)

/- Lemma 19.11.4 (2): for every cardinal `κ`, the full subcategory of objects `M` with
`|M| = #(Subobject M) ≤ κ` is essentially small. This is the canonical full-subcategory instance
attached to `subobjectCardinalLE_essentiallySmall κ`. -/
#check
  (inferInstance :
    EssentiallySmall.{w}
      (ObjectProperty.FullSubcategory (fun M : C ↦ Cardinal.mk (Subobject M) ≤ κ)))

end CategoryTheory

/-! ### Proposition_19_11_5 (from Chap19) -/
open CategoryTheory Limits Opposite MorphismProperty

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{max u v} C]

open Ordinal.ToType

/- Domain-style sampling for 19.11.5:
- primary domain: cardinal-bounded presentability of objects in Grothendieck abelian categories,
  expressed by preservation of colimits of ordinal-indexed monomorphism diagrams under
  `coyoneda.obj (op M)`;
- sampled owner declarations:
  `is_alpha_small_wrt`,
  `Cardinal.mk (Subobject M)`,
  `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`,
  `IsCardinalFiltered.isCardinalFiltered_preorder`;
- best owner abstraction: the core owner is
  `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`; the Stacks proposition is the
  source-facing ordinal-shape specialization of that owner to the chapter predicate
  `is_alpha_small_wrt`;
- primitive data: the object `M`, the ordinal `α`, and the inequality
  `Cardinal.mk (Subobject M) < α.cof`;
- derived API: for any `α`-indexed diagram of monomorphisms, `Hom(M, -)` preserves its colimit,
  i.e. `M` is `α`-small with respect to monomorphisms.

Source/core/bridge triage:
- `source-facing`: `is_alpha_small_wrt M (monomorphisms C) α`;
- `core/canonical`: `IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono`;
- `bridge/view`: the `α.ToType`-indexed specialization supplied by the proof below.
-/

-- Proof sketch: compare with Proposition 19.2.5. For a morphism `f : M ⟶ colim B` into an
-- `α`-indexed transfinite composition of monomorphisms, consider the inverse-image subobjects
-- `f ⁻¹(B_β) ≤ M`. Since there are at most `Cardinal.mk (Subobject M)` such subobjects and
-- `α.cof` is larger, the corresponding indices are bounded in `α`; AB5 then implies one inverse
-- image is all of `M`, so `f` factors through some stage, which is exactly `α`-smallness with
-- respect to monomorphisms.
/-- Proposition 19.11.5: in a Grothendieck abelian category, if the cofinality of `α` is strictly
larger than the size `|M| = Cardinal.mk (Subobject M)` of an object `M`, then `M` is `α`-small
with respect to injections, i.e. with respect to monomorphisms. -/
theorem is_alpha_small_wrt_monomorphisms_of_subobject_cardinal_lt_cof
    (M : C) (α : Ordinal) (hα : Cardinal.mk (Subobject M) < α.cof) :
    is_alpha_small_wrt M (monomorphisms C) α := by
  have hcof_gt_one : 1 < α.cof := by
    refine lt_of_le_of_lt ?_ hα
    rw [Cardinal.one_le_iff_ne_zero, Cardinal.mk_ne_zero_iff]
    exact ⟨⊤⟩
  have hsucc : Order.IsSuccLimit α := (Ordinal.one_lt_cof_iff).1 hcof_gt_one
  letI : Fact α.cof.IsRegular := ⟨Cardinal.isRegular_cof hsucc⟩
  letI : IsCardinalFiltered α.ToType α.cof :=
    isCardinalFiltered_preorder α.ToType α.cof fun K s hs ↦ by
      let j : α.ToType :=
        mk
          ⟨⨆ k, (s k : Ordinal),
            Ordinal.iSup_lt_of_lt_cof hs
              fun k ↦ (show (s k : Ordinal) < α from (s k).toOrd.2)⟩
      refine ⟨j, ?_⟩
      intro k
      have hle : (s k).toOrd ≤ j.toOrd := by
        exact
          show (s k : Ordinal) ≤ j.toOrd from by
            simpa [j] using Ordinal.le_iSup (fun k ↦ (s k : Ordinal)) k
      simpa [j] using mk.monotone hle
  have hM : HasCardinalLT (Subobject M) α.cof := by
    simpa [hasCardinalLT_iff_cardinal_mk_lt] using hα
  intro B hB
  letI : ∀ (j j' : α.ToType) (f : j ⟶ j'), Mono (B.map f) := fun _ _ f ↦ hB f
  exact
    IsGrothendieckAbelian.preservesColimit_coyoneda_obj_of_mono B hM

end

end CategoryTheory

/-! ### Lemma_19_11_6 (from Chap19) -/
open CategoryTheory Limits ZeroObject
open CategoryTheory.MorphismProperty

universe w v u

namespace CategoryTheory

/-- Lemma 19.11.6: in a Grothendieck abelian category with generator `U`, an object `I` is
injective exactly when every morphism from a subobject `M ⊆ U` to `I` extends along the inclusion
`M.arrow : M ⟶ U`. -/
-- Proof sketch: interpret the stated extension property as saying that the zero map `I ⟶ 0` has
-- the right lifting property with respect to every generating monomorphism coming from a subobject
-- of `U`. Then use `generatingMonomorphisms_rlp hU` to identify these with all monomorphisms in a
-- Grothendieck abelian category, and conclude by `injective_iff_rlp_monomorphisms_zero`.
theorem injective_iff_generator_subobject_extension
    {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
    {U I : C} (hU : IsSeparator U) :
    Injective I ↔
      ∀ (M : Subobject U) (φ : (M : C) ⟶ I), ∃ ψ : U ⟶ I, M.arrow ≫ ψ = φ := by
  rw [injective_iff_rlp_monomorphisms_zero,
    ← IsGrothendieckAbelian.generatingMonomorphisms_rlp hU]
  constructor
  · intro h M φ
    let _ : HasLiftingProperty M.arrow (0 : I ⟶ 0) := h _ ⟨M⟩
    let sq : CommSq φ M.arrow (0 : I ⟶ 0) 0 := ⟨by simp⟩
    exact ⟨sq.lift, sq.fac_left⟩
  · intro h A B g hg
    rcases hg with ⟨M⟩
    refine ⟨fun {f b} _ ↦ ?_⟩
    rcases h M f with ⟨l, hl⟩
    exact ⟨⟨{ l := l, fac_left := hl, fac_right := (isZero_zero C).eq_of_tgt _ _ }⟩⟩

end CategoryTheory

/-! ### Theorem_19_11_7 (from Chap19) -/
universe w v u

namespace CategoryTheory

noncomputable section

/- Domain-style sampling for Theorem 19.11.7:
- primary domain: functorial injective embeddings in Grothendieck abelian categories;
- sampled owner declarations:
  `EnoughInjectives`,
  `IsGrothendieckAbelian.enoughInjectives`,
  `HasFunctorialInjectiveEmbeddings`,
  `hasFunctorialInjectiveEmbeddings_of_enoughInjectives`;
- best owner abstraction: this item is a `bridge/view` specialization from the Grothendieck owner
  hypothesis to the Chapter 12 owner `HasFunctorialInjectiveEmbeddings C`;
- primitive data: the canonical mathlib instance `EnoughInjectives C` for a Grothendieck abelian
  category;
- derived API: the Chapter 12 bridge `hasFunctorialInjectiveEmbeddings_of_enoughInjectives`.

Source/core/bridge triage:
- `source-facing`: Theorem 19.11.7, asserting functorial injective embeddings for a Grothendieck
  abelian category;
- `core/canonical`: mathlib's `EnoughInjectives C` instance for Grothendieck abelian categories and
  the project owner `HasFunctorialInjectiveEmbeddings C`;
- `bridge/view`: the specialization from the former to the latter. -/

/-- Theorem 19.11.7: every Grothendieck abelian category admits functorial injective embeddings. -/
noncomputable instance grothendieckAbelian_hasFunctorialInjectiveEmbeddings
    (C : Type u) [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{w} C] :
    HasFunctorialInjectiveEmbeddings C := by
  exact hasFunctorialInjectiveEmbeddings_of_isGrothendieckAbelian

end

end CategoryTheory
