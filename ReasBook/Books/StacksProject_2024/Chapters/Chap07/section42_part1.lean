import Mathlib
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.UnivLE
import Mathlib.Logic.Small.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_7_42_1 (from Chap07) -/
open CategoryTheory.Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

open scoped SheafifiedRepresentable

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 7.42.1:
- primary domain: sheafified representables in the topos `Sh(C, J)` and initial objects there;
- sampled owner declarations:
  `GrothendieckTopology.sheafifiedRepresentable`,
  `CategoryTheory.GrothendieckTopology.SheafifiedRepresentable.h[_]^#[_]`,
  `CategoryTheory.Limits.IsInitial`,
  `CategoryTheory.Limits.IsInitial.ofIso`;
- best owner abstraction: the canonical sheaf object `h[U]^#[J]` together with the initial-object
  owner `IsInitial`;
- primitive data: only the site `(C, J)` and the object `U : C`;
- derived API: any equivalence with the canonical map `∅^# ⟶ h[U]^#[J]` being an isomorphism or
  with bottom-sieve covering belongs downstream, not in this owner file.

Source/core/bridge triage:
- `source-facing`: the Stacks Project predicate that `U` is sheaf theoretically empty;
- `core/canonical`: the witness-valued owner `IsInitial (h[U]^#[J])`;
- `bridge/view`: later reformulations via unique sections and the bottom covering sieve.

Because `IsInitial` is witness-valued rather than `Prop`-valued, this file keeps only the
source-facing existence predicate and does not introduce any extra wrapper data around the
canonical owner.
-/
/-- Definition 7.42.1: an object `U` of a site `(C, J)` is sheaf theoretically empty if the
sheafified representable `h_U^#`, written canonically elsewhere as `h[U]^#[J]`, is initial in the
sheaf category. Since mathlib's canonical owner `IsInitial` is witness-valued rather than
`Prop`-valued, the source-facing predicate is exactly the proposition that such a witness exists,
with no extra package data beyond that canonical witness. This is equivalent to the source
formulation that the canonical morphism `∅^# ⟶ h_U^#` is an isomorphism. -/
def IsSheafTheoreticallyEmpty (J : GrothendieckTopology C) (U : C) : Prop :=
  Nonempty (IsInitial h[U]^#[J])

namespace IsSheafTheoreticallyEmpty

-- Proof sketch: unfold `J.IsSheafTheoreticallyEmpty U`; it is definitionally the proposition that
-- the sheafified representable `h[U]^#[J]` admits an `IsInitial` witness.
/-- A sheaf theoretically empty object has an initial sheafified representable witness. -/
theorem nonempty_isInitial {J : GrothendieckTopology C} {U : C}
    (hU : J.IsSheafTheoreticallyEmpty U) :
    Nonempty (IsInitial h[U]^#[J]) := by
  -- Unfolding the definition identifies the hypothesis with the target witness proposition.
  simpa [GrothendieckTopology.IsSheafTheoreticallyEmpty] using hU

end IsSheafTheoreticallyEmpty

end CategoryTheory.GrothendieckTopology

/-! ### Lemma_7_42_2 (from Chap07) -/
open CategoryTheory Opposite Limits

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 7.42.2:
- primary domain: Grothendieck topologies, sheafification, and initial/terminal objects in the
  sheaf category;
- sampled owner API:
  `GrothendieckTopology.IsSheafTheoreticallyEmpty`,
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`,
  `Sheaf.isTerminalOfBotCover`,
  `Presieve.isTerminal_of_isSheafFor_empty_presieve`;
- source/core/bridge triage:
  `source-facing`: the equivalent reformulations and pullback stability of sheaf theoretically
  empty objects;
  `core/canonical`: the owner predicate
  `J.IsSheafTheoreticallyEmpty U := Nonempty (IsInitial (h[U]^#[J]))`;
  `bridge/view`: the unique-sections and bottom-sieve-cover reformulations.

Primitive data are only `J`, `U`, and the canonical owner predicate. The unique-sections and
bottom-sieve clauses are derived API, so local helper declarations for the empty presheaf and its
sheafification are unnecessary duplicate wheel definitions and are removed in favor of the
canonical owners above. -/

-- Proof sketch: the canonical map `∅^# ⟶ h_U^#` is an isomorphism exactly when precomposition
-- with it induces bijections on Hom-sets into every sheaf. By the sheafification adjunction,
-- `Hom(h_U^#, ℱ)` identifies with sections `ℱ(U)`, while `Hom(∅^#, ℱ)` is always a singleton
-- because `∅` is initial in presheaves. This yields the unique-sections formulation.
/-- An object `U` is sheaf theoretically empty exactly when every set-valued sheaf on `(C, J)`
has a unique section over `U`. -/
theorem sheafTheoreticallyEmpty_iff_forall_unique_sections
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔
      ∀ ℱ : Sheaf J (Type (max u v)), Nonempty (Unique (ℱ.obj.obj (op U))) := by
  constructor
  · intro hU ℱ
    -- Unpack the initiality witness for the sheafified representable.
    rcases (show Nonempty (IsInitial (J.uliftSheafifiedRepresentable U)) from by
      simpa [GrothendieckTopology.IsSheafTheoreticallyEmpty] using hU) with ⟨hInit⟩
    -- Transport the unique morphism out of the initial object across the Yoneda-style equivalence.
    refine ⟨{
      default := (J.uliftSheafifiedRepresentableHomEquiv ℱ U) (IsInitial.to hInit ℱ)
      uniq := fun s ↦ ?_
    }⟩
    have hs :
        (J.uliftSheafifiedRepresentableHomEquiv ℱ U).symm s = IsInitial.to hInit ℱ :=
      IsInitial.hom_ext hInit _ _
    rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply s, hs]
  · intro hSections
    classical
    -- Rebuild initiality by choosing the distinguished section in each target sheaf.
    have hInit : Nonempty (IsInitial (J.uliftSheafifiedRepresentable U)) := by
      refine ⟨IsInitial.ofUniqueHom (fun ℱ ↦ ?_) (fun ℱ m ↦ ?_)⟩
      · let hUnique : Unique (ℱ.obj.obj (op U)) := Classical.choice (hSections ℱ)
        exact (J.uliftSheafifiedRepresentableHomEquiv ℱ U).symm hUnique.default
      · let hUnique : Unique (ℱ.obj.obj (op U)) := Classical.choice (hSections ℱ)
        have hm :
            (J.uliftSheafifiedRepresentableHomEquiv ℱ U) m = hUnique.default :=
          hUnique.uniq ((J.uliftSheafifiedRepresentableHomEquiv ℱ U) m)
        rw [← (J.uliftSheafifiedRepresentableHomEquiv ℱ U).symm_apply_apply m, hm]
    simpa [GrothendieckTopology.IsSheafTheoreticallyEmpty] using hInit

/-- Helper for Lemma 7.42.2: a section of the sheafification of the empty presheaf forces the
bottom sieve on `U` to be covering. -/
private lemma bot_mem_of_sheafify_bot_nonempty
    (J : GrothendieckTopology C) (U : C) :
    Nonempty ((J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))).obj (op U)) → (⊥ : Sieve U) ∈ J U := by
  rintro ⟨s⟩
  -- Local surjectivity of `toSheafify` makes the image sieve of `s` covering.
  have hmem :
      Presheaf.imageSieve (J.toSheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) s ∈ J U :=
    Presheaf.imageSieve_mem J (J.toSheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) s
  -- The source presheaf has no sections anywhere, so this image sieve is literally `⊥`.
  have himage :
      Presheaf.imageSieve (J.toSheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))) s = (⊥ : Sieve U) := by
    ext V g
    constructor
    · rintro ⟨t, ht⟩
      have hInit : IsInitial ((⊥_ (Cᵒᵖ ⥤ Type (max u v))).obj (op V)) :=
        IsInitial.isInitialObj ((CategoryTheory.evaluation Cᵒᵖ (Type (max u v))).obj (op V))
          (⊥_ (Cᵒᵖ ⥤ Type (max u v))) initialIsInitial
      have hEmpty : IsEmpty (ToType ((⊥_ (Cᵒᵖ ⥤ Type (max u v))).obj (op V))) :=
        (CategoryTheory.Limits.Types.initial_iff_empty _).mp ⟨hInit⟩
      exact hEmpty.false t
    · intro hg
      exact False.elim hg
  simpa [himage] using hmem

/-- Helper for Lemma 7.42.2: if the bottom sieve on `U` is covering, then every sheaf has a
unique section over `U`. -/
private lemma forall_unique_sections_of_bot_mem
    (J : GrothendieckTopology C) (U : C) (hbot : (⊥ : Sieve U) ∈ J U) :
    ∀ ℱ : Sheaf J (Type (max u v)), Nonempty (Unique (ℱ.obj.obj (op U))) := by
  intro ℱ
  -- The sheaf condition for the empty cover says that the section type is terminal.
  exact ⟨CategoryTheory.Limits.Types.isTerminalEquivUnique _ (ℱ.isTerminalOfBotCover U hbot)⟩

-- Proof sketch: specialize the previous theorem to the sheaf of closed sieves to detect when the
-- bottom sieve is covering, and use the empty-presieve sheaf condition to translate a covering
-- bottom sieve into singleton section sets for any sheaf.
/-- An object `U` is sheaf theoretically empty exactly when the bottom sieve on `U` is covering. -/
@[simp]
theorem isSheafTheoreticallyEmpty_iff_bot_mem
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔ (⊥ : Sieve U) ∈ J U := by
  constructor
  · intro hU
    let emptySheaf : Sheaf J (Type (max u v)) :=
      ⟨J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v))),
        J.sheafify_isSheaf (⊥_ (Cᵒᵖ ⥤ Type (max u v)))⟩
    -- Apply the unique-sections criterion to the sheafification of the empty presheaf.
    have hUnique :=
      (sheafTheoreticallyEmpty_iff_forall_unique_sections J U).mp hU emptySheaf
    rcases hUnique with ⟨hUnique⟩
    exact bot_mem_of_sheafify_bot_nonempty J U ⟨hUnique.default⟩
  · intro hbot
    -- A covering empty sieve makes every sheaf section set a singleton.
    exact (sheafTheoreticallyEmpty_iff_forall_unique_sections J U).mpr
      (forall_unique_sections_of_bot_mem J U hbot)

-- Proof sketch: use the characterization of sheaf theoretically empty objects by the canonical
-- map `∅^# ⟶ h_U^#`, identify morphisms from `h_U^#` to a sheaf with sections over `U`, apply the
-- sheaf condition for the bottom sieve to characterize singleton section sets, and specialize to
-- the sheafification of the initial presheaf. The bottom-sieve clause is exactly the empty-family
-- covering condition.
/-- Lemma 7.42.2: for an object `U` of a site `(C, J)`, the following are equivalent: `U` is
sheaf theoretically empty, every set-valued sheaf on `(C, J)` has a unique section over `U`, the
sheafification `∅^#` of the initial presheaf has a unique section over `U`, that section type is
nonempty, and the bottom sieve on `U` is covering. -/
theorem sheafTheoreticallyEmpty_tfae (J : GrothendieckTopology C) (U : C) :
    List.TFAE
      [ J.IsSheafTheoreticallyEmpty U,
        ∀ ℱ : Sheaf J (Type (max u v)), Nonempty (Unique (ℱ.obj.obj (op U))),
        Nonempty (Unique ((J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))).obj (op U))),
        Nonempty ((J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v)))).obj (op U)),
        (⊥ : Sieve U) ∈ J U ] := by
  let emptySheaf : Sheaf J (Type (max u v)) :=
    ⟨J.sheafify (⊥_ (Cᵒᵖ ⥤ Type (max u v))),
      J.sheafify_isSheaf (⊥_ (Cᵒᵖ ⥤ Type (max u v)))⟩
  -- Record the source equivalences in the same order as the textbook proof.
  tfae_have 1 ↔ 2 := by
    exact sheafTheoreticallyEmpty_iff_forall_unique_sections J U
  -- Specialize to the sheafification of the empty presheaf.
  tfae_have 2 → 3 := by
    intro h
    simpa [emptySheaf] using h emptySheaf
  -- Forget the `Unique` structure to obtain a section.
  tfae_have 3 → 4 := by
    rintro ⟨hUnique⟩
    exact ⟨hUnique.default⟩
  -- A section of `∅^#(U)` forces the empty sieve to cover `U`.
  tfae_have 4 → 5 := by
    exact bot_mem_of_sheafify_bot_nonempty J U
  -- A covering empty sieve makes every sheaf section set a singleton.
  tfae_have 5 → 2 := by
    exact forall_unique_sections_of_bot_mem J U
  tfae_finish

-- Proof sketch: translate sheaf theoretical emptiness into the bottom-sieve covering condition
-- via `sheafTheoreticallyEmpty_tfae`, pull back the bottom sieve along `f`, use stability of
-- covering sieves and `Sieve.pullback_bot`, and translate back.
namespace IsSheafTheoreticallyEmpty

/-- Pullbacks of sheaf theoretically empty objects are sheaf theoretically empty. -/
theorem of_arrow
    {J : GrothendieckTopology C} {U U' : C}
    (hU : J.IsSheafTheoreticallyEmpty U)
    (f : U' ⟶ U) :
    J.IsSheafTheoreticallyEmpty U' := by
  -- Rewrite the source and target using the bottom-sieve characterization.
  rw [isSheafTheoreticallyEmpty_iff_bot_mem] at hU
  rw [isSheafTheoreticallyEmpty_iff_bot_mem]
  -- Pull back the empty covering sieve along `f`.
  simpa [Sieve.pullback_bot] using J.pullback_stable f hU

end IsSheafTheoreticallyEmpty

end CategoryTheory.GrothendieckTopology

/-! ### Definition_7_42_3 (from Chap07) -/
/- Domain-style sampling for Definition 7.42.3:
- primary domain: Grothendieck topologies and site functors with cover-lifting conditions;
- sampled owner API:
  `CategoryTheory.Functor.IsCocontinuous`,
  `CategoryTheory.Functor.cover_lift`,
  `CategoryTheory.GrothendieckTopology.Cover`,
  `CategoryTheory.GrothendieckTopology.IsSheafTheoreticallyEmpty`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project notion of an almost cocontinuous functor of sites;
  `core/canonical`: the owner class `CategoryTheory.Functor.IsAlmostCocontinuous`, modeled on
  mathlib's owner `Functor.IsCocontinuous`;
  `bridge/view`: the explicit covering-family refinement statement with the
  sheaf-theoretically-empty alternative.

Primitive data are only the functor, the two Grothendieck topologies, and the covering sieve on
`U` obtained by adjoining the sheaf-theoretically-empty-image sieve to the canonical pullback
sieve `T.functorPullback u`. The explicit covering-family refinement and
factorization-through-an-arrow formulations from the source are derived bridge lemmas recovered
from that covering-sieve owner statement. The stronger owner `Functor.IsCocontinuous` remains a
derived special case. -/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Definition 7.42.3: a functor of sites is almost cocontinuous if every covering of `u(U)` can
be pulled back to a covering sieve on `U` consisting of arrows whose image objects are each either
sheaf theoretically empty in `D` or whose map to `u(U)` already belongs to the original covering
sieve. The explicit covering-family refinement and factorization-through-an-arrow formulations are
equivalent and are provided below as derived API. -/
class IsAlmostCocontinuous (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop where
  cover_lift {U : C} {T : Sieve (u.obj U)} (hT : T ∈ K (u.obj U)) :
      ({
        arrows := fun Y f ↦ K.IsSheafTheoreticallyEmpty (u.obj Y) ∨ (T.functorPullback u) f
        downward_closed := by
          intro Y Z f hf g
          rcases hf with h | h
          · exact .inl <| h.of_arrow (u.map g)
          · exact .inr <| (T.functorPullback u).downward_closed h g
      } : Sieve U) ∈ J U

/-- The source-text formulation of almost cocontinuity using explicit factorization through an
arrow of the covering sieve. -/
lemma cover_lift_factors
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsAlmostCocontinuous J K] {U : C} (T : K.Cover (u.obj U)) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      K.IsSheafTheoreticallyEmpty (u.obj I.Y) ∨
        ∃ (j : T.Arrow) (g : u.obj I.Y ⟶ j.Y), g ≫ j.f = u.map I.f := by
  let h : IsAlmostCocontinuous u J K := inferInstance
  let S : Sieve U :=
    {
      arrows := fun Y f ↦ K.IsSheafTheoreticallyEmpty (u.obj Y) ∨
        ((T : Sieve (u.obj U)).functorPullback u) f
      downward_closed := by
        intro Y Z f hf g
        rcases hf with h | h
        · exact .inl <| h.of_arrow (u.map g)
        · exact .inr <| ((T : Sieve (u.obj U)).functorPullback u).downward_closed h g
    }
  have hS : S ∈ J U := by
    simpa [S] using h.cover_lift T.condition
  refine ⟨⟨S, hS⟩, ?_⟩
  intro I
  rcases I.hf with hI | hI
  · exact .inl hI
  · exact .inr ⟨⟨_, _, hI⟩, 𝟙 _, by simp⟩

/-- Every cocontinuous functor of sites is almost cocontinuous. -/
instance isAlmostCocontinuous_of_isCocontinuous
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] :
    IsAlmostCocontinuous u J K where
  cover_lift {U} {T} hT := by
    refine J.superset_covering ?_ <| u.cover_lift J K hT
    intro Y f hf
    exact .inr hf

end Functor

end CategoryTheory
