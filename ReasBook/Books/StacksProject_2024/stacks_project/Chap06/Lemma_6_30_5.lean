import StacksProject_2024.stacks_project.Chap06.Basis_extension_preserves_stalks
import StacksProject_2024.stacks_project.Chap06.Lemma_6_30_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite TopologicalSpace TopCat TopCat.Presheaf
open TopCat.Presheaf.Sheafify

noncomputable section

universe u v

namespace BasisSheaf

variable {X : TopCat.{u}} {B : Set (Opens X)}

/-
Domain-style sampling for Lemma 6.30.5:
- primary domain: sheaves of sets on a basis, their basis stalks, and the extension bridge to
  ordinary sheafification on `X`;
- sampled owner declarations:
  `BasisSiteSheaf.stalk`,
  `BasisSiteSheaf.stalkComparison`,
  `basis_sheaf_stalkComparison_isIso`,
  `BasisSheaf.extend`;
- best owner abstraction: the source-facing basis stalk family
  `∀ x : U, F.stalk hB x.1`, with the ordinary-stalk family of `F.extend hB` obtained by the
  canonical comparison isomorphisms;
- primitive data: the basis sheaf `F`, the basis witness `hB`, the basis open `U`, and sections on
  smaller basis opens;
- derived API: the ordinary-stalk family and the `isLocallyGerm` predicate on the extension.

Source/core/bridge triage:
- `source-facing`: the map `F(U) → ∏_{x ∈ U} F_x` and the basis-neighborhood representability
  predicate from Stacks Lemma 6.30.5;
- `core/canonical`: the chapter owner `BasisSiteSheaf.stalk`;
- `bridge/view`: `BasisSheaf.stalkComparison hB x : F_x → (F.extend hB)_x`.
-/

/-- The stalk of a basis sheaf at `x`, computed on basis neighborhoods of `x`. -/
abbrev stalk (F : BasisSheaf B) (hB : Opens.IsBasis B) (x : X) :=
  (BasisSheaf.toBasisSiteSheaf F hB).stalk x

/-- The canonical comparison from the basis stalk of `F` at `x` to the ordinary stalk of its
extension `F.extend hB`. -/
abbrev stalkComparison (F : BasisSheaf B) (hB : Opens.IsBasis B) (x : X) :
    F.stalk hB x ⟶ (F.extend hB).presheaf.stalk x := by
  change
    ((BasisSheaf.toBasisSiteSheaf F hB).stalk x ⟶
      (BasisSheaf.toBasisSiteSheaf F hB).extend.presheaf.stalk x)
  exact (BasisSheaf.toBasisSiteSheaf F hB).stalkComparison x

/-- Basis-stalk comparison is an isomorphism. -/
theorem stalkComparison_isIso (F : BasisSheaf B) (hB : Opens.IsBasis B) (x : X) :
    IsIso (F.stalkComparison hB x) := by
  change
    IsIso ((BasisSheaf.toBasisSiteSheaf F hB).stalkComparison x)
  exact basis_sheaf_stalkComparison_isIso (BasisSheaf.toBasisSiteSheaf F hB) x

/-- The family of basis-stalk germs associated to a section over a basis open `U`. -/
abbrev sectionToBasisStalkFamily (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B) :
    F.obj.obj (op U) → ∀ x : U.1, F.stalk hB x.1 :=
  fun s x ↦
    colimit.ι
      ((BasisSheaf.toBasisSiteSheaf F hB).stalkDiagram x.1)
      (op ⟨U, x.2⟩) s

/-- The source-facing local representability condition from Stacks Lemma 6.30.5: a family of basis
stalk elements on `U` is locally induced by sections on basis neighborhoods inside `U`. -/
def IsLocallyRepresentable (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B)
    (t : ∀ x : U.1, F.stalk hB x.1) : Prop :=
  ∀ x : U.1,
    ∃ (V : BasisOpen B) (i : V ⟶ U) (_ : x.1 ∈ V.1) (s : F.obj.obj (op V)),
      ∀ y : V.1, t ⟨y.1, i.hom.le y.2⟩ = sectionToBasisStalkFamily F hB V s y

/-- The ordinary-stalk family obtained from a basis-stalk family by the canonical stalk
comparison. -/
abbrev basisStalkFamilyToStalkFamily
    (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B) :
    (∀ x : U.1, F.stalk hB x.1) → ∀ x : U.1, (F.extend hB).presheaf.stalk x.1 :=
  fun t x ↦ F.stalkComparison hB x.1 (t x)

/-- The family of ordinary stalk germs of the extension of a basis sheaf along a basis open `U`. -/
abbrev sectionToStalkFamily (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B) :
    F.obj.obj (op U) → ∀ x : U.1, (F.extend hB).presheaf.stalk x.1 :=
  fun s ↦
    ((F.extend hB).presheaf.toSheafify.app (op U.1)
      (F.restrictExtendComponentHom hB (op U) s)).1

variable (F : BasisSheaf B) (hB : Opens.IsBasis B) (U : BasisOpen B)

-- Proof sketch: this is the defining colimit-germ family, so for each `x : U` we may take the
-- neighborhood `V = U` and the original section `s`.
/-- Any section over `U` determines a basis-stalk family satisfying the source-facing local
representability condition. -/
theorem sectionToBasisStalkFamily_isLocallyRepresentable (s : F.obj.obj (op U)) :
    IsLocallyRepresentable F hB U (sectionToBasisStalkFamily F hB U s) := by
  intro x
  refine ⟨U, 𝟙 U, x.2, s, ?_⟩
  intro y
  simp [sectionToBasisStalkFamily]

-- Proof sketch: on each point, apply the stalk-comparison isomorphism
-- `F_x ≅ (F.extend hB)_x`; the basis-neighborhood condition is exactly the textbook source-facing
-- condition, while `isLocallyGerm` is the ordinary-stalk formulation for the extension.
/-- Bridge theorem: the source-facing basis-local representability condition is equivalent to the
canonical `isLocallyGerm` predicate after transporting basis stalks to ordinary stalks of
`F.extend hB`. -/
theorem isLocallyRepresentable_iff_isLocallyGerm
    (t : ∀ x : U.1, F.stalk hB x.1) :
    IsLocallyRepresentable F hB U t ↔
      (isLocallyGerm (F.extend hB).presheaf).pred
        (basisStalkFamilyToStalkFamily F hB U t) := by
  sorry

-- Proof sketch: first rewrite the basis-stalk family into the ordinary-stalk family using the
-- comparison isomorphisms `F_x ≅ (F.extend hB)_x`; then apply the bridge theorem above.
/-- The ordinary-stalk family attached to a section over `U` satisfies the canonical
`isLocallyGerm` predicate on the extension `F.extend hB`. -/
theorem germFamily_isLocallyGerm (s : F.obj.obj (op U)) :
    (isLocallyGerm (F.extend hB).presheaf).pred (sectionToStalkFamily F hB U s) := by
  sorry

-- Proof sketch: this is the source-facing formulation of Stacks Lemma 6.30.5. The codomain is
-- the subtype of basis-stalk families satisfying the textbook basis-neighborhood condition `(*)`.
/-- Lemma 6.30.5: for a sheaf of sets `F` on a basis `B` and a basis open `U`, taking germs gives a
bijection from sections on `U` to families of basis-stalk elements on `U` that are locally induced
by sections on basis neighborhoods inside `U`. -/
theorem sections_bijective_toLocallyRepresentableFamilies :
    Function.Bijective
      (fun s : F.obj.obj (op U) ↦
        show { t : ∀ x : U.1, F.stalk hB x.1 | IsLocallyRepresentable F hB U t } from
          ⟨sectionToBasisStalkFamily F hB U s,
            sectionToBasisStalkFamily_isLocallyRepresentable F hB U s⟩) := sorry

/-- `Set.BijOn` restatement of Lemma 6.30.5. -/
theorem sections_bijOn_locallyRepresentableFamilies :
    Set.BijOn
      (sectionToBasisStalkFamily F hB U)
      (Set.univ : Set (F.obj.obj (op U)))
      { t : ∀ x : U.1, F.stalk hB x.1 | IsLocallyRepresentable F hB U t } := sorry

-- Proof sketch: transport the source-facing bijection of Lemma 6.30.5 through the stalk
-- comparison isomorphisms `F_x ≅ (F.extend hB)_x`, and then use
-- `isLocallyRepresentable_iff_isLocallyGerm`.
/-- Companion bridge: after transporting basis stalks to ordinary stalks of `F.extend hB`, Lemma
6.30.5 becomes the canonical sheafification-style bijection onto locally germ families. -/
theorem sections_bijective_toOrdinaryLocallyGermFamilies :
    Function.Bijective
      (fun s : F.obj.obj (op U) ↦
        show { t : ∀ x : U.1, (F.extend hB).presheaf.stalk x.1 |
            (isLocallyGerm (F.extend hB).presheaf).pred t } from
          ⟨sectionToStalkFamily F hB U s, germFamily_isLocallyGerm F hB U s⟩) := sorry

end BasisSheaf
