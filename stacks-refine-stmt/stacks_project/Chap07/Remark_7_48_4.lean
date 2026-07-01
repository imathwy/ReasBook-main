import Mathlib
import stacks_project.Chap07.Lemma_7_8_3
import stacks_project.Chap07.Remark_7_48_3

-- Declarations for this item will be appended below by the statement pipeline.

universe w' w u v

namespace CategoryTheory

open SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C]

private abbrev CoverFamily (X : C) := SemiRepresentableFamily.Over.{v, u, max u v} X

/- Domain-style sampling for Remark 7.48.4:
- primary domain: precoverages, their closure axioms, and covering families up to tautological
  equivalence;
- inspected owner declarations:
  `Precoverage`,
  `Precoverage.toGrothendieck`,
  `Precoverage.comp_mem_coverings`,
  `Precoverage.mem_coverings_of_isPullback`,
  `Coverage.toGrothendieck_eq_of_tautological_enlargement`,
  `Precoverage.HasIsos`,
  `Precoverage.IsStableUnderComposition`,
  `Precoverage.IsStableUnderBaseChange`,
  `SemiRepresentableFamily.Over.IsCovering`,
  `SemiRepresentableFamily.Over.combinatoriallyEquivalent_implies_tautologicallyEquivalent`;
- best owner abstraction: the source-facing owner here is the modified precoverage
  `Precoverage.tautologicalEnlargement K`; the remark's `(1')-(3')` statements are owner-level
  closure properties of that precoverage, while the induced-topology comparison is a separate
  bridge back to `Coverage`;
- primitive data: the enlarged covering predicate on presieves;
- derived API: the owner-level characterization of its covering families, the remark's modified
  closure axioms, and the equality of the associated Grothendieck topologies.

Source/core/bridge triage:
- `source-facing`: `tautologicalEnlargement`;
- `core/canonical`: `Precoverage C` together with `Precoverage.toGrothendieck` and the canonical
  precoverage owner
  classes for isomorphisms, composition, and base change;
- `bridge/view`: `SemiRepresentableFamily.Over.IsCovering` and the passage from presieve equality
  to tautological equivalence via combinatorial equivalence, plus the final coverage-level topology
  comparison.
-/

namespace Precoverage

/-- Remark 7.48.4: for a precoverage `K`, the "shrunk" collection of coverings consisting of those
presieves tautologically equivalent to some original `K`-cover is the canonical precoverage
obtained by adjoining precisely those tautologically equivalent covering families. -/
def tautologicalEnlargement (K : Precoverage C) : Precoverage C where
  coverings X :=
    { R : Presieve X |
        ∃ 𝒰 𝒱 : CoverFamily X,
          IsCovering K 𝒰 ∧
            TautologicallyEquivalent 𝒰 𝒱 ∧
            𝒱.toPresieve = R }

/-- A family is covering for the tautological enlargement exactly when it is tautologically
equivalent to an original `K`-covering family. -/
theorem isCovering_tautologicalEnlargement_iff
    {K : Precoverage C} {X : C}
    {𝒱 : CoverFamily X} :
    IsCovering K.tautologicalEnlargement 𝒱 ↔
      ∃ 𝒰 : CoverFamily X,
        IsCovering K 𝒰 ∧ TautologicallyEquivalent 𝒰 𝒱 := by
  constructor
  · intro h𝒱
    rcases (by simpa [tautologicalEnlargement, IsCovering] using h𝒱 :
        ∃ 𝒰 𝒲 : CoverFamily X,
          IsCovering K 𝒰 ∧
            TautologicallyEquivalent 𝒰 𝒲 ∧
            𝒲.toPresieve = 𝒱.toPresieve) with ⟨𝒰, 𝒲, h𝒰, h𝒰𝒲, h𝒲𝒱⟩
    refine ⟨𝒰, h𝒰, h𝒰𝒲.trans ?_⟩
    exact combinatoriallyEquivalent_implies_tautologicallyEquivalent
      (by simpa [CombinatoriallyEquivalent] using h𝒲𝒱)
  · rintro ⟨𝒰, h𝒰, h𝒰𝒱⟩
    simpa [tautologicalEnlargement, IsCovering] using
      (show ∃ 𝒰 𝒲 : CoverFamily X,
          IsCovering K 𝒰 ∧
            TautologicallyEquivalent 𝒰 𝒲 ∧
            𝒲.toPresieve = 𝒱.toPresieve from
        ⟨𝒰, 𝒱, h𝒰, h𝒰𝒱, rfl⟩)

/-- Every original `K`-cover is also a cover for the tautological enlargement. -/
theorem le_tautologicalEnlargement (K : Precoverage C) :
    K ≤ K.tautologicalEnlargement := by
  intro X R hR
  rcases R.exists_eq_ofArrows with ⟨ι, Y, f, rfl⟩
  let 𝒰 : CoverFamily X := ofArrows Y f
  refine ⟨𝒰, 𝒰, ?_, TautologicallyEquivalent.refl 𝒰, rfl⟩
  simpa [𝒰, IsCovering] using hR

/-- Remark 7.48.4 (1'): singleton isomorphism families are covering for the tautological
enlargement whenever the original site has isomorphism coverings. -/
theorem mem_tautologicalEnlargement_of_isIso
    {K : Precoverage C} [K.HasIsos]
    {X Y : C} (f : Y ⟶ X) [IsIso f] :
    Presieve.singleton f ∈ K.tautologicalEnlargement X := by
  let 𝒰 : CoverFamily X := ofArrows (fun _ : PUnit ↦ Y) fun _ ↦ f
  refine ⟨𝒰, 𝒰, ?_, TautologicallyEquivalent.refl 𝒰, ?_⟩
  · simpa [𝒰, IsCovering, Presieve.ofArrows_pUnit] using
      (K.mem_coverings_of_isIso f)
  · simp [𝒰, toPresieve, Presieve.ofArrows_pUnit]

instance instHasIsos_tautologicalEnlargement
    (K : Precoverage C) [K.HasIsos] :
    K.tautologicalEnlargement.HasIsos where
  mem_coverings_of_isIso f := mem_tautologicalEnlargement_of_isIso f

/-- Remark 7.48.4 (2'): the tautological enlargement is stable under indexed composition of
covering families whenever the original site is. -/
theorem comp_mem_tautologicalEnlargement
    {K : Precoverage C} [K.IsStableUnderComposition]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ K.tautologicalEnlargement S)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ K.tautologicalEnlargement (X i)) :
    Presieve.ofArrows (fun p : Σ i, σ i ↦ Y p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) ∈
      K.tautologicalEnlargement S := by
  sorry

instance instIsStableUnderComposition_tautologicalEnlargement
    (K : Precoverage C) [K.IsStableUnderComposition] :
    K.tautologicalEnlargement.IsStableUnderComposition where
  comp_mem_coverings := comp_mem_tautologicalEnlargement

/-- Remark 7.48.4 (3'): the tautological enlargement is stable under chosen pullback/base-change
families whenever the original site is. -/
theorem mem_tautologicalEnlargement_of_isPullback
    {K : Precoverage C} [K.IsStableUnderBaseChange]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ K.tautologicalEnlargement S)
    {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    Presieve.ofArrows P p₁ ∈ K.tautologicalEnlargement Y := by
  sorry

instance instIsStableUnderBaseChange_tautologicalEnlargement
    (K : Precoverage C) [K.IsStableUnderBaseChange] :
    K.tautologicalEnlargement.IsStableUnderBaseChange where
  mem_coverings_of_isPullback := mem_tautologicalEnlargement_of_isPullback

end Precoverage

namespace Coverage

open Precoverage

/-- The tautological enlargement of a site defines the same Grothendieck topology as the original
coverage. This formalizes the remark's claim that the modified covering notion makes no difference
to the associated topology. -/
theorem tautologicalEnlargement_toGrothendieck (K : Coverage C) :
    (tautologicalEnlargement K.toPrecoverage).toGrothendieck = K.toGrothendieck := by
  exact toGrothendieck_eq_of_tautological_enlargement
    (le_tautologicalEnlargement K.toPrecoverage) fun _ _ h𝒱 ↦
      isCovering_tautologicalEnlargement_iff.mp h𝒱

end Coverage
end CategoryTheory
