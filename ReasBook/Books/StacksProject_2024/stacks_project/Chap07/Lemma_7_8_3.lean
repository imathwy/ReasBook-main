import StacksProject_2024.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {U : C}

namespace SemiRepresentableFamily
namespace Over

/- Domain-style sampling for Lemma 7.8.3:
- primary domain: the fixed-target family relations `Refines`, `CombinatoriallyEquivalent`, and
  `TautologicallyEquivalent` on `SemiRepresentableFamily.Over U`;
- inspected declarations:
  `SemiRepresentableFamily.Over.Refines`,
  `SemiRepresentableFamily.Over.CombinatoriallyEquivalent`,
  `SemiRepresentableFamily.Over.TautologicallyEquivalent`,
  `eq_equivalence`,
  `Equivalence.comap`;
- best owner abstraction: the relation owners from Definitions 7.8.1 and 7.8.2, with the
  equality-based owner theorem `eq_equivalence.comap` supplying the canonical equivalence proof for
  `CombinatoriallyEquivalent`;
- primitive data: the three relation definitions, where `TautologicallyEquivalent` directly asks
  for pointwise slice isomorphisms on the two refinement morphisms;
- derived API here: the owner lemmas `TautologicallyEquivalent.refines`,
  `TautologicallyEquivalent.refl`, `TautologicallyEquivalent.symm`,
  `TautologicallyEquivalent.trans`, `Refines.refl`, `Refines.trans`, and the source-facing
  implication from tautological equivalence to mutual refinement,
  and the three equivalence-relation statements.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma clauses relating the three notions of equivalence/refinement;
- `core/canonical`: the owner relations `Refines`, `CombinatoriallyEquivalent`, and
  `TautologicallyEquivalent`;
- `bridge/view`: `TautologicallyEquivalent.refines`.
-/

/- Companion recall: `combinatoriallyEquivalent_implies_tautologicallyEquivalent` was introduced in
Definition 7.8.2 and provides the first implication relating these notions of equivalence. -/
#check combinatoriallyEquivalent_implies_tautologicallyEquivalent

theorem TautologicallyEquivalent.refines
    {𝒰 𝒱 : Over U} (h : TautologicallyEquivalent 𝒰 𝒱) :
    Refines 𝒰 𝒱 := by
  rcases h with ⟨f, _, _, _⟩
  exact ⟨f⟩

theorem TautologicallyEquivalent.refl (𝒰 : Over U) :
    TautologicallyEquivalent 𝒰 𝒰 := by
  refine ⟨𝟙 𝒰, 𝟙 𝒰, ?_, ?_⟩
  · intro i
    exact ⟨Iso.refl (𝒰.obj i)⟩
  · intro i
    exact ⟨Iso.refl (𝒰.obj i)⟩

theorem TautologicallyEquivalent.symm
    {𝒰 𝒱 : Over U} (h : TautologicallyEquivalent 𝒰 𝒱) :
    TautologicallyEquivalent 𝒱 𝒰 := by
  rcases h with ⟨f, g, hf, hg⟩
  exact ⟨g, f, hg, hf⟩

theorem TautologicallyEquivalent.trans
    {𝒰 𝒱 𝒲 : Over U}
    (h𝒰𝒱 : TautologicallyEquivalent 𝒰 𝒱)
    (h𝒱𝒲 : TautologicallyEquivalent 𝒱 𝒲) :
    TautologicallyEquivalent 𝒰 𝒲 := by
  rcases h𝒰𝒱 with ⟨f, g, hf, hg⟩
  rcases h𝒱𝒲 with ⟨f', g', hf', hg'⟩
  refine ⟨f ≫ f', g' ≫ g, ?_, ?_⟩
  · intro i
    rcases hf i with ⟨e⟩
    rcases hf' (f.f i) with ⟨e'⟩
    exact ⟨e ≪≫ e'⟩
  · intro i
    rcases hg' i with ⟨e'⟩
    rcases hg (g'.f i) with ⟨e⟩
    exact ⟨e' ≪≫ e⟩

theorem Refines.refl (𝒰 : Over U) : Refines 𝒰 𝒰 :=
  ⟨𝟙 𝒰⟩

theorem Refines.trans
    {𝒰 𝒱 𝒲 : Over U} (h𝒰𝒱 : Refines 𝒰 𝒱) (h𝒱𝒲 : Refines 𝒱 𝒲) :
    Refines 𝒰 𝒲 :=
  Nonempty.map2 (· ≫ ·) h𝒰𝒱 h𝒱𝒲

-- Proof sketch: unpack a tautological equivalence into morphisms of fixed-target families in both
-- directions and regard them as morphisms of fixed-target families over the identity of `U`,
-- yielding refinements in both directions.
/-- Lemma 7.8.3 (1): tautologically equivalent families of morphisms with fixed target refine each
other. -/
theorem tautologicallyEquivalent_implies_refines_in_both_directions
    {𝒰 𝒱 : Over U} (h : TautologicallyEquivalent 𝒰 𝒱) :
    Refines 𝒰 𝒱 ∧ Refines 𝒱 𝒰 := by
  exact ⟨h.refines, h.symm.refines⟩

-- Proof sketch: `CombinatoriallyEquivalent` is equality of the canonical presieves attached to the
-- two families, so reflexivity, symmetry, and transitivity are the corresponding equality laws.
/-- Lemma 7.8.3 (2): combinatorial equivalence is an equivalence relation on families of
morphisms with fixed target `U`. -/
theorem combinatoriallyEquivalent_isEquivalence :
    _root_.Equivalence (CombinatoriallyEquivalent : Over U → Over U → Prop) :=
  by
    simpa [CombinatoriallyEquivalent] using
      eq_equivalence.comap (fun 𝒰 : Over U ↦ 𝒰.toPresieve)

-- Proof sketch: reflexivity uses identity morphisms, symmetry swaps the two refinement morphisms,
-- and transitivity composes refinement morphisms while the composition of isomorphisms remains an
-- isomorphism in the slice category.
/-- Lemma 7.8.3 (3): tautological equivalence is an equivalence relation on families of morphisms
with fixed target `U`. -/
theorem tautologicallyEquivalent_isEquivalence :
    _root_.Equivalence (TautologicallyEquivalent : Over U → Over U → Prop) :=
  by
    exact ⟨TautologicallyEquivalent.refl, TautologicallyEquivalent.symm,
      TautologicallyEquivalent.trans⟩

-- Proof sketch: reflexivity is given by identity morphisms, symmetry swaps the two refinement
-- maps, and transitivity composes the refinement morphisms in each direction.
/-- Lemma 7.8.3 (4): refining each other is an equivalence relation on families of morphisms with
fixed target `U`. -/
theorem refines_in_both_directions_isEquivalence :
    _root_.Equivalence
      (fun 𝒰 𝒱 : Over U ↦ Refines 𝒰 𝒱 ∧ Refines 𝒱 𝒰) :=
  by
    refine ⟨?_, ?_, ?_⟩
    · intro 𝒰
      exact ⟨Refines.refl 𝒰, Refines.refl 𝒰⟩
    · intro 𝒰 𝒱 h
      exact ⟨h.2, h.1⟩
    · intro 𝒰 𝒱 𝒲 h𝒰𝒱 h𝒱𝒲
      exact ⟨h𝒰𝒱.1.trans h𝒱𝒲.1, h𝒱𝒲.2.trans h𝒰𝒱.2⟩

end Over
end SemiRepresentableFamily

end CategoryTheory
