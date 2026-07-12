import Mathlib.CategoryTheory.FiberedCategory.Cartesian

-- Declarations for this item will be appended below by the statement pipeline.

universe uA uB uC vA vB vC

namespace CategoryTheory.Functor

variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]

/- Domain-style sampling for Lemma 4.33.3:
- primary domain: strongly cartesian morphisms for functors and their behavior under composition;
- sampled owner declarations:
  `IsStronglyCartesian`,
  `comp`,
  `of_comp`,
  `map_comp_map`;
- best owner abstraction: `Functor.IsStronglyCartesian`;
- primitive data: a functor pair `F : A ⥤ B`, `G : B ⥤ C`, a morphism `φ : x ⟶ y`, and the two
  strongly cartesian hypotheses for `φ` over `F` and `F.map φ` over `G`;
- derived API: the induced strongly cartesian structure for `φ` over the composite functor
  `F ⋙ G`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma asserting that strong cartesianness is stable under functor
  composition;
- `core/canonical`: the owner predicate `Functor.IsStronglyCartesian`;
- `bridge/view`: none; this file supplies the source-facing functor-composition theorem directly in
  the owner namespace so downstream files reuse one public result instead of carrying private
  duplicates. -/

-- Proof sketch: given a lift `τ` over `g ≫ G.map (F.map φ)`, first use the strong cartesianness
-- of `F.map φ` for `G` to obtain a lift `δ : F.obj a' ⟶ F.obj a` of `g`, then use the strong
-- cartesianness of `φ` for `F` to lift `δ` to `χ : a' ⟶ a`. The universal properties for `G` and
-- `F` then identify `χ` as the unique lift over `g` for the composite functor `F ⋙ G`.
/-- Lemma 4.33.3: if `φ : a ⟶ b` is strongly cartesian for `F : A ⥤ B` and `F.map φ` is strongly
cartesian for `G : B ⥤ C`, then `φ` is strongly cartesian for the composite functor `F ⋙ G`. -/
theorem isStronglyCartesian_map_comp
    (F : A ⥤ B) (G : B ⥤ C) {a b : A} (φ : a ⟶ b)
    [F.IsStronglyCartesian (F.map φ) φ]
    [G.IsStronglyCartesian (G.map (F.map φ)) (F.map φ)] :
    (F ⋙ G).IsStronglyCartesian ((F ⋙ G).map φ) φ := by
  refine
    { toIsHomLift := by
        exact IsHomLift.map φ
      universal_property' := ?_ }
  intro a' g τ hτ
  have hτlift : (F ⋙ G).IsHomLift (g ≫ G.map (F.map φ)) τ := by
    simpa [Functor.comp_map] using hτ
  have hτG : G.map (F.map τ) = g ≫ G.map (F.map φ) := by
    simpa [Functor.comp_map] using
      (@IsHomLift.eq_of_isHomLift _ _ _ _ (F ⋙ G) _ _ (g ≫ G.map (F.map φ)) τ hτlift).symm
  let δ : F.obj a' ⟶ F.obj a :=
    IsStronglyCartesian.map G (G.map (F.map φ)) (F.map φ) hτG (F.map τ)
  letI : G.IsHomLift g δ := by
    dsimp [δ]
    infer_instance
  have hδ : δ ≫ F.map φ = F.map τ := by
    simpa [δ] using
      IsStronglyCartesian.fac G (G.map (F.map φ)) (F.map φ) hτG (F.map τ)
  let χ : a' ⟶ a :=
    IsStronglyCartesian.map F (F.map φ) φ hδ.symm τ
  letI : F.IsHomLift δ χ := by
    dsimp [χ]
    infer_instance
  have hχ : χ ≫ φ = τ := by
    simpa [χ] using IsStronglyCartesian.fac F (F.map φ) φ hδ.symm τ
  letI : (F ⋙ G).IsHomLift g χ := by
    have hδeq : g = G.map δ := IsHomLift.eq_of_isHomLift G g δ
    have hχeq : δ = F.map χ := IsHomLift.eq_of_isHomLift F δ χ
    exact IsHomLift.of_fac (F ⋙ G) g χ rfl rfl (by
      simpa [Functor.comp_map, hχeq] using hδeq)
  refine ⟨χ, ⟨inferInstance, hχ⟩, ?_⟩
  intro π hπ
  have hπlift : (F ⋙ G).IsHomLift g π := hπ.1
  have hπG : G.IsHomLift g (F.map π) := by
    have hπeq : g = G.map (F.map π) := by
      simpa [Functor.comp_map] using
        (@IsHomLift.eq_of_isHomLift _ _ _ _ (F ⋙ G) _ _ g π hπlift)
    exact IsHomLift.of_fac G g (F.map π) rfl rfl (by simpa using hπeq)
  have hFπ : F.map π = δ := by
    exact
      @IsStronglyCartesian.ext _ _ _ _ G _ _ _ _
        (G.map (F.map φ)) (F.map φ) inferInstance _ _ g (F.map π) δ hπG
        (inferInstance : G.IsHomLift g δ) <| by
          calc
            F.map π ≫ F.map φ = F.map (π ≫ φ) := by simp
            _ = F.map τ := by rw [hπ.2]
            _ = δ ≫ F.map φ := hδ.symm
  letI : F.IsHomLift δ π := IsHomLift.of_fac F δ π rfl rfl (by simpa using hFπ.symm)
  exact IsStronglyCartesian.ext F (F.map φ) φ δ (by rw [hπ.2, hχ])

end CategoryTheory.Functor
