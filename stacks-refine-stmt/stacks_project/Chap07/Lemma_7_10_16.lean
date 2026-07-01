import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Plus

universe v u

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (F : Cᵒᵖ ⥤ Type (max u v))
variable (U : C)

/- Domain-style sampling for Lemma 7.10.16:
- primary domain: sheafification of set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.Meq`,
  `CategoryTheory.Presheaf.IsLocallySurjective`,
  `CategoryTheory.Presheaf.IsLocallyInjective`,
  `CategoryTheory.Presheaf.IsSheaf.amalgamate`,
  `CategoryTheory.Presheaf.IsSheaf.hom_ext`;
- source-facing layer: the two textbook assertions describing sections of `J.sheafify F` in terms
  of local representatives in `F` and the converse gluing of compatible matching families;
- core/canonical owners: the matching-family object `Meq F S`, the local-bijectivity owners for
  `J.toSheafify F`, and the sheaf gluing/extensionality API on `J.sheafify F`;
- bridge/view layer: the source-facing existence and uniqueness theorems below, derived from those
  owner abstractions.

Primitive data for the second assertion are exactly a cover `S : J.Cover U` and a matching family
`x : Meq F S`. The glued section, its restriction formula, and the uniqueness statement are
derived API from the canonical sheaf owner `J.sheafify_isSheaf F`; no additional public wrapper
around matching families is warranted.
-/

-- Proof sketch: local surjectivity of `J.toSheafify F` gives local representatives for any
-- section of `J.sheafify F`, and local injectivity provides the compatibility on overlaps after
-- refining by further covers. Conversely, `J.sheafify F` is a sheaf, so any compatible matching
-- family of sections of `F` glues uniquely to a global section.
/-- Lemma 7.10.16, first assertion: every section of the sheafification is locally represented by a
compatible matching family of sections of the original presheaf. The compatibility datum is the
canonical mathlib object `Meq F S`. -/
theorem exists_cover_and_matchingFamily_of_sheafification_section
    (s : (J.sheafify F).obj (op U)) :
    ∃ (S : J.Cover U) (x : Meq F S),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I) := by
  sorry

/-- Companion source-facing formulation of Lemma 7.10.16, second assertion: a compatible matching
family glues uniquely to a section of the sheafification. -/
theorem existsUnique_sheafificationSection_of_matchingFamily
    (S : J.Cover U) (x : Meq F S) :
    ∃! s : (J.sheafify F).obj (op U),
      ∀ I : S.Arrow,
        (J.sheafify F).map I.f.op s = (J.toSheafify F).app (op I.Y) (x I) := by
  let y : ∀ I : S.Arrow, PUnit ⟶ (J.sheafify F).obj (op I.Y) :=
    fun I _ ↦ (J.toSheafify F).app (op I.Y) (x I)
  have hy :
      ∀ ⦃I₁ I₂ : S.Arrow⦄ (r : I₁.Relation I₂),
        y I₁ ≫ (J.sheafify F).map r.g₁.op = y I₂ ≫ (J.sheafify F).map r.g₂.op := by
    intro I₁ I₂ r
    funext _
    change
      (J.sheafify F).map r.g₁.op ((J.toSheafify F).app (op I₁.Y) (x I₁)) =
        (J.sheafify F).map r.g₂.op ((J.toSheafify F).app (op I₂.Y) (x I₂))
    rw [← FunctorToTypes.naturality _ _ (J.toSheafify F) r.g₁.op (x I₁)]
    rw [← FunctorToTypes.naturality _ _ (J.toSheafify F) r.g₂.op (x I₂)]
    exact congrArg ((J.toSheafify F).app (op r.Z))
      (x.condition (Cover.Relation.mk' r))
  refine ⟨((J.sheafify_isSheaf F).amalgamate S y hy) PUnit.unit, ?_, ?_⟩
  · intro I
    exact congrFun ((J.sheafify_isSheaf F).amalgamate_map S y hy I) PUnit.unit
  intro s hs
  have h :
      (fun _ : PUnit ↦ s) = (J.sheafify_isSheaf F).amalgamate S y hy := by
    apply (J.sheafify_isSheaf F).hom_ext S
    intro I
    funext u
    cases u
    simpa [y, hs I] using
      congrFun (((J.sheafify_isSheaf F).amalgamate_map S y hy I).symm) PUnit.unit
  exact congrFun h PUnit.unit
