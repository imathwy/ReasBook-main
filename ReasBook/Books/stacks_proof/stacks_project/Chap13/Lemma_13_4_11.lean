import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling:
- primary domain: distinguished triangles in pretriangulated categories, split epimorphisms, and
  the canonical binary biproduct attached to a split distinguished triangle;
- sampled owner declarations:
  `Triangle.mor₃_eq_zero_iff_epi₂`,
  `Triangle.epi₂`,
  `CategoryTheory.isSplitEpi_of_epi`,
  `CategoryTheory.Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
- best owner abstraction: `IsSplitEpi T.mor₂` is the canonical owner for the existence of a right
  inverse to `T.mor₂`, and `exists_iso_binaryBiproduct_of_distTriang` is the canonical owner for
  the induced biproduct splitting of the triangle;
- primitive data: a distinguished triangle `T`, its distinguishedness proof `hT`, and either the
  vanishing hypothesis `T.mor₃ = 0` or an explicit right inverse `s` to `T.mor₂`;
-- derived API: the chosen section supplied by `IsSplitEpi T.mor₂` and the induced map
-- `biprod.desc T.mor₁ s`.

Source/core/bridge triage:
- `source-facing`: the statement that a right inverse to `T.mor₂` produces a biproduct splitting;
- `core/canonical`: `IsSplitEpi T.mor₂` and
  `Pretriangulated.exists_iso_binaryBiproduct_of_distTriang`;
-- `bridge/view`: the `IsIso` statement for `biprod.desc T.mor₁ s`.
-/

-- Proof sketch: `T.mor₃ = 0` makes `T.mor₂` epi by `Triangle.epi₂`; pretriangulated categories
-- are split-epi categories, so the canonical owner `IsSplitEpi T.mor₂` follows from the ambient
-- `SplitEpiCategory` instance.
/-- Lemma 13.4.11 (1): if the third morphism of a distinguished triangle is zero, then the second
morphism is split epic. -/
@[stacks 05QT]
theorem isSplitEpi_mor₂_of_distinguished_mor₃_eq_zero {T : Triangle D}
    (hT : T ∈ distTriang D) (hzero : T.mor₃ = 0) :
    IsSplitEpi T.mor₂ := by
  letI : Epi T.mor₂ := T.epi₂ hT hzero
  exact isSplitEpi_of_epi T.mor₂

-- Proof sketch: a right inverse `s` to `T.mor₂` forces `T.mor₃ = 0` because
-- `T.mor₂` is then split epic, hence epic, so the third morphism vanishes. The exactness
-- criterion `coyoneda_exact₂` then supplies the complementary projection needed to package the
-- given section `s` into the biproduct datum `binaryBiproductData`, whose universal isomorphism
-- identifies `biprod.desc T.mor₁ s` as an inverse.
/-- Lemma 13.4.11 (2): if `s : Z ⟶ Y` is a right inverse to the second morphism in a
distinguished triangle `(X, Y, Z, f, g, h)`, then the induced map `X ⊞ Z ⟶ Y` with components
`f` and `s` is an isomorphism. -/
@[stacks 05QT]
theorem isIso_biprod_desc_of_distinguished_right_inverse {T : Triangle D}
    (hT : T ∈ distTriang D) (s : T.obj₃ ⟶ T.obj₂) (hs : s ≫ T.mor₂ = 𝟙 T.obj₃) :
    IsIso (biprod.desc T.mor₁ s) := by
  have hzero : T.mor₃ = 0 := by
    haveI : IsSplitEpi T.mor₂ := IsSplitEpi.mk' { section_ := s, id := hs }
    exact Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi T.mor₂)
  obtain ⟨fst, hfst⟩ := T.coyoneda_exact₂ hT (𝟙 T.obj₂ - T.mor₂ ≫ s) (by simp [hs])
  have htotal : fst ≫ T.mor₁ + T.mor₂ ≫ s = 𝟙 T.obj₂ := by
    rw [← hfst, sub_add_cancel]
  let d := binaryBiproductData T hT hzero s hs fst htotal
  let e : T.obj₂ ≅ T.obj₁ ⊞ T.obj₃ := biprod.uniqueUpToIso _ _ d.isBilimit
  have hdesc : biprod.desc T.mor₁ s = e.inv := by
    apply biprod.hom_ext'
    · simp [e, d]
    · simp [e, d]
  rw [hdesc]
  infer_instance

/- Lemma 13.4.11 (3): for any objects `X'` and `Z'` of a pre-triangulated category, the standard
split triangle `(X', X' ⊞ Z', Z', (1,0), (0,1), 0)` is distinguished. This is exactly the
canonical theorem `CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished`. -/
recall CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished

end CategoryTheory
