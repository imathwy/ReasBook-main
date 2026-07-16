import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import StacksProject_2024.stacks_project.Chap13.Lemma_13_4_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open ComplexShape
open HomologicalComplex

universe v u

namespace CategoryTheory

section

variable {𝒜 : Type u} [Category.{v} 𝒜] [Preadditive 𝒜] [HasZeroObject 𝒜]
  [HasBinaryBiproducts 𝒜]

local notation "K" => HomotopyCategory 𝒜 (up ℤ)
local notation "Q" => HomotopyCategory.quotient 𝒜 (up ℤ)

/- Domain-style sampling for Lemma 13.10.7:
- primary domain: distinguished triangles in the homotopy category of cochain complexes and their
  realization by degreewise split short exact sequences;
- inspected owner declarations:
  `distTriang (K)`,
  `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit`,
  `CochainComplex.trianglehOfDegreewiseSplit`,
  `Triangle.isoMk`;
- best owner abstraction: the canonical owner is the distinguished-triangle class `distTriang K`,
  while the degreewise split model is the bridge/view
  `CochainComplex.trianglehOfDegreewiseSplit`; comparison data should therefore be an ordinary
  triangle isomorphism, not a second local wrapper predicate;
- primitive data: a degreewise split short complex `0 ⟶ A ⟶ B' ⟶ C ⟶ 0` together with a triangle
  isomorphism whose first and third components are identities;
- derived API: distinguishedness of the target triangle and the equality of third morphisms follow
  from `hT` and the triangle-isomorphism commutativity, so they should not be stored as primitive
  public data.
- source/core/bridge triage:
  `source-facing`: the comparison theorem promised by Lemma 13.10.7;
  `core/canonical`: `distTriang K`;
  `bridge/view`: `HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit` together with
    `CochainComplex.trianglehOfDegreewiseSplit`.
-/

-- Proof sketch: use the characterization of distinguished triangles in `K(\mathcal A)` by
-- degreewise split triangles together with the explicit inverse-rotation of a cone triangle. The
-- proof in the text constructs a triangle `(A^•, W^•[-1], C^•, a', b', c)` from the cone of `c`,
-- then applies TR3 and the two-out-of-three lemma for morphisms of triangles to obtain an
-- isomorphism whose first and third components are identities.
/-- Helper for Lemma 13.10.7: after transporting the connecting morphism across the quotient-shift
comparison, it is represented by an actual cochain map. -/
lemma exists_representative_of_homotopy_third_map
    {A C : CochainComplex 𝒜 ℤ}
    (c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧) :
    ∃ γ : C ⟶ A⟦(1 : ℤ)⟧,
      (Q).map γ = c ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom := by
  -- Lift the shifted morphism in the homotopy category to an honest cochain map.
  exact (HomotopyCategory.quotient 𝒜 (up ℤ)).map_surjective
    (c ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom)

/-- Helper for Lemma 13.10.7: once the third morphism is represented by a cochain map
`γ : C^• ⟶ A^•[1]`, the twice-rotated distinguished triangle is isomorphic to the standard
mapping-cone triangle of `γ`, through the identity on `C^•` and the canonical quotient-shift
comparison on `A^•[1]`. -/
lemma exists_double_rotate_iso_mappingCone
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang K)
    {γ : C ⟶ A⟦(1 : ℤ)⟧}
    (hγ : (Q).map γ = c ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom) :
    ∃ e : (Triangle.mk a b c).rotate.rotate ≅ CochainComplex.mappingCone.triangleh γ,
      e.hom.hom₁ = 𝟙 ((Q).obj C) ∧
        e.hom.hom₂ = ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom := by
  have hT₂ : (Triangle.mk a b c).rotate.rotate ∈ distTriang K := by
    -- Rotate twice so that the connecting morphism becomes the first arrow.
    exact rot_of_distTriang _ (rot_of_distTriang _ hT)
  -- Compare two distinguished triangles with the same first arrow.
  obtain ⟨e, he₁, he₂⟩ :=
    exists_iso_of_arrow_iso
      (Triangle.mk a b c).rotate.rotate
      (CochainComplex.mappingCone.triangleh γ)
      hT₂
      (HomotopyCategory.mappingCone_triangleh_distinguished γ)
      (Arrow.isoMk (Iso.refl ((Q).obj C)) (((Functor.commShiftIso Q (1 : ℤ)).app A).symm) (by
        simpa using hγ))
  exact ⟨e, he₁, he₂⟩

/-- Helper for Lemma 13.10.7: a comparison between the twice-rotated triangles transports back by
two inverse rotations to a comparison with the twice inverse-rotated target triangle. -/
noncomputable def double_invRotate_iso_of_double_rotate_iso
    {T T' : Triangle K} (e : T.rotate.rotate ≅ T') :
    T ≅ T'.invRotate.invRotate :=
  -- First undo one rotation on the source, then undo the second one, and finally transport `e`.
  (triangleRotation K).unitIso.app T ≪≫
    (invRotate K).mapIso ((triangleRotation K).unitIso.app T.rotate) ≪≫
      (invRotate K).mapIso ((invRotate K).mapIso e)

/-- Helper for Lemma 13.10.7: after transporting the twice-rotated cone comparison back twice,
the third component simplifies to the identity on `C^•`; the first component still carries an
endpoint transport that will later be cancelled against the shifted degreewise-split comparison. -/
lemma double_invRotate_iso_outer_components
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    {γ : C ⟶ A⟦(1 : ℤ)⟧}
    (eRotate : (Triangle.mk a b c).rotate.rotate ≅ CochainComplex.mappingCone.triangleh γ)
    (heRotate₁ : eRotate.hom.hom₁ = 𝟙 ((Q).obj C))
    (heRotate₂ : eRotate.hom.hom₂ = ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom) :
    let e := double_invRotate_iso_of_double_rotate_iso eRotate
    e.hom.hom₃ = 𝟙 ((Q).obj C) := by
  -- TODO: unfold the two inverse rotations on the third vertex, where no endpoint transport
  -- remains, and simplify using `heRotate₁`.
  sorry

/-- Helper for Lemma 13.10.7: the endpoint transport for shifting `A[1]` and `C[1]` back by
`[-1]` is the canonical `shiftFunctorCompIsoId` comparison. -/
private theorem shift_plus_one_then_minus_one_eq :
    (1 : ℤ) + (-1 : ℤ) = 0 := by
  simp

/-- Helper for Lemma 13.10.7: after shifting the rotated cone short complex by `-1` and
transporting the outer terms along `shiftFunctorCompIsoId`, the composite of the transported maps
is still zero. -/
private theorem shifted_cone_shortComplex_comp_zero
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    let Sshift := (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
      (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ))
    let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
      shift_plus_one_then_minus_one_eq).app A
    let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
      shift_plus_one_then_minus_one_eq).app C
    (iA.inv ≫ Sshift.f) ≫ (Sshift.g ≫ iC.hom) = 0 := by
  -- TODO: insert the endpoint identities `iA.inv ≫ iA.hom = 𝟙` and `iC.hom ≫ iC.inv = 𝟙`
  -- around the shifted rotated-cone composite, then reduce to the canonical zero relation.
  sorry

/-- Helper for Lemma 13.10.7: the source-route short complex is the rotated cone short complex,
shifted by `-1` and with the outer terms transported back to literal `A` and `C`. -/
private noncomputable def shifted_cone_shortComplex
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    ShortComplex (CochainComplex 𝒜 ℤ) :=
  let Sshift := (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
    (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ))
  let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app A
  let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app C
  ShortComplex.mk (iA.inv ≫ Sshift.f) (Sshift.g ≫ iC.hom)
    (shifted_cone_shortComplex_comp_zero (A := A) (C := C) γ)

/-- Helper for Lemma 13.10.7: the explicit shifted cone short complex is just the shifted rotated
cone short complex with its outer terms transported back to `A` and `C`. -/
noncomputable def CochainComplex.mappingCone.shifted_cone_shortComplex_iso
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    shifted_cone_shortComplex (A := A) (C := C) γ ≅
      (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
        (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)) := by
  -- TODO: package the endpoint transports given by `shiftFunctorCompIsoId` into a
  -- `ShortComplex.isoMk`, and verify the two commutative squares after cancelling the
  -- endpoint identities.
  sorry

/-- Helper for Lemma 13.10.7: evaluating the explicit shifted cone short complex in degree `n`
identifies with evaluating the rotated cone short complex in degree `n - 1`. -/
noncomputable def CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (shifted_cone_shortComplex (A := A) (C := C) γ).map
        (HomologicalComplex.eval 𝒜 (up ℤ) n) ≅
      ((CochainComplex.mappingCone.triangleRotateShortComplex γ).map
        (HomologicalComplex.eval 𝒜 (up ℤ) (n - 1))) := by
  -- TODO: first map `shifted_cone_shortComplex_iso` through evaluation, then compose with the
  -- canonical `shiftEval` comparison identifying evaluation after shifting by `-1`.
  sorry

/-- Helper for Lemma 13.10.7: the explicit shifted cone short complex inherits the canonical
degreewise splitting from the rotated cone short complex. -/
noncomputable abbrev CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    ((shifted_cone_shortComplex (A := A) (C := C) γ).map
      (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting :=
  -- Transport the standard rotated-cone splitting across the evaluation-level comparison.
  ShortComplex.Splitting.ofIso
    (CochainComplex.mappingCone.triangleRotateShortComplexSplitting γ (n - 1))
    ((CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).symm)

/-- Helper for Lemma 13.10.7: two inverse rotations of the cone triangle are the `(-1)`-shift of
the once-rotated cone triangle. -/
noncomputable def CochainComplex.mappingCone.invRotateInvRotateIsoShiftedRotate
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    (CochainComplex.mappingCone.triangleh γ).invRotate.invRotate ≅
      ((Triangle.shiftFunctor K (-1)).obj ((CochainComplex.mappingCone.triangleh γ).rotate)) := by
  -- TODO: instantiate `CategoryTheory.Pretriangulated.invRotateIsoRotateRotateShiftFunctorNegOne`
  -- with the once inverse-rotated cone triangle, then simplify the double rotation of
  -- `invRotate` back to the single `rotate`.
  sorry

/-- Helper for Lemma 13.10.7: a cone comparison on the twice-rotated triangle should be
transported back by two inverse rotations and identified with the canonical degreewise split cone
short complex. -/
lemma exists_degreewiseSplit_triangle_of_rotated_mappingCone
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    {γ : C ⟶ A⟦(1 : ℤ)⟧}
    (eRotate : (Triangle.mk a b c).rotate.rotate ≅ CochainComplex.mappingCone.triangleh γ)
    (heRotate₁ : eRotate.hom.hom₁ = 𝟙 ((Q).obj C))
    (heRotate₂ : eRotate.hom.hom₂ = ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom) :
    ∃ (B' : CochainComplex 𝒜 ℤ) (f : A ⟶ B') (g : B' ⟶ C) (hfg : f ≫ g = 0)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting),
      ∃ e : Triangle.mk a b c ≅
          CochainComplex.trianglehOfDegreewiseSplit (ShortComplex.mk f g hfg) σ,
        e.hom.hom₁ = 𝟙 ((Q).obj A) ∧
          e.hom.hom₃ = 𝟙 ((Q).obj C) := by
  -- Route correction: the remaining work is no longer the TR3 comparison. The unresolved part is
  -- the transport from the doubly inverse-rotated cone triangle to the explicit shifted
  -- degreewise split short complex.
  -- TODO: compose `double_invRotate_iso_of_double_rotate_iso eRotate` with the shifted-rotate
  -- comparison for `γ`, then cancel the endpoint transports using the explicit component formulas.
  sorry

/-- Lemma 13.10.7: if `(A^•, B^•, C^•, a, b, c)` is a distinguished triangle in
`K(\mathcal A)`, then it is isomorphic, through the identity on `A^•` and `C^•`, to a
distinguished triangle `(A^•, (B')^•, C^•, a', b', c)` coming from a degreewise split short exact
sequence `0 ⟶ A^n ⟶ (B')^n ⟶ C^n ⟶ 0` in every degree. -/
theorem distinguished_triangle_iso_to_degreewiseSplit
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang K) :
    ∃ (B' : CochainComplex 𝒜 ℤ) (f : A ⟶ B') (g : B' ⟶ C) (hfg : f ≫ g = 0)
      (σ : ∀ n : ℤ,
        ((ShortComplex.mk f g hfg).map (HomologicalComplex.eval 𝒜 (up ℤ) n)).Splitting),
      ∃ e : Triangle.mk a b c ≅
          CochainComplex.trianglehOfDegreewiseSplit (ShortComplex.mk f g hfg) σ,
        e.hom.hom₁ = 𝟙 ((Q).obj A) ∧
          e.hom.hom₃ = 𝟙 ((Q).obj C) := by
  -- Lift the connecting morphism to a cochain map so that the cone construction is available.
  obtain ⟨γ, hγ⟩ := exists_representative_of_homotopy_third_map (A := A) (C := C) c
  -- Compare the twice-rotated triangle with the cone triangle of that representative.
  obtain ⟨eRotate, heRotate₁, heRotate₂⟩ :=
    exists_double_rotate_iso_mappingCone (A := A) (B := B) (C := C) hT hγ
  -- Finish by transporting the cone triangle back twice and rewriting it as the canonical
  -- degreewise split short complex attached to the cone.
  exact
    exists_degreewiseSplit_triangle_of_rotated_mappingCone
      (A := A) (B := B) (C := C) (a := a) (b := b) (c := c)
      (γ := γ) eRotate heRotate₁ heRotate₂

end

end CategoryTheory
