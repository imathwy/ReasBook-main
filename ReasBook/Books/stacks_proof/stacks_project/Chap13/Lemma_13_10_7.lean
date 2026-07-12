import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Tactic.StacksAttribute

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

/-- Helper for Lemma 13.10.7: the endpoint transport for shifting `A[1]` and `C[1]` back by
`[-1]` is the canonical `shiftFunctorCompIsoId` comparison. -/
private theorem shift_plus_one_then_minus_one_eq :
    (1 : ℤ) + (-1 : ℤ) = 0 := by
  simp

/-- Helper for Lemma 13.10.7: after shifting the rotated cone short complex by `-1` and
transporting the outer terms along `shiftFunctorCompIsoId`, the composite of the transported maps
is still zero. -/
private theorem transported_shortComplex_comp_zero
    {X₁ X₁' X₂ X₃ X₃' : CochainComplex 𝒜 ℤ}
    (i₁ : X₁' ≅ X₁) (f : X₁' ⟶ X₂) (g : X₂ ⟶ X₃') (i₃ : X₃' ≅ X₃)
    (hfg : f ≫ g = 0) :
    (i₁.inv ≫ f) ≫ (g ≫ i₃.hom) = 0 := by
  -- Proof comment: transport the vanishing composite through the endpoint isomorphisms by
  -- composing `hfg` on the left and right.
  simpa [Category.assoc] using congrArg (fun k ↦ i₁.inv ≫ k ≫ i₃.hom) hfg

/-- Helper for Lemma 13.10.7: inserting the identity on the middle term gives the left square
needed by `ShortComplex.isoMk`. -/
private theorem transported_shortComplex_iso_comm₁₂
    {X₁ X₁' X₂ : CochainComplex 𝒜 ℤ}
    (i₁ : X₁' ≅ X₁) (f : X₁' ⟶ X₂) :
    i₁.inv ≫ f = (i₁.inv ≫ f) ≫ 𝟙 X₂ := by
  -- Proof comment: this is just right-unit simplification for the middle object.
  simp

/-- Helper for Lemma 13.10.7: cancelling the endpoint transport on the right gives the second
square needed by `ShortComplex.isoMk`. -/
private theorem transported_shortComplex_iso_comm₂₃
    {X₂ X₃ X₃' : CochainComplex 𝒜 ℤ}
    (g : X₂ ⟶ X₃') (i₃ : X₃' ≅ X₃) :
    𝟙 X₂ ≫ g = (g ≫ i₃.hom) ≫ i₃.inv := by
  -- Proof comment: insert the identity on `X₃'` as `i₃.hom ≫ i₃.inv`.
  simpa [Category.assoc] using (Iso.hom_inv_id_assoc i₃ g).symm

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
  -- Proof comment: use the generic transport lemma with the zero relation already built into the
  -- shifted rotated-cone short complex.
  let Sshift := (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
    (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ))
  let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app A
  let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app C
  simpa [Sshift, iA, iC] using
    (transported_shortComplex_comp_zero (i₁ := iA) (f := Sshift.f) (g := Sshift.g)
      (i₃ := iC) Sshift.zero)

/-- Helper for Lemma 13.10.7: the left square in the transported shifted-cone short-complex
comparison is tautological after unfolding the chosen endpoint transport on `A`. -/
private theorem shifted_cone_shortComplex_iso_comm₁₂
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    let Sshift := (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
      (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ))
    let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
      shift_plus_one_then_minus_one_eq).app A
    let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
      shift_plus_one_then_minus_one_eq).app C
    iA.inv ≫ Sshift.f = (iA.inv ≫ Sshift.f) ≫ 𝟙 Sshift.X₂ := by
  -- Proof comment: this is the generic left-unit transport square for the chosen endpoint iso.
  let Sshift := (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
    (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ))
  let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app A
  let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app C
  simpa [Sshift, iA, iC] using
    (transported_shortComplex_iso_comm₁₂ (i₁ := iA) (f := Sshift.f))

/-- Helper for Lemma 13.10.7: the right square in the transported shifted-cone short-complex
comparison is tautological after unfolding the chosen endpoint transport on `C`. -/
private theorem shifted_cone_shortComplex_iso_comm₂₃
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    let Sshift := (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
      (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ))
    let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
      shift_plus_one_then_minus_one_eq).app A
    let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
      shift_plus_one_then_minus_one_eq).app C
    𝟙 Sshift.X₂ ≫ Sshift.g = (Sshift.g ≫ iC.hom) ≫ iC.inv := by
  -- Proof comment: this is the generic right-endpoint cancellation square for the chosen iso.
  let Sshift := (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
    (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ))
  let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app A
  let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app C
  simpa [Sshift, iA, iC] using
    (transported_shortComplex_iso_comm₂₃ (g := Sshift.g) (i₃ := iC))

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

/-- Helper for Lemma 13.10.7: the transported shifted cone short complex really has `A` and `C`
as its outer objects. -/
@[simp] private theorem shifted_cone_shortComplex_endpoints
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    (shifted_cone_shortComplex (A := A) (C := C) γ).X₁ = A ∧
      (shifted_cone_shortComplex (A := A) (C := C) γ).X₃ = C := by
  -- Proof comment: both endpoint transports were chosen exactly so that the shifted cone lands
  -- back on the literal outer complexes `A` and `C`.
  constructor <;> rfl

/-- Helper for Lemma 13.10.7: the explicit shifted cone short complex is just the shifted rotated
cone short complex with its outer terms transported back to `A` and `C`. -/
noncomputable def CochainComplex.mappingCone.shifted_cone_shortComplex_iso
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    shifted_cone_shortComplex (A := A) (C := C) γ ≅
      (CochainComplex.mappingCone.triangleRotateShortComplex γ).map
        (shiftFunctor (CochainComplex 𝒜 ℤ) (-1 : ℤ)) :=
  let iA := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app A
  let iC := (shiftFunctorCompIsoId (CochainComplex 𝒜 ℤ) (1 : ℤ) (-1 : ℤ)
    shift_plus_one_then_minus_one_eq).app C
  -- Proof comment: the transported short complex differs from the shifted rotated-cone complex
  -- only by these endpoint identifications.
  ShortComplex.isoMk iA.symm (Iso.refl _) iC.symm
    (shifted_cone_shortComplex_iso_comm₁₂ (A := A) (C := C) γ)
    (shifted_cone_shortComplex_iso_comm₂₃ (A := A) (C := C) γ)

/-- Helper for Lemma 13.10.7: shifting by `-1` and then evaluating in degree `n` is evaluation in
degree `n - 1`. -/
private theorem shift_minus_one_eval_eq (n : ℤ) :
    (-1 : ℤ) + n = n - 1 := by
  omega

/-- Helper for Lemma 13.10.7: composing an equality isomorphism with the identity equality
isomorphism does not change it. -/
private theorem XIsoOfEq_hom_comp_rfl
    {X : CochainComplex 𝒜 ℤ} {p q : ℤ} (h : p = q) :
    (X.XIsoOfEq h).hom ≫ (X.XIsoOfEq (rfl : q = q)).hom = (X.XIsoOfEq h).hom := by
  -- Proof comment: this is the `XIsoOfEq` composition rule specialized to a trivial second step.
  simpa using X.XIsoOfEq_hom_comp_XIsoOfEq_hom h (rfl : q = q)

/-- Helper for Lemma 13.10.7: evaluating the explicit shifted cone short complex in degree `n`
identifies with evaluating the rotated cone short complex in degree `n - 1`. -/
noncomputable def CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (shifted_cone_shortComplex (A := A) (C := C) γ).map
        (HomologicalComplex.eval 𝒜 (up ℤ) n) ≅
      ((CochainComplex.mappingCone.triangleRotateShortComplex γ).map
        (HomologicalComplex.eval 𝒜 (up ℤ) (n - 1))) :=
  ((HomologicalComplex.eval 𝒜 (up ℤ) n).mapShortComplex.mapIso
      (CochainComplex.mappingCone.shifted_cone_shortComplex_iso (A := A) (C := C) γ)) ≪≫
    (CochainComplex.mappingCone.triangleRotateShortComplex γ).mapNatIso
      (CochainComplex.shiftEval 𝒜 (-1 : ℤ) n (n - 1) (shift_minus_one_eval_eq n))

/-- Helper for Lemma 13.10.7: on the left endpoint, the evaluation-level transport from the
shifted cone short complex to the rotated cone short complex is literally the identity. -/
private theorem shifted_cone_shortComplex_eval_iso_hom_τ₁
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).hom.τ₁ =
        (A.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom := by
  -- Proof comment: the chosen endpoint transport on `A` cancels exactly against the `shiftEval`
  -- comparison for `A⟦1⟧`, leaving no residual map on the left endpoint.
  dsimp [CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso,
    CochainComplex.mappingCone.shifted_cone_shortComplex_iso, CochainComplex.shiftEval,
    shiftFunctorCompIsoId]
  simp [CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorAdd'_hom_app_f']
  rw [CochainComplex.XIsoOfEq_shift]
  let h1 : n = n - 1 + 1 := by
    omega
  let h2 : n - 1 + 1 = (n - 1) + 1 := by
    omega
  calc
    (A.XIsoOfEq h1).hom ≫ (A.XIsoOfEq h2).hom = (A.XIsoOfEq (h1.trans h2)).hom := by
      simpa using A.XIsoOfEq_hom_comp_XIsoOfEq_hom h1 h2

/-- Helper for Lemma 13.10.7: on the left endpoint, the inverse evaluation-level transport from
the rotated cone short complex back to the shifted cone short complex is literally the identity. -/
private theorem shifted_cone_shortComplex_eval_iso_inv_τ₁
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).inv.τ₁ =
        (A.XIsoOfEq (show n = (n - 1) + 1 by omega)).inv := by
  -- Proof comment: this is the inverse form of the previous endpoint cancellation.
  dsimp [CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso,
    CochainComplex.mappingCone.shifted_cone_shortComplex_iso, CochainComplex.shiftEval,
    shiftFunctorCompIsoId]
  simp [CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorAdd'_inv_app_f']
  rw [CochainComplex.XIsoOfEq_shift]
  simp [shifted_cone_shortComplex]
  let h1 : n = (n - 1) + 1 := by
    omega
  simpa using A.XIsoOfEq_inv_comp_XIsoOfEq_hom h1 (rfl : n = n)

/-- Helper for Lemma 13.10.7: on the right endpoint, the evaluation-level transport from the
shifted cone short complex to the rotated cone short complex is literally the identity. -/
private theorem shifted_cone_shortComplex_eval_iso_hom_τ₃
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).hom.τ₃ =
        (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom := by
  -- Proof comment: the same cancellation occurs on `C`, because its endpoint transport was
  -- chosen from the same `shiftFunctorCompIsoId` comparison.
  dsimp [CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso,
    CochainComplex.mappingCone.shifted_cone_shortComplex_iso, CochainComplex.shiftEval,
    shiftFunctorCompIsoId]
  simp [CochainComplex.shiftFunctorZero_inv_app_f, CochainComplex.shiftFunctorAdd'_hom_app_f']
  rw [CochainComplex.XIsoOfEq_shift]
  let h1 : n = n - 1 + 1 := by
    omega
  let h2 : n - 1 + 1 = (n - 1) + 1 := by
    omega
  calc
    (C.XIsoOfEq h1).hom ≫ (C.XIsoOfEq h2).hom = (C.XIsoOfEq (h1.trans h2)).hom := by
      simpa using C.XIsoOfEq_hom_comp_XIsoOfEq_hom h1 h2

/-- Helper for Lemma 13.10.7: on the right endpoint, the inverse evaluation-level transport from
the rotated cone short complex back to the shifted cone short complex is literally the identity. -/
private theorem shifted_cone_shortComplex_eval_iso_inv_τ₃
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).inv.τ₃ =
        (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).inv := by
  -- Proof comment: this is the inverse form of the right-endpoint cancellation.
  dsimp [CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso,
    CochainComplex.mappingCone.shifted_cone_shortComplex_iso, CochainComplex.shiftEval,
    shiftFunctorCompIsoId]
  simp [CochainComplex.shiftFunctorZero_hom_app_f, CochainComplex.shiftFunctorAdd'_inv_app_f']
  rw [CochainComplex.XIsoOfEq_shift]
  simp [shifted_cone_shortComplex]
  let h1 : n = (n - 1) + 1 := by
    omega
  simpa using C.XIsoOfEq_inv_comp_XIsoOfEq_hom h1 (rfl : n = n)

/-- Helper for Lemma 13.10.7: rewrite the left endpoint of the transported splitting in the exact
`e.symm.hom` shape that appears in `ShortComplex.Splitting.ofIso`. -/
private theorem shifted_cone_shortComplex_eval_iso_symm_hom_τ₁
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).symm.hom.τ₁ =
        (A.XIsoOfEq (show n = (n - 1) + 1 by omega)).inv := by
  -- Proof comment: `symm.hom` is definitionally the inverse endpoint transport.
  simpa using shifted_cone_shortComplex_eval_iso_inv_τ₁ (A := A) (C := C) γ n

/-- Helper for Lemma 13.10.7: rewrite the left endpoint of the transported splitting in the exact
`e.symm.inv` shape that appears in `ShortComplex.Splitting.ofIso`. -/
private theorem shifted_cone_shortComplex_eval_iso_symm_inv_τ₁
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).symm.inv.τ₁ =
        (A.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom := by
  -- Proof comment: `symm.inv` is definitionally the forward endpoint transport.
  simpa using shifted_cone_shortComplex_eval_iso_hom_τ₁ (A := A) (C := C) γ n

/-- Helper for Lemma 13.10.7: rewrite the right endpoint of the transported splitting in the exact
`e.symm.hom` shape that appears in `ShortComplex.Splitting.ofIso`. -/
private theorem shifted_cone_shortComplex_eval_iso_symm_hom_τ₃
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).symm.hom.τ₃ =
        (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).inv := by
  -- Proof comment: `symm.hom` is definitionally the inverse endpoint transport.
  simpa using shifted_cone_shortComplex_eval_iso_inv_τ₃ (A := A) (C := C) γ n

/-- Helper for Lemma 13.10.7: rewrite the right endpoint of the transported splitting in the exact
`e.symm.inv` shape that appears in `ShortComplex.Splitting.ofIso`. -/
private theorem shifted_cone_shortComplex_eval_iso_symm_inv_τ₃
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).symm.inv.τ₃ =
        (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom := by
  -- Proof comment: `symm.inv` is definitionally the forward endpoint transport.
  simpa using shifted_cone_shortComplex_eval_iso_hom_τ₃ (A := A) (C := C) γ n

/-- Helper for Lemma 13.10.7: on the middle term, the evaluation transport from the shifted cone
short complex to the rotated cone short complex is the `shiftEval` component for the cone term. -/
private theorem shifted_cone_shortComplex_eval_iso_hom_τ₂
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).hom.τ₂ =
        (((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂).XIsoOfEq
          (show n + (-1 : ℤ) = n - 1 by omega)).hom := by
  -- Proof comment: the short-complex isomorphism is the identity on the middle term, so only the
  -- `shiftEval` comparison on the rotated cone contributes here.
  dsimp [CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso,
    CochainComplex.mappingCone.shifted_cone_shortComplex_iso, CochainComplex.shiftEval]
  simp [shifted_cone_shortComplex]

/-- Helper for Lemma 13.10.7: on the middle term, the inverse evaluation transport from the
rotated cone short complex back to the shifted cone short complex is the inverse `shiftEval`
component for the cone term. -/
private theorem shifted_cone_shortComplex_eval_iso_inv_τ₂
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).inv.τ₂ =
        (((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂).XIsoOfEq
          (show n + (-1 : ℤ) = n - 1 by omega)).inv := by
  -- Proof comment: this is the inverse form of the same `shiftEval` transport.
  dsimp [CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso,
    CochainComplex.mappingCone.shifted_cone_shortComplex_iso, CochainComplex.shiftEval]
  simp [shifted_cone_shortComplex]

/-- Helper for Lemma 13.10.7: transporting the middle differential across the evaluation-level
comparison used by `ShortComplex.Splitting.ofIso` converts the shifted differential into the
negative of the rotated-cone differential. -/
private theorem shiftedConeShortComplexEvalIsoSymmTau2DTransport
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
      (A := A) (C := C) γ n).inv.τ₂ ≫
      (shifted_cone_shortComplex (A := A) (C := C) γ).X₂.d n (n + 1) ≫
      (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
        (A := A) (C := C) γ (n + 1)).hom.τ₂ =
      -((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
        (n - 1) (n + 1 - 1)) := by
  -- Route correction: the remaining mismatch is not at the endpoints anymore; it is the sign
  -- carried by the shifted middle differential. Normalize that sign once here.
  rw [shifted_cone_shortComplex_eval_iso_inv_τ₂ (A := A) (C := C) γ n,
    shifted_cone_shortComplex_eval_iso_hom_τ₂ (A := A) (C := C) γ (n + 1)]
  -- Proof comment: after rewriting the evaluation transports to `XIsoOfEq`, the shifted
  -- differential is just the `-1`-shift differential transported to consecutive degrees.
  dsimp [shifted_cone_shortComplex]
  change
    ((((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂).XIsoOfEq
        (show n + (-1 : ℤ) = n - 1 by omega)).inv ≫
      (((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂)⟦(-1 : ℤ)⟧).d n (n + 1) ≫
      (((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂).XIsoOfEq
        (show (n + 1) + (-1 : ℤ) = n + 1 - 1 by omega)).hom =
      -((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
        (n - 1) (n + 1 - 1)))
  rw [CochainComplex.shiftFunctor_obj_d']
  simp only [Int.negOnePow_neg, Int.negOnePow_one, Units.neg_smul, one_smul]
  calc
    ((CochainComplex.mappingCone γ).XIsoOfEq
          (show n + (-1 : ℤ) = n - 1 by omega)).inv ≫
        (-(CochainComplex.mappingCone γ).d (n + -1) (n + 1 + -1)) ≫
          ((CochainComplex.mappingCone γ).XIsoOfEq
            (show (n + 1) + (-1 : ℤ) = n + 1 - 1 by omega)).hom
        =
      -((((CochainComplex.mappingCone γ).XIsoOfEq
            (show n + (-1 : ℤ) = n - 1 by omega)).inv ≫
          (CochainComplex.mappingCone γ).d (n + -1) (n + 1 + -1)) ≫
          ((CochainComplex.mappingCone γ).XIsoOfEq
            (show (n + 1) + (-1 : ℤ) = n + 1 - 1 by omega)).hom) := by
          simp [Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp]
    _ = -(((CochainComplex.mappingCone γ).d (n - 1) (n + 1 + -1)) ≫
          ((CochainComplex.mappingCone γ).XIsoOfEq
            (show (n + 1) + (-1 : ℤ) = n + 1 - 1 by omega)).hom) := by
          simp [Category.assoc]
    _ = -((CochainComplex.mappingCone γ).d (n - 1) (n + 1 - 1)) := by
          simp

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

/-- Helper for Lemma 13.10.7: the explicit shifted cone degreewise-split triangle is
distinguished in `K(\mathcal A)` by the canonical degreewise-split characterization. -/
private theorem shifted_cone_triangleh_distinguished
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    CochainComplex.trianglehOfDegreewiseSplit
        (shifted_cone_shortComplex (A := A) (C := C) γ)
        (CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
          (A := A) (C := C) γ) ∈ distTriang K := by
  -- Proof comment: any triangle of the form `trianglehOfDegreewiseSplit` is distinguished.
  rw [HomotopyCategory.distinguished_iff_iso_trianglehOfDegreewiseSplit]
  exact ⟨_, _, ⟨Iso.refl _⟩⟩

/-- Helper for Lemma 13.10.7: the explicit shifted cone degreewise-split triangle has the same
third morphism as the original distinguished triangle. -/
private theorem rotated_mappingCone_first_map_eq_third_morphism
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    {γ : C ⟶ A⟦(1 : ℤ)⟧}
    (eRotate : (Triangle.mk a b c).rotate.rotate ≅ CochainComplex.mappingCone.triangleh γ)
    (heRotate₁ : eRotate.hom.hom₁ = 𝟙 ((Q).obj C))
    (heRotate₂ : eRotate.hom.hom₂ = ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom) :
    c = (Q).map γ ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).hom := by
  -- Proof comment: the `comm₁` square of the twice-rotated comparison says that the first arrow
  -- of `(Triangle.mk a b c).rotate.rotate`, namely `c`, becomes the honest cone map `Q.map γ`
  -- after postcomposing with the quotient-shift comparison on `A[1]`.
  have hcomm₁ : c ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom = (Q).map γ := by
    simpa [heRotate₁, heRotate₂] using eRotate.hom.comm₁
  calc
    c = c ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom ≫
        ((Functor.commShiftIso Q (1 : ℤ)).app A).hom := by
          simpa [Category.assoc] using
            (congrArg
              (fun k ↦ c ≫ k)
              (((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom_inv_id)).symm
    _ = (Q).map γ ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).hom := by
          simpa [Category.assoc] using
            congrArg (fun k ↦ k ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).hom) hcomm₁

/-- Helper for Lemma 13.10.7: in the homotopy category, the connecting morphism attached to the
explicit shifted cone degreewise-split short complex is represented by `γ`. -/
private theorem shiftedConeHomOfDegreewiseSplit_f
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) (n : ℤ) :
    (CochainComplex.homOfDegreewiseSplit
        (shifted_cone_shortComplex (A := A) (C := C) γ)
        (CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
          (A := A) (C := C) γ)).f n = γ.f n := by
  -- Proof comment: expand `homOfDegreewiseSplit` to the cocycle formula, rewrite the endpoint
  -- transports with the dedicated `τ₁`/`τ₃` lemmas, and use the middle transport lemma to
  -- reduce to the standard rotated-cone cocycle computation.
  rw [CochainComplex.homOfDegreewiseSplit_f]
  dsimp [CochainComplex.cocycleOfDegreewiseSplit,
    CochainComplex.mappingCone.shifted_cone_shortComplex_splitting, ShortComplex.Splitting.ofIso]
  rw [shifted_cone_shortComplex_eval_iso_hom_τ₃ (A := A) (C := C) γ n,
    shifted_cone_shortComplex_eval_iso_inv_τ₁ (A := A) (C := C) γ (n + 1)]
  have htransport :
      ((C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
          (-(CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega)) ≫
            (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
              (A := A) (C := C) γ n).inv.τ₂) ≫
        (shifted_cone_shortComplex (A := A) (C := C) γ).X₂.d n (n + 1) ≫
          (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
            (A := A) (C := C) γ (n + 1)).hom.τ₂ ≫
            (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
              (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv =
        (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
          (-(CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega)) ≫
            (-((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
              (n - 1) (n + 1 - 1))) ≫
              (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
                (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
            (-(CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega)) ≫
              k ≫
              (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
                  (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv)
        (shiftedConeShortComplexEvalIsoSymmTau2DTransport (A := A) (C := C) γ n)
  calc
    ((C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
          (-(CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega)) ≫
            (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
              (A := A) (C := C) γ n).inv.τ₂) ≫
        (shifted_cone_shortComplex (A := A) (C := C) γ).X₂.d n (n + 1) ≫
          (CochainComplex.mappingCone.shifted_cone_shortComplex_eval_iso
            (A := A) (C := C) γ (n + 1)).hom.τ₂ ≫
            (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
                (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv
        = (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
            (-(CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega)) ≫
              (-((CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
                (n - 1) (n + 1 - 1))) ≫
                (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
                    (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv := htransport
    _ = γ.f n := by
      -- Proof comment: apply `d_snd_v` under exactly the signed prefix and suffix that appear in
      -- the goal. First normalize the visible minus signs, then expand `d ≫ snd`, and finally
      -- use `inl ≫ fst = 𝟙` and `inl ≫ snd = 0`.
      have hsign :
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (-(CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega)) ≫
                (-(CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
                  (n - 1) (n + 1 - 1)) ≫
                  (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
                      (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv
            =
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                (CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
                  (n - 1) (n + 1 - 1) ≫
                  (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
                      (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv := by
        let u :=
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
            (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega)
        let w := (CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
          (n - 1) (n + 1 - 1)
        let z :=
          (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
              (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv
        simpa [u, w, z, Category.assoc] using
          congrArg (fun t ↦ t ≫ z) (Preadditive.neg_comp_neg u w)
      have hidx : n - 1 + 1 = n + 1 - 1 := by
        omega
      have hsnd' :
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                (CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
                  (n - 1) (n - 1 + 1) ≫
                  (CochainComplex.mappingCone.snd γ).v (n - 1 + 1) (n - 1 + 1) (by omega) ≫
                    (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv
            =
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                (((CochainComplex.mappingCone.fst γ).1.v (n - 1) (n - 1 + 1) (by omega)) ≫
                    γ.f (n - 1 + 1) +
                  (CochainComplex.mappingCone.snd γ).v (n - 1) (n - 1) (by simp) ≫
                      (A⟦(1 : ℤ)⟧).d (n - 1) (n - 1 + 1)) ≫
                  (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦
              (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
                (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                  k ≫
                    (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv)
              (CochainComplex.mappingCone.d_snd_v (φ := γ) (n - 1) (n - 1 + 1) (by omega))
      have hsnd :
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                (CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
                  (n - 1) (n + 1 - 1) ≫
                  (CochainComplex.mappingCone.snd γ).v (n + 1 - 1) (n + 1 - 1) (by omega) ≫
                    (A.XIsoOfEq (show n + 1 = (n + 1 - 1) + 1 by omega)).inv
            =
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                (((CochainComplex.mappingCone.fst γ).1.v (n - 1) (n - 1 + 1) (by omega)) ≫
                    γ.f (n - 1 + 1) +
                  (CochainComplex.mappingCone.snd γ).v (n - 1) (n - 1) (by simp) ≫
                      (A⟦(1 : ℤ)⟧).d (n - 1) (n - 1 + 1)) ≫
                  (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv := by
        convert hsnd' using 1
        · let s1 : {j : ℤ // n + 1 = j + 1} := ⟨n + 1 - 1, by omega⟩
          let s2 : {j : ℤ // n + 1 = j + 1} := ⟨n - 1 + 1, by omega⟩
          have hs : s1 = s2 := by
            apply Subtype.ext
            change n + 1 - 1 = n - 1 + 1
            omega
          simpa [s1, s2, Category.assoc] using congrArg
            (fun s ↦
              (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
                (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                  (CochainComplex.mappingCone.triangleRotateShortComplex γ).X₂.d
                    (n - 1) s.1 ≫
                    (CochainComplex.mappingCone.snd γ).v s.1 s.1 (by omega) ≫
                      (A.XIsoOfEq s.2).inv)
            hs
      have hfinal :
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                (((CochainComplex.mappingCone.fst γ).1.v (n - 1) (n - 1 + 1) (by omega)) ≫
                    γ.f (n - 1 + 1) +
                  (CochainComplex.mappingCone.snd γ).v (n - 1) (n - 1) (by simp) ≫
                      (A⟦(1 : ℤ)⟧).d (n - 1) (n - 1 + 1)) ≫
                    (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv
            = γ.f n := by
        have hAeq :
              (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv =
                ((A⟦(1 : ℤ)⟧).XIsoOfEq (show n = (n - 1 + 1) by omega)).inv := by
          simp [CochainComplex.XIsoOfEq_shift]
        have hγtransport :
            (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
                  γ.f (n - 1 + 1) ≫
                  ((A⟦(1 : ℤ)⟧).XIsoOfEq (show n = (n - 1 + 1) by omega)).inv =
              γ.f n := by
          have hnat :
              γ.f n ≫
                    ((A⟦(1 : ℤ)⟧).XIsoOfEq (show n = (n - 1 + 1) by omega)).hom =
                  (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫ γ.f (n - 1 + 1) := by
            simpa using
              (HomologicalComplex.XIsoOfEq_hom_naturality
                  (φ := γ) (h := show n = (n - 1 + 1) by omega))
          calc
              (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫ γ.f (n - 1 + 1) ≫
                  ((A⟦(1 : ℤ)⟧).XIsoOfEq (show n = (n - 1 + 1) by omega)).inv
              = γ.f n ≫
                    ((A⟦(1 : ℤ)⟧).XIsoOfEq (show n = (n - 1 + 1) by omega)).hom ≫
                      ((A⟦(1 : ℤ)⟧).XIsoOfEq (show n = (n - 1 + 1) by omega)).inv := by
                  simpa [Category.assoc] using congrArg
                    (fun k ↦
                        k ≫ ((A⟦(1 : ℤ)⟧).XIsoOfEq
                          (show n = (n - 1 + 1) by omega)).inv) hnat.symm
            _ = γ.f n := by
                  simp [Category.assoc]
        calc
          (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
              (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                (((CochainComplex.mappingCone.fst γ).1.v (n - 1) (n - 1 + 1) (by omega)) ≫
                    γ.f (n - 1 + 1) +
                  (CochainComplex.mappingCone.snd γ).v (n - 1) (n - 1) (by simp) ≫
                      (A⟦(1 : ℤ)⟧).d (n - 1) (n - 1 + 1)) ≫
                    (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv
              = (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫ γ.f (n - 1 + 1) ≫
                  (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv := by
                have hcore :
                    (CochainComplex.mappingCone.inl γ).v (n - 1 + 1) (n - 1) (by omega) ≫
                      (((CochainComplex.mappingCone.fst γ).1.v (n - 1) (n - 1 + 1) (by omega)) ≫
                          γ.f (n - 1 + 1) +
                        (CochainComplex.mappingCone.snd γ).v (n - 1) (n - 1) (by simp) ≫
                          (A⟦(1 : ℤ)⟧).d (n - 1) (n - 1 + 1)) ≫
                        (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv
                      =
                    γ.f (n - 1 + 1) ≫
                  (A.XIsoOfEq (show n + 1 = (n - 1 + 1) + 1 by omega)).inv := by
                  simpa only [Preadditive.comp_add, Preadditive.add_comp,
                    Category.assoc, CochainComplex.mappingCone.inl_v_fst_v_assoc,
                    CochainComplex.mappingCone.inl_v_snd_v_assoc, zero_comp, zero_add, add_zero]
                simpa [Category.assoc] using congrArg
                  (fun k ↦ (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫ k) hcore
        _ = (C.XIsoOfEq (show n = (n - 1) + 1 by omega)).hom ≫
                  γ.f (n - 1 + 1) ≫
                  ((A⟦(1 : ℤ)⟧).XIsoOfEq (show n = (n - 1 + 1) by omega)).inv := by
              simpa [hAeq]
        _ = γ.f n := hγtransport
      exact hsign.trans (hsnd.trans hfinal)

/-- Helper for Lemma 13.10.7: in the homotopy category, the connecting morphism attached to the
explicit shifted cone degreewise-split short complex is represented by `γ`. -/
private theorem shiftedConeQMapHomOfDegreewiseSplit_eq_representative
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    (Q).map
        (CochainComplex.homOfDegreewiseSplit
          (shifted_cone_shortComplex (A := A) (C := C) γ)
          (CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
            (A := A) (C := C) γ)) =
      (Q).map γ := by
  -- Proof comment: compute the connecting morphism componentwise before applying the quotient.
  -- The dedicated helper isolates the only transport-heavy normalization.
  have hγ :
      CochainComplex.homOfDegreewiseSplit
          (shifted_cone_shortComplex (A := A) (C := C) γ)
          (CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
            (A := A) (C := C) γ) = γ := by
    ext n
    simpa using shiftedConeHomOfDegreewiseSplit_f (A := A) (C := C) γ n
  exact congrArg ((HomotopyCategory.quotient 𝒜 (up ℤ)).map) hγ

/-- Helper for Lemma 13.10.7: the third morphism of the explicit shifted cone degreewise-split
triangle is the quotient of the representative `γ`, followed by the standard quotient-shift
comparison. -/
private theorem shiftedConeTrianglehMor₃_eq_representative
    {A C : CochainComplex 𝒜 ℤ}
    (γ : C ⟶ A⟦(1 : ℤ)⟧) :
    (CochainComplex.trianglehOfDegreewiseSplit
        (shifted_cone_shortComplex (A := A) (C := C) γ)
        (CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
          (A := A) (C := C) γ)).mor₃ =
      (Q).map γ ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).hom := by
  -- Proof comment: `trianglehOfDegreewiseSplit` is obtained by applying `mapTriangle` to the
  -- cochain-level triangle, so after normalizing the connecting map there is nothing left to
  -- transport except the canonical `commShiftIso` factor.
  simpa [CochainComplex.trianglehOfDegreewiseSplit, CochainComplex.triangleOfDegreewiseSplit] using
    congrArg
      (fun z ↦ z ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).hom)
      (shiftedConeQMapHomOfDegreewiseSplit_eq_representative (A := A) (C := C) γ)

/-- Helper for Lemma 13.10.7: the explicit shifted cone degreewise-split triangle has the same
third morphism as the original distinguished triangle. -/
private theorem shifted_cone_triangleh_mor₃
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    {γ : C ⟶ A⟦(1 : ℤ)⟧}
    (eRotate : (Triangle.mk a b c).rotate.rotate ≅ CochainComplex.mappingCone.triangleh γ)
    (heRotate₁ : eRotate.hom.hom₁ = 𝟙 ((Q).obj C))
    (heRotate₂ : eRotate.hom.hom₂ = ((Functor.commShiftIso Q (1 : ℤ)).app A).symm.hom) :
    (CochainComplex.trianglehOfDegreewiseSplit
        (shifted_cone_shortComplex (A := A) (C := C) γ)
        (CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
          (A := A) (C := C) γ)).mor₃ = c := by
  -- Route correction: the remaining blocker is now isolated to the third morphism. Once this
  -- equality is proved, `isoTriangleOfIso₁₃` gives the final `(id, -, id)` comparison directly.
  have hcγ : c = (Q).map γ ≫ ((Functor.commShiftIso Q (1 : ℤ)).app A).hom := by
    -- Proof comment: extract the concrete representative of the original connecting morphism from
    -- the first commutative square of the twice-rotated comparison.
    exact rotated_mappingCone_first_map_eq_third_morphism
      (A := A) (B := B) (C := C) (a := a) (b := b) (c := c)
      (γ := γ) eRotate heRotate₁ heRotate₂
  -- Proof comment: the target-side normalization is now isolated in the dedicated owner-level
  -- `homOfDegreewiseSplit` computation.
  rw [shiftedConeTrianglehMor₃_eq_representative (A := A) (C := C) γ]
  exact hcγ.symm

/-- Helper for Lemma 13.10.7: a cone comparison on the twice-rotated triangle should be
transported back by two inverse rotations and identified with the canonical degreewise split cone
short complex. -/
lemma exists_degreewiseSplit_triangle_of_rotated_mappingCone
    {A B C : CochainComplex 𝒜 ℤ}
    {a : (Q).obj A ⟶ (Q).obj B}
    {b : (Q).obj B ⟶ (Q).obj C}
    {c : (Q).obj C ⟶ ((Q).obj A)⟦(1 : ℤ)⟧}
    {γ : C ⟶ A⟦(1 : ℤ)⟧}
    (hT : Triangle.mk a b c ∈ distTriang K)
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
  -- Route correction: instead of normalizing a long composite of triangle isomorphisms, compare
  -- the source triangle directly with the explicit degreewise-split target through the identity on
  -- the outer vertices. The only non-formal input is that the target third morphism is `c`.
  refine ⟨(shifted_cone_shortComplex (A := A) (C := C) γ).X₂,
    (shifted_cone_shortComplex (A := A) (C := C) γ).f,
    (shifted_cone_shortComplex (A := A) (C := C) γ).g,
    (shifted_cone_shortComplex (A := A) (C := C) γ).zero,
    CochainComplex.mappingCone.shifted_cone_shortComplex_splitting (A := A) (C := C) γ, ?_⟩
  let T' :=
    CochainComplex.trianglehOfDegreewiseSplit
      (shifted_cone_shortComplex (A := A) (C := C) γ)
      (CochainComplex.mappingCone.shifted_cone_shortComplex_splitting
        (A := A) (C := C) γ)
  have hT' : T' ∈ distTriang K := by
    -- Proof comment: this target triangle is distinguished by construction.
    simpa [T'] using shifted_cone_triangleh_distinguished (A := A) (C := C) γ
  have hMor₃ : T'.mor₃ = c := by
    -- Proof comment: isolate the remaining transport-heavy computation to a dedicated helper.
    simpa [T'] using shifted_cone_triangleh_mor₃
      (A := A) (B := B) (C := C) (a := a) (b := b) (c := c)
      (γ := γ) eRotate heRotate₁ heRotate₂
  refine ⟨CategoryTheory.Pretriangulated.isoTriangleOfIso₁₃
      (Triangle.mk a b c) T' hT hT' (Iso.refl _) (Iso.refl _) ?_, ?_⟩
  · -- Proof comment: with identity outer components, the comparison condition is exactly `hMor₃`.
    rw [hMor₃]
    exact
      (by
        simp :
          c ≫ (shiftFunctor K (1 : ℤ)).map (𝟙 ((Q).obj A)) = 𝟙 ((Q).obj C) ≫ c)
  · -- Proof comment: `isoTriangleOfIso₁₃` is built with the prescribed identity outer terms.
    simp [T']

/-- Lemma 13.10.7: if `(A^•, B^•, C^•, a, b, c)` is a distinguished triangle in
`K(\mathcal A)`, then it is isomorphic, through the identity on `A^•` and `C^•`, to a
distinguished triangle `(A^•, (B')^•, C^•, a', b', c)` coming from a degreewise split short exact
sequence `0 ⟶ A^n ⟶ (B')^n ⟶ C^n ⟶ 0` in every degree. -/
@[stacks 0G6C]
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
      (A := A) (B := B) (C := C) (a := a) (b := b) (c := c) hT
      (γ := γ) eRotate heRotate₁ heRotate₂

end

end CategoryTheory
