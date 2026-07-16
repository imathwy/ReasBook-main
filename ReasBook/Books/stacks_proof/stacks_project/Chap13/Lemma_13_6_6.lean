import Mathlib
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_proof.stacks_project.Chap04.Definition_4_27_20

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty.IsStableUnderRetracts
open CategoryTheory.Pretriangulated
open scoped ZeroObject

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [ObjectProperty.IsTriangulated P]

/- Domain-style sampling for Lemma `13.6.6`.
- primary domain: saturated compatible multiplicative systems arising from triangulated object
  properties in a triangulated category;
- sampled owner declarations:
  `P.isoClosure.trW`,
  `P.trW`,
  `P.trW_isoClosure`,
  `P.isoClosure.IsTriangulated`,
  `ObjectProperty.IsClosedUnderIsomorphisms`,
  `P.IsStableUnderRetracts`,
  `P.trW.IsMultiplicative`,
  `P.trW.IsCompatibleWithTriangulation`;
- best owner abstraction: the source-facing morphism-property owner is `P.isoClosure.trW`,
  attached to the strictly full triangulated subcategory `P.isoClosure`; `P.trW` is only the
  bridge view provided by `P.trW_isoClosure`;
- source/core/bridge triage:
  `source-facing`: the Stacks saturation condition for the strictly full triangulated subcategory
    attached to `P`, i.e. `P.isoClosure`, together with its canonical Verdier morphism property
    `P.isoClosure.trW`;
  `core/canonical`: the owners `P.isoClosure.trW`, `ObjectProperty.isoClosure`, and
    `ObjectProperty.IsStableUnderRetracts`;
  `bridge/view`: the comparison `P.trW_isoClosure` and the derived reformulation using `P.trW`,
    with the iso-closed specialization as a companion.
- primitive data: the triangulated object property `P`;
- derived API: the multiplicative-system and triangulation-compatibility instances on `P.trW`,
  the iso-closure `P.isoClosure`, the owner theorem on `P.isoClosure.trW`, and its iso-closed
  specialization on `P.trW`.

No extra local wrapper is needed here: the owner-level theorem should use `P.isoClosure.trW`
directly, and the iso-closed `P.trW` formulation should be derived from it rather than exposed
through an extra intermediate bridge theorem.
-/

/- Companion recall: for a triangulated object property `P`, the cone-defined morphism property
`P.trW` is already a multiplicative system by the canonical `trW` instance. -/
#check (inferInstance : MorphismProperty.IsMultiplicative P.trW)

/- Companion recall: for a triangulated object property `P`, the cone-defined morphism property
`P.trW` is already compatible with the triangulated structure by the canonical `trW` instance. -/
#check (inferInstance : MorphismProperty.IsCompatibleWithTriangulation P.trW)

-- Proof sketch: for the forward implication, use the saturation axiom for `P.isoClosure.trW` on
-- the standard distinguished triangles attached to a biproduct decomposition to show that
-- `P.isoClosure` is stable under retracts. For the reverse implication, follow the octahedral
-- argument from the text: if `f ≫ g` and `g ≫ h` lie in `P.isoClosure.trW`, then the cones of
-- these composites lie in `P.isoClosure`; use the octahedron to relate these cones to a cone of
-- `g`, and apply retract stability to conclude that the cone of `g` also lies in `P.isoClosure`.
/-- Helper for Lemma 13.6.6: if the zero morphism `X ⟶ Y` lies in `P.isoClosure.trW`, then the
cone of a distinguished triangle on it is isomorphic to `Y ⊞ X⟦1⟧`, so that biproduct lies in
`P.isoClosure`. -/
private lemma biprod_shift_mem_of_zero_trW
    ⦃X Y : D⦄ (hzero : P.isoClosure.trW (0 : X ⟶ Y)) :
    P.isoClosure (Y ⊞ X⟦(1 : ℤ)⟧) := by
  rcases (P.isoClosure.trW_iff (f := (0 : X ⟶ Y))).1 hzero with ⟨Z, g, h, hT, hZ⟩
  let T : Triangle D := Triangle.mk (0 : X ⟶ Y) g h
  have hT' : T ∈ distTriang D := hT
  have hTrot : T.rotate ∈ distTriang D := rot_of_distTriang _ hT'
  have hzero_rot : T.rotate.mor₃ = 0 := by
    change -((0 : X ⟶ Y)⟦(1 : ℤ)⟧') = 0
    simp
  -- Rotate once so the split-triangle theorem applies to the zero third morphism.
  obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang T.rotate hTrot hzero_rot
  -- Transport membership in `P.isoClosure` across the resulting biproduct identification.
  simpa [T] using (P.isoClosure.prop_of_iso e hZ)

/-- Helper for Lemma 13.6.6: the first morphism of the inverse rotation of the standard split
biproduct triangle is the zero morphism. -/
private lemma invRotate_binaryBiproductTriangle_mor₁_eq_zero
    ⦃X Y : D⦄ :
    ((binaryBiproductTriangle Y X).invRotate).mor₁ = (0 : X⟦(-1 : ℤ)⟧ ⟶ Y) :=
by
  -- Unfold the inverse rotation to reduce the first edge to the negation of a shifted zero map.
  suffices hneg : -(0 : X⟦(-1 : ℤ)⟧ ⟶ Y) = 0 by
    simpa only [Triangle.invRotate_obj₁, Int.reduceNeg, binaryBiproductTriangle_obj₃,
      Triangle.invRotate_obj₂, binaryBiproductTriangle_obj₁, Triangle.invRotate_mor₁,
      binaryBiproductTriangle_mor₃, Functor.map_zero, Limits.zero_comp] using hneg
  exact (neg_zero : -(0 : X⟦(-1 : ℤ)⟧ ⟶ Y) = 0)

/-- Helper for Lemma 13.6.6: under saturation of `P.isoClosure.trW`, membership of `P.isoClosure`
passes to the right summand of a binary biproduct. -/
private lemma isoClosure_of_biprod_right_of_saturated_trW
    [IsSaturatedMultiplicativeSystem P.isoClosure.trW]
    ⦃X Y : D⦄ (hXY : P.isoClosure (X ⊞ Y)) :
    P.isoClosure Y := by
  have hYX : P.isoClosure (Y ⊞ X) := by
    -- Swap the two biproduct summands so the source split triangle targets `Y`.
    exact P.isoClosure.prop_of_iso (Limits.biprod.braiding X Y) hXY
  have hzero_biprod : P.isoClosure.trW (0 : 0 ⟶ Y ⊞ X) := by
    -- The contractible triangle on `Y ⊞ X` identifies this zero map with the cone object itself.
    exact ((P.isoClosure).trW_iff_of_distinguished
      (Triangle.mk (0 : 0 ⟶ Y ⊞ X) (𝟙 (Y ⊞ X)) 0)
      (contractible_distinguished₁ (Y ⊞ X))).2 hYX
  have hzero_left : P.isoClosure.trW (0 : X⟦(-1 : ℤ)⟧ ⟶ Y) := by
    -- The inverse rotation of the split biproduct triangle produces the auxiliary zero map.
    have hT : (binaryBiproductTriangle Y X).invRotate ∈ distTriang D := by
      exact inv_rot_of_distTriang _ (binaryBiproductTriangle_distinguished Y X)
    have hmem : P.isoClosure.trW ((binaryBiproductTriangle Y X).invRotate.mor₁) := by
      exact ((P.isoClosure).trW_iff_of_distinguished ((binaryBiproductTriangle Y X).invRotate) hT).2
        (by simpa [Triangle.invRotate, binaryBiproductTriangle] using hYX)
    rw [invRotate_binaryBiproductTriangle_mor₁_eq_zero (X := X) (Y := Y)] at hmem
    exact hmem
  have hzero_Y : P.isoClosure.trW (0 : 0 ⟶ Y) := by
    -- Saturation removes the middle zero map from the two standard composites.
    have hfg : P.isoClosure.trW ((0 : X⟦(-1 : ℤ)⟧ ⟶ 0) ≫ (0 : 0 ⟶ Y)) := by
      simpa using hzero_left
    have hgh : P.isoClosure.trW ((0 : 0 ⟶ Y) ≫ (Limits.biprod.inl : Y ⟶ Y ⊞ X)) := by
      simpa using hzero_biprod
    simpa using
      (IsSaturatedMultiplicativeSystem.saturation
        (W := P.isoClosure.trW)
        (f := (0 : X⟦(-1 : ℤ)⟧ ⟶ 0))
        (g := (0 : 0 ⟶ Y))
        (h := (Limits.biprod.inl : Y ⟶ Y ⊞ X))
        hfg hgh)
  -- A zero map `0 ⟶ Y` lies in `trW` exactly when `Y` itself lies in `P.isoClosure`.
  exact ((P.isoClosure).trW_iff_of_distinguished
    (Triangle.mk (0 : 0 ⟶ Y) (𝟙 Y) 0)
    (contractible_distinguished₁ Y)).1 hzero_Y

/-- Helper for Lemma 13.6.6: the target of a retract is isomorphic to a biproduct whose right
summand is the retract source. -/
private lemma retract_target_iso_biprod_right
    ⦃X Y : D⦄ (r : Retract X Y) :
    ∃ K : D, Nonempty (Y ≅ K ⊞ X) := by
  obtain ⟨K, i, h, hT⟩ := distinguished_cocone_triangle₁ r.r
  haveI : IsSplitEpi r.r := IsSplitEpi.mk' { section_ := r.i, id := r.retract }
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi r.r)
  -- The split-triangle theorem turns the retract map into the canonical projection.
  obtain ⟨e, _, _⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk i r.r h) hT hzero
  exact ⟨K, ⟨e⟩⟩

/-- Helper for Lemma 13.6.6: if `P.isoClosure` is stable under retracts, then `P.isoClosure.trW`
satisfies the saturation axiom. -/
private lemma saturation_of_isoClosure_trW_of_retract_stable
    [P.isoClosure.IsStableUnderRetracts]
    ⦃W X Y Z : D⦄ (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (hfg : P.isoClosure.trW (f ≫ g)) (hgh : P.isoClosure.trW (g ≫ h)) :
    P.isoClosure.trW g := by
  obtain ⟨Q₁, v₁, w₁, hT₁⟩ := distinguished_cocone_triangle f
  obtain ⟨Q₂, v₂, w₂, hT₂⟩ := distinguished_cocone_triangle g
  obtain ⟨Q₃, v₃, w₃, hT₃⟩ := distinguished_cocone_triangle h
  obtain ⟨Q₁₂, v₁₂, w₁₂, hT₁₂⟩ := distinguished_cocone_triangle (f ≫ g)
  obtain ⟨Q₂₃, v₂₃, w₂₃, hT₂₃⟩ := distinguished_cocone_triangle (g ≫ h)
  have hQ₁₂ : P.isoClosure Q₁₂ := by
    exact ((P.isoClosure).trW_iff_of_distinguished (Triangle.mk (f ≫ g) v₁₂ w₁₂) hT₁₂).1 hfg
  have hQ₂₃ : P.isoClosure Q₂₃ := by
    exact ((P.isoClosure).trW_iff_of_distinguished (Triangle.mk (g ≫ h) v₂₃ w₂₃) hT₂₃).1 hgh
  let o₁₂ :=
    Triangulated.someOctahedron
      (C := D) (show f ≫ g = f ≫ g by rfl) hT₁ hT₂ hT₁₂
  let o₂₃ :=
    Triangulated.someOctahedron
      (C := D) (show g ≫ h = g ≫ h by rfl) hT₂ hT₃ hT₂₃
  let s : Q₂ ⟶ Q₁⟦(1 : ℤ)⟧ := w₂ ≫ v₁⟦(1 : ℤ)⟧'
  let t : Q₃ ⟶ Q₂⟦(1 : ℤ)⟧ := w₃ ≫ v₂⟦(1 : ℤ)⟧'
  have hs : P.isoClosure.trW s := by
    -- Rotate the first octahedral triangle so that `s` becomes its second morphism.
    have hs' : P.isoClosure.trW ((o₁₂.triangle.rotate).mor₂) := by
      exact trW.mk' P.isoClosure (rot_of_distTriang _ o₁₂.mem) hQ₁₂
    simpa [s, Triangulated.Octahedron.triangle, o₁₂] using hs'
  have ht : P.isoClosure.trW t := by
    -- The same rotated argument on the second octahedron gives `t ∈ trW`.
    have ht' : P.isoClosure.trW ((o₂₃.triangle.rotate).mor₂) := by
      exact trW.mk' P.isoClosure (rot_of_distTriang _ o₂₃.mem) hQ₂₃
    simpa [t, Triangulated.Octahedron.triangle, o₂₃] using ht'
  have hs_shift : P.isoClosure.trW (s⟦(1 : ℤ)⟧') := by
    simpa using (IsCompatibleWithShift.iff P.isoClosure.trW s (1 : ℤ)).2 hs
  have hts : P.isoClosure.trW (t ≫ s⟦(1 : ℤ)⟧') := by
    exact P.isoClosure.trW.comp_mem _ _ ht hs_shift
  have hzero_ts : t ≫ s⟦(1 : ℤ)⟧' = 0 := by
    have hmid' := congrArg (fun k ↦ k⟦(1 : ℤ)⟧') (comp_distTriang_mor_zero₂₃ _ hT₂)
    have hmid0 :
        (shiftFunctor D (1 : ℤ)).map (0 : Y ⟶ X⟦(1 : ℤ)⟧) =
          (0 : Y⟦(1 : ℤ)⟧ ⟶ X⟦(1 : ℤ)⟧⟦(1 : ℤ)⟧) := by
      simp
    have hmid : v₂⟦(1 : ℤ)⟧' ≫ w₂⟦(1 : ℤ)⟧' = 0 := by
      simpa [Functor.map_comp] using hmid'.trans hmid0
    -- The middle factor vanishes because it is the shifted composition of consecutive triangle maps.
    calc
      t ≫ s⟦(1 : ℤ)⟧'
          = w₃ ≫ (v₂⟦(1 : ℤ)⟧' ≫ w₂⟦(1 : ℤ)⟧') ≫ (shiftFunctor D (1 : ℤ)).map ((shiftFunctor D (1 : ℤ)).map v₁) := by
              simp [s, t, Category.assoc, Functor.map_comp]
      _ = 0 := by rw [hmid]; simp
  have hts_shift : P.isoClosure.trW ((t ≫ s⟦(1 : ℤ)⟧')⟦(-1 : ℤ)⟧') := by
    simpa using (IsCompatibleWithShift.iff P.isoClosure.trW (t ≫ s⟦(1 : ℤ)⟧') (-1 : ℤ)).2 hts
  let Q₁' : D := ((shiftFunctor D (-1 : ℤ)).obj ((shiftFunctor D (1 : ℤ)).obj ((shiftFunctor D (1 : ℤ)).obj Q₁)))
  let Q₃' : D := ((shiftFunctor D (1 : ℤ)).obj ((shiftFunctor D (-1 : ℤ)).obj Q₃))
  have hzero_mem : P.isoClosure.trW (0 : Q₃⟦(-1 : ℤ)⟧ ⟶ Q₁') := by
    simpa [hzero_ts] using hts_shift
  have hBiprod : P.isoClosure (Q₁' ⊞ Q₃') :=
    biprod_shift_mem_of_zero_trW (P := P) hzero_mem
  have hQ₁_shift_raw : P.isoClosure Q₁' :=
    of_biprod_left P.isoClosure hBiprod
  have hQ₃_raw : P.isoClosure Q₃' :=
    of_biprod_right P.isoClosure hBiprod
  have hQ₁_shift : P.isoClosure (Q₁⟦(1 : ℤ)⟧) := by
    exact P.isoClosure.prop_of_iso
      ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by simp)).app (Q₁⟦(1 : ℤ)⟧))
      hQ₁_shift_raw
  have hQ₃ : P.isoClosure Q₃ := by
    exact P.isoClosure.prop_of_iso
      ((shiftFunctorCompIsoId D (-1 : ℤ) (1 : ℤ) (by simp)).app Q₃)
      hQ₃_raw
  have hQ₁ : P.isoClosure Q₁ := by
    have hQ₁_back : P.isoClosure (Q₁⟦(1 : ℤ)⟧⟦(-1 : ℤ)⟧) := by
      exact P.isoClosure.le_shift (-1 : ℤ) (Q₁⟦(1 : ℤ)⟧) hQ₁_shift
    -- Shift back from `Q₁⟦1⟧` to `Q₁`.
    exact P.isoClosure.prop_of_iso
      ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by simp)).app Q₁) hQ₁_back
  have hQ₂ : P.isoClosure Q₂ := by
    -- The first octahedral triangle now has its first two terms in `P.isoClosure`.
    exact P.isoClosure.ext_of_isTriangulatedClosed₃ o₁₂.triangle o₁₂.mem hQ₁ hQ₁₂
  -- The cone of `g` lies in `P.isoClosure`, so `g ∈ P.isoClosure.trW`.
  exact ((P.isoClosure).trW_iff_of_distinguished (Triangle.mk g v₂ w₂) hT₂).2 hQ₂

/-- Lemma 13.6.6: for a triangulated object property `P` on a triangulated category `D`, the
canonical Verdier morphism property attached to the strictly full triangulated subcategory
`P.isoClosure`, namely `P.isoClosure.trW`, is a saturated multiplicative system if and only if
`P.isoClosure` is stable under retracts. -/
@[stacks 05RG]
theorem isoClosure_trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts :
    IsSaturatedMultiplicativeSystem P.isoClosure.trW ↔ P.isoClosure.IsStableUnderRetracts := by
  constructor
  · intro hsat
    letI : IsSaturatedMultiplicativeSystem P.isoClosure.trW := hsat
    refine ⟨?_⟩
    intro X Y r hY
    obtain ⟨K, ⟨e⟩⟩ := retract_target_iso_biprod_right (X := X) (Y := Y) r
    have hBiprod : P.isoClosure (K ⊞ X) := by
      exact P.isoClosure.prop_of_iso e hY
    -- Reduce retract stability to the direct-summand statement proved above.
    simpa using isoClosure_of_biprod_right_of_saturated_trW (P := P) (X := K) (Y := X) hBiprod
  · intro hstable
    letI : P.isoClosure.IsStableUnderRetracts := hstable
    refine
      { toHasLeftCalculusOfFractions := inferInstance
        toHasRightCalculusOfFractions := inferInstance
        saturation := ?_ }
    intro W X Y Z f g h hfg hgh
    -- Route correction: the reverse direction follows the source octahedral proof literally,
    -- with the zero-composite step packaged by `biprod_shift_mem_of_zero_trW`.
    exact saturation_of_isoClosure_trW_of_retract_stable (P := P) f g h hfg hgh

/-- If `P` is already closed under isomorphisms, Lemma 13.6.6 specializes to retract stability of
`P` itself. -/
theorem trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts
    [P.IsClosedUnderIsomorphisms] :
    IsSaturatedMultiplicativeSystem P.trW ↔ P.IsStableUnderRetracts := by
  simpa only [P.trW_isoClosure, P.isoClosure_eq_self] using
    (isoClosure_trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts P)

/-- If `P` is stable under retracts, then the cone-defined morphism property `P.trW` is a
saturated multiplicative system. -/
theorem trW_isSaturatedMultiplicativeSystem [P.IsStableUnderRetracts] :
    IsSaturatedMultiplicativeSystem P.trW :=
  (trW_isSaturatedMultiplicativeSystem_iff_isStableUnderRetracts P).2 inferInstance

instance [P.IsStableUnderRetracts] : IsSaturatedMultiplicativeSystem P.trW :=
  trW_isSaturatedMultiplicativeSystem P

end

end CategoryTheory
