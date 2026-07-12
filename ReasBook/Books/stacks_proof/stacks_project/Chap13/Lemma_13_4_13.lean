import Mathlib
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open CategoryTheory.Pretriangulated.Opposite

noncomputable section

universe w v u

section

variable {I : Type w} {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.13:
- primary domain: distinguished triangles in a pretriangulated category, together with coproducts
  and the shift/coproduct comparison;
- sampled core/canonical declarations:
  `CategoryTheory.Pretriangulated.productTriangle`,
  `CategoryTheory.Pretriangulated.productTriangle_distinguished`,
  `CategoryTheory.Pretriangulated.triangleOpEquivalence`,
  `CategoryTheory.Pretriangulated.unop_distinguished`;
- best owner abstraction: the canonical core owner is `productTriangle`; the corresponding
  source-facing owner for this item should therefore be a project-level
  `CategoryTheory.Pretriangulated.coproductTriangle`. There is no exact upstream owner with the
  same minimal hypotheses: the opposite-category `productTriangle` route naturally lands in the
  auxiliary coproduct-of-shifts presentation and asks for coproducts of the shifted first terms.
  The source-facing owner here therefore stays local, with its distinguishedness theorem obtained
  as a `bridge/view` from the core product theorem in the opposite category, while the public
  target map stays in the intrinsic codomain `(∐ i, (T i).obj₁)⟦1⟧`;
- primitive-vs-derived split:
  primitive data are the family `T : I → Triangle D` and coproducts of the three object-families;
  derived API is the source-facing coproduct triangle together with its distinguishedness.

Source/core/bridge triage:
- `source-facing`: the owner `CategoryTheory.Pretriangulated.coproductTriangle T`;
- `core/canonical`: `productTriangle` and `productTriangle_distinguished`;
- `bridge/view`: opposite-category transport via `triangleOpEquivalence`, with
  `PreservesCoproduct.iso (shiftFunctor D (1 : ℤ))` only as the comparison between the auxiliary
  coproduct-of-shifts presentation and the intrinsic shifted coproduct. The source-facing owner is
  not a duplicate wheel of the core owner, but the minimal-hypothesis bridge attached to it. -/

/- (1) The canonical owner for a family of distinguished triangles is
`CategoryTheory.Pretriangulated.productTriangle`. -/
#check CategoryTheory.Pretriangulated.productTriangle

/- (2) If a family of objects of a pre-triangulated category admits a coproduct, then the shifted
coproduct is canonically identified with the coproduct of the shifted family by the comparison
isomorphism `Limits.PreservesCoproduct.iso (shiftFunctor D (1 : ℤ))`; this is a bridge from the
auxiliary coproduct-of-shifts presentation to the intrinsic codomain `(∐ i, X i)⟦1⟧`. -/
#check Limits.PreservesCoproduct.iso (shiftFunctor D (1 : ℤ))

/- (3) The product of a family of distinguished triangles is distinguished. This is the canonical
theorem `CategoryTheory.Pretriangulated.productTriangle_distinguished`. -/
#check CategoryTheory.Pretriangulated.productTriangle_distinguished

/- (4) Distinguishedness transports back from triangles in the opposite category via
`CategoryTheory.Pretriangulated.unop_distinguished`. -/
#check CategoryTheory.Pretriangulated.unop_distinguished

end

namespace CategoryTheory.Pretriangulated

section

variable {I : Type w} {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- The coproduct of a family of triangles. -/
@[simps!]
def coproductTriangle (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] : Triangle D :=
  Triangle.mk
    (Limits.Sigma.desc (fun i ↦ (T i).mor₁ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₂) i))
    (Limits.Sigma.desc (fun i ↦ (T i).mor₂ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₃) i))
    (Limits.Sigma.desc
      (fun i ↦ (T i).mor₃ ≫ (Limits.Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧'))

/-- Companion bridge to the source-facing Stacks formula: after transporting the last morphism of
`coproductTriangle T` across the canonical shift/coproduct comparison, one recovers the
coproduct-of-shifts map `⨿ Tᵢ.obj₃ ⟶ ⨿ Tᵢ.obj₁⟦1⟧`. -/
@[reassoc, simp]
theorem coproductTriangle_mor₃_comp_preservesCoproductIso_hom (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)] :
    (coproductTriangle T).mor₃ ≫
        (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)).hom =
      Limits.Sigma.desc
        (fun i ↦ (T i).mor₃ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₁⟦(1 : ℤ)⟧) i) := by
  apply Limits.Sigma.hom_ext
  intro i
  dsimp [coproductTriangle]
  rw [Limits.Sigma.ι_desc_assoc, Limits.Sigma.ι_desc]
  rw [Category.assoc]
  congr 1
  have hhom :
      (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)).hom =
        inv (sigmaComparison (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)))
  rw [hhom]
  exact
    map_ι_comp_inv_sigmaComparison (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁) i

end

section

variable {I : Type w} {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ]
  [Preadditive D] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Helper for Lemma 13.4.13: shifting a chosen coproduct yields a chosen coproduct of the shifted
family. -/
lemma hasCoproduct_shift (E : I → D) [HasCoproduct E] :
    HasCoproduct (fun i ↦ E i⟦(1 : ℤ)⟧) := by
  -- Transport the chosen coproduct cocone along the shift functor.
  let t :
      IsColimit
        (Cofan.mk ((∐ E)⟦(1 : ℤ)⟧) (fun i ↦ (Limits.Sigma.ι E i)⟦(1 : ℤ)⟧')) := by
    simpa using
      (Limits.isColimitOfHasCoproductOfPreservesColimit (shiftFunctor D (1 : ℤ)) E)
  exact ⟨⟨_, t⟩⟩

/-- Helper for Lemma 13.4.13: the shifted coproduct inclusion composed with the comparison map is
the shifted inclusion into the shifted coproduct. -/
lemma shifted_coproduct_inclusion_comp_sigmaComparison (E : I → D) [HasCoproduct E]
    [HasCoproduct (fun i ↦ E i⟦(1 : ℤ)⟧)] (i : I) :
    Limits.Sigma.ι (fun j ↦ E j⟦(1 : ℤ)⟧) i ≫ sigmaComparison (shiftFunctor D (1 : ℤ)) E =
      (shiftFunctor D (1 : ℤ)).map (Limits.Sigma.ι E i) := by
  let e := PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) E
  -- Cancel the comparison isomorphism and reduce to `map_ι_comp_inv_sigmaComparison`.
  apply (cancel_mono e.hom).1
  have h := map_ι_comp_inv_sigmaComparison (shiftFunctor D (1 : ℤ)) E i
  simpa [e, PreservesCoproduct.inv_hom, Category.assoc] using
    congrArg (fun k => k ≫ e.hom) h.symm

/-- Helper for Lemma 13.4.13: the shifted inclusion of a coproduct factor followed by the
canonical shift/coproduct comparison is the corresponding inclusion into the coproduct of shifts. -/
@[reassoc, simp]
lemma shift_coproduct_inclusion_comp_preservesCoproductIso_hom (E : I → D) [HasCoproduct E]
    [HasCoproduct (fun i ↦ E i⟦(1 : ℤ)⟧)] (i : I) :
    (Limits.Sigma.ι E i)⟦(1 : ℤ)⟧' ≫
        (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) E).hom =
      Limits.Sigma.ι (fun j ↦ E j⟦(1 : ℤ)⟧) i := by
  -- Rewrite the comparison as the inverse sigma comparison and use the standard coproduct formula.
  have hhom :
      (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) E).hom =
        inv (sigmaComparison (shiftFunctor D (1 : ℤ)) E) := by
    apply IsIso.eq_inv_of_hom_inv_id
    simpa [PreservesCoproduct.inv_hom] using
      (Iso.inv_hom_id (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) E))
  rw [hhom]
  exact map_ι_comp_inv_sigmaComparison (shiftFunctor D (1 : ℤ)) E i

/-- Helper for Lemma 13.4.13: the chosen coproduct inclusion becomes the chosen product
projection after passing to the opposite-side product comparison isomorphism. -/
@[reassoc, simp]
lemma coproduct_inclusion_comp_unop_opCoproductIsoProduct_hom (E : I → D) [HasCoproduct E]
    (i : I) :
    Limits.Sigma.ι E i ≫ (Limits.opCoproductIsoProduct E).unop.symm.hom =
      (Limits.Pi.π (fun j ↦ Opposite.op (E j)) i).unop := by
  -- Unop the standard opposite-coproduct/product identity.
  simpa using
    congrArg Quiver.Hom.unop (Limits.opCoproductIsoProduct_inv_comp_ι (Z := E) i)

/-- Helper for Lemma 13.4.13: the opposite-category image of the rotated family of triangles. -/
noncomputable abbrev rotatedOppositeTriangleFamily (T : I → Triangle D) : I → Triangle Dᵒᵖ :=
  fun i ↦ (triangleOpEquivalence D).functor.obj (Opposite.op ((T i).rotate))

/-- Helper for Lemma 13.4.13: after rotating and passing to the opposite category, shifting the
first object once in `Dᵒᵖ` recovers the opposite of the original first object, so the chosen
coproduct on the first terms supplies the needed chosen product. -/
lemma rotated_opposite_shifted_first_hasProduct (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] :
    HasProduct (fun i ↦ (rotatedOppositeTriangleFamily T i).obj₁⟦(1 : ℤ)⟧) := by
  -- Route correction: the blocker was the shifted-first `HasProduct` instance in `Dᵒᵖ`,
  -- so transport the product along the canonical opposite-shift identification back to
  -- the opposite of the original first family before invoking instance search.
  let e :
      ∀ i, (rotatedOppositeTriangleFamily T i).obj₁⟦(1 : ℤ)⟧ ≅ Opposite.op ((T i).obj₁) :=
    fun i ↦
      (shiftFunctorOpIso D (1 : ℤ) (-1 : ℤ) (by omega)).app
          (Opposite.op ((T i).obj₁⟦(1 : ℤ)⟧)) ≪≫
        ((shiftFunctorCompIsoId D (1 : ℤ) (-1 : ℤ) (by omega)).app ((T i).obj₁)).symm.op
  exact Limits.hasProduct_of_equiv_of_iso
    (fun i ↦ Opposite.op ((T i).obj₁))
    (fun i ↦ (rotatedOppositeTriangleFamily T i).obj₁⟦(1 : ℤ)⟧)
    (Equiv.refl I) e

/-- Helper for Lemma 13.4.13: the opposite-category image of the rotated coproduct triangle. -/
noncomputable abbrev rotated_coproduct_triangle_op (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] : Triangle Dᵒᵖ :=
  (triangleOpEquivalence D).functor.obj (Opposite.op ((coproductTriangle T).rotate))

/-- Helper for Lemma 13.4.13: the shifted coproduct desc map is the inverse of the canonical
shift/coproduct comparison. -/
lemma shifted_coproduct_desc_eq_preservesCoproductIso_inv (E : I → D) [HasCoproduct E]
    [HasCoproduct (fun i ↦ E i⟦(1 : ℤ)⟧)] :
    Limits.Sigma.desc (fun i ↦ (Limits.Sigma.ι E i)⟦(1 : ℤ)⟧') =
      (PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) E).inv := by
  let e := PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) E
  -- Cancel the comparison isomorphism and check the universal property on each coproduct factor.
  apply (cancel_mono e.hom).1
  apply Limits.Sigma.hom_ext
  intro i
  calc
    Limits.Sigma.ι (fun j ↦ E j⟦(1 : ℤ)⟧) i ≫
        Limits.Sigma.desc (fun i ↦ (Limits.Sigma.ι E i)⟦(1 : ℤ)⟧') ≫
          e.hom =
      (Limits.Sigma.ι E i)⟦(1 : ℤ)⟧' ≫ e.hom := by
        simpa [Category.assoc] using
          congrArg (fun k => k ≫ e.hom)
            (Limits.Sigma.ι_desc (p := fun i ↦ (Limits.Sigma.ι E i)⟦(1 : ℤ)⟧') i)
    _ = Limits.Sigma.ι (fun j ↦ E j⟦(1 : ℤ)⟧) i := by
      simpa [e] using shift_coproduct_inclusion_comp_preservesCoproductIso_hom (D := D) E i
    _ = Limits.Sigma.ι (fun j ↦ E j⟦(1 : ℤ)⟧) i ≫ e.inv ≫ e.hom := by
      simpa [Category.assoc] using
        (Iso.inv_hom_id_assoc e (Limits.Sigma.ι (fun j ↦ E j⟦(1 : ℤ)⟧) i)).symm

/-- Helper for Lemma 13.4.13: the coproduct triangle projects to the `i`-th triangle on the first
edge. -/
lemma coproductTriangle_component_comm₁ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (T i).mor₁ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₂) i =
      Limits.Sigma.ι (fun j ↦ (T j).obj₁) i ≫ (coproductTriangle T).mor₁ := by
  -- Evaluate the coproduct desc map on the `i`-th coproduct factor.
  simpa [coproductTriangle] using
    (Limits.Sigma.ι_desc
      (p := fun i ↦ (T i).mor₁ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₂) i) i).symm

/-- Helper for Lemma 13.4.13: the coproduct triangle projects to the `i`-th triangle on the
second edge. -/
lemma coproductTriangle_component_comm₂ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (T i).mor₂ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₃) i =
      Limits.Sigma.ι (fun j ↦ (T j).obj₂) i ≫ (coproductTriangle T).mor₂ := by
  -- Evaluate the coproduct desc map on the `i`-th coproduct factor.
  simpa [coproductTriangle] using
    (Limits.Sigma.ι_desc
      (p := fun i ↦ (T i).mor₂ ≫ Limits.Sigma.ι (fun j ↦ (T j).obj₃) i) i).symm

/-- Helper for Lemma 13.4.13: the coproduct triangle projects to the `i`-th triangle on the third
edge. -/
lemma coproductTriangle_component_comm₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (T i).mor₃ ≫ (Limits.Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧' =
      Limits.Sigma.ι (fun j ↦ (T j).obj₃) i ≫ (coproductTriangle T).mor₃ := by
  -- Evaluate the coproduct desc map on the `i`-th coproduct factor.
  simpa [coproductTriangle] using
    (Limits.Sigma.ι_desc
      (p := fun i ↦ (T i).mor₃ ≫ (Limits.Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧') i).symm

/-- Helper for Lemma 13.4.13: the coproduct triangle maps canonically to each triangle in the
family. -/
noncomputable def coproductTriangle_component (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    T i ⟶ coproductTriangle T :=
  Triangle.homMk _ _
    (Limits.Sigma.ι (fun j ↦ (T j).obj₁) i)
    (Limits.Sigma.ι (fun j ↦ (T j).obj₂) i)
    (Limits.Sigma.ι (fun j ↦ (T j).obj₃) i)
    (coproductTriangle_component_comm₁ (D := D) (T := T) i)
    (coproductTriangle_component_comm₂ (D := D) (T := T) i)
    (coproductTriangle_component_comm₃ (D := D) (T := T) i)

/-- Helper for Lemma 13.4.13: the third square for the comparison from the rotated coproduct
triangle to the `i`-th rotated opposite triangle. -/
lemma rotate_coproduct_triangle_op_component_comm₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    (rotated_coproduct_triangle_op (D := D) T).mor₃ ≫
        ((((Limits.Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧').op)⟦(1 : ℤ)⟧') =
      (Limits.Sigma.ι (fun j ↦ (T j).obj₂) i).op ≫
        (rotatedOppositeTriangleFamily (D := D) T i).mor₃ := by
  -- Route correction: package the raw coproduct projection as a triangle morphism in `D`, rotate
  -- it there, and let `triangleOpEquivalence` provide the third square in `Dᵒᵖ`.
  let φ : (T i).rotate ⟶ (coproductTriangle T).rotate :=
    (CategoryTheory.Pretriangulated.rotate D).map
      (coproductTriangle_component (D := D) (T := T) i)
  simpa [φ, rotated_coproduct_triangle_op, rotatedOppositeTriangleFamily,
    coproductTriangle_component] using
    (((triangleOpEquivalence D).functor.map (Opposite.op φ)).comm₃)

/-- Helper for Lemma 13.4.13: the component comparison from the rotated coproduct triangle in
`Dᵒᵖ` to the `i`-th rotated opposite triangle. -/
noncomputable def rotate_coproduct_triangle_op_component (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] (i : I) :
    rotated_coproduct_triangle_op (D := D) T ⟶ rotatedOppositeTriangleFamily (D := D) T i :=
  (triangleOpEquivalence D).functor.map <|
    Opposite.op <|
      (CategoryTheory.Pretriangulated.rotate D).map
        (coproductTriangle_component (D := D) (T := T) i)

/-- Helper for Lemma 13.4.13: the lifted comparison from the rotated coproduct triangle in
`Dᵒᵖ` to the product of the rotated opposite family. -/
noncomputable def rotate_coproduct_triangle_op_lift (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₂)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₃)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁⟦(1 : ℤ)⟧)] :
    rotated_coproduct_triangle_op (D := D) T ⟶
      productTriangle (rotatedOppositeTriangleFamily (D := D) T) :=
  productTriangle.lift _ (rotate_coproduct_triangle_op_component (D := D) (T := T))

/-- Helper for Lemma 13.4.13: the second and third components of the lifted comparison are the
standard opposite coproduct/product comparison maps. -/
lemma rotate_coproduct_triangle_op_lift_hom₂_hom₃ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₂)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₃)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁⟦(1 : ℤ)⟧)] :
    (rotate_coproduct_triangle_op_lift (D := D) (T := T)).hom₂ =
        (Limits.opCoproductIsoProduct (fun i ↦ (T i).obj₃)).hom ∧
      (rotate_coproduct_triangle_op_lift (D := D) (T := T)).hom₃ =
        (Limits.opCoproductIsoProduct (fun i ↦ (T i).obj₂)).hom := by
  constructor
  · -- Check the second component projectionwise against the universal property of the product.
    apply Limits.Pi.hom_ext
    intro i
    dsimp [rotate_coproduct_triangle_op_lift, rotate_coproduct_triangle_op_component]
    symm
    rw [Limits.Pi.lift_π]
    change
      (Limits.opCoproductIsoProduct (fun i ↦ (T i).obj₃)).hom ≫
          Limits.Pi.π (fun j ↦ Opposite.op ((T j).obj₃)) i =
        (Limits.Sigma.ι (fun j ↦ (T j).obj₃) i).op
    exact Limits.opCoproductIsoProduct_hom_comp_π (Z := fun i ↦ (T i).obj₃) i
  · -- The third component is the same calculation for the coproduct of the second objects.
    apply Limits.Pi.hom_ext
    intro i
    dsimp [rotate_coproduct_triangle_op_lift, rotate_coproduct_triangle_op_component]
    symm
    rw [Limits.Pi.lift_π]
    change
      (Limits.opCoproductIsoProduct (fun i ↦ (T i).obj₂)).hom ≫
          Limits.Pi.π (fun j ↦ Opposite.op ((T j).obj₂)) i =
        (Limits.Sigma.ι (fun j ↦ (T j).obj₂) i).op
    exact Limits.opCoproductIsoProduct_hom_comp_π (Z := fun i ↦ (T i).obj₂) i

/-- Helper for Lemma 13.4.13: the first component of the lifted comparison is the composite of
the shift/coproduct comparison with the opposite coproduct/product comparison. -/
lemma rotate_coproduct_triangle_op_lift_hom₁ (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₂)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₃)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁⟦(1 : ℤ)⟧)] :
    (rotate_coproduct_triangle_op_lift (D := D) (T := T)).hom₁ =
      ((PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)).inv).op ≫
        (Limits.opCoproductIsoProduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)).hom := by
  -- Rewrite the lifted map as the opposite of the shifted coproduct desc map, then use the
  -- canonical opposite coproduct/product comparison.
  simpa [rotate_coproduct_triangle_op_lift, rotate_coproduct_triangle_op_component,
    coproductTriangle_component, rotatedOppositeTriangleFamily,
    shifted_coproduct_desc_eq_preservesCoproductIso_inv (D := D) (E := fun i ↦ (T i).obj₁)] using
    (Limits.desc_op_comp_opCoproductIsoProduct_hom
      (Z := fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)
      (π := fun i ↦ (Limits.Sigma.ι (fun j ↦ (T j).obj₁) i)⟦(1 : ℤ)⟧')).symm

/-- Helper for Lemma 13.4.13: the lifted comparison is an isomorphism because its three object
maps are the canonical comparison isomorphisms. -/
lemma rotate_coproduct_triangle_op_lift_isIso (T : I → Triangle D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] [HasCoproduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₂)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₃)]
    [HasProduct (fun i ↦ (rotatedOppositeTriangleFamily (D := D) T i).obj₁⟦(1 : ℤ)⟧)] :
    IsIso (rotate_coproduct_triangle_op_lift (D := D) (T := T)) := by
  let ψ := rotate_coproduct_triangle_op_lift (D := D) (T := T)
  have h₂₃ := rotate_coproduct_triangle_op_lift_hom₂_hom₃ (D := D) (T := T)
  have h₁ := rotate_coproduct_triangle_op_lift_hom₁ (D := D) (T := T)
  -- Each component is one of the canonical comparison isomorphisms.
  have h₁iso : IsIso ψ.hom₁ := by
    rw [h₁]
    have hshift :
        IsIso (((PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)).inv).op) := by
      change IsIso (((PreservesCoproduct.iso (shiftFunctor D (1 : ℤ)) (fun i ↦ (T i).obj₁)).symm.op).hom)
      infer_instance
    letI : IsIso ((Limits.opCoproductIsoProduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧)).hom) := by
      infer_instance
    exact IsIso.comp_isIso' hshift inferInstance
  have h₂iso : IsIso ψ.hom₂ := by
    rw [h₂₃.1]
    infer_instance
  have h₃iso : IsIso ψ.hom₃ := by
    rw [h₂₃.2]
    infer_instance
  -- The triangle morphism is therefore an isomorphism componentwise.
  simpa [ψ] using Triangle.isIso_of_isIsos ψ h₁iso h₂iso h₃iso

-- Proof sketch: dualize the product argument for the core owner `productTriangle`, use the
-- universal property of the coproduct and the co-special form of Remark 13.4.4 to identify the
-- resulting source-facing owner `coproductTriangle T`, and transport distinguishedness back from
-- the opposite category.
/-- Lemma 13.4.13: clause (4) says that for a family of distinguished triangles in a
pre-triangulated category, if the coproducts of the first, second, and third terms exist, then
the coproduct triangle is distinguished. -/
@[stacks 0CRG]
lemma coproductTriangle_distinguished (T : I → Triangle D)
    (hT : ∀ i, T i ∈ distTriang D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] :
    coproductTriangle T ∈ distTriang D := by
  letI : HasCoproduct (fun i ↦ (T i).obj₁⟦(1 : ℤ)⟧) := hasCoproduct_shift (fun i ↦ (T i).obj₁)
  let R : I → Triangle Dᵒᵖ := rotatedOppositeTriangleFamily T
  letI : HasProduct (fun i ↦ (R i).obj₁) := by
    -- The first objects of `R` are the opposites of the shifted first objects of `T`.
    change HasProduct (fun i ↦ Opposite.op ((T i).obj₁⟦(1 : ℤ)⟧))
    infer_instance
  letI : HasProduct (fun i ↦ (R i).obj₂) := by
    -- The second objects of `R` are the opposites of the third objects of `T`.
    change HasProduct (fun i ↦ Opposite.op ((T i).obj₃))
    infer_instance
  letI : HasProduct (fun i ↦ (R i).obj₃) := by
    -- The third objects of `R` are the opposites of the second objects of `T`.
    change HasProduct (fun i ↦ Opposite.op ((T i).obj₂))
    infer_instance
  letI : HasProduct (fun i ↦ (R i).obj₁⟦(1 : ℤ)⟧) := by
    simpa [R] using rotated_opposite_shifted_first_hasProduct T
  have hR : productTriangle R ∈ distTriang Dᵒᵖ := by
    -- The source route first proves distinguishedness for the opposite-category product triangle.
    exact productTriangle_distinguished R
      (fun i ↦ op_distinguished ((T i).rotate) (rot_of_distTriang _ (hT i)))
  -- Follow the source proof: pass to the opposite-category product triangle of the rotated family,
  -- transport distinguishedness back to `D`, and compare that triangle with the rotated coproduct.
  have hrotate : (coproductTriangle T).rotate ∈ distTriang D := by
    let A : Triangle Dᵒᵖ := rotated_coproduct_triangle_op (D := D) T
    let ψ : A ⟶ productTriangle R := rotate_coproduct_triangle_op_lift (D := D) (T := T)
    -- Route correction: the old stalled route tried to package the global triangle isomorphism
    -- first. The repaired route builds the component maps `A ⟶ R i`, then packages them as `ψ`.
    have hψ : IsIso ψ := by
      simpa [A, ψ, R] using rotate_coproduct_triangle_op_lift_isIso (D := D) (T := T)
    let eop : A ≅ productTriangle R := asIso ψ
    have hA : A ∈ distTriang Dᵒᵖ := by
      -- Transport distinguishedness back along the comparison isomorphism in `Dᵒᵖ`.
      exact (distinguished_iff_of_iso eop).2 hR
    have hAu : ((triangleOpEquivalence D).inverse.obj A).unop ∈ distTriang D := by
      -- Return to the original category using the opposite pretriangulated structure.
      exact unop_distinguished A hA
    let eunit :
        (coproductTriangle T).rotate ≅ ((triangleOpEquivalence D).inverse.obj A).unop :=
      (((triangleOpEquivalence D).unitIso.app (Opposite.op ((coproductTriangle T).rotate))).unop).symm
    -- The unit isomorphism identifies the unopped opposite-category model with the rotated
    -- coproduct triangle we want.
    exact (distinguished_iff_of_iso eunit).2 hAu
  -- Rotate back once to recover the original coproduct triangle.
  exact (rotate_distinguished_triangle (coproductTriangle T)).mpr hrotate

end

end CategoryTheory.Pretriangulated

end
