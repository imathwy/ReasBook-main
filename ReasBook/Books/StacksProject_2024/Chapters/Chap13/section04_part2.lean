import Mathlib
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_13_4_12 (from Chap13) -/
universe v u

namespace CategoryTheory

open CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling:
- primary domain: morphisms in a pretriangulated preadditive category, viewed up to isomorphism in
  the arrow category and compared with the canonical biproduct projection/inclusion model;
- relevant upstream owner declarations in this domain:
  `CategoryTheory.Arrow`,
  `Arrow.isoMk`,
  `CategoryTheory.IsIsomorphic`,
  `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel`,
  `biprod.isKernelSndKernelFork` / `biprod.isCokernelInlCokernelFork`;
- best owner abstraction: `Arrow D` is the canonical owner for saying that a morphism is
  isomorphic to another morphism, and `IsIsomorphic` is the canonical Prop-level owner for
  existence of such an isomorphism; the textbook decomposition should be expressed there rather
  than by primitive object isomorphisms plus a raw composite equality or a raw `Nonempty` wrapper;
- primitive data vs derived API: the primitive ingredients are `HasKernel f`, `HasCokernel f`,
  and the standard arrow `biprod.snd ≫ biprod.inl`; the explicit domain/codomain isomorphisms are
  derived data packaged by an arrow-category isomorphism, whose existence is then recorded by the
  Prop-level owner `IsIsomorphic`.

This file is therefore `source-facing`: it keeps the Stacks equivalence, but refines clause `(3)`
to the canonical arrow-category owner instead of a parallel low-level encoding.
-/

-- Proof sketch: for `(3) → (1), (2)`, transport kernels and cokernels along the displayed
-- isomorphisms and use the standard kernel of `biprod.snd` and cokernel of `biprod.inl`. For
-- `(1) → (3)`, a morphism with kernel is mono after restricting away the kernel summand, hence
-- split mono in a pretriangulated category; combine the kernel splitting and
-- `isBilimitBinaryBiconeOfIsSplitMonoOfCokernel` for the resulting cokernel decomposition. The
-- implication `(2) → (3)` is dual.
/-- Lemma 13.4.12: for a morphism `f : X ⟶ Y` in a pre-triangulated category, the following are
equivalent: `f` has a kernel, `f` has a cokernel, and `f` is isomorphic to a composition
`K ⊞ Z ⟶ Z ⟶ Z ⊞ Q` given by a projection followed by a coprojection. The isomorphism is
expressed in the canonical arrow category `Arrow D`, using the Prop-level owner
`IsIsomorphic`. -/
theorem tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection {X Y : D}
    (f : X ⟶ Y) :
    List.TFAE
      [ HasKernel f
      , HasCokernel f
      , ∃ K Z Q : D,
          IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) ] := sorry

/-- In a pre-triangulated category, a morphism has a kernel if and only if it has a cokernel. -/
theorem hasKernel_iff_hasCokernel_of_pretriangulated {X Y : D} (f : X ⟶ Y) :
    HasKernel f ↔ HasCokernel f :=
  (tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection f).out 0 1

/-- In a pre-triangulated category, a morphism has a kernel if and only if it is isomorphic in the
arrow category to a projection followed by a coprojection. -/
theorem hasKernel_iff_isomorphicTo_projection_then_coprojection {X Y : D} (f : X ⟶ Y) :
    HasKernel f ↔
      ∃ K Z Q : D,
        IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) :=
  (tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection f).out 0 2

/-- In a pre-triangulated category, a morphism has a cokernel if and only if it is isomorphic in
the arrow category to a projection followed by a coprojection. -/
theorem hasCokernel_iff_isomorphicTo_projection_then_coprojection {X Y : D} (f : X ⟶ Y) :
    HasCokernel f ↔
      ∃ K Z Q : D,
        IsIsomorphic (Arrow.mk f) (Arrow.mk (biprod.snd ≫ biprod.inl : K ⊞ Z ⟶ Z ⊞ Q)) :=
  (tfae_hasKernel_hasCokernel_isomorphicTo_projection_then_coprojection f).out 1 2

end CategoryTheory

/-! ### Lemma_13_4_13 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

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

-- Proof sketch: dualize the product argument for the core owner `productTriangle`, use the
-- universal property of the coproduct and the co-special form of Remark 13.4.4 to identify the
-- resulting source-facing owner `coproductTriangle T`, and transport distinguishedness back from
-- the opposite category.
/-- Lemma 13.4.13: clause (4) says that for a family of distinguished triangles in a
pre-triangulated category, if the coproducts of the first, second, and third terms exist, then
the coproduct triangle is distinguished. -/
lemma coproductTriangle_distinguished (T : I → Triangle D)
    (hT : ∀ i, T i ∈ distTriang D)
    [HasCoproduct (fun i ↦ (T i).obj₁)] [HasCoproduct (fun i ↦ (T i).obj₂)]
    [HasCoproduct (fun i ↦ (T i).obj₃)] :
    coproductTriangle T ∈ distTriang D := sorry

end

end CategoryTheory.Pretriangulated

end

/-! ### Lemma_13_4_14 (from Chap13) -/
universe v u

namespace CategoryTheory

open CategoryTheory.Arrow
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- Domain-style sampling for Lemma 13.4.14:
- primary domain: pretriangulated categories, distinguished triangles, and the canonical owner
  notion `IsIdempotentComplete D`;
- sampled owner declarations:
  `IsIdempotentComplete`,
  `isIdempotentComplete_of_countableProducts_of_splitEpi_kernels`,
  `isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels`,
  `exists_iso_binaryBiproduct_of_distTriang`,
  `IsKernel.ofIso`,
  `IsCokernel.ofIso`;
- best owner abstraction: the public target of the Stacks lemma is the canonical owner
  `IsIdempotentComplete D`, while the pretriangulated input is expressed through the distinguished
  triangle API and the standard biproduct kernels/cokernels;
- primitive data vs derived API: the primitive data are only the ambient pretriangulated category
  and the countable product/coproduct hypotheses. The kernels of split epis and cokernels of split
  monos are derived by identifying such morphisms with the canonical biproduct projection/inclusion
  and transporting the standard kernel/cokernel along an arrow isomorphism.

Source/core/bridge triage:
- `source-facing`: the two implications recorded in Lemma 13.4.14;
- `core/canonical`: `IsIdempotentComplete D`;
- `bridge/view`: `Lemma_12_4_3` together with the pretriangulated biproduct splitting of a
  distinguished triangle whose remaining morphism vanishes.
-/

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private theorem hasKernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasKernel g] : HasKernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  refine ⟨⟨KernelFork.ofι (kernel.ι g ≫ eX.inv) ?_, ?_⟩⟩
  · show (kernel.ι g ≫ eX.inv) ≫ f = 0
    calc
      (kernel.ι g ≫ eX.inv) ≫ f = kernel.ι g ≫ (g ≫ eY.inv) := by
        simpa [eX, eY] using congrArg (kernel.ι g ≫ ·) (Arrow.w e.inv)
      _ = 0 := by simp
  · exact IsKernel.ofIso g (kernelIsKernel g)
      (KernelFork.ofι (kernel.ι g ≫ eX.inv) (by
        show (kernel.ι g ≫ eX.inv) ≫ f = 0
        calc
          (kernel.ι g ≫ eX.inv) ≫ f = kernel.ι g ≫ (g ≫ eY.inv) := by
            simpa [eX, eY] using congrArg (kernel.ι g ≫ ·) (Arrow.w e.inv)
          _ = 0 := by simp))
      eX.symm eY.symm (Iso.refl _) (by simpa [eX, eY] using Arrow.w e.inv) (by simp)

omit [HasZeroObject D] [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] in
private theorem hasCokernel_of_arrow_iso {X Y X' Y' : D} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (e : Arrow.mk f ≅ Arrow.mk g) [HasCokernel g] : HasCokernel f := by
  let eX : X ≅ X' := Arrow.leftFunc.mapIso e
  let eY : Y ≅ Y' := Arrow.rightFunc.mapIso e
  refine ⟨⟨CokernelCofork.ofπ (eY.hom ≫ cokernel.π g) ?_, ?_⟩⟩
  · show f ≫ (eY.hom ≫ cokernel.π g) = 0
    calc
      f ≫ (eY.hom ≫ cokernel.π g) = eX.hom ≫ (g ≫ cokernel.π g) := by
        simpa [eX, eY] using congrArg (· ≫ cokernel.π g) (Arrow.w e.hom).symm
      _ = 0 := by simp
  · exact IsCokernel.ofIso g (cokernelIsCokernel g)
      (CokernelCofork.ofπ (eY.hom ≫ cokernel.π g) (by
        show f ≫ (eY.hom ≫ cokernel.π g) = 0
        calc
          f ≫ (eY.hom ≫ cokernel.π g) = eX.hom ≫ (g ≫ cokernel.π g) := by
            simpa [eX, eY] using congrArg (· ≫ cokernel.π g) (Arrow.w e.hom).symm
          _ = 0 := by simp))
      eX.symm eY.symm (Iso.refl _) (by simpa [eX, eY] using Arrow.w e.inv) (by simp)

-- Proof sketch: apply the owner theorem
-- `isIdempotentComplete_of_countableProducts_of_splitEpi_kernels`. In a pretriangulated category,
-- every split epi extends to a distinguished triangle whose third morphism vanishes, hence the
-- split theorem `exists_iso_binaryBiproduct_of_distTriang` identifies it with `biprod.snd`; the
-- standard kernel of `biprod.snd` then transports back along the resulting arrow isomorphism.
/-- Lemma 13.4.14 (1): in a pre-triangulated category with countable products, idempotents split.
-/
theorem pretriangulated_isIdempotentComplete_of_countableProducts [HasCountableProducts D] :
    IsIdempotentComplete D := by
  refine isIdempotentComplete_of_countableProducts_of_splitEpi_kernels ?_
  intro X Y f _
  obtain ⟨K, i, h, hT⟩ := distinguished_cocone_triangle₁ f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_epi₂ _ hT (inferInstance : Epi f)
  obtain ⟨e, _, hf⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk i f h) hT hzero
  let e' : Arrow.mk f ≅ Arrow.mk (biprod.snd : K ⊞ Y ⟶ Y) :=
    Arrow.isoMk e (Iso.refl _) (by simpa using hf.symm)
  letI : HasKernel (biprod.snd : K ⊞ Y ⟶ Y) := inferInstance
  exact hasKernel_of_arrow_iso e'

-- Proof sketch: argue dually with
-- `isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels`. A split mono extends to a
-- distinguished triangle whose first morphism vanishes, so the same pretriangulated splitting
-- theorem identifies it with `biprod.inl`; the standard cokernel of `biprod.inl` transports back
-- along the induced arrow isomorphism.
/-- Lemma 13.4.14 (2): in a pre-triangulated category with countable coproducts, idempotents
split. -/
theorem pretriangulated_isIdempotentComplete_of_countableCoproducts [HasCountableCoproducts D] :
    IsIdempotentComplete D := by
  refine isIdempotentComplete_of_countableCoproducts_of_splitMono_cokernels ?_
  intro X Y f _
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  have hzero : h = 0 := Triangle.mor₃_eq_zero_of_mono₁ _ hT (inferInstance : Mono f)
  obtain ⟨e, hf, _⟩ := exists_iso_binaryBiproduct_of_distTriang (Triangle.mk f g h) hT hzero
  let e' : Arrow.mk f ≅ Arrow.mk (biprod.inl : X ⟶ X ⊞ Z) :=
    Arrow.isoMk (Iso.refl _) e (by simpa using hf.symm)
  letI : HasCokernel (biprod.inl : X ⟶ X ⊞ Z) := inferInstance
  exact hasCokernel_of_arrow_iso e'

end CategoryTheory

/-! ### Lemma_13_4_15 (from Chap13) -/
namespace CategoryTheory

/- Domain-style sampling:
- primary domain: triangulated categories, specifically the octahedron axiom and its reduction to
  a convenient isomorphic composable pair;
- sampled owner declarations in this domain:
  `Pretriangulated`,
  `IsTriangulated`,
  `Octahedron.ofIso`,
  `IsTriangulated.mk'`;
- best owner abstraction: the constructor `IsTriangulated.mk'`, which directly packages the source
  reduction principle for TR4 into the canonical owner `IsTriangulated`;
- primitive data vs derived API: the primitive data is exactly the reduced octahedron witness for
  an isomorphic replacement of a composable pair. The ambient triangulated-category structure is
  then derived by the owner constructor, so no local wrapper or duplicate reformulation is needed.

Source/core/bridge triage:
- `source-facing`: the Stacks reduction principle for proving TR4 after replacing a composable pair
  by an isomorphic one carrying distinguished triangles;
- `core/canonical`: `IsTriangulated`;
- `bridge/view`: `Octahedron.ofIso`, internalized by the constructor `IsTriangulated.mk'`.
-/

/- Lemma 13.4.15: to prove TR4 for a pre-triangulated category, it suffices to verify the
octahedron axiom after replacing any composable pair of morphisms by an isomorphic pair
`X' ⟶ Y' ⟶ Z'` for which the triangles on `f'`, `g'`, and `g' ≫ f'` are distinguished. This
reduction principle is exactly the canonical constructor `CategoryTheory.IsTriangulated.mk'`. -/
recall IsTriangulated.mk'

end CategoryTheory

/-! ### Lemma_13_4_16 (from Chap13) -/
open CategoryTheory
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  (P : ObjectProperty C)

/- Domain-style sampling for Lemma 13.4.16:
- primary domain: triangulated object properties in a pretriangulated category and the associated
  Verdier morphism property `P.trW`;
- sampled owner declarations:
  `ObjectProperty.IsTriangulated`,
  `ObjectProperty.IsTriangulated.toContainsZero`,
  `ObjectProperty.IsTriangulated.toIsStableUnderShift`,
  `ObjectProperty.trW`;
- best owner abstraction: `ObjectProperty.IsTriangulated P`;
- primitive data: the owner fields `P.ContainsZero`, `P.IsStableUnderShift ℤ`, and
  `P.IsTriangulatedClosed₂`;
- derived API: the companion closure clauses `Closed₁` and `Closed₃`, and the cone morphism
  property `P.trW`;
- source/core/bridge triage:
  `source-facing`: the Stacks characterization of a triangulated object property by zero, shift,
    and cone closure for morphisms between objects of `P`;
  `core/canonical`: `ObjectProperty.IsTriangulated`;
  `bridge/view`: the ambient-category reformulation of the cone clause in terms of `P.trW`.

The two implication clauses that are already exact fields of `ObjectProperty.IsTriangulated`
should therefore be direct recalls, not new theorem wrappers, while the converse direction remains
as a bridge theorem. -/

namespace ObjectProperty

/- Lemma 13.4.16 (1): a triangulated object property contains the zero object. This is the
`toContainsZero` field of the canonical owner `ObjectProperty.IsTriangulated`. -/
recall IsTriangulated.toContainsZero

/- Lemma 13.4.16 (2): a triangulated object property is stable under the shift functor. This is
the `toIsStableUnderShift` field of `ObjectProperty.IsTriangulated`. -/
recall IsTriangulated.toIsStableUnderShift

/-- Lemma 13.4.16 (3): if `P` is triangulated, then every morphism between objects of `P` lies in
the Verdier morphism property `P.trW`. -/
theorem trW_of_isTriangulated
    (hTriangulated : P.IsTriangulated)
    {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.trW f := by
  letI := hTriangulated
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  simpa [P.trW_isoClosure] using
    trW.mk P.isoClosure hT (P.ext_of_isTriangulatedClosed₃' _ hT hX hY)

/-- Lemma 13.4.16 (4): if `P` contains zero, is stable under shifts, and every morphism between
objects of `P` lies in `P.trW`, then `P` is triangulated. -/
theorem isTriangulated_of_containsZero_of_isStableUnderShift_of_trW
    (hZero : P.ContainsZero) (hShift : P.IsStableUnderShift ℤ)
    (hW : ∀ {X Y : C} (f : X ⟶ Y) (_ : P X) (_ : P Y), P.trW f) :
    P.IsTriangulated where
  toContainsZero := hZero
  toIsStableUnderShift := hShift
  toIsTriangulatedClosed₂ := by
    letI := hShift
    refine ⟨fun T hT h₁ h₃ ↦ ?_⟩
    have hmem : P.isoClosure.trW T.mor₃ := by
      simpa [P.trW_isoClosure] using hW T.mor₃ h₃ (P.le_shift 1 _ h₁)
    simpa using
      ((P.isoClosure).trW_iff_of_distinguished' T.rotate (rot_of_distTriang _ hT)).1 hmem

end ObjectProperty

end

end CategoryTheory

/-! ### Lemma_13_4_17 (from Chap13) -/
namespace CategoryTheory

universe v₁ v₂ u₁ u₂

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type u₂} [Category.{v₂} D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/- Domain-style sampling for Lemma 13.4.17:
- primary domain: exact functors between pretriangulated categories and their additive structure;
- sampled owner declarations:
  `Functor.IsTriangulated`,
  `Functor.IsTriangulated.map_distinguished`,
  the upstream owner instance `[F.IsTriangulated] : F.Additive`,
  `Adjunction.isTriangulated_rightAdjoint` as a downstream consumer of the same exact-functor
    abstraction;
- best owner abstraction: `Functor.IsTriangulated`;
- primitive data: the shift-compatibility structure `[F.CommShift ℤ]` and the distinguished-triangle
  preservation structure `[F.IsTriangulated]`;
- derived API: the additive structure on `F`, provided canonically by the owner instance rather
  than by a separate local theorem;
- source/core/bridge triage:
  `source-facing`: the Stacks assertion that an exact functor is additive;
  `core/canonical`: the mathlib owner instance `[F.IsTriangulated] : F.Additive`;
  `bridge/view`: the recall below, specialized to exact functors encoded by
    `Functor.CommShift ℤ` and `Functor.IsTriangulated`.

This item is therefore a pure recall of the canonical owner consequence, not a new theorem-shaped
API. -/

variable (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/- Lemma 13.4.17: an exact functor of pretriangulated categories, encoded by
`F.CommShift ℤ` and `F.IsTriangulated`, is additive. This is the canonical upstream instance
attached to `Functor.IsTriangulated`. -/
#check (inferInstance : F.Additive)

end

end CategoryTheory

/-! ### Lemma_13_4_18 (from Chap13) -/
universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Limits

section

variable {D : Type u₁} {D' : Type u₂} [Category.{v₁} D] [Category.{v₂} D']
  [HasZeroObject D] [HasZeroObject D'] [HasShift D ℤ] [HasShift D' ℤ]
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D' n)]
  [Pretriangulated D] [Pretriangulated D']
  (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] [F.Full] [F.Faithful]

/- Domain-style sampling for Lemma 13.4.18:
- primary domain: fully faithful exact functors between pretriangulated categories and their
  action on distinguished triangles;
- sampled core/canonical declarations in this domain:
  `Functor.IsTriangulated`,
  `Functor.map_distinguished`,
  `Functor.map_distinguished_iff`,
  `Functor.mapTriangle`;
- best owner abstraction: Definition 13.3.3 already fixes exactness as the owner pair
  `[F.CommShift ℤ] [F.IsTriangulated]`, and for a full faithful functor the precise reflection
  statement is already the canonical theorem `Functor.map_distinguished_iff`;
- primitive data: the functor `F`, its exactness owners, and the full/faithful hypotheses;
- derived API: the equivalence between distinguishedness of `T` and of `F.mapTriangle.obj T`.

Source/core/bridge triage:
- `source-facing`: the Stacks lemma that a fully faithful exact functor reflects distinguished
  triangles;
- `core/canonical`: `Functor.map_distinguished_iff`;
- `bridge/view`: the forward implication `Functor.map_distinguished` and the mapped triangle
  `F.mapTriangle.obj T`.

There is no chapter-local owner to keep here: the file should reuse the upstream theorem directly
rather than repackage it as a parallel local lemma. -/

/- Lemma 13.4.18: if `F : D ⥤ D'` is a fully faithful exact functor between pre-triangulated
categories, then a triangle `T` of `D` is distinguished if and only if its image
`F.mapTriangle.obj T`, corresponding to the tuple `(F(X), F(Y), F(Z), F(f), F(g), F(h))`, is
distinguished in `D'`. This is exactly the canonical theorem
`CategoryTheory.Functor.map_distinguished_iff`. -/
recall Functor.map_distinguished_iff

end

end CategoryTheory

/-! ### Lemma_13_4_19 (from Chap13) -/
universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

/- Domain-style sampling for Lemma 13.4.19:
- primary domain: composition of exact functors between pretriangulated categories;
- sampled owner declarations:
  `Functor.CommShift`,
  `Functor.IsTriangulated`,
  `Functor.mapTriangleCompIso`,
  the composite instance `[F.IsTriangulated] [G.IsTriangulated] : (F ⋙ G).IsTriangulated`;
- best owner abstraction: exactness is already owned by the pair
  `Functor.CommShift ℤ` and `Functor.IsTriangulated`, so this lemma should be a direct recall of
  the composite owner instances, not a parallel local wrapper.

Primitive data vs. derived API:
- primitive data: the functors together with their `CommShift` structures;
- derived exactness API: the `IsTriangulated` owner on the composite functor.

Source/core/bridge triage:
- `source-facing`: exact functors compose;
- `core/canonical`: `Functor.CommShift` and `Functor.IsTriangulated`;
- `bridge/view`: the anonymous composite instances provided by the shift and triangulated functor
  APIs.
-/

section CommShift

variable {D : Type u₁} {D' : Type u₂} {D'' : Type u₃}
  [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} D'']
  [HasShift D ℤ] [HasShift D' ℤ] [HasShift D'' ℤ]
  (F : D ⥤ D') (F' : D' ⥤ D'')
  [F.CommShift ℤ] [F'.CommShift ℤ]

/- Lemma 13.4.19, primitive owner layer: the composite of shift-compatible functors is again
shift-compatible. -/
#check (inferInstance : (F ⋙ F').CommShift ℤ)

end CommShift

section IsTriangulated

variable {D : Type u₁} {D' : Type u₂} {D'' : Type u₃}
  [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} D'']
  [HasZeroObject D] [HasZeroObject D'] [HasZeroObject D'']
  [HasShift D ℤ] [HasShift D' ℤ] [HasShift D'' ℤ]
  [Preadditive D] [Preadditive D'] [Preadditive D'']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [∀ n : ℤ, (shiftFunctor D'' n).Additive]
  [Pretriangulated D] [Pretriangulated D'] [Pretriangulated D'']
  (F : D ⥤ D') (F' : D' ⥤ D'')
  [F.CommShift ℤ] [F'.CommShift ℤ] [F.IsTriangulated] [F'.IsTriangulated]

/- Lemma 13.4.19, exact owner layer: if `F` and `F'` are exact functors in the canonical sense of
Definition 13.3.3, then `F ⋙ F'` is exact as well. The faithful source-facing surface is to check
the canonical composite `IsTriangulated` owner directly, since the composite instance is already
provided upstream and has no separate local name to recall. -/
#check (inferInstance : (F ⋙ F').IsTriangulated)

end IsTriangulated

end CategoryTheory

/-! ### Lemma_13_4_20 (from Chap13) -/
namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

section Precompose

/- Domain-style sampling for Lemma 13.4.20:
- primary domain: homological functors out of pretriangulated categories and exact functors between
  abelian categories;
- sampled owner declarations:
  `Functor.IsHomological`,
  the canonical precomposition instance `(L ⋙ F).IsHomological`,
  `ShortComplex.Exact.map`,
  `ExactFunctor`;
- best owner abstraction: `Functor.IsHomological`;
- primitive data: a triangulated functor `F : D' ⥤ D`, a homological functor `H : D ⥤ A`, and an
  exact functor `G : A ⥤ₑ A'`;
- derived API: the induced homologicality instances on `F ⋙ H` and `H ⋙ G.obj`;
- source/core/bridge triage:
  `source-facing`: the two stability statements in Lemma 13.4.20;
  `core/canonical`: `Functor.IsHomological`;
  `bridge/view`: exactness transport along `ShortComplex.Exact.map` for the abelian
    postcomposition case.

The precomposition part is therefore a pure recall of the owner instance, while the
postcomposition part should be stated directly as an owner instance on the composite functor,
rather than as a parallel theorem returning the same `Prop`. -/

variable {D' : Type u₂} [Category.{v₂} D'] [HasZeroObject D'] [HasShift D' ℤ] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]

/- Lemma 13.4.20: if `H : D ⥤ A` is homological and `F : D' ⥤ D` is an exact functor between
pretriangulated categories, encoded by `F.CommShift ℤ` and `F.IsTriangulated`, then the composite
`F ⋙ H` is homological. This is exactly the canonical instance on `Functor.IsHomological`; the
companion declaration below records the analogous postcomposition owner instance for exact functors
between abelian categories. -/
variable (F : D' ⥤ D) (H : D ⥤ A) [F.CommShift ℤ] [F.IsTriangulated] [H.IsHomological] in
#check (inferInstance : (F ⋙ H).IsHomological)

end Precompose

section Postcompose

variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable {A' : Type u₄} [Category.{v₄} A'] [Abelian A']

-- Proof sketch: for any distinguished triangle in `D`, homologicality of `H` gives an exact
-- short complex in `A`. Since `G : A ⥤ₑ A'` is exact, its underlying functor `G.obj` preserves
-- exact short complexes, so the image short complex for `H ⋙ G.obj` is exact.
/-- Postcomposition with an exact functor between abelian categories preserves homological
functors. -/
instance (H : D ⥤ A) (G : A ⥤ₑ A') [H.IsHomological] : (H ⋙ G.obj).IsHomological where
  exact T hT := (H.map_distinguished_exact T hT).map G.obj

end Postcompose

end CategoryTheory

/-! ### Lemma_13_4_21 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

universe vA vA' vD vD' uA uA' uD uD'

namespace CategoryTheory

namespace DeltaFunctor

/-
Domain-style sampling for Lemma 13.4.21:
- primary domain: composition of `δ`-functors with exact functors on the triangulated target side
  and on the abelian source side;
- sampled owner declarations in this domain:
  `CategoryTheory.DeltaFunctor`,
  `CategoryTheory.Functor.map_distinguished`,
  `CategoryTheory.Functor.commShiftIso_hom_naturality`,
  `ShortComplex.ShortExact.map_of_exact`;
- best owner abstraction: the public source-facing owners are the two composition constructors
  `DeltaFunctor.postcomposeExactFunctor` and `DeltaFunctor.precomposeExactFunctor`; the mapped
  distinguished-triangle and naturality facts are derived fields of those owners, not separate
  public wrapper theorems;
- primitive data: a `DeltaFunctor G`, together with either an exact triangulated functor
  `F : D ⥤ D'` or an exact functor `H : A' ⥤ₑ A` between abelian categories;
- derived API: the resulting composite `DeltaFunctor`s and their underlying-functor
  identification lemmas;
- source/core/bridge triage:
  `source-facing`: `DeltaFunctor.postcomposeExactFunctor` and
    `DeltaFunctor.precomposeExactFunctor`;
  `core/canonical`: `DeltaFunctor`, `Functor.map_distinguished`,
    `Functor.commShiftIso_hom_naturality`, and `ShortComplex.ShortExact.map_of_exact`;
  `bridge/view`: the induced connecting morphisms obtained by postcomposition or precomposition.

The distinguished-triangle and naturality proofs are implementation scaffolding for the two owner
constructions, so this file should expose the constructors directly and keep those proofs out of
the public API surface.
-/

section Postcompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {D' : Type uD'} [Category.{vD'} D'] [HasZeroObject D'] [HasShift D' ℤ]
variable [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

variable (G : DeltaFunctor A D) (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated]

/-- Lemma 13.4.21 (1): postcomposing a `δ`-functor `G : A ⥤ D` with an exact functor of
triangulated categories `F : D ⥤ D'` yields a `δ`-functor `A ⥤ D'`. -/
noncomputable def postcomposeExactFunctor : DeltaFunctor A D' where
  toFunctor := G.toFunctor ⋙ F
  additive := inferInstance
  δ := fun {S} hS ↦
    F.map (G.δ hS) ≫ (F.commShiftIso (1 : ℤ)).hom.app (G.obj S.X₁)
  map_distinguished := fun {S} hS ↦ by
    simpa using
      F.map_distinguished (G.triangle hS) (G.triangle_distinguished hS)
  δ_naturality := fun {S T} hS hS' φ ↦ by
    simpa [Functor.comp_map, Category.assoc] using
      CommSq.vert_comp
        ((G.δ_naturality hS hS' φ).map F)
        (CommSq.mk (F.commShiftIso_hom_naturality (G.map φ.τ₁) (1 : ℤ)))

/-- The underlying functor of the postcomposed `δ`-functor is the ordinary composite functor. -/
@[simp] theorem postcomposeExactFunctor_toFunctor :
    (G.postcomposeExactFunctor F).toFunctor = G.toFunctor ⋙ F := rfl

end Postcompose

section Precompose

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {A' : Type uA'} [Category.{vA'} A'] [Abelian A']
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
variable [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

variable (G : DeltaFunctor A D) (H : A' ⥤ₑ A)

/-- Lemma 13.4.21 (2): precomposing a `δ`-functor `G : A ⥤ D` with an exact functor
`H : A' ⥤ A` of abelian categories yields a `δ`-functor `A' ⥤ D`. -/
noncomputable def precomposeExactFunctor : DeltaFunctor A' D where
  toFunctor := H.obj ⋙ G.toFunctor
  additive := by
    letI : H.obj.Additive := ((AdditiveFunctor.ofExact A' A).obj H).property
    infer_instance
  δ := fun {_} hS ↦ G.δ (hS.map_of_exact H.obj)
  map_distinguished := fun {_} hS ↦ by
    simpa [Functor.comp_map] using
      G.map_distinguished (hS.map_of_exact H.obj)
  δ_naturality := fun {_ _} hS hS' φ ↦ by
    simpa [Functor.comp_map] using
      G.δ_naturality (hS.map_of_exact H.obj) (hS'.map_of_exact H.obj)
        ((H.obj.mapShortComplex).map φ)

/-- The underlying functor of the precomposed `δ`-functor is the ordinary composite functor. -/
@[simp] theorem precomposeExactFunctor_toFunctor :
    (G.precomposeExactFunctor H).toFunctor = H.obj ⋙ G.toFunctor := rfl

end Precompose

end DeltaFunctor

end CategoryTheory

/-! ### Lemma_13_4_22 (from Chap13) -/
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated

noncomputable section

universe vA vB vD uA uB uD

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

namespace DeltaFunctor

section

/-
Domain-style sampling for Lemma 13.4.22:
- primary domain: composing a source-side `δ`-functor with a homological functor on a
  pretriangulated target to obtain the induced cohomological long exact sequence;
- sampled owner declarations in this domain:
  `CategoryTheory.DeltaFunctor`,
  `CategoryTheory.CohomologicalDeltaFunctor`,
  `CategoryTheory.Functor.homologySequenceδ`,
  `CategoryTheory.Functor.homologySequenceComposableArrows₅_exact`;
- best owner abstraction:
  `source-facing`: `DeltaFunctor.toCohomologicalDeltaFunctor`;
  `core/canonical`: the chapter owners `DeltaFunctor`, `CohomologicalDeltaFunctor`, and the
    mathlib long-exact-sequence owners attached to `Functor.IsHomological`;
  `bridge/view`: the direct reuse of `Functor.homologySequenceδ` on the distinguished triangle
    `G.triangle hS`, with no separate local boundary-map owner.
- primitive data: a `δ`-functor `G : A ⥤ D`, a homological functor `H : D ⥤ B` with shift
- primitive data: a `δ`-functor `G : A ⥤ D` with its owner-level additive structure, a
  homological functor `H : D ⥤ B` with shift
  sequence, and the degree-`-1` vanishing hypothesis needed for left exactness in degree `0`;
- derived API: the resulting cohomological `δ`-functor owner assembled directly from the
  canonical long-exact-sequence maps.

The adjacent exactness windows and boundary-map naturality are already canonically owned by the
homological-functor API in mathlib once one passes to the distinguished triangle
`G.triangle hS`. This file should therefore build the source-facing cohomological `δ`-functor
directly from those owners instead of keeping parallel local exactness wrapper theorems.
-/

variable (G : DeltaFunctor A D) (H : D ⥤ B)
variable [H.IsHomological] [H.ShiftSequence ℤ]

/-- Lemma 13.4.22: if `G : A ⥤ D` is a `δ`-functor and `H : D ⥤ B` is a homological functor
such that `H^{-1}(G(X)) = 0` for every object `X` of `A`, then the degreewise composites
`H^n ∘ G` with their induced connecting morphisms form a cohomological `δ`-functor
`A ⥤ B`. -/
noncomputable def toCohomologicalDeltaFunctor
    (hneg : ∀ X : A, IsZero ((H.shift (-1)).obj (G.obj X))) :
    CohomologicalDeltaFunctor A B where
  F := fun n ↦ AdditiveFunctor.of (G.toFunctor ⋙ H.shift (n : ℤ))
  δ := fun {S} hS n ↦ by
    simpa using H.homologySequenceδ (G.triangle hS) (n : ℤ) (n + 1 : ℤ) (by simp)
  mono_map_f_zero := fun {S} hS ↦ by
    have hδ : H.homologySequenceδ (G.triangle hS) (-1) 0 (by simp) = 0 := by
      exact (hneg S.X₃).eq_of_src _ _
    exact (H.homologySequence_mono_shift_map_mor₁_iff
      (G.triangle hS) (G.triangle_distinguished hS) (-1) 0 (by simp)).2 (by
        simpa [triangle] using hδ)
  exact₅ := fun {_} hS n ↦ by
    simpa [triangle] using
      H.homologySequenceComposableArrows₅_exact
        (G.triangle hS) (G.triangle_distinguished hS) (n : ℤ) (n + 1 : ℤ) (by simp)
  δ_naturality := fun {_ _} hS hT φ n ↦ by
    refine CommSq.mk ?_
    simpa [triangle] using
      H.homologySequenceδ_naturality
        (G.triangle hS) (G.triangle hT) (G.triangleMap hS hT φ)
        (n : ℤ) (n + 1 : ℤ) (by simp)

end

end DeltaFunctor

end CategoryTheory

/-! ### Proposition_13_4_23 (from Chap13) -/
noncomputable section

open CategoryTheory Limits
open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

set_option checkBinderAnnotations false in
section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

/- Domain-style sampling for Proposition 13.4.23:
- primary domain: triangulated categories, commutative squares, distinguished triangles, and the
  octahedral formalism.
- inspected declarations: `CommSq`, `Triangle`, `TriangleMorphism`,
  `Pretriangulated.completeDistinguishedTriangleMorphism`, and `Triangulated.Octahedron`.
- best owner abstraction: the source-facing `3-by-3` extension should sit over the canonical input
  square `CommSq f u v f'`, while its row/column data should be read as `Triangle`s and the two
  comparison maps between the first two rows and the first two columns should be exposed through
  the canonical owner `TriangleMorphism`.
- primitive-vs-derived split:
  primitive data: the extra objects and arrows of the `3-by-3` diagram, the six
  distinguished-triangle witnesses, the four commutation rules needed to build the two comparison
  triangle morphisms, the three adjacent squares, and the lower-right anticommutativity;
  derived API: the six rows/columns as canonical `Triangle`s together with the two comparison
  `TriangleMorphism`s. -/

/- Source/core/bridge triage for Proposition 13.4.23:
- source-facing: `DistinguishedThreeByThreeExtension`, which records the textbook `3-by-3`
  diagram.
- core/canonical: `CommSq`, `Triangle`, `TriangleMorphism`, and `Octahedron`.
- bridge/view: the six row/column `Triangle` views together with the two comparison
  `TriangleMorphism`s assembled from the source-facing arrows and commutative squares. -/

/-- A `3-by-3` extension of a commutative square in a triangulated category.

The six distinguished triangles are the top, middle, and bottom rows together with the left,
middle, and right columns of the usual `3-by-3` diagram. The two comparison maps from the first
two rows and the first two columns are exposed below as canonical `TriangleMorphism`s, the
adjacent shift-compatible squares are part of the data, and the lower-right square is required to
anticommute. -/
structure DistinguishedThreeByThreeExtension
    {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
    (sq : CommSq f u v f') where
  Z : C
  Z' : C
  X'' : C
  Y'' : C
  Z'' : C
  top2 : Y ⟶ Z
  top3 : Z ⟶ X⟦(1 : ℤ)⟧
  middleRow2 : Y' ⟶ Z'
  middleRow3 : Z' ⟶ X'⟦(1 : ℤ)⟧
  left2 : X' ⟶ X''
  left3 : X'' ⟶ X⟦(1 : ℤ)⟧
  middleCol2 : Y' ⟶ Y''
  middleCol3 : Y'' ⟶ Y⟦(1 : ℤ)⟧
  right1 : Z ⟶ Z'
  right2 : Z' ⟶ Z''
  right3 : Z'' ⟶ Z⟦(1 : ℤ)⟧
  bottom1 : X'' ⟶ Y''
  bottom2 : Y'' ⟶ Z''
  bottom3 : Z'' ⟶ X''⟦(1 : ℤ)⟧
  topRow_distinguished : Triangle.mk f top2 top3 ∈ distTriang C
  middleRow_distinguished : Triangle.mk f' middleRow2 middleRow3 ∈ distTriang C
  leftColumn_distinguished : Triangle.mk u left2 left3 ∈ distTriang C
  middleColumn_distinguished : Triangle.mk v middleCol2 middleCol3 ∈ distTriang C
  topToMiddle_comm₂ : top2 ≫ right1 = v ≫ middleRow2
  topToMiddle_comm₃ : top3 ≫ u⟦(1 : ℤ)⟧' = right1 ≫ middleRow3
  leftToMiddle_comm₂ : left2 ≫ bottom1 = f' ≫ middleCol2
  leftToMiddle_comm₃ : left3 ≫ f⟦(1 : ℤ)⟧' = bottom1 ≫ middleCol3
  bottomRow_distinguished :
    Triangle.mk bottom1 bottom2 bottom3 ∈ distTriang C
  rightColumn_distinguished :
    Triangle.mk right1 right2 right3 ∈ distTriang C
  middle : CommSq middleRow2 middleCol2 right2 bottom2
  middleRight : CommSq middleRow3 right2 (left2⟦(1 : ℤ)⟧') bottom3
  lowerMiddle : CommSq bottom2 middleCol3 right3 (top2⟦(1 : ℤ)⟧')
  lowerRight_anticomm :
    bottom3 ≫ left3⟦(1 : ℤ)⟧' = -(right3 ≫ top3⟦(1 : ℤ)⟧')

namespace DistinguishedThreeByThreeExtension

variable {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
  {sq : CommSq f u v f'}

/-- The top distinguished triangle in a `3-by-3` extension. -/
abbrev topRow (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk f E.top2 E.top3

/-- The middle distinguished triangle in a `3-by-3` extension. -/
abbrev middleRow (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk f' E.middleRow2 E.middleRow3

/-- The left distinguished triangle in a `3-by-3` extension. -/
abbrev leftColumn (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk u E.left2 E.left3

/-- The middle distinguished triangle in the column direction. -/
abbrev middleColumn (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk v E.middleCol2 E.middleCol3

/-- The bottom distinguished triangle in a `3-by-3` extension. -/
abbrev bottomRow (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk E.bottom1 E.bottom2 E.bottom3

/-- The right distinguished triangle in a `3-by-3` extension. -/
abbrev rightColumn (E : DistinguishedThreeByThreeExtension sq) : Triangle C :=
  Triangle.mk E.right1 E.right2 E.right3

/-- The comparison morphism from the top row to the middle row. -/
abbrev topRowToMiddleRow (E : DistinguishedThreeByThreeExtension sq) :
    E.topRow ⟶ E.middleRow :=
  Triangle.homMk _ _ u v E.right1 sq.w E.topToMiddle_comm₂ E.topToMiddle_comm₃

/-- The comparison morphism from the left column to the middle column. -/
abbrev leftColumnToMiddleColumn (E : DistinguishedThreeByThreeExtension sq) :
    E.leftColumn ⟶ E.middleColumn :=
  Triangle.homMk _ _ f f' E.bottom1 sq.w.symm E.leftToMiddle_comm₂ E.leftToMiddle_comm₃

@[simp]
theorem topRow_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.topRow ∈ distTriang C :=
  E.topRow_distinguished

@[simp]
theorem middleRow_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.middleRow ∈ distTriang C :=
  E.middleRow_distinguished

@[simp]
theorem leftColumn_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.leftColumn ∈ distTriang C :=
  E.leftColumn_distinguished

@[simp]
theorem middleColumn_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.middleColumn ∈ distTriang C :=
  E.middleColumn_distinguished

@[simp]
theorem bottomRow_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.bottomRow ∈ distTriang C :=
  E.bottomRow_distinguished

@[simp]
theorem rightColumn_mem_distTriang (E : DistinguishedThreeByThreeExtension sq) :
    E.rightColumn ∈ distTriang C :=
  E.rightColumn_distinguished

end DistinguishedThreeByThreeExtension

-- Proof sketch: complete the top row and the left column to distinguished triangles, upgrade the
-- original square to morphisms of triangles, and then apply the octahedron axiom twice to obtain
-- the right column and the bottom row; the lower-right sign comes from the shifted triangle in the
-- final octahedral step.
/-- Proposition 13.4.23: any commutative square in a triangulated category extends to a
`3-by-3` diagram whose top, middle, and bottom rows and whose left, middle, and right columns are
distinguished triangles, with the adjacent shift-compatible squares and an anticommutative
lower-right square. -/
theorem commSq_has_distinguished_three_by_three_extension
    [IsTriangulated C] {X Y X' Y' : C} {f : X ⟶ Y} {u : X ⟶ X'} {v : Y ⟶ Y'} {f' : X' ⟶ Y'}
    (sq : CommSq f u v f') :
    Nonempty (DistinguishedThreeByThreeExtension sq) := sorry

/-- Proposition 13.4.23 in equation form: a commuting square `f ≫ v = u ≫ f'` admits a
distinguished `3-by-3` extension. -/
theorem commutative_square_has_distinguished_three_by_three_extension
    [IsTriangulated C] {X Y X' Y' : C} (f : X ⟶ Y) (u : X ⟶ X') (v : Y ⟶ Y')
    (f' : X' ⟶ Y') (comm : f ≫ v = u ≫ f') :
    Nonempty (DistinguishedThreeByThreeExtension (CommSq.mk comm)) := by
  simpa using commSq_has_distinguished_three_by_three_extension (CommSq.mk comm)

end

end CategoryTheory
