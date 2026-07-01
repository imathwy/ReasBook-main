import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

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
