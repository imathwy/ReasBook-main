import stacks_project.Chap12.Lemma_12_10_3
import stacks_project.Chap12.Lemma_12_10_6
import stacks_project.Chap12.Lemma_12_11_2
import stacks_project.Chap12.«12_11_2_1»

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open ComplexShape

universe uA vA uB vB

namespace _root_.CategoryTheory.ObjectProperty

open _root_.CategoryTheory.ObjectProperty.SerreClassLocalization

noncomputable section

section

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (P : ObjectProperty A) [P.IsSerreClass]

/- Domain-style sampling for Lemma 12.11.3:
- primary domain: Serre localizations of abelian categories, the induced maps on `K₀`, and the
  canonical `ZMod 2` cyclic cochain complex detecting kernel classes;
- sampled owner declarations:
  `AbelianK0.mapExactFunctor`,
  `toSerreQuotient_kernel_eq`,
  `toSerreQuotient_essSurj`,
  `cyclicCochainComplex`;
- owner abstractions: the inclusion `P.ι`, the quotient functor `Q := P.isoModSerre.Q`, the
  induced `K₀` maps, and the canonical owner `cyclicCochainComplex` for the `ZMod 2` complex;
- primitive data: the Serre class `P`, the exact functors `P.ι` and `Q`, and the endomorphisms
  `φ, ψ` with square-zero relations;
- derived API: exactness and surjectivity on `K₀`, plus the kernel description via homology of the
  canonical cyclic complex after passage to the Serre quotient.

Source/core/bridge triage:
- `source-facing`: the exact sequence on `K₀` and the kernel characterization in the textbook
  cyclic-complex form;
- `core/canonical`: `AbelianK0.mapExactFunctor`, `ExactFunctor.of`, `Q`,
  `Q.mapHomologicalComplex`, and
  `cyclicCochainComplex`;
- `bridge/view`: quotient-acyclicity of the cyclic complex implies that its homology objects lie in
  the Serre class. -/

local notation "Q" => P.isoModSerre.Q
local instance : Abelian P.isoModSerre.Localization :=
  abelian Q P

local instance : PreservesFiniteLimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.1

local instance : PreservesFiniteColimits P.ι :=
  (exactFunctor_iff P.ι).1 (weakSerreSubcategory_inclusion_exact P) |>.2

local instance : PreservesFiniteLimits Q :=
  (exactFunctor_iff Q).1 (toSerreQuotient_exact P) |>.1

local instance : PreservesFiniteColimits Q :=
  (exactFunctor_iff Q).1 (toSerreQuotient_exact P) |>.2

local notation "K₀ι" => AbelianK0.mapExactFunctor (ExactFunctor.of P.ι)
local notation "K₀Q" => AbelianK0.mapExactFunctor (ExactFunctor.of Q)

-- Proof sketch: combine the exactness of the inclusion and quotient functors with the universal
-- property of `K₀` from `AbelianK0.mapExactFunctor`; exactness at `K₀(A)` comes from the quotient-kernel
-- description of the Serre localization, and surjectivity follows from essential surjectivity of
-- `toSerreQuotient_essSurj P`.
/-- Lemma 12.11.3 (1): the inclusion `\mathcal C \to \mathcal A` and the quotient functor
`\mathcal A \to \mathcal A / \mathcal C` induce an exact sequence
`K₀(\mathcal C) → K₀(\mathcal A) → K₀(\mathcal A / \mathcal C) → 0`. -/
theorem serreClassK0_exactSequence :
    Function.Exact K₀ι K₀Q ∧ Function.Surjective K₀Q := sorry

-- Proof sketch: apply the Serre-kernel criterion to the homology object of a complex `K`. If the
-- image of `K` in the Serre quotient is acyclic, then its `i`-th homology vanishes after
-- applying `Q`, so `K.homology i` lies in the kernel of `Q`, which is exactly `P`.
/-- If a homological complex becomes acyclic in the Serre quotient, then each of its homology
objects belongs to the Serre class. -/
theorem homology_mem_of_quotientAcyclic
    {ι : Type*} (c : ComplexShape ι) {K : HomologicalComplex A c}
    (hK : (((Q).mapHomologicalComplex c).obj K).Acyclic) (i : ι) :
    P (K.homology i) := by
  sorry

-- Proof sketch: a kernel element is represented by a formal difference of objects of the Serre
-- subcategory that becomes trivial in `K₀(A)`; organize the corresponding data as the canonical
-- `ZMod 2`-indexed cyclic cochain complex from `12.11.2.1`, require that its image in the Serre
-- quotient be exact, and read off the degree-`0` and degree-`1` homology objects in `P`.
-- Conversely, the usual Euler-characteristic computation for this cyclic complex shows that the
-- displayed difference maps to zero in `K₀(A)`.

/-- Lemma 12.11.3 (2): an element of the kernel of `K₀(\mathcal C) → K₀(\mathcal A)` is exactly a
difference `[H⁰(K)] - [H¹(K)]` coming from the canonical `ZMod 2`-indexed cyclic cochain complex
in `\mathcal A` built from the constant object `M` and alternating differentials
`\varphi, \psi`, whose image in the Serre quotient is exact and whose degree-`0` and degree-`1`
homology objects lie in the Serre subcategory `\mathcal C`. -/
theorem mem_ker_serreClassInclusionK0Map_iff
    (x : AbelianK0 P.FullSubcategory) :
    x ∈ (K₀ι).ker ↔
      ∃ (M : A) (φ ψ : M ⟶ M) (hφψ : φ ≫ ψ = 0) (hψφ : ψ ≫ φ = 0),
      let K := cyclicCochainComplex φ ψ hφψ hψφ
      ∃ hExactQ : (((Q).mapHomologicalComplex (up (ZMod 2))).obj K).Acyclic,
        x =
          K₀[⟨K.homology 0, homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 0⟩] -
            K₀[⟨K.homology 1, homology_mem_of_quotientAcyclic P (up (ZMod 2)) hExactQ 1⟩] := sorry

end

end

end _root_.CategoryTheory.ObjectProperty
