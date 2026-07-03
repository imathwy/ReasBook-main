import Mathlib
import StacksProject_2024.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory ComplexShape HomologicalComplex MonoidalCategory

noncomputable section

universe u

namespace CochainComplex

variable {R : Type u} [CommRing R]

local notation "single₀" => singleFunctor (ModuleCat R) (0 : ℤ)

/-
Domain sampling pass:
* primary domain: K-flat cochain complexes of `R`-modules, tested by tensoring with finitely
  presented `R`-modules;
* sampled owner declarations:
  - `CochainComplex.singleFunctor` from mathlib, used here through the standard local notation
    `single₀` for a module concentrated in degree `0`;
  - `CochainComplex.IsKFlat` from `Definition_15_59_1`, the source-facing owner predicate;
  - `CochainComplex.isKFlat_colimit_of_isFiltered` from `Lemma_15_59_8`, the chapter closure
    theorem
    used by the textbook reduction from arbitrary modules to finitely presented modules;
  - `CategoryTheory.ShortComplex.TensorShortExactForFinitelyPresented` from
    `Theorem_10_82_3`, showing the project’s canonical style for “for every finitely presented
    module” is an instance-binder quantification rather than an explicit witness argument.

Source/core/bridge triage:
* `source-facing`: the criterion that acyclicity after tensoring with finitely presented modules
  already implies K-flatness;
* `core/canonical`: `CochainComplex.IsKFlat`;
* `bridge/view`: `HomologicalComplex.tensorObj K ((single₀).obj M)`, the canonical tensor with
  `M` placed in degree `0`.

Primitive data are only the complex `K` and the finitely-presented tensor-acyclicity hypothesis.
The K-flatness conclusion is derived API over the existing owner `CochainComplex.IsKFlat`, so this
file should stay as a single owner-level criterion and avoid any auxiliary wrapper predicate.
-/

-- Proof sketch: by Lemmas `10.11.3` and `10.12.9`, the same tensor-acyclicity holds for every
-- `R`-module because every module is a filtered colimit of finitely presented modules. Then
-- truncate an arbitrary acyclic complex termwise, use exactness of filtered colimits to reduce to
-- bounded complexes, and finish by induction on the length of the bounded complex via
-- Lemma `15.58.4` and the two-out-of-three argument from Lemma `15.59.6`.
/-- Lemma 15.59.9: if tensoring a cochain complex `K^•` of `R`-modules on the right with every
finitely presented `R`-module gives an acyclic cochain complex, then `K^•` is K-flat. -/
theorem isKFlat_of_tensor_finitelyPresented_acyclic
    (K : CochainComplex (ModuleCat R) ℤ)
    (hfp : ∀ (M : ModuleCat R) [Module.FinitePresentation R M],
      (HomologicalComplex.tensorObj K ((single₀).obj M)).Acyclic) :
    K.IsKFlat := sorry

end CochainComplex
