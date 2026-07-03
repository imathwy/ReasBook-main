import StacksProject_2024.Chap13.Definition_13_8_1
import StacksProject_2024.Chap13.Definition_13_11_3
import StacksProject_2024.Chap15.Definition_15_70_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open DerivedCategory
open scoped CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Mod" => ModuleCat R
local notation "DbMod" => Dᵇ(Mod)
local notation "Hb" => boundedDerivedHomologyFunctor Mod

/-
Domain-style sampling for Lemma 15.70.5:
- primary domain: finite injective dimension in `D(R)`, together with bounded derived objects and
  bounded cochain-complex presentations;
- sampled owner declarations:
  `HasFiniteInjectiveDimension`,
  `injectiveDimension`,
  `DbMod`,
  `boundedDerivedHomologyFunctor`,
  `DerivedCategory.homologyFunctor`,
  `t.bounded`,
  `Compᵇ(Mod)`;
- best owner abstraction: the source-facing statements stay about finite injective dimension,
  while boundedness in `D(R)` should be stated directly on the chapter owner
  `DbMod`, and the representative-level bounded-complex hypothesis should reuse the
  chapter owner `Compᵇ(Mod)` rather than a raw cochain complex together with separate
  support-bound witnesses;
  finite injective dimension for modules is already canonically owned by `injectiveDimension`,
  and the bounded-derived cohomology objects should be read through the chapter owner
  `boundedDerivedHomologyFunctor`, so the hypotheses below should use
  `injectiveDimension _ ≠ ⊤` directly on `((Hb i).obj K)`;
- primitive vs. derived:
  primitive data are the bounded derived object `K : DbMod` in part `(1)`, read through the
  chapter owner `Hb i`,
  the bounded representative complex `K' : Compᵇ(Mod)` in part `(2)`, and the module-level
  finite-injective-dimension hypotheses on cohomology objects or terms;
  derived API is the resulting `HasFiniteInjectiveDimension` conclusion, stated in part `(2)`
  directly for the represented object `Q.obj K'.obj`;
- source/core/bridge triage:
  `source-facing`: the two finite-injective-dimension theorems below;
  `core/canonical`: `HasFiniteInjectiveDimension`, `injectiveDimension`,
    `DbMod`, `Hb`,
    `DerivedCategory.homologyFunctor`, `t.bounded`, and
    `Compᵇ(Mod)`;
  `bridge/view`: passage from a chosen representative `K'` to an arbitrary isomorphic derived
  object, which is not kept in the main public theorem statement.
-/

-- Proof sketch: apply the Ext spectral sequence of Lemma `13.21.3` to the functor
-- `Hom_R(N, -)` and use the boundedness of `K` together with the finite injective-dimension
-- bounds on the cohomology objects `H^i(K)` to deduce eventual vanishing of
-- `Ext^n_R(N, K)` for every module `N`; then conclude from the criterion of Lemma `15.70.2`.
/-- Lemma 15.70.5 (1): if `K` lies in the bounded derived category `D^b(R)` and each cohomology
module `H^i(K)` has finite injective dimension, then `K` has finite injective dimension. -/
theorem hasFiniteInjectiveDimension_of_bounded_of_homology_finiteInjectiveDimension
    (K : DbMod)
    (hH : ∀ i : ℤ,
      injectiveDimension ((Hb i).obj K) ≠ ⊤) :
    HasFiniteInjectiveDimension K.obj := sorry

-- Proof sketch: for each term `K'ⁱ`, choose a finite injective resolution and splice these
-- resolutions into a bounded double complex representing `DerivedCategory.Q.obj K'`. The total
-- complex is again bounded with injective terms, so it gives a finite injective-amplitude
-- representative of `DerivedCategory.Q.obj K'`.
/-- Lemma 15.70.5 (2): if a bounded cochain complex `K'` has termwise finite injective dimension,
then the represented derived object `Q.obj K'.obj` has finite injective
dimension. The boundedness datum is carried by the chapter owner `Compᵇ(Mod)`. -/
theorem hasFiniteInjectiveDimension_of_bounded_of_termwise_finiteInjectiveDimension
    (K' : Compᵇ(Mod))
    (hterm : ∀ i : ℤ, injectiveDimension (K'.obj.X i) ≠ ⊤) :
    HasFiniteInjectiveDimension (Q.obj K'.obj) := sorry

end

end CategoryTheory
