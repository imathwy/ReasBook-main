import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.LinearAlgebra.Dimension.Finite
import stacks_project.Chap15.Definition_15_59_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open ComplexShape

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)
local notation "H" => DerivedCategory.homologyFunctor (ModuleCat R)
private abbrev Q : Cpx ⥤ DMod := DerivedCategory.Q

/- Domain-style sampling for Definition 15.65.1:
- primary domain: pseudo-coherence for derived `R`-complexes and `R`-modules;
  `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`,
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`;
- best owner abstraction: this file owns the absolute derived predicates
  `DerivedCategory.IsMPseudoCoherent` and `DerivedCategory.IsPseudoCoherent`, together with the
  high-frequency cochain-complex and module bridge abbreviations built from these owners; the
  relative notions remain downstream bridge/view layers;
- primitive vs. derived:
  primitive data are the bounded finite-free representative and the cohomology comparison map in
  `D(R)`;
  derived API is the cochain-complex specialization via `DerivedCategory.Q` and the module
  specialization `M ↦ M[0]`, exposed through `CochainComplex.IsMPseudoCoherent`,
  `CochainComplex.IsPseudoCoherent`, `ModuleCat.IsMPseudoCoherent`, and
  `ModuleCat.IsPseudoCoherent`;
- source/core/bridge triage:
  `source-facing`: the four numbered predicates of Definition `15.65.1`;
  `core/canonical`: the owner predicates on `DerivedCategory` together with
    `CochainComplex.IsTermwiseFiniteFree` and its induced termwise `Module.Free` /
    `Module.Finite` instances;
  `bridge/view`: the cochain-complex and module specializations, together with the relative
    extensions from `15.82.4` and `15.82.10`.
-/

namespace CochainComplex

/-- A cochain complex of `R`-modules is termwise finite free when every degree is a finite free
`R`-module. -/
class IsTermwiseFiniteFree (E : Cpx) : Prop where
  out : ∀ i : ℤ, Module.Free R (E.X i) ∧ Module.Finite R (E.X i)

instance (E : Cpx) [hE : IsTermwiseFiniteFree E] (i : ℤ) : Module.Free R (E.X i) :=
  (hE.out i).1

instance (E : Cpx) [hE : IsTermwiseFiniteFree E] (i : ℤ) : Module.Finite R (E.X i) :=
  (hE.out i).2

end CochainComplex

namespace DerivedCategory

/-- Definition 15.65.1 (1): an object `K^•` of `D(R)` is `m`-pseudo-coherent if it admits a map
from a bounded cochain complex of finite free `R`-modules inducing isomorphisms on cohomology in
degrees `> m` and an epimorphism in degree `m`. -/
def IsMPseudoCoherent (K : DMod) (m : ℤ) : Prop :=
  ∃ E : Cpx,
    (∃ a b : ℤ, E.IsStrictlyGE a ∧ E.IsStrictlyLE b) ∧
      E.IsTermwiseFiniteFree ∧
      ∃ α : Q.obj E ⟶ K,
        (∀ i : ℤ, m < i → IsIso ((H i).map α)) ∧
          Epi ((H m).map α)

/-- Definition 15.65.1 (2): an object `K^•` of `D(R)` is pseudo-coherent if it is represented in
the derived category by a bounded-above cochain complex of finite free `R`-modules. -/
def IsPseudoCoherent (K : DMod) : Prop :=
  ∃ E : Cpx,
    (∃ b : ℤ, E.IsStrictlyLE b) ∧
      E.IsTermwiseFiniteFree ∧
      ∃ α : Q.obj E ⟶ K, IsIso α

end DerivedCategory

namespace CochainComplex

/-- A cochain complex is `m`-pseudo-coherent when its image in `D(R)` is `m`-pseudo-coherent in
the canonical sense of Definition `15.65.1`. -/
abbrev IsMPseudoCoherent (K : Cpx) (m : ℤ) : Prop :=
  DerivedCategory.IsMPseudoCoherent ((Q).obj K) m

/-- A cochain complex is pseudo-coherent when its image in `D(R)` is pseudo-coherent in the
canonical sense of Definition `15.65.1`. -/
abbrev IsPseudoCoherent (K : Cpx) : Prop :=
  DerivedCategory.IsPseudoCoherent ((Q).obj K)

end CochainComplex

namespace ModuleCat

/-- The degree-zero embedding `\operatorname{Mod}(R) ⥤ D(R)`. -/
abbrev single0Functor : ModuleCat R ⥤ DMod :=
  DerivedCategory.singleFunctor (ModuleCat R) (0 : ℤ)

/-- Definition 15.65.1 (3): an `R`-module `M` is `m`-pseudo-coherent when the derived object
`M[0]` is `m`-pseudo-coherent. -/
abbrev IsMPseudoCoherent (M : ModuleCat R) (m : ℤ) : Prop :=
  DerivedCategory.IsMPseudoCoherent (single0Functor.obj M) m

/-- Definition 15.65.1 (4): an `R`-module `M` is pseudo-coherent when the derived object `M[0]`
is pseudo-coherent. -/
abbrev IsPseudoCoherent (M : ModuleCat R) : Prop :=
  DerivedCategory.IsPseudoCoherent (single0Functor.obj M)

end ModuleCat

end

end CategoryTheory
