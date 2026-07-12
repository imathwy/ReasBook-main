import Mathlib
import StacksProject_2024.Chap08.Definition_8_5_5
import StacksProject_2024.Chap08.Lemma_8_11_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open FibredCategoryOver

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {Xₛ Yₛ : StackInGroupoidsOver.{u, v, max u v, v} J}

/- Domain-style sampling for Definition 8.11.4:
- primary domain: gerbes over morphisms of stacks in groupoids, expressed through the canonical
  factorization-to-target projection over the topology on the target stack inherited from the
  ambient site;
- inspected owner-level declarations:
  `IsGerbe`,
  `fibredInGroupoidsFactorizationToTarget`,
  `inheritedTopology`,
  `factorizationToTarget_isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms`;
- best owner abstraction: the canonical gerbe predicate
  `IsGerbe (inheritedTopology J Yₛ)
    (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor`;
- primitive-vs-derived split:
  primitive data: none in this file, since Definition 8.11.4 only specializes the upstream gerbe
    owner to the canonical factorization attached to `F`;
  derived API: the short owner-level names `IsGerbeOver F` and
    `LocallyLiftsFiberMorphisms F`, plus the gerbe characterization specialized from
    Lemma 8.11.3.

Source/core/bridge triage:
- source-facing: the phrase “`F` is a gerbe over `Yₛ`” for a morphism of stacks in groupoids;
- core/canonical: `IsGerbe` on the factorization-to-target projection over `inheritedTopology`;
- bridge/view: the short property alias `IsGerbeOver F` and its companion
  characterization theorem below. -/

namespace StackInGroupoidsOver.Hom

variable (F : Xₛ ⟶ Yₛ)

/- Definition 8.11.4: the phrase “`F` is a gerbe over `Yₛ`” is the canonical gerbe predicate on
the factorization-to-target projection over the topology on `Yₛ` inherited from `(C, J)`. The
source-facing characterization from Lemma `8.11.3` is recovered by its canonical explicit-
factorization specialization. -/
#check IsGerbe (inheritedTopology J Yₛ)
  (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor

/-- Bridge/view shorthand for the source-facing phrase “`F` is a gerbe over `Yₛ`”. -/
abbrev IsGerbeOver (F : Xₛ ⟶ Yₛ) : Prop :=
  IsGerbe (inheritedTopology J Yₛ)
    (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor

/-- Lemma 8.11.3 identifies a gerbe over the target stack with the two local lifting conditions on
the original morphism. -/
@[stacks 06P1]
theorem isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms
    (F : Xₛ ⟶ Yₛ) :
    IsGerbeOver F ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F :=
by
  change
    IsGerbe (inheritedTopology J Yₛ)
      (fibredInGroupoidsFactorizationToTarget (toBasedFunctor F)).toFunctor ↔
      LocallyEssentiallySurjectiveOnObjects F ∧
        LocallyLiftsFiberMorphisms F
  exact
    factorizationToTarget_isGerbeOverInheritedTopology_iff_locallyEssentiallySurjective_and_locallyLiftsFiberMorphisms
      F

-- Proof sketch: apply the forward implication of the equivalence from Lemma `8.11.3` and project
-- to the local essential-surjectivity clause.
/-- A gerbe over the target stack is locally essentially surjective on objects after refining by a
cover of the base object. -/
theorem IsGerbeOver.locallyEssentiallySurjectiveOnObjects {F : Xₛ ⟶ Yₛ}
    (hF : IsGerbeOver F) :
    LocallyEssentiallySurjectiveOnObjects F :=
  (isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms
    F).mp hF |>.1

/-- A gerbe over the target stack locally lifts morphisms in fibers after refining by a cover. -/
theorem IsGerbeOver.locallyLiftsFiberMorphisms {F : Xₛ ⟶ Yₛ} (hF : IsGerbeOver F) :
    LocallyLiftsFiberMorphisms F :=
  (isGerbeOver_iff_locallyEssentiallySurjectiveOnObjects_and_locallyLiftsFiberMorphisms
    F).mp hF |>.2

end StackInGroupoidsOver.Hom

end CategoryTheory
