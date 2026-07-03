import Mathlib
import stacks_project.Chap17.Definition_17_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopCat.Presheaf TopologicalSpace
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for global generation versus stalkwise generation:
- inspected owner declarations:
  `SheafOfModules.GeneratingSections`,
  `SheafOfModules.GeneratingSections.π`,
  `RingedSpace.moduleStalkHom`,
  `sheaf_epi_iff_stalk_surjective`;
- best owner abstraction:
  the core owner is `ℱ.GeneratingSections`, with `ℱ.freeHomEquiv.symm s` and its stalk maps as the
  primitive bridge from a family of global sections to the sheaf itself;
- primitive data:
  a family `s : I → ℱ.sections`;
- derived API:
  the stalkwise spanning reformulation of the owner condition `Epi (ℱ.freeHomEquiv.symm s)`.

Layer triage:
- `source-facing`: a chosen family of global sections generates `ℱ`;
- `core/canonical`: `ℱ.GeneratingSections`, `ℱ.freeHomEquiv`, and `RingedSpace.moduleStalkHom`;
- `bridge/view`: the stalkwise `Submodule.span = ⊤` criterion below.
-/

variable {X : RingedSpace.{u}}
variable {ℱ : RingedSpace.Modules X}
variable {I : Type u}

-- Proof sketch: let `π : free I ⟶ ℱ` be the morphism corresponding to the family `s`. The family
-- generates `ℱ` exactly when `π` is an epimorphism. By the stalkwise criterion for epimorphisms of
-- sheaves, this is equivalent to surjectivity of every stalk map `π_x`. For module homomorphisms,
-- surjectivity of `π_x` is equivalent to the germs of the sections spanning the stalk.
/-- Lemma 17.4.2: a family of global sections of an `\mathcal O_X`-module sheaf on a ringed space
generates the sheaf if and only if, for every point `x`, the germs of those sections span the
stalk `\mathcal F_x` as an `\mathcal O_{X, x}`-module. -/
theorem generating_sections_iff_stalkwise_span_eq_top (s : I → ℱ.sections) :
    Epi (ℱ.freeHomEquiv.symm s) ↔
      ∀ x : X,
        Submodule.span (X.presheaf.stalk x)
          (Set.range fun i ↦ Γgerm ℱ.val.presheaf x ((s i).1 (op ⊤))) = ⊤ := sorry

end AlgebraicGeometry
