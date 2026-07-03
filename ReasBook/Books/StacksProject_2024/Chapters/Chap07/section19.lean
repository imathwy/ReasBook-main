import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Adjunction.Opposites
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_7_19_1 (from Chap07) -/
open CategoryTheory Opposite
open CategoryTheory.Functor

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling:
- primary domain: presheaf right Kan extensions and their counits;
- sampled owner API:
  `HasRightKanExtension`,
  `Functor.rightKanExtensionCounit`,
  `Functor.ranCounit`,
  nearby chapter analogue `Lemma_7_5_3` for the left Kan extension unit;
- source/core/bridge triage:
  `source-facing`: Lemma 7.19.1 records, for one fixed presheaf `ℱ`, the canonical evaluation map
    and its restriction-map compatibility;
  `core/canonical`: `Functor.rightKanExtensionCounit`;
  `bridge/view`: the component at `U` and the naturality equation for `f : V ⟶ U`.

Primitive data are `u`, `ℱ`, and the existence of the right Kan extension along `u.op`. The
component map and its restriction compatibility are derived API from the counit natural
transformation, so this file should expose that owner projection directly rather than a parallel
local definition. The adjunction-level counit `Functor.ranCounit` is a stronger companion owner,
since it requires right Kan extensions for all presheaves; the source lemma only fixes one
presheaf, so `Functor.rightKanExtensionCounit` is the correct main entry here.
-/

/- Lemma 7.19.1: for a presheaf `ℱ` on `C` and `u : C ⥤ D`, the canonical map
`${}_p u \mathcal F (u(U)) \to \mathcal F(U)` is the component at `U` of the right Kan extension
counit `u.op.rightKanExtensionCounit ℱ`. -/
recall Functor.rightKanExtensionCounit

variable (u : C ⥤ D) (ℱ : Cᵒᵖ ⥤ Type w) [HasRightKanExtension u.op ℱ]
variable {U V : C} (f : V ⟶ U)

/- The source-facing map of Lemma 7.19.1 is the `U`-component of that counit. -/
#check (u.op.rightKanExtensionCounit ℱ).app (op U)

/- The restriction-map compatibility in Lemma 7.19.1 is exactly the naturality of the counit:
for `f : V ⟶ U`, this is `(u.op.rightKanExtensionCounit ℱ).naturality f.op`. -/
#check (u.op.rightKanExtensionCounit ℱ).naturality f.op

end CategoryTheory

/-! ### Lemma_7_19_2 (from Chap07) -/
universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

open CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (u : C ⥤ D)

/- Domain-style sampling:
- primary domain: presheaf right Kan extensions into `Type` and the adjunction they induce;
- sampled owner API:
  `Functor.HasPointwiseRightKanExtension`,
  `Functor.pointwiseRightKanExtension`,
  `Functor.ran`,
  `Functor.ranAdjunction`,
- source/core/bridge triage:
  `source-facing`: Lemma 7.19.2 records the pullback/pushforward adjunction on set-valued
    presheaves;
  `core/canonical`: `Functor.ranAdjunction`;
  `bridge/view`: the canonical passage from pointwise right Kan extensions of `Type`-valued
    presheaves along `u.op` to the chosen right Kan extension functor `u.op.ran`.

Primitive data are only the functor `u`; for `Type`-valued presheaves, the needed right Kan
extensions are derived canonically from pointwise limits in `Type`. The adjunction itself is then
derived API from `Functor.ranAdjunction`, so this file should expose that owner after supplying
the canonical presheaf specialization directly rather than add a parallel local wrapper or extra
existence hypotheses to the public API.
-/

section

/- Lemma 7.19.2: for a functor `u : C ⥤ D`, pullback of set-valued presheaves along `u.op`,
realized as precomposition with `u.op`, has as right adjoint the presheaf pushforward realized by
right Kan extension along `u.op`. This is exactly the canonical presheaf specialization of
`Functor.ranAdjunction`. -/
#check (u.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂ w)) :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂ w))).obj u.op ⊣ u.op.ran)

variable (ℱ : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w))
variable (𝒢 : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂ w))

/- The source-facing hom-set bijection is the `Adjunction.homEquiv` of the presheaf right
Kan-extension adjunction. -/
#check (((u.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂ w))).homEquiv 𝒢 ℱ) :
    ((u.op ⋙ 𝒢) ⟶ ℱ) ≃ (𝒢 ⟶ u.op.ran.obj ℱ))

end

end CategoryTheory

/-! ### Lemma_7_19_3 (from Chap07) -/
open Opposite
open CategoryTheory.Functor
open CategoryTheory.Limits

universe u₁ u₂ v

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v} C]
variable {D : Type u₂} [Category.{v} D]
variable (u : C ⥤ D) (v' : D ⥤ C) (adj : u ⊣ v')

/- Domain-style sampling:
- primary domain: category-theoretic consequences of an adjunction on presheaf pullback,
  comma categories, and Kan extension comparisons;
- sampled owner API:
  `Adjunction.compYonedaIso`,
  `mkInitialOfLeftAdjoint`,
  `mkTerminalOfRightAdjoint`,
  `Adjunction.rightAdjointUniq`;
- source-facing: Lemma 7.19.3 records the five standard consequences of a functor `u`
  admitting a right adjoint `v'`;
- core/canonical: the adjunction owner declarations listed above;
- bridge/view: the objectwise representable comparison and the presheaf pullback/right- and
  left-Kan specializations.

Primitive data are the functors `u`, `v'`, the adjunction `adj`, and the existence of the
relevant Kan extensions in clauses `(4)` and `(5)`. The representable comparison, the
initial/terminal comma objects, and the Kan-extension identifications are derived API from those
owners, so this file should expose the owner projections directly rather than keep parallel local
wrappers. Clause `(5)` then uses the dual owner `Adjunction.leftAdjointUniq`. -/

/- Lemma 7.19.3 (1): the presheaf comparison underlying the representable pullback identity is the
canonical Yoneda comparison attached to an adjunction. -/
recall Adjunction.compYonedaIso

/- Lemma 7.19.3 (1): pulling back the representable presheaf `h_V` along `u` yields the
representable presheaf `h_{v'(V)}`. In mathlib this is the Yoneda comparison
`adj.compYonedaIso.symm.app V`, viewed objectwise. -/
#check
  (Iso.app (adj.compYonedaIso.symm) :
    ∀ V : D,
      ((whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op).obj (yoneda.obj V) ≅
        yoneda.obj (v'.obj V))

/- Lemma 7.19.3 (2): for `U : C`, the unit map `U ⟶ v'(u(U))` defines an initial object of
`StructuredArrow U v'`. -/
#check
  (mkInitialOfLeftAdjoint v' adj :
    ∀ U : C,
      IsInitial (StructuredArrow.mk (adj.unit.app U) : StructuredArrow U v'))

/- Lemma 7.19.3 (3): for `V : D`, the counit map `u(v'(V)) ⟶ V` defines a terminal object of
`CostructuredArrow u V`. -/
#check
  (mkTerminalOfRightAdjoint v' adj :
    ∀ V : D,
      IsTerminal (CostructuredArrow.mk (adj.counit.app V) : CostructuredArrow u V))

section RightKanExtensionComparison

variable [∀ P : Cᵒᵖ ⥤ Type v, u.op.HasRightKanExtension P]

/- Lemma 7.19.3 (4): the Stacks identity `${}_p u = v^p` is realized in the project API by the
canonical isomorphism from the chosen right Kan extension functor `u.op.ran` to pullback along
`v'`, obtained from uniqueness of right adjoints. -/
#check
  ((u.op.ranAdjunction (Type v)).rightAdjointUniq (adj.op.whiskerLeft (Type v)) :
    u.op.ran ≅ (whiskeringLeft Dᵒᵖ Cᵒᵖ (Type v)).obj v'.op)

end RightKanExtensionComparison

section LeftKanExtensionComparison

variable [∀ P : Dᵒᵖ ⥤ Type v, v'.op.HasLeftKanExtension P]

/- Lemma 7.19.3 (5): the Stacks identity `u^p = v'_p` is realized in the project API by the
canonical isomorphism from pullback along `u` to the chosen left Kan extension functor `v'.op.lan`,
obtained from uniqueness of left adjoints. -/
#check
  ((adj.op.whiskerLeft (Type v)).leftAdjointUniq (v'.op.lanAdjunction (Type v)) :
    (whiskeringLeft Cᵒᵖ Dᵒᵖ (Type v)).obj u.op ≅ v'.op.lan)

end LeftKanExtensionComparison

end

end CategoryTheory
