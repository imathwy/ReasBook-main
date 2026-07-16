import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced `Scheme.IdealSheafData.subscheme`; local precedent in
-- Lemma 30.12.3 uses ideal-sheaf subobjects on integral closed subschemes and direct images by
-- `Scheme.Modules.pushforward`.

/-- Lemma 30.12.4: let `X` be a Noetherian scheme and let `P` be a property of coherent
`\mathcal O_X`-modules. If `P` is closed under extensions along short exact sequences of
coherent modules, and if `P` holds for the pushforward of every quasi-coherent ideal sheaf on
every integral closed subscheme of `X`, then `P` holds for every coherent module on `X`. -/
@[stacks 01YG]
theorem coherent_property_of_shortExact_and_pushforward_ideal
    (P : X.Modules → Prop)
    (h_shortExact :
      ∀ {S : ShortComplex X.Modules}, S.ShortExact →
        S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
        P S.X₁ → P S.X₃ → P S.X₂)
    (h_pushforward_ideal :
      ∀ (Z : X.IdealSheafData) (h_integral : IsIntegral Z.subscheme)
        (I : Subobject (SheafOfModules.unit Z.subscheme.ringCatSheaf : Z.subscheme.Modules)),
        (Subobject.underlying.obj I : Z.subscheme.Modules).IsQuasicoherent →
          P ((Scheme.Modules.pushforward Z.subschemeι).obj
            (Subobject.underlying.obj I : Z.subscheme.Modules)))
    (ℱ : X.Modules) [ℱ.IsCoherent] :
    P ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
