import StacksProject_2024.Chap26.Lemma_26_24_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {U X : Scheme.{u}}

-- Semantic recall: `Scheme.Modules.pushforward`, `Scheme.Modules.restrict`, and
-- `Scheme.Modules.restrictFunctor` are the canonical scheme-module owners here. For a
-- quasi-compact open immersion, the source extension object is therefore the canonical
-- pushforward `(pushforward j).obj G`, while the restriction comparison is the counit of
-- `restrictAdjunction j`.

/-- For a quasi-compact open immersion into a quasi-compact quasi-separated scheme, the canonical
pushforward extension of a quasi-coherent module is quasi-coherent. -/
instance pushforward_obj_isQuasicoherent_of_quasiCompact_openImmersion
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (G : U.Modules) [G.IsQuasicoherent] :
    ((pushforward j).obj G).IsQuasicoherent := by
  simpa using
    Scheme.pushforward_obj_isQuasicoherent_of_quasiCompact_quasiSeparated j G

/-- Lemma 28.22.1 (1): for a quasi-compact open immersion `j : U ⟶ X`, every quasi-coherent
`\mathcal O_U`-module extends to a quasi-coherent `\mathcal O_X`-module. -/
@[stacks 01PE]
theorem exists_quasiCoherentExtension
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (G : U.Modules) [G.IsQuasicoherent] :
    ∃ H : X.Modules, H.IsQuasicoherent ∧ Nonempty (H.restrict j ≅ G) := by
  exact ⟨(pushforward j).obj G, inferInstance, ⟨(asIso (restrictAdjunction j).counit).app G⟩⟩

/-- Lemma 28.22.1 (2): for a quasi-compact open immersion `j : U ⟶ X`, every quasi-coherent
subsheaf of `\mathcal F|_U` extends to a quasi-coherent subsheaf of `\mathcal F`. -/
@[stacks 01PE]
theorem exists_quasiCoherentSubsheafExtension
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) (G : Subobject (F.restrict j))
    [(Subobject.underlying.obj G).IsQuasicoherent] :
    ∃ H : Subobject F,
      (Subobject.underlying.obj H).IsQuasicoherent ∧
        ∃ e : (Subobject.underlying.obj H).restrict j ≅ Subobject.underlying.obj G,
          CommSq e.hom ((restrictFunctor j).map H.arrow) G.arrow (𝟙 _) := sorry

/-- Lemma 28.22.1 (3): for a quasi-compact open immersion `j : U ⟶ X`, every morphism from a
quasi-coherent `\mathcal O_U`-module to `\mathcal F|_U` extends to a morphism into
`\mathcal F`. -/
@[stacks 01PE]
theorem exists_quasiCoherentMorphismExtension
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) (G : U.Modules) [G.IsQuasicoherent]
    (φ : G ⟶ F.restrict j) :
    ∃ H : X.Modules,
      H.IsQuasicoherent ∧
        ∃ ψ : H ⟶ F, ∃ e : H.restrict j ≅ G,
          CommSq e.hom ((restrictFunctor j).map ψ) φ (𝟙 _) := sorry

end AlgebraicGeometry.Scheme.Modules
