import Mathlib.Algebra.Homology.Monoidal
import StacksProject_2024.Chap15.Lemma_15_72_1

open CategoryTheory
open CategoryTheory.Limits
open CochainComplex.HomComplex
open ComplexShape
open HomologicalComplex
open MonoidalClosed
open scoped ModuleComplexInternalHom

noncomputable section

universe u

section

variable {R : Type u} [CommRing R]

local notation "CpxR" => CochainComplex (ModuleCat R) ℤ
local notation:70 A " ⊗ " B => tensorObj A B

/- Domain-style sampling for 15.72.6:
- primary domain: the tensor-to-iterated-internal-Hom comparison for the chapter internal-Hom
  complex on cochain complexes of `R`-modules;
- sampled owner declarations:
  `module_complex_internal_hom`,
  `module_complex_internal_hom_piIso`,
  `module_complex_internal_hom_piProj`,
  `HomologicalComplex.tensorObj`,
  `HomologicalComplex.mapBifunctorDesc`,
  `MonoidalClosed.curry`,
  `ihom.ev`;
- best owner abstraction: the public owner remains the source-facing Chapter 15 internal-Hom
  complex `⟪-, -⟫`, and the tensor source should be presented on the theorem surface by the
  canonical cochain-complex tensor notation `⊗`; the ambient module-level closed-monoidal
  structure supplies the summandwise evaluation/currying maps used to build the chain map, but it
  does not replace the chapter owner;
- primitive data vs. derived API: the primitive owner data are the complexes `⟪K, L⟫` and their
  canonical degree decompositions `module_complex_internal_hom_piIso`; the owner-side projection
  bridge `module_complex_internal_hom_piProj` and the canonical morphism
  `⟪L, M⟫ ⊗ K ⟶ ⟪⟪K, L⟫, M⟫`, together with its three source-facing naturality squares in `K`,
  `L`, and `M`, are derived API expressed through the owner-side bifunctorial bridge
  `module_complex_internal_homMap`;
- source/core/bridge triage:
  `source-facing`: `tensor_internal_hom_to_iterated_internal_hom`;
  `core/canonical`: `module_complex_internal_hom`, `module_complex_internal_hom_piIso`,
    `HomologicalComplex.tensorObj`, `MonoidalClosed.curry`, and `ihom.ev`;
  `bridge/view`: the projection maps from the product decomposition of the source and target
  internal-Hom complexes together with the owner-side bifunctoriality map
  `module_complex_internal_homMap`.
-/ 

-- Proof sketch: rewrite `n` as `t + r` and reassociate the sum on `ℤ`.
/-- Reindexing the target degree in the iterated tensor-Hom comparison map. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_indexEq
    {t r n p : ℤ} (h : t + r = n) :
    t + (p + r) = n + p := by
  omega

section

open MonoidalCategory

/-- The summandwise braiding/evaluation map contributing to the degree-`n` component of the
canonical morphism `Tot(⟪L, M⟫ ⊗ K) ⟶ ⟪⟪K, L⟫, M⟫`. This is the owner-level component whose
sign is analyzed in Remark `15.72.7`. -/
noncomputable def tensor_internal_hom_to_iterated_internal_hom_component
    (K L M : CpxR) (t r n p : ℤ) (h : t + r = n) :
    ((⟪L, M⟫).X t ⊗ K.X r) ⟶
      (ihom ((⟪K, L⟫).X p)).obj (M.X (n + p)) :=
  MonoidalClosed.curry
    (((module_complex_internal_hom_piProj K L p r) ⊗ₘ
        ((module_complex_internal_hom_piProj L M t (p + r)) ⊗ₘ 𝟙 (K.X r))) ≫
      (α_ ((ihom (K.X r)).obj (L.X (p + r)))
        ((ihom (L.X (p + r))).obj (M.X (t + (p + r)))) (K.X r)).inv ≫
      ((β_ ((ihom (K.X r)).obj (L.X (p + r)))
          ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))).hom ⊗ₘ
        𝟙 (K.X r)) ≫
      (β_ (((ihom (L.X (p + r))).obj (M.X (t + (p + r)))) ⊗
          ((ihom (K.X r)).obj (L.X (p + r)))) (K.X r)).hom ≫
      (K.X r ◁
        (β_ ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))
          ((ihom (K.X r)).obj (L.X (p + r)))).hom) ≫
      (α_ (K.X r) ((ihom (K.X r)).obj (L.X (p + r)))
        ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))).inv ≫
      ((ihom.ev (K.X r)).app (L.X (p + r)) ⊗ₘ
        𝟙 ((ihom (L.X (p + r))).obj (M.X (t + (p + r))))) ≫
      (ihom.ev (L.X (p + r))).app (M.X (t + (p + r))) ≫
      eqToHom (congrArg (fun z : ℤ ↦ M.X z)
        (tensor_internal_hom_to_iterated_internal_hom_indexEq h)))

end

/-- The degree-`n` component of the canonical tensor-to-iterated-internal-Hom morphism. -/
private noncomputable def tensor_internal_hom_to_iterated_internal_hom_f
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K] (n : ℤ) :
    (⟪L, M⟫ ⊗ K).X n ⟶ (⟪⟪K, L⟫, M⟫).X n :=
  let desc :
      (⟪L, M⟫ ⊗ K).X n ⟶
        ∏ᶜ fun p : ℤ ↦ (ihom ((⟪K, L⟫).X p)).obj (M.X (n + p)) :=
    mapBifunctorDesc fun t r h ↦
      Pi.lift fun p ↦
        tensor_internal_hom_to_iterated_internal_hom_component K L M t r n p h
  desc ≫ (module_complex_internal_hom_piIso ⟪K, L⟫ M n).hom

-- Proof sketch: project both sides to a tensor summand in total degree `i` and then to a factor
-- of the target product. The source differential splits into the tensor differential on
-- `⟪L, M⟫ ⊗ K`, while the target differential is the internal-Hom differential on
-- `⟪⟪K, L⟫, M⟫`; the component identities are exactly the sign computations isolated in the
-- local auxiliary development.
/-- The degreewise tensor-to-iterated-internal-Hom maps commute with the differentials. -/
private theorem tensor_internal_hom_to_iterated_internal_hom_f_comm
    (K L M : CpxR) [HasTensor (⟪L, M⟫) K] (i j : ℤ) (hij : (up ℤ).Rel i j) :
    tensor_internal_hom_to_iterated_internal_hom_f K L M i ≫
      (⟪⟪K, L⟫, M⟫).d i j =
        (⟪L, M⟫ ⊗ K).d i j ≫
          tensor_internal_hom_to_iterated_internal_hom_f K L M j := by
  sorry

section

variable [∀ K L : CochainComplex (ModuleCat R) ℤ, HasTensor K L]

/-- Lemma 15.72.6: there is a canonical morphism from the total tensor complex
`Tot(⟪L, M⟫ ⊗ K)` to the iterated internal-Hom complex `⟪⟪K, L⟫, M⟫`. -/
noncomputable def tensor_internal_hom_to_iterated_internal_hom
    (K L M : CpxR) :
    (⟪L, M⟫ ⊗ K) ⟶ ⟪⟪K, L⟫, M⟫ :=
  { f := tensor_internal_hom_to_iterated_internal_hom_f K L M
    comm' := tensor_internal_hom_to_iterated_internal_hom_f_comm K L M }

/-- The comparison morphism of Lemma 15.72.6 is functorial in `K`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_K
    {K₁ K₂ L M : CpxR} (α : K₁ ⟶ K₂) :
    CommSq
      (tensorHom (𝟙 (⟪L, M⟫)) α)
      (tensor_internal_hom_to_iterated_internal_hom K₁ L M)
      (tensor_internal_hom_to_iterated_internal_hom K₂ L M)
      (module_complex_internal_homMap (module_complex_internal_homMap α (𝟙 L)) (𝟙 M)) := by
  sorry

/-- The comparison morphism of Lemma 15.72.6 is functorial in `L`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_L
    (K : CpxR) {L₁ L₂ M : CpxR} (β : L₁ ⟶ L₂) :
    CommSq
      (tensorHom (module_complex_internal_homMap β (𝟙 M)) (𝟙 K))
      (tensor_internal_hom_to_iterated_internal_hom K L₂ M)
      (tensor_internal_hom_to_iterated_internal_hom K L₁ M)
      (module_complex_internal_homMap (module_complex_internal_homMap (𝟙 K) β) (𝟙 M)) := by
  sorry

/-- The comparison morphism of Lemma 15.72.6 is functorial in `M`. -/
theorem tensor_internal_hom_to_iterated_internal_hom_natural_M
    (K L : CpxR) {M₁ M₂ : CpxR} (γ : M₁ ⟶ M₂) :
    CommSq
      (tensorHom (module_complex_internal_homMap (𝟙 L) γ) (𝟙 K))
      (tensor_internal_hom_to_iterated_internal_hom K L M₁)
      (tensor_internal_hom_to_iterated_internal_hom K L M₂)
      (module_complex_internal_homMap (𝟙 ⟪K, L⟫) γ) := by
  sorry

end

end
