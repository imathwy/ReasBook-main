import StacksProject_2024.Chap15.Remark_15_96_5
import StacksProject_2024.Chap15.Lemma_15_94_9
import StacksProject_2024.Chap15.PrincipalIdeal
import StacksProject_2024.Chap20.IdealSheafStalkIdeal
import StacksProject_2024.Chap20.Lemma_20_26_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped PrincipalIdeal

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
local notation "ModX" => RingedSpace.Modules X
local notation "𝒪X" => (SheafOfModules.unit (RingedSpace.ringCatSheaf X) : ModX)
variable {I : Subobject 𝒪X}

/- Domain-style sampling:
- primary domain: stalkwise Berthelot-Ogus constructions for complexes of `𝒪_X`-modules;
- sampled owner declarations:
  `CategoryTheory.Subobject`,
  `RingedSpace.stalkComplex`,
  `RingedSpace.idealSheafStalkIdeal`,
  `NatModuleCochainComplex`,
  `etaFDegreeSubmodule`,
  `η[f]`;
- best owner abstraction: the chapter-15 owner `η[f]` on `NatModuleCochainComplex`, with the
  ringed-space side entering only through the stalk complex `stalkNatComplex K x`;
- primitive data: the stalk complex `stalkNatComplex K x` and the ideal powers
  `idealSheafStalkIdeal I x ^ n`;
- derived API: the induced source-facing stalk complex `etaIdealStalkComplex I K x` and the
  comparison isomorphism to `η[f]`, with the degreewise ideal-power submodules kept internal.

Source/core/bridge triage:
- `source-facing`: `etaIdealStalkComplex` and the generator-based comparison in
  Lemma `20.55.4`;
- `core/canonical`: `η[f]` from Chapter 15 together with the Chapter 20 owners
  `RingedSpace.stalkComplex` and `RingedSpace.idealSheafStalkIdeal`;
- `bridge/view`: `stalkNatComplex`, which restricts the canonical stalk complex of
  `K.extend ComplexShape.embeddingUpNat` to the Chapter 15 owner domain. -/

/-- The nonnegative-degree restriction of the canonical stalk complex of
`K.extend ComplexShape.embeddingUpNat`. This is the Chapter 15 input complex used to compare the
stalkwise construction attached to `𝓘` with `η[f]`. -/
abbrev stalkNatComplex (K : CochainComplex ModX ℕ) (x : X) :
    NatModuleCochainComplex (X.presheaf.stalk x) :=
  (stalkComplex (K.extend ComplexShape.embeddingUpNat) x).restriction ComplexShape.embeddingUpNat

/-- The source-facing nonnegative stalk complex is exactly the restriction of the canonical
`ℤ`-indexed stalk complex along `ComplexShape.embeddingUpNat`. -/
theorem stalkNatComplex_eq_restriction (K : CochainComplex ModX ℕ) (x : X) :
    stalkNatComplex K x =
      (stalkComplex (K.extend ComplexShape.embeddingUpNat) x).restriction
        ComplexShape.embeddingUpNat :=
  rfl

section StalkComparison

variable (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X)

private def etaIdealStalkDegreeSubmodule
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X) (n : ℕ) :
    Submodule (X.presheaf.stalk x) ((stalkNatComplex K x).X n) :=
  ((idealSheafStalkIdeal I x ^ n) •
      (⊤ : Submodule (X.presheaf.stalk x) ((stalkNatComplex K x).X n))) ⊓
    (((idealSheafStalkIdeal I x ^ (n + 1)) •
      (⊤ : Submodule (X.presheaf.stalk x) ((stalkNatComplex K x).X (n + 1)))).comap
        ((stalkNatComplex K x).d n (n + 1)).hom)

-- Proof sketch: the differential is linear, so it sends the `𝓘_x^n`-multiple condition
-- into the `𝓘_x^(n + 1)`-multiple condition, and the second defining condition advances
-- by one degree because successive differentials compose to zero.
/-- The stalk differential sends the degree-`n` Berthelot-Ogus submodule into degree `n + 1`. -/
private theorem etaIdealStalkDifferential_mem
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X) (n : ℕ) :
    ∀ s : etaIdealStalkDegreeSubmodule I K x n,
      (stalkNatComplex K x).d n (n + 1) s ∈ etaIdealStalkDegreeSubmodule I K x (n + 1) := by
  intro s
  -- The target is an intersection: the first component is already part of the degree-`n`
  -- condition, and the second comes from `d ∘ d = 0`.
  refine ⟨?_, ?_⟩
  · simpa [etaIdealStalkDegreeSubmodule] using s.2.2
  · -- The next differential vanishes, hence it belongs to every successor ideal multiple.
    change
      (stalkNatComplex K x).d (n + 1) ((n + 1) + 1) ((stalkNatComplex K x).d n (n + 1) s) ∈
        (idealSheafStalkIdeal I x ^ ((n + 1) + 1)) •
          (⊤ : Submodule (X.presheaf.stalk x) ((stalkNatComplex K x).X ((n + 1) + 1)))
    have hzero :
        (ModuleCat.Hom.hom ((stalkNatComplex K x).d (n + 1) ((n + 1) + 1)))
            ((ConcreteCategory.hom ((stalkNatComplex K x).d n (n + 1))) s) = 0 := by
      exact LinearMap.congr_fun
        (congrArg ModuleCat.Hom.hom
          ((stalkNatComplex K x).d_comp_d n (n + 1) ((n + 1) + 1))) s
    rw [hzero]
    exact Submodule.zero_mem _

/-- The degree-`n` differential on the stalkwise Berthelot-Ogus complex attached to `𝓘`. -/
private def etaIdealStalkDifferentialLinear
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X) (n : ℕ) :
    etaIdealStalkDegreeSubmodule I K x n →ₗ[X.presheaf.stalk x]
      etaIdealStalkDegreeSubmodule I K x (n + 1) :=
  (((stalkNatComplex K x).d n (n + 1)).hom.comp
      (etaIdealStalkDegreeSubmodule I K x n).subtype).codRestrict
    (etaIdealStalkDegreeSubmodule I K x (n + 1))
    (etaIdealStalkDifferential_mem I K x n)

-- Proof sketch: the differentials are restrictions of the stalk differentials of `K`, so their
-- composite is the restriction of `d ∘ d = 0`.
/-- Two successive differentials in the stalkwise Berthelot-Ogus complex compose to zero. -/
private theorem etaIdealStalkDifferential_sq
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X) (n : ℕ) :
    ModuleCat.ofHom (etaIdealStalkDifferentialLinear I K x n) ≫
        ModuleCat.ofHom (etaIdealStalkDifferentialLinear I K x (n + 1)) =
      0 := by
  -- Forgetting the codomain restrictions reduces the claim to the ambient square-zero relation.
  ext s
  change
    (ModuleCat.Hom.hom ((stalkNatComplex K x).d (n + 1) ((n + 1) + 1)))
      ((ModuleCat.Hom.hom ((stalkNatComplex K x).d n (n + 1))) s) = 0
  exact LinearMap.congr_fun
    (congrArg ModuleCat.Hom.hom
      ((stalkNatComplex K x).d_comp_d n (n + 1) ((n + 1) + 1))) s

/-- The stalkwise Berthelot-Ogus complex attached to the ideal sheaf inclusion `𝓘 ⟶ 𝒪_X`.
This is the source-facing model for the stalk `(η_𝓘 K)_x`. -/
noncomputable def etaIdealStalkComplex
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X) :
    NatModuleCochainComplex (X.presheaf.stalk x) :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of (X.presheaf.stalk x) (etaIdealStalkDegreeSubmodule I K x n))
    (fun n ↦ ModuleCat.ofHom (etaIdealStalkDifferentialLinear I K x n))
    (fun n ↦ etaIdealStalkDifferential_sq I K x n)

section Generator

variable (f : X.presheaf.stalk x)
  (hf : principalIdeal f = idealSheafStalkIdeal I x)

/-- Helper for Lemma 20.55.4: after choosing a generator, the stalkwise ideal-power condition and
the principal-power Berthelot-Ogus condition define the same ambient membership predicate. -/
private theorem etaIdealStalkDegreeSubmodule_mem_iff
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X)
    (f : X.presheaf.stalk x)
    (hf : principalIdeal f = idealSheafStalkIdeal I x) (n : ℕ)
    (s : (stalkNatComplex K x).X n) :
    s ∈ etaIdealStalkDegreeSubmodule I K x n ↔
      s ∈ etaFDegreeSubmodule f (stalkNatComplex K x) n := by
  -- Rewrite the stalk ideal powers through the chosen generator, then normalize the principal
  -- ideal multiples to the multiplication ranges appearing in `η[f]`.
  rw [etaIdealStalkDegreeSubmodule, etaFDegreeSubmodule, ← hf]
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
  rw [← range_lsmul_eq_principalIdeal_smul_top (f ^ n)]
  rw [← range_lsmul_eq_principalIdeal_smul_top (f ^ (n + 1))]

private noncomputable def etaIdealStalkDegreeEquiv
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X)
    (f : X.presheaf.stalk x)
    (hf : principalIdeal f = idealSheafStalkIdeal I x) (n : ℕ) :
    etaIdealStalkDegreeSubmodule I K x n ≃ₗ[X.presheaf.stalk x]
      etaFDegreeSubmodule f (stalkNatComplex K x) n where
  toFun s := ⟨s, (etaIdealStalkDegreeSubmodule_mem_iff I K x f hf n s).1 s.2⟩
  invFun s := ⟨s, (etaIdealStalkDegreeSubmodule_mem_iff I K x f hf n s).2 s.2⟩
  left_inv s := by
    ext
    rfl
  right_inv s := by
    ext
    rfl
  map_add' s t := by
    ext
    rfl
  map_smul' a s := by
    ext
    rfl

/-- Helper for Lemma 20.55.4: the degreewise comparison equivalence acts as the identity on the
ambient stalk module. -/
private theorem etaIdealStalkDegreeEquiv_apply
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X)
    (f : X.presheaf.stalk x)
    (hf : principalIdeal f = idealSheafStalkIdeal I x) (n : ℕ)
    (s : etaIdealStalkDegreeSubmodule I K x n) :
    (((etaIdealStalkDegreeEquiv I K x f hf n) s :
        etaFDegreeSubmodule f (stalkNatComplex K x) n) : (stalkNatComplex K x).X n) = s := by
  rfl

private theorem etaIdealStalkDegreeEquiv_comm
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X)
    (f : X.presheaf.stalk x)
    (hf : principalIdeal f = idealSheafStalkIdeal I x) (n : ℕ) :
    ModuleCat.ofHom (etaIdealStalkDegreeEquiv I K x f hf n).toLinearMap ≫
        (η[f] (stalkNatComplex K x)).d n (n + 1) =
      (etaIdealStalkComplex I K x).d n (n + 1) ≫
        ModuleCat.ofHom (etaIdealStalkDegreeEquiv I K x f hf (n + 1)).toLinearMap := by
  -- Both sides land in the same codomain submodule, so it is enough to compare their ambient
  -- values elementwise.
  apply ModuleCat.hom_ext
  ext s
  have hd_stalk :
      (etaIdealStalkComplex I K x).d n (n + 1) =
        ModuleCat.ofHom (etaIdealStalkDifferentialLinear I K x n) := by
    simpa [etaIdealStalkComplex] using
      (CochainComplex.of_d
        (fun n ↦ ModuleCat.of (X.presheaf.stalk x) (etaIdealStalkDegreeSubmodule I K x n))
        (fun n ↦ ModuleCat.ofHom (etaIdealStalkDifferentialLinear I K x n))
        (fun n ↦ etaIdealStalkDifferential_sq I K x n)
        n)
  rw [hd_stalk]
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom]
  change
    (ModuleCat.Hom.hom ((η[f] (stalkNatComplex K x)).d n (n + 1)))
        ((etaIdealStalkDegreeEquiv I K x f hf n) s) =
      (etaIdealStalkDegreeEquiv I K x f hf (n + 1))
        ((etaIdealStalkDifferentialLinear I K x n) s)
  apply Subtype.ext
  rw [etaIdealStalkDegreeEquiv_apply I K x f hf (n + 1)
    ((etaIdealStalkDifferentialLinear I K x n) s)]
  delta etaFComplex
  rw [CochainComplex.of_d]
  change
    (ModuleCat.Hom.hom ((stalkNatComplex K x).d n (n + 1)))
        ((((etaIdealStalkDegreeEquiv I K x f hf n) s :
            etaFDegreeSubmodule f (stalkNatComplex K x) n) :
            (stalkNatComplex K x).X n)) =
      ((stalkNatComplex K x).d n (n + 1)).hom s
  rw [etaIdealStalkDegreeEquiv_apply I K x f hf n s]

end Generator

-- Proof sketch: if `𝓘_x = (f)`, then the ideal-power filtration
-- `𝓘_x^n (K_x^n)` is exactly the principal-power filtration `f^n (K_x^n)`. After
-- rewriting both degreewise submodules using the generator equation `hf`, the two complexes have
-- the same terms and the same restricted differentials.
/-- Lemma 20.55.4: let `K` be a complex of `𝒪_X`-modules. For a point `x` and a generator `f` of
the ideal stalk `𝓘_x`, the stalkwise Berthelot-Ogus complex `(η_𝓘 K)_x` is canonically
isomorphic to the local Berthelot-Ogus complex `η[f] (stalkNatComplex K x)` from More on Algebra,
Section `15.96`. -/
@[stacks 0GT6]
noncomputable def etaIdealStalkComplex_iso_etaFComplex_of_generator
    (I : Subobject 𝒪X) (K : CochainComplex ModX ℕ) (x : X) (f : X.presheaf.stalk x)
    (hf : principalIdeal f = idealSheafStalkIdeal I x) :
    etaIdealStalkComplex I K x ≅
      η[f] (stalkNatComplex K x) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (etaIdealStalkDegreeEquiv I K x f hf n).toModuleIso)
    (by
      rintro n _ rfl
      exact etaIdealStalkDegreeEquiv_comm I K x f hf n)

end StalkComparison

end AlgebraicGeometry.RingedSpace
