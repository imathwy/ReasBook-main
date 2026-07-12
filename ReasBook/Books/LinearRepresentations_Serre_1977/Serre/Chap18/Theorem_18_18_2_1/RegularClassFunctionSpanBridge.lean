import Mathlib
import LinearRepresentations_Serre_1977.Chap12.CharacterRingOverFieldScalarExtension
import LinearRepresentations_Serre_1977.Chap18.Proposition_18_18_1_2
import LinearRepresentations_Serre_1977.Chap18.Remark_18_18_1_3
import LinearRepresentations_Serre_1977.Chap18.Theorem_18_18_2_1.RegularConjClassCore

noncomputable section

universe u x

open CategoryTheory

namespace Representation

section

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {K : Type u} [Field K]
variable {G : Type u} [Group G] [Finite G]
variable {ι : Type x}

section ExtensionToSpanReduction

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
variable [IsAlgClosed (IsLocalRing.ResidueField A)] [CharP (IsLocalRing.ResidueField A) p]

/-- Helper for Theorem 18-18.2-1: the descended `p`-regular lift depends only on the underlying
class function, not on the chosen proof of conjugacy invariance. -/
private theorem pRegularLift_eq_of_isClassFunction_local
    {f : G → K}
    (hf₁ hf₂ : _root_.IsClassFunction f) :
    IsClassFunction.pRegularLift (G := G) (p := p) hf₁ =
      IsClassFunction.pRegularLift (G := G) (p := p) hf₂ := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate both descended lifts at the same regular representative.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) hf₁ c = f s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf₁ s)
    _ = IsClassFunction.pRegularLift (G := G) (p := p) hf₂ c := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf₂ s).symm

/-- Helper for Theorem 18-18.2-1: descending the zero class function gives the zero function on
`PRegularConjClass G p`. -/
private theorem pRegularLift_zero_local
    (hzero : _root_.IsClassFunction (0 : G → K)) :
    IsClassFunction.pRegularLift (G := G) (p := p) hzero = 0 := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- The descended zero class function still evaluates to zero on every regular representative.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) hzero c = (0 : G → K) s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hzero s)
    _ = 0 := by
      simp

/-- Helper for Theorem 18-18.2-1: `pRegularLift` is additive on class functions. -/
private theorem pRegularLift_add_local
    {f g : G → K}
    (hf : _root_.IsClassFunction f)
    (hg : _root_.IsClassFunction g)
    (hfg : _root_.IsClassFunction (f + g)) :
    IsClassFunction.pRegularLift (G := G) (p := p) hfg =
      IsClassFunction.pRegularLift (G := G) (p := p) hf +
        IsClassFunction.pRegularLift (G := G) (p := p) hg := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate the descended sum on one representative and reduce to pointwise addition upstairs.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) hfg c = (f + g) s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hfg s)
    _ = f s + g s := by
      rfl
    _ =
        (IsClassFunction.pRegularLift (G := G) (p := p) hf +
          IsClassFunction.pRegularLift (G := G) (p := p) hg) c := by
      simpa [Pi.add_apply, hs] using
        congrArg₂ (· + ·)
          (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf s).symm
          (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hg s).symm

/-- Helper for Theorem 18-18.2-1: `pRegularLift` commutes with scalar multiplication on class
functions. -/
private theorem pRegularLift_smul_local
    (a : K)
    {f : G → K}
    (hf : _root_.IsClassFunction f)
    (haf : _root_.IsClassFunction (a • f)) :
    IsClassFunction.pRegularLift (G := G) (p := p) haf =
      a • IsClassFunction.pRegularLift (G := G) (p := p) hf := by
  funext c
  let s := PRegularConjClass.representative (G := G) (p := p) c
  have hs : PRegularConjClass.ofSubtype (G := G) p s = c := by
    apply Subtype.ext
    simpa [s] using PRegularConjClass.mk_representative (G := G) (p := p) c
  -- Evaluate the descended scalar multiple on one representative and reduce to pointwise scalar
  -- multiplication upstairs.
  calc
    IsClassFunction.pRegularLift (G := G) (p := p) haf c = (a • f) s := by
      simpa [hs] using
        (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) haf s)
    _ = a * f s := by
      rfl
    _ = (a • IsClassFunction.pRegularLift (G := G) (p := p) hf) c := by
      simpa [Pi.smul_apply, hs] using
        congrArg (a • ·)
          (IsClassFunction.pRegularLift_ofSubtype (G := G) (p := p) hf s).symm

/-- Helper for Theorem 18-18.2-1: the ordinary character of a finite-dimensional `K[G]`-module is
still a bundled class function on `G`. -/
private theorem ordinaryCharacter_mem_classFunctionSubmodule
    (X : FDRep K G) :
    X.character ∈ classFunctionSubmodule K G := by
  -- Repackage the ordinary character using its conjugacy invariance.
  refine (mem_classFunctionSubmodule_iff K _).2 ?_
  refine ⟨?_⟩
  intro s t hst
  rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
  have hconj : t = (a : G) * s * (a : G)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).2
    simpa [mul_assoc] using ha.eq.symm
  rw [hconj]
  exact (X.char_conj s a).symm

/-- Helper for Theorem 18-18.2-1: bundle an honest ordinary character as an element of the class
function submodule on `G`. -/
private abbrev ordinaryCharacterClassFunction
    (X : FDRep K G) : classFunctionSubmodule K G :=
  ⟨X.character, ordinaryCharacter_mem_classFunctionSubmodule (K := K) (G := G) X⟩

/-- Helper for Theorem 18-18.2-1: if Serre's bundled zero-extension already lies in the span of
bundled honest ordinary characters, then the underlying unbundled extension lies in the span of the
corresponding raw characters. -/
private theorem regularClassFunctionExtension_mem_span_honest_characters_of_bundled_span_local
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtensionClassFunction (G := G) (p := p) f ∈
        Submodule.span K
          (Set.range fun X : FDRep K G ↦
            ordinaryCharacterClassFunction (K := K) (G := G) X)) :
    regularClassFunctionExtension (G := G) (p := p) f ∈
      Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } := by
  let Sfun : Set (G → K) := { ψ : G → K | ∃ X : FDRep K G, ψ = X.character }
  -- Forget the bundled span witness to raw functions once, rather than reopening the same
  -- induction inside every downstream regular-class-function argument.
  change
    ((regularClassFunctionExtensionClassFunction (G := G) (p := p) f :
        classFunctionSubmodule K G) : G → K) ∈ Submodule.span K Sfun
  refine
    Submodule.span_induction
      (p := fun φ (_hφ :
        φ ∈ Submodule.span K
          (Set.range fun X : FDRep K G ↦
            ordinaryCharacterClassFunction (K := K) (G := G) X)) ↦
        ((φ : classFunctionSubmodule K G) : G → K) ∈ Submodule.span K Sfun)
      ?_ ?_ ?_ ?_ hExtension
  · intro φ hφ
    rcases hφ with ⟨X, rfl⟩
    refine Submodule.subset_span ?_
    exact ⟨X, rfl⟩
  · simpa using (Submodule.zero_mem (Submodule.span K Sfun))
  · intro φ ψ hφ hψ hφ_mem hψ_mem
    simpa using Submodule.add_mem (Submodule.span K Sfun) hφ_mem hψ_mem
  · intro a φ hφ hφ_mem
    simpa using Submodule.smul_mem (Submodule.span K Sfun) a hφ_mem

/-- Helper for Theorem 18-18.2-1: once Serre's zero-extension lies in the span of honest ordinary
characters upstairs, the Brauer characters already span all functions on `PRegularConjClass G p`.
This public theorem is the exact Serre part `(b)` bridge from an upstairs honest-character span
witness to the downstairs Brauer-character span. -/
theorem
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_of_extension_span_local
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtensionClassFunction (G := G) (p := p) f ∈
        Submodule.span K
          (Set.range fun X : FDRep K G ↦
            ordinaryCharacterClassFunction (K := K) (G := G) X)) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  -- Forget the bundled honest-character span witness once, then descend it through the Brauer
  -- decomposition bridge on `PRegularConjClass G p`.
  have hExtension_fun :
      regularClassFunctionExtension (G := G) (p := p) f ∈
        Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } :=
    regularClassFunctionExtension_mem_span_honest_characters_of_bundled_span_local
      (G := G) (p := p) (K := K) f hExtension
  have hmem :
      IsClassFunction.pRegularLift
          (G := G) (p := p)
          (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) ∈
        Submodule.span K
          (Set.range fun i ↦
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
              (PrimeToPRoot.toFieldLift lift)) :=
    pRegularLift_mem_span_of_complete_family_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f)
      hExtension_fun
  -- Serre's extension-restriction identity turns the descended span witness back into the
  -- original regular class function.
  simpa [pRegularLift_regularClassFunctionExtension (G := G) (p := p) f] using hmem

/-- Helper for Theorem 18-18.2-1: once Serre's zero-extension lies in the span of honest ordinary
characters upstairs, the Brauer characters already span all functions on `PRegularConjClass G p`.
-/
private theorem span_irreducibleModularCharacters_eq_top_of_complete_family_of_extension_span_local
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hExtension :
      ∀ f : PRegularConjClass G p → K,
        regularClassFunctionExtensionClassFunction (G := G) (p := p) f ∈
          Submodule.span K
            (Set.range fun X : FDRep K G ↦
              ordinaryCharacterClassFunction (K := K) (G := G) X)) :
    Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
      ⊤ := by
  apply top_unique
  intro f _
  -- Reduce the `top` claim to the one-function descent statement above, so the source route for
  -- Serre part `(b)` is recorded once and reused.
  exact
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_of_extension_span_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete f (hExtension f)

/-- Helper for Theorem 18-18.2-1: an ordinary virtual character already lies in the `K`-span of
honest ordinary characters. -/
private theorem characterRing_mem_span_fdRep_characters_local
    [CharZero K]
    {f : G → K} (hf : f ∈ R[K](G)) :
    f ∈ Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } := by
  let SInt : Set (G → K) :=
    { ψ : G → K |
        ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V)
          (_ : FiniteDimensional K V) (ρ : Representation K G V), ψ = ρ.character }
  have hspanInt :
      f ∈ Submodule.span ℤ SInt := by
    -- First use the Chapter `12` character-ring owner, which records every virtual character as
    -- an integral combination of honest ordinary characters.
    simpa [SInt] using
      (Representation.characterRing_mem_span_honest_characters
        (K := K) (G := G) f hf)
  -- Then reinterpret each honest representation as an `FDRep` and enlarge the coefficient ring
  -- from `ℤ` to `K`.
  refine
    Submodule.span_induction
      (s := SInt)
      (p := fun g _ ↦
        g ∈ Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character })
      ?_ ?_ ?_ ?_ hspanInt
  · intro ψ hψ
    rcases hψ with ⟨V, _instAddCommGroupV, _instModuleV, _instFiniteDimensionalV, ρ, rfl⟩
    exact Submodule.subset_span ⟨FDRep.of ρ, rfl⟩
  · exact Submodule.zero_mem _
  · intro g h _ _ hg hh
    exact Submodule.add_mem _ hg hh
  · intro n g _ hg
    -- Scalar extension from `ℤ` to `K` is harmless because the target is already a `K`-submodule.
    simpa using
      (Submodule.smul_mem
        (Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character })
        (n : K) hg)

/-- Helper for Theorem 18-18.2-1: any function in Serre's field-level owner `R_K(G)` already lies
in the ambient `K`-span of honest ordinary characters. This is the exact part `(b)` adapter before
descending those ordinary characters to Brauer characters on `PRegularConjClass G p`. -/
theorem function_mem_span_fdRep_characters_of_mem_characterRingOverField_local
    [CharZero K]
    {f : G → K} (hf : f ∈ R[K](G)) :
    f ∈ Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } := by
  -- Reuse the already-proved Chapter `12` expansion of a virtual character into honest ordinary
  -- characters; this public wrapper exposes the exact field-level owner used in Serre part `(b)`.
  exact characterRing_mem_span_fdRep_characters_local (G := G) (K := K) hf

/-- Helper for Theorem 18-18.2-1: any function in Serre's scalar-extension owner
`A ⊗ R_K(G)` already lies in the ambient `K`-span of honest ordinary characters. -/
private theorem
    function_mem_span_fdRep_characters_of_mem_characterRingOverFieldAlgebraScalarExtension_local
    [CharZero K]
    {f : G → K} (hf : f ∈ A ⊗R[K](G)) :
    f ∈ Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } := by
  let S := (((R[K](G)).toSubmodule : Submodule ℤ (G → K)) : Set (G → K))
  let T : Submodule K (G → K) :=
    Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character }
  -- Route correction: part `(b)` only needs the source owner `A ⊗ R_K(G)` to land in the
  -- ambient `K`-span of honest characters, so the scalar-extension induction is isolated here.
  refine
    Submodule.span_induction
      (s := S)
      (p := fun g _ ↦ g ∈ T)
      ?_ ?_ ?_ ?_ hf
  · intro χ hχ
    have hχ' : χ ∈ R[K](G) := by
      simpa [S] using hχ
    exact characterRing_mem_span_fdRep_characters_local (G := G) (K := K) hχ'
  · exact Submodule.zero_mem T
  · intro g h _ _ hg hh
    exact Submodule.add_mem T hg hh
  · intro a g _ hg
    simpa [T, Algebra.smul_def] using Submodule.smul_mem T (algebraMap A K a) hg

/-- Helper for Theorem 18-18.2-1: if a class function already lies in the raw `K`-span of honest
ordinary characters, then its bundled class-function owner lies in the corresponding bundled span.
-/
private theorem classFunction_mem_bundled_span_honest_characters_of_raw_span_local
    {f : G → K}
    (hfClass : _root_.IsClassFunction f)
    (hf :
      f ∈ Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character }) :
    (⟨f, (mem_classFunctionSubmodule_iff K f).2 hfClass⟩ : classFunctionSubmodule K G) ∈
      Submodule.span K
        (Set.range fun X : FDRep K G ↦
          ordinaryCharacterClassFunction (K := K) (G := G) X) := by
  let Sfun : Set (G → K) := { ψ : G → K | ∃ X : FDRep K G, ψ = X.character }
  have hspan :
      ∀ {g : G → K} (hg : g ∈ Submodule.span K Sfun),
        ∃ hgClass : _root_.IsClassFunction g,
          (⟨g, (mem_classFunctionSubmodule_iff K g).2 hgClass⟩ : classFunctionSubmodule K G) ∈
            Submodule.span K
              (Set.range fun X : FDRep K G ↦
                ordinaryCharacterClassFunction (K := K) (G := G) X) := by
    intro g hg
    refine
      Submodule.span_induction
        (s := Sfun)
        (p := fun g _ ↦
          ∃ hgClass : _root_.IsClassFunction g,
            (⟨g, (mem_classFunctionSubmodule_iff K g).2 hgClass⟩ : classFunctionSubmodule K G) ∈
              Submodule.span K
                (Set.range fun X : FDRep K G ↦
                  ordinaryCharacterClassFunction (K := K) (G := G) X))
        ?_ ?_ ?_ ?_ hg
    · intro ψ hψ
      rcases hψ with ⟨X, rfl⟩
      have hψClass : _root_.IsClassFunction X.character := by
        refine ⟨?_⟩
        intro s t hst
        rcases (ConjClasses.mk_eq_mk_iff_isConj.mp hst) with ⟨a, ha⟩
        have hconj : t = (a : G) * s * (a : G)⁻¹ := by
          apply (eq_mul_inv_iff_mul_eq).2
          simpa [mul_assoc] using ha.eq.symm
        rw [hconj]
        exact (X.char_conj s a).symm
      refine ⟨hψClass, ?_⟩
      exact Submodule.subset_span ⟨X, rfl⟩
    · refine ⟨by simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K))), ?_⟩
      exact Submodule.zero_mem _
    · intro g h _ _ ihg ihh
      rcases ihg with ⟨hgClass, hg_mem⟩
      rcases ihh with ⟨hhClass, hh_mem⟩
      have hsumClass : _root_.IsClassFunction (g + h) := by
        refine ⟨?_⟩
        intro s t hst
        exact congrArg₂ (· + ·) (hgClass.eq_of_mk_eq hst) (hhClass.eq_of_mk_eq hst)
      refine ⟨hsumClass, ?_⟩
      simpa using Submodule.add_mem _ hg_mem hh_mem
    · intro a g _ ihg
      rcases ihg with ⟨hgClass, hg_mem⟩
      have hsmulClass : _root_.IsClassFunction (a • g) := by
        refine ⟨?_⟩
        intro s t hst
        exact congrArg (a • ·) (hgClass.eq_of_mk_eq hst)
      refine ⟨hsmulClass, ?_⟩
      simpa using Submodule.smul_mem _ a hg_mem
  rcases hspan hf with ⟨hfClass', hf_mem⟩
  -- Proof irrelevance identifies the rebundled class function with the original owner.
  simpa using hf_mem

/-- Helper for Theorem 18-18.2-1: once Serre's zero-extension is an ordinary virtual character
upstairs, its bundled class-function owner already lies in the span of bundled honest ordinary
characters. -/
private theorem regularClassFunctionExtensionClassFunction_mem_span_honest_characters_of_extension_mem_characterRing_local
    [CharZero K]
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtension (G := G) (p := p) f ∈ R[K](G)) :
    regularClassFunctionExtensionClassFunction (G := G) (p := p) f ∈
      Submodule.span K
        (Set.range fun X : FDRep K G ↦
          ordinaryCharacterClassFunction (K := K) (G := G) X) := by
  have hraw :
      regularClassFunctionExtension (G := G) (p := p) f ∈
        Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } :=
    characterRing_mem_span_fdRep_characters_local
      (G := G) (K := K) hExtension
  -- Rebundle the raw span witness to the exact source owner used in the spanning descent.
  exact
    classFunction_mem_bundled_span_honest_characters_of_raw_span_local
      (G := G) (K := K)
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f)
      hraw

/-- Helper for Theorem 18-18.2-1: once Serre's zero-extension lies in the Chapter `12`
scalar-extension owner `A ⊗ R_K(G)`, its bundled class-function owner already lies in the span of
bundled honest ordinary characters. -/
private theorem
    regularClassFunctionExtensionClassFunction_mem_span_honest_characters_of_extension_mem_characterRingScalarExtension_local
    [CharZero K]
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtension (G := G) (p := p) f ∈ A ⊗R[K](G)) :
    regularClassFunctionExtensionClassFunction (G := G) (p := p) f ∈
      Submodule.span K
        (Set.range fun X : FDRep K G ↦
          ordinaryCharacterClassFunction (K := K) (G := G) X) := by
  have hraw :
      regularClassFunctionExtension (G := G) (p := p) f ∈
        Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } :=
    function_mem_span_fdRep_characters_of_mem_characterRingOverFieldAlgebraScalarExtension_local
      (A := A) (K := K) (G := G) hExtension
  -- Rebundle the scalar-extension span witness to the bundled class-function owner.
  exact
    classFunction_mem_bundled_span_honest_characters_of_raw_span_local
      (G := G) (K := K)
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f)
      hraw

/-- Helper for Theorem 18-18.2-1: if Serre's zero-extension is known to be an ordinary virtual
character upstairs, then the Brauer characters already span all regular class functions. -/
private theorem
    span_irreducibleModularCharacters_eq_top_of_complete_family_of_extension_mem_characterRing_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hExtension :
      ∀ f : PRegularConjClass G p → K,
        regularClassFunctionExtension (G := G) (p := p) f ∈ R[K](G)) :
    Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
      ⊤ := by
  -- Route correction: the only remaining input is the source witness that each zero-extension is
  -- an ordinary virtual character upstairs; the bundled honest-character span step is now cached
  -- in `regularClassFunctionExtensionClassFunction_mem_span_honest_characters_of_extension_mem_characterRing_local`.
  refine
    span_irreducibleModularCharacters_eq_top_of_complete_family_of_extension_span_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete ?_
  intro f
  exact
    regularClassFunctionExtensionClassFunction_mem_span_honest_characters_of_extension_mem_characterRing_local
      (G := G) (p := p) (K := K) f (hExtension f)

/-- Helper for Theorem 18-18.2-1: under the source coefficient-ring hypotheses, once Serre's
zero-extension of one regular class function is known to be an ordinary virtual character on `G`,
the corresponding regular class function already lies in the Brauer-character span downstairs. -/
private theorem
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_of_extension_mem_characterRing_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtension (G := G) (p := p) f ∈ R[K](G)) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  have hraw :
      regularClassFunctionExtension (G := G) (p := p) f ∈
        Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } :=
    characterRing_mem_span_fdRep_characters_local
      (G := G) (K := K) hExtension
  have hmem :
      IsClassFunction.pRegularLift
          (G := G) (p := p)
          (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) ∈
        Submodule.span K
          (Set.range fun i ↦
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
              (PrimeToPRoot.toFieldLift lift)) :=
    -- First expand the ordinary virtual character upstairs into honest ordinary characters, then
    -- descend each of those restrictions through the already-proved decomposition bridge.
    pRegularLift_mem_span_of_complete_family_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f)
      hraw
  -- Serre's extension-restriction identity turns the descended span witness back into `f`.
  simpa [pRegularLift_regularClassFunctionExtension (G := G) (p := p) f] using hmem

/-- Helper for Theorem 18-18.2-1: under the source coefficient-ring hypotheses, once Serre's
zero-extension of one regular class function is known to be an ordinary virtual character on `G`,
the corresponding regular class function already lies in the Brauer-character span downstairs. This
public theorem is the exact field-level descent used in Serre part `(b)`. -/
theorem
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_of_extension_mem_characterRingOverField_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtension (G := G) (p := p) f ∈ R[K](G)) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  -- Re-export the proved field-owner descent so the target theorem can depend on the precise
  -- source route `regularClassFunctionExtension f ∈ R_K(G)`.
  exact
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_of_extension_mem_characterRing_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete f hExtension

/-- Helper for Theorem 18-18.2-1: Serre part `(b)` only needs the weaker public hypothesis that
the zero-extension lies in the ambient `K`-span generated by `R_K(G)`. This bridge records the
source-faithful descent from that ordinary-character span upstairs to the Brauer-character span on
`PRegularConjClass G p`. -/
theorem
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_extension_characterRing_span_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtension (G := G) (p := p) f ∈
        Submodule.span K (R[K](G) : Set (G → K))) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  let T : Submodule K (PRegularConjClass G p → K) :=
    Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift))
  -- Route correction: Serre's part `(b)` uses only a finite linear combination of ordinary
  -- characters upstairs, so we descend from the public span `Submodule.span K (R[K](G))`
  -- instead of the over-strong hypothesis `regularClassFunctionExtension f ∈ R[K](G)`.
  have hdescend :
      ∀ {g : G → K},
        g ∈ Submodule.span K (R[K](G) : Set (G → K)) →
          ∃ hgClass : _root_.IsClassFunction g,
            IsClassFunction.pRegularLift (G := G) (p := p) hgClass ∈ T := by
    intro g hg
    refine
      Submodule.span_induction
        (s := (R[K](G) : Set (G → K)))
        (p := fun ψ _ ↦
          ∃ hψClass : _root_.IsClassFunction ψ,
            IsClassFunction.pRegularLift (G := G) (p := p) hψClass ∈ T)
        ?_ ?_ ?_ ?_ hg
    · intro ψ hψ
      -- Each generator in `R_K(G)` descends by the already-proved field-level bridge.
      let hψClass : _root_.IsClassFunction ψ :=
        Representation.isClassFunction_of_mem_characterRingOverField ψ hψ
      refine ⟨hψClass, ?_⟩
      exact
        pRegularLift_mem_span_of_complete_family_local
          (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete
          hψClass
          (function_mem_span_fdRep_characters_of_mem_characterRingOverField_local
            (G := G) (K := K) hψ)
    · -- The zero function descends to the zero vector in the Brauer-character span.
      refine ⟨by simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K))), ?_⟩
      rw [pRegularLift_zero_local (G := G) (p := p) (K := K)
        (by simpa using (inferInstance : _root_.IsClassFunction (fun _ : G ↦ (0 : K))))]
      exact Submodule.zero_mem T
    · intro ψ χ _ _ hψ hχ
      -- Span descent is additive because `pRegularLift` commutes with addition.
      rcases hψ with ⟨hψClass, hψ_mem⟩
      rcases hχ with ⟨hχClass, hχ_mem⟩
      have hsumClass : _root_.IsClassFunction (ψ + χ) := by
        refine ⟨?_⟩
        intro s t hst
        exact congrArg₂ (· + ·) (hψClass.eq_of_mk_eq hst) (hχClass.eq_of_mk_eq hst)
      refine ⟨hsumClass, ?_⟩
      rw [pRegularLift_add_local (G := G) (p := p) (K := K) hψClass hχClass hsumClass]
      exact Submodule.add_mem T hψ_mem hχ_mem
    · intro a ψ _ hψ
      -- Span descent is `K`-linear because `pRegularLift` commutes with scalar multiplication.
      rcases hψ with ⟨hψClass, hψ_mem⟩
      have hsmulClass : _root_.IsClassFunction (a • ψ) := by
        refine ⟨?_⟩
        intro s t hst
        exact congrArg (a • ·) (hψClass.eq_of_mk_eq hst)
      refine ⟨hsmulClass, ?_⟩
      rw [pRegularLift_smul_local (G := G) (p := p) (K := K) a hψClass hsmulClass]
      exact Submodule.smul_mem T a hψ_mem
  -- Apply the span descent to the zero-extension itself, then identify its `p`-regular lift with
  -- the original function `f`.
  rcases hdescend hExtension with ⟨hgClass, hg_mem⟩
  have hEq :
      IsClassFunction.pRegularLift
          (G := G) (p := p)
          (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) =
        IsClassFunction.pRegularLift (G := G) (p := p) hgClass :=
    pRegularLift_eq_of_isClassFunction_local
      (G := G) (p := p) (K := K)
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) hgClass
  have hcanon :
      IsClassFunction.pRegularLift
          (G := G) (p := p)
          (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) ∈ T := by
    simpa [hEq] using hg_mem
  simpa [pRegularLift_regularClassFunctionExtension (G := G) (p := p) f] using hcanon

/-- Helper for Theorem 18-18.2-1: once Serre's zero-extension lies in the scalar-extension owner
`A ⊗ R_K(G)`, the regular class function already lies in the Brauer-character span downstairs. -/
theorem
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_of_extension_mem_characterRingScalarExtension_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (f : PRegularConjClass G p → K)
    (hExtension :
      regularClassFunctionExtension (G := G) (p := p) f ∈ A ⊗R[K](G)) :
    f ∈ Submodule.span K
      (Set.range fun i ↦
        FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
          (PrimeToPRoot.toFieldLift lift)) := by
  have hraw :
      regularClassFunctionExtension (G := G) (p := p) f ∈
        Submodule.span K { ψ : G → K | ∃ X : FDRep K G, ψ = X.character } :=
    function_mem_span_fdRep_characters_of_mem_characterRingOverFieldAlgebraScalarExtension_local
      (A := A) (K := K) (G := G) hExtension
  have hmem :
      IsClassFunction.pRegularLift
          (G := G) (p := p)
          (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f) ∈
        Submodule.span K
          (Set.range fun i ↦
            FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
              (PrimeToPRoot.toFieldLift lift)) :=
    -- First expand the scalar-extended owner upstairs into honest ordinary characters, then
    -- descend each restricted character through the decomposition bridge.
    pRegularLift_mem_span_of_complete_family_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete
      (regularClassFunctionExtension_isClassFunction (G := G) (p := p) f)
      hraw
  -- Serre's extension-restriction identity turns the descended span witness back into `f`.
  simpa [pRegularLift_regularClassFunctionExtension (G := G) (p := p) f] using hmem

/-- Helper for Theorem 18-18.2-1: once every zero-extension lies in the public span
`Submodule.span K (R_K(G))`, Serre part `(b)` already yields the full spanning statement on
`PRegularConjClass G p`. This keeps the remaining mixed-character blocker at the correct public
API boundary. -/
theorem
    span_irreducibleModularCharacters_eq_top_of_complete_family_extension_characterRing_span_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hExtension :
      ∀ f : PRegularConjClass G p → K,
        regularClassFunctionExtension (G := G) (p := p) f ∈
          Submodule.span K (R[K](G) : Set (G → K))) :
    Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
      ⊤ := by
  apply top_unique
  intro f _
  -- Reduce the top statement to the one-function span bridge just proved above.
  exact
    regularClassFunction_mem_span_irreducibleModularCharacters_of_complete_family_extension_characterRing_span_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete f (hExtension f)

/-- Helper for Theorem 18-18.2-1: if every zero-extension lies in `A ⊗ R_K(G)`, then the Brauer
characters of a complete irreducible family span all regular class functions. -/
private theorem
    span_irreducibleModularCharacters_eq_top_of_complete_family_of_extension_mem_characterRingScalarExtension_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hExtension :
      ∀ f : PRegularConjClass G p → K,
        regularClassFunctionExtension (G := G) (p := p) f ∈ A ⊗R[K](G)) :
    Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
      ⊤ := by
  -- The Chapter `12` scalar-extension owner is now consumed only through the rebundled honest
  -- ordinary-character span helper above.
  refine
    span_irreducibleModularCharacters_eq_top_of_complete_family_of_extension_span_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete ?_
  intro f
  exact
    regularClassFunctionExtensionClassFunction_mem_span_honest_characters_of_extension_mem_characterRingScalarExtension_local
      (A := A) (G := G) (p := p) (K := K) f (hExtension f)

/-- Helper for Theorem 18-18.2-1: if every zero-extension is an ordinary virtual character in
`R_K(G)`, then the Brauer characters of a complete irreducible family span all regular class
functions. This public wrapper records the exact field-level owner statement for Serre part `(b)`.
-/
theorem
    span_irreducibleModularCharacters_eq_top_of_complete_family_of_extension_mem_characterRingOverField_local
    [CharZero K]
    [Fact p.Prime]
    (lift : PrimeToPRoot p (IsLocalRing.ResidueField A) →* Kˣ)
    (hred : ∀ x : PrimeToPRoot p (IsLocalRing.ResidueField A), ∃ a : A,
      algebraMap A K a = ((lift x : Kˣ) : K) ∧
        IsLocalRing.residue A a = ((x : (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A))
    (hω : ∀ s : G, IsPRegular p s → ∃ ω : K, IsPrimitiveRoot ω (orderOf s))
    (E : ι → FDRep (IsLocalRing.ResidueField A) G)
    (hE_pairwise : PairwiseNonisomorphic E)
    (hE_complete : IsCompleteIrreducibleFamily E)
    (hExtension :
      ∀ f : PRegularConjClass G p → K,
        regularClassFunctionExtension (G := G) (p := p) f ∈ R[K](G)) :
    Submodule.span K
        (Set.range fun i ↦
          FDRep.modularCharacterOnPRegularConjClass (p := p) (E i)
            (PrimeToPRoot.toFieldLift lift)) =
      ⊤ := by
  -- Re-export the proved field-owner spanning step so later target wrappers only have to supply
  -- Serre's owner witness `regularClassFunctionExtension f ∈ R_K(G)`.
  exact
    span_irreducibleModularCharacters_eq_top_of_complete_family_of_extension_mem_characterRing_local
      (p := p) (A := A) (K := K) (G := G) lift hred hω E hE_pairwise hE_complete hExtension

end ExtensionToSpanReduction

end

end Representation
