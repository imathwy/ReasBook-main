import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import StacksProject_2024.stacks_project.Chap20.«20_25_3_1»

noncomputable section

open CategoryTheory ComplexShape HomologicalComplex MonoidalCategory

universe u v

/- Domain-style sampling for Lemma 20.25.4:
- primary domain: the sign compatibility between cohomology boundary morphisms and cup products
  induced by compatible pairings on two short exact sequences of cochain complexes;
- sampled owner declarations:
  `CategoryTheory.ShortComplex.ShortExact.δ`,
  `HomologicalComplex.HomologySequence.δ_naturality`,
  `tensorObj_d_on_summand_eq`,
  `CategoryTheory.derivedCohomologyProduct`;
- best owner abstraction:
  `source-facing`: the cohomology identity
    `γ₁(∂ a₃ ∪ b₁) = (-1)^(n + 1) γ₃(a₃ ∪ ∂ b₁)`;
  `core/canonical`: the connecting morphisms are the owner maps `ShortComplex.ShortExact.δ`;
  `bridge/view`: there is no upstream generic owner in the project or in mathlib for the
    cohomology cup product induced by an arbitrary pairing of cochain complexes in this level of
    generality, so this file uses the explicit bridge predicates `InducesCohomologyCup` and
    `InducesCohomologyCupTo`; when a canonical induced cup product is available, the optional
    helper owner `CohomologyCupTo` packages that choice separately from the source-facing theorem;
- primitive data vs. derived API:
  the primitive data are the two short exact sequences of cochain complexes and the compatible
  pairings `γ₁`, `γ₂`, `γ₃`; the displayed signed compatibility is derived API from the
  canonical cohomology cup products packaged by `CohomologyCupTo`.

Source/core/bridge triage:
- `source-facing`: `cohomology_boundary_cup_eq_negOnePow`;
- `core/canonical`: `ShortComplex.ShortExact.δ`,
  `HomologicalComplex.HomologySequence.δ_naturality`, and `tensorObj_d_on_summand_eq`;
- `bridge/view`: `cohomologyCupOnCycles`, `cohomologyCupOnCyclesTo`,
  `InducesCohomologyCup`, `InducesCohomologyCupTo`, `CohomologyCupTo`, and `cohomologyCupTo`.
-/

section

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
variable [MonoidalPreadditive C]

variable {SF SG : ShortComplex (CochainComplex C ℤ)} (hF : SF.ShortExact) (hG : SG.ShortExact)
variable {H : CochainComplex C ℤ}

variable [HasTensor SF.X₁ SG.X₂] [HasTensor SF.X₂ SG.X₂] [HasTensor SF.X₁ SG.X₃]
variable [HasTensor SF.X₂ SG.X₁] [HasTensor SF.X₃ SG.X₁]

section

variable {K L H' : CochainComplex C ℤ} [HasTensor K L]

private theorem cohomologyCupOnCycles_d_eq_zero
    (γ : tensorObj K L ⟶ H') (p q : ℤ) :
    ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫ γ.f (p + q)) ≫
        H'.d (p + q) (p + q + 1) = 0 := by
  have hcomm :
      ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫ γ.f (p + q)) ≫
          H'.d (p + q) (p + q + 1) =
        ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫
            (tensorObj K L).d (p + q) (p + q + 1)) ≫
          γ.f (p + q + 1) := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ (((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫ t)
        (γ.comm (p + q) (p + q + 1))
  have hsum :
      ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫
          (tensorObj K L).d (p + q) (p + q + 1)) ≫ γ.f (p + q + 1) =
        ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫
            ((K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
                ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) +
              p.negOnePow •
                ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
                  ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf)))) ≫
          γ.f (p + q + 1)) := by
    simpa [Category.assoc] using
      congrArg
        (fun t ↦ ((K.iCycles p ⊗ₘ L.iCycles q) ≫ t))
        (tensorObj_d_on_summand_eq_assoc p q (γ.f (p + q + 1)))
  calc
    ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫ γ.f (p + q)) ≫
        H'.d (p + q) (p + q + 1) =
      ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫
          (tensorObj K L).d (p + q) (p + q + 1)) ≫
        γ.f (p + q + 1) := hcomm
    _ =
      ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫
          ((K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
              ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) +
            p.negOnePow •
              ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
                ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf)))) ≫
        γ.f (p + q + 1)) := hsum
    _ = 0 := by
      have hleft :
          (K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.d p (p + 1) ▷ L.X q) = 0 := by
        calc
          (K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.d p (p + 1) ▷ L.X q) =
              (K.iCycles p ≫ K.d p (p + 1)) ⊗ₘ (L.iCycles q ≫ 𝟙 (L.X q)) := by
                simpa only [MonoidalCategory.tensorHom_id] using
                  (MonoidalCategory.tensorHom_comp_tensorHom
                    (K.iCycles p) (L.iCycles q) (K.d p (p + 1)) (𝟙 (L.X q)))
          _ = 0 := by
            simpa [HomologicalComplex.iCycles_d] using
              (MonoidalPreadditive.zero_tensor (L.iCycles q : L.cycles q ⟶ L.X q))
      have hright :
          (K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.X p ◁ L.d q (q + 1)) = 0 := by
        calc
          (K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.X p ◁ L.d q (q + 1)) =
              (K.iCycles p ≫ 𝟙 (K.X p)) ⊗ₘ (L.iCycles q ≫ L.d q (q + 1)) := by
                simpa only [MonoidalCategory.id_tensorHom] using
                  (MonoidalCategory.tensorHom_comp_tensorHom
                    (K.iCycles p) (L.iCycles q) (𝟙 (K.X p)) (L.d q (q + 1)))
          _ = 0 := by
            simpa [HomologicalComplex.iCycles_d] using
              (MonoidalPreadditive.tensor_zero (K.iCycles p : K.cycles p ⟶ K.X p))
      have hleft_assoc :
          (K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.d p (p + 1) ▷ L.X q) ≫
              ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) ≫ γ.f (p + q + 1) = 0 := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ t ≫ ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) ≫ γ.f (p + q + 1))
            hleft
      have hright_assoc :
          (K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.X p ◁ L.d q (q + 1)) ≫
              ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf) ≫ γ.f (p + q + 1) = 0 := by
        simpa [Category.assoc] using
          congrArg
            (fun t ↦ t ≫ ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf) ≫ γ.f (p + q + 1))
            hright
      calc
        (((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫
            ((K.d p (p + 1) ⊗ₘ 𝟙 (L.X q)) ≫
                ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) +
              p.negOnePow •
                ((𝟙 (K.X p) ⊗ₘ L.d q (q + 1)) ≫
                  ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf)))) ≫
            γ.f (p + q + 1) =
          (K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.d p (p + 1) ▷ L.X q) ≫
              ιTensorObj K L (p + 1) q (p + q + 1) (by abel_nf) ≫ γ.f (p + q + 1) +
            p.negOnePow •
              ((K.iCycles p ⊗ₘ L.iCycles q) ≫ (K.X p ◁ L.d q (q + 1)) ≫
                ιTensorObj K L p (q + 1) (p + q + 1) (by abel_nf) ≫ γ.f (p + q + 1)) := by
              simp [Category.assoc, Preadditive.comp_add, Preadditive.add_comp]
        _ =
            0 + p.negOnePow • 0 := by
              rw [hleft_assoc, hright_assoc]
        _ = 0 := by
          simp

/-- The cycles-level cup-product map into `H^{p + q}(H'^\bullet)` obtained by evaluating the
chain-level pairing `γ : K^\bullet ⊗ L^\bullet ⟶ H'^\bullet` on cocycles in bidegree `(p,q)`. -/
noncomputable def cohomologyCupOnCycles
    (γ : tensorObj K L ⟶ H') (p q : ℤ) [H'.HasHomology (p + q)] :
    K.cycles p ⊗ L.cycles q ⟶ H'.homology (p + q) :=
  H'.liftCycles
      ((((K.iCycles p) ⊗ₘ (L.iCycles q)) ≫ ιTensorObj K L p q (p + q) rfl) ≫ γ.f (p + q))
      (p + q + 1) (by simp)
      (cohomologyCupOnCycles_d_eq_zero γ p q) ≫
    H'.homologyπ (p + q)

/-- A cohomology-level cup-product morphism is induced by the chain-level pairing `γ` if its
precomposition with the two quotient maps from cocycles agrees with the canonical cycles-level map
`cohomologyCupOnCycles γ`. -/
def InducesCohomologyCup
    (γ : tensorObj K L ⟶ H') (p q : ℤ)
    [K.HasHomology p] [L.HasHomology q] [H'.HasHomology (p + q)]
    (γCup : K.homology p ⊗ L.homology q ⟶ H'.homology (p + q)) : Prop :=
  ((K.homologyπ p) ⊗ₘ (L.homologyπ q)) ≫ γCup = cohomologyCupOnCycles γ p q

/-- The cycles-level cup-product map in a displayed textbook target degree `r`, obtained from
`cohomologyCupOnCycles γ p q` after identifying the intrinsic target degree `p + q` with `r`. -/
noncomputable def cohomologyCupOnCyclesTo
    (γ : tensorObj K L ⟶ H') (p q r : ℤ) [H'.HasHomology r] (h : p + q = r) :
    K.cycles p ⊗ L.cycles q ⟶ H'.homology r :=
  letI : H'.HasHomology (p + q) := by
    subst h
    infer_instance
  cohomologyCupOnCycles γ p q ≫ eqToHom (by subst h; rfl)

@[simp] theorem cohomologyCupOnCyclesTo_rfl
    (γ : tensorObj K L ⟶ H') (p q : ℤ) [H'.HasHomology (p + q)] :
    cohomologyCupOnCyclesTo γ p q (p + q) rfl = cohomologyCupOnCycles γ p q := by
  simp [cohomologyCupOnCyclesTo]

/-- A cohomology-level cup-product morphism into a chosen textbook target degree `r` is induced
by the chain-level pairing `γ` if its precomposition with the quotient maps from cocycles agrees
with the transported cycles-level cup-product map in degree `r`. -/
def InducesCohomologyCupTo
    (γ : tensorObj K L ⟶ H') (p q r : ℤ)
    [K.HasHomology p] [L.HasHomology q] [H'.HasHomology r]
    (γCup : K.homology p ⊗ L.homology q ⟶ H'.homology r) : Prop :=
  ∃ h : p + q = r,
    ((K.homologyπ p) ⊗ₘ (L.homologyπ q)) ≫ γCup = cohomologyCupOnCyclesTo γ p q r h

/-- A cohomology cup product in target degree `r` is induced once the intrinsic target
degree `p + q` is identified with `r` and its source-facing equality with the transported
cycles-level cup product is known. -/
theorem inducesCohomologyCupTo_of_eq
    (γ : tensorObj K L ⟶ H') (p q r : ℤ)
    [K.HasHomology p] [L.HasHomology q] [H'.HasHomology r]
    (γCup : K.homology p ⊗ L.homology q ⟶ H'.homology r)
    (h : p + q = r)
    (hγCup :
      ((K.homologyπ p) ⊗ₘ (L.homologyπ q)) ≫ γCup = cohomologyCupOnCyclesTo γ p q r h) :
    InducesCohomologyCupTo γ p q r γCup :=
  ⟨h, hγCup⟩

/-- Unpacking `InducesCohomologyCupTo` recovers the source-facing equality with the transported
cycles-level cup-product map in the displayed degree `r`. -/
theorem inducesCohomologyCupTo_spec
    (γ : tensorObj K L ⟶ H') (p q r : ℤ)
    [K.HasHomology p] [L.HasHomology q] [H'.HasHomology r]
    (γCup : K.homology p ⊗ L.homology q ⟶ H'.homology r)
    (hγCup : InducesCohomologyCupTo γ p q r γCup) :
    ∃ h : p + q = r,
      ((K.homologyπ p) ⊗ₘ (L.homologyπ q)) ≫ γCup = cohomologyCupOnCyclesTo γ p q r h :=
  hγCup

/-- A canonical cohomology cup product in displayed degree `r` induced by `γ`. The `uniq` field
expresses that the cohomology-level morphism is determined by the chain-level pairing `γ` and the
displayed degree identification, so downstream source-facing statements need not expose auxiliary
`Epi` side conditions or a separate chosen morphism. -/
class CohomologyCupTo
    (γ : tensorObj K L ⟶ H') (p q r : ℤ)
    [K.HasHomology p] [L.HasHomology q] [H'.HasHomology r] where
  map : K.homology p ⊗ L.homology q ⟶ H'.homology r
  induces : InducesCohomologyCupTo γ p q r map
  uniq : ∀ γCup, InducesCohomologyCupTo γ p q r γCup → γCup = map

/-- The canonical cohomology cup-product morphism in displayed degree `r` induced by `γ`. -/
abbrev cohomologyCupTo
    (γ : tensorObj K L ⟶ H') (p q r : ℤ)
    [K.HasHomology p] [L.HasHomology q] [H'.HasHomology r]
    [hγCup : CohomologyCupTo γ p q r] :
    K.homology p ⊗ L.homology q ⟶ H'.homology r :=
  hγCup.map

end

/-- Helper for Lemma 20.25.4: in the source short exact sequence
`0 → G₃^\bullet → G₂^\bullet → G₁^\bullet → 0`, the left term `G₃^\bullet` is stored as
`SG.X₁`. -/
abbrev secondSequenceG₃ (SG : ShortComplex (CochainComplex C ℤ)) : CochainComplex C ℤ :=
  SG.X₁

/-- Helper for Lemma 20.25.4: in the source short exact sequence
`0 → G₃^\bullet → G₂^\bullet → G₁^\bullet → 0`, the right term `G₁^\bullet` is stored as
`SG.X₃`. -/
abbrev secondSequenceG₁ (SG : ShortComplex (CochainComplex C ℤ)) : CochainComplex C ℤ :=
  SG.X₃

/-- Lemma 20.25.4: let
`0 → F₁^\bullet → F₂^\bullet → F₃^\bullet → 0` and
`0 → G₃^\bullet → G₂^\bullet → G₁^\bullet → 0`
be short exact sequences of cochain complexes, and let
`γ₁ : F₁^\bullet ⊗ G₁^\bullet → H^\bullet`,
`γ₂ : F₂^\bullet ⊗ G₂^\bullet → H^\bullet`,
`γ₃ : F₃^\bullet ⊗ G₃^\bullet → H^\bullet`
be compatible pairings, recorded by the two tensor-product `CommSq` hypotheses below. Suppose
Čech cohomology agrees with cohomology for the source terms `F₁^\bullet`, `F₃^\bullet`,
`G₃^\bullet = SG.X₁`, and `G₁^\bullet = SG.X₃` in the displayed degrees. Assume the canonical
cohomology cup products induced by `γ₁` and `γ₃` are available in the common textbook target
degree `n + m + 1`. Then the canonical boundary maps `hF.δ n (n + 1) rfl` and `hG.δ m (m + 1) rfl`
satisfy
`γ₁(∂ a₃ ∪ b₁) = (-1)^(n + 1) γ₃(a₃ ∪ ∂ b₁)`. The statement is expressed as an equality of the
corresponding morphisms
`H^n(F₃^\bullet) ⊗ H^m(G₁^\bullet) ⟶ H^{n + m + 1}(H^\bullet)`. -/
@[stacks 07MC]
theorem cohomology_boundary_cup_eq_negOnePow
    (γ₁ : tensorObj SF.X₁ (secondSequenceG₁ SG) ⟶ H)
    (γ₂ : tensorObj SF.X₂ SG.X₂ ⟶ H)
    (γ₃ : tensorObj SF.X₃ (secondSequenceG₃ SG) ⟶ H)
    (hγ₁ : CommSq (tensorHom (𝟙 SF.X₁) SG.g) (tensorHom SF.f (𝟙 SG.X₂)) γ₁ γ₂)
    (hγ₃ : CommSq (tensorHom SF.g (𝟙 SG.X₁)) (tensorHom (𝟙 SF.X₂) SG.f) γ₃ γ₂)
    (n m : ℤ)
    [SF.X₁.HasHomology (n + 1)] [SF.X₃.HasHomology n]
    [(secondSequenceG₃ SG).HasHomology (m + 1)] [(secondSequenceG₁ SG).HasHomology m]
    [H.HasHomology (n + m + 1)]
    [CohomologyCupTo γ₁ (n + 1) m (n + m + 1)]
    [CohomologyCupTo γ₃ n (m + 1) (n + m + 1)] :
    ((hF.δ n (n + 1) rfl) ▷ (secondSequenceG₁ SG).homology m) ≫
        cohomologyCupTo γ₁ (n + 1) m (n + m + 1) =
      (n + 1).negOnePow •
        (((SF.X₃.homology n ◁ hG.δ m (m + 1) rfl) ≫
            cohomologyCupTo γ₃ n (m + 1) (n + m + 1))) := sorry

end
