import Mathlib
import StacksProject_2024.stacks_project.Chap12.Definition_12_20_2
import StacksProject_2024.stacks_project.Chap12.Definition_12_21_3
import StacksProject_2024.stacks_project.Chap12.Definition_12_22_3

-- Declarations for this item will be appended below by the statement pipeline.

/-
Domain-style sampling for Definition 12.22.5:
- primary domain: spectral sequences attached to differential objects in an abelian category;
- sampled core/canonical declarations:
  `SpectralSequence C (fun _ : ℤ ↦ ComplexShape.refl PUnit.{1}) 1`,
  `SpectralSequence.cycle`,
  `SpectralSequence.boundary`,
  `ExactCouple.associatedSpectralSequence`;
- best owner abstraction: the page-`1` spectral-sequence owner
  `ExactCouple.associatedSpectralSequence (exactCouple α)`;
- primitive data: the source-facing page-`E₀` owner `spectralSequence α`, whose zeroth page is
  `cokernel α`, and the canonical page-`1` spectral-sequence owner attached to the exact couple;
- derived API in this file: the page-`0` spectral sequence and the source-facing zero-based
  pullback filtrations `cycle`/`boundary` on `E₀`;
- source/core/bridge triage:
  `source-facing`: `spectralSequence`, `cycle`, `boundary`;
  `core/canonical`: `ExactCouple.associatedSpectralSequence`;
  `bridge/view`: the pullback of the canonical page-`1` filtration along `ker(d₀) ⟶ E₁`.

The public source-facing content here is the page-`E₀` presentation. The positive-stage `Z_{r+1}`/
`B_{r+1}` objects on page `E₁` are already owned upstream by `SpectralSequence.cycle` and
`SpectralSequence.boundary`, so this file should reuse that owner directly while adding the
explicit zero-stage source terms `Z₀ = E₀` and `B₀ = 0` instead of rebuilding a parallel
page-`1` wrapper.
-/

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoryTheory
open HomologicalComplex.HomologySequence
open scoped SpectralSequence

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace DifferentialObjectAssociatedSpectralSequence

open ExactCouple

variable {A : HomologicalComplex C (ComplexShape.refl PUnit.{1})}
variable (α : A ⟶ A)

/-- The exact couple obtained from the periodic homology sequence of
`0 ⟶ (A,d) --α→ (A,d) ⟶ (A / α A,d) ⟶ 0`. Its outer object is `H(A)`, its inner object is
`H(cokernel α)`, the endomorphism is induced by `α`, the map `H(A) ⟶ H(cokernel α)` is induced by
the quotient map, and the return map is the connecting morphism. -/
private noncomputable def exactCouple [Mono α] : @CategoryTheory.ExactCouple C _ _ := by
  let S : ShortComplex (HomologicalComplex C (ComplexShape.refl PUnit.{1})) :=
    ShortComplex.mk α (cokernel.π α) (cokernel.condition α)
  let hS : S.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.exact_cokernel α) (inferInstance : Mono S.f) (inferInstance : Epi S.g)
  exact
    { A := H(A)
      E := H(cokernel α)
      α := HomologicalComplex.homologyMap α PUnit.unit
      f := hS.δ PUnit.unit PUnit.unit rfl
      g := HomologicalComplex.homologyMap (cokernel.π α) PUnit.unit
      f_comp_α := by
        simpa [S] using hS.δ_comp PUnit.unit PUnit.unit rfl
      g_comp_f := by
        simpa [S] using hS.comp_δ PUnit.unit PUnit.unit rfl
      α_comp_g := by
        rw [← HomologicalComplex.homologyMap_comp, cokernel.condition, HomologicalComplex.homologyMap_zero]
      exact_f_α := by
        simpa [S] using hS.homology_exact₁ PUnit.unit PUnit.unit rfl
      exact_g_f := by
        simpa [S] using hS.homology_exact₃ PUnit.unit PUnit.unit rfl
      exact_α_g := by
        simpa [S] using hS.homology_exact₂ PUnit.unit }

/-- Definition 12.22.5: the spectral sequence associated to a differential object `(A,d)` and a
monomorphism `α : (A,d) ⟶ (A,d)` starts at page `E₀ = (A / α A,d)`, with `d₀` the induced
differential on the quotient, and from page `1` onward is the canonical spectral sequence of the
exact couple attached to the short exact sequence
`0 ⟶ (A,d) --α→ (A,d) ⟶ (A / α A,d) ⟶ 0`. In particular `E₁ = H(A / α A,d)`. -/
noncomputable def spectralSequence [Mono α] :
    SpectralSequence C (fun _ : ℤ ↦ ComplexShape.refl PUnit.{1}) 0 where
  page r hr := match r with
    | Int.ofNat 0 => cokernel α
    | Int.ofNat (n + 1) => (exactCouple α).associatedSpectralSequence.page (Int.ofNat (n + 1))
    | Int.negSucc _ => nomatch hr
  iso r r' _ hrr' hr := match r with
    | Int.ofNat 0 => match hrr' with
      | rfl => eqToIso (by
          simpa using (associatedSpectralSequence_pageObject (exactCouple α) 0).symm)
    | Int.ofNat (n + 1) => match hrr' with
      | rfl => by
          simpa using
            (exactCouple α).associatedSpectralSequence.iso
              (Int.ofNat (n + 1)) (Int.ofNat (n + 2)) PUnit.unit
    | Int.negSucc _ => nomatch hr

section

variable [Mono α]

/-- The zeroth page is the quotient differential object `(A / α A, d)`. -/
theorem page_zero :
    (spectralSequence α).page 0 = cokernel α := rfl

/-- The unique object on page `E₀` is the quotient object `A / α A`. -/
theorem page_zero_obj :
    ((spectralSequence α).page 0).X PUnit.unit = (cokernel α).X PUnit.unit := rfl

/-- The differential `d₀` is the induced differential on the quotient complex `A / α A`. -/
theorem page_zero_d :
    ((spectralSequence α).page 0).d PUnit.unit PUnit.unit =
      (cokernel α).d PUnit.unit PUnit.unit := rfl

/-- The kernel subobject maps canonically to the cycles object. -/
private noncomputable def kernelSubobjectToCycles
    {κ : Type*} {c : ComplexShape κ} (K : HomologicalComplex C c) (pq : κ) :
    (kernelSubobject (K.dFrom pq) : C) ⟶ K.cycles pq :=
  K.liftCycles (kernelSubobject (K.dFrom pq)).arrow (c.next pq) rfl
    (kernelSubobject_arrow_comp (K.dFrom pq))

/-- The cycle object of the quotient differential object, viewed as a subobject of `E₀`. -/
private noncomputable abbrev pageZeroCycles :
    Subobject ((cokernel α).X PUnit.unit) :=
  kernelSubobject ((cokernel α).dFrom PUnit.unit)

/-- The canonical map `Z₁ = ker(d₀) ⟶ H(A / α A,d) = E₁`. Pulling back the owner filtration of
`(exactCouple α).associatedSpectralSequence` along this morphism recovers the recursive source
filtration on `E₀`. -/
private noncomputable def pageZeroCyclesToHomology :
    (pageZeroCycles α : C) ⟶ H(cokernel α) :=
  kernelSubobjectToCycles (cokernel α) PUnit.unit ≫
    (cokernel α).homologyπ PUnit.unit

/-- Pull a subobject of `H(A / α A,d) = E₁` back to the corresponding subobject of
`E₀ = A / α A` via the canonical map `ker(d₀) ⟶ H(A / α A,d)`. -/
private noncomputable def pullbackToPageZero
    (Z : Subobject (H(cokernel α))) :
    Subobject ((cokernel α).X PUnit.unit) :=
  (Subobject.map (pageZeroCycles α).arrow).obj
    ((Subobject.pullback (pageZeroCyclesToHomology α)).obj Z)

/-- The positive owner page number corresponding to the source-facing stage `r + 1` on `E₀`. -/
private abbrev ownerPageIndex (r : ℕ) : ℕ+ :=
  ⟨r + 1, Nat.succ_pos _⟩

/-- Definition 12.22.5: the recursive cycle piece `Z_r` inside the page-`E₀` object
`A / α A`. The zero stage is `Z₀ = E₀`, and for `r + 1` this is the source-facing filtration on
`E₀` obtained from the canonical owner filtration on the page-`E₁` view by pullback along
`ker(d₀) ⟶ E₁`. -/
def cycle : ℕ → Subobject ((cokernel α).X PUnit.unit)
  | 0 => ⊤
  | r + 1 =>
      pullbackToPageZero α
        ((exactCouple α).associatedSpectralSequence.cycle PUnit.unit (ownerPageIndex r))

/-- Definition 12.22.5: the recursive boundary piece `B_r` inside the page-`E₀` object
`A / α A`. The zero stage is `B₀ = 0`, and for `r + 1` this is the source-facing boundary
filtration obtained from the canonical owner filtration on the page-`E₁` view by pullback along
`ker(d₀) ⟶ E₁`. -/
def boundary : ℕ → Subobject ((cokernel α).X PUnit.unit)
  | 0 => ⊥
  | r + 1 =>
      pullbackToPageZero α
        ((exactCouple α).associatedSpectralSequence.boundary PUnit.unit (ownerPageIndex r))

/-- The zero-stage cycle piece is the whole page-`E₀` object. -/
theorem cycle_zero :
    cycle α 0 = ⊤ :=
  rfl

/-- The zero-stage boundary piece is zero. -/
theorem boundary_zero :
    boundary α 0 = ⊥ :=
  rfl

/-- The first page is the differential-homology object `H(A / α A,d)`. -/
theorem page_one :
    ((spectralSequence α).page 1).X PUnit.unit = H(cokernel α) := by
  simpa [spectralSequence] using
    associatedSpectralSequence_pageObject (exactCouple α) 0

end

end DifferentialObjectAssociatedSpectralSequence

end CategoryTheory
