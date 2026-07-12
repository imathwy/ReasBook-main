import StacksProject_2024.Chap22.PropertyPDGModule

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

noncomputable section

universe u

namespace CochainComplex

section

variable {A : Type u} [Ring A]

local notation "DGMod" => CochainComplex (ModuleCat.{u, u} A) ℤ

/-- A differential graded `A`-module is a direct sum of shifts of `A` if it is isomorphic to a
chosen coproduct of shifted free modules `A[k]`. -/
def IsDirectSumOfShiftedFree (P : DGMod) : Prop :=
  ∃ (ι : Type u) (degree : ι → ℤ)
    (hι : HasCoproduct (fun i ↦ shiftedFreeDGModule A (degree i))),
      let _ := hι
      Nonempty (P ≅ ∐ fun i ↦ shiftedFreeDGModule A (degree i))

/-- Helper for Lemma 22.20.3: the sequential diagram `0 ⟶ X ⟶ Y ⟶ Y ⟶ ⋯` used in the
property `(P)` filtrations. -/
private def zeroMapThenIdentityTailStage (X Y : DGMod) : ℕ → DGMod
  | 0 => ⊥_ DGMod
  | 1 => X
  | _ + 2 => Y

/-- Helper for Lemma 22.20.3: the transition maps in the sequential diagram
`0 ⟶ X ⟶ Y ⟶ Y ⟶ ⋯`. -/
private def zeroMapThenIdentityTailInclusion {X Y : DGMod} (u : X ⟶ Y) :
    ∀ n : ℕ, zeroMapThenIdentityTailStage X Y n ⟶ zeroMapThenIdentityTailStage X Y (n + 1)
  | 0 => 0
  | 1 => u
  | _ + 2 => 𝟙 Y

/-- Helper for Lemma 22.20.3: the corresponding sequential diagram object. -/
private abbrev zeroMapThenIdentityTailDiagram {X Y : DGMod} (u : X ⟶ Y) : ℕ ⥤ DGMod :=
  Functor.ofSequence (zeroMapThenIdentityTailInclusion u)

/-- Helper for Lemma 22.20.3: every map out of stage `2` in the constant tail is the identity. -/
private theorem zeroMapThenIdentityTail_map_from_two {X Y : DGMod} (u : X ⟶ Y) (k : ℕ) :
    (zeroMapThenIdentityTailDiagram u).map
        (CategoryTheory.homOfLE (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))) =
      𝟙 Y := by
  induction k with
  | zero =>
      -- Proof comment: stage `2` already lies in the constant `Y`-tail, so the first outgoing
      -- map is literally the identity.
      simpa [zeroMapThenIdentityTailDiagram, zeroMapThenIdentityTailStage] using
        (CategoryTheory.Functor.OfSequence.map_id (zeroMapThenIdentityTailInclusion u) 2)
  | succ k hk =>
      -- Proof comment: factor the longer map through the previous tail stage, then use the
      -- induction hypothesis and the identity tail step.
      rw [show homOfLE (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le (k + 1)))) =
            homOfLE (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))) ≫
              homOfLE (Nat.le_succ (k + 2)) by
            apply Subsingleton.elim]
      rw [Functor.map_comp, hk]
      have hstep := CategoryTheory.Functor.OfSequence.map_le_succ
        (zeroMapThenIdentityTailInclusion u) (k + 2)
      have hstep' :
          (zeroMapThenIdentityTailDiagram u).map (homOfLE (Nat.le_succ (k + 2))) = 𝟙 Y := by
        simpa [zeroMapThenIdentityTailDiagram, zeroMapThenIdentityTailInclusion] using hstep
      rw [hstep']
      exact Category.id_comp (𝟙 Y)

/-- Helper for Lemma 22.20.3: in the sequential diagram `0 ⟶ X ⟶ Y ⟶ Y ⟶ ⋯`, the colimit is
already reached at stage `2`, i.e. at the object `Y`. -/
private noncomputable def colimitIsoOfZeroThenMapThenIdentityTail {X Y : DGMod} (u : X ⟶ Y) :
    Y ≅ colimit (zeroMapThenIdentityTailDiagram u) := by
  let h : (zeroMapThenIdentityTailDiagram u).IsEventuallyConstantFrom 2 := by
    intro j f
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (CategoryTheory.leOfHom f)
    have hk' : j = k + 2 := by
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
    subst hk'
    have hf :
        f = homOfLE (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))) :=
      Subsingleton.elim _ _
    cases hf
    have hmap :
        (zeroMapThenIdentityTailDiagram u).map
          (homOfLE (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k)))) = 𝟙 Y :=
      zeroMapThenIdentityTail_map_from_two u k
    rw [hmap]
    change IsIso (𝟙 Y)
    infer_instance
  -- Proof comment: the tail is eventually constant from stage `2`, so the colimit is already
  -- realized by the object `Y` at that stage.
  exact (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.isColimitCocone).symm

/-- Helper for Lemma 22.20.3: the first zero inclusion in the filtration is an admissible
monomorphism after forgetting the differential. -/
private theorem isAdmissibleMono_zeroFromInitial (P : DGMod) :
    IsAdmissibleMono dgModuleUnderlyingGradedHomSystem (0 : (⊥_ DGMod) ⟶ P) := by
  -- Proof comment: the underlying graded map splits through the unique map back to the initial
  -- graded object, and termwise this is just the split mono `0 ⟶ P.X n`.
  rw [isAdmissibleMono_iff_termwiseSplitMono]
  intro n
  refine IsSplitMono.mk' ⟨0, ?_⟩
  let hzero : IsZero ((⊥_ DGMod).X n) := by
    exact (HomologicalComplex.eval (ModuleCat A) (ComplexShape.up ℤ) n).map_isZero
      initialIsInitial.isZero
  exact hzero.eq_of_src _ _

/-- Helper for Lemma 22.20.3: the first zero inclusion in the filtration is a monomorphism. -/
private theorem mono_zeroFromInitial (P : DGMod) :
    Mono (0 : (⊥_ DGMod) ⟶ P) := by
  exact initialIsInitial.isZero.mono (0 : (⊥_ DGMod) ⟶ P)

/-- Helper for Lemma 22.20.3: in a short exact sequence, the cokernel of the first map is the
right-hand term. -/
private noncomputable def cokernelIsoRightTermOfShortExact
    (S : ShortComplex DGMod) (hS : S.ShortExact) :
    cokernel S.f ≅ S.X₃ :=
  -- Proof comment: use the canonical cokernel packaged by short exactness and compare it with the
  -- chosen categorical cokernel.
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel S.f) hS.gIsCokernel

/-- Helper for Lemma 22.20.3: the empty coproduct of shifted free differential graded
`A`-modules is a zero object. -/
private theorem isZero_emptyShiftedFreeCoproduct (degree : PEmpty → ℤ) :
    IsZero (∐ fun i : PEmpty ↦ shiftedFreeDGModule A (degree i)) := by
  let F : Discrete PEmpty ⥤ CochainComplex (ModuleCat.{u, u} A) ℤ :=
    Discrete.functor (fun i : PEmpty ↦ shiftedFreeDGModule A (degree i))
  -- Proof comment: identify the empty coproduct with a colimit of a constant initial diagram.
  refine (IsInitial.ofIso initialIsInitial ?_).isZero
  let e : F ≅
      (Functor.const (Discrete PEmpty)).obj
        (⊥_ (CochainComplex (ModuleCat.{u, u} A) ℤ)) :=
    NatIso.ofComponents (fun i ↦ PEmpty.elim i.as)
  exact colimitConstInitial.symm ≪≫ (HasColimit.isoOfNatIso e).symm

/-- Helper for Lemma 22.20.3: the chosen empty coproduct is canonically isomorphic to `0`. -/
private noncomputable def cokernelZeroFromZeroIso (P : DGMod) :
    cokernel (0 : (⊥_ DGMod) ⟶ P) ≅ P := by
  let c :
      IsColimit
        (CokernelCofork.ofπ (𝟙 P) (by simp :
          (0 : (⊥_ DGMod) ⟶ P) ≫ 𝟙 P = 0)) :=
    by
      refine CokernelCofork.IsColimit.ofπ' (𝟙 P) (by simp) ?_
      intro Z s hs
      exact ⟨s, by simpa using hs⟩
  -- Proof comment: compare the explicit cokernel cofork with the chosen categorical cokernel.
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (0 : (⊥_ DGMod) ⟶ P)) c

/-- Helper for Lemma 22.20.3: in the filtration `0 ⟶ P ⟶ P ⟶ ⋯`, the first quotient is
canonically `P`. -/
private noncomputable def firstTailQuotientIso (P : DGMod) :
    cokernel (zeroMapThenIdentityTailInclusion (X := P) (Y := P) (𝟙 P) 0) ≅ P := by
  -- Proof comment: the first step of the tail filtration is the zero map out of the initial
  -- object, so its cokernel is exactly the target module `P`.
  simpa [zeroMapThenIdentityTailInclusion] using cokernelZeroFromZeroIso (A := A) P

/-- Helper for Lemma 22.20.3: every later quotient in the filtration `0 ⟶ P ⟶ P ⟶ ⋯` is a zero
object because the tail maps are identities. -/
private theorem laterTailQuotientIsZero (P : DGMod) (n : ℕ) :
    IsZero (cokernel (zeroMapThenIdentityTailInclusion (X := P) (Y := P) (𝟙 P) (n + 1))) := by
  -- Proof comment: once the filtration reaches `P`, every transition map is the identity, whose
  -- cokernel is zero.
  cases n with
  | zero =>
      simpa [zeroMapThenIdentityTailInclusion] using Limits.isZero_cokernel_of_epi (𝟙 P)
  | succ n =>
      simpa [zeroMapThenIdentityTailInclusion] using Limits.isZero_cokernel_of_epi (𝟙 P)

/-- A direct sum of shifted free differential graded `A`-modules has property `(P)`. -/
theorem IsDirectSumOfShiftedFree.hasPropertyP {P : DGMod}
    (hP : IsDirectSumOfShiftedFree P) :
    HasPropertyP P := by
  rcases hP with ⟨ι, degree, hι, ⟨e⟩⟩
  let stage : ℕ → DGMod := zeroMapThenIdentityTailStage (A := A) (X := P) (Y := P)
  let inclusion : ∀ n : ℕ, stage n ⟶ stage (n + 1) :=
    zeroMapThenIdentityTailInclusion (A := A) (X := P) (Y := P) (𝟙 P)
  let pieceIndex : ℕ → Type u
    | 0 => ι
    | _ + 1 => PEmpty
  let pieceDegree : ∀ n : ℕ, pieceIndex n → ℤ
    | 0 => degree
    | _ + 1 => fun i ↦ PEmpty.elim i
  have hIdAdmissible : IsAdmissibleMono dgModuleUnderlyingGradedHomSystem (𝟙 P) := by
    refine (isAdmissibleMono_iff_termwiseSplitMono (A := A) (ι := 𝟙 P)).2 ?_
    intro n
    exact IsSplitMono.mk' ⟨𝟙 _, by simp⟩
  let F : PropertyPFiltration P :=
    {
      stage := stage
      stageZero := by
        simpa [stage, zeroMapThenIdentityTailStage] using (isZero_zero DGMod)
      inclusion := inclusion
      mono := by
        intro n
        cases n with
        | zero =>
            simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using
              mono_zeroFromInitial (A := A) P
        | succ n =>
            simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using
              (show Mono (𝟙 P) by infer_instance)
      admissible := by
        intro n
        cases n with
        | zero =>
            simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using
              isAdmissibleMono_zeroFromInitial (A := A) P
        | succ n =>
            simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using hIdAdmissible
      hasColimit := inferInstance
      colimitIso := by
        simpa [stage, inclusion, zeroMapThenIdentityTailDiagram] using
          colimitIsoOfZeroThenMapThenIdentityTail (X := P) (Y := P) (𝟙 P)
      pieceIndex := pieceIndex
      pieceDegree := pieceDegree
      pieceHasCoproduct := by
        intro n
        cases n with
        | zero =>
            exact hι
        | succ n =>
            infer_instance
      pieceIso := by
        intro n
        cases n with
        | zero =>
            simpa [stage, inclusion, pieceIndex, pieceDegree, zeroMapThenIdentityTailInclusion] using
              (firstTailQuotientIso (A := A) P) ≪≫ e
        | succ n =>
            let emptyDegree : PEmpty → ℤ := fun i ↦ PEmpty.elim i
            simpa [stage, inclusion, pieceIndex, pieceDegree, emptyDegree,
              zeroMapThenIdentityTailInclusion] using
              (cokernel.ofEpi (𝟙 P)) ≪≫
                (isZero_emptyShiftedFreeCoproduct (A := A) emptyDegree).isoZero.symm
    }
  exact F.hasPropertyP

/-- Bridge to the Chapter 22 property `(P)` owner: an admissible short exact sequence
`0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` with `S.X₁` and `S.X₃` direct sums of shifts of `A` exhibits the
middle term `S.X₂` as having property `(P)`. -/
theorem hasPropertyP_of_admissibleShortExact_of_shiftedFree
    (S : ShortComplex DGMod)
    (hS : IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S)
    (hX₁ : IsDirectSumOfShiftedFree S.X₁)
    (hX₃ : IsDirectSumOfShiftedFree S.X₃) :
    HasPropertyP S.X₂ := by
  rcases hX₁ with ⟨ι₁, degree₁, hι₁, ⟨e₁⟩⟩
  rcases hX₃ with ⟨ι₃, degree₃, hι₃, ⟨e₃⟩⟩
  let stage : ℕ → DGMod := zeroMapThenIdentityTailStage (A := A) (X := S.X₁) (Y := S.X₂)
  let inclusion : ∀ n : ℕ, stage n ⟶ stage (n + 1) :=
    zeroMapThenIdentityTailInclusion (A := A) S.f
  let pieceIndex : ℕ → Type u
    | 0 => ι₁
    | 1 => ι₃
    | _ + 2 => PEmpty
  let pieceDegree : ∀ n : ℕ, pieceIndex n → ℤ
    | 0 => degree₁
    | 1 => degree₃
    | _ + 2 => fun i ↦ PEmpty.elim i
  have hIdAdmissible : IsAdmissibleMono dgModuleUnderlyingGradedHomSystem (𝟙 S.X₂) := by
    refine (isAdmissibleMono_iff_termwiseSplitMono (A := A) (ι := 𝟙 S.X₂)).2 ?_
    intro n
    exact IsSplitMono.mk' ⟨𝟙 _, by simp⟩
  let F : PropertyPFiltration S.X₂ :=
    {
      stage := stage
      stageZero := by
        simpa [stage, zeroMapThenIdentityTailStage] using (isZero_zero DGMod)
      inclusion := inclusion
      mono := by
        intro n
        cases n with
        | zero =>
            simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using
              mono_zeroFromInitial (A := A) S.X₁
        | succ n =>
            cases n with
            | zero =>
                simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using hS.shortExact.mono_f
            | succ n =>
                simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using
                  (show Mono (𝟙 S.X₂) by infer_instance)
      admissible := by
        intro n
        cases n with
        | zero =>
            simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using
              isAdmissibleMono_zeroFromInitial (A := A) S.X₁
        | succ n =>
            cases n with
            | zero =>
                simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using
                  (hS.isAdmissibleMono : IsAdmissibleMono dgModuleUnderlyingGradedHomSystem S.f)
            | succ n =>
                simpa [stage, inclusion, zeroMapThenIdentityTailInclusion] using hIdAdmissible
      hasColimit := inferInstance
      colimitIso := by
        simpa [stage, inclusion, zeroMapThenIdentityTailDiagram] using
          colimitIsoOfZeroThenMapThenIdentityTail (X := S.X₁) (Y := S.X₂) S.f
      pieceIndex := pieceIndex
      pieceDegree := pieceDegree
      pieceHasCoproduct := by
        intro n
        cases n with
        | zero =>
            exact hι₁
        | succ n =>
            cases n with
            | zero =>
                exact hι₃
            | succ n =>
                infer_instance
      pieceIso := by
        intro n
        cases n with
        | zero =>
            simpa [stage, inclusion, pieceIndex, pieceDegree, zeroMapThenIdentityTailInclusion] using
              (cokernelZeroFromZeroIso (A := A) S.X₁) ≪≫ e₁
        | succ n =>
            cases n with
            | zero =>
                simpa [stage, inclusion, pieceIndex, pieceDegree, zeroMapThenIdentityTailInclusion] using
                  (cokernelIsoRightTermOfShortExact (A := A) S hS.shortExact) ≪≫ e₃
            | succ n =>
                let emptyDegree : PEmpty → ℤ := fun i ↦ PEmpty.elim i
                simpa [stage, inclusion, pieceIndex, pieceDegree, emptyDegree,
                  zeroMapThenIdentityTailInclusion] using
                  (cokernel.ofEpi (𝟙 S.X₂)) ≪≫
                    (isZero_emptyShiftedFreeCoproduct (A := A) emptyDegree).isoZero.symm
    }
  exact F.hasPropertyP

/-- Lemma 22.20.3: every differential graded `A`-module admits a morphism from a differential
graded `A`-module `S.X₂` which is epimorphic in every degree, induces epimorphisms on the
canonical cycles maps in every degree, and is the middle term of an admissible short exact
sequence `0 ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ 0` whose ends are direct sums of shifts of `A`. -/
@[stacks 09KN]
theorem exists_degreewiseSurjective_cyclesSurjective_admissibleShortExact
    (M : DGMod) :
    ∃ (S : ShortComplex DGMod) (π : S.X₂ ⟶ M),
      IsAdmissibleShortExact dgModuleUnderlyingGradedHomSystem S ∧
        IsDirectSumOfShiftedFree S.X₁ ∧
        IsDirectSumOfShiftedFree S.X₃ ∧
        (∀ n : ℤ, Epi (π.f n)) ∧
        (∀ n : ℤ, Epi (cyclesMap π n)) := by
  -- TODO: assemble the textbook cell construction from one elementary two-term cell for each
  -- homogeneous element of `M`, then add extra shifted-free cycle summands to force surjectivity
  -- on `cyclesMap`. The remaining blocker is packaging that coproduct construction into an
  -- admissible short complex with degreewise and cyclewise epimorphism proofs.
  sorry

/-- Downstream-friendly bridge form of Lemma 22.20.3: the source module `P` produced there already
has property `(P)` in the Chapter 22 owner sense, while the map to `M` is termwise epimorphic and
induces epimorphisms on the canonical cycles maps. -/
theorem exists_degreewiseSurjective_cyclesSurjective_hasPropertyP
    (M : DGMod) :
    ∃ (P : DGMod) (π : P ⟶ M),
      HasPropertyP P ∧
        (∀ n : ℤ, Epi (π.f n)) ∧
        (∀ n : ℤ, Epi (cyclesMap π n)) := by
  rcases exists_degreewiseSurjective_cyclesSurjective_admissibleShortExact M with
    ⟨S, π, hS, hX₁, hX₃, hπ, hcycles⟩
  exact ⟨S.X₂, π,
    hasPropertyP_of_admissibleShortExact_of_shiftedFree S hS hX₁ hX₃, hπ, hcycles⟩

end

end CochainComplex
