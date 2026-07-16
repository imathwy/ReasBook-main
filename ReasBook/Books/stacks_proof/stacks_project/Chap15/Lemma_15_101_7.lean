import stacks_proof.stacks_project.Chap15.Remark_15_101_6
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] {I : Ideal A}

namespace IadicFiniteModuleSystem

variable {X Y : IadicFiniteModuleSystem A I}

local notation "Q" => IadicFiniteModuleSystem.Category.quotient A I

open HomRepresentative

/- Domain-style sampling for Lemma 15.101.7:
- primary domain: isomorphism criteria for morphisms in the category `IadicFiniteModuleSystem`
  from Remark `15.101.6`;
- sampled owner declarations:
  `CategoryTheory.IsIso`,
  `CategoryTheory.Quotient`,
  `IadicFiniteModuleSystem.Category.quotient`,
  `IadicFiniteModuleSystem.HomRepresentative`,
  `Submodule.torsionBySet`;
- best owner abstraction:
  `source-facing`: the isomorphism criterion for a morphism
    `f : (Q).obj X ⟶ (Q).obj Y`;
  `core/canonical`: the owner predicate `CategoryTheory.IsIso f` on morphisms in the category of
    Remark `15.101.6`;
  `bridge/view`: the representative-level predicate saying one, equivalently every,
    representative has eventually bounded kernel and cokernel;
- primitive data: the representative-level torsion conditions on kernels and cokernels;
- derived API: the morphism-level predicate
  `HasEventuallyBoundedKernelAndCokernel f` and the main `IsIso f ↔ ...` theorem below.

This item therefore should not stop at the auxiliary representative predicate: the public main
entry is the `IsIso` criterion on the actual category morphism. -/

namespace HomRepresentative

private abbrev levelKernel (f : HomRepresentative X Y)
    (n : {n : ℕ+ // f.cutoff ≤ (n : ℕ)}) :
    Submodule (stageRing A I n.1) (powerSubmodule f.cutoff X n.1) :=
  LinearMap.ker (f n.1 n.2)

private abbrev levelCokernel (f : HomRepresentative X Y)
    (n : {n : ℕ+ // f.cutoff ≤ (n : ℕ)}) : Type u :=
  torsionQuotient f.cutoff Y n.1 ⧸ LinearMap.range (f n.1 n.2)

private def hasEventuallyBoundedKernelAndCokernel (f : HomRepresentative X Y) : Prop :=
  ∃ c' N : ℕ, ∃ hN : f.cutoff ≤ N,
    ∀ n : ℕ+, ∀ hn : N ≤ (n : ℕ),
      Module.IsTorsionBySet
          (stageRing A I n)
          (levelKernel f ⟨n, Nat.le_trans hN hn⟩)
          (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n)) ∧
          Module.IsTorsionBySet
              (stageRing A I n)
              (levelCokernel f ⟨n, Nat.le_trans hN hn⟩)
              (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n))

end HomRepresentative

/-- Auxiliary morphism-level predicate for Lemma 15.101.7 in the category from Remark 15.101.6: a
morphism has eventually bounded kernel and cokernel if, for one (equivalently every)
representative `(c, \varphi_n)`, there exists a power `I^{c'}` annihilating both the kernel and
cokernel of the level maps `I^c E_n → E'_n / E'_n[I^c]` for all sufficiently large `n`. -/
def HasEventuallyBoundedKernelAndCokernel
    (f : (Q).obj X ⟶ (Q).obj Y) : Prop :=
  -- Route correction: the public predicate now records existence of one bounded representative,
  -- so the main theorem no longer depends on quotient-lift congruence before the representative
  -- criterion is established.
  ∃ f₀ : HomRepresentative X Y, (Q).map f₀ = f ∧ hasEventuallyBoundedKernelAndCokernel f₀

/-- Helper for Lemma 15.101.7: ideal-power submodules are nested in the expected direction when
the cutoff increases. -/
private theorem powerSubmodule_le_of_le
    (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    powerSubmodule d X n ≤ powerSubmodule c X n := by
  -- This is the standard monotonicity of `I^d E_n ⊆ I^c E_n` for `c ≤ d`.
  simpa [powerSubmodule] using
    (Submodule.pow_smul_top_le (stageIdeal A I n) (X n) h)

/-- Helper for Lemma 15.101.7: torsion submodules are nested in the expected direction when the
torsion cutoff increases. -/
private theorem torsionSubmodule_le_of_le
    (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    torsionSubmodule c X n ≤ torsionSubmodule d X n := by
  -- Increasing the torsion cutoff only enlarges the torsion submodule.
  simpa using
    (Submodule.torsionBySet_le_torsionBySet_pow c d h (stageIdeal A I n))

/-- Helper for Lemma 15.101.7: the canonical inclusion `I^d E_n ↪ I^c E_n` for `c ≤ d`. -/
private abbrev powerSubmoduleInclusionLocal
    (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    powerSubmodule d X n →ₗ[stageRing A I n] powerSubmodule c X n :=
  Submodule.inclusion (powerSubmodule_le_of_le (A := A) (I := I) X h n)

/-- Helper for Lemma 15.101.7: the canonical quotient transition induced by increasing the torsion
cutoff. -/
private noncomputable abbrev torsionQuotientMapLocal
    (X : IadicFiniteModuleSystem A I) {c d : ℕ} (h : c ≤ d) (n : ℕ+) :
    torsionQuotient c X n →ₗ[stageRing A I n] torsionQuotient d X n :=
  (torsionSubmodule c X n).mapQ
    (torsionSubmodule d X n)
    LinearMap.id
    (torsionSubmodule_le_of_le (A := A) (I := I) X h n)

/-- Helper for Lemma 15.101.7: the reflexive torsion transition map is the identity. -/
private theorem torsionQuotientMapLocal_refl_eq_id
    (X : IadicFiniteModuleSystem A I) (c : ℕ) (n : ℕ+) :
    torsionQuotientMapLocal (A := A) (I := I) X (show c ≤ c by rfl) n = LinearMap.id := by
  -- The proof argument for the unchanged cutoff is irrelevant, so the quotient transition does
  -- nothing on representatives.
  ext z
  rfl

/-- Helper for Lemma 15.101.7: composing two local torsion transitions is the direct transition
across the transitive cutoff inequality. -/
private theorem torsionQuotientMapLocal_comp_eq
    (X : IadicFiniteModuleSystem A I) {c d e : ℕ}
    (hcd : c ≤ d) (hde : d ≤ e) (n : ℕ+) :
    (torsionQuotientMapLocal (A := A) (I := I) X hde n).comp
        (torsionQuotientMapLocal (A := A) (I := I) X hcd n) =
      torsionQuotientMapLocal (A := A) (I := I) X (Nat.le_trans hcd hde) n := by
  -- Both quotient transitions keep the same chosen class and only differ by proof parameters.
  ext z
  rfl

/-- Helper for Lemma 15.101.7: the canonical quotient map from `I^d E_n` to
`E_n / E_n[I^c]`. -/
private abbrev quotientPowerMapLocal
    (c d : ℕ) (X : IadicFiniteModuleSystem A I) (n : ℕ+) :
    powerSubmodule d X n →ₗ[stageRing A I n] torsionQuotient c X n :=
  (torsionSubmodule c X n).mkQ.comp (powerSubmodule d X n).subtype

/-- Helper for Lemma 15.101.7: the inclusion `I^c E_n ↪ I^c E_n` is the identity map. -/
private theorem powerSubmoduleInclusionLocal_refl_eq_id
    (X : IadicFiniteModuleSystem A I) (c : ℕ) (n : ℕ+) :
    powerSubmoduleInclusionLocal (A := A) (I := I) X (show c ≤ c by rfl) n = LinearMap.id := by
  -- Both maps are the same subtype inclusion after proof irrelevance on the cutoff inequality.
  ext x
  rfl

/-- Helper for Lemma 15.101.7: composing two local power-submodule inclusions is the direct
inclusion across the transitive cutoff inequality. -/
private theorem powerSubmoduleInclusionLocal_comp_eq
    (X : IadicFiniteModuleSystem A I) {c d e : ℕ}
    (hcd : c ≤ d) (hde : d ≤ e) (n : ℕ+) :
    (powerSubmoduleInclusionLocal (A := A) (I := I) X hcd n).comp
        (powerSubmoduleInclusionLocal (A := A) (I := I) X hde n) =
      powerSubmoduleInclusionLocal (A := A) (I := I) X (Nat.le_trans hcd hde) n := by
  -- Both sides are the same subtype inclusion after collapsing the proof arguments.
  ext x
  rfl

/-- Helper for Lemma 15.101.7: the power-submodule `I^(c + d) E_n` is exactly `I^d (I^c E_n)`. -/
private theorem powerSubmodule_add_eq_smul
    (X : IadicFiniteModuleSystem A I) (c d : ℕ) (n : ℕ+) :
    powerSubmodule (c + d) X n =
      (stageIdeal A I n) ^ d • powerSubmodule c X n := by
  -- This is the standard ideal-power factorization behind the source proof.
  let J : Ideal (stageRing A I n) := stageIdeal A I n
  calc
    powerSubmodule (c + d) X n
        = J ^ (d + c) • (⊤ : Submodule (stageRing A I n) (X n)) := by
            simp [J, powerSubmodule, Nat.add_comm]
    _ = (J ^ d * J ^ c) • (⊤ : Submodule (stageRing A I n) (X n)) := by
          rw [pow_add]
    _ = ((J ^ d : Submodule (stageRing A I n) (stageRing A I n)) •
          (J ^ c : Submodule (stageRing A I n) (stageRing A I n))) •
            (⊤ : Submodule (stageRing A I n) (X n)) := by
          rfl
    _ = J ^ d • powerSubmodule c X n := by
          rw [Submodule.smul_assoc]

/-- Helper for Lemma 15.101.7: multiplying an element of `I^c E_n` by an element of `I^d`
lands in `I^(c + d) E_n`. -/
private theorem smul_mem_powerSubmodule_add
    (X : IadicFiniteModuleSystem A I) (c d : ℕ) (n : ℕ+)
    {a : stageRing A I n} (ha : a ∈ stageIdeal A I n ^ d)
    {x : powerSubmodule c X n} :
    a • (x : X n) ∈ powerSubmodule (c + d) X n := by
  -- We rewrite `I^(c + d) E_n` as `I^d (I^c E_n)` and apply the defining smul membership.
  have hx :
      a • (x : X n) ∈ (stageIdeal A I n) ^ d • powerSubmodule c X n := by
    exact Submodule.smul_mem_smul ha x.2
  simpa [powerSubmodule_add_eq_smul (A := A) (I := I) X c d n] using hx

/-- Helper for Lemma 15.101.7: elements that are `I^d`-torsion are automatically killed by every
element of `I^(2d)`. -/
private theorem torsionSubmodule_isTorsionBySet_square
    (X : IadicFiniteModuleSystem A I) (d : ℕ) (n : ℕ+) :
    Module.IsTorsionBySet
      (stageRing A I n)
      (torsionSubmodule d X n)
      (↑((stageIdeal A I n) ^ (2 * d)) : Set (stageRing A I n)) := by
  intro y
  -- We expand an element of `I^(2d)` as a sum of products of two `I^d` elements.
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  apply Subtype.ext
  change ((↑a : stageRing A I n) • (y : X n)) = 0
  have hy :
      ∀ b : ↑(↑((stageIdeal A I n) ^ d) : Set (stageRing A I n)),
        ((b : stageRing A I n) • (y : X n)) = 0 :=
    (Submodule.mem_torsionBySet_iff _ _).mp y.2
  have ha' :
      (↑a : stageRing A I n) ∈
        (stageIdeal A I n ^ d) •
          (stageIdeal A I n ^ d : Submodule (stageRing A I n) (stageRing A I n)) := by
    simpa [two_mul, pow_add] using a.2
  refine Submodule.smul_induction_on ha' ?_ ?_
  · intro r hr s hs
    have hsy : ((s : stageRing A I n) • (y : X n)) = 0 := hy ⟨s, hs⟩
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using
      congrArg (fun z => (r : stageRing A I n) • z) hsy
  · intro z w hz hw
    simpa [add_smul, hz, hw]

/-- Helper for Lemma 15.101.7: one explicit promotion step of a representative. This is the local
adapter copy of the source construction from Remark `15.101.6`. -/
private noncomputable def promoteOnce (f : HomRepresentative X Y) :
    HomRepresentative X Y :=
  { cutoff := f.cutoff + 1
    map := fun n hn ↦
      (torsionQuotientMapLocal (A := A) (I := I) Y (Nat.le_succ f.cutoff) n).comp
        ((f n (Nat.le_trans (Nat.le_succ f.cutoff) hn)).comp
          (powerSubmoduleInclusionLocal (A := A) (I := I) X (Nat.le_succ f.cutoff) n)) }

/-- Helper for Lemma 15.101.7: repeated promotion of a representative to a deeper cutoff. -/
private noncomputable def raise_cutoff
    (f : HomRepresentative X Y) : ℕ → HomRepresentative X Y
  | 0 => f
  | d + 1 => promoteOnce (raise_cutoff f d)

/-- Helper for Lemma 15.101.7: the local explicit promotion step is the generating promotion
relation from Remark `15.101.6`. -/
private theorem promotesTo_promoteOnce
    (f : HomRepresentative X Y) :
    HomRepresentative.promotesTo f (promoteOnce (A := A) (I := I) f) := by
  -- Both sides unfold to the same stagewise promotion formula.
  rfl

/-- Helper for Lemma 15.101.7: promoting twice in succession is the same as promoting once by the
sum of the two cutoff increments. -/
private theorem raise_cutoff_add
    (f : HomRepresentative X Y) (d e : ℕ) :
    raise_cutoff (A := A) (I := I) (raise_cutoff (A := A) (I := I) f d) e =
      raise_cutoff (A := A) (I := I) f (d + e) := by
  -- We flatten repeated promotion into a single longer promotion chain.
  induction e generalizing f with
  | zero =>
      rfl
  | succ e ihe =>
      simpa [raise_cutoff, ihe, Nat.add_assoc]

/-- Helper for Lemma 15.101.7: raising the cutoff by `d` increases the stored cutoff exactly by
`d`. -/
private theorem raise_cutoff_cutoff
    (f : HomRepresentative X Y) (d : ℕ) :
    (raise_cutoff (A := A) (I := I) f d).cutoff = f.cutoff + d := by
  -- We track the cutoff recursively through the repeated promotion steps.
  induction d with
  | zero =>
      rfl
  | succ d ih =>
      simpa [raise_cutoff, promoteOnce, ih, Nat.add_assoc]

/-- Helper for Lemma 15.101.7: evaluating a raised representative amounts to evaluating the
original representative on the included source element and then applying the canonical torsion
transition to the deeper cutoff. -/
private theorem raise_cutoff_apply_eq_torsionQuotientMapLocal
    {U V : IadicFiniteModuleSystem A I} (r : HomRepresentative U V) (d : ℕ)
    (n : ℕ+) (hn : r.cutoff + d ≤ (n : ℕ))
    (x : powerSubmodule (r.cutoff + d) U n) :
    (raise_cutoff (A := A) (I := I) r d) n hn x =
      (torsionQuotientMapLocal (A := A) (I := I) V (Nat.le_add_right r.cutoff d) n)
        (r n (Nat.le_trans (Nat.le_add_right r.cutoff d) hn)
          ((powerSubmoduleInclusionLocal (A := A) (I := I) U
            (Nat.le_add_right r.cutoff d) n) x)) := by
  -- We peel off one promotion step at a time; each step adds exactly one more torsion transition.
  induction d generalizing x with
  | zero =>
      simpa [raise_cutoff, Nat.add_zero,
        powerSubmoduleInclusionLocal_refl_eq_id (A := A) (I := I) U r.cutoff n,
        torsionQuotientMapLocal_refl_eq_id (A := A) (I := I) V r.cutoff n,
        LinearMap.id_apply]
  | succ d ih =>
      let x' : powerSubmodule (r.cutoff + d) U n :=
        (powerSubmoduleInclusionLocal (A := A) (I := I) U
          (Nat.le_succ (r.cutoff + d)) n) x
      have hih :
          (raise_cutoff (A := A) (I := I) r d) n
              (Nat.le_trans (Nat.le_succ (r.cutoff + d)) hn) x' =
            (torsionQuotientMapLocal (A := A) (I := I) V
                (Nat.le_add_right r.cutoff d) n)
              (r n (Nat.le_trans (Nat.le_add_right r.cutoff d)
                  (Nat.le_trans (Nat.le_succ (r.cutoff + d)) hn))
                ((powerSubmoduleInclusionLocal (A := A) (I := I) U
                    (Nat.le_add_right r.cutoff d) n) x')) := by
        exact ih n (Nat.le_trans (Nat.le_succ (r.cutoff + d)) hn) x'
      -- The final promotion step composes the old transition with one extra quotient transition.
      simpa [raise_cutoff, promoteOnce, x', LinearMap.comp_apply, Nat.add_assoc,
        powerSubmoduleInclusionLocal_comp_eq (A := A) (I := I) U
          (Nat.le_add_right r.cutoff d) (Nat.le_succ (r.cutoff + d)) n,
        torsionQuotientMapLocal_comp_eq (A := A) (I := I) V
          (Nat.le_add_right r.cutoff d) (Nat.le_succ (r.cutoff + d)) n] using hih

/-- Helper for Lemma 15.101.7: the identity representative raised to cutoff `d` is still the
canonical quotient map `I^d E_n → E_n / E_n[I^d]`. -/
private theorem raise_cutoff_id_apply
    (X : IadicFiniteModuleSystem A I) (d : ℕ) (n : ℕ+) (hn : d ≤ (n : ℕ))
    (x : powerSubmodule d X n) :
    (raise_cutoff (A := A) (I := I) (HomRepresentative.id X) d) n hn x =
      quotientPowerMapLocal (A := A) (I := I) d d X n x := by
  -- We unfold one promotion step at a time; for the identity representative every step is still
  -- the same quotient class of the underlying element.
  induction d generalizing x with
  | zero =>
      rfl
  | succ d ih =>
      have hih :=
        ih n (Nat.le_trans (Nat.le_succ d) hn)
          ((powerSubmoduleInclusionLocal (A := A) (I := I) X (Nat.le_succ d) n) x)
      simpa [raise_cutoff, promoteOnce, quotientPowerMapLocal, powerSubmoduleInclusionLocal,
        torsionQuotientMapLocal, LinearMap.comp_apply] using congrArg
          ((torsionQuotientMapLocal (A := A) (I := I) X (Nat.le_succ d) n)) hih

/-- Helper for Lemma 15.101.7: if the base level map already vanishes on a deep source element,
then every further cutoff raise also vanishes on that element. -/
private theorem raise_cutoff_apply_eq_zero_of_base_eq_zero
    {U V : IadicFiniteModuleSystem A I} (r : HomRepresentative U V) (d : ℕ)
    (n : ℕ+) (hn : r.cutoff + d ≤ (n : ℕ))
    (x : powerSubmodule (r.cutoff + d) U n)
    (hx :
      r n (Nat.le_trans (Nat.le_add_right r.cutoff d) hn)
        ((powerSubmoduleInclusionLocal (A := A) (I := I) U
          (Nat.le_add_right r.cutoff d) n) x) = 0) :
    (raise_cutoff (A := A) (I := I) r d) n hn x = 0 := by
  -- We peel off one promotion step at a time and keep the same vanishing source class.
  induction d generalizing x with
  | zero =>
      simpa [raise_cutoff, powerSubmoduleInclusionLocal_refl_eq_id (A := A) (I := I) U,
        LinearMap.id_apply] using hx
  | succ d ih =>
      have hx' :
          r n
              (Nat.le_trans (Nat.le_add_right r.cutoff d)
                (Nat.le_trans (Nat.le_succ (r.cutoff + d)) hn))
              ((powerSubmoduleInclusionLocal (A := A) (I := I) U
                  (Nat.le_add_right r.cutoff d) n)
                ((powerSubmoduleInclusionLocal (A := A) (I := I) U
                    (Nat.le_succ (r.cutoff + d)) n) x)) = 0 := by
        simpa [Nat.add_assoc, LinearMap.comp_apply,
          powerSubmoduleInclusionLocal_comp_eq (A := A) (I := I) U
            (Nat.le_add_right r.cutoff d) (Nat.le_succ (r.cutoff + d)) n] using hx
      have hih :
          (raise_cutoff (A := A) (I := I) r d) n
              (Nat.le_trans (Nat.le_succ (r.cutoff + d)) hn)
              ((powerSubmoduleInclusionLocal (A := A) (I := I) U
                  (Nat.le_succ (r.cutoff + d)) n) x) = 0 := by
        exact ih n (Nat.le_trans (Nat.le_succ (r.cutoff + d)) hn)
          ((powerSubmoduleInclusionLocal (A := A) (I := I) U
            (Nat.le_succ (r.cutoff + d)) n) x) hx'
      -- The last promotion step only applies the quotient transition to an already zero class.
      simpa [raise_cutoff, promoteOnce, LinearMap.comp_apply, hih]

/-- Helper for Lemma 15.101.7: every explicit cutoff raise is equivalent to the original
representative in the promotion quotient. -/
private theorem relation_raise_cutoff
    (f : HomRepresentative X Y) (d : ℕ) :
    relation A I f (raise_cutoff (A := A) (I := I) f d) := by
  -- We add one promotion step at a time and compose the generated equivalence.
  induction d with
  | zero =>
      simpa [relation, raise_cutoff] using (Relation.EqvGen.refl f)
  | succ d ih =>
      have hstep :
          relation A I
            (raise_cutoff (A := A) (I := I) f d)
            (raise_cutoff (A := A) (I := I) f (d + 1)) := by
        simpa [relation, raise_cutoff] using
          (Relation.EqvGen.rel
            (r := HomRepresentative.promotesTo)
            (a := raise_cutoff (A := A) (I := I) f d)
            (b := promoteOnce (A := A) (I := I)
              (raise_cutoff (A := A) (I := I) f d))
            (promotesTo_promoteOnce (A := A) (I := I)
              (raise_cutoff (A := A) (I := I) f d)))
      exact Relation.EqvGen.trans _ _ _ ih hstep

/-- Helper for Lemma 15.101.7: two representatives are equivalent exactly when sufficiently deep
cutoff raises of them agree strictly. -/
private theorem relation_iff_exists_common_raise_cutoff
    (f g : HomRepresentative X Y) :
    relation A I f g ↔
      ∃ d₁ d₂ : ℕ,
        raise_cutoff (A := A) (I := I) f d₁ =
          raise_cutoff (A := A) (I := I) g d₂ := by
  constructor
  · intro h
    -- We replace each zig-zag of promotion steps by equality after raising both cutoffs far enough.
    induction h with
    | rel a b hab =>
        refine ⟨1, 0, ?_⟩
        rcases hab with rfl
        rfl
    | refl a =>
        exact ⟨0, 0, rfl⟩
    | symm a b hab ih =>
        rcases ih with ⟨d₁, d₂, hEq⟩
        exact ⟨d₂, d₁, hEq.symm⟩
    | trans a b c hab hbc ihab ihbc =>
        rcases ihab with ⟨d₁, d₂, hEq₁₂⟩
        rcases ihbc with ⟨e₁, e₂, hEq₂₃⟩
        refine ⟨d₁ + e₁, e₂ + d₂, ?_⟩
        -- We keep raising both equalities until the two middle representatives coincide literally.
        have hEq₁₂' :=
          congrArg (fun hrep ↦ raise_cutoff (A := A) (I := I) hrep e₁) hEq₁₂
        have hEq₂₃' :=
          congrArg (fun hrep ↦ raise_cutoff (A := A) (I := I) hrep d₂) hEq₂₃
        calc
          raise_cutoff (A := A) (I := I) a (d₁ + e₁)
              = raise_cutoff (A := A) (I := I) b (d₂ + e₁) := by
                  simpa [raise_cutoff_add] using hEq₁₂'
          _ = raise_cutoff (A := A) (I := I) b (e₁ + d₂) := by
                rw [Nat.add_comm]
          _ = raise_cutoff (A := A) (I := I) c (e₂ + d₂) := by
                simpa [raise_cutoff_add] using hEq₂₃'
  · rintro ⟨d₁, d₂, hEq⟩
    -- Common strict equality after raising cutoffs gives a zig-zag back to the original pair.
    have hf :
        relation A I f (raise_cutoff (A := A) (I := I) f d₁) :=
      relation_raise_cutoff (A := A) (I := I) f d₁
    have hg :
        relation A I g (raise_cutoff (A := A) (I := I) g d₂) :=
      relation_raise_cutoff (A := A) (I := I) g d₂
    have hmid :
        relation A I
          (raise_cutoff (A := A) (I := I) f d₁)
          (raise_cutoff (A := A) (I := I) g d₂) := by
      simpa [relation, hEq] using
        (Relation.EqvGen.refl (raise_cutoff (A := A) (I := I) f d₁))
    exact
      Relation.EqvGen.trans _ _ _ hf <|
        Relation.EqvGen.trans _ _ _ hmid <|
          Relation.EqvGen.symm _ _ hg

/-- Helper for Lemma 15.101.7: after multiplying a quotient class by an element of `I^d`, the
result is represented by an element of `I^d E_n`. -/
private theorem smul_mem_quotientPowerMap_range
    (c d : ℕ) (Y : IadicFiniteModuleSystem A I) (n : ℕ+)
    {a : stageRing A I n} (ha : a ∈ stageIdeal A I n ^ d)
    (q : torsionQuotient c Y n) :
    a • q ∈ LinearMap.range (quotientPowerMapLocal (A := A) (I := I) c d Y n) := by
  -- We choose a representative of the quotient class and multiply it upstairs.
  obtain ⟨y, rfl⟩ := (torsionSubmodule c Y n).mkQ_surjective q
  refine ⟨⟨a • y, ?_⟩, ?_⟩
  · simpa [powerSubmodule] using
      (Submodule.smul_mem_smul ha
        (show y ∈ (⊤ : Submodule (stageRing A I n) (Y n)) from by simp))
  · rfl

/-- Helper for Lemma 15.101.7: restricting a representative to a deeper source power keeps the
same target torsion cutoff. -/
private abbrev restrictedLevelMapLocal
    (f : HomRepresentative X Y) (d : ℕ)
    (n : ℕ+) (hn : f.cutoff + d ≤ (n : ℕ)) :
    powerSubmodule (f.cutoff + d) X n →ₗ[stageRing A I n]
      torsionQuotient f.cutoff Y n :=
  (f n (Nat.le_trans (Nat.le_add_right f.cutoff d) hn)).comp
    (powerSubmoduleInclusionLocal (A := A) (I := I) X
      (Nat.le_add_right f.cutoff d) n)

/-- Helper for Lemma 15.101.7: every restricted representative value on `I^(c + d) E_n` comes
from an explicit element of `I^d E'_n`. -/
private theorem representativeImage_mem_quotientPowerMap_range_local
    (f : HomRepresentative X Y) (d : ℕ)
    (n : ℕ+) (hn : f.cutoff + d ≤ (n : ℕ))
    (x : powerSubmodule (f.cutoff + d) X n) :
    ∃ y : powerSubmodule d Y n,
      quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n y =
        restrictedLevelMapLocal (A := A) (I := I) f d n hn x := by
  let J : Ideal (stageRing A I n) := stageIdeal A I n
  have hpow :
      powerSubmodule (f.cutoff + d) X n = J ^ d • powerSubmodule f.cutoff X n := by
    -- This is the standard `I^(c + d) = I^d I^c` rewrite behind the source proof.
    simpa [J] using powerSubmodule_add_eq_smul (A := A) (I := I) X f.cutoff d n
  have hx : (x : X n) ∈ J ^ d • powerSubmodule f.cutoff X n := by
    simpa [hpow] using x.2
  -- We reduce the claim to generators of `I^d • I^c E_n`.
  refine
    Submodule.smul_induction_on' hx
      (p := fun z hz ↦
        ∃ y : powerSubmodule d Y n,
          quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n y =
            restrictedLevelMapLocal (A := A) (I := I) f d n hn ⟨z, by simpa [hpow] using hz⟩)
      ?_ ?_
  · intro a ha y hy
    -- A generator maps to a scalar multiple in the quotient, hence to an explicit deep witness.
    let φ := f n (Nat.le_trans (Nat.le_add_right f.cutoff d) hn)
    rcases
      smul_mem_quotientPowerMap_range (A := A) (I := I) f.cutoff d Y n ha
        (φ ⟨y, hy⟩)
      with ⟨w, hw⟩
    have hsmul :
        φ ⟨a • y, (powerSubmodule f.cutoff X n).smul_mem a hy⟩ =
          a • φ ⟨y, hy⟩ := by
      -- This is just linearity of the level map on the chosen generator.
      change φ (a • (⟨y, hy⟩ : powerSubmodule f.cutoff X n)) = _
      rw [LinearMap.map_smul]
    refine ⟨w, ?_⟩
    change quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n w =
      φ ⟨a • y, (powerSubmodule f.cutoff X n).smul_mem a hy⟩
    rw [hsmul]
    exact hw
  · intro z w hz hw hzmem hwmem
    let ι := powerSubmoduleInclusionLocal (A := A) (I := I) X
      (Nat.le_add_right f.cutoff d) n
    let φ := f n (Nat.le_trans (Nat.le_add_right f.cutoff d) hn)
    rcases hzmem with ⟨yz, hyz⟩
    rcases hwmem with ⟨yw, hyw⟩
    refine ⟨yz + yw, ?_⟩
    calc
      quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n (yz + yw)
          = quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n yz +
              quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n yw := by
                simp
      _ = φ (ι ⟨z, by simpa [hpow] using hz⟩) +
            φ (ι ⟨w, by simpa [hpow] using hw⟩) := by
              rw [hyz, hyw]
              simp [restrictedLevelMapLocal, ι, φ, LinearMap.comp_apply]
      _ = φ (ι ⟨z + w, by simpa [hpow] using add_mem hz hw⟩) := by
            rw [← LinearMap.map_add]
            rfl
      _ = restrictedLevelMapLocal (A := A) (I := I) f d n hn
            ⟨z + w, by simpa [hpow] using add_mem hz hw⟩ := by
            rfl

/-- Helper for Lemma 15.101.7: the restricted image canonically defines a quotient-range witness
for the local composition model. -/
private theorem representativeImage_in_quotientPowerMap_range_local
    (f : HomRepresentative X Y) (d : ℕ)
    (n : ℕ+) (hn : f.cutoff + d ≤ (n : ℕ))
    (x : powerSubmodule (f.cutoff + d) X n) :
    restrictedLevelMapLocal (A := A) (I := I) f d n hn x ∈
      LinearMap.range (quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n) := by
  -- The explicit witness from the previous lemma packages the required range membership.
  rcases representativeImage_mem_quotientPowerMap_range_local
      (A := A) (I := I) f d n hn x with
    ⟨y, hy⟩
  exact ⟨y, hy.symm⟩

/-- Helper for Lemma 15.101.7: the restricted representative value viewed inside the quotient-range
codomain used by the composition formula. -/
private noncomputable def representativeToQuotientPowerRangeLocal
    (f : HomRepresentative X Y) (d : ℕ)
    (n : ℕ+) (hn : f.cutoff + d ≤ (n : ℕ)) :
    powerSubmodule (f.cutoff + d) X n →ₗ[stageRing A I n]
      (quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n).range :=
  LinearMap.codRestrict
    (quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n).range
    (restrictedLevelMapLocal (A := A) (I := I) f d n hn)
    (representativeImage_in_quotientPowerMap_range_local (A := A) (I := I) f d n hn)

/-- Helper for Lemma 15.101.7: the promoted target-level map before descending through the
quotient-range model. -/
private noncomputable abbrev promotedLevelMapAuxLocal
    (c : ℕ) {Y Z : IadicFiniteModuleSystem A I} (g : HomRepresentative Y Z)
    (n : ℕ+) (hn : c + g.cutoff ≤ (n : ℕ)) :
    powerSubmodule g.cutoff Y n →ₗ[stageRing A I n]
      torsionQuotient (c + g.cutoff) Z n :=
  (torsionQuotientMapLocal (A := A) (I := I) Z (Nat.le_add_left g.cutoff c) n).comp
    (g n (Nat.le_trans (Nat.le_add_left g.cutoff c) hn))

/-- Helper for Lemma 15.101.7: a quotient class that is already `I^c`-torsion dies after enlarging
the target torsion cutoff by `c`. -/
private theorem torsionQuotientMapLocal_eq_zero_of_mem_torsion
    {Z : IadicFiniteModuleSystem A I} (c d : ℕ) (n : ℕ+)
    {q : torsionQuotient d Z n}
    (hq : q ∈
      Submodule.torsionBySet (stageRing A I n) (torsionQuotient d Z n)
        (↑((stageIdeal A I n) ^ c) : Set (stageRing A I n))) :
    (torsionQuotientMapLocal (A := A) (I := I) Z
      (show d ≤ c + d by exact Nat.le_add_left d c) n) q = 0 := by
  obtain ⟨z, rfl⟩ := (torsionSubmodule d Z n).mkQ_surjective q
  -- We show directly that the chosen representative lies in the larger torsion submodule.
  change (Submodule.Quotient.mk z : torsionQuotient (c + d) Z n) = 0
  refine (Submodule.Quotient.mk_eq_zero (p := torsionSubmodule (c + d) Z n)).2 ?_
  rw [Submodule.mem_torsionBySet_iff]
  intro b
  have hb :
      (↑b : stageRing A I n) ∈
        (stageIdeal A I n ^ c) •
          (stageIdeal A I n ^ d : Submodule (stageRing A I n) (stageRing A I n)) := by
    simpa [pow_add] using b.2
  -- Every generator of `I^c I^d` kills the chosen representative.
  refine Submodule.smul_induction_on hb ?_ ?_
  · intro a ha r hr
    have haq : (a : stageRing A I n) • (Submodule.Quotient.mk z : torsionQuotient d Z n) = 0 := by
      exact (Submodule.mem_torsionBySet_iff _ _).mp hq ⟨a, ha⟩
    have haz : (a : stageRing A I n) • z ∈ torsionSubmodule d Z n := by
      exact (Submodule.Quotient.mk_eq_zero
        (p := torsionSubmodule d Z n)).1 <| by
          simpa using haq
    have hrz : (r : stageRing A I n) • ((a : stageRing A I n) • z) = 0 := by
      exact (Submodule.mem_torsionBySet_iff _ _).mp haz ⟨r, hr⟩
    simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using hrz
  · intro x y hx hy
    simp [add_smul, hx, hy]

/-- Helper for Lemma 15.101.7: if a quotient class dies after enlarging the torsion cutoff to
`e`, then the original class is `I^e`-torsion. -/
private theorem mem_torsionBySet_of_torsionQuotientMapLocal_eq_zero
    {Z : IadicFiniteModuleSystem A I} {c e : ℕ} (hce : c ≤ e) (n : ℕ+)
    {q : torsionQuotient c Z n}
    (hq :
      (torsionQuotientMapLocal (A := A) (I := I) Z hce n) q = 0) :
    q ∈
      Submodule.torsionBySet
        (stageRing A I n)
        (torsionQuotient c Z n)
        (↑((stageIdeal A I n) ^ e) : Set (stageRing A I n)) := by
  obtain ⟨z, rfl⟩ := (torsionSubmodule c Z n).mkQ_surjective q
  rw [Submodule.mem_torsionBySet_iff]
  intro a
  change ((Submodule.Quotient.mk ((a : stageRing A I n) • z) :
      torsionQuotient c Z n)) = 0
  have hz_torsion : z ∈ torsionSubmodule e Z n := by
    change (Submodule.Quotient.mk z : torsionQuotient e Z n) = 0 at hq
    exact (Submodule.Quotient.mk_eq_zero (p := torsionSubmodule e Z n)).1 hq
  exact (Submodule.mem_torsionBySet_iff _ _).mp hz_torsion a

/-- Helper for Lemma 15.101.7: the descended promoted map vanishes on the kernel of the quotient
power map, so it factors through the quotient-range model. -/
private theorem quotientPowerMapLocal_ker_le_promotedLevelMapAuxLocal_ker
    (c : ℕ) {Y Z : IadicFiniteModuleSystem A I} (g : HomRepresentative Y Z)
    (n : ℕ+) (hn : c + g.cutoff ≤ (n : ℕ)) :
    LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n) ≤
      LinearMap.ker (promotedLevelMapAuxLocal (A := A) (I := I) c g n hn) := by
  intro y hy
  rw [LinearMap.mem_ker] at hy ⊢
  -- The kernel condition says that the chosen deep element is already `I^c`-torsion upstairs.
  have hy_torsion : ((powerSubmodule g.cutoff Y n).subtype y : Y n) ∈ torsionSubmodule c Y n := by
    exact (Submodule.Quotient.mk_eq_zero
      (p := torsionSubmodule c Y n)).1 <| by
        simpa [quotientPowerMapLocal, LinearMap.comp_apply] using hy
  have hq_torsion :
      g n (Nat.le_trans (Nat.le_add_left g.cutoff c) hn) y ∈
        Submodule.torsionBySet
          (stageRing A I n)
          (torsionQuotient g.cutoff Z n)
          (↑((stageIdeal A I n) ^ c) : Set (stageRing A I n)) := by
    -- Linearity transfers the torsion relation through the level map.
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have hay : (↑a : stageRing A I n) • ((powerSubmodule g.cutoff Y n).subtype y : Y n) = 0 := by
      exact (Submodule.mem_torsionBySet_iff _ _).mp hy_torsion a
    have hay' : (↑a : stageRing A I n) • y = 0 := by
      apply Subtype.ext
      simpa using hay
    rw [← LinearMap.map_smul, hay', map_zero]
  -- Enlarging the torsion cutoff annihilates that already torsion class.
  simpa [promotedLevelMapAuxLocal, LinearMap.comp_apply] using
    torsionQuotientMapLocal_eq_zero_of_mem_torsion
      (A := A) (I := I) c g.cutoff n hq_torsion

/-- Helper for Lemma 15.101.7: the quotient-range model descended from the promoted target-level
map. -/
private noncomputable def promotedLevelMapLocal
    (c : ℕ) {Y Z : IadicFiniteModuleSystem A I} (g : HomRepresentative Y Z)
    (n : ℕ+) (hn : c + g.cutoff ≤ (n : ℕ)) :
    (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n).range →ₗ[stageRing A I n]
      torsionQuotient (c + g.cutoff) Z n :=
  let lifted :
      powerSubmodule g.cutoff Y n ⧸
          LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n) →ₗ[stageRing A I n]
          torsionQuotient (c + g.cutoff) Z n :=
    (LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n)).liftQ
      (promotedLevelMapAuxLocal (A := A) (I := I) c g n hn)
      (quotientPowerMapLocal_ker_le_promotedLevelMapAuxLocal_ker
        (A := A) (I := I) c g n hn)
  lifted.comp
    (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n).quotKerEquivRange.symm.toLinearMap

/-- Helper for Lemma 15.101.7: on a canonical quotient-power witness, the descended range map
agrees with the obvious promoted target-level formula. -/
@[simp] private theorem promotedLevelMapLocal_apply_quotientPowerMapLocal
    (c : ℕ) {Y Z : IadicFiniteModuleSystem A I} (g : HomRepresentative Y Z)
    (n : ℕ+) (hn : c + g.cutoff ≤ (n : ℕ))
    (y : powerSubmodule g.cutoff Y n) :
    promotedLevelMapLocal (A := A) (I := I) c g n hn
      ⟨quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n y,
        LinearMap.mem_range_self _ y⟩ =
      promotedLevelMapAuxLocal (A := A) (I := I) c g n hn y := by
  -- We unwind the quotient-range wrapper and reduce to the defining `liftQ` computation.
  rw [promotedLevelMapLocal]
  dsimp
  have hs :
      (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n).quotKerEquivRange.symm
        ⟨quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n y,
          LinearMap.mem_range_self _ y⟩ =
        (LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n)).mkQ y := by
    simpa [quotientPowerMapLocal, LinearMap.comp_apply] using
      (LinearMap.quotKerEquivRange_symm_apply_image
        (f := quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n) y
        (LinearMap.mem_range_self _ y))
  rw [hs]
  have hlift :
      (((LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n)).liftQ
          (promotedLevelMapAuxLocal (A := A) (I := I) c g n hn)
          (quotientPowerMapLocal_ker_le_promotedLevelMapAuxLocal_ker
            (A := A) (I := I) c g n hn)).comp
        (LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n)).mkQ) =
        promotedLevelMapAuxLocal (A := A) (I := I) c g n hn := by
    exact
      Submodule.liftQ_mkQ
        (p := LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n))
        (f := promotedLevelMapAuxLocal (A := A) (I := I) c g n hn)
        (h := quotientPowerMapLocal_ker_le_promotedLevelMapAuxLocal_ker
          (A := A) (I := I) c g n hn)
  change
    (((LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n)).liftQ
        (promotedLevelMapAuxLocal (A := A) (I := I) c g n hn)
        (quotientPowerMapLocal_ker_le_promotedLevelMapAuxLocal_ker
          (A := A) (I := I) c g n hn))
      ((LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) c g.cutoff Y n)).mkQ y)) =
      promotedLevelMapAuxLocal (A := A) (I := I) c g n hn y
  simpa [LinearMap.comp_apply] using congrArg (fun φ ↦ φ y) hlift

/-- Helper for Lemma 15.101.7: a chosen quotient-power witness computes the value of the composed
representative in the local normalization model. -/
private theorem comp_apply_of_range_witness_local
    (f : HomRepresentative X Y) (g : HomRepresentative Y Z)
    (n : ℕ+) (hn : f.cutoff + g.cutoff ≤ (n : ℕ))
    (x : powerSubmodule (f.cutoff + g.cutoff) X n)
    (y : powerSubmodule g.cutoff Y n)
    (hy : quotientPowerMapLocal (A := A) (I := I) f.cutoff g.cutoff Y n y =
      restrictedLevelMapLocal (A := A) (I := I) f g.cutoff n hn x) :
    (f.comp g) n hn x =
      promotedLevelMapAuxLocal (A := A) (I := I) f.cutoff g n hn y := by
  -- We replace the codomain witness inside the composition formula by the chosen explicit one.
  change
    promotedLevelMapLocal (A := A) (I := I) f.cutoff g n hn
      (representativeToQuotientPowerRangeLocal (A := A) (I := I) f g.cutoff n hn x) =
        promotedLevelMapAuxLocal (A := A) (I := I) f.cutoff g n hn y
  have hwitness :
      representativeToQuotientPowerRangeLocal (A := A) (I := I) f g.cutoff n hn x =
        ⟨quotientPowerMapLocal (A := A) (I := I) f.cutoff g.cutoff Y n y,
          LinearMap.mem_range_self _ y⟩ := by
    apply Subtype.ext
    simpa [representativeToQuotientPowerRangeLocal, restrictedLevelMapLocal] using hy.symm
  rw [hwitness]
  -- On a canonical witness, the descended map evaluates by the explicit promoted formula.
  simpa using
    promotedLevelMapLocal_apply_quotientPowerMapLocal
      (A := A) (I := I) f.cutoff g n hn y

/-- Helper for Lemma 15.101.7: if the level cokernel is `I^c'`-torsion, then every element of a
deeper target power submodule already comes from the level map modulo `I^{f.cutoff}`-torsion. -/
private theorem quotientPowerMap_mem_range_of_cokernel_torsion
    (f : HomRepresentative X Y) {c' d : ℕ} (hcd : c' ≤ d)
    (n : ℕ+) (hn : f.cutoff ≤ (n : ℕ))
    (hcoker :
      Module.IsTorsionBySet
        (stageRing A I n)
        (levelCokernel f ⟨n, hn⟩)
        (↑((stageIdeal A I n) ^ c') : Set (stageRing A I n)))
    (x : powerSubmodule d Y n) :
    quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n x ∈
      LinearMap.range (f n hn) := by
  let J : Ideal (stageRing A I n) := stageIdeal A I n
  have hclass_zero_of_mem :
      ∀ z : Y n, ∀ hz : z ∈ powerSubmodule c' Y n,
        (Submodule.Quotient.mk
            (quotientPowerMapLocal (A := A) (I := I) f.cutoff c' Y n ⟨z, hz⟩) :
          levelCokernel f ⟨n, hn⟩) = 0 := by
    intro z hz
    have hz' : z ∈ J ^ c' • (⊤ : Submodule (stageRing A I n) (Y n)) := by
      simpa [J, powerSubmodule] using hz
    -- We expand the deep element as a sum of generators from `I^c' E_n`.
    refine Submodule.smul_induction_on' hz' ?_ ?_
    · intro a ha y hy
      let q : torsionQuotient f.cutoff Y n := Submodule.Quotient.mk y
      have hq :
          (a : stageRing A I n) •
            (Submodule.Quotient.mk q : levelCokernel f ⟨n, hn⟩) = 0 := by
        exact (Submodule.mem_torsionBySet_iff _ _).mp
          (hcoker (Submodule.Quotient.mk q)) ⟨a, ha⟩
      -- A generator `a • y` maps to the corresponding scalar multiple in the cokernel.
      simpa [J, q, quotientPowerMapLocal, LinearMap.comp_apply] using hq
    · intro z w hz hw hzero_z hzero_w
      -- Additivity lets us combine the two previously vanishing classes.
      simpa [quotientPowerMapLocal, LinearMap.comp_apply, hzero_z, hzero_w]
  have hx' : (x : Y n) ∈ powerSubmodule c' Y n := by
    exact (powerSubmodule_le_of_le (A := A) (I := I) Y hcd n) x.2
  have hclass_zero :
      (Submodule.Quotient.mk
          (quotientPowerMapLocal (A := A) (I := I) f.cutoff d Y n x) :
        levelCokernel f ⟨n, hn⟩) = 0 := by
    -- Dropping from cutoff `d` to cutoff `c'` does not change the underlying quotient class.
    simpa [quotientPowerMapLocal, LinearMap.comp_apply] using
      hclass_zero_of_mem (x : Y n) hx'
  -- Vanishing in the quotient by the range means the chosen class already lies in the range.
  exact
    (Submodule.Quotient.mk_eq_zero (p := LinearMap.range (f n hn))).1 hclass_zero

/-- Helper for Lemma 15.101.7: if the level kernel is `I^d`-torsion, then the quotient map
`I^{f.cutoff} E_n → E_n / E_n[I^d]` descends canonically through the range of `f_n`. -/
private theorem range_descend_to_torsionQuotient
    (f : HomRepresentative X Y) {d : ℕ} (hfd : f.cutoff ≤ d)
    (n : ℕ+) (hn : d ≤ (n : ℕ))
    (hkernel :
      Module.IsTorsionBySet
        (stageRing A I n)
        (levelKernel f ⟨n, Nat.le_trans hfd hn⟩)
        (↑((stageIdeal A I n) ^ d) : Set (stageRing A I n))) :
    ∃ ψrange : LinearMap.range (f n (Nat.le_trans hfd hn)) →ₗ[stageRing A I n]
        torsionQuotient d X n,
      ψrange.comp (LinearMap.rangeRestrict (f n (Nat.le_trans hfd hn))) =
        quotientPowerMapLocal (A := A) (I := I) d f.cutoff X n := by
  let φ := f n (Nat.le_trans hfd hn)
  have hker_le :
      LinearMap.ker φ ≤
        LinearMap.ker (quotientPowerMapLocal (A := A) (I := I) d f.cutoff X n) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change (Submodule.Quotient.mk ((x : powerSubmodule f.cutoff X n) : X n) :
      torsionQuotient d X n) = 0
    -- A kernel element is `I^d`-torsion by hypothesis, hence zero in the quotient by
    -- `torsionSubmodule d`.
    refine (Submodule.Quotient.mk_eq_zero (p := torsionSubmodule d X n)).2 ?_
    rw [Submodule.mem_torsionBySet_iff]
    intro a
    have hx_torsion :
        ⟨x, hx⟩ ∈
          Submodule.torsionBySet
            (stageRing A I n)
            (levelKernel f ⟨n, Nat.le_trans hfd hn⟩)
            (↑((stageIdeal A I n) ^ d) : Set (stageRing A I n)) := by
      exact hkernel ⟨x, hx⟩
    have hx_zero :
        (a : stageRing A I n) • (⟨x, hx⟩ : levelKernel f ⟨n, Nat.le_trans hfd hn⟩) = 0 := by
      exact (Submodule.mem_torsionBySet_iff _ _).mp hx_torsion a
    exact Subtype.ext_iff_val.mp hx_zero
  let lifted :
      powerSubmodule f.cutoff X n ⧸ LinearMap.ker φ →ₗ[stageRing A I n]
        torsionQuotient d X n :=
    (LinearMap.ker φ).liftQ
      (quotientPowerMapLocal (A := A) (I := I) d f.cutoff X n)
      hker_le
  let ψrange :
      LinearMap.range φ →ₗ[stageRing A I n] torsionQuotient d X n :=
    lifted.comp φ.quotKerEquivRange.symm.toLinearMap
  refine ⟨ψrange, ?_⟩
  -- We compare both sides on actual images, where `quotKerEquivRange.symm` and `liftQ`
  -- normalize to their defining formulas.
  ext x
  have hs :
      φ.quotKerEquivRange.symm ⟨φ x, LinearMap.mem_range_self _ x⟩ =
        (LinearMap.ker φ).mkQ x := by
    simpa using
      (LinearMap.quotKerEquivRange_symm_apply_image
        (f := φ) x (LinearMap.mem_range_self _ x))
  have hlift :
      lifted.comp (LinearMap.ker φ).mkQ =
        quotientPowerMapLocal (A := A) (I := I) d f.cutoff X n := by
    exact
      (Submodule.liftQ_mkQ
        (p := LinearMap.ker φ)
        (f := quotientPowerMapLocal (A := A) (I := I) d f.cutoff X n)
        (h := hker_le))
  change ψrange ⟨φ x, LinearMap.mem_range_self _ x⟩ =
    quotientPowerMapLocal (A := A) (I := I) d f.cutoff X n x
  rw [show LinearMap.rangeRestrict φ x = ⟨φ x, LinearMap.mem_range_self _ x⟩ by rfl]
  change lifted (φ.quotKerEquivRange.symm ⟨φ x, LinearMap.mem_range_self _ x⟩) =
    quotientPowerMapLocal (A := A) (I := I) d f.cutoff X n x
  rw [hs]
  simpa [lifted, LinearMap.comp_apply] using congrArg (fun ψ => ψ x) hlift

/-- Helper for Lemma 15.101.7: if every `I^d`-multiple of an element is already `I^d`-torsion,
then the element is `I^(2d)`-torsion. -/
private theorem mem_torsionSubmodule_two_mul_of_smul_mem_torsionSubmodule
    (X : IadicFiniteModuleSystem A I) (d : ℕ) (n : ℕ+) {x : X n}
    (hx : ∀ a : ↑(↑((stageIdeal A I n) ^ d) : Set (stageRing A I n)),
      (a : stageRing A I n) • x ∈ torsionSubmodule d X n) :
    x ∈ torsionSubmodule (2 * d) X n := by
  rw [Submodule.mem_torsionBySet_iff]
  intro b
  have hb :
      (↑b : stageRing A I n) ∈
        (stageIdeal A I n ^ d) •
          (stageIdeal A I n ^ d : Submodule (stageRing A I n) (stageRing A I n)) := by
    simpa [two_mul, pow_add] using b.2
  -- We expand an element of `I^(2d)` as a sum of products of two `I^d` elements.
  refine Submodule.smul_induction_on hb ?_ ?_
  · intro r hr s hs
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hx ⟨s, hs⟩) ⟨r, hr⟩
  · intro y z hy hz
    simpa [add_smul, hy, hz]

/-- Helper for Lemma 15.101.7: if every `I^d`-multiple of a module element is already `I^d`-torsion
inside that module, then the element is `I^(2d)`-torsion. -/
private theorem mem_torsionBySet_two_mul_of_smul_mem_torsionBySet
    {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    (J : Ideal R) (d : ℕ) {x : M}
    (hx : ∀ a : ↑(↑(J ^ d) : Set R),
      (a : R) • x ∈ Submodule.torsionBySet R M ↑(J ^ d)) :
    x ∈ Submodule.torsionBySet R M ↑(J ^ (2 * d)) := by
  rw [Submodule.mem_torsionBySet_iff]
  intro b
  have hb :
      (↑b : R) ∈
        (J ^ d) • (J ^ d : Submodule R R) := by
    simpa [two_mul, pow_add] using b.2
  -- We expand an element of `I^(2d)` as a sum of products of two `I^d` elements.
  refine Submodule.smul_induction_on hb ?_ ?_
  · intro r hr s hs
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hx ⟨s, hs⟩) ⟨r, hr⟩
  · intro y z hy hz
    simpa [add_smul, hy, hz]

/-- Helper for Lemma 15.101.7: if a representative has a two-sided inverse up to the promotion
relation, then its level kernels and cokernels become uniformly torsion. -/
private theorem hasEventuallyBoundedKernelAndCokernel_of_related_inverse
    (f : HomRepresentative X Y)
    {g : HomRepresentative Y X}
    (hfg : relation A I (f.comp g) (HomRepresentative.id X))
    (hgf : relation A I (g.comp f) (HomRepresentative.id Y)) :
    hasEventuallyBoundedKernelAndCokernel f := by
  -- Route correction: the fixed-level promotion comparison route stalled because promotion changes
  -- both source and target cutoffs. The common-raised-cutoff normalization above is the right
  -- source-faithful replacement.
  rcases (relation_iff_exists_common_raise_cutoff
    (A := A) (I := I) (X := X) (Y := X) (f := f.comp g) (g := HomRepresentative.id X)).1 hfg with
    ⟨d_left, e_left, hleft⟩
  rcases (relation_iff_exists_common_raise_cutoff
    (A := A) (I := I) (X := Y) (Y := Y) (f := g.comp f) (g := HomRepresentative.id Y)).1 hgf with
    ⟨d_right, e_right, hright⟩
  have hleft_cutoff :
      f.cutoff + g.cutoff + d_left = e_left := by
    -- Equality of raised representatives forces equality of their literal cutoffs.
    simpa [raise_cutoff_cutoff, HomRepresentative.comp, Nat.add_assoc] using
      congrArg HomRepresentative.cutoff hleft
  have hright_cutoff :
      g.cutoff + f.cutoff + d_right = e_right := by
    -- The same cutoff comparison applies to the other composite.
    simpa [raise_cutoff_cutoff, HomRepresentative.comp, Nat.add_assoc] using
      congrArg HomRepresentative.cutoff hright
  let D0 := max (f.cutoff + g.cutoff + d_left) (g.cutoff + f.cutoff + d_right)
  let D := 2 * D0
  refine ⟨D, D, ?_, ?_⟩
  · -- Choosing `N = D` is enough because `D` dominates both composite cutoffs.
    have hf_le_D0 : f.cutoff ≤ D0 := by
      exact Nat.le_trans
        (Nat.le_add_right f.cutoff (g.cutoff + d_left))
        (Nat.le_max_left _ _)
    have hD0_le_D : D0 ≤ D := by
      simpa [D, two_mul] using Nat.le_add_right D0 D0
    exact Nat.le_trans hf_le_D0 hD0_le_D
  · intro n hn
    have hD0_le : D0 ≤ (n : ℕ) := by
      have hD0_le_D : D0 ≤ D := by
        simpa [D, two_mul] using Nat.le_add_right D0 D0
      exact Nat.le_trans hD0_le_D hn
    have hn_left : f.cutoff + g.cutoff + d_left ≤ (n : ℕ) :=
      Nat.le_trans (Nat.le_max_left _ _) hD0_le
    have hn_right : g.cutoff + f.cutoff + d_right ≤ (n : ℕ) :=
      Nat.le_trans (Nat.le_max_right _ _) hD0_le
    have hkernel_torsion :
        Module.IsTorsionBySet
          (stageRing A I n)
          (levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
            (Nat.le_add_right f.cutoff g.cutoff)
            (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩)
          (↑((stageIdeal A I n) ^ D) : Set (stageRing A I n)) := by
      intro x
      -- We first show that every `I^D0`-multiple of a kernel element becomes `I^D0`-torsion.
      have hx_torsion_D0 :
          ∀ a : ↑(↑((stageIdeal A I n) ^ D0) : Set (stageRing A I n)),
            (a : stageRing A I n) •
                (((x : levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
                  (Nat.le_add_right f.cutoff g.cutoff)
                  (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩) :
                    powerSubmodule f.cutoff X n) : X n) ∈
              torsionSubmodule D0 X n := by
        intro a
        have hgd_left : g.cutoff + d_left ≤ D0 := by
          omega
        have ha_left :
            (a : stageRing A I n) ∈ (stageIdeal A I n) ^ (g.cutoff + d_left) := by
          exact (Ideal.pow_le_pow_right hgd_left) a.2
        have hxdeep_mem :
            (a : stageRing A I n) •
                (((x : levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
                  (Nat.le_add_right f.cutoff g.cutoff)
                  (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩) :
                    powerSubmodule f.cutoff X n) : X n) ∈
              powerSubmodule (f.cutoff + (g.cutoff + d_left)) X n := by
          simpa [Nat.add_assoc] using
            smul_mem_powerSubmodule_add
              (A := A) (I := I) X f.cutoff (g.cutoff + d_left) n ha_left
              (x := (x : levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
                (Nat.le_add_right f.cutoff g.cutoff)
                (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩))
        let xdeep : powerSubmodule (f.cutoff + g.cutoff + d_left) X n :=
          ⟨(a : stageRing A I n) •
              (((x : levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
                (Nat.le_add_right f.cutoff g.cutoff)
                (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩) :
                  powerSubmodule f.cutoff X n) : X n),
            by simpa [Nat.add_assoc] using hxdeep_mem⟩
        have hn_fg : f.cutoff + g.cutoff ≤ (n : ℕ) := by
          exact Nat.le_trans (Nat.le_add_right (f.cutoff + g.cutoff) d_left) hn_left
        let xbase : powerSubmodule (f.cutoff + g.cutoff) X n :=
          powerSubmoduleInclusionLocal (A := A) (I := I) X
            (Nat.le_add_right (f.cutoff + g.cutoff) d_left) n xdeep
        have hmap_zero_direct :
            f n
                (Nat.le_trans (Nat.le_trans (Nat.le_add_right f.cutoff g.cutoff)
                  (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left)
                ((powerSubmoduleInclusionLocal (A := A) (I := I) X
                    (Nat.le_trans (Nat.le_add_right f.cutoff g.cutoff)
                      (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) n) xdeep) = 0 := by
          -- The direct inclusion of `xdeep` back to cutoff `f.cutoff` is just `a • x`.
          change f n
              (Nat.le_trans (Nat.le_trans (Nat.le_add_right f.cutoff g.cutoff)
                (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left)
              ((a : stageRing A I n) •
                (x : levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
                  (Nat.le_add_right f.cutoff g.cutoff)
                  (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩)) = 0
          rw [LinearMap.map_smul, x.2, smul_zero]
        have hrestricted_zero :
            restrictedLevelMapLocal (A := A) (I := I) f g.cutoff n hn_fg xbase = 0 := by
          -- The intermediate source-power inclusions collapse to the direct inclusion above.
          change f n (Nat.le_trans (Nat.le_add_right f.cutoff g.cutoff) hn_fg)
              ((powerSubmoduleInclusionLocal (A := A) (I := I) X
                  (Nat.le_add_right f.cutoff g.cutoff) n) xbase) = 0
          simpa [restrictedLevelMapLocal, xbase, hn_fg, LinearMap.comp_apply, Nat.add_assoc,
            powerSubmoduleInclusionLocal_comp_eq (A := A) (I := I) X
              (Nat.le_add_right f.cutoff g.cutoff)
              (Nat.le_add_right (f.cutoff + g.cutoff) d_left) n] using hmap_zero_direct
        have hcomp_zero :
            (f.comp g) n hn_fg xbase = 0 := by
          have hy_zero :
              quotientPowerMapLocal (A := A) (I := I) f.cutoff g.cutoff Y n
                  (0 : powerSubmodule g.cutoff Y n) =
                restrictedLevelMapLocal (A := A) (I := I) f g.cutoff n hn_fg xbase := by
            simpa [hrestricted_zero]
          have hcomp_eval :=
            comp_apply_of_range_witness_local (A := A) (I := I) f g n hn_fg xbase
              (0 : powerSubmodule g.cutoff Y n) hy_zero
          simpa [promotedLevelMapAuxLocal, LinearMap.comp_apply] using hcomp_eval
        have hraised_zero :
            (raise_cutoff (A := A) (I := I) (f.comp g) d_left) n hn_left xdeep = 0 := by
          exact raise_cutoff_apply_eq_zero_of_base_eq_zero
            (A := A) (I := I) (r := f.comp g) d_left n hn_left xdeep hcomp_zero
        have hleft_eval :
            (raise_cutoff (A := A) (I := I) (HomRepresentative.id X) e_left) n hn_left xdeep = 0 := by
          have happly := congrArg (fun hrep ↦ hrep n hn_left xdeep) hleft
          simpa [hraised_zero] using happly.symm
        have hx_torsion_left :
            (a : stageRing A I n) •
                (((x : levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
                  (Nat.le_add_right f.cutoff g.cutoff)
                  (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩) :
                    powerSubmodule f.cutoff X n) : X n) ∈
              torsionSubmodule e_left X n := by
          exact (Submodule.Quotient.mk_eq_zero (p := torsionSubmodule e_left X n)).1 <| by
            simpa [raise_cutoff_id_apply (A := A) (I := I) X e_left n hn_left xdeep,
              quotientPowerMapLocal, LinearMap.comp_apply, xdeep, Nat.add_assoc] using hleft_eval
        exact
          torsionSubmodule_le_of_le (A := A) (I := I) X
            (show e_left ≤ D0 by exact Nat.le_max_left _ _) n hx_torsion_left
      have hx_torsion_D :
          (((x : levelKernel f ⟨n, Nat.le_trans (Nat.le_trans
            (Nat.le_add_right f.cutoff g.cutoff)
            (Nat.le_add_right (f.cutoff + g.cutoff) d_left)) hn_left⟩) :
              powerSubmodule f.cutoff X n) : X n) ∈
            torsionSubmodule D X n := by
        simpa [D, two_mul] using
          mem_torsionSubmodule_two_mul_of_smul_mem_torsionSubmodule
            (A := A) (I := I) X D0 n hx_torsion_D0
      -- Converting the ambient torsion statement back to the level-kernel subtype is now formal.
      rw [Submodule.mem_torsionBySet_iff]
      intro a
      apply Subtype.ext
      simpa [D] using (Submodule.mem_torsionBySet_iff _ _).mp hx_torsion_D a
    have hcokernel_torsion :
        Module.IsTorsionBySet
          (stageRing A I n)
          (levelCokernel f ⟨n, Nat.le_trans (Nat.le_trans
            (Nat.le_add_right f.cutoff g.cutoff)
            (Nat.le_add_right (f.cutoff + g.cutoff) d_right)) (by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn_right)⟩)
          (↑((stageIdeal A I n) ^ D) : Set (stageRing A I n)) := by
      let hnf :
          f.cutoff ≤ (n : ℕ) :=
        Nat.le_trans (Nat.le_trans
          (Nat.le_add_right f.cutoff g.cutoff)
          (Nat.le_add_right (f.cutoff + g.cutoff) d_right)) <|
            by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn_right
      intro q
      -- We first show that every `I^D0`-multiple of a cokernel class is already `I^D0`-torsion.
      have hq_torsion_D0 :
          ∀ a : ↑(↑((stageIdeal A I n) ^ D0) : Set (stageRing A I n)),
            (a : stageRing A I n) • q ∈
              Submodule.torsionBySet
                (stageRing A I n)
                (levelCokernel f ⟨n, hnf⟩)
                (↑((stageIdeal A I n) ^ D0) : Set (stageRing A I n)) := by
        intro a
        rw [Submodule.mem_torsionBySet_iff]
        intro b
        obtain ⟨q0, rfl⟩ := (LinearMap.range (f n hnf)).mkQ_surjective q
        -- We choose a deep representative of `a • q0` at the common right cutoff.
        rcases
          smul_mem_quotientPowerMap_range
            (A := A) (I := I) f.cutoff D0 Y n a.2 q0 with
          ⟨yD0, hyD0⟩
        have hright_le_D0 : g.cutoff + f.cutoff + d_right ≤ D0 := by
          exact Nat.le_max_right _ _
        let yright : powerSubmodule (g.cutoff + f.cutoff + d_right) Y n :=
          powerSubmoduleInclusionLocal (A := A) (I := I) Y hright_le_D0 n yD0
        have hyright :
            quotientPowerMapLocal (A := A) (I := I) f.cutoff
                (g.cutoff + f.cutoff + d_right) Y n yright =
              (a : stageRing A I n) • q0 := by
          simpa [yright, quotientPowerMapLocal, LinearMap.comp_apply] using hyD0
        have hn_gf : g.cutoff + f.cutoff ≤ (n : ℕ) := by
          exact Nat.le_trans (Nat.le_add_right (g.cutoff + f.cutoff) d_right) hn_right
        let ybase : powerSubmodule (g.cutoff + f.cutoff) Y n :=
          powerSubmoduleInclusionLocal (A := A) (I := I) Y
            (Nat.le_add_right (g.cutoff + f.cutoff) d_right) n yright
        obtain ⟨x, hx⟩ :=
          representativeImage_mem_quotientPowerMap_range_local
            (A := A) (I := I) (f := g) f.cutoff n hn_gf ybase
        have hcomp_eval :
            (g.comp f) n hn_gf ybase =
              promotedLevelMapAuxLocal (A := A) (I := I) g.cutoff f n hn_gf x := by
          exact
            comp_apply_of_range_witness_local
              (A := A) (I := I) g f n hn_gf ybase x hx
        have hdeep_left :
            (raise_cutoff (A := A) (I := I) (g.comp f) d_right) n hn_right yright =
              (torsionQuotientMapLocal (A := A) (I := I) Y
                  (show f.cutoff ≤ g.cutoff + f.cutoff + d_right by omega) n)
                (f n hnf x) := by
          -- Evaluating the raised composite and then normalizing the composition formula exposes a
          -- direct transition of the original level map `f_n`.
          simpa [ybase, promotedLevelMapAuxLocal, LinearMap.comp_apply, hcomp_eval,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm,
            torsionQuotientMapLocal_comp_eq (A := A) (I := I) Y
              (Nat.le_add_left f.cutoff g.cutoff)
              (Nat.le_add_right (g.cutoff + f.cutoff) d_right) n] using
            raise_cutoff_apply_eq_torsionQuotientMapLocal
              (A := A) (I := I) (r := g.comp f) d_right n hn_right yright
        have happly := congrArg (fun hrep ↦ hrep n hn_right yright) hright
        have hdeep_eq :
            (torsionQuotientMapLocal (A := A) (I := I) Y
                (show f.cutoff ≤ g.cutoff + f.cutoff + d_right by omega) n)
              ((a : stageRing A I n) • q0) =
            (torsionQuotientMapLocal (A := A) (I := I) Y
                (show f.cutoff ≤ g.cutoff + f.cutoff + d_right by omega) n)
              (f n hnf x) := by
          -- The common raised right-identity identifies the deep transition of `a • q0` with a
          -- deep transition of a value already in the range of `f_n`.
          simpa [hdeep_left, hyright, raise_cutoff_id_apply (A := A) (I := I) Y e_right n
            (by simpa [hright_cutoff, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hn_right)
            (by simpa [hright_cutoff, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using yright),
            hright_cutoff, quotientPowerMapLocal, torsionQuotientMapLocal, LinearMap.comp_apply,
            Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using happly.symm
        have hdiff_zero :
            (torsionQuotientMapLocal (A := A) (I := I) Y
                (show f.cutoff ≤ g.cutoff + f.cutoff + d_right by omega) n)
              ((a : stageRing A I n) • q0 - f n hnf x) = 0 := by
          rw [LinearMap.map_sub, hdeep_eq, sub_self]
        have hdiff_torsion_right :
            (a : stageRing A I n) • q0 - f n hnf x ∈
              Submodule.torsionBySet
                (stageRing A I n)
                (torsionQuotient f.cutoff Y n)
                (↑((stageIdeal A I n) ^ (g.cutoff + f.cutoff + d_right)) :
                  Set (stageRing A I n)) := by
          exact
            mem_torsionBySet_of_torsionQuotientMapLocal_eq_zero
              (A := A) (I := I)
              (show f.cutoff ≤ g.cutoff + f.cutoff + d_right by omega) n hdiff_zero
        have hdiff_torsion_D0 :
            (a : stageRing A I n) • q0 - f n hnf x ∈
              Submodule.torsionBySet
                (stageRing A I n)
                (torsionQuotient f.cutoff Y n)
                (↑((stageIdeal A I n) ^ D0) : Set (stageRing A I n)) := by
          exact
            (Submodule.torsionBySet_le_torsionBySet_pow
              (g.cutoff + f.cutoff + d_right) D0 hright_le_D0 (stageIdeal A I n))
              hdiff_torsion_right
        have hsmul_zero :
            (b : stageRing A I n) • ((a : stageRing A I n) • q0 - f n hnf x) = 0 := by
          exact (Submodule.mem_torsionBySet_iff _ _).mp hdiff_torsion_D0 b
        have hrange :
            (b : stageRing A I n) • ((a : stageRing A I n) • q0) ∈
              LinearMap.range (f n hnf) := by
          refine ⟨(b : stageRing A I n) • x, ?_⟩
          have hbf :
              (b : stageRing A I n) • ((a : stageRing A I n) • q0) =
                (b : stageRing A I n) • (f n hnf x) := by
            simpa [smul_sub] using hsmul_zero
          calc
            (b : stageRing A I n) • ((a : stageRing A I n) • q0)
                = (b : stageRing A I n) • (f n hnf x) := hbf
            _ = f n hnf ((b : stageRing A I n) • x) := by
                  simpa using (LinearMap.map_smul (f n hnf) (b : stageRing A I n) x).symm
        -- Vanishing in the quotient by the range is exactly the cokernel statement.
        change (Submodule.Quotient.mk
          ((b : stageRing A I n) • ((a : stageRing A I n) • q0)) :
            levelCokernel f ⟨n, hnf⟩) = 0
        exact (Submodule.Quotient.mk_eq_zero (p := LinearMap.range (f n hnf))).2 hrange
      -- Applying the generic square-exponent torsion lemma upgrades the previous `I^D0`-torsion
      -- estimate to the required `I^(2D0)` bound.
      simpa [D, two_mul] using
        mem_torsionBySet_two_mul_of_smul_mem_torsionBySet
          (J := stageIdeal A I n) D0 hq_torsion_D0
    exact ⟨hkernel_torsion, hcokernel_torsion⟩

/-- Helper for Lemma 15.101.7: an eventual uniform torsion bound on kernels and cokernels produces
an inverse representative up to the promotion relation. -/
private theorem exists_related_inverse_of_hasEventuallyBoundedKernelAndCokernel
    (f : HomRepresentative X Y)
    (hf : hasEventuallyBoundedKernelAndCokernel f) :
    ∃ g : HomRepresentative Y X,
      relation A I (f.comp g) (HomRepresentative.id X) ∧
      relation A I (g.comp f) (HomRepresentative.id Y) := by
  -- Route correction: the remaining converse is the textbook `ψ_n` construction. One chooses a
  -- common deep cutoff, defines `ψ_n : I^d E'_n → E_n / E_n[I^d]` by lifting through cokernel
  -- torsion, and proves well-definedness using kernel torsion.
  rcases hf with ⟨c', N, hN, htors⟩
  let d := max (max f.cutoff N) c'
  have hdf : f.cutoff ≤ d := by
    exact Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
  have hdN : N ≤ d := by
    exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  have hdc : c' ≤ d := Nat.le_max_right _ _
  -- TODO: define the stagewise maps `ψ_n : I^d E'_n → E_n / E_n[I^d]` using the cokernel torsion
  -- part of `htors`, prove well-definedness with the kernel torsion part at the same cutoff `d`,
  -- package them into a representative `g`, and compare both composites to the raised identities.
  sorry

/-- Helper for Lemma 15.101.7: an isomorphism class in the quotient category admits an inverse
representative whose two composites are already related to the identity representatives. -/
private theorem exists_related_inverse_of_isIso_quotientMap
    (f : HomRepresentative X Y) [IsIso ((Q).map f)] :
    ∃ g : HomRepresentative Y X,
      relation A I (f.comp g) (HomRepresentative.id X) ∧
      relation A I (g.comp f) (HomRepresentative.id Y) := by
  -- We first choose a raw representative for the inverse quotient morphism.
  obtain ⟨g, hg⟩ : ∃ g : HomRepresentative Y X, (Q).map g = inv ((Q).map f) := by
    refine Quot.inductionOn (inv ((Q).map f)) ?_
    intro g
    exact ⟨g, rfl⟩
  refine ⟨g, ?_, ?_⟩
  · -- Equality in the quotient category descends to the defining relation on representatives.
    apply Quotient.exact
    calc
      (Q).map (f.comp g) = (Q).map f ≫ (Q).map g := by
        simp
      _ = (Q).map f ≫ inv ((Q).map f) := by
        rw [hg]
      _ = 𝟙 _ := by
        simp
      _ = (Q).map (HomRepresentative.id X) := by
        simp
  · -- The same descent argument handles the opposite composite.
    apply Quotient.exact
    calc
      (Q).map (g.comp f) = (Q).map g ≫ (Q).map f := by
        simp
      _ = inv ((Q).map f) ≫ (Q).map f := by
        rw [hg]
      _ = 𝟙 _ := by
        simp
      _ = (Q).map (HomRepresentative.id Y) := by
        simp

/-- Helper for Lemma 15.101.7: at the representative level, invertibility in the quotient category
is equivalent to a uniform eventual torsion bound on kernels and cokernels. -/
private theorem quotientMap_isIso_iff_hasEventuallyBoundedKernelAndCokernel
    (f : HomRepresentative X Y) :
    IsIso ((Q).map f) ↔ hasEventuallyBoundedKernelAndCokernel f := by
  constructor
  · intro hf
    -- We first descend the quotient inverse to a representative-level inverse relation.
    obtain ⟨g, hfg, hgf⟩ :=
      exists_related_inverse_of_isIso_quotientMap (A := A) (I := I) (X := X) (Y := Y) f
    -- The remaining source-faithful step is the torsion analysis on those two related composites.
    exact
      hasEventuallyBoundedKernelAndCokernel_of_related_inverse
        (A := A) (I := I) (X := X) (Y := Y) f hfg hgf
  · intro hf
    -- Once a related inverse representative exists, the quotient morphism is strictly invertible.
    obtain ⟨g, hfg, hgf⟩ :=
      exists_related_inverse_of_hasEventuallyBoundedKernelAndCokernel
        (A := A) (I := I) (X := X) (Y := Y) f hf
    refine ⟨⟨(Q).map g, ?_, ?_⟩⟩
    · calc
        (Q).map f ≫ (Q).map g = (Q).map (f.comp g) := by
          simp
        _ = (Q).map (HomRepresentative.id X) := by
          exact Quotient.sound hfg
        _ = 𝟙 _ := by
          simp
    · calc
        (Q).map g ≫ (Q).map f = (Q).map (g.comp f) := by
          simp
        _ = (Q).map (HomRepresentative.id Y) := by
          exact Quotient.sound hgf
        _ = 𝟙 _ := by
          simp

-- Proof sketch: if `f` is an isomorphism in the quotient category of Remark `15.101.6`, choose
-- an inverse representative and compose the two representatives. The identity representative has
-- zero kernel and cokernel, so the bounded-kernel/cokernel condition follows from compatibility
-- with promotion and composition. Conversely, the bounded kernel/cokernel condition yields a
-- representative that is invertible in the quotient category after increasing the cutoff, which
-- gives `IsIso f`.
/-- Lemma 15.101.7: a morphism in the category `\mathcal C` of Remark `15.101.6` is an
isomorphism if and only if it has eventually bounded kernel and cokernel. -/
@[stacks 0EGX]
theorem isIso_iff_hasEventuallyBoundedKernelAndCokernel
    (f : (Q).obj X ⟶ (Q).obj Y) :
    IsIso f ↔ HasEventuallyBoundedKernelAndCokernel f := by
  -- Route correction: after rewriting the public predicate as an existential representative
  -- wrapper, the quotient-level statement reduces immediately to the representative criterion.
  refine Quot.inductionOn f ?_
  intro f₀
  constructor
  · intro hf₀
    -- The chosen representative itself witnesses the existential morphism-level predicate.
    exact ⟨f₀, rfl, (quotientMap_isIso_iff_hasEventuallyBoundedKernelAndCokernel
      (A := A) (I := I) (X := X) (Y := Y) f₀).1 hf₀⟩
  · rintro ⟨g, hg, hgBounded⟩
    -- Any bounded representative of the same quotient morphism gives the desired isomorphism.
    have hgIso : IsIso ((Q).map g) :=
      (quotientMap_isIso_iff_hasEventuallyBoundedKernelAndCokernel
        (A := A) (I := I) (X := X) (Y := Y) g).2 hgBounded
    cases hg
    exact hgIso

end IadicFiniteModuleSystem

end
