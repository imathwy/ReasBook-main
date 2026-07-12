import Mathlib.RingTheory.DividedPowers.DPMorphism

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-
Source/core/bridge triage:
- `source-facing`: Lemma 23.2.5 on agreement of divided powers on `I * J` and gluing divided power
  structures from `I` and `J` to `I ⊔ J`.
- `core/canonical`: the mathlib owners `DividedPowers.coincide_on_smul` and
  `DividedPowers.IsDPMorphism`.
- `bridge/view`: part (1) transports the canonical `I • J` statement to the source-facing product
  ideal `I * J`; part (2) keeps the source-facing gluing statement while expressing restriction to
  `I` and `J` via the canonical identity-map divided-power morphism condition.
-/

namespace DividedPowers

section

variable {A : Type u} [CommRing A] {I J : Ideal A}

/-- Source-facing overlap condition for Lemma 23.2.5: the divided power structures `γ` on `I`
and `δ` on `J` agree on the intersection ideal `I ⊓ J`. -/
abbrev agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J) : Prop :=
  ∀ n : ℕ, ∀ ⦃x : A⦄, x ∈ I ⊓ J → γ.dpow n x = δ.dpow n x

/-- Source-facing compatibility condition for Lemma 23.2.5: a divided power structure `ε` on
`I ⊔ J` restricts to `γ` on `I` and to `δ` on `J` via the identity map. -/
abbrev compatibleOnSup (γ : DividedPowers I) (δ : DividedPowers J)
    (ε : DividedPowers (I ⊔ J)) : Prop :=
  IsDPMorphism γ ε (RingHom.id A) ∧ IsDPMorphism δ ε (RingHom.id A)

/-- Companion projection for Lemma 23.2.5: compatibility on `I ⊔ J` includes the identity-map
restriction from `γ` on `I`. -/
theorem compatibleOnSup_left (γ : DividedPowers I) (δ : DividedPowers J)
    {ε : DividedPowers (I ⊔ J)} (hε : compatibleOnSup γ δ ε) :
    IsDPMorphism γ ε (RingHom.id A) :=
  hε.1

/-- Companion projection for Lemma 23.2.5: compatibility on `I ⊔ J` includes the identity-map
restriction from `δ` on `J`. -/
theorem compatibleOnSup_right (γ : DividedPowers I) (δ : DividedPowers J)
    {ε : DividedPowers (I ⊔ J)} (hε : compatibleOnSup γ δ ε) :
    IsDPMorphism δ ε (RingHom.id A) :=
  hε.2

/- Lemma 23.2.5 (1): if `γ` is a divided power structure on `I` and `δ` is a divided power
structure on `J`, then they agree on the product ideal `I * J`. -/
@[stacks 07GQ]
theorem coincide_on_mul (γ : DividedPowers I) (δ : DividedPowers J) {n : ℕ} {x : A}
    (hx : x ∈ I * J) :
    γ.dpow n x = δ.dpow n x := by
  have hx' : x ∈ I • J := by
    simpa [Ideal.smul_eq_mul] using hx
  simpa using γ.coincide_on_smul δ hx'

/-- Companion to Lemma 23.2.5: any divided power structure on `I ⊔ J` compatible with `γ` on
`I` and with `δ` on `J` forces `γ` and `δ` to agree on `I ⊓ J`. -/
theorem agreeOnInf_of_compatibleOnSup (γ : DividedPowers I) (δ : DividedPowers J)
    {ε : DividedPowers (I ⊔ J)} (hε : compatibleOnSup γ δ ε) :
    agreeOnInf γ δ := by
  intro n x hx
  have hγ : ε.dpow n x = γ.dpow n x := by
    simpa using (compatibleOnSup_left γ δ hε).dpow_comp x hx.1
  have hδ : ε.dpow n x = δ.dpow n x := by
    simpa using (compatibleOnSup_right γ δ hε).dpow_comp x hx.2
  exact hγ.symm.trans hδ

/- Lemma 23.2.5 (2): if `γ` is a divided power structure on `I` and `δ` is a divided power
structure on `J` that agree on `I ⊓ J`, then there is a unique divided power structure on `I ⊔ J`
restricting to `γ` on `I` and to `δ` on `J`; equivalently, the identity map is a divided power
morphism from `(I, γ)` and from `(J, δ)` into `(I ⊔ J, ε)`. -/
@[stacks 07GQ]
theorem existsUnique_sup_of_agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) : ∃! ε : DividedPowers (I ⊔ J), compatibleOnSup γ δ ε := sorry

/-- Companion to Lemma 23.2.5: for fixed restrictions `γ` on `I` and `δ` on `J`, any two divided
power structures on `I ⊔ J` compatible with both are equal. -/
theorem eq_of_compatibleOnSup (γ : DividedPowers I) (δ : DividedPowers J)
    {ε ε' : DividedPowers (I ⊔ J)}
    (hε : compatibleOnSup γ δ ε) (hε' : compatibleOnSup γ δ ε') :
    ε = ε' :=
  (existsUnique_sup_of_agreeOnInf γ δ (agreeOnInf_of_compatibleOnSup γ δ hε)).unique hε hε'

/-- Companion to Lemma 23.2.5: if `γ` on `I` and `δ` on `J` agree on `I ⊓ J`, then there exists a
divided power structure on `I ⊔ J` whose identity-map restrictions recover `γ` and `δ`. -/
theorem exists_sup_of_agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J)
    (hagree : agreeOnInf γ δ) : ∃ ε : DividedPowers (I ⊔ J), compatibleOnSup γ δ ε :=
  (existsUnique_sup_of_agreeOnInf γ δ hagree).exists

/-- Companion to Lemma 23.2.5: divided powers on `I` and `J` glue uniquely to `I ⊔ J` exactly
when they agree on the overlap `I ⊓ J`. -/
theorem existsUnique_sup_iff_agreeOnInf (γ : DividedPowers I) (δ : DividedPowers J) :
    (∃! ε : DividedPowers (I ⊔ J), compatibleOnSup γ δ ε) ↔ agreeOnInf γ δ := by
  constructor
  · rintro ⟨ε, hε, -⟩
    exact agreeOnInf_of_compatibleOnSup γ δ hε
  · exact existsUnique_sup_of_agreeOnInf γ δ

end

end DividedPowers
