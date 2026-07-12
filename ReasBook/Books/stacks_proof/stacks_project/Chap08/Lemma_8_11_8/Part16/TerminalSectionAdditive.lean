import Mathlib

universe w

namespace CategoryTheory

/-- Helper for Lemma 8.11.8: once a restriction map on terminal sections is known to preserve
addition, package it as the corresponding morphism in `AddCommGrpCat`. This keeps the final
reconstruction record free of inline proof terms. -/
noncomputable def terminal_section_add_hom_of_map_add
    {A B : AddCommGrpCat.{w}} (f : A → B)
    (hf : ∀ a b, f (a + b) = f a + f b) :
    A ⟶ B :=
  AddCommGrpCat.ofHom <| AddMonoidHom.mk' f hf

/-- Helper for Lemma 8.11.8 Part16: if a map of terminal-section types is identified, through
transported additive equivalences, with an `AddCommGrpCat` morphism, then it preserves addition
for the transported group structures. -/
theorem terminal_section_map_add_of_equiv_square
    {A B : AddCommGrpCat.{w}} {α β : Type w}
    (eα : α ≃ A) (eβ : β ≃ B)
    (f : α → β) (g : A ⟶ B)
    (hfg : ∀ a, eβ (f a) = g.hom (eα a)) :
    letI : AddCommGroup α := Equiv.addCommGroup eα
    letI : AddCommGroup β := Equiv.addCommGroup eβ
    ∀ a b : α, f (a + b) = f a + f b := by
  letI : AddCommGroup α := Equiv.addCommGroup eα
  letI : AddCommGroup β := Equiv.addCommGroup eβ
  have hα : ∀ a b : α, eα (a + b) = eα a + eα b := by
    intro a b
    change eα (eα.symm (eα a + eα b)) = eα a + eα b
    exact eα.apply_symm_apply (eα a + eα b)
  have hβ : ∀ a b : β, eβ (a + b) = eβ a + eβ b := by
    intro a b
    change eβ (eβ.symm (eβ a + eβ b)) = eβ a + eβ b
    exact eβ.apply_symm_apply (eβ a + eβ b)
  intro a b
  apply eβ.injective
  calc
    eβ (f (a + b)) = g.hom (eα (a + b)) := hfg (a + b)
    _ = g.hom (eα a + eα b) := by rw [hα a b]
    _ = g.hom (eα a) + g.hom (eα b) := by
      exact map_add g.hom (eα a) (eα b)
    _ = eβ (f a) + eβ (f b) := by rw [← hfg a, ← hfg b]
    _ = eβ (f a + f b) := by rw [hβ (f a) (f b)]

/-- Helper for Lemma 8.11.8 Part16: the morphism packaged from an additive terminal-section map
evaluates to the original underlying function. -/
theorem terminal_section_add_hom_of_map_add_apply
    {A B : AddCommGrpCat.{w}} (f : A → B)
    (hf : ∀ a b, f (a + b) = f a + f b) (a : A) :
    terminal_section_add_hom_of_map_add (A := A) (B := B) f hf a = f a := by
  -- Unpack the bundled additive homomorphism; no transport is involved in this wrapper.
  rfl

/-- Helper for Lemma 8.11.8 Part16: the morphism packaged from an additive terminal-section map
preserves zero. -/
theorem terminal_section_add_hom_of_map_add_zero
    {A B : AddCommGrpCat.{w}} (f : A → B)
    (hf : ∀ a b, f (a + b) = f a + f b) :
    terminal_section_add_hom_of_map_add (A := A) (B := B) f hf 0 = 0 := by
  -- Once the function is packaged as an `AddCommGrpCat` morphism, zero preservation is canonical.
  exact map_zero (terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom

/-- Helper for Lemma 8.11.8 Part16: the morphism packaged from an additive terminal-section map
preserves negation. -/
theorem terminal_section_add_hom_of_map_add_neg
    {A B : AddCommGrpCat.{w}} (f : A → B)
    (hf : ∀ a b, f (a + b) = f a + f b) (a : A) :
    (terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom (-a) =
      -(terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom a := by
  -- Use the bundled additive homomorphism field, where preservation of negation is standard.
  exact map_neg (terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom a

/-- Helper for Lemma 8.11.8 Part16: the morphism packaged from an additive terminal-section map
preserves subtraction. -/
theorem terminal_section_add_hom_of_map_add_sub
    {A B : AddCommGrpCat.{w}} (f : A → B)
    (hf : ∀ a b, f (a + b) = f a + f b) (a b : A) :
    (terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom (a - b) =
      (terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom a -
        (terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom b := by
  -- Use the bundled additive homomorphism field, keeping subtraction normalization out of the
  -- later reconstructed restriction-map proof.
  exact map_sub (terminal_section_add_hom_of_map_add (A := A) (B := B) f hf).hom a b

/-- Helper for Lemma 8.11.8 Part16: two terminal-section morphisms packaged from additive maps
are equal as soon as their underlying functions agree. -/
theorem terminal_section_add_hom_of_map_add_ext
    {A B : AddCommGrpCat.{w}} {f g : A → B}
    (hf : ∀ a b, f (a + b) = f a + f b)
    (hg : ∀ a b, g (a + b) = g a + g b)
    (hfg : ∀ a, f a = g a) :
    terminal_section_add_hom_of_map_add (A := A) (B := B) f hf =
      terminal_section_add_hom_of_map_add (A := A) (B := B) g hg := by
  -- Reduce equality of bundled additive maps to the pointwise equality already descended on
  -- terminal sections.
  ext a
  exact hfg a

/-- Helper for Lemma 8.11.8 Part16: the terminal-section morphism packaged from an additive
map is independent of the particular proof of additivity. -/
theorem terminal_section_add_hom_of_map_add_proof_irrel
    {A B : AddCommGrpCat.{w}} (f : A → B)
    (hf hg : ∀ a b, f (a + b) = f a + f b) :
    terminal_section_add_hom_of_map_add (A := A) (B := B) f hf =
      terminal_section_add_hom_of_map_add (A := A) (B := B) f hg := by
  -- Use the already proved pointwise extensionality lemma; only the proof fields differ.
  exact terminal_section_add_hom_of_map_add_ext hf hg (fun a ↦ rfl)

/-- Helper for Lemma 8.11.8 Part16: the identity function on terminal sections preserves
addition. -/
theorem terminal_section_id_map_add (A : AddCommGrpCat.{w}) :
    ∀ a b : A, (fun x : A ↦ x) (a + b) = (fun x : A ↦ x) a + (fun x : A ↦ x) b := by
  -- The identity map leaves both sides syntactically identical.
  intro a b
  rfl

/-- Helper for Lemma 8.11.8 Part16: packaging the identity terminal-section map gives the
identity morphism in `AddCommGrpCat`. -/
theorem terminal_section_add_hom_of_map_add_id
    (A : AddCommGrpCat.{w}) :
    terminal_section_add_hom_of_map_add (A := A) (B := A) (fun a : A ↦ a)
      (terminal_section_id_map_add A) = 𝟙 A := by
  -- Extensionality reduces the bundled identity law to evaluation on one section.
  ext a
  rfl

/-- Helper for Lemma 8.11.8 Part16: composing two additive terminal-section maps is additive. -/
theorem map_add_comp_of_map_add
    {A B D : AddCommGrpCat.{w}} (f : A → B) (g : B → D)
    (hf : ∀ a b, f (a + b) = f a + f b)
    (hg : ∀ a b, g (a + b) = g a + g b) :
    ∀ a b, g (f (a + b)) = g (f a) + g (f b) := by
  -- Push additivity through `f` and then through `g`.
  intro a b
  rw [hf, hg]

/-- Helper for Lemma 8.11.8 Part16: packaging a composite additive terminal-section map agrees
with composing the separately packaged morphisms. -/
theorem terminal_section_add_hom_of_map_add_comp
    {A B D : AddCommGrpCat.{w}} (f : A → B) (g : B → D)
    (hf : ∀ a b, f (a + b) = f a + f b)
    (hg : ∀ a b, g (a + b) = g a + g b) :
    terminal_section_add_hom_of_map_add (A := A) (B := B) f hf ≫
      terminal_section_add_hom_of_map_add (A := B) (B := D) g hg =
        terminal_section_add_hom_of_map_add (A := A) (B := D) (fun a ↦ g (f a))
          (map_add_comp_of_map_add f g hf hg) := by
  -- Extensionality reduces the categorical composite to equality of underlying functions.
  ext a
  rfl

/-- Helper for Lemma 8.11.8 Part16: the packaged additive maps form a left inverse when their
underlying functions do. This supplies the `hom_inv_id` proof field for comparison isomorphisms
constructed from terminal-section equivalences. -/
theorem terminal_section_add_hom_of_map_add_hom_inv_id
    {A B : AddCommGrpCat.{w}} (f : A → B) (g : B → A)
    (hf : ∀ a b, f (a + b) = f a + f b)
    (hg : ∀ a b, g (a + b) = g a + g b)
    (hgf : ∀ a, g (f a) = a) :
    terminal_section_add_hom_of_map_add (A := A) (B := B) f hf ≫
      terminal_section_add_hom_of_map_add (A := B) (B := A) g hg = 𝟙 A := by
  -- Reduce the inverse law for bundled additive maps to the underlying terminal-section inverse.
  ext a
  exact hgf a

/-- Helper for Lemma 8.11.8 Part16: the packaged additive maps form a right inverse when their
underlying functions do. This supplies the `inv_hom_id` proof field for comparison isomorphisms
constructed from terminal-section equivalences. -/
theorem terminal_section_add_hom_of_map_add_inv_hom_id
    {A B : AddCommGrpCat.{w}} (f : A → B) (g : B → A)
    (hf : ∀ a b, f (a + b) = f a + f b)
    (hg : ∀ a b, g (a + b) = g a + g b)
    (hfg : ∀ b, f (g b) = b) :
    terminal_section_add_hom_of_map_add (A := B) (B := A) g hg ≫
      terminal_section_add_hom_of_map_add (A := A) (B := B) f hf = 𝟙 B := by
  -- As above, extensionality pushes the categorical identity to the underlying inverse law.
  ext b
  exact hfg b

/-- Helper for Lemma 8.11.8 Part16: the inverse of a two-sided inverse additive map is
additive. -/
theorem inverse_map_add_of_map_add
    {A B : AddCommGrpCat.{w}} (f : A → B) (g : B → A)
    (hf : ∀ a b, f (a + b) = f a + f b)
    (hgf : ∀ a, g (f a) = a)
    (hfg : ∀ b, f (g b) = b) :
    ∀ a b, g (a + b) = g a + g b := by
  intro a b
  -- Apply the forward additive map to the desired inverse-additivity equation.
  have happly : f (g (a + b)) = f (g a + g b) := by
    rw [hfg, hf, hfg, hfg]
  -- The two inverse laws make `f` injective in the exact form needed here.
  calc
    g (a + b) = g (f (g (a + b))) := (hgf (g (a + b))).symm
    _ = g (f (g a + g b)) := by rw [happly]
    _ = g a + g b := hgf (g a + g b)

/-- Helper for Lemma 8.11.8 Part16: the inverse equivalence of an additive equivalence of
terminal section groups is additive. -/
theorem equiv_symm_map_add_of_map_add
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) :
    ∀ a b, e.symm (a + b) = e.symm a + e.symm b := by
  -- Specialize the two-sided inverse lemma to the underlying equivalence.
  exact inverse_map_add_of_map_add (A := A) (B := B) e e.symm he
    (fun a ↦ e.symm_apply_apply a) (fun b ↦ e.apply_symm_apply b)

/-- Helper for Lemma 8.11.8 Part16: the packaged additive map of an equivalence has the
expected left inverse. -/
theorem terminal_section_add_hom_of_equiv_hom_inv_id
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) :
    terminal_section_add_hom_of_map_add (A := A) (B := B) e he ≫
      terminal_section_add_hom_of_map_add (A := B) (B := A) e.symm
        (equiv_symm_map_add_of_map_add e he) = 𝟙 A := by
  -- Reuse the generic packaged inverse law with the equivalence inverse.
  exact terminal_section_add_hom_of_map_add_hom_inv_id e e.symm he
    (equiv_symm_map_add_of_map_add e he) (fun a ↦ e.symm_apply_apply a)

/-- Helper for Lemma 8.11.8 Part16: the packaged additive map of an equivalence has the
expected right inverse. -/
theorem terminal_section_add_hom_of_equiv_inv_hom_id
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) :
    terminal_section_add_hom_of_map_add (A := B) (B := A) e.symm
        (equiv_symm_map_add_of_map_add e he) ≫
      terminal_section_add_hom_of_map_add (A := A) (B := B) e he = 𝟙 B := by
  -- Reuse the generic packaged inverse law in the other direction.
  exact terminal_section_add_hom_of_map_add_inv_hom_id e e.symm he
    (equiv_symm_map_add_of_map_add e he) (fun b ↦ e.apply_symm_apply b)

/-- Helper for Lemma 8.11.8 Part16: an additive equivalence of terminal section groups packages
as an isomorphism in `AddCommGrpCat`. -/
noncomputable def terminal_section_add_iso_of_equiv_map_add
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) :
    A ≅ B where
  hom := terminal_section_add_hom_of_map_add e he
  inv := terminal_section_add_hom_of_map_add e.symm (equiv_symm_map_add_of_map_add e he)
  hom_inv_id := terminal_section_add_hom_of_equiv_hom_inv_id e he
  inv_hom_id := terminal_section_add_hom_of_equiv_inv_hom_id e he

/-- Helper for Lemma 8.11.8 Part16: the forward morphism of an additive isomorphism packaged
from an equivalence is the separately packaged additive homomorphism. -/
theorem terminal_section_add_iso_of_equiv_map_add_hom
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) :
    (terminal_section_add_iso_of_equiv_map_add (A := A) (B := B) e he).hom =
      terminal_section_add_hom_of_map_add (A := A) (B := B) e he := by
  -- The isomorphism stores the forward morphism in this normalized packaged form.
  rfl

/-- Helper for Lemma 8.11.8 Part16: the forward map of an additive isomorphism packaged from an
equivalence is the original equivalence on terminal sections. -/
theorem terminal_section_add_iso_of_equiv_map_add_hom_apply
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) (a : A) :
    (terminal_section_add_iso_of_equiv_map_add (A := A) (B := B) e he).hom a = e a := by
  -- Unfold only the already packaged hom wrapper, keeping later comparison proofs pointwise.
  rfl

/-- Helper for Lemma 8.11.8 Part16: the inverse map of an additive isomorphism packaged from an
equivalence is the inverse equivalence on terminal sections. -/
theorem terminal_section_add_iso_of_equiv_map_add_inv_apply
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) (b : B) :
    (terminal_section_add_iso_of_equiv_map_add (A := A) (B := B) e he).inv b = e.symm b := by
  -- The inverse side is the same wrapper applied to the inverse equivalence.
  rfl

/-- Helper for Lemma 8.11.8 Part16: the inverse morphism of an additive isomorphism packaged
from an equivalence is the packaged inverse additive map. -/
theorem terminal_section_add_iso_of_equiv_map_add_inv
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he : ∀ a b, e (a + b) = e a + e b) :
    (terminal_section_add_iso_of_equiv_map_add (A := A) (B := B) e he).inv =
      terminal_section_add_hom_of_map_add (A := B) (B := A) e.symm
        (equiv_symm_map_add_of_map_add e he) := by
  -- The packaged isomorphism stores the inverse morphism in exactly this normalized form.
  rfl

/-- Helper for Chap08 Lemma 8 11 8/Part16: the additive isomorphism packaged from an
equivalence does not depend on the particular proof that the equivalence preserves addition. -/
theorem terminal_section_add_iso_of_equiv_map_add_proof_irrel
    {A B : AddCommGrpCat.{w}} (e : A ≃ B)
    (he he' : ∀ a b, e (a + b) = e a + e b) :
    terminal_section_add_iso_of_equiv_map_add (A := A) (B := B) e he =
      terminal_section_add_iso_of_equiv_map_add (A := A) (B := B) e he' := by
  -- Extensionality reduces the isomorphism equality to the common underlying equivalence.
  ext a
  rfl

end CategoryTheory
