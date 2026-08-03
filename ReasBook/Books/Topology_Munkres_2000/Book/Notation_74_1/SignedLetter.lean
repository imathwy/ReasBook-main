module

public import Topology_Munkres_2000.Book.Definition_74_4.Scheme

public section

namespace SignedLetter

/-- A label occurring with exponent `+1` in a polygon word. -/
@[expose]
def positive {α : Type*} (label : α) : α × Bool :=
  (label, true)

/-- In signed-letter contexts, a bare label denotes that label with exponent `+1`. -/
scoped instance coeProdBool {α : Type*} : Coe α (α × Bool) where
  coe := positive

/-- A label occurring with exponent `-1` in a polygon word. -/
@[expose]
def inverse {α : Type*} (label : α) : α × Bool :=
  (label, false)

scoped postfix:max "⁻¹" => SignedLetter.inverse

@[simp]
theorem positive_fst {α : Type*} (label : α) : (positive label).1 = label :=
  rfl

@[simp]
theorem positive_snd {α : Type*} (label : α) : (positive label).2 = true :=
  rfl

@[simp]
theorem inverse_fst {α : Type*} (label : α) : (label⁻¹).1 = label :=
  rfl

@[simp]
theorem inverse_snd {α : Type*} (label : α) : (label⁻¹).2 = false :=
  rfl


end SignedLetter
