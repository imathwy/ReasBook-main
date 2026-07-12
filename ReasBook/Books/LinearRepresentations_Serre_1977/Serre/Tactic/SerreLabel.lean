import Mathlib.Tactic.Recall

/-!
# Serre label attribution

This file provides repo-local attribution tools for linking declarations, recall entries, and
checked terms to labels from Serre's text.

Use:
* `@[serre "Exercise 15-15.2-6"]` on declarations.
* `serre_recall "Theorem 19-19.1-1" someDeclaration` for recall-only entries.
* `serre_check "Definition 1-1.2-1" (Some Lean expression)` for check-only entries.
* `#serre_labels`, `#serre_labels!`, `#serre_label "..."`, and `#serre_label! "..."` to inspect
  recorded attributions.
-/

open Lean Elab Command Term Meta

namespace Serre.Label

/-- The kind of Lean surface carrying a Serre attribution. -/
inductive AnchorKind where
  | decl
  | recall
  | check
  deriving BEq, Hashable, Repr

instance : ToString AnchorKind where
  toString
    | .decl => "decl"
    | .recall => "recall"
    | .check => "check"

/-- A Serre label attribution stored in the environment. -/
structure Entry where
  /-- The full source label, e.g. `"Exercise 15-15.2-6"`. -/
  label : String
  /-- The surface form that carries this label. -/
  kind : AnchorKind
  /-- The declaration name, when the attribution targets a declaration. -/
  declName : Option Name
  /-- A printable target: declaration name for declarations/recalls,
  pretty expression for checks. -/
  target : String
  /-- Optional human comment supplied at the attribution site. -/
  comment : String
  deriving BEq, Hashable

/-- Environment extension storing all Serre label attributions. -/
initialize entryExt : SimplePersistentEnvExtension Entry (Array (Array Entry)) ←
  registerSimplePersistentEnvExtension {
    addImportedFn entries := entries
    addEntryFn entries _ := entries
  }

/-- Add a Serre label attribution to the environment. -/
def addEntry {m : Type → Type} [MonadEnv m]
    (label : String) (kind : AnchorKind) (declName : Option Name) (target comment : String) :
    m Unit :=
  modifyEnv (entryExt.addEntry ·
    { label, kind, declName, target, comment })

/-- All Serre label entries in an environment, sorted deterministically. -/
def entries (env : Environment) : Array Entry :=
  let entries := PersistentEnvExtension.getState entryExt env
  entries.2.flatten.appendList entries.1 |>.qsort fun a b =>
    if a.label == b.label then
      if toString a.kind == toString b.kind then
        a.target < b.target
      else
        toString a.kind < toString b.kind
    else
      a.label < b.label

/-- Serre label entries with a fixed label. -/
def entriesForLabel (env : Environment) (label : String) : Array Entry :=
  entries env |>.filter fun entry => entry.label == label

/-- Attribute syntax for tagging declarations with a Serre source label. -/
syntax (name := serreAttr) "serre" str (ppSpace str)? : attr

initialize registerBuiltinAttribute {
  name := `serreAttr
  descr := "Apply a Serre source label to a declaration."
  add := fun decl stx _attrKind => do
    let (label, comment) ← match stx with
      | `(attr| serre $label:str $[$comment:str]?) =>
          pure (label.getString, (comment.map (·.getString)).getD "")
      | _ => throwUnsupportedSyntax
    let oldDoc := (← findDocString? (← getEnv) decl).getD ""
    let commentInDoc := if comment.isEmpty then "" else s!" ({comment})"
    let newDoc := [oldDoc, s!"[Serre Label {label}]{commentInDoc}"]
    addDocStringCore decl <| "\n\n".intercalate (newDoc.filter (· != ""))
    addEntry label .decl (some decl) decl.toString comment
  applicationTime := .beforeElaboration
}

/-- `serre_recall "Label" decl` records a Serre label attribution and then runs
`recall decl`. -/
syntax (name := serreRecall)
  (docComment)? "serre_recall " str ident ppIndent(optDeclSig) (declVal)? : command

elab_rules : command
  | `($[$doc?:docComment]? serre_recall $label:str $id $sig:optDeclSig $[$val?]?) => do
      let labelStr := label.getString
      let declName ← resolveGlobalConstNoOverload id
      addConstInfo id declName
      elabCommand <| ← `($[$doc?:docComment]? recall $id $sig:optDeclSig $[$val?]?)
      addEntry labelStr .recall (some declName) declName.toString ""

/-- `serre_check "Label" term` records a check-only Serre label attribution and logs the type. -/
syntax (name := serreCheck) "serre_check " str term : command

elab_rules : command
  | `(serre_check $label:str $term:term) => do
      let labelStr := label.getString
      let (target, typeStr) ← liftTermElabM do
        let expr ← Term.elabTermAndSynthesize term none
        let type ← inferType expr
        let target ← ppExpr expr
        let type ← ppExpr type
        pure (toString target, toString type)
      addEntry labelStr .check none target ""
      logInfo m!"{target} : {typeStr}"

private def entryMessage (entry : Entry) : MessageData :=
  let comment :=
    if entry.comment.isEmpty then
      ""
    else
      s!" ({entry.comment})"
  m!"[{entry.label}] {entry.kind}: {entry.target}{comment}"

/-- Trace Serre label entries, optionally including declaration types. -/
def traceEntries (entries : Array Entry) (verbose : Bool := false) : CommandElabM Unit := do
  if entries.isEmpty then
    logInfo "No Serre labels found."
  else
    let env ← getEnv
    let mut msgs := #[m!""]
    for entry in entries do
      msgs := msgs.push (entryMessage entry)
      if verbose then
        if let some declName := entry.declName then
          if let some info := env.find? declName then
            msgs := (msgs.push info.type).push ""
    logInfo <| MessageData.joinSep msgs.toList "\n"

/-- `#serre_labels` lists all Serre label attributions.
Use `#serre_labels!` for types too. -/
elab (name := serreLabels) "#serre_labels" tk:("!")? : command => do
  traceEntries (entries (← getEnv)) tk.isSome

/-- `#serre_label "Label"` lists all attributions for one Serre label.
Use `#serre_label! "Label"` for types too. -/
elab (name := serreLabel) "#serre_label" tk:("!")? label:str : command => do
  traceEntries (entriesForLabel (← getEnv) label.getString) tk.isSome

end Serre.Label
