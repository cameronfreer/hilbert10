/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Lean
import Hilbert10

/-!
# API leakage audit

Checks that the *statements* of public results do not mention route-internal machinery.
Run via `lake env lean scripts/ApiLeakageAudit.lean`; any leak is a hard error.

The axiom audit answers "is this proved from standard axioms". This one answers a different
question: "can a user read this statement without reading the route". A public theorem whose
type mentions `ExpTerm`, a selector lane or a packed configuration has leaked its proof strategy
into its interface, and that is a design defect even when the proof is correct.

## What counts as internal

Ownership is decided by the **owning module**, not by the namespace prefix. Internal declarations
deliberately live in ordinary namespaces — `Hilbert10.ExpTerm`, `Hilbert10.RegisterMachine` —
so a name filter would miss exactly the cases this gate exists to catch. A constant is internal
when its module is `Hilbert10.Internal.*` or `Hilbert10Experimental.*`.

## What is checked

Every non-private declaration owned by a public module, which subsumes the frozen headline list
of `AxiomAudit.lean` — those all live in public modules. The rename tripwire stays there; this
gate deliberately keeps no second copy of the list to drift out of date.

## Generated companions are bodies

Equation lemmas (`f.eq_def`, `f.eq_1`, …) and the other declarations the equation compiler emits
restate a definition's *body*, so they are skipped for the same reason bodies are. A definition
whose body uses internal machinery is the intended design; its unfolding cannot leak anything the
definition does not already contain.

## Types only, with reducible aliases unfolded

Only the *type* of a declaration is inspected. Bodies are not: a public abstraction implemented
by internal machinery is the intended design, not a leak — that is what "internal" means.

Reducible definitions (including `abbrev`) owned by public modules *are* unfolded, one level at a
time, because a public alias for an internal type would otherwise conceal the leak behind a name.
Non-reducible public definitions are opaque here, for the same reason bodies are.
-/

open Lean Meta

/-- Modules whose declarations are implementation, not interface. -/
def isInternalModule (m : Name) : Bool :=
  (`Hilbert10.Internal).isPrefixOf m || (`Hilbert10Experimental).isPrefixOf m

/-- Modules that carry the supported API. -/
def isPublicModule (m : Name) : Bool :=
  (`Hilbert10).isPrefixOf m && !isInternalModule m

/-- The module a constant is declared in, if it comes from an import. -/
def ownerModule? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.allImportedModuleNames[idx.toNat]?

/-- Constants occurring in `e`, with reducible public definitions unfolded so that an alias
cannot hide an internal constant behind a public name. -/
partial def leakedConstants (e : Expr) : MetaM NameSet := do
  let env ← getEnv
  let mut todo := (e.getUsedConstants).toList
  let mut seen : NameSet := {}
  let mut found : NameSet := {}
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    match ownerModule? env n with
    | some m =>
      if isInternalModule m then
        found := found.insert n
      else if isPublicModule m && (← isReducible n) then
        if let some info := env.find? n then
          if let some v := info.value? then
            todo := v.getUsedConstants.toList ++ todo
    | none => pure ()
  return found

/-- Names the equation compiler generates from a definition. Their statements are unfoldings of
a body, which this gate does not inspect. -/
def isGeneratedCompanion (n : Name) : Bool :=
  match n with
  | .str _ s =>
    let suffixDigits (pre : String) : Bool :=
      s.startsWith pre && !(s.drop pre.length).isEmpty && (s.drop pre.length).all Char.isDigit
    s == "eq_def" || s == "induct" || s == "fun_cases" ||
      suffixDigits "eq_" || suffixDigits "match_" || suffixDigits "proof_" 
  | _ => false

/-- Declarations whose statements are exempt, with the reason. Every entry is a decision that a
transformation named in a public statement is part of that statement's mathematical content. -/
def statementExemptions : List Name := []

def checkType (label : String) (n : Name) (type : Expr) : MetaM (Option String) := do
  if statementExemptions.contains n then return none
  let leaks ← leakedConstants type
  if leaks.isEmpty then return none
  let names := leaks.toList.map toString
  return some s!"{label}: {n} mentions internal {String.intercalate ", " names}"

#eval show MetaM Unit from do
  let env ← getEnv
  let mut failures : Array String := #[]
  let mut swept := 0
  for (n, info) in env.constants.toList do
    if isPrivateName n || n.isInternalDetail || isGeneratedCompanion n then continue
    match ownerModule? env n with
    | some m =>
      if isPublicModule m then
        swept := swept + 1
        if let some msg ← checkType "public" n info.type then
          failures := failures.push msg
    | none => pure ()
  if failures.isEmpty then
    IO.println s!"api leakage audit: {swept} public declaration(s) clean"
  else
    for f in failures.qsort (· < ·) do
      IO.println f
    throwError "api leakage audit: {failures.size} leak(s)"
