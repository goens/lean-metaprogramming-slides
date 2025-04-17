import LeanSlides

#set_pandoc_options "-V" "revealjs-url=https://unpkg.com/reveal.js@^4" "-V" "theme=white"

#slides Intro /-!
# Lean's Pipeline

  ![Lean's Pipeline](https://goens.org/img/lean-architecture.png)

## Today
  - Parser
  - Macro Expansion
  - Elaborator/Pretty printer

# An Example

```
def foo (x : Nat) : Nat := x + 1
```

## Elaborates to
```
def foo : Nat -> Nat :=
fun (x : Nat) => HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) x (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))
```
-/

def foo (x : Nat) : Nat := x + 1
#print foo

set_option pp.raw true in
#print foo

#slides ExtensibleFrontend /-!

# Lean frontend is Extensible
  - Parser
  - Macros
  - Elaborator

# Parser
  Essentially: `String → Syntax`

  (more like `String → M Syntax` for a monad `M`)

  This means e.g. the string
```
"fun x : Nat => x + 1"
```
 gets parsed to a syntax tree:
```
(Term.paren "(" (Term.fun "fun" (Term.basicFun [`x] [(Term.typeSpec ":" `Nat)] "=>" («term_+_» `x "+" (num "1")))) ")")
```

# Extending the parser
- notation (infixl/r, etc)
- syntax
- More advanced: custom parsers (not today)
-/

axiom OPlus : Nat → Nat → Nat

infixl:45 " ⊕'' " => OPlus

#reduce (1 : Nat) ⊕'' (2 : Nat) ⊕'' (3 : Nat)

axiom Prec : Nat → Nat

notation:50 "PPP" x => Prec x

#reduce (PPP 3)

declare_syntax_cat mynat

syntax num : mynat
syntax mynat "+" mynat : mynat
syntax "[ℕ|" mynat "]" : term

-- More advanced stuff: see the definition e.g. of `num` above.

#slides Macros /-!
# Macros
Macros transform syntax: `Syntax → MacroM Syntax`
They can also be nested

# Simple macros
- Custom syntax with `macro_rules`
- Important: quotations and antiquotations

# Quotations
- Comes from Lisp: reflect syntax into language
- Difference between
```
 x + y
```

and
```
 `(x + y)
```
# Antiquotations

In a quotation, sometimes we might want to insert a value again, e.g.:
```
`(Nat.succ $(Lean.quote 1+1))
```
-/


macro_rules
  | `([ℕ| $n:num]) => `($n)
  | `([ℕ| $n₁ + $n₂]) => `(Nat.add [ℕ| $n₁] [ℕ| $n₂])

syntax "mytwo" : mynat

macro_rules
  | `([ℕ| mytwo]) => `(Nat.succ $(Lean.quote (0 + 1)))

#eval [ℕ| mytwo + 1]

inductive MyNat
  | var : String → MyNat
  | val : Nat → MyNat
  | add : MyNat → MyNat → MyNat

syntax ident : mynat
syntax "[MyNat|" mynat "]" : term

macro_rules
  | `([MyNat| $n:num]) => `(MyNat.val $n)
  | `([MyNat| $n₁ + $n₂]) => `(MyNat.add [MyNat| $n₁] [MyNat| $n₂])
  | `([MyNat| $x:ident]) => `(MyNat.var $x)

#eval [MyNat| 1 + 1]
#eval [MyNat| x + 1]

macro_rules
  | `([MyNat| $x:ident]) => `(MyNat.var $(Lean.quote x.getId.toString))

#eval [MyNat| x + 1]

#slides CustomMacros /-!
# Advanced Macros
- Somtimes, `macro_rules` is not enough
- Macro: is just a function!

-/


open Lean Elab Command Term Meta

-- Example from the metaprogramming book
syntax:10 (name := lxor) term:10 " LXOR " term:11 : term

@[macro lxor] def lxorImpl : Macro
  | `($l:term LXOR $r:term) => `(!$l && $r) -- we can use the quotation mechanism to create `Syntax` in macros
  | _ => Macro.throwUnsupported

#eval true LXOR true -- false
#eval true LXOR false -- false
#eval false LXOR true -- true
#eval false LXOR false -- false

-- An example from my own work (on demand):
-- https://github.com/goens/lean-murphi/blob/main/Murphi/EDSL.lean

-- Macro is just a function
#check Macro

#slides Elaboration /-!
 # Elaboration
 - Next step: `Syntax → ElabM Expr`
 - `Expr` is the Lean expression language (CIC)
 - This does stuff like typeclass synthesis, etc.
 -/

#check Expr
#check fun x : Nat => x + 1


#slides CustomElaboration /-!
# Custom Elaborators
- They're also just functions!
- Annotation (just like macros )
- This is where custom tactics go!

# Commands

Commands are not very different from terms, they just "live" at the top level of the documents.

We define them just like macros or elaborators, with a decorator:
```
@[command_elab command_syntax]
```

Here's the command we used to print the syntax example at the beginning:
-/


syntax (name := printsyntax) "#printsyntax" term : command -- declare the syntax

@[command_elab printsyntax]
def printSyntax : CommandElab := fun stx => do -- declare and register the elaborator
  logInfo s!"The syntax is:\n {stx[1]}"

#printsyntax fun x : Nat => x + 1

#slides Turtles /-!
# Turtles All the Way Down
- Lean is built in Lean
- Expressions like `if` `then` `else`
- Commands like `def`
- Even extensions themselves (e.g. `syntax`)
-/

example : (if true then 1 else 0) = 1 := by rfl

#slides Tactics /-!
# Tactic
  - Essentially: a Lean program
  - Runs in tactic mode (special elaborator)
  - Has a special monad (to access the goal, etc)

# Simple Custom Tactics

  - Just macros!
  ```
  macro "custom_sorry_macro" : tactic => `(tactic| sorry)
  ```
  (Example from the metaprogramming book)
-/

macro "custom_sorry_macro" : tactic => `(tactic| sorry)

/-! This is *not* a theorem, it's technically wrong...
 (`MyNat` just describes the syntax, not the interpretation) -/
theorem MyNatComm : [MyNat| x + y] = [MyNat| y + x] := by
  custom_sorry_macro

syntax "and_all" tactic : tactic

macro_rules
  | `(tactic| and_all $tac) => `(tactic|
      first
        | apply And.intro <;> (and_all $tac)
        | $tac;
    )

example : 43 = 43 ∧ 42 = 42 := by
  and_all trivial

example : 43 = 43 ∧ 42 = 42 ∧ 1 = 1:= by
  and_all rfl

#slides MoreResources /-!

# More reasouces
- Metaprogramming book: https://leanprover-community.github.io/lean4-metaprogramming-book/
- Lean Monad map: https://github.com/leanprover-community/mathlib4/wiki/Monad-map
- QQ package: https://reservoir.lean-lang.org/@leanprover-community/Qq
-/
