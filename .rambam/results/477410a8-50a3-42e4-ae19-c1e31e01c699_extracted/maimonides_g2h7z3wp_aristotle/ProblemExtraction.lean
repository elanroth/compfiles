-- Stub for ProblemExtraction macros
import Lean

open Lean Elab Command in
elab "problem_file" _rest:term : command => pure ()

syntax "determine " ident " : " term " := " term : command
macro_rules
  | `(command| determine $name : $ty := $val) => `(def $name : $ty := $val)

syntax "problem " ident ppSpace bracketedBinder* " :\n" term " := " term : command
macro_rules
  | `(command| problem $name $args* :
    $ty := $val) => `(theorem $name $args* : $ty := $val)
