module main
open CFG
open transition_system

run {grammar_structure && #Name >1 && some Variable && some Abstraction && some Application} for 10
