module transition_system
open CFG

-- op trace --
abstract sig Reduction {}
one sig Alpha, Beta extends Reduction {}
one sig Track {
	var op: lone Reduction 
}

-- alpha reduction --
-- λx.E => λn.E[x->n] --
pred alpha_reduce [ab: Abstraction, n: Name] {
	-- pre conditions --
	-- new parameter name
	ab.param.name != n
	-- no capture or confusion
	no (ab.body.subtree_names & n)

	-- post conditions --
	-- change the name

	-- frame conditions --
	-- no other relation changes

	Track.op' = Alpha
}

-- beta reduction --
-- (λx.E)(E1) => E[x->E1] --

------------------------------
-- initial state conditions --
------------------------------
pred init [] {
	-- for convenience, no tracked operation --
	no Track.op
	
	-- well formed expression --
	grammar_structure

	-- names and some expressions --
	#Name > 1 and some Abstraction and some Application
}

-------------------------
-- transition relation --
-------------------------
pred trans [] {
	(some ab: Abstraction | some n: Name | alpha_reduce[ab, n])
}

