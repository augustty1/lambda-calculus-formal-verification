----------------------------------------------
-- recognizable set and syntatic categories --
----------------------------------------------
abstract sig Expression {}

sig Name {}

sig Variable extends Expression {
	var	name : one Name
}

sig Abstraction extends Expression {
	var param : one Variable,
	var body : one Expression
}

sig Application extends Expression {
	var func : one Expression,
	var arg : one Expression
}

----------------------
-- macros and utils --
----------------------
fun derivations[e: Expression]: set Expression {
	(e.(Abstraction<:param) + e.(Abstraction<:body)+
	 e.(Application<:func) + e.(Application<:arg) )
}

fun subtree[e: Expression]: set Expression {
	e.*({e1,e2: Expression | e2 in e1.derivations})
}

-- ? --
fun subtree_names[e: Expression]: set Name{
	(e.subtree & Variable).name
}

pred grammar_structure {
	-- one start expression --
	one e: Expression | e not in Expression.derivations

	-- no cycles --
	no e: Expression |
		e in e.^({e1,e2: Expression | e2 in e1.derivations})
		
	-- no expression derives from itself --
	no e: Expression | e in e.derivations
	
	-- both abstractions and applications generate distinct expressions --
	all ab: Abstraction | ab.param != ab.body
	all ap: Application | ap.func != ap.arg

	-- an expression is not derived from two distinct expressions --
	all e1,e2: Expression |
		e1!=e2 => no(e1.derivations & e2.derivations)
}

-- remark : variables can share the same name --


