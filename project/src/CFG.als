-- recognizable set and syntatic categories --
abstract sig Expression {}

sig Name {}

sig Variable extends Expression {
	name : one Name
}

sig Abstraction extends Expression {
	param : one Variable,
	body : one Expression
}

sig Application extends Expression {
	func : one Expression,
	arg : one Expression
}

fun derivations[e: Expression]: set Expression {
	(e.(Abstraction<:param) + e.(Abstraction<:body)+
	e.(Application<:func) + e.(Application<:arg) )
}

fact grammar_structure {
	-- one start expression --
	one e: Expression | e not in Expression.derivations

	-- no cycles ???? --	

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