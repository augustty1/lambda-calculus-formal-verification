-- name and syntactic category registers

sig Name {}

abstract sig Expression {}

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
