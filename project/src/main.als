--=============================
-- DCC831 Formal methods
-- 2025.2
-- Final project
--
-- Name: Augusto Guerra de Lima
--
--==============================

----------------
-- Signatures --
----------------
abstract sig Status {}

one sig Active, Inactive extends Status {}

abstract sig Expression {
	 var status : one Status
}

abstract sig Reduction {}

one sig Alpha, Beta, None extends Reduction {}

sig Abstraction extends Expression {
	var param : one Variable,
	var body : one Expression
}

sig Application extends Expression {
	var func : one Expression,
	var arg : one Expression
}

sig Variable extends Expression {
	var binder: lone Abstraction
}

one sig Track {
	var op: lone Reduction
}

----------------------
-- Macros and utils --
----------------------

fun derivations[e: Expression]: set Expression {
	(e.(Abstraction<:param) + e.(Abstraction<:body)+
	 e.(Application<:func) + e.(Application<:arg) )
}

fun subtree[e: Expression]: set Expression {
	e.*({e1,e2: Expression | e2 in e1.derivations})
}

fun subtree2[e: Expression, f: Expression]: set Expression {
	e.*({e1,e2: Expression | (e2 in e1.derivations and e1 != f and e2 != f)})
}

fun active_expressions [] : set Expression {
	{e: Expression | e.status = Active}
}

fun inactive_expressions [] : set Expression {
	{e: Expression | e.status = Inactive}
}

-- Frame conditions

pred noStatusChange [S : set Expression] {
	all e : S | e.status' = e.status
}

pred noParamChange [S : set Abstraction] {
	all a : S | a.param' = a.param
}

pred noBodyChange [S : set Abstraction] {
	all a : S | a.body' = a.body
}

pred noFuncChange [S : set Application] {
	all a : S | a.func' = a.func
}

pred noArgChange [S : set Application] {
	all a : S | a.arg' = a.arg
}

pred noBinderChange [S : set Variable] {
	all v : S | v.binder' = v.binder
}

----------------------------
-- Well formed expression --
----------------------------

pred well_formed_expression {
	-- No Inactive expressions, a priori -
	no e: Expression | e.status = Inactive

	-- One start expression --
	one e: Expression | e not in Expression.derivations

	-- No cycles --
	no e: Expression |
		e in e.^({e1,e2: Expression | e2 in e1.derivations})
		
	-- No expression derivates from itself --
	no e: Expression | e in e.derivations

	----------
	-- Bind --
	----------
	-- The parameter is binded by its abstraction --
	all a: Abstraction | a.param.binder = a

	-- If v is binded, then v is the parameter or occurs within the body --
	all v: Variable | some v.binder => ((v=v.binder.param) or (v in subtree[v.binder.body]))

	-- Binders are distinct --
	all v1,v2: Variable | (some v1.binder and some v2.binder and v1!=v2) => (v1.binder != v2.binder)

	-- Binded variables make sense within the scope in which they are binded --
	all v: Variable, e: Expression | 
		(e!=v and some v.binder and v in subtree[e]) => (v not in subtree2[e,v.binder] or e in subtree[v.binder])

}

----------------
-- Operations --
----------------

pred beta_reduction [ap: Application]{
	-- Pre-conditions
	ap.func in Abstraction
	ap.status = Active

	-- Post-conditions
	-- pais de ap tem que apontar para o Body agora
	all a: Application | ((a.func = ap) => (a.func' = ap.func.body))
	all a: Application | ((a.arg = ap) => (a.arg' = ap.func.body))
	all a: Abstraction | ((a.body = ap) => (a.body' = ap.func.body))

	-- ocorrencias de ap.func.param agora apontam para ap.arg
	all a: (Application & subtree[ap.func.body]) | 
			((a.func = ap.func.param) => (a.func' = ap.arg))
	
	all a: (Application & subtree[ap.func.body]) |
			((a.arg = ap.func.param) => (a.arg' = ap.arg)) 

	all a: (Abstraction & subtree[ap.func.body]) | 
			((a.body = ap.func.param) => (a.body' = ap.arg))

	-- setar como inativo
	--tratar corner de aparecer func no arg --
	-- se nao aparece continua fazendo o q estava fazendo
	((ap.func not in subtree[ap.arg]) => (
		ap.func.param.status' = Inactive and
		ap.func.status' = Inactive 	 	and		
		ap.status' = Inactive))

	-- se aparece entao nao desativa a abstração
	((ap.func in subtree[ap.arg]) => (ap.status' = Inactive))
			

	-- Frame-conditions
	-- Status com os corner cases --
	-- se nao aparecer continua fazendo o que estava fazendo
	((ap.func not in subtree[ap.arg]) => (
		noStatusChange[Expression - (ap + ap.func + ap.func.param)]
	))

	-- se aparecer entao nao desativa a abstração
	((ap.func in subtree[ap.arg]) => (
		noStatusChange[Expression - ap]
	))
	
	noParamChange[Abstraction]
	noBodyChange[Abstraction - ({a : Abstraction | a.body = ap} + {a: Abstraction & subtree [ap.func.body] | a.body = ap.func.param})]
	noFuncChange[Application - ({a: Application | a.func = ap} + {a: Application & subtree[ap.func.body] | a.func = ap.func.param })]
	noArgChange[Application - ({a: Application | a.arg = ap} + {a: Application & subtree[ap.func.body] | a.arg = ap.func.param})]
	noBinderChange[Variable]

	-- Track op
	Track.op' = Beta
}

pred noOp [] {
	-- Frame conditions
	noStatusChange[Expression]
	noParamChange[Abstraction]
	noBodyChange[Abstraction]
	noFuncChange[Application]
	noArgChange[Application]
	noBinderChange[Variable]
	
	-- Track op
	Track.op' = None
}

------------------------------
-- Initial state conditions --
------------------------------

pred init [] {
	no Track.op
	
	well_formed_expression


	-- Some useful tests --
--	some Abstraction and some Application  
--	some Abstraction and (some ap: Application | ap not in Expression.derivations) and (no v:Variable | no v.binder)
--	some Abstraction (some ap: Application | ap not in Expression.derivations)
--	#Abstraction = 1 and #Variable = 1
--	some Abstraction and some Application and (no v: Variable | no v.binder)
--  #Abstraction = 1  and	one a: Abstraction,  b: Application | (a.body = b) and (no v:Variable | no v.binder)
-- Beta-redex
--	#Abstraction = 1 and #Application = 1 and (one a: Abstraction, b: Application | a.param = a.body and b.func = a and b.func != b.arg)

}

-------------------------
-- Transition relation --
-------------------------

pred trans [] {
	(some ap: Application | beta_reduction[ap])
	or
	noOp[]
}

----------------------
-- System predicate --
----------------------

pred system {
	init and always trans
}

run {system and eventually Track.op=Beta} for 10

----------------
-- Properties --
----------------

pred p1 {
-- Toda expressao eventualmente nao vai ser mais reduzida --
-- Corner case, operador omega, é necessario fixa-lo --
	eventually(always(Track.op != Beta))
}

pred p2 {
	-- Id N => N
	(
		one ap : Application | (
			ap not in Expression.derivations and
			ap.func in Abstraction			 and
			ap.func.body in Variable		 and
			ap.func.param = ap.func.body     and
			ap.func != ap.arg			     and
			beta_reduction[ap] 
		)
	)
	=>
	(
		one ap : Application | (
			beta_reduction[ap] and
			subtree[ap.arg] = active_expressions'
		)
	)
}

----------------
-- Assertions --
----------------

-- assert a1 {system => p1} -- Esperado: Contraexemplo, não encontrou. Motivo: Corner case
-- assert a2 {system => p2} -- Esperado: Não tem contra-exemplo, de fato não encontrou

--check a2 for 8


