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


-- talvez de pra resolver com cardinalidade das relações em alloy
fact {

-- variáveis podem compartilhar de um mesmo nome
	-- meu modelo ja permite isso

-- param e body em Abstraction devem ser expressões distintas (podem ter mesmo nome)
	-- e que não sejam a si própria
	-- como param é Variable nem precisa de por a restrição
 	all ab: Abstraction | (ab.param != ab.body ) && (ab.body != ab)

-- func e arg em Application devem ser expressões distintas (podem ter mesmo nome)
	-- e não podem ser a si própria
	all ap: Application | (ap.func != ap.arg) && (ap.func != ap) && (ap.arg != ap)

-- aplicacoes distintas se relacionam com expressoes distintas
	-- todo param e arg e func e etc tem pais distintos	
	all i,j : Application | i!=j implies ((i.arg != j.arg) && (i.func != j.func) && (i.arg != j.func))

-- abstracoes distintas se relacionam com expressoes distintas
	all i,j: Abstraction | i!=j implies ((i.param != j.param) && (i.body != j.body) && (i.param != j.body))

-- aplicaoes e abstracoes se relacionam com expressoes distintas
	-- talvez de pra algutinar tudo isso com uma funcao que me retornar os "filhos" e falar que sempre sao distintos ou os "pais"


}

-- isso aqui deu problema
run {some Variable && some Application && some Abstraction} for 8
