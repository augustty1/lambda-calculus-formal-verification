module transition_system
open CFG

-- op trace --
abstract sig Reduction {}
one sig None, Alpha, Beta extends Reduction {}

-- alpha reduction --
-- λx.E => λw.E[x->w] --

/*
	Não tem ninguém em E utilizando o nome w.
	i.e. Não tem ninguém na subárvore enraizada em E tal que utilize o nome w.
	
	Se isso é verdade, todo elemento pertencente ao conjunto de expressões que fazem parte 
	da subárvore E e que utilizam x mudam para w.

	Nada mais acontece além dessa renomeação.
	i.e. Relações se mantem as mesmas.
*/

-- beta reduction --
-- (λx.E)(E1) => E[x->E1] --

/*
	Tem que verificar uma forma de validade
	Caso contrario deve ter havido uma redução alpha na expressão

	Ordem em que as reduções betas são aplicadas ? 
	Mas minha expressão é cheia de parenteses, já que é uma árvore.
*/
