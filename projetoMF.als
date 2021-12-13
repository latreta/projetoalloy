abstract sig Vacina {}
sig Tipo {}
one sig CoronaVac, Pfizer, Astrazeneca, Janssen extends Vacina {}

sig Vacinados {
	primeiraDose: Tipo -> one (Vacina - Janssen),
	segundaDose: Tipo -> lone (Vacina - Janssen),
	doseUnica: Tipo -> Janssen,
	doseExtra: Tipo -> Pfizer
}

//Retorna a quantidade de pessoas que receberam a primeira dose do tipo passado pelo parametro
fun primeiraDoseAplicada(v: Vacina): Int{
	#(~(Vacinados.primeiraDose)[v] + ~(Vacinados.doseUnica)[v])
}

//Verifica se a primeira é igual a segunda
assert primeiraIgualSegunda {
	all v: Vacinados | v.primeiraDose = v.segundaDose
}

check primeiraIgualSegunda

//pred show () {}

//run show for 3 but 2 Vacinados
