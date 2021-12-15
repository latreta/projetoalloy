abstract sig Vacina {}
one sig Nome {}
one sig CoronaVac, Pfizer, Astrazeneca, Janssen extends Vacina {}

sig Vacinados {
    primeiraDose: Nome -> lone Vacina,
    segundaDose: Nome -> lone Vacina,
    doseExtra: Nome -> lone Pfizer
}

fact "Nao se pode tomar primeira e segunda dose diferentes"{
    no v: Vacinados | v.segundaDose[Nome] not in v.primeiraDose[Nome] 
}

fact "Dose unica de Janssen"{
    some v: Vacinados | Janssen = v.primeiraDose[Nome] implies v.segundaDose[Nome] not in Vacina
}

fact "Nao pode tomar janssen de segunda dose" {
    no v: Vacinados | Janssen = v.segundaDose[Nome]
}

fact "Nao pode tomar dose extra sem ter tomado duas vacinas"{
	all v: Vacinados | Nome -> Pfizer in v.doseExtra implies Nome -> Janssen in v.primeiraDose or Nome -> Pfizer in v.doseExtra implies v.segundaDose[Nome] != none
}

//Retorna a quantidade de pessoas que receberam a primeira dose do tipo passado pelo parametro
fun primeiraDoseAplicada(v: Vacina): Int{
    #(~(Vacinados.primeiraDose)[v])
}

//Verifica se a primeira é igual a segunda
assert primeiraIgualSegunda {
    all v: Vacinados | v.primeiraDose[Nome] in v.segundaDose[Nome] or
                    v.segundaDose[Nome] = none
}

//check primeiraIgualSegunda

pred show () {}

run show for 3