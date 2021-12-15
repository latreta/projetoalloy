abstract sig Vacina {}
abstract sig EfeitoColateral {}
sig Nome {}
one sig CoronaVac, Pfizer, Astrazeneca, Janssen extends Vacina {}
one sig Febre, Dor, Enjoo, Paladar, Diarreia extends EfeitoColateral {}

one sig Vacinados {
    primeiraDose: Nome -> lone Vacina,
    segundaDose: Nome -> lone Vacina,
    colaterais: Nome -> set EfeitoColateral,
    doseExtra: Nome -> lone Pfizer
}

fact "Nao se pode tomar primeira e segunda dose diferentes"{
    all v: Vacinados | no n: Nome | v.segundaDose[n] not in v.primeiraDose[n] 
}

fact "Nao pode tomar janssen de segunda dose" {
    all  v: Vacinados | no n: Nome | Janssen = v.segundaDose[n]
}

fact "Nao pode tomar dose extra sem ter tomado duas vacinas"{
    all v: Vacinados | all n: Nome |   n -> Pfizer in v.doseExtra implies n -> Janssen in v.primeiraDose
                or n -> Pfizer in v.doseExtra implies v.segundaDose[n] != none
}

fact "Nao se pode ter efeito colateral sem tomar vacina" {
    all v: Vacinados | all n: Nome | v.colaterais[n] != none implies v.primeiraDose[n] != none
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

pred show () {}

//check primeiraIgualSegunda for 3
run show for 15
