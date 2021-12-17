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

fact "Nao pode tomar dose extra sem ter tomado duas vacinas ou uma dose da Janssen"{
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

//Pessoa tomou dose extra
pred pessoaTomouDoseExtra(n: Nome){
Pfizer in Vacinados.doseExtra[n]
}

//Retorna se a pessoa 'n' tomou vacina 'v'
pred pessoaVacinada(n: Nome, vac: Vacina){
	all v: Vacinados | v.primeiraDose[n] = vac or v.segundaDose[n] = vac
}

//Retorna se pessoa 'n' teve efeito colateral 'col'
pred pessoaEfeitoColateral(n: Nome, col: EfeitoColateral){
	all v: Vacinados | col in v.colaterais[n]
}

//Retorna se a vacina 'v' causou efeitor colateral 'col'
pred vacinaEfeitoColateral(vac: Vacina, col: EfeitoColateral){
	all v: Vacinados | all n: Nome | vac in v.primeiraDose[n] and col in v.colaterais[n]
}



//Verifica se a primeira é igual a segunda
assert primeiraIgualSegunda {
    all v: Vacinados | all n: Nome | v.segundaDose[n] != none implies v.primeiraDose[n] = v.segundaDose[n] 
}

//Verifica se a Janssen é dose única
assert janssenDoseUnica {
	all v: Vacinados | all n: Nome | Janssen in v.primeiraDose[n] implies v.segundaDose[n] = none
}

//Verifica se tomou doseExtra sem ter tomado duas vacinas
assert verificaDoseExtraValida {
	all v: Vacinados | all n: Nome | Pfizer in v.doseExtra[n] implies Janssen in v.primeiraDose[n] or 
	v.segundaDose[n] != none 
}

//Verifica se tem efeito colateral sem vacina
assert verificaEfeitoColateralSemVacina{
	all v: Vacinados | all n: Nome | #v.colaterais[n] > 0 implies v.primeiraDose[n] in Vacina
}

pred show () {}

//check verificaEfeitoColateralSemVacina for 15
run pessoaEfeitoColateral for 15
