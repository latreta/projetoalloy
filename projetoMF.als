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

// Asserts

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

//Definição de predicados

//Verifica se pessoa 'n' tomou dose extra
pred pessoaTomouDoseExtra(n: Nome){
	Pfizer in Vacinados.doseExtra[n]
}

//Retorna se a pessoa 'n' tomou vacina 'v'
pred pessoaVacinada(n: Nome, vac: Vacina){
	all v: Vacinados | v.primeiraDose[n] = vac or v.segundaDose[n] = vac
}

//Verifica se pessoa 'n' teve efeito colateral 'col'
pred pessoaEfeitoColateral(n: Nome, col: EfeitoColateral){
	all v: Vacinados | col in v.colaterais[n]
}

//Verifica se a vacina 'v' causou efeito colateral 'col'
pred vacinaEfeitoColateral(vac: Vacina, col: EfeitoColateral){
	all v: Vacinados | all n: Nome | vac in v.primeiraDose[n] and col in v.colaterais[n]
}

// Verifica se a pessoa 'n' tomou Janssen
pred tomouJanssen(n: Nome) {
	all v:Vacinados | v.primeiraDose[n] = Janssen
}

// Verifica se pessoa 'n' tomou segunda dose 
pred tomouSegundaDose(n: Nome){
	all v:Vacinados | v.segundaDose[n] != none
}

// Verifica se pessoa 'n' pode tomar a dose extra
pred podeTomarDoseExtra(n: Nome) {
	tomouJanssen[n] or tomouSegundaDose[n] and !pessoaTomouDoseExtra[n]
}

//  Verifica se ao menos 1 pessoa tomou uma determinada Vacina 'vac'
pred verificaSeVacinaFoiTomada(vac: Vacina) {
	all v: Vacinados | vac in v.primeiraDose[Nome] or v.doseExtra[Nome] = vac
}

// Verifica se pessoa 'n' pode ou não tomar a primeira dose
pred podeTomarPrimeiraDose(n:Nome){
	all v:Vacinados | v.primeiraDose[n] = none
}

// Verifica se pessoa 'n' pode ou não tomar a segunda dose
pred podeTomarSegundaDose(n:Nome, vac:Vacina){
	all v:Vacinados | !tomouJanssen[n] and  !tomouSegundaDose[n] and v.primeiraDose[n] = vac
}

pred show () {}

//Retorna a quantidade de pessoas que receberam a primeira dose do tipo passado pelo parametro
fun primeiraDoseAplicada(v: Vacina): Int {
    #(~(Vacinados.primeiraDose)[v])
}

fun listarNomesPrimeiraDose(): set Nome {
	~(Vacinados.primeiraDose)[Vacina]
}

fun listarNomesDuasDose(): set Nome {
	~(Vacinados.primeiraDose)[Vacina] & ~(Vacinados.segundaDose)[Vacina]
}

fun listarPessoasTomaramVacina(v: Vacina): set Nome {
	~(Vacinados.primeiraDose)[v] + ~(Vacinados.segundaDose)[v] + ~(Vacinados.doseExtra)[v]
}

fun quantasPessoasTomaramDoseExtra(): Int {
	#(~(Vacinados.doseExtra)[Vacina])
}

fun quantasPessoasPrecisamDoseExtra(): Int {
	#((~(Vacinados.segundaDose)[Vacina] + ~(Vacinados.primeiraDose)[Janssen]) - (~(Vacinados.doseExtra)[Pfizer]))
}

pred addPrimeiraDose(v, vc: Vacinados, n: Nome, vac: Vacina) {
	vc.primeiraDose = v.primeiraDose + n -> vac
}

fun listaEfeitosColateraisPorPessoa(v: Vacinados, n: Nome): Nome -> set EfeitoColateral {
	n <: v.colaterais
}

pred addSegundaDose(v, vc: Vacinados, n: Nome, vac: Vacina) {
	vc.segundaDose = v.segundaDose + n -> vac
}

pred addDoseExtra(v, vc: Vacinados, n: Nome) {
	vc.doseExtra = v.doseExtra + n -> Pfizer
}

//check verificaEfeitoColateralSemVacina for 15
run podeTomarSegundaDose for 15
