/*
*Importando a library ordering. Em seguida, aplicando à assinatura Time.
*/
open util/ordering [Time]

module cacabugs

/*
*Assinatura para simular tempo, cada tempo é 
*referente a um dia diferente
*/
sig Time{}

/*
* Grupo é o time de funcionarios que caçam bugs.
*/
one sig Grupo{
	codigoFonteAnalisado: CodigoFonte one -> Time
	
}

sig Bug{
	situacaoDoBug: StatusDoBug one -> Time
}

sig Empresa{
	funcionarios: set Funcionario,
	repositorio: one Repositorio,
	grupoCacaBug: Grupo
}

sig Funcionario extends Pessoa{
	-- Toda instancia de funcionario é um membro de um grupo
	membro:  Grupo one -> Time
}

sig Pessoa{}

sig Repositorio{
	clientes: set Cliente
}

sig CodigoFonte{
	erros: set Bug  -> Time,
	versao: VersaoDoCodigo one -> Time
}

sig Cliente{
	projetos: set Projeto
}

sig Projeto{
	pastas: set Pasta
}

sig Pasta{
	subpastas: set Subpasta
}

sig Subpasta{
	codigosfonte: one CodigoFonte
}

abstract sig StatusDoBug{}
one sig Nivel1, Nivel2, Nivel3 extends StatusDoBug{}


abstract sig VersaoDoCodigo{}
 sig Atual, Antiga extends VersaoDoCodigo{}


pred setCodigo[c:CodigoFonte, g:Grupo, t,t': Time] {
	c = g.codigoFonteAnalisado.t
	g.codigoFonteAnalisado.t' != c
}

pred init [t:Time] {}

fact traces {
	init [first]
 	all pre: Time-last | let pos = pre.next |
 		some c: CodigoFonte, g: Grupo |	
 		setCodigo[c,g,pre,pos]
}


// FATOS
fact EstruturaDoSistema{
	--Todo Projeto Fonte Tem Um Cliente
	all p:Projeto| some c:Cliente| p in c.projetos

	-- Toda pasta tem um unico projeto
	all p:Pasta | one p2:Projeto | p in p2.pastas

	-- Todo projeto tem uma unica pasta
	all p:Projeto| one p2:Pasta | p2 in p.pastas

	-- Toda pasta tem um ou mais subpastas
	all p:Pasta | some s:Subpasta | s in p.subpastas

	-- Toda subpasta tem apenas uma pasta 
	all s:Subpasta | one p:Pasta | s in p.subpastas

	--Toda subpasta tem apenas um codigo fonte
	all c:CodigoFonte | one s:Subpasta |  c in s.codigosfonte

	--  Todo empresa so tem apenas um grupo
	one e:Empresa| one g:Grupo|  g in e.grupoCacaBug

	-- Todo funcionario tem que ta ligado a uma empresa
	all f:Funcionario | one e:Empresa | f in e.funcionarios	

	--Qualquer bug esta em algum codigo fonte, 
	--e não estar em outro codigo fonte no mesmo instante de tempo
	all b:Bug | some c:CodigoFonte | all c1:CodigoFonte| all t:Time |
	b in c.erros.t && 	b not in (c1-c).erros.t

	--Um grupo não pode vasculhar o mesmo codigo durante dois dias
	
	
	--Um grupo so pode pegar codigo fonte com bug
	all g:Grupo | all t:Time| #(g.codigoFonteAnalisado.t).erros.t > 0

	--Todo nivel deve estar vinculado a um bug
	--	all s:StatusDoBug | all b:Bug | all t:Time | !(s not in b.situacaoDoBug.t)


	-- Todo projo so pode ter uma versao atual do codigo
	 all p:Projeto |all t:Time|one s:Subpasta | one c:CodigoFonte| 
	((s in p.pastas.subpastas)  and (c in s.codigosfonte)) and (c.versao.t == Atual)

	-- Todo versao deve esta ligada a um codigo
--	all v:VersaoDoCodigo | all c:CodigoFonte| all t:Time| v in c.versao.t

	//todos os clientes tem que estar ligado ao repositorio
	all p:Projeto | one p.~projetos
	all c: Cliente | one c.~clientes
	all c: Cliente | some c.projetos
}


fact fato1{
	
	#Empresa = 1
	#Repositorio = 1
	#Funcionario=3
	#Subpasta = 3
	#Projeto =  1
}

run{} for 3 but  exactly  3 Bug
