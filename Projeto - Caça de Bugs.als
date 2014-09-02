/*
*Importando a library ordering. Em seguida, aplicando à assinatura Time.
*/
open util/ordering [Time]

module cacabugs


/**ASSINATURAS*/

/*
*Assinatura para simular tempo, cada tempo é 
*referente a um dia diferente
*/
sig Time{}

/*
* Grupo é o time de funcionarios que caçam bugs.
*/
one sig Grupo{
	codigoFonteAnalisado: CodigoFonte one -> Time,
	prestaServico: Cliente one -> Time
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
	pastas: set Pasta,
	statusProjeto: StatusProjeto one -> Time
}

sig Pasta{
	subpastas: set Subpasta
}

sig Subpasta{
	codigosfonte: one CodigoFonte
}

abstract sig StatusDoBug{}
one sig Nivel1, Nivel2, Nivel3 extends StatusDoBug{}

abstract sig StatusProjeto{}
 sig Apto, Inapto extends StatusProjeto{}

abstract sig VersaoDoCodigo{}
sig Atual, Antiga extends VersaoDoCodigo{}



/**FUNCOES*/

-- Retorna o cliente ao qual o grupo esta prestando servico
fun getClienteByGrupo[g:Grupo, t:Time]: Cliente{
	g.prestaServico.t
}

-- Retorna o codigo fonte que esta sendo analisado pelo grupo
fun getCodigoByGrupo[g:Grupo, t:Time]: CodigoFonte{
	g.codigoFonteAnalisado.t
}

-- Retorna os codigos fontes de todas as subpastas de todos os projetos de um cliente
--fun getAllCodigosByCliente[c:Cliente]: CodigoFonte{
--	c.projetos.pastas.subpastas.codigosfonte
--}

-- Retorna o cliente que eh dono do codigo passado como paramentro
fun getClienteByCodigo[c:CodigoFonte]: Cliente{
	c.~codigosfonte.~subpastas.~pastas.~projetos
}

-- Retorna o projeto na qual o codigo esta contido
fun getProjetoByCodigo[c:CodigoFonte]: Projeto{
	c.~codigosfonte.~subpastas.~pastas
}

/**PREDICADOS*/


--Garante que um grupo nao vai passar mais de um dia seguido analisando o codigo do mesmo cliente
pred setCliente[cliente:Cliente, g:Grupo, t,t': Time] {
	
	-- Pega o cliente que ta sendo analisado pelo grupo em um tempo t
		getClienteByGrupo[g,t] != getClienteByGrupo[g,t']

	-- Pega o codigo fonte de um cliente em um tempo t e compara com o codigo fonte de um grupo em um mesmo instante de tempo
		getClienteByGrupo[g,t] == getClienteByCodigo[getCodigoByGrupo[g,t]] 

	-- Pega o codigo fonte de um cliente em um tempo t e compara com o codigo fonte de um grupo em um mesmo instante de tempo
		getClienteByGrupo[g,t']== getClienteByCodigo[getCodigoByGrupo[g,t']] 

	-- Verifica se o codigo fonte analisado pelo grupo é a versao mais atual no tempo t
		getCodigoByGrupo[g,t].versao.t == Atual

	-- Verifica se o codigo fonte analisado pelo grupo é a versao mais atual no tempo t'
		getCodigoByGrupo[g,t'].versao.t' == Atual
}

-- Garante que se um projeto tem bug seu status sera Inapto e caso contrario sera Apto
pred setStatusProjeto[bug:Bug, codigo:CodigoFonte,  t:Time]{
		
		-- Garante que o codigo fonte eh a versão mais atual
		codigo.versao.t == Atual

		-- Se existir um erro no código implica dizer o projeto na qual esta cotido o bug esta inapto
		bug in codigo.erros.t => (getProjetoByCodigo[codigo].statusProjeto.t==Inapto)

		-- Se nao existir um erro no código implica dizer o projeto na qual o codigo esta cotido esta Apto
		(#codigo.erros.t == 0) =>  (getProjetoByCodigo[codigo].statusProjeto.t==Apto)

	-- Todo status de projeto deve esta ligado a um projeto
	
}

pred init [t:Time] {}

fact tracesProjetoStatus{
	init [first]
 	all codigo:CodigoFonte |all pre: Time-last | let pos = pre.next |
 		all bug: Bug |	
 		setStatusProjeto[bug,codigo,pos]
}

fact traces {
	init [first]
 	all cliente: Cliente |all pre: Time-last | let pos = pre.next |
 		some g: Grupo |	
 		setCliente[cliente,g,pre,pos]
}





/**FATOS*/
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
	
	--Um grupo so pode pegar codigo fonte com bug
	all g:Grupo | all t:Time| #(g.codigoFonteAnalisado.t).erros.t > 0

	--Todo nivel deve estar vinculado a um bug
	--	all s:StatusDoBug | all b:Bug | all t:Time | !(s not in b.situacaoDoBug.t)


	-- Todo projo so pode ter uma versao atual do codigo
	 all p:Projeto |all t:Time|one s:Subpasta | one c:CodigoFonte| 
	((s in p.pastas.subpastas)  and (c in s.codigosfonte)) and (c.versao.t == Atual)


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
	#Cliente = 2

}

run{} for 3 but  exactly  3 Bug
