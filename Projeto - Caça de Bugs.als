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

sig Relatorio{
	
}

sig Bug{}

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
		erro: Bug lone -> Time
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
	
	-- Todo grupo tem pelo menos um funcinario
--	one g:Grupo | all f:Funcionario | one t:Time| f in g.funcionarios.t

	-- Todo funcionario tem que ta ligado a uma empresa
	all f:Funcionario | one e:Empresa | f in e.funcionarios	

	--Todo bug esta ligado a um codigo fonte
	

	//todos os clientes tem que estar ligado ao repositorio
	all p:Projeto | one p.~projetos
	all c: Cliente | one c.~clientes
	all c: Cliente | some c.projetos
}


fact fato1{
	
	#Empresa = 1
	#Repositorio = 1
	#Funcionario=3
}

run{} for 3 but  exactly  2 Subpasta
