module cacabugs

sig Empresa{
	repositorio: one Repositorio,
	cacadores: set Funcionario
}

sig Funcionario extends Pessoa{}

sig Pessoa{}

sig Repositorio{
	clientes: set Cliente
}

sig CodigoFonte{}

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

fact Sistema{
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

	-- Todo funcionario esta em apenas uma empresa
	all f:Funcionario | one e:Empresa | f in e.cacadores

	-- Toda empresa tem pelo menos um funcinario
	all e:Empresa | some f:Funcionario | f in e.cacadores
}

fact fato1{
	//todos os clientes tem que estar ligado ao repositorio
	all p:Projeto | one p.~projetos
	all c: Cliente | one c.~clientes
	all c: Cliente | some c.projetos
	#Empresa = 1
	#Repositorio = 1
}

run{} for 3 but   exactly  3 Subpasta
