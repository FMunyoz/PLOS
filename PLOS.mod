#*********************** Modelo ********************
# Bin Packing with Fragmentable Items: Presentation and Approximations
# Bertrand Lecun, Thierry Mautor, Franck Quessette, Marc-Antoine Weisser
#
# Definición
#
# Fragmentable Bin Packing Problem (FIBP): Es un Bin Packing Problem en el que cada item IdBaldes puede ser dividido en items más pequeños.
# Para nuestro modelo el item es el número de baldes para un Cliente-Articulo. Con esto conseguimos que el máimo número de baldes del mismo ClienteArticulo vaya en el mismo palet.
#
# Objetivo: Determinar el número mínimo de Palets de tamaño CapacidadDelPaletEnBaldes en que se pueden fragmentar los BaldesDelArticuloParaElCliente minimizando  el número de fragmentos de items 
#
# Tenemos un número de items card(IdBaldes) donde cada IdBaldes tiene un número de baldes BaldesDelArticuloParaElCliente(IdBaldes)
# Tenemos un número de palets NumeroDePaletsPosibles, cada uno de ellos con una capacidad CapacidadDelPaletEnBaldes;
# 
# Mínimo número de palets:  aquellos que, por la capacidad, permiten poner el total de baldes.
#
# Restricciones generales
#
#  TotalDeBaldesEnFragmentos: Para cada item  Cliente-Articulo (IdBaldes), la suma de Baldes de todos los palets debe ser igual número de baldes del IdBaldes, es decir, todos los baldes deben estar repartidos entre los palets.
#  CadaPaletNoDebeExcederse: Para todo palet, La suma de baldes en cada palet debe ser menor o igual a la capacidad (número de baldes) del palet.
#  PaletEsUsadoParaIdBalde: Un palet es usado para el item IdBalde si algun balde de IdBalde es puesto en el Palet.
#
#Restricciones  de Campofrío
#
# BaldesCompatibles: Todos los baldes del palet deben ser compatibles (del mismo TipoDeBalde). 
# Todos los baldes del palet dben ser de la misma sección.

# Conjuntos
set IdBaldes dimen 2;

# Parámetros
param BaldesDelArticuloParaElCliente{(i,j) in IdBaldes};
param TipoDeBalde{(i,j) in IdBaldes};
param SeccionDelBalde{(i,j) in IdBaldes};
param BaldeCompatible {(i,j) in IdBaldes, (l,m) in IdBaldes} := if TipoDeBalde[i,j] = TipoDeBalde[l,m] then 1, binary;
param BaldesDeLaMismaSeccion {(i,j) in IdBaldes, (l,m) in IdBaldes} := if SeccionDelBalde[i,j] = SeccionDelBalde[l,m] then 1, binary;

param NumeroDePaletsPosibles := 100;
param CapacidadDelPaletEnBaldes := 44;

#variables
var IdBaldeEnPalet{IdBaldes, 1..NumeroDePaletsPosibles}, binary;
var BaldesDelIdBaldeEnPalet{(i,j) in IdBaldes, 1..NumeroDePaletsPosibles} >= 0, integer;
var BaldesEnMismoPalet {(i,j) in IdBaldes, (l,m) in IdBaldes, k in 1..NumeroDePaletsPosibles}, binary;

#Restricciones
subject to MinimoNumeroDePalets: round(sum{(i,j) in IdBaldes} BaldesDelArticuloParaElCliente[i,j]/CapacidadDelPaletEnBaldes) <= sum {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles} IdBaldeEnPalet[i,j,k];
subject to TotalDeBaldesEnFragmentos {(i,j) in IdBaldes}: sum{k in 1..NumeroDePaletsPosibles} BaldesDelIdBaldeEnPalet[i,j,k] = BaldesDelArticuloParaElCliente[i,j];
subject to CadaPaletNoDebeExcederse {k in 1..NumeroDePaletsPosibles}: sum{(i,j) in IdBaldes}BaldesDelIdBaldeEnPalet[i, j, k] <= CapacidadDelPaletEnBaldes;
subject to PaletEsUsadoParaIdBalde {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles}: BaldesDelIdBaldeEnPalet[i,j,k] / BaldesDelArticuloParaElCliente[i,j] <= IdBaldeEnPalet[i,j,k];
subject to NumeroDeCortesEnFuncionDeBaldes {(i,j) in IdBaldes}: sum{k in 1..NumeroDePaletsPosibles} BaldesDelIdBaldeEnPalet[i,j,k] >= BaldesDelArticuloParaElCliente[i,j];

# Calculo de BaldesEnMismoPalet (obtenido mediante la creación del AND lógico mediante constraints)
subject to CondicionPrimeraDelAND {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles, (l,m) in IdBaldes}: IdBaldeEnPalet[i,j,k] >= BaldesEnMismoPalet[i,j,l,m,k];
subject to CondicionSegundaDelAND {(i,j) in IdBaldes, (l,m) in IdBaldes, k in 1..NumeroDePaletsPosibles}: IdBaldeEnPalet[i,j,k] + IdBaldeEnPalet[l,m,k] - 1 <= BaldesEnMismoPalet[i,j,l,m,k];



# Solo pueden ir en un palet baldes compatibles: dos baldes están en el mismo palet si BaldesEnMismoPalet[i,j,k,l,m] = 1;
subject to BaldesCompatibles {k in 1..NumeroDePaletsPosibles}: sum{(i,j) in IdBaldes, (l,m) in IdBaldes: i<>l or j <> m} BaldeCompatible[i,j,l,m] * BaldesEnMismoPalet[i,j,l,m,k] = sum{(i,j) in IdBaldes} IdBaldeEnPalet[i,j,k];
# Solo pueden ir en un palet baldes de la misma sección
subject to SonBaldesDeLaMismaSeccion {k in 1..NumeroDePaletsPosibles}: sum{(i,j) in IdBaldes, (l,m) in IdBaldes: i<>l or j <> m} BaldesDeLaMismaSeccion[i,j,l,m] * BaldesEnMismoPalet[i,j,l,m,k] = sum{(i,j) in IdBaldes} IdBaldeEnPalet[i,j,k];
# Objetivo
minimize NumeroDeFragmentos: sum {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles} IdBaldeEnPalet[i,j,k];

solve;

printf '-----------------------------------------------\n';
for {k in 1..NumeroDePaletsPosibles, (i,j) in IdBaldes: BaldesDelIdBaldeEnPalet[i,j,k] > 0} printf 'Palet: %d, %s %s, Baldes: %d Tipo de Balde:%d Seccion:%d\n', k, i, j, BaldesDelIdBaldeEnPalet[i,j,k],TipoDeBalde[i,j], SeccionDelBalde[i,j];
printf '-----------------------------------------------\n';
display BaldesEnMismoPalet;

# Datos
data;
set IdBaldes := ('Cliente1', 'Articulo1'),
				('Cliente1', 'Articulo2'),
				('Cliente2', 'Articulo1'),
				('Cliente2', 'Articulo2'),
				('Cliente2', 'Articulo3');

param BaldesDelArticuloParaElCliente := ['Cliente1', 'Articulo1'] 140,
										['Cliente1', 'Articulo2'] 150,
										['Cliente2', 'Articulo1'] 10,
										['Cliente2', 'Articulo2'] 10,
										['Cliente2', 'Articulo3'] 50;

param TipoDeBalde := ['Cliente1', 'Articulo1'] 1,
					 ['Cliente1', 'Articulo2'] 1,
					 ['Cliente2', 'Articulo1'] 2,
					 ['Cliente2', 'Articulo2'] 2,
					 ['Cliente2', 'Articulo3'] 2;
					 
param SeccionDelBalde := ['Cliente1', 'Articulo1'] 2,
						['Cliente1', 'Articulo2'] 1,
						['Cliente2', 'Articulo1'] 2,
						['Cliente2', 'Articulo2'] 1,
						['Cliente2', 'Articulo3'] 2;

end;

