#*********************** Modelo ********************
# Basado en:
# Bin Packing with Fragmentable Items: Presentation and Approximations
# Bertrand Lecun, Thierry Mautor, Franck Quessette, Marc-Antoine Weisser
#
# Fragmentable Group and Item bin packing with Compatibility Preferences
# Aderemi Adeyemo, Victor O.Oladokun
#
# Definición
#
# Fragmentable Bin Packing Problem (FIBP): Es un Bin Packing Problem en el que cada item IdBaldes puede ser dividido en items más pequeños.
# Para nuestro modelo el item es el número de baldes para un Cliente-Articulo. Con esto conseguimos que el máimo número de baldes del mismo ClienteArticulo vaya en el mismo palet.
#
# Objetivo: Determinar el número mínimo de Palets de tamaño  en que se pueden fragmentar los BaldesDelArticuloParaElCliente minimizando  el número de fragmentos de items 
#
# Tenemos un número de items card(IdBaldes) donde cada IdBaldes tiene un número de baldes BaldesDelArticuloParaElCliente(IdBaldes)
# Tenemos un número de palets NumeroDePaletsPosibles, cada uno de ellos con una capacidad CapasDeBaldes;
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
param TiposDeBalde := 3;
param NumerosDeSecciones := 3;
param BaldesDelArticuloParaElCliente{(i,j) in IdBaldes};
param TipoDeBalde{(i,j) in IdBaldes};
param SeccionDelBalde{(i,j) in IdBaldes};
param LargoDelBalde{(i,j) in IdBaldes};
param AnchoDelBalde{(i,j) in IdBaldes};
param AltoDelBalde{(i,j) in IdBaldes};

set IdBaldesDeTipo{t in 1..TiposDeBalde} := setof{(i,j) in IdBaldes: TipoDeBalde[i,j] = t}(i,j);
set IdBaldesDeSeccion{t in 1..NumerosDeSecciones} := setof{(i,j) in IdBaldes: SeccionDelBalde[i,j] = t}(i,j);

param TotalDeIdBaldesDeTipo{(i,j) in IdBaldes, t in 1..TiposDeBalde} := card({(l,m) in IdBaldesDeTipo[t]:i=l and j=m});
param TotalDeIdBaldesDeSeccion{(i,j) in IdBaldes, t in 1..NumerosDeSecciones} := card({(l,m) in IdBaldesDeSeccion[t]:i=l and j=m});

param NumeroDePaletsPosibles := 360;
param CapasDeBaldes := 11;
param AlturaDelPalet := 1950;
param BaldesPorCapa := 4;
param CapacidadDelPaletEnBaldes := CapasDeBaldes * BaldesPorCapa;

#variables

var IdBaldeEnPalet{IdBaldes, 1..NumeroDePaletsPosibles}, binary;
var IdBaldeCompatibleEnPalet{IdBaldes, 1..NumeroDePaletsPosibles}, binary;
var IdBaldeMismaSeccionEnPalet{IdBaldes, 1..NumeroDePaletsPosibles}, binary;
var BaldesEnPalet{1..NumeroDePaletsPosibles} >= 0, integer;
var BaldesDelIdBaldeEnPalet{(i,j) in IdBaldes, 1..NumeroDePaletsPosibles} >= 0, integer;

#Restricciones generales del modelo
subject to MinimoNumeroDePalets: round(sum{(i,j) in IdBaldes} BaldesDelArticuloParaElCliente[i,j]/(CapasDeBaldes*BaldesPorCapa)) <= sum {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles} IdBaldeEnPalet[i,j,k];
subject to TotalDeBaldesEnFragmentos {(i,j) in IdBaldes}: sum{k in 1..NumeroDePaletsPosibles} BaldesDelIdBaldeEnPalet[i,j,k] = BaldesDelArticuloParaElCliente[i,j];
subject to CadaPaletNoDebeExcederse {k in 1..NumeroDePaletsPosibles}: sum{(i,j) in IdBaldes}BaldesDelIdBaldeEnPalet[i, j, k] <= CapasDeBaldes*BaldesPorCapa;
subject to LaSumaDeBaldesEsCoherente {k in 1..NumeroDePaletsPosibles}: sum{(i,j) in IdBaldes}BaldesDelIdBaldeEnPalet[i, j, k] = BaldesEnPalet[k];

subject to PaletEsUsadoParaIdBalde {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles}: BaldesDelIdBaldeEnPalet[i,j,k] / BaldesDelArticuloParaElCliente[i,j] <= IdBaldeEnPalet[i,j,k];
subject to NumeroDeCortesEnFuncionDeBaldes {(i,j) in IdBaldes}: sum{k in 1..NumeroDePaletsPosibles} BaldesDelIdBaldeEnPalet[i,j,k] >= BaldesDelArticuloParaElCliente[i,j];

# Los baldes deben ser del mismo tipo
subject to TodosLosIdBaldesDebenSerCompatibles {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles}: sum{t in 1..TiposDeBalde} TotalDeIdBaldesDeTipo[i,j,t] *  IdBaldeCompatibleEnPalet[i,j,k]  =  sum{(l,m) in IdBaldes}IdBaldeEnPalet[l,m,k];

# Los baldes deben ser de la misma seccion
subject to TodosLosIdBaldesDebenSerDeLaMismaSeccion {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles}: sum{t in 1..NumerosDeSecciones} TotalDeIdBaldesDeSeccion[i,j,t] *  IdBaldeMismaSeccionEnPalet[i,j,k]  =  sum{(l,m) in IdBaldes}IdBaldeEnPalet[l,m,k];


# Objetivo
minimize NumeroDeFragmentos: sum {(i,j) in IdBaldes, k in 1..NumeroDePaletsPosibles} IdBaldeEnPalet[i,j,k];
display IdBaldesDeTipo;
display TotalDeIdBaldesDeTipo;
solve;

#printf '-----------------------------------------------\n';
#for  {k in 1..NumeroDePaletsPosibles: BaldesEnPalet[k] > 0} printf '%d %d %d\n', k, sum{(i,j) in IdBaldes, t in 1..TiposDeBalde} TotalDeIdBaldesDeTipo[i,j,t] *  IdBaldeCompatibleEnPalet[i,j,k] , sum{(i,j) in IdBaldes}IdBaldeEnPalet[i,j,k];
printf '-----------------------------------------------\n';
for {k in 1..NumeroDePaletsPosibles, (i,j) in IdBaldes: BaldesDelIdBaldeEnPalet[i,j,k] > 0} printf 'Palet: %d, %s %s, Baldes: %d Tipo de Balde:%d Seccion:%d\n', k, i, j, BaldesDelIdBaldeEnPalet[i,j,k],TipoDeBalde[i,j], SeccionDelBalde[i,j];
printf '-----------------------------------------------\n';
display BaldesEnPalet;

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
					 ['Cliente1', 'Articulo2'] 2,
					 ['Cliente2', 'Articulo1'] 1,
					 ['Cliente2', 'Articulo2'] 2,
					 ['Cliente2', 'Articulo3'] 3;
					 
param SeccionDelBalde := ['Cliente1', 'Articulo1'] 2,
						['Cliente1', 'Articulo2'] 1,
						['Cliente2', 'Articulo1'] 2,
						['Cliente2', 'Articulo2'] 1,
						['Cliente2', 'Articulo3'] 2;
						
param LargoDelBalde := 	['Cliente1', 'Articulo1'] 595,
						['Cliente1', 'Articulo2'] 595,
						['Cliente2', 'Articulo1'] 595,
						['Cliente2', 'Articulo2'] 595,
						['Cliente2', 'Articulo3'] 595;

param AnchoDelBalde := 	['Cliente1', 'Articulo1'] 395,
						['Cliente1', 'Articulo2'] 395,
						['Cliente2', 'Articulo1'] 395,
						['Cliente2', 'Articulo2'] 395,
						['Cliente2', 'Articulo3'] 395;

param AltoDelBalde := 	['Cliente1', 'Articulo1'] 164,
						['Cliente1', 'Articulo2'] 164,
						['Cliente2', 'Articulo1'] 164,
						['Cliente2', 'Articulo2'] 164,
						['Cliente2', 'Articulo3'] 164;


end;

