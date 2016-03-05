#*********************** Modelo ********************
# Basado en:
# Bin Packing with Fragmentable Items: Presentation and Approximations
# Bertrand Lecun, Thierry Mautor, Franck Quessette, Marc-Antoine Weisser
#
# Fragmentable Group and Item bin packing with Compatibility Preferences
# Aderemi Adeyemo, Victor O.Oladokun
#
# Definición
#-----------------------------------
# Fragmentable Bin Packing Problem (FIBP): Es un Bin Packing Problem en el que cada item Items puede ser dividido en items más pequeños.
# Para nuestro modelo el item es el número de baldes para un Cliente-Articulo. Con esto conseguimos que el máimo número de baldes del mismo ClienteArticulo vaya en el mismo palet.
#
# Objetivo: Determinar el número mínimo de Palets en que se pueden fragmentar los BaldesDelItem minimizando  el número de fragmentos de items 
#
# Tenemos un número de items card(Items) donde cada Item tiene un número de baldes BaldesDelItem(Items)
# Tenemos un número de palets NumeroDePaletsPosibles, cada uno de ellos con una capacidad CapacidadDelPaletEnBaldes
#
# Ademas, considermos que el tamaño total de los items es inferior a la capacidad total de los palets
# 
# Mínimo número de palets:  aquellos que, por la capacidad, permiten poner el total de baldes.
#
# Restricciones generales
#
#  TotalDeBaldesEnFragmentos: Para cada item  Cliente-Articulo (Items), la suma de Baldes de todos los palets debe ser igual número de baldes del Items, es decir, todos los baldes deben estar repartidos entre los palets.
#  CadaPaletNoDebeExcederse: Para todo palet, La suma de baldes en cada palet debe ser menor o igual a la capacidad (número de baldes) del palet.
#  PaletEsUsadoParaItem: Un palet es usado para el item Item si algun balde de Item es puesto en el Palet.
#
#Restricciones  de Campofrío
#
# BaldesCompatibles: Todos los baldes del palet deben ser compatibles (del mismo TipoDeBalde). 
# Todos los baldes del palet dben ser de la misma sección.
#
# Modelo
# -------------------------------------------------------------
# Parametros independientes
# 
param CapasDeBaldes := 8;
param AltoDelPalet := 1950;
param AnchoDelPalet := 800;
param LargoDelPalet := 1200;
param ColumnasPorPalet := 4;

param BigM :=2;

param CapacidadDelPaletEnBaldes := CapasDeBaldes * ColumnasPorPalet;

# Conjuntos

set Items dimen 2;

# Parámetros Dependientes del conjunto
param BaldesDelItem{(i,j) in Items};
param TipoDeBalde{(i,j) in Items};

param LargoDelBalde{(i,j) in Items};
param AnchoDelBalde{(i,j) in Items};
param AltoDelBalde{(i,j) in Items};

#Lectura de datos

table tin IN 'CSV' 'C:\gusek_0-2-19\gusek\Modelos\PED_Export_OPTIMIZADOR_DiaG4.csv' :
Items <- [NombreDeGrupo, ArticuloDelBalde], BaldesDelItem ~ CantidadDeBaldes, TipoDeBalde ~ TipoDeBalde, AltoDelBalde, AnchoDelBalde, LargoDelBalde;

# Conjuntos a partir de los datos leidos

set TiposDeBalde:= setof{(i,j) in Items} TipoDeBalde[i,j];
set Secciones:= setof{(i,j) in Items} substr(i, 2,1);
set ItemsDeTipo{t in TiposDeBalde} := setof{(i,j) in Items: TipoDeBalde[i,j] = t}(i,j);
set ItemsDeSeccion{s in Secciones} := setof{(i,j) in Items: substr(i,2,1) = s}(i,j);

param NumeroDePaletsPosibles :=100;
param NumeroDeSecciones := card(Secciones);

param TotalDeItemsDeTipo{(i,j) in Items, t in TiposDeBalde} := card({(l,m) in ItemsDeTipo[t]:i=l and j=m});
param TotalDeItemsDeSeccion{(i,j) in Items, s in Secciones} := card({(l,m) in ItemsDeSeccion[s]:i=l and j=m});
display TiposDeBalde;

display Items;
display ItemsDeTipo;
display TiposDeBalde;

#variables

var PaletUsado{1..NumeroDePaletsPosibles}, binary;
var ItemEnPalet{Items, 1..NumeroDePaletsPosibles}, binary;
var TipoEstaEnPalet{TiposDeBalde, 1..NumeroDePaletsPosibles}, binary;
var SeccionEstaEnPalet{Secciones, 1..NumeroDePaletsPosibles}, binary;
var BaldesEnColumnaDelPalet{1..CapasDeBaldes, 1..NumeroDePaletsPosibles} >= 0, integer;
var BaldesDelItemEnColumnaDelPalet{c in 1..ColumnasPorPalet, (i,j) in Items, 1..NumeroDePaletsPosibles} >= 0, integer;

#Restricciones generales del modelo

# Para cada item, el total de baldes repartidos en columnas en los palets debe ser igual al total de baldes del item para el cliente. Los baldes de un item deben ser repartidos entre todos los palets.
subject to II_TotalDeBaldesEnFragmentos {(i,j) in Items}: sum{c in 1..ColumnasPorPalet, k in 1..NumeroDePaletsPosibles} BaldesDelItemEnColumnaDelPalet[c,i,j,k] = BaldesDelItem[i,j];

# Cuando el item (i,j) se encuentra en alguna columna del palet k entonces el item está en el palet.
subject to IV_ElItemEstaEnElPalet {(i,j) in Items, k in 1..NumeroDePaletsPosibles}: sum{c in 1..ColumnasPorPalet}(BaldesDelItemEnColumnaDelPalet[c,i,j,k])/BaldesDelItem[i,j] <= ItemEnPalet[i,j,k];

# Todo item debe estar en algún palet
subject to _4_TodoItemEnAlgunPalet{(i,j) in Items}: sum{k in 1..NumeroDePaletsPosibles} ItemEnPalet[i,j,k] >= 1;

#Restricciones de capacidad del palet. 

#Cada palet no debe excederse
subject to III_CadaPaletNoDebeExcederse {k in 1..NumeroDePaletsPosibles}: sum{c in 1..ColumnasPorPalet, (i,j) in Items}BaldesDelItemEnColumnaDelPalet[c, i, j, k] <= CapasDeBaldes*ColumnasPorPalet;
#Cada columna no debe excederse
subject to IIIa_CadaColumnaDelPaletNoDebeExcederse {c in 1..ColumnasPorPalet, k in 1..NumeroDePaletsPosibles}: sum{(i,j) in Items}(BaldesDelItemEnColumnaDelPalet[c, i, j, k] * AltoDelBalde[i,j]) <= AltoDelPalet;


#Restricciones de coherencia del palet
subject to LaSumaDeBaldesEsCoherente {k in 1..NumeroDePaletsPosibles}: sum{c in 1..ColumnasPorPalet, (i,j) in Items}BaldesDelItemEnColumnaDelPalet[c, i, j, k] = sum{c in 1..CapasDeBaldes}BaldesEnColumnaDelPalet[c, k];
subject to LaSumaDeBaldesEnColumnaEsCoherente {c in 1..ColumnasPorPalet, k in 1..NumeroDePaletsPosibles}: sum{(i,j) in Items}BaldesDelItemEnColumnaDelPalet[c, i, j, k] = BaldesEnColumnaDelPalet[c, k];

subject to PaletEsUsadoParaItem {(i,j) in Items, k in 1..NumeroDePaletsPosibles}: sum{c in 1..ColumnasPorPalet}BaldesDelItemEnColumnaDelPalet[c,i,j,k] / BaldesDelItem[i,j] <= ItemEnPalet[i,j,k];
subject to NumeroDeCortesEnFuncionDeBaldes {(i,j) in Items}: sum{c in 1..ColumnasPorPalet, k in 1..NumeroDePaletsPosibles} BaldesDelItemEnColumnaDelPalet[c,i,j,k] >= BaldesDelItem[i,j];

# Los baldes deben ser del mismo tipo. Para ello se usa la técnica de Big M.
subject to ActivaTipoEstaEnPalet{tb in TiposDeBalde, (i,j) in ItemsDeTipo[tb], k in 1..NumeroDePaletsPosibles}: TipoEstaEnPalet[tb, k] >= 1 - BigM * (1 - ItemEnPalet[i,j,k]);
# Los baldes deben ser de la misma sección. Para ello se usa la técnica de Big M.
subject to ActivaSeccionEstaEnPalet{s in Secciones, (i,j) in ItemsDeSeccion[s], k in 1..NumeroDePaletsPosibles}: SeccionEstaEnPalet[s, k] >= 1 - BigM * (1 - ItemEnPalet[i,j,k]);

# Para cualquier item y cualquier palet, la suma para todos los tipos de ... es igual al total de Items en el palet.
subject to TodosLosItemsDebenSerCompatibles {k in 1..NumeroDePaletsPosibles}: sum{tb in TiposDeBalde} TipoEstaEnPalet[tb, k] <= 1;

# Los baldes deben ser de la misma seccion
subject to TodosLosItemsDebenSerDeLaMismaSeccion {k in 1..NumeroDePaletsPosibles}: sum{s in Secciones} SeccionEstaEnPalet[s, k] <= 1;

# Si el algún balde está en el palet entonces el palet es usado
subject to PaletUsadoEnLaSolucion {k in 1..NumeroDePaletsPosibles, (i,j) in Items}: PaletUsado[k]>=ItemEnPalet[i,j,k];

# El minimo de palets debe ser al menos la capacidad de baldes en palets
subject to MinimoNumeroDePalets: sum {k in 1..NumeroDePaletsPosibles} PaletUsado[k] >= NumeroDeSecciones;
subject to MinimoNuemroDePalets: sum {k in 1..NumeroDePaletsPosibles} PaletUsado[k] >= sum{(i,j) in Items} (AnchoDelBalde[i,j]*AltoDelBalde[i,j]*LargoDelBalde[i,j])/(AnchoDelPalet*AltoDelPalet*LargoDelPalet);

# Objetivo
minimize NumeroDePalets: sum {k in 1..NumeroDePaletsPosibles} PaletUsado[k];
#minimize NumeroDeFragmentos: sum {(i,j) in Items, k in 1..NumeroDePaletsPosibles} ItemEnPalet[i,j,k];


solve;
display {(i,j) in Items, k in 1..NumeroDePaletsPosibles: ItemEnPalet[i,j,k]>0}ItemEnPalet[i,j,k];
#display {c in 1..ColumnasPorPalet, (i,j) in Items, k in 1..NumeroDePaletsPosibles:BaldesDelItemEnColumnaDelPalet[c,i,j,k]>0}BaldesDelItemEnColumnaDelPalet[c,i,j,k];
#display {(i,j) in Items, k in 1..NumeroDePaletsPosibles:ItemEnPalet[i,j,k]>0 }ItemEnPalet[i,j,k];
table Salida {k in 1..NumeroDePaletsPosibles, c in 1..ColumnasPorPalet, (i,j) in Items: BaldesDelItemEnColumnaDelPalet[c,i,j,k] > 0} OUT "CSV" "C:\gusek_0-2-19\gusek\Modelos\TRMOSAICO_DiaG4.csv":
k, i, j, BaldesDelItemEnColumnaDelPalet[c,i,j,k], c;
printf '-----------------------------------------------\n';
for {k in 1..NumeroDePaletsPosibles, c in 1..ColumnasPorPalet, (i,j) in Items: BaldesDelItemEnColumnaDelPalet[c,i,j,k] > 0} printf 'Palet: %d Columna: %d, %s %s, Baldes: %d Tipo de Balde:%d Seccion:%s\n', k, c, i, j, BaldesDelItemEnColumnaDelPalet[c,i,j,k],TipoDeBalde[i,j], substr(i,2,1);
printf '-----------------------------------------------\n';
end;

