#*********************** Modelo ********************
# Basado en A Linear Programming Approach for the Threea-Dimensional Bin-Packing Problem 
# Mhand Hifi*, Imed Kacem**, St´ephane N`egre*, LeiWu
#
# --------------- Lectura de Datos --------------*/

set Articulos dimen 1;
param CantidadDeBaldes{Articulos}, integer;
param TipoDeBalde{Articulos}, integer;
#param ArticuloDelBalde{DatosDeLosBaldes}, symbolic;
#param LargoDelBalde {card(DatosDeLosBaldes)}, integer;
#param AnchoDelBalde {card(DatosDeLosBaldes)}, integer;
#param AltoDelBalde {card(DatosDeLosBaldes)}, integer;
#param TipoDeBalde {card(DatosDeLosBaldes)}, integer;

table tin IN 'CSV' 'C:\gusek_0-2-19\gusek\Ped_Export_OPTIMIZADOR_3.csv' :
#Opcion ODBC
#table tin IN 'ODBC' 'DRIVER={Microsoft Text Driver (*.txt; *.csv)};Dbq=C:\gusek_0-2-19\gusek\' 'Ped_Export_OPTIMIZADOR_2.csv' :
Articulos <- [RECNO], CantidadDeBaldes ~ CantidadDeBaldes, TipoDeBalde ~ TipoDeBalde ;#,,CodigoArticuloDelCliente, LargoDelBalde,AnchoDelBalde,AltoDelBalde,TipoDeBalde];

set Baldes := setof{i in Articulos, j in 1..CantidadDeBaldes[i]}(i * 1000 + j);
printf "%d\n", card(Baldes);

# Conjuntos ------------------------------------------
param NumeroDeBaldes := card(Baldes);

# Declaraciones --------------------------------------

param AnchoDelPalet :=800, integer;
param LargoDelPalet :=1200, integer;
param AltoDelPalet :=1950, integer;
param LimiteSuperiorDePalets:=20;
param BaldeCompatible {i in Baldes, j in Baldes} := if TipoDeBalde[i] = TipoDeBalde[j] then 1 else 0, binary;
#param BaldesDeLaMismaSeccion {i in Baldes, j in Baldes} := if SeccionDelBalde[i] = SeccionDelBalde[j] then 1 else 0, binary;

# Variables de decision ------------------------------
var NumeroDePalets >= 0, integer;

var BaldeALaIzquierdaDelBalde {i in Baldes, j in Baldes}, binary;
var BaldeAbajoDelBalde {i in Baldes, j in Baldes}, binary;
var BaldeDetrasDelBalde {i in Baldes, j in Baldes}, binary;
var BaldeEnPaletPrevioABalde {i in Baldes, j in Baldes}, binary;
# Restricciones --------------------------------------
# Todo par de baldes: o está en el mismo palet, o está en un palet previo o está en un palet posterior.
subject to BaldesNoSuperpuestos {i in Baldes, j in Baldes: j > i}: BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i] + BaldeEnPaletPrevioABalde[i,j] + BaldeEnPaletPrevioABalde[j,i] = 1;
# Solo pueden ir en un palet baldes compatibles
#subject to BaldesCompatibles {(a,b) in Articulos, (c,d) in Articulos}: (BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i]) * BaldeCompatible[i,j] + BaldeEnPaletPrevioABalde[i,j] + BaldeEnPaletPrevioABalde[j,i] = 1;
# Solo pueden ir en un palet baldes de la misma sección
#subject to BaldesSonDeLaMismaSeccion {i in Baldes, j in Baldes: i > j}: (BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i])  * BaldesDeLaMismaSeccion[i,j] + BaldeEnPaletPrevioABalde[i,j] + BaldeEnPaletPrevioABalde[j,i] = 1;

# Objetivo -------------------------------------------
minimize NumeroDePaletsAPreparar: NumeroDePalets;

end;

