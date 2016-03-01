/*********************** Modelo ********************/
# Basado en A Linear Programming Approach for the Three-Dimensional Bin-Packing Problem 
# Mhand Hifi*, Imed Kacem**, St´ephane N`egre*, LeiWu
#
# Mejorado obteniendo un límite inferior (lower bound) basado en desigualdades válidas (valid inequalities)
/* ------------------ Declaraciones ---------------*/
param AnchoDelPalet > 0, integer;
param LargoDelPalet > 0, integer;
param AltoDelPalet > 0, integer;
param NumeroDeBaldes > 0, integer;

/*             Conjuntos                                     */
set Baldes :=1..NumeroDeBaldes;
set Palets :=1..NumeroDeBaldes;


/*             Parámetros de entrada                   */

param AnchoDelBalde {i in Baldes} > 0, integer;
param LargoDelBalde {i in Baldes} > 0, integer;
param AltoDelBalde {i in Baldes} > 0, integer;
param PesoFicticio{i in Baldes} := 5;

/*             Variables de decision                     */
var NumeroDePalets >= 0, integer;
var PaletDelBalde {i in Baldes} >= 1, integer;
var BaldeALaIzquierdaDelBalde {i in Baldes, j in Baldes}, binary;
var BaldeAbajoDelBalde {i in Baldes, j in Baldes}, binary;
var BaldeDetrasDelBalde {i in Baldes, j in Baldes}, binary;
var BaldeEnPaletPrevioABalde {i in Baldes, j in Baldes}, binary;
var CoordenadaXDelBalde {i in Baldes}, >= 0, integer;
var CoordenadaYDelBalde {i in Baldes}, >= 0, integer;
var CoordenadaZDelBalde {i in Baldes}, >= 0, integer;

/* -------------Declaración Funcional ------------*/
/*                 Restricciones                            */

# No  intersección: Los baldes no se pueden superponer.
subject to BaldesNoSuperpuestos {i in Baldes, j in Baldes: j > i}: BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i] + BaldeEnPaletPrevioABalde[i,j] + BaldeEnPaletPrevioABalde[j,i] = 1;
subject to NoSeExcedeElAnchoDelPalet {i in Baldes, j in Baldes: i <> j}: CoordenadaXDelBalde[i] - CoordenadaXDelBalde[j] + AnchoDelPalet * (BaldeALaIzquierdaDelBalde[i,j] - BaldeEnPaletPrevioABalde[i,j] - BaldeEnPaletPrevioABalde[j,i]) <=  AnchoDelPalet - AnchoDelBalde[i];
subject to NoSeExcedeElLargoDelPalet {i in Baldes, j in Baldes: i <> j}: CoordenadaYDelBalde[i] - CoordenadaYDelBalde[j] + LargoDelPalet * (BaldeDetrasDelBalde[i,j] - BaldeEnPaletPrevioABalde[i,j] - BaldeEnPaletPrevioABalde[j,i]) <=  LargoDelPalet - LargoDelBalde[i];
subject to NoSeExcedeElAltoDelPalet {i in Baldes, j in Baldes: i <> j}: CoordenadaZDelBalde[i] - CoordenadaZDelBalde[j] + AltoDelPalet * (BaldeAbajoDelBalde[i,j] - BaldeEnPaletPrevioABalde[i,j] - BaldeEnPaletPrevioABalde[j,i]) <=  AltoDelPalet - AltoDelBalde[i];
# Garantiza que un balde está en el mismo palet o no. Entender que es el valor label of the bin.
subject to SiBaldeEstaEnElMismoPaletDebeTenerAlgunBaldeAlLado {i in Baldes, j in Baldes: i <> j}: (NumeroDeBaldes - 1) * (BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i]) + PaletDelBalde[i] - PaletDelBalde[j] + NumeroDeBaldes * BaldeEnPaletPrevioABalde[i,j] <= NumeroDeBaldes - 1;
# No se sale el balde del palet
subject to CoordenadaXDelBaldeEstaEnElPalet {i in Baldes}: 0 <= CoordenadaXDelBalde[i] <= AnchoDelPalet - AnchoDelBalde[i];
subject to CoordenadaYDelBaldeEstaEnElPalet {i in Baldes}: 0 <= CoordenadaYDelBalde[i] <= LargoDelPalet - LargoDelBalde[i];
subject to CoordenadaZDelBaldeEstaEnElPalet {i in Baldes}: 0 <= CoordenadaZDelBalde[i] <= AltoDelPalet - AltoDelBalde[i];
subject to ElPaletAsignadoDebeSerUnoDeLosSeleccionados {i in Baldes}: NumeroDePalets >= PaletDelBalde[i];
subject to ElNumeroDePaletsDebeNoExcedeElNumeroDeBaldes: NumeroDePalets <= NumeroDeBaldes;
subject to NumeroMaximoDePalets {i in Baldes}:  PaletDelBalde[i] <= NumeroDePalets;

#Restricción lower bound de Eastman (relacionada con el problema de agenda de trabajo en máquinas paralelas)
subject to LowerBoundDeEastmanX: sum {i in Baldes} PesoFicticio[i] * AltoDelBalde[i]* LargoDelBalde[i] * (CoordenadaXDelBalde[i] + AnchoDelBalde[i] + (PaletDelBalde[i]-1) * AnchoDelPalet >= 1/AltoDelPalet*AnchoDelPalet * sum{i in Baldes} PesoFicticio[i] * (AlturaDelBalde[i]* LargoDelPalet * sum{j in i-1} (AnchoDelBalde[j]*AltoDelBalde[j]*LargoDelBalde[j] + sum{k in AltoDelBalde[i]*AnchoDelBalde[i]} k * AnchoDelBalde[i])) + (AltoDelPalet * AnchoDelPalet - 1)/ (2 * AltoDelPalet * AnchoDelPalet) * sum {i in Baldes} PesoFicticio[i] * AnchoDelBalde[i]*AltoDelBalde[i]*LargoDelBalde[i];
/*                Función objetivo                         */
minimize NumeroDePaletsAPreparar: NumeroDePalets;

# Datos
#
data;
param NumeroDeBaldes := 10;
param AnchoDelPalet  := 800;
param LargoDelPalet  := 1200;
param AltoDelPalet   :=  1950;
param AnchoDelBalde  := 1 297 2 395 3 297 4 395 5 297 6 395 7 395 8 395 9 297 10 297;
param LargoDelBalde  := 1 395 2 595 3 395 4 595 5 395 6 595 7 595 8 595 9 395 10 395;
param AltoDelBalde   := 1 151 2 112 3 151 4 164 5 151 6 164 7 112 8 112 9 151 10 151;

end;
