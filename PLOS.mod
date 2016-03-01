/*********************** Modelo ********************/
/* ------------------ Declaraciones ---------------*/
param NumeroDeBaldes > 0, integer;
param VolumenDelPalet > 0, integer;
/*             Conjuntos                                     */
set Baldes :=1..NumeroDeBaldes;
set Palets :=1..NumeroDeBaldes;
/*             Parámetros de entrada                   */

param DimensionDelBalde {i in Baldes}> 0, integer;

/*             Variables de decision                     */
var SeUsaPalet {i in Palets}, binary;
var PaletLlevaElBalde {i in Palets, j in Baldes}, binary;
/* -------------Declaración Funcional ------------*/
/*                 Restricciones                            */
#Cada balde debe ir en un palet
subject to CadaBaldeDebeIrEnUnPalet{j in Baldes}: sum{i in Palets} PaletLlevaElBalde[i,j] = 1;
#No se debe exceder el volumen de los palets
subject to NoExcederVolumen{i in Palets}: sum {j in Baldes} DimensionDelBalde[j] * PaletLlevaElBalde[i,j] <= VolumenDelPalet * SeUsaPalet[i];

/*                Función objetivo                         */
minimize NumeroDePalets: sum {i in Palets} SeUsaPalet[i];

display{i in Palets, j in Baldes}: PaletLlevaElBalde[i,j];

/*                Salida                                       */
# Datos
#
data;
param NumeroDeBaldes := 3;
param VolumenDelPalet := 1872000;
param DimensionDelBalde := 1 20000, 2 500000, 3 200000;
end;
