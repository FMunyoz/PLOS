/*********************** Modelo ********************/
/* ------------------ Declaraciones ---------------*/
param NumeroDeBaldes > 0, integer;
param VolumenDelPalet > 0, integer;

/*             Conjuntos                                     */
set Baldes :=1..NumeroDeBaldes;
set Palets :=1..NumeroDeBaldes;
set EjesDelBalde := {"x","y","z"};
set Ejes := {"x","y","z"};

/*             Parámetros de entrada                   */

param DimensionXDelBalde {i in Baldes}> 0, integer;



/*             Variables de decision                     */
var SeUsaPalet {i in Palets}, binary;
var BaldeVaEnElPalet {i in Baldes, j in Palets}, binary;
var BaldeAlineadoEnPalet {i in Baldes, j in EjesDelBalde, k in Ejes}, binary;


/* -------------Declaración Funcional ------------*/
/*                 Restricciones                            */
# Ortogonalidad: Los lados de los baldes deben ubicarse paralelo a uno y solo uno de los ejes. 
subject to CadaBaldeDebeIrAlineado{i in Baldes, j in EjesDelBalde}: sum{k in Ejes} BaldeAlineadoEnPalet[i, j, k] = 1;
subject to CadaBaldeDebeIrAlineadoAUnSoloEje {i in Baldes, k in Ejes}: sum{j in EjesDelBalde} BaldeAlineadoEnPalet[i, j, k] = 1;
# Dominio: todos los vértices del balde deben estar dentro del palet

# No  intersección: Los baldes no se pueden superponer.
	
#No se debe exceder el volumen de los palets
subject to NoExcederVolumen{j in Palets}: sum {i in Baldes} DimensionXDelBalde[j] * BaldeVaEnElPalet[i,j] <= VolumenDelPalet * SeUsaPalet[j];

/*                Función objetivo                         */
minimize NumeroDePalets: sum {i in Palets} SeUsaPalet[i];

display{i in Baldes, j in Palets}: BaldeVaEnElPalet[i,j];

/*                Salida                                       */
# Datos
#
data;
param NumeroDeBaldes := 3;
param VolumenDelPalet := 1872000;
param DimensionXDelBalde := 1 20000, 2 500000, 3 200000;
end;
