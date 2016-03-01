/*********************** Modelo ********************/
# Basado en A Linear Programming Approach for the Three-Dimensional Bin-Packing Problem 
# Mhand Hifi*, Imed Kacem**, St´ephane N`egre*, LeiWu
#
/* ------------------ Declaraciones ---------------*/
param NumeroDeBaldes > 0, integer;
param AnchoDelPalet :=800, integer;
param LargoDelPalet :=1200, integer;
param AltoDelPalet :=1950, integer;
param LimiteSuperiorDePalets:=20;

/*             Conjuntos                                     */
set Baldes :=1..NumeroDeBaldes;
set Palets :=1..LimiteSuperiorDePalets;

/*             Parámetros de entrada                   */
param ArticuloDelBalde {Baldes}, symbolic;
param SeccionDelBalde {Baldes} , integer;
param Secciones := 4;
param TiposDeBalde {Baldes}, integer;
param TipoDeBalde {i in Baldes}:= TiposDeBalde[i] - 1, binary;
param AnchoDelBalde {Baldes} > 0, integer;
param LargoDelBalde {i in Baldes} > 0, integer;
param AltoDelBalde {i in Baldes} > 0, integer;
param LimiteInferiorDePalets := sum{i in Baldes} round((AnchoDelBalde[i] * AltoDelBalde[i] * LargoDelBalde[i]) / (AnchoDelPalet * AltoDelPalet * LargoDelPalet)) + 1, integer;
param BaldeCompatible {i in Baldes, j in Baldes} := if TipoDeBalde[i] = TipoDeBalde[j] then 1 else 0, binary;
param BaldesDeLaMismaSeccion {i in Baldes, j in Baldes} := if SeccionDelBalde[i] = SeccionDelBalde[j] then 1 else 0, binary;
# param BaldeDelMismoArticulo {i in Baldes, j in Baldes} := if ArticuloDelBalde[i] = ArticuloDelBalde[j] then 1 else 0, binary;

display LimiteInferiorDePalets;
display LimiteSuperiorDePalets;


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
subject to NoSeExcedeElAnchoDelPalet {i in Baldes, j in Baldes: j <> i}: CoordenadaXDelBalde[i] - CoordenadaXDelBalde[j] + AnchoDelPalet * (BaldeALaIzquierdaDelBalde[i,j] - BaldeEnPaletPrevioABalde[i,j] - BaldeEnPaletPrevioABalde[j,i]) <=  AnchoDelPalet - AnchoDelBalde[i];
subject to NoSeExcedeElLargoDelPalet {i in Baldes, j in Baldes: j <> i}: CoordenadaYDelBalde[i] - CoordenadaYDelBalde[j] + LargoDelPalet * (BaldeDetrasDelBalde[i,j] - BaldeEnPaletPrevioABalde[i,j] - BaldeEnPaletPrevioABalde[j,i]) <=  LargoDelPalet - LargoDelBalde[i];
subject to NoSeExcedeElAltoDelPalet {i in Baldes, j in Baldes: j <> i}: CoordenadaZDelBalde[i] - CoordenadaZDelBalde[j] + AltoDelPalet * (BaldeAbajoDelBalde[i,j] - BaldeEnPaletPrevioABalde[i,j] - BaldeEnPaletPrevioABalde[j,i]) <=  AltoDelPalet - AltoDelBalde[i];
# Garantiza que un balde está en el mismo palet o no. 
subject to SiBaldeEstaEnElMismoPaletDebeTenerAlgunBaldeAlLado {i in Baldes, j in Baldes: i <> j}: (LimiteSuperiorDePalets - 1) * (BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i]) + PaletDelBalde[i] - PaletDelBalde[j] + (LimiteSuperiorDePalets * BaldeEnPaletPrevioABalde[i,j]) <= (LimiteSuperiorDePalets - 1);
# No se sale el balde del palet
subject to CoordenadaXDelBaldeEstaEnElPalet {i in Baldes}: 0<= CoordenadaXDelBalde[i] <= AnchoDelPalet - AnchoDelBalde[i];
subject to CoordenadaYDelBaldeEstaEnElPalet {i in Baldes}: 0<= CoordenadaYDelBalde[i] <= LargoDelPalet - LargoDelBalde[i];
subject to CoordenadaZDelBaldeEstaEnElPalet {i in Baldes}: 0<= CoordenadaZDelBalde[i] <= AltoDelPalet - AltoDelBalde[i];
subject to ElNumeroDePaletsDebeNoExcedeElLimiteSuperior: NumeroDePalets <= LimiteSuperiorDePalets;
subject to NumeroMaximoDePalets {i in Baldes}:  PaletDelBalde[i] <= NumeroDePalets;


# Al menos el numero de palets debe ser el volumen de los baldes
subject to NumeroMiniDePaletsPorVolumen {i in Baldes}: LimiteInferiorDePalets <= PaletDelBalde[i];
# Al menos el numero de palets debe ser el número de sercciones
subject to NumeroMiniDePaletsPorSeccion {i in Baldes}: Secciones <= PaletDelBalde[i];

# Solo pueden ir en un palet baldes compatibles
subject to BaldesCompatibles {i in Baldes, j in Baldes: j > i}: (BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i]) * BaldeCompatible[i,j] + BaldeEnPaletPrevioABalde[i,j] + BaldeEnPaletPrevioABalde[j,i] = 1;
# Solo pueden ir en un palet baldes de la misma sección
subject to BaldesSonDeLaMismaSeccion {i in Baldes, j in Baldes: i > j}: (BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i])  * BaldesDeLaMismaSeccion[i,j] + BaldeEnPaletPrevioABalde[i,j] + BaldeEnPaletPrevioABalde[j,i] = 1;

minimize NumeroDePaletsAPreparar: NumeroDePalets;

# Datos
#
data;
#param ArticuloDelBalde:= 1 "Articulo1" 2 "Articulo2" 3 "Articulo3" 4 "Articulo3";
#param SeccionDelBalde:= 1 "Seccion1" 2 "Seccion1" 3 "Seccion1" 4 "Seccion1";
#param TipoDeBalde := 1 "Tipo1" 2 "Tipo1" 3 "Tipo1" 4 "Tipo4";
param NumeroDeBaldes := 20;
#param AnchoDelBalde  := 1 297 2 395 3 297 4 800;
#param LargoDelBalde  := 1 395 2 595 3 395 4 1200;
#param AltoDelBalde   := 1 151 2 112 3 151 4 1950;
param SeccionDelBalde:= 1 3 2 3 3 3 4 1 5 3 6 1 7 1 8 1 9 4 10 4 11 6 12 3 13 2 14 2 15 4 16 5 17 5 18 3 19 3 20 1;# 21 1 22 2 23 2 24 3 25 7 26 7 27 7 28 5 29 7 30 1 31 1 32 1 33 1 34 1 35 2 36 5 37 5 38 5 39 5 40 5 41 5 42 1 43 2 44 3 45 3 46 7 47 5 48 1 49 3 50 1;

param TiposDeBalde := 1 2 2 1 3 2 4 1 5 2 6 1 7 1 8 1 9 2 10 2 11 2 12 2 13 1 14 2 15 2 16 1 17 1 18 1 19 1 20 1;# 21 1 22 1 23 1 24 2 25 2 26 2 27 2 28 1 29 2 30 1 31 2 32 2 33 2 34 1 35 1 36 1 37 1 38 1 39 1 40 1 41 1 42 1 43 2 44 1 45 2 46 1 47 1 48 1 49 1 50 1;

param ArticuloDelBalde:= 1 '11062-1/3 LOMO CINTA C.E VACIO' 2 '11063-COSTILLAR VACIO' 3 '11093-SOLOMILLO VACIO 4 UND' 4 '11792-COSTILLA CHURRASCO NATUR BASIC' 5 '11799-SOLOMILLO VACIO GENERICO' 6 '11917-COSTILLA TROZO C.E. BAND.' 7 '11936-ESTOFADO C.E. 750 GR. BAND.' 8 '11996-FILETE LOMO FINO 300 NATUR BAN' 9 '12102-BURGUERMEAT VACUNO 400 GR.BAND' 10 '12103-BURGUERMEAT VACUNO 800 GR.C.E.' 11 '12141-BROCHETA ADOBADA 320 GR. BAND.' 12 '12165-SOLOMILLO VACIO GENER. PVP2' 13 '12167-COSTILLA' 14 '12168-AGUJA CERDO C/H' 15 '12178-CARNE PICADA DE TERNERA 400 GR' 16 '12195-PECHUGA PAVO ADOBADA 350 GR. B' 17 '12196-PECHUGA PAVO FINAS HIERBAS 350' 18 '12209-LOMO FRESCO VACIO' 19 '12244-CODILLO DE JAMON VACIO' 20 '12246-12-14 CHULETAS LOMO BAND.';# 21 '12248-FILETE JAMON BAND.' 22 '20051-PANCETA CON COSTILLA' 23 '20109-TIRA DE COSTILLA' 24 '20126-COSTILLA ADOBADA IBERICA VACIO' 25 '20158-SOLOMILLO IBERICO VACIO' 26 '20159-PRESA IBERICA VACIO' 27 '20160-SECRETO IBERICO VACIO' 28 '20495-CHULETA SAJONIA' 29 '20514-LOMO IBERICO BAND.' 30 '20543-ESCALOPE JAMON FINO 300 GR.BAN' 31 '20605-LOMO TROZO FILETEADO NATUR BAN' 32 '20608-CHULETA LOMO 6UN NATUR BAND.' 33 '20609-SECRETO NATUR BAND.' 34 '20611-FILETE BACON NATUR BAND.' 35 '20625-CENTRO SIN SOLOMILLO' 36 '20672-LOMO ADOBADO 300 GR. SKIN' 37 '20673-LOMO ADOBADO SKIN 500 GR.' 38 '20674-LOMO AJILLO 300 GR. SKIN' 39 '20700-MAGRO ADOB.300 GR. BAND.' 40 '20701-LOMO SAJONIA .300 GR. BAND.' 41 '20702-LOMO ADOB. HORNO 300 GR. BAND.' 42 '20714-CHULETA AGUJA C.E. BAND.' 43 '20725-CODILLO JAMON SIN PIEL' 44 '20735-JAMON 3D S/H  VACIO' 45 '20738-SECRETO VACIO' 46 '20743-CHULETERO S/C IBERICO' 47 '20777-CHULETA SAJONIA BAND.' 48 '20819-FILETE AGUJA NATUR 400 GR. BAN' 49 '20912-CARRILLADAS VACIO' 50 '20923-ESCAL.JAMON SIEMPRE TIERNO 275';

param AnchoDelBalde := 1 297 2 395 3 297 4 395 5 297 6 395 7 395 8 395 9 297 10 297 11 297 12 297 13 395 14 297 15 297 16 395 17 395 18 395 19 395 20 395; # 21 395 22 395 23 395 24 297 25 297 26 297 27 297 28 395 29 297 30 395 31 297 32 297 33 297 34 395 35 395 36 395 37 395 38 395 39 395 40 395 41 395 42 395 43 297 44 395 45 297 46 395 47 395 48 395 49 395 50 395;
param LargoDelBalde := 1 395 2 595 3 395 4 595 5 395 6 595 7 595 8 595 9 395 10 395 11 395 12 395 13 595 14 395 15 395 16 595 17 595 18 595 19 595 20 595;# 21 595 22 595 23 595 24 395 25 395 26 395 27 395 28 595 29 395 30 595 31 395 32 395 33 395 34 595 35 595 36 595 37 595 38 595 39 595 40 595 41 595 42 595 43 395 44 595 45 395 46 595 47 595 48 595 49 595 50 595;
param AltoDelBalde := 1 151 2 112 3 151 4 164 5 151 6 164 7 112 8 112 9 151 10 151 11 151 12 151 13 164 14 151 15 151 16 112 17 112 18 112 19 164 20 164;# 21 112 22 112 23 164 24 151 25 151 26 151 27 151 28 164 29 151 30 112 31 151 32 151 33 151 34 164 35 230 36 112 37 112 38 112 39 112 40 112 41 112 42 164 43 151 44 164 45 151 46 164 47 112 48 164 49 164 50 164;

end;
