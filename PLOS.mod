/*********************** Modelo ********************/
# Basado en A Linear Programming Approach for the Three-Dimensional Bin-Packing Problem 
# Mhand Hifi*, Imed Kacem**, St´ephane N`egre*, LeiWu
#
/* ------------------ Declaraciones ---------------*/
param NumeroDeBaldes > 0, integer;
param AnchoDelPalet :=800, integer;
param LargoDelPalet :=1200, integer;
param AltoDelPalet :=1950, integer;
param LimiteSuperiorDePalets:=12;

/*             Conjuntos                                     */
set Baldes :=1..NumeroDeBaldes;
set Palets :=1..LimiteSuperiorDePalets;

/*             Parámetros de entrada                   */
param ArticuloDelBalde {Baldes}, symbolic;
param SeccionDelBalde {Baldes} , symbolic;
param TipoDeBalde {Baldes}, symbolic;
param AnchoDelBalde {Baldes} > 0, integer;
param LargoDelBalde {i in Baldes} > 0, integer;
param AltoDelBalde {i in Baldes} > 0, integer;
param LimiteInferiorDePalets := sum{i in Baldes} round((AnchoDelBalde[i] * AltoDelBalde[i] * LargoDelBalde[i]) / (AnchoDelPalet * AltoDelPalet * LargoDelPalet)), integer;
param BaldeCompatible {i in Baldes, j in Baldes} := if TipoDeBalde[i] = TipoDeBalde[j] then 1 else 0, binary;
param BaldesDeLaMismaSeccion {i in Baldes, j in Baldes} := if SeccionDelBalde[i] = SeccionDelBalde[j] then 1 else 0, binary;
# param BaldeDelMismoArticulo {i in Baldes, j in Baldes} := if ArticuloDelBalde[i] = ArticuloDelBalde[j] then 1 else 0, binary;

display LimiteInferiorDePalets;
display LimiteSuperiorDePalets;


/*             Variables de decision                     */
var NumeroDePalets >= 0, integer;
var PaletDelBalde {i in Baldes} >= 1, integer;
var BaldeEnPalet {i in Baldes, j in Palets}, binary;
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
# Solo pueden ir en un palet baldes compatibles
#subject to BaldesCompatibles {i in Baldes, j in Baldes: i > j}: PaletDelBalde[j] - PaletDelBalde[i] + BaldeCompatible[i,j] >=1;
#subject to BaldesCompatibles {i in Baldes, j in Baldes: i > j}: BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i] >= BaldeCompatible[i,j];
# Solo pueden ir en un palet baldes de la misma sección
#subject to BaldesSonDeLaMismaSeccion {i in Baldes, j in Baldes: i > j}: PaletDelBalde[j] - PaletDelBalde[i] + BaldesDeLaMismaSeccion[i,j] >=1;
#subject to BaldesSonDeLaMismaSeccion {i in Baldes, j in Baldes: i > j}:  BaldeALaIzquierdaDelBalde[i,j] + BaldeALaIzquierdaDelBalde[j,i] + BaldeAbajoDelBalde[i,j] + BaldeAbajoDelBalde[j,i] + BaldeDetrasDelBalde[i,j]+ BaldeDetrasDelBalde[j,i] >= BaldesDeLaMismaSeccion[i,j];

minimize NumeroDePaletsAPreparar: NumeroDePalets;

# Datos
#
data;
#param ArticuloDelBalde:= 1 "Articulo1" 2 "Articulo2" 3 "Articulo3" 4 "Articulo3";
#param SeccionDelBalde:= 1 "Seccion1" 2 "Seccion1" 3 "Seccion1" 4 "Seccion1";
#param TipoDeBalde := 1 "Tipo1" 2 "Tipo1" 3 "Tipo1" 4 "Tipo4";
param NumeroDeBaldes := 100;
#param AnchoDelBalde  := 1 297 2 395 3 297 4 800;
#param LargoDelBalde  := 1 395 2 595 3 395 4 1200;
#param AltoDelBalde   := 1 151 2 112 3 151 4 1950;
param SeccionDelBalde:= 1 3 2 3 3 3 4 1 5 3 6 1 7 1 8 1 9 4 10 4 11 6 12 3 13 2 14 2 15 4 16 5 17 5 18 3 19 3 20 1 21 1 22 2 23 2 24 3 25 7 26 7 27 7 28 5 29 7 30 1 31 1 32 1 33 1 34 1 35 2 36 5 37 5 38 5 39 5 40 5 41 5 42 1 43 2 44 3 45 3 46 7 47 5 48 1 49 3 50 1 51 3 52 1 53 1 54 1 55 1 56 2 57 3 58 4 59 4 60 4 61 4 62 4 63 5 64 4 65 3 66 4 67 5 68 7 69 7 70 7 71 3 72 3 73 3 74 3 75 3 76 3 77 3 78 3 79 3 80 2 81 3 82 3 83 1 84 3 85 1 86 1 87 1 88 1 89 1 90 1 91 1 92 4 93 4 94 2 95 6 96 6 97 1 98 1 99 3 100 2;
/*101 4 102 1 103 5 104 5 105 2 106 3 107 3 108 4 109 6 110 1 111 1 112 1 113 1 114 1 115 1 116 7 117 5 118 1 119 3 120 3 121 1 122 1 123 1 124 1 125 1 126 1 127 5 128 5 129 5 130 3 131 3 132 5 133 5 134 5 135 3 136 3 137 5 138 5 139 1 140 1 141 1 142 2 143 2 144 2 145 2 146 1 147 1 148 3 149 1 150 3 151 1 152 1 153 1 154 1 155 1 156 3 157 4 158 4 159 4 160 4 161 4 162 5 163 4 164 3 165 4 166 4 167 5 168 4 169 5 170 5 171 7 172 7 173 7 174 7 175 7 176 4 177 2 178 2 179 3 180 3 181 3 182 3 183 3 184 3 185 3 186 3 187 3 188 1 189 1 190 3 191 1 192 1 193 1 194 1 195 1 196 1 197 1 198 1 199 1 200 1 201 1 202 3 203 4 204 4 205 6 206 6 207 1 208 1 209 3 210 4 211 1 212 5 213 5 214 3 215 3 216 4 217 6 218 1 219 1 220 1 221 1 222 1 223 1 224 7 225 5 226 1 227 3 228 3 229 1 230 1 231 1 232 1 233 1 234 1 235 1 236 5 237 5 238 5 239 3 240 5 241 5 242 5 243 3 244 3 245 2 246 5 247 5 248 1 249 1 250 1 251 1 252 1 253 3 254 1 255 1 256 1 257 1 258 1 259 1 260 3 261 1 262 1 263 1 264 1 265 1 266 1 267 1 268 1 269 1 270 1 271 1 272 1 273 1 274 1 275 1 276 1 277 1 278 3 279 3 280 3 281 2 282 3 283 3 284 3 285 4 286 4 287 4 288 4 289 4 290 5 291 4 292 3 293 4 294 4 295 5 296 4 297 5 298 5 299 7 300 7 301 7 302 7 303 7 304 4;*/
param TipoDeBalde := 1 2 2 1 3 2 4 1 5 2 6 1 7 1 8 1 9 2 10 2 11 2 12 2 13 1 14 2 15 2 16 1 17 1 18 1 19 1 20 1 21 1 22 1 23 1 24 2 25 2 26 2 27 2 28 1 29 2 30 1 31 2 32 2 33 2 34 1 35 1 36 1 37 1 38 1 39 1 40 1 41 1 42 1 43 2 44 1 45 2 46 1 47 1 48 1 49 1 50 1 51 1 52 2 53 2 54 2 55 2 56 2 57 2 58 2 59 2 60 2 61 2 62 2 63 1 64 2 65 1 66 2 67 2 68 2 69 2 70 2 71 2 72 2 73 2 74 1 75 2 76 2 77 1 78 2 79 1 80 1 81 1 82 2 83 1 84 2 85 1 86 2 87 2 88 1 89 1 90 1 91 1 92 2 93 2 94 2 95 2 96 2 97 1 98 1 99 2 100 1;

param ArticuloDelBalde:= 1 '11062-1/3 LOMO CINTA C.E VACIO' 2 '11063-COSTILLAR VACIO' 3 '11093-SOLOMILLO VACIO 4 UND' 4 '11792-COSTILLA CHURRASCO NATUR BASIC' 5 '11799-SOLOMILLO VACIO GENERICO' 6 '11917-COSTILLA TROZO C.E. BAND.' 7 '11936-ESTOFADO C.E. 750 GR. BAND.' 8 '11996-FILETE LOMO FINO 300 NATUR BAN' 9 '12102-BURGUERMEAT VACUNO 400 GR.BAND' 10 '12103-BURGUERMEAT VACUNO 800 GR.C.E.' 11 '12141-BROCHETA ADOBADA 320 GR. BAND.' 12 '12165-SOLOMILLO VACIO GENER. PVP2' 13 '12167-COSTILLA' 14 '12168-AGUJA CERDO C/H' 15 '12178-CARNE PICADA DE TERNERA 400 GR' 16 '12195-PECHUGA PAVO ADOBADA 350 GR. B' 17 '12196-PECHUGA PAVO FINAS HIERBAS 350' 18 '12209-LOMO FRESCO VACIO' 19 '12244-CODILLO DE JAMON VACIO' 20 '12246-12-14 CHULETAS LOMO BAND.' 21 '12248-FILETE JAMON BAND.' 22 '20051-PANCETA CON COSTILLA' 23 '20109-TIRA DE COSTILLA' 24 '20126-COSTILLA ADOBADA IBERICA VACIO' 25 '20158-SOLOMILLO IBERICO VACIO' 26 '20159-PRESA IBERICA VACIO' 27 '20160-SECRETO IBERICO VACIO' 28 '20495-CHULETA SAJONIA' 29 '20514-LOMO IBERICO BAND.' 30 '20543-ESCALOPE JAMON FINO 300 GR.BAN' 31 '20605-LOMO TROZO FILETEADO NATUR BAN' 32 '20608-CHULETA LOMO 6UN NATUR BAND.' 33 '20609-SECRETO NATUR BAND.' 34 '20611-FILETE BACON NATUR BAND.' 35 '20625-CENTRO SIN SOLOMILLO' 36 '20672-LOMO ADOBADO 300 GR. SKIN' 37 '20673-LOMO ADOBADO SKIN 500 GR.' 38 '20674-LOMO AJILLO 300 GR. SKIN' 39 '20700-MAGRO ADOB.300 GR. BAND.' 40 '20701-LOMO SAJONIA .300 GR. BAND.' 41 '20702-LOMO ADOB. HORNO 300 GR. BAND.' 42 '20714-CHULETA AGUJA C.E. BAND.' 43 '20725-CODILLO JAMON SIN PIEL' 44 '20735-JAMON 3D S/H  VACIO' 45 '20738-SECRETO VACIO' 46 '20743-CHULETERO S/C IBERICO' 47 '20777-CHULETA SAJONIA BAND.' 48 '20819-FILETE AGUJA NATUR 400 GR. BAN' 49 '20912-CARRILLADAS VACIO' 50 '20923-ESCAL.JAMON SIEMPRE TIERNO 275' 51 '20925-TIRA COSTILLA VACIO' 52 '21042-FILETE LOMO NATUR 550 GR. BAND' 53 '21043-CHULETA AGUJA NATUR 450 GR. BA' 54 '21044-CHULETA LOMO NATUR 450 GR. BAN' 55 '21045-ESCALOPE JAMON SIEMPRE TIERNO' 56 '21082-OREJAS DE CERDO' 57 '21093-SOLOMILLO CERDO C/CORDON VACIO' 58 '40660-HAMBURGUESA MIXTA 4UN 340.BAND' 59 '40725-HAMBURGUESA VACUNO 6UN 510. BA' 60 '40726-HAMBURGUESA VACUNO 4UN 340. BA' 61 '40822-BURGUERMEAT MIXTA 400. BAND.' 62 '40823-BURGUERMEAT CERDO 400. BAND.' 63 '40835-LOMO ADOBADO TROZO FILETADO BA' 64 '40836-BURGUERMEAT MIXTA 800 BAND.' 65 '40914-LOMO ADOB.TROZO FIL. C.E VACIO' 66 '40949-SALCHICHA FRESCA 350. C.E BAND' 67 '41400-LOMO ADOBADO IBERICO 350. BAND' 68 '41404-COSTILLA IBERICA BAND.' 69 '41405-SECRETO IBERICO BAND.' 70 '41406-PRESA IBERICA BAND.' 71 '10750-JAMON 3 PIEZAS S/H VACIO NATUR' 72 '10782-JAMON 3 PIEZAS S/H VACIO' 73 '11062-1/3 LOMO CINTA C.E VACIO' 74 '11063-COSTILLAR VACIO' 75 '11092-AGUJA CERDO S/H VACIO' 76 '11093-SOLOMILLO VACIO 4 UND' 77 '11094-LOMO FRESCO VACIO' 78 '11095-AGUJA S/H NATUR VACIO' 79 '11097-LOMO CINTA VACIO NATUR' 80 '11161-CHULETERO CERDO S/AGUJA' 81 '11346-PANCETA C/CORTEZA VACIO' 82 '11731-SOLOMILLO PACK2 VACIO' 83 '11792-COSTILLA CHURRASCO NATUR BASIC' 84 '11799-SOLOMILLO VACIO GENERICO' 85 '11839-CHULETA AGUJA C.E. BAND.' 86 '11905-PANCETA TROZO NATUR BAND.' 87 '11906-COSTILLARES EN TIRA NATUR BAND' 88 '11917-COSTILLA TROZO C.E. BAND.' 89 '11922-FILETE PANCETA NATUR FAM. BAND' 90 '11936-ESTOFADO C.E. 750 GR. BAND.' 91 '11996-FILETE LOMO FINO 300 NATUR BAN' 92 '12102-BURGUERMEAT VACUNO 400 GR.BAND' 93 '12103-BURGUERMEAT VACUNO 800 GR.C.E.' 94 '12127-AGUJA CERDO C/H' 95 '12141-BROCHETA ADOBADA 320 GR. BAND.' 96 '12142-PINCHO ADOBADO 360 GR. BAND.' 97 '12150-CHULETA AGUJA C.E PVP2 BAND.' 98 '12163-COSTILLA TROZO C.E. PVP2  BAND' 99 '12165-SOLOMILLO VACIO GENER. PVP2' 100 '12169-TIRA DE COSTILLA';

param AnchoDelBalde := 1 297 2 395 3 297 4 395 5 297 6 395 7 395 8 395 9 297 10 297 11 297 12 297 13 395 14 297 15 297 16 395 17 395 18 395 19 395 20 395 21 395 22 395 23 395 24 297 25 297 26 297 27 297 28 395 29 297 30 395 31 297 32 297 33 297 34 395 35 395 36 395 37 395 38 395 39 395 40 395 41 395 42 395 43 297 44 395 45 297 46 395 47 395 48 395 49 395 50 395 51 395 52 297 53 297 54 297 55 297 56 297 57 297 58 297 59 297 60 297 61 297 62 297 63 395 64 297 65 395 66 297 67 297 68 297 69 297 70 297 71 297 72 297 73 297 74 395 75 297 76 297 77 395 78 297 79 395 80 395 81 395 82 297 83 395 84 297 85 395 86 297 87 297 88 395 89 395 90 395 91 395 92 297 93 297 94 297 95 297 96 297 97 395 98 395 99 297 100 395;
param LargoDelBalde := 1 395 2 595 3 395 4 595 5 395 6 595 7 595 8 595 9 395 10 395 11 395 12 395 13 595 14 395 15 395 16 595 17 595 18 595 19 595 20 595 21 595 22 595 23 595 24 395 25 395 26 395 27 395 28 595 29 395 30 595 31 395 32 395 33 395 34 595 35 595 36 595 37 595 38 595 39 595 40 595 41 595 42 595 43 395 44 595 45 395 46 595 47 595 48 595 49 595 50 595 51 595 52 395 53 395 54 395 55 395 56 395 57 395 58 395 59 395 60 395 61 395 62 395 63 595 64 395 65 595 66 395 67 395 68 395 69 395 70 395 71 395 72 395 73 395 74 595 75 395 76 395 77 595 78 395 79 595 80 595 81 595 82 395 83 595 84 395 85 595 86 395 87 395 88 595 89 595 90 595 91 595 92 395 93 395 94 395 95 395 96 395 97 595 98 595 99 395 100 595;

param AltoDelBalde := 1 151 2 112 3 151 4 164 5 151 6 164 7 112 8 112 9 151 10 151 11 151 12 151 13 164 14 151 15 151 16 112 17 112 18 112 19 164 20 164 21 112 22 112 23 164 24 151 25 151 26 151 27 151 28 164 29 151 30 112 31 151 32 151 33 151 34 164 35 230 36 112 37 112 38 112 39 112 40 112 41 112 42 164 43 151 44 164 45 151 46 164 47 112 48 164 49 164 50 164 51 112 52 151 53 151 54 151 55 151 56 151 57 151 58 151 59 151 60 151 61 151 62 151 63 112 64 151 65 112 66 151 67 151 68 151 69 151 70 151 71 151 72 151 73 151 74 112 75 151 76 151 77 112 78 151 79 112 80 164 81 164 82 151 83 164 84 151 85 164 86 151 87 151 88 164 89 164 90 112 91 112 92 151 93 151 94 151 95 151 96 151 97 164 98 164 99 151 100 112;

end;
