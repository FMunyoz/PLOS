/*********************** Modelo ********************/
# Basado en A Linear Programming Approach for the Three-Dimensional Bin-Packing Problem 
# Mhand Hifi*, Imed Kacem**, St´ephane N`egre*, LeiWu
#
/* ------------------ Declaraciones ---------------*/
param NumeroDeBaldes > 0, integer;
param AnchoDelPalet > 0, integer;
param LargoDelPalet > 0, integer;
param AltoDelPalet > 0, integer;


/*             Conjuntos                                     */
set Baldes :=1..NumeroDeBaldes;
set Palets :=1..4;

/*             Parámetros de entrada                   */
param ArticuloDelBalde {i in Baldes}, symbolic;
param SeccionDelBalde {i in Baldes}, symbolic;
param TipoDeBalde {i in Baldes}, symbolic;
param AnchoDelBalde {i in Baldes} > 0, integer;
param LargoDelBalde {i in Baldes} > 0, integer;
param AltoDelBalde {i in Baldes} > 0, integer;
param LimiteInferiorDePalets :=sum{i in Baldes} round((AnchoDelBalde[i] * AltoDelBalde[i] * LargoDelBalde[i]) / (AnchoDelPalet * AltoDelPalet * LargoDelPalet)), integer;
param LimiteSuperiorDePalets:= 4;
param BaldeCompatible {i in Baldes, j in Baldes} := if TipoDeBalde[i] = TipoDeBalde[j] then 1 else 0, binary;
param BaldesDeLaMismaSeccion {i in Baldes, j in Baldes} := if SeccionDelBalde[i] = SeccionDelBalde[j] then 1 else 0, binary;
param BaldeDelMismoArticulo {i in Baldes, j in Baldes} := if ArticuloDelBalde[i] = ArticuloDelBalde[j] then 1 else 0, binary;


/*             Variables de decision                     */
var NumeroDePalets >= 0, integer;
var PaletDelBalde {i in Baldes} >= 1, integer;
var SeUsaPalet {i in Palets}, binary;
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
subject to IdentificaPaletDelBalde {i in Baldes, j in Palets: i = j}: BaldeEnPalet[i, j] = 1; 
# Restricciones del bin packing problem
#subject to ElVolumenDeLPaletNoSeExcede {j in Palets}: sum{i in Baldes} ((AnchoDelBalde[i] * AltoDelBalde[i] * LargoDelBalde[i]) *  BaldeEnPalet[i,j]) <= SeUsaPalet[j] * (AnchoDelPalet * AltoDelPalet * LargoDelPalet);
#subject to CadaBaldeDebeEstarEnUnPalet {i in Baldes}: sum{j in Palets} BaldeEnPalet[i,j] = 1;
#subject to NumeroDePaletsDebeCoincidir: sum{j in Palets} SeUsaPalet[j] = NumeroDePalets;

# Al menos el numero de palets debe ser el volumen de los baldes
subject to NumeroMiniDePalesPorVolumen {i in Baldes}: LimiteInferiorDePalets <= PaletDelBalde[i];
# Solo pueden ir en un palet baldes compatibles
subject to BaldesCompatibles {i in Baldes, j in Baldes: i > j}: PaletDelBalde[j] - PaletDelBalde[i] + BaldeCompatible[i,j] >=1;
# Solo pueden ir en un palet baldes de la misma sección
subject to BaldesSonDeLaMismaSeccion {i in Baldes, j in Baldes: i > j}: PaletDelBalde[j] - PaletDelBalde[i] + BaldesDeLaMismaSeccion[i,j] >=1;
# en los palets monoproducto no puede haber un articulo distinto

## Función objetivo
#En un palet monoproducto El número de baldes es igual al número de palets con el mismo artículo

minimize NumeroDePaletsAPreparar: NumeroDePalets;

# Datos
#
data;
param ArticuloDelBalde:= 1 "Articulo1" 2 "Articulo2" 3 "Articulo3" 4 "Articulo3";
param SeccionDelBalde:= 1 "Seccion1" 2 "Seccion1" 3 "Seccion1" 4 "Seccion1";
param TipoDeBalde := 1 "Tipo1" 2 "Tipo1" 3 "Tipo1" 4 "Tipo4";
param NumeroDeBaldes := 4;
param AnchoDelPalet  := 800;
param LargoDelPalet  := 1200;
param AltoDelPalet   :=  1950;
param AnchoDelBalde  := 1 297 2 395 3 297 4 800;
param LargoDelBalde  := 1 395 2 595 3 395 4 1200;
param AltoDelBalde   := 1 151 2 112 3 151 4 1950;

#param AnchoDelBalde := 1 297 2 395 3 297 4 395 5 297 6 395 7 395 8 395 9 297 10 297 11 297 12 297 13 395 14 297 15 297 16 395 17 395 18 395 19 395 20 395 21 395 22 395 23 395 24 297 25 297 26 297 27 297 28 395 29 297 30 395 31 297 32 297 33 297 34 395 35 395 36 395 37 395 38 395 39 395 40 395 41 395 42 395 43 297 44 395 45 297 46 395 47 395 48 395 49 395 50 395 51 395 52 297 53 297 54 297 55 297 56 297 57 297 58 297 59 297 60 297 61 297 62 297 63 395 64 297 65 395 66 297 67 297 68 297 69 297 70 297 71 297 72 297 73 297 74 395 75 297 76 297 77 395 78 297 79 395 80 395 81 395 82 297 83 395 84 297 85 395 86 297 87 297 88 395 89 395 90 395 91 395 92 297 93 297 94 297 95 297 96 297 97 395 98 395 99 297 100 395 101 297 102 395 103 395 104 395 105 395 106 297 107 297 108 297 109 297 110 395 111 297 112 395 113 395 114 395 115 395 116 297 117 395 118 395 119 395 120 297 121 297 122 297 123 297 124 297 125 395 126 395 127 395 128 395 129 395 130 297 131 297 132 395 133 395 134 395 135 395 136 395 137 395 138 395 139 395 140 395 141 297 142 297 143 395 144 395 145 297 146 395 147 395 148 395 149 395 150 395 151 297 152 297 153 297 154 297 155 297 156 395 157 297 158 297 159 297 160 297 161 297 162 395 163 297 164 395 165 297 166 297 167 297 168 297 169 297 170 297 171 297 172 297 173 297 174 297 175 297 176 297 177 297 178 395 179 297 180 395 181 297 182 297 183 395 184 297 185 395 186 395 187 297 188 395 189 395 190 297 191 395 192 297 193 297 194 297 195 395 196 395 197 395 198 395 199 395 200 395 201 395 202 395 203 297 204 297 205 297 206 297 207 395 208 395 209 297 210 297 211 395 212 395 213 395 214 297 215 297 216 297 217 297 218 395 219 297 220 395 221 395 222 395 223 395 224 297 225 395 226 395 227 395 228 297 229 297 230 297 231 297 232 297 233 297 234 395 235 395 236 395 237 395 238 395 239 297 240 395 241 395 242 395 243 395 244 395 245 395 246 395 247 395 248 395 249 395 250 297 251 395 252 395 253 395 254 395 255 297 256 297 257 297 258 297 259 297 260 395 261 395 262 297 263 395 264 297 265 297 266 297 267 297 268 297 269 395 270 297 271 395 272 297 273 297 274 395 275 297 276 395 277 395 278 297 279 297 280 395 281 395 282 395 283 395 284 395 285 297 286 297 287 297 288 297 289 297 290 395 291 297 292 395 293 297 294 297 295 297 296 297 297 297 298 297 299 297 300 297 301 297 302 297 303 800 304 800;
#param LargoDelBalde := 1 395 2 595 3 395 4 595 5 395 6 595 7 595 8 595 9 395 10 395 11 395 12 395 13 595 14 395 15 395 16 595 17 595 18 595 19 595 20 595 21 595 22 595 23 595 24 395 25 395 26 395 27 395 28 595 29 395 30 595 31 395 32 395 33 395 34 595 35 595 36 595 37 595 38 595 39 595 40 595 41 595 42 595 43 395 44 595 45 395 46 595 47 595 48 595 49 595 50 595 51 595 52 395 53 395 54 395 55 395 56 395 57 395 58 395 59 395 60 395 61 395 62 395 63 595 64 395 65 595 66 395 67 395 68 395 69 395 70 395 71 395 72 395 73 395 74 595 75 395 76 395 77 595 78 395 79 595 80 595 81 595 82 395 83 595 84 395 85 595 86 395 87 395 88 595 89 595 90 595 91 595 92 395 93 395 94 395 95 395 96 395 97 595 98 595 99 395 100 595 101 395 102 595 103 595 104 595 105 595 106 395 107 395 108 395 109 395 110 595 111 395 112 595 113 595 114 595 115 595 116 395 117 595 118 595 119 595 120 395 121 395 122 395 123 395 124 395 125 595 126 595 127 595 128 595 129 595 130 395 131 395 132 595 133 595 134 595 135 595 136 595 137 595 138 595 139 595 140 595 141 395 142 395 143 595 144 595 145 395 146 595 147 595 148 595 149 595 150 595 151 395 152 395 153 395 154 395 155 395 156 595 157 395 158 395 159 395 160 395 161 395 162 595 163 395 164 595 165 395 166 395 167 395 168 395 169 395 170 395 171 395 172 395 173 395 174 395 175 395 176 395 177 395 178 595 179 395 180 595 181 395 182 395 183 595 184 395 185 595 186 595 187 395 188 595 189 595 190 395 191 595 192 395 193 395 194 395 195 595 196 595 197 595 198 595 199 595 200 595 201 595 202 595 203 395 204 395 205 395 206 395 207 595 208 595 209 395 210 395 211 595 212 595 213 595 214 395 215 395 216 395 217 395 218 595 219 395 220 595 221 595 222 595 223 595 224 395 225 595 226 595 227 595 228 395 229 395 230 395 231 395 232 395 233 395 234 595 235 595 236 595 237 595 238 595 239 395 240 595 241 595 242 595 243 595 244 595 245 595 246 595 247 595 248 595 249 595 250 395 251 595 252 595 253 595 254 595 255 395 256 395 257 395 258 395 259 395 260 595 261 595 262 395 263 595 264 395 265 395 266 395 267 395 268 395 269 595 270 395 271 595 272 395 273 395 274 595 275 395 276 595 277 595 278 395 279 395 280 595 281 595 282 595 283 595 284 595 285 395 286 395 287 395 288 395 289 395 290 595 291 395 292 595 293 395 294 395 295 395 296 395 297 395 298 395 299 395 300 395 301 395 302 395 303 600 304 600;

#param AltoDelBalde := 1 151 2 112 3 151 4 164 5 151 6 164 7 112 8 112 9 151 10 151 11 151 12 151 13 164 14 151 15 151 16 112 17 112 18 112 19 164 20 164 21 112 22 112 23 164 24 151 25 151 26 151 27 151 28 164 29 151 30 112 31 151 32 151 33 151 34 164 35 230 36 112 37 112 38 112 39 112 40 112 41 112 42 164 43 151 44 164 45 151 46 164 47 112 48 164 49 164 50 164 51 112 52 151 53 151 54 151 55 151 56 151 57 151 58 151 59 151 60 151 61 151 62 151 63 112 64 151 65 112 66 151 67 151 68 151 69 151 70 151 71 151 72 151 73 151 74 112 75 151 76 151 77 112 78 151 79 112 80 164 81 164 82 151 83 164 84 151 85 164 86 151 87 151 88 164 89 164 90 112 91 112 92 151 93 151 94 151 95 151 96 151 97 164 98 164 99 151 100 112 101 151 102 112 103 112 104 112 105 112 106 151 107 151 108 151 109 151 110 112 111 151 112 112 113 112 114 112 115 112 116 151 117 112 118 112 119 164 120 151 121 151 122 151 123 151 124 151 125 164 126 112 127 112 128 112 129 112 130 151 131 151 132 112 133 112 134 112 135 112 136 112 137 112 138 112 139 164 140 164 141 151 142 151 143 164 144 112 145 151 146 164 147 164 148 112 149 164 150 112 151 151 152 151 153 151 154 151 155 151 156 112 157 151 158 151 159 151 160 151 161 151 162 112 163 151 164 112 165 151 166 151 167 151 168 151 169 151 170 151 171 151 172 151 173 151 174 151 175 151 176 151 177 151 178 164 179 151 180 112 181 151 182 151 183 112 184 151 185 112 186 164 187 151 188 112 189 164 190 151 191 164 192 151 193 151 194 151 195 164 196 164 197 112 198 112 199 112 200 164 201 164 202 112 203 151 204 151 205 151 206 151 207 164 208 164 209 151 210 151 211 112 212 112 213 112 214 151 215 151 216 151 217 151 218 112 219 151 220 112 221 112 222 112 223 112 224 151 225 112 226 112 227 164 228 151 229 151 230 151 231 151 232 151 233 151 234 164 235 112 236 112 237 112 238 112 239 151 240 112 241 112 242 112 243 112 244 112 245 112 246 112 247 112 248 164 249 164 250 151 251 164 252 164 253 112 254 164 255 151 256 151 257 151 258 151 259 151 260 112 261 112 262 151 263 164 264 151 265 151 266 151 267 151 268 151 269 164 270 151 271 112 272 151 273 151 274 164 275 151 276 164 277 164 278 151 279 151 280 112 281 164 282 164 283 112 284 164 285 151 286 151 287 151 288 151 289 151 290 112 291 151 292 112 293 151 294 151 295 151 296 151 297 151 298 151 299 151 300 151 301 151 302 151 303 1950 304 1950; 

end;
