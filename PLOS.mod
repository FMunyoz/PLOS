# test1.mod writes CSV file
set I := {1..300};
set J := {1..20};
set K := {1..100};
param  x{I,J,K} := Uniform01();
table tout {i in I, j in J, k in K} OUT "CSV" "TRMOSAICO.csv" :
i, j, k, x[i,j,k];
end;