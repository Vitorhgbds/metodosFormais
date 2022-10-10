method Triplo(x:int) returns (r:int) // Assinatura
requires true // PRÉ: Pode ser omitido nesse caso.
ensures r == 3*x // PÓS 
//Code:
{
    // r:= 3*x;

    // return 3*x;
    
    var y := Dobro(x);
    return y + x;
}

// Função dobro, sem especificação porque não é o foco. Não é necessário desenvolver.
method Dobro(x:int) returns (r:int)
ensures r == 2*x