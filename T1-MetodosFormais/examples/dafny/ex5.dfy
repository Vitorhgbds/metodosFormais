function Fat(n:nat):nat
decreases n
{
    if n == 0
    then 1
    else n * Fat(n-1)
}

method Fatorial(n:nat) returns (f:nat)
ensures f == Fat(n)
{
    f := 1;
    var i := 1;
    while i <= n
        decreases n - i
        invariant 1 <= i <= n+1 
        invariant f == Fat(i-1) 
    {
        f := f * i;
        i := i + 1;
    }
    return f;
}

/*
Variante: Mostrar que termina
Invariante: Mostrar o que um laço/repetição faz.

Variante: n-i
Descreases: Palavra chave para descrever a variante.
A Variante sempre é descrescente e finito.
2, 1, 0, -1
*/
