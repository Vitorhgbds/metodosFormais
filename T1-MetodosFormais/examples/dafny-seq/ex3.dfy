method Remover(a:array<int>, fim:nat, inicio:nat, n:nat)
requires fim <= a.Length
requires inicio + n <= fim
modifies a
ensures a[..inicio] == old(a)[..inicio]
ensures a[inicio..fim-n] == old(a)[inicio+n..fim]
{
    var i:nat := 0;
    while i < fim - (inicio+n)
    invariant i <= fim -(inicio+n)
    invariant a[..inicio] == old(a)[..inicio]
    invariant a[inicio..inicio+i] == old(a)[inicio+n..inicio+n+i]
    invariant a[inicio+i..fim] == old()
    decreases i - (fim - (inicio+n))
    {
        a[inicio+i] := a[inicio+n+i];
    }
}