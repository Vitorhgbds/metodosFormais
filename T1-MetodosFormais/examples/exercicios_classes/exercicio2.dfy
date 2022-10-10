class {:autocontracts}  FilaNat
{
    //Implementação
    var a: array<nat>;
    var cauda: nat;
    //Abstração
    ghost var Conteudo: seq<nat>;

    predicate Valid()
    {
        a.Length != 0
        && 0 <= cauda <= a.Length
        && Conteudo == a[0..cauda]
    }

    constructor ()
      ensures Conteudo == []
    {
        a := new nat[5];
        cauda := 0;
        Conteudo := [];
    }

    method Tamanho() returns (n:nat)
      ensures n == |Conteudo|
      ensures Conteudo == old(Conteudo)
    {
        return cauda;
    }

    method Enfileira(e:nat)
      ensures Conteudo == old(Conteudo) + [e]
    {
        if (cauda == a.Length)
        {
            //duplica o tamanho do array original
            var b := new nat[2 * a.Length];
            forall(i | 0 <= i < a.Length)
            {
                b[i] := a[i];
            }
            a := b;
        }
        a[cauda] := e;
        cauda := cauda + 1;
        Conteudo := Conteudo + [e];
    }

    method Desenfileira() returns (e:nat)
      requires |Conteudo| > 0
      ensures e == old(Conteudo)[0]
      ensures Conteudo == old(Conteudo)[1..]
    {
        e := a[0];
        cauda := cauda - 1;
        forall(i | 0 <= i < cauda)
        {
            a[i] := a[i+1];
        }
        Conteudo := a[0..cauda];
    }
}

method Main()
{
    var fila := new FilaNat();
    fila.Enfileira(1);
    fila.Enfileira(2);
    assert fila.Conteudo == [1,2];
    var e := fila.Desenfileira();
    assert e == 1;
    assert fila.Conteudo == [2];
}










