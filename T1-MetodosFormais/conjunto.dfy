/*
    T1 - Métodos Formais

    Implementação de uma classe de Conjunto de inteiros.

    Nomes: Eduarda Keller, Júlia Makowski, João Pedro Martins, Lucas Cardoso e Vitor Hugo

    
*/
class {:autocontracts} ConjuntoInt
{
    //Abstração
    ghost var Conteudo: seq<int>;

    //Implementação
    var itens: array<int>;
    var cauda: nat;
    var count: nat;

    // para o objeto ser valido
    predicate Valid()
    {
        itens.Length > 0
        && 0 <= cauda <= itens.Length
        && Conteudo == itens[..cauda]
        && (forall i,j :: 0 <= i < j < cauda ==> itens[i] != itens[j])
    }

    // A ideia é o construtor iniciar o conjunto como array de tamanho 0, já que conjuntos não tem limites,
    // então a cada elemento adicionado teremos que aumentar o tamanho do array.
    constructor()
    ensures Conteudo == [] // Conteúdo é a sequência vazia
    ensures cauda <= itens.Length
    {

        itens := new int[1];
        cauda := 0;
        // Referenciar o abstrato que apareceu no ensures
        Conteudo := [];
    }
    // metodo auxiliar que verifica se o elemento já existe dentro do array
    method pertence(e:int) returns (r:bool)
    ensures r <==> e in Conteudo
    ensures r ==> e in Conteudo
    ensures !r ==> e !in Conteudo
    {
        var i := 0;
        while i < cauda 
        invariant 0 <= i <= cauda
        invariant forall j::0 <= j < i ==> itens[j] != e
        {
            if itens[i] == e {
                return true;
            }
            i := i + 1;
        }
        return false;
    } 
    
    method Adicionar(elemento:int) returns (r:bool)
    // se o elemento não estava no conteudo antes da invocação do metodo, então retorna true porque ele adicionou;
    // caso o elemento exista no conteudo antigo, retorna falso
    ensures r <==> elemento !in old(this.Conteudo)
    // definimos o que acontece com o conteudo depois do metodo
    ensures r ==> this.Conteudo == old(this.Conteudo) + [elemento]
    ensures !r ==> this.Conteudo == old(this.Conteudo)
    {
        // verificamos se o elemento já está presente na lista
        var isInList := pertence(elemento);
        if isInList {
            r := false;
        }
        else{
            //verificamos se a lista está cheia antes de adicionar
            if cauda == itens.Length {
                // caso lista cheia, criamos uma nova mapeamos os elementos
                var novosItens := new int[itens.Length + 1];
                forall i | 0 <= i < cauda {
                    novosItens[i] := itens[i];
                }
                itens := novosItens; 
            }
            // adicionamos o elemento na lista
            itens[cauda] := elemento;
            cauda := cauda + 1;
            Conteudo := Conteudo + [elemento];
            r := true;
        }
    }


    // Método auxiliar que busca o elemento e devolve o índice. Ou devolve -1 caso não encontrar.
    method BuscarIndice(elemento:int) returns (indice:int)
    ensures indice < 0 ==> forall i :: 0 <= i < cauda ==> itens[i] != elemento
    ensures 0 <= indice ==> indice < cauda && itens[indice] == elemento
    ensures Conteudo == old(Conteudo)
    {
        indice := 0;
        while indice < cauda
        decreases cauda - indice
        invariant 0 <= indice <= cauda
        invariant forall i :: 0 <= i < indice ==> itens[i] != elemento
        {
            if itens[indice] == elemento
            {
                return indice;
            }
            indice := indice + 1;
        }
        return -1;

    }

    method Tamanho() returns (t:nat)
    requires cauda >= 0
    ensures cauda == |Conteudo|
    ensures Conteudo == old(Conteudo)
    {
        return cauda;
    }

    method EstaVazio() returns (r:bool)
    ensures r <==> |Conteudo| == 0
    {
        return cauda == 0;        
    }

    method Remove(e:int) returns (b:bool)
    requires |Conteudo| > 0
    ensures b ==> (forall i :: i in old(Conteudo) && i != e ==> i in Conteudo) && |Conteudo| == |old(Conteudo)| - 1
    ensures !b ==> Conteudo == old(Conteudo)
    ensures b <==> e in old(Conteudo)
    ensures e !in Conteudo
    {
        var pertence := pertence(e);
        if(!pertence) {
            b := false;
            return;
        }
 
        var pos := BuscarIndice(e);
        cauda := cauda - 1;
        forall(i | pos <= i < cauda)
        {
            itens[i] := itens[i+1];
        }
        Conteudo := Conteudo[0..pos] + Conteudo[pos+1..];
        b := true;
    }


    /*method Interseccao(outroConjunto:ConjuntoInt) returns (novoConjunto:ConjuntoInt)
    requires outroConjunto.Valid()
    //ensures forall i :: 0 <= i < novoConjunto.cauda ==> novoConjunto.itens[i] in Conteudo && novoConjunto.itens[i] in outroConjunto.Conteudo
    //ensures Conteudo == old(Conteudo)
    //ensures outroConjunto.Conteudo == old(outroS'Conjunto.Conteudo)
    //ensures novoConjunto.Valid()
    {
        novoConjunto := new ConjuntoInt();
        var i := 0;
        while i < cauda 
        invariant 0 <= i <= cauda
        decreases cauda - i
        {
            var e := itens[i];
            var isInIntersect := outroConjunto.pertence(e);
            if(isInIntersect) {
                var b := novoConjunto.Adicionar(e);
            }
            i := i + 1;
        }
        return novoConjunto;
    }*/

    method Uniao(outroConjunto: ConjuntoInt) returns (novoConjunto:ConjuntoInt)
    requires outroConjunto.Valid()
    requires this != outroConjunto
    ensures fresh(novoConjunto)
    ensures novoConjunto.Valid()
    ensures Conteudo == old(Conteudo)
    ensures outroConjunto.Conteudo == old(outroConjunto.Conteudo)
    //ensures forall i :: 0 <= i < novoConjunto.cauda ==> novoConjunto.itens[i] in Conteudo || novoConjunto.itens[i] in outroConjunto.Conteudo
    {
        novoConjunto := new ConjuntoInt();
        var i := 0;
        while i < cauda
        invariant novoConjunto.Valid()
        //decreases cauda - i
        invariant Conteudo == old(Conteudo)
        modifies novoConjunto
        invariant 0 <= i <= cauda
        {
            var e := itens[i];
            var adicionou := novoConjunto.Adicionar(e);
            i := i + 1;
        }
        i := 0;
    /*    while i < outroConjunto.cauda
        modifies novoConjunto
        invariant novoConjunto.Valid()
        invariant Conteudo == old(Conteudo)
        invariant outroConjunto.Conteudo == old(outroConjunto.Conteudo)
        invariant 0 <= i <= outroConjunto.cauda
        {
            var adicionou := novoConjunto.Adicionar(outroConjunto.itens[i]);
            i := i + 1;
        }
        */
    }

    //method União(novoArray:seq) returns


}
/*
method Main{
    var c := new ConjuntoInt();
    assert c.Conteudo == [];
    var p := c.pertence(0);
    assert !p;
    var a := c.adicionar(1);
    assert a;
    assert c.Conteudo == [1];
    var p := c.pertence(1);
    assert p;
    // Adicionar 1 retorna false pois já temos 1.
    var a := c.adicionar(1);
    assert !a;
    var a := c.adicionar(2);
    assert a;
    var a := c.adicionar(5);
    assert a;
    var a := c.adicionar(6);
    assert a;
    assert c.Conteudo == [1,2,5,6];
    var index := c.BuscarIndice(5)
    //assert index == 2
    //var tamanho := c.Tamanho()
    //assert tamanho == 4
    //var vazio := c.EstaVazio()
    //assert !vazio
    }*/