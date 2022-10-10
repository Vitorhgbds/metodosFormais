/*
    T1 - Métodos Formais

    Implementação de uma classe de Conjunto de inteiros.

    Nomes: Eduarda Keller, Júlia Makowski, João Pedro Martins, Lucas Cardoso e Vitor Hugo

    
*/
class {:autocontracts} ConjuntoInt
{
    //Abstração
    ghost var Conteudo: seq<int>;
    ghost const TamanhoMaximo: nat;

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
    }

    // A ideia é o construtor iniciar o conjunto como array de tamanho 0, já que conjuntos não tem limites,
    // então a cada elemento adicionado teremos que aumentar o tamanho do array em 1.
    constructor(tm:nat)
    requires tm > 0
    ensures Conteudo == [] // Conteúdo é a sequência vazia
    {

        itens := new int[tm];
        cauda := 0;
        // Referenciar o abstrato que apareceu no ensures
        Conteudo := [];
        TamanhoMaximo := tm;
    }
    // metodo auxiliar que verifica se o elemento já existe dentro do array
    method pertence(e:int) returns (r:bool)
    ensures r <==> e in Conteudo
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
    requires |Conteudo| < TamanhoMaximo // Conjunto não pode estar cheio
    // se o elemento não estava no conteudo antes da invocação do metodo, então retorna true porque ele adicionou;
    // caso o elemento exista no conteudo antigo, retorna falso
    ensures r <==> elemento !in old(Conteudo)
    // definimos o que acontece com o conteudo depois do metodo
    ensures r ==> Conteudo == old(Conteudo) + [elemento]
    ensures !r ==> Conteudo == old(Conteudo) 
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
                var novosItens := new int[2 * cauda];
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
    method BuscarIndice(x:int) returns (r:int)
    ensures r < 0 ==> forall i :: 0 <= i <itens.Length ==> itens[i] != x
    ensures 0 <= r < itens.Length ==> itens[r] == x
    {
        r := 0;
        while r < itens.Length
        decreases itens.Length - r
        invariant 0 <= r <= itens.Length
        invariant forall i :: 0 <= i < r ==> itens[i] != x
        {
            if itens[r] == x
            {
                return r;
            }
            r := r + 1;
        }
        return -1;

    }

    // Retorna TRUE se removeu e FALSE se o elemento não estava no conjunto.
    method Remover(elemento:int) returns (r:bool)
    ensures r <==> elemento in old(Conteudo)
    ensures !r ==> Conteudo == old(Conteudo)
    {
        var elementIndex := BuscarIndice(elemento);
        if(elementIndex == -1){
            r := false;
        } else{
            var novoArray := new int[itens.Length];
            var i := 0;
            while i < itens.Length
            decreases itens.Length - i
            invariant 0 <= i <= itens.Length
            invariant forall i :: 0 <= i < r ==> itens[i] != x
            {

            }
            forall i | 0 <= i < elementIndex {
                novoArray[i] := itens[i];
            }
            forall i | elementIndex <= i < cauda {
                novoArray[i] := itens[i + 1];
            }
            itens := novoArray;
            Conteudo := itens[..cauda];
            r := true;
        }
    }
    
}
