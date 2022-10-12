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
        && (forall i,j :: 0 <= i < j < cauda ==> itens[i] != itens[j])
    }

    // A ideia é o construtor iniciar o conjunto como array de tamanho 0, já que conjuntos não tem limites,
    // então a cada elemento adicionado teremos que aumentar o tamanho do array.
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

    method Tamanho() returns (t:nat)
    requires cauda >= 0
    ensures cauda == |Conteudo|
    {
        return cauda;
    }

    method EstaVazio() returns (r:bool)
    ensures r ==> |Conteudo| == 0
    ensures !r ==> |Conteudo| > 0
    {
        if(cauda==0) {
            r:= true;
        } else {
            r:=false;
        }         
    }


    method Interseccao(a: ConjuntoInt, b:ConjuntoInt) returns (novoArray:ConjuntoInt)
    requires a.Valid()
    requires b.Valid()
    requires a.itens.Length > 0
    requires b.itens.Length > 0
    ensures novoArray.itens.Length >= 0
    //ensures novoArray.itens[novoArray.cauda] in novoArray.Conteudo ==> novoArray.itens[novoArray.cauda] in a.Conteudo && novoArray.itens[novoArray.cauda] in b.Conteudo
    {
        var tmA:int := a.Tamanho();
        var tm:int := b.Tamanho();
        if(tmA >= tm) {
            var tm:int := tmA;
        }
        var auxArray := new ConjuntoInt(tm);

        var i:nat := 0;
        while(i < auxArray.itens.Length - 1)
        decreases auxArray.itens.Length - i
        invariant 0 <= i <= auxArray.itens.Length
        {
            var resultado := b.pertence(a.itens[i]);
            if(resultado){
                var indice := b.BuscarIndice(a.itens[i]);
                auxArray.itens[i] := b.itens[indice];
            }
            i := i + 1;
        }
        novoArray := auxArray;
        
        return novoArray;
    }

    method Uniao(a: ConjuntoInt, b:ConjuntoInt) returns (novoArray:ConjuntoInt)
    requires a.Valid()
    requires b.Valid()
    requires a.itens.Length > 0
    requires b.itens.Length > 0
    ensures novoArray.itens.Length >= 0
    //ensures novoArray.itens[novoArray.cauda] in novoArray.Conteudo ==> novoArray.itens[novoArray.cauda] in a.Conteudo && novoArray.itens[novoArray.cauda] in b.Conteudo
    {
        var auxArray := new ConjuntoInt(b.itens.Length+a.itens.Length);

        auxArray := a;
        var u:nat := a.itens.Length;
        var i:nat := a.itens.Length;
        var j:nat := 0;

        while(i < auxArray.itens.Length - 1)
        decreases auxArray.itens.Length - i
        invariant 0 <= i <= auxArray.itens.Length
        {
            var resultado := a.pertence(b.itens[j]);
            if(!resultado){
                auxArray.itens[u] := b.itens[j];
                j:= j + 1;
                u:= u + 1;
            }
            i := i + 1;
        }
        novoArray := auxArray;
        
        return novoArray;
    }

    //method União(novoArray:seq) returns

    // Retorna TRUE se removeu e FALSE se o elemento não estava no conjunto.
    method Remover(elemento:int) returns (r:bool)
    requires itens.Length > 0
    requires cauda >=0
    ensures !r ==> elemento !in old(Conteudo)
    {
        var elementIndex := BuscarIndice(elemento);
        if(elementIndex == -1){
            return false;
        } else{
            var novoArray := new int[itens.Length - 1];
            var i:nat := 0;
            while(i < elementIndex && i < itens.Length)
            decreases itens.Length - i
            invariant 0 <= i <= itens.Length
            {
                novoArray[i] := itens[i];
                i := i + 1;
            }
            while(i < itens.Length - 2)
            decreases novoArray.Length - i
            invariant 0 <= i <= itens.Length
            {
                novoArray[i] := itens[i + 1];
                i := i + 1;
            }
            itens := novoArray;
            if(cauda==0){
                cauda :=0;
            }else{
                cauda := cauda-1;
            }                
            Conteudo := itens[..cauda];
            r:=true;
        }
    }    
}