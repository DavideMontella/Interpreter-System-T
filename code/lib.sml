signature LISTUTIL= 
 sig
  val isIn : ''a * ''a list -> bool
  val union: ''a list * ''a list -> ''a list
  val minus: ''a list * ''a list -> ''a list
  val intersect: ''a list * ''a list -> ''a list
  val map: ('a -> 'b) -> 'a list -> 'b list
  val fold: (('a * 'b) -> 'b) -> 'b -> 'a list -> 'b
  val zip: 'a list * 'b list -> ('a * 'b)list
  exception Lookup
  val lookup: (''a * 'b) list -> ''a -> 'b
  exception Prefix
  val prefix: 'a list * int -> 'a list
 end;


	(*
		List() è un funtore che non prende nulla in input e torna una struttura con la famiglia di segnature di LISTUTIL.
	*)
functor List(): LISTUTIL=
struct
	
  (*Torna true solo se x è contenuto nella lista data in input*)
  fun isIn(x,[])= false
    | isIn(x,hd::tl) = x = hd orelse isIn(x,tl)
	
  (*Unisce le due liste date in input scartando i duplicati*)
  fun union([],l) =l
    | union(hd::tl,l) = if isIn(hd,l) then union(tl,l)
                        else hd::union(tl,l)
	
  (*Ritorna la prima lista dopo avergli tolto gli elementi in comune con la seconda lista*)
  fun minus([],l)= []
    | minus(hd::tl,l) = if isIn(hd,l) then minus(tl,l)
                        else hd::minus(tl,l)
	
  (*Ritorna l'intersezione delle due liste*)
  fun intersect([],l) = []
    | intersect(hd::tl, l) = if isIn(hd,l) then
                                hd::intersect(tl,l)
                             else intersect(tl,l)
  
  (*Prende in input una funzione, una lista e restituisce la lista dove ogni elemento è l'elemento della lista data in input al quale è stata applicata la funzione presa in input*)							 
  fun map f [] = []
    | map f (hd::tl) = f hd :: map f tl
  
  (*Prende in input una funzione f, un elemento che viene restituito solo quando la lista data in input è vuota e una lista. Restituisce l'applicazione di f sulla coppia (hd, ric) dove hd è il primo elemento della lista e ric è il risultato della chiamata ricorsiva fatta dandogli in input le stesse cose prese in input ed la lista diminuita del primo elemento*)
  fun fold f b [] = b
    | fold f b (hd::tl) = f(hd,fold f b tl)
  
  (*Prende in input una coppia di liste. Restituisce una lista di coppie dove la i-esima coppia rappresenta gli i-esimi elementi delle due liste prese in input*)
  fun zip([],l) = []
    | zip(l,[]) = []
    | zip(hd::tl, hd'::tl')= (hd,hd')::zip(tl,tl')

  (*Prende in input una lista di coppie e un elemento x. Restituisce il secondo elemento della coppia che contiene x come primo elemento*)
  exception Lookup
  fun lookup [] x = raise Lookup
    | lookup ((x,y)::tl) x'=
        if x=x' then y else lookup tl x'
  
  (*Prende in input una lista ed un intero n. Restituisce la lista che contiene tutti i primi n elementi della lista presa in input*)
  exception Prefix
  fun prefix(l,0) = []
    | prefix([],n) = raise Prefix
    | prefix((hd::tl),n)= hd::prefix(tl,n-1)
end;

