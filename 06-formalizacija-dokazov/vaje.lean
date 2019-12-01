namespace hidden -- Zato, da lahko povozimo uradne definicije, ki jih sicer ne bi mogli
universe u -- Parameter, ki se uporablja v tipih

-------------------------------------------------------------------------------
inductive list (A:Type) : Type
| Nil {} : list -- Brez {} moramo konstruktorju Nil vedno podati tip A
| Cons : A -> list -> list -- Cons tip A ugotovi iz tipa prvega elementa

-- Kadar definiramo funkcije, so vsi argumenti, podani v {} ali (), fiksni
-- inductive llist : Type -> Type
-- | NNil {A} : llist A
-- | Cons{A} : A -> llist A -> llist A
-- To je bolj nazorna definicija, ki pa ne deluje

namespace list -- S tem si zagotovimo, da nam ni vsakič potrebno pisati list.Cons, temveč le Cons
-- Dopolnite definicije in dokažitve trditve za sezname iz vaj 3. Uporabljate -- lahko notacijo x :: xs, [] in ++ (namesto @), vendar bodite pozorni na
-- oklepaje.

notation x `::` xs := Cons x xs
notation `[]` := Nil

def join {A} : list A -> list A -> list A
| [] ys := ys
| (x::xs) ys := x :: (join xs ys)

notation xs `++` ys := join xs ys -- Združevanje seznamov (@)

theorem join_nil {A} (xs: list A) :
-- Če seznamu na desni dodamo prazen seznam, ga s tem nismo spremenili
-- Na tem mestu bomo dokaze, ki smo jih rešili na vajah, zapisali še v Leanu
  xs ++ [] = xs 
:=
begin
  induction xs,
  -- Imamo primera, ko je xs prazen seznam in ko je sestavljen, kjer za rep to že velja
  {unfold join,},
  unfold join, -- prestavimo oklepaje, s čimer dobimo IP
  rewrite xs_ih,
end


def reverse {A} : list A -> list A
| [] := []
| (x::xs) := (reverse xs) ++ (x::[])

-- Za naslednji izrek potrebujemo dokaz, da je join asociativen ukaz
theorem join_assoc {A} (xs ys zs : list A):
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs)
:=
begin
    induction xs,
    unfold join,
    unfold join, rewrite xs_ih,
end


theorem reverse_join {A} (xs ys : list A):
    reverse (xs ++ ys) = (reverse ys) ++ (reverse xs)
:=
begin
    induction xs,
    {unfold join, unfold reverse, rewrite join_nil, },
    -- rewrite join_nil moramo uporabiti za ys, ker na njem ne uporabljamo indukcije
    unfold join, unfold reverse, rewrite xs_ih, rewrite join_assoc,
end





end list
-------------------------------------------------------------------------------

-- Podobno kot za sezname, napišite tip za drevesa in dokažite trditve iz 
-- vaj 3. Če po definiciji tipa `tree` odprete `namespace tree` lahko
-- uporabljate konstruktorje brez predpone, torej `Empty` namesto
-- `tree.Empty`.

inductive tree (A : Type) : Type
| Empty {} : tree
| Node : tree -> A -> tree -> tree

namespace tree
def mirror {A} : tree A -> tree A
| Empty := Empty
| (Node lt x rt) := (Node (mirror rt) x (mirror lt))


theorem mirror_mirror {A} (t : tree A) :
    mirror (mirror t) = t
:=
begin
    induction t,
    {unfold mirror, },
    -- Ker imamo dve poddrevesi, s tem dobimo tudi dve indukcijski predpostavki
    unfold mirror, rewrite [t_ih_a, t_ih_a_1],
    -- Rewrite [] uporabimo za večkratno uporabo, lahko dodamo tudi smer, v kateri deluje (<-)
end


def tree_map {A B : Type} (f : A -> B) : tree A -> tree B
| Empty := Empty
| (Node lt x rt) := Node (tree_map lt) (f x) (tree_map rt)
-- Ker smo funkciji f podali že na začetku, se povsod uporabi, zato je ne podajamo v rekurziji

theorem mirror_map_comm {A B : Type} (t : tree A) (f : A -> B) :
    tree_map f (mirror t) = mirror (tree_map f t)
:=
begin
    induction t,
    {unfold mirror, unfold tree_map, unfold mirror, },
    unfold mirror, unfold tree_map, rewrite [t_ih_a, t_ih_a_1], unfold mirror, 
end


end tree
-- Na podoben način delujejo dokazi za drevesa v splošnem
-------------------------------------------------------------------------------
-- Definirajte nekaj konstruktov jezika IMP.
-- IMP za razliko od Lambde nima samo termov (ima exp, bexp, cmd)
-- Prav tako potrebuje lokacije

inductive loc : Type
| Loc : int -> loc

-- Ker v IMPu ločimo med različnimi vrstami termov, definiramo tip vrst
inductive kind : Type
| AExp | BExp | Comm

namespace kind

-- Funkcije za delovanje potrebujejo še neko vrsto spomina -> potrebujemo le za oprecajisko semantiko
inductive memory : Type
| Null : memory
| Cons : memory -> loc -> int -> memory
-- To pomeni l_1 = i_1, l_2 = i_2, l_3 = i_3, ...
-- Cons( Cons( Cons( Null, l_1, i_1), l_2, i_2)...)

-- Tip 'term' sprejme še vrsto terma. Ukazi so tako tipa `term Comm`.
inductive term : kind -> Type
| Int : int -> term AExp
| Plus : term AExp -> term AExp -> term AExp
| Bool : bool -> term BExp
| Eq : term AExp -> term AExp -> term BExp
| Update : loc -> term AExp -> term Comm

theorem bullshit (t1 t2 : term AExp) :
    t1 = t2
:=
begin
    -- V tem primeru moramo ločiti ogromno število različnih možnosti, ki jih lahko obsega t; če bi uporabili induction
    -- Zaradi tega uporabimo cases, ker ta upošteva tip t-ja, vendar problem nastane, ker s tem nimamo IP
    cases t2,
    ...
end



end kind

end hidden