-- ==================== Syntax ====================

def loc := string


inductive aexp : Type
| Lookup : loc -> aexp
| Int : int -> aexp
| Plus : aexp -> aexp -> aexp
| Minus : aexp -> aexp -> aexp
| Times : aexp -> aexp -> aexp

-- Komentar: Lean ima vgrajene tudi določene bližnjice, ki jih dobimo s \ + ukaz

inductive bexp : Type
| Bool : bool -> bexp
| Equal : aexp -> aexp -> bexp
| Less : aexp -> aexp -> bexp


inductive cmd : Type
| Assign : loc -> aexp -> cmd
| IfThenElse : bexp -> cmd -> cmd -> cmd
| Seq : cmd -> cmd -> cmd
| Skip : cmd
| WhileDo : bexp -> cmd -> cmd

-- ================== Example 'fact.imp' in LEAN notation. ==================

def fact : cmd :=
  cmd.Seq
    (cmd.Seq
      (cmd.Assign "n" (aexp.Int 10))
      (cmd.Assign "fact" (aexp.Int 1)) )
    (cmd.WhileDo
      (bexp.Less (aexp.Int 0) (aexp.Lookup "n"))
      (cmd.Seq
        (cmd.Assign "fact" 
          (aexp.Times (aexp.Lookup "fact") (aexp.Lookup "n")) )
        (cmd.Assign "n"
          (aexp.Minus (aexp.Lookup "n")(aexp.Int 1)) ) ) )

-- ==================== Environment ====================

inductive env : Type
| Nil : env
| Cons : loc -> int -> env -> env
-- Nil ~ []
-- Cons l i E ~ (l, i) :: E

inductive lookup : loc -> env -> int -> Prop
| Find {loc i E} : 
    lookup loc (env.Cons loc i E) i 
| Search {loc loc' i' E' i} : 
    loc≠loc' -> lookup loc E' i -> 
    lookup loc (env.Cons loc' i' E') i
-- lookup l E i ~> (l, i) ∈ E
-- Možnosti sta 2: ali obstaja seznam okolja, kjer je lokacija prvi element tega seznama, ali pa
-- obstaja dokaz za ostanek tega seznama (tj. po načelu indukcije)

-- lookup : env -> loc -> int option
-- PROP: lookup l E i ~> FUNCTION: lookup E l = Some i
-- Zaradi našega zapisa nam ni treba obravnavati primera, ko l ne leži v okolju, tj. primer None, 
-- vendar s tem obstajajo protiprimeri za dokaze.

-- ==================== Operational Semantics ====================

inductive aeval : env -> aexp -> int -> Prop
| Lookup {E loc i} :
    lookup loc E i -> 
    aeval E (aexp.Lookup loc) i
| Int {E i} :
    aeval E (aexp.Int i) i
| Plus {E a1 i1 a2 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Plus a1 a2) (i1 + i2)
| Minus {E a1 i1 a2 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Plus a1 a2) (i1 - i2)
| Times {E a1 i1 a2 i2} :
    aeval E a1 i1 -> aeval E a2 i2 ->
    aeval E (aexp.Plus a1 a2) (i1 * i2)


-- Lean works best with '<' and '≤' so we use them instead of '>' and '≥'.
inductive beval : env -> bexp -> bool -> Prop
| Bool {E b} :
    beval E (bexp.Bool b) b
| Equal_t {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 -> i1 = i2 -> -- Tip te enakosti je PROP, ker gre za Lean enakost
    beval E (bexp.Equal a1 a2) true
    -- Zaradi tega imamo Equal_t in Equal_f, tj. ločimo primera, ko enakost velja in ko ne
| Equal_f {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 -> i1 ≠ i2 ->
    beval E (bexp.Equal a1 a2) false
| Less_t {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 -> i1 < i2 ->
    beval E (bexp.Less a1 a2) true
| Less_f {E a1 a2 i1 i2} :
    aeval E a1 i1 -> aeval E a2 i2 -> ¬ (i1 < i2) ->
    beval E (bexp.Less a1 a2) false
-- V Leanu je definirana le neenakost < in ne >, zato imamo manj dela z negacijami kot pa z definiranje
-- te neenakosti. Sicer bi morali to še definirati in dokazovati.

inductive ceval : env -> cmd -> env -> Prop
| Assign {E a i l} :
    aeval E a i ->
    ceval E (cmd.Assign l a) (env.Cons l i E)
-- Edini ukaz, ki spreminja okolje. 
-- Opomba: Nič nemore iz okolja odstraniti nekega elementa.
| IfThenElse_t {E b c1 c2 E'} :
    beval E b true -> ceval E c1 E' ->
    ceval E (cmd.IfThenElse b c1 c2) E'
| IfThenElse_f {E b c1 c2 E'} :
    beval E b false -> ceval E c2 E' ->
    ceval E (cmd.IfThenElse b c1 c2) E'
| Seq {c1 c2 E E' E''} :
    ceval E c1 E' -> ceval E' c2 E'' ->
    ceval E (cmd.Seq c1 c2) E''
| Skip {E} :
    ceval E cmd.Skip E
| WhileDo_t {E b c E' E''} :
    beval E b true -> ceval E c E' ->
    ceval E' (cmd.WhileDo b c) E'' ->
    ceval E (cmd.WhileDo b c) E''
| WhileDo_f {E b c} :
    beval E b false ->
    ceval E (cmd.WhileDo b c) E
-- V prvo vrstico pišemo predpostavke, v drugo pa končne zaključke na podoben način, kot smo to
-- to počeli v drevesih.

-- ==================== Safety ====================

-- Contains all the names of already assigned locations.
inductive locs : Type
| Nil : locs
| Cons : loc -> locs -> locs
-- Samo doda dodatno ime v okolje, ko to potrebujemo.


inductive loc_safe : loc -> locs -> Prop
| Find {loc L} : 
    loc_safe loc (locs.Cons loc L) 
| Search {loc loc' L} : 
    loc'≠loc -> loc_safe loc L -> 
    loc_safe loc (locs.Cons loc' L)
-- Gre za podoben primer kot prej -> ali je lokacija v glavi ali pa obstaja dokaz za rep

-- Primer l0 l1 l2 l3 l4...
-- l2 ≠ l0, l2 ≠ l1, Find l2 l3 l4 ...


-- Preverjamo, da so ukazi varni v dani specifikaciji
inductive asafe : locs -> aexp -> Prop
| Lookup {L l} :
    loc_safe l L ->
    asafe L (aexp.Lookup l)
| Int {L i} :
    asafe L (aexp.Int i)
| Plus {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Plus a1 a2)
| Minus {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Minus a1 a2)
| Times {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    asafe L (aexp.Times a1 a2)
-- To je torej varno, ko so varna vsa poddrevesa -> enako velja tudi za bool.


inductive bsafe : locs -> bexp -> Prop
| Bool {L b} :
    bsafe L (bexp.Bool b)
| Equal {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Equal a1 a2)
| Less {L a1 a2} :
    asafe L a1 -> asafe L a2 ->
    bsafe L (bexp.Less a1 a2)


inductive csafe : locs -> cmd -> locs -> Prop
| Assign {L l a} :
    asafe L a -> 
    csafe L (cmd.Assign l a) (locs.Cons l L)
-- V L smo varni, če lahko v njem varno izračunamo a, nato pa je posledično varno tudi novo okolje.
-- Edini, ki je zanimiv, saj edini deluje z lokacijami.
--| IfThenElse 
--    bsafe L b -> csafe L c1 L1 -> csafe L c2 L2 ->
--    csafe L (cmd.IfThenElse b c1 c2) (L1 ∩ L2)
-- V tem primeru ne vemo, če je b true ali false, vendar so v resnici varne le lokacije, ki ležijo
-- tako v L1 kot v L2, tj. v preseku, ki pa ga moramo še definirati.
-- Note: This part requires a definition of locs intersection.
| Seq {L c1 L' c2 L''} :
    csafe L c1 L' -> csafe L' c2 L'' ->
    csafe L (cmd.Seq c1 c2) L''
| Skip {L} :
    csafe L (cmd.Skip) L
| WhileDo {L b c L'} :
    bsafe L b -> csafe L c L' ->
    csafe L (cmd.WhileDo b c) L'
-- Za while zanko se v resnici varnosti ne da točno dokazati.

-- ==================== Auxiliary safety for lookup ====================

-- Ensures that the given environment maps all the required locations.
inductive env_maps : env -> locs -> Prop
| Nil {E} :
    env_maps E locs.Nil
| Cons {loc E L} :
    env_maps E L -> (∃i, lookup loc E i) ->
    env_maps E (locs.Cons loc L)
-- Gre za dokaz, za katerega ponavadi ne vemo, da ga moramo dokazati, vendar se pogosto pojavlja
-- v drugih dokazih.


-- Increasing the environment does not break its safety.
-- Izrek, ki ošibi našo specifikacijo -> ker za IP uporabljamo manjše okolje.
theorem env_maps_weaken {E L loc i}:
  env_maps E L -> env_maps (env.Cons loc i E) L
:=
begin
  intro es, induction es with E' loc' E' L' maps finds ih, -- Imena za nove spremenljivke
  case env_maps.Nil
    { apply env_maps.Nil, },
  case env_maps.Cons
    { apply env_maps.Cons, assumption,
    -- Dokazujemo, da okolju L' lahko dodamo loc', s čimer ne izgubimo varnosti.
      -- we compare the the strings to know which lookup result is correct
      cases string.has_decidable_eq loc' loc with neq eq,
      -- Ločimo primera, ko se lokaciji ujemata in ko se ne.
      { cases finds with i', existsi i',
        -- lookup must search deeper 
        apply lookup.Search, assumption, assumption, }, -- Primer, ko se lokaciji ne ujemata.
      existsi i, 
      -- loc' and loc are equal, 'subst eq' will rewrite them to the same name.
      subst eq, apply lookup.Find, }
end


-- If the location is safe in the same specification as the environment
-- then we are guaranteed to look up a value
theorem safe_lookup {L E loc}:
  loc_safe loc L -> env_maps E L -> ∃ (i:int), lookup loc E i
:=
begin
  -- if we have an impossible hypothesis 'h' (such as a safety check in
  -- an empty locs list) we can complete the proof with 'cases h'
  sorry
end

-- ==================== Safety theorems ====================

theorem asafety {L E a}:
  asafe L a -> env_maps E L -> ∃ (i:int), aeval E a i
:=
begin
-- V tem primeru je veliko možnosti za izvajanje indukcije. 
  intros s es,
  induction s,
  case asafe.Lookup
    { cases safe_lookup s_a es with i, 
    -- cases safe_lookup ... applies the theorem and eliminates the ∃ 
      existsi i, apply aeval.Lookup, assumption, },
  case asafe.Int
    { existsi s_i, apply aeval.Int, },
  case asafe.Plus
    { cases s_ih_a es with i1, -- IP uporabimo na argumentu es -> es je dokaz, da je okolje varno
      cases s_ih_a_1 es with i2,
       existsi (i1 + i2), apply aeval.Plus, assumption, assumption,  },
  case asafe.Minus
    { sorry },
  case asafe.Times
    { sorry },
end
-- Enako kot pri Plus imamo tudi pri Minus in Times.


theorem bsafety {L E b}:
  bsafe L b -> env_maps E L -> ∃ (v:bool), beval E b v
:=
begin
  intros s es,
  induction s,
  case bsafe.Bool
    { existsi s_b, apply beval.Bool, },
  case bsafe.Equal
    { cases asafety s_a es with i1,
      cases asafety s_a_1 es with i2,
      cases int.decidable_eq i1 i2 with neq eq,
      -- we cannot just do a case analysis on logical formulas because
      -- we are not using classical logic. Luckily integer equality is
      -- decidable, so we can specify to do a case analysis on that
      -- i1 ≠ i2 -> Equalitiy vrne false
      { existsi ff, apply beval.Equal_f, assumption, assumption, assumption, }, 
      -- Komentar: ff je tipa bool, false pa ima tip PROP
      -- i1 = i2
      { sorry }, },
  case bsafe.Less
    { sorry,
      cases int.decidable_lt i1 i2 with neq eq,
      -- i1 ≰ i2
      { sorry },
      -- i1 < i2
      { sorry }, },
end


theorem csafety {L L' E c }:
  csafe L c L' -> env_maps E L -> ∃ (E':env), ceval E c E' ∧ env_maps E' L'
:=
begin
  -- constructor splits ∧ into two subgoals
  intros s, revert E, -- we revert to obtain a stronger induction
  induction s; intros E es,
  case csafe.Assign
    { cases asafety s_a_1 es with i,
      existsi (env.Cons s_loc i E),
      constructor, -- constructor splits ∧ into two subgoals
      { sorry },
      sorry },
  case csafe.Seq
    { sorry },
  case csafe.Skip
    { sorry },
  case csafe.WhileDo
    { -- this part can't really be done in big step semantics
      sorry },
end