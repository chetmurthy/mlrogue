(* $Id: translate.ml,v 1.27 2015/04/09 15:14:21 deraugla Exp $ *)

module Internal = struct
value string_make = Bytes.make;
value string_set = Bytes.set;
value string_get = Bytes.get;

value lex = "rogue.lexicon";

value lexicon = Hashtbl.create 1;
value lexicon_mtime = ref 0.0;
value lang = ref (Bytes.of_string "");

value add_lexicon word transl =
  let transl =
    match transl with
    [ Some transl -> transl
    | None -> Bytes.of_string ("[" ^ (Bytes.to_string word) ^ "]") ]
  in
  Hashtbl.add lexicon word transl
;

value cut_trail_dot s =
  let len = Bytes.length s in
  if (len >= 3 && Bytes.get s (len-2) = ' ' || len = 1) && Bytes.get s (len-1) = '.' then
    Bytes.sub s 0 (len - 1)
  else s
;

value read_lexicon () = do {
  let ic = open_in lex in
  try
    while True do {
      let s =
        let s = input_line ic in
        cut_trail_dot (Bytes.of_string s)
      in
      let len = Bytes.length s in
      if len >= 4 && Bytes.sub s 0 4 = Bytes.of_string "    " then
        let s = Bytes.sub s 4 (len - 4) in
        if lang.val <> (Bytes.of_string "") then
          loop (Bytes.of_string "") where rec loop default =
            let t = try Some (Bytes.of_string (input_line ic)) with [ End_of_file -> None ] in
            let ti =
              match t with
              [ Some t ->
                  try Some (t, Bytes.index t ':') with
                  [ Not_found -> None ]
              | None -> None ]
            in
            match ti with
            [ Some (t, i) ->
                let line_lang = Bytes.sub t 0 i in
                if line_lang = lang.val ||
                   Bytes.length lang.val > Bytes.length line_lang &&
                   Bytes.sub lang.val 0 (Bytes.length line_lang) =
                     line_lang
                then
                  let t =
                    if i + 2 < Bytes.length t then
                      Bytes.sub t (i + 2) (Bytes.length t - i - 2)
                    else Bytes.of_string ""
                  in
                  let t = cut_trail_dot t in
                  if line_lang = lang.val then add_lexicon s (Some t)
                  else loop t
                else loop default
            | None ->
                add_lexicon s (if default = Bytes.of_string "" then None else Some default) ]
        else add_lexicon s (Some s)
      else ();
    }
  with
  [ End_of_file -> () ];
  close_in ic;
};

value gen_transl glang str = do {
  if Sys.file_exists lex then
    let stbuf = Unix.stat lex in
    if stbuf.Unix.st_mtime > lexicon_mtime.val then do {
      lang.val := glang;
      Hashtbl.clear lexicon;
      lexicon_mtime.val := stbuf.Unix.st_mtime;
      read_lexicon ();
    }
    else ()
  else ();
  Hashtbl.find lexicon str
};

value transl glang str =
  try gen_transl glang str with
  [ Not_found -> if lang.val = Bytes.of_string "" then str
                 else Bytes.of_string ("[" ^ (Bytes.to_string str) ^ "]") ]
;

value fast_transl glang str =
  try Hashtbl.find lexicon str with
  [ Not_found -> transl glang str ]
;

value check_format ini_fmt (r : string) =
  let s : string = string_of_format (ini_fmt : format 'a 'b 'c) in
  let s = Bytes.of_string s in
  let r = Bytes.of_string r in
  let rec loop i j =
    if i < Bytes.length s - 1 && j < Bytes.length r - 1 then
      match (Bytes.get s i, Bytes.get s (i + 1), Bytes.get r j, Bytes.get r (j + 1)) with
      [ ('%', x, '%', y) ->
          if x = y then loop (i + 2) (j + 2) else None
      | ('%', _, _, _) -> loop i (j + 1)
      | (_, _, '%', _) -> loop (i + 1) j
      | _ -> loop (i + 1) (j + 1) ]
    else if i < Bytes.length s - 1 then
      if Bytes.get s i = '%' then None else loop (i + 1) j
    else if j < Bytes.length r - 1 then
      if Bytes.get r j = '%' then None else loop i (j + 1)
    else
      Some (Scanf.format_from_string (Bytes.to_string r) ini_fmt : format 'a 'b 'c)
  in
  loop 0 0
;

value tnf s = "[" ^ s ^ "]";

value valid_format ini_fmt r =
  match check_format ini_fmt r with
  | Some fmt -> fmt
  | None -> Scanf.format_from_string (tnf (string_of_format ini_fmt)) ini_fmt
  end
;

value ftransl glang (fmt : format 'a 'b 'c) =
  let sfmt : string = string_of_format fmt in
  try valid_format fmt (Bytes.to_string (gen_transl glang (Bytes.of_string sfmt))) with
  [ Not_found ->
      if lang.val = Bytes.of_string "" then fmt
      else
        (Scanf.format_from_string ("[" ^ sfmt ^ "]") fmt : format 'a 'b 'c) ]
;

value erase str i j =
  Bytes.cat (Bytes.sub str 0 i) (Bytes.sub str j (Bytes.length str - j))
;

(*
 * eval_set scans strings of the form @(x) where x is a list of characters
 * meaning a predicate to set for each character. Fills [set], the set of
 * predicates. Treats also the special case for @(&) = delete the next
 * character if any.
 *)

value eval_set str =
  loop [] str 0 where rec loop set str i =
    if i + 3 < Bytes.length str then
      if Bytes.get str i = '@' && Bytes.get str (i+1) = '(' && Bytes.get str (i+3) <> '?' &&
         Bytes.get str (i+3) <> '-'
      then
        if Bytes.get str (i+2) = '&' && Bytes.get str (i+3) = ')' && i + 4 < Bytes.length str
        then
          loop set (erase str i (i + 5)) i
        else
          let (set, j) =
            loop set (i + 2) where rec loop set i =
              if i < Bytes.length str then
                if Bytes.get str i <> ')' then loop [Bytes.get str i :: set] (i + 1)
                else (set, i + 1)
              else (set, i)
          in
          loop set (erase str i j) i
      else loop set str (i + 1)
    else (set, str)
;

value rec apply_expr set str i =
  if i + 1 < Bytes.length str && Bytes.get str (i+1) = '?' then
    if List.mem (Bytes.get str i) set then
      let str = erase str i (i + 2) in
      let (str, i) = apply_expr set str i in
      if i < Bytes.length str && Bytes.get str i = ':' then
        let (str, j) = apply_expr set str (i + 1) in
        (erase str i j, i)
      else (str, i)
    else
      let (str, j) = apply_expr set str (i + 2) in
      let str = erase str i j in
      if i < Bytes.length str && Bytes.get str i = ':' then
        let str = erase str i (i + 1) in
        apply_expr set str i
      else (str, i)
  else if i < Bytes.length str && (Bytes.get str i = ':' || Bytes.get str i = ')') then
    (str, i)
  else apply_expr set str (i + 1)
;

(*
 * eval_app scans strings matching expressions between @( and ).
 *    an expression is:
 *     - a [character] followed by "?", an [expression] and possibly ":" and
 *       [another expression]
 *     - any [string] not holding ":"
 *    The [character] is a predicate. If defined, the first expression is
 *    evaluated, else it is the second one. The evaluation of a string is
 *    itself.
 *
 *  ex: p?e:m?A?en:er:w?e:n?es
 *    In this example, if m and A are only defined predicates:
 *      p not being defined, it is m?A?en:er:w?e:n?es
 *      m being defined, it is A?en:er
 *      A being defined, it is en
 *    This example shows how to display adjectives in German, where
 *    m is for masculine, w for feminine and n for neuter
 *)

value eval_app set str =
  loop str 0 where rec loop str i =
    if i + 3 < Bytes.length str then
      if Bytes.get str i = '@' && Bytes.get str (i+1) = '(' && Bytes.get str (i+3) <> '-' then (
        let str = erase str i (i + 2) in
        let (str, i) = apply_expr set str i in
        if i < Bytes.length str then
          if Bytes.get str i = ')' then loop (erase str i (i + 1)) i
          else loop str i
        else str
      )
      else loop str (i + 1)
    else str
;

(*
 * eval_shift scans strings matching:
 *   @(#-) shifting # words of the left after the next word.
 *   @(#--) shifting # words of the left to the end.
 * ex:
 *   before: "Une avec un diamant@(3-) bague"
 *    after: "Une bague avec un diamant"
 *   before: "Sie haben geworfen@(1--) einen kurzen Bogen"
 *    after: "Sie haben einen kurzen Bogen geworfen"
 *)

value rec eval_shift s =
  let t = string_make (Bytes.length s) '#' in
  loop False 0 0 where rec loop changed i j =
    if i + 4 < Bytes.length s && Bytes.get s i = '@' && Bytes.get s (i+1) = '(' &&
       Bytes.get s (i+3) = '-'
    then
      let nleft = Char.code (Bytes.get s (i+2)) - Char.code '0' in
      let to_the_end = Bytes.get s (i+4) = '-' in
      let k = if to_the_end then i + 5 else i + 4 in
      if k < Bytes.length s && Bytes.get s k = ')' then (
        let l =
          loop nleft (i - 1) where rec loop nleft l =
            if l > 0 then
              if Bytes.get s l = ' ' then
                if nleft <= 1 then l + 1
                else loop (nleft - 1) (l - 1)
              else loop nleft (l - 1)
            else 0
        in
        let len = i - l in
        let j = j - len in
        let k = k + 1 in
        let i = if k < Bytes.length s && Bytes.get s k = ' ' then k + 1 else k in
        let (i, j) =
          if to_the_end then
            loop i j where rec loop i j =
              if i < Bytes.length s then do {
                string_set t j (Bytes.get s i);
                loop (i + 1) (j + 1)
              }
              else do {
                let j =
                  if string_get t (j-1) <> ' ' then do { string_set t j ' '; j + 1 }
                  else j
                in
                Bytes.blit s l t j len;
                (i, j + len)
              }
          else
            loop i j where rec loop i j =
              if i < Bytes.length s then
                if Bytes.get s i = ' ' then do {
                  string_set t j ' ';
                  Bytes.blit s l t (j + 1) len;
                  (i, j + 1 + len)
                }
                else do {
                  string_set t j (Bytes.get s i);
                  loop (i + 1) (j + 1)
                }
              else if k < Bytes.length s && Bytes.get s k = ' ' then do {
                string_set t j ' ';
                Bytes.blit s l t (j + 1) len;
                (i, j + 1 + len)
              }
              else do {
                Bytes.blit s l t j len;
                (i, j + len)
              }
        in
        loop True i j
      )
      else do {
        string_set t j (Bytes.get s i);
        loop changed (i + 1) (j + 1)
      }
    else if i < Bytes.length s then do {
      string_set t j (Bytes.get s i);
      loop changed (i + 1) (j + 1)
    }
    else if changed then eval_shift (Bytes.sub t 0 j)
    else Bytes.sub t 0 j
;

(* etransl make grammatical transformations indicated inside strings
   between "@(" and ")". This system allows e.g. to conjugate articles,
   nouns, adjectives, verbs, to put adjectives after nouns, to put verbs
   at the end of the sentence, things like that. Useful at least in
   French (fr:) and German (de:).
     The idea is simple: some parts of the sentence set predicates
   and other parts generate strings depending on these predicates.
   A predicate is synctactically a character and semantically what
   the user wants: "this noun is masculine", "this verb expects
   accusative", and so on.
     The syntax to set the predicate x is @(x).
     The syntax of evaluation is between @( and ) and looks like
   the C expression x?y:z which can be use recursively. It can be
   also indications to shift words.

     Example in German. The concatenation of phrases:
       Sie haben geworfen@(A)@(1--)      (You dropped)
       ein@(w?e:A?m?en)                  (a)
       +1,+0
       kurz@(A?en:er) Bogen@(m)          (short bow)
   gives the initial sentence:

 Sie haben geworfen@(A)@(1--) ein@(w?e:A?m?en) +1,+0 kurz@(A?en:er) Bogen@(m)

   1/ First step ("eval_set") extracts the predicates. Here, the set
      predicates are "A" and "m" (User semantics of "A" is "this
      verb expects accusative" and "m" is "this noun is masculine").

 Sie haben geworfen@(A)@(1--) ein@(w?e:A?m?en) +1,+0 kurz@(A?en:er) Bogen@(m)
                   ^^^^                                                  ^^^^
      resulting string (predicates deleted):
 Sie haben geworfen@(1--) ein@(w?e:A?m?en) +1,+0 kurz@(A?en:er) Bogen

    2/ Second step ("eval_app") evaluates the expressions of the form
       x?y:z:

 Sie haben geworfen@(1--) ein@(w?e:A?m?en) +1,+0 kurz@(A?en:er) Bogen
                             ^^^^^^^^^^^^^           ^^^^^^^^^^
     Expression @(w?e:A?m?en) is read: if predicate "w" is set then "e"
     else if predicate "A" is set then if predicate "m" is set then "en"
     (else nothing). Semantically, it means that if the noun is feminine
     (weiblich in German), the result is "e" (word is "eine") else if the
     noun is masculine and if the accusative form is expected, the result
     is "en" (word is "einen") else nothing (word is "ein").
       The second expression @(A?en:er) returns here "en" (word "kurzen").
     Resulting string:

       Sie haben geworfen@(1--) einen +1,+0 kurzen Bogen

    3/ Third step ("eval_shift") applies the shift predicates. Here,
       @(1--) means put "1" word on the left to the end of the
       sentence. Result:

       Sie haben einen +1,+0 kurzen Bogen geworfen
*)

value etransl str =
  let (set, str) = eval_set str in
  let str = eval_app set str in
  eval_shift str
;

value translc lang c =
  let s = transl lang (Bytes.make 1 c) in
  if Bytes.length s = 1 then Bytes.get s 0 else c
;

value clear_lexicon lang = do {
  Hashtbl.clear lexicon;
  lexicon_mtime.val := 0.0;
};

end ;

value ftransl a b = Internal.ftransl (Bytes.of_string a) b ;
value transl a b = Bytes.to_string (Internal.transl (Bytes.of_string a) (Bytes.of_string b)) ;
value translc a b = Internal.translc (Bytes.of_string a) b ;
value etransl a = Bytes.to_string (Internal.etransl (Bytes.of_string a)) ;
value clear_lexicon a = Internal.clear_lexicon (Bytes.of_string a) ;
value fast_transl a b = Bytes.to_string (Internal.fast_transl (Bytes.of_string a) (Bytes.of_string b)) ;
