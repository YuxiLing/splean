import SPLean.Extra.ToANF.ASTBased
import SPLean.Extra.ToANF.QqBased

open trm val prim

section Tests

open Lean Meta Elab Command in
elab tk:"#anf_diff_test" ppSpace t:term : command => do
  match t with
  | `([lang| $l:lang ]) =>
    let (e1, res) ← liftTermElabM do
      let e1 ← anf_meta l
      let e2 ← Term.elabTerm (← `($(mkIdent ``ANF.anf_toplevel) [lang| $l])) (mkConst ``val)
      let res ← isDefEq e1 e2
      pure (e1, res)
    unless res do
      throwError "something went wrong. the result from meta ANF: {e1}"
    logInfoAt tk m!"{e1}"
  | _ => throwAbortCommand

-- for debugging
local macro "lang_def'" n:ident ":=" l:lang : command => do
  `(def $n:ident : val := reduce_skip_val% (ANF.anf_toplevel [lang| $l])
    #print $n:ident)

#anf_diff_test [lang|
  fun i =>
    if i < 0 then (- 1) * i else i
]

#anf_diff_test [lang|
  fun p i =>
    !((p ++ 1) ++ i)
]

#anf_diff_test [lang|
  fun p i v =>
    ((p ++ 1) ++ i) := v
]

#anf_diff_test [lang|
  fun p i =>
    if (val_abs i) < (val_array_length p) then
      val_array_get p n
    else
      d
]

#anf_diff_test [lang|
  fun p i v =>
    if (val_abs i) < (val_array_length p) then
      val_array_set p i v
    else
      ()
]

#anf_diff_test [lang|
  fix f p i n v =>
    if (n > 0) then
      ((val_array_set p) i) v ;
      f p (i + 1) (n - 1) v
    end
]

#anf_diff_test [lang|
  fun p =>
    p := (!p) + 1
]

-- WARNING: these tests are not exhaustive

end Tests
