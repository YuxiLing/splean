import SPLean.Extra.ToANF.QqBased

-- for now, use the `Qq`-based version as the standard one
syntax "lang_def'" ident ":=" lang : command

elab_rules : command
  | `(lang_def' $n:ident := $l:lang) => define_anf_val n l
