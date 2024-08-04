-- import Ssreflect.Lang
import Mathlib.Data.Finmap

import Lgtm.Util
import Lgtm.HProp
import Lgtm.HHProp
import Lgtm.XSimp

section HSepLog

open Classical

variable {α : Type} [DecidableEq α]

def htrm := α -> trm
def hval := α -> val

local notation "hheap" => @hheap α
local notation "hhProp" => @hhProp α
local notation "htrm" => @htrm α
local notation "hval" => @hval α

open trm val

def heval_nonrel (S : Set α) (hh : hheap) (ht : htrm) (hQ : α -> val -> hProp) : Prop :=
  ∀ s ∈ S, eval (hh s) (ht s) (hQ s)

def bighstarDef (s : Set α) (hH : α -> hProp) (h₀ : hheap) : hhProp :=
  [∗ i in s| hH i] ∗ [∗ i in s.compl| (· = h₀ i)]

def heval (S : Set α) (hh : hheap) (ht : htrm) (hQ : hval -> hhProp) : Prop :=
  ∃ (hQ' : α -> val -> hProp),
    heval_nonrel S hh ht hQ' ∧
    ∀ hv, bighstarDef S (fun s => hQ' s (hv s)) hh ==> hQ hv

end HSepLog
