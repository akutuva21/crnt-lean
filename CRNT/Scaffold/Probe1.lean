import Mathlib.Data.Fin.Basic
open Mathlib

example {n : ℕ} (i : Fin n) : Fin.castSucc i = i.succ := rfl

example {n : ℕ} (i : Fin n) (f : Fin (n+1) → Bool) : f (Fin.castSucc i) = f i.succ := rfl
