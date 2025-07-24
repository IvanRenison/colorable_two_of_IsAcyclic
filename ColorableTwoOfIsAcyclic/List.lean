import Mathlib

variable {V : Type}

lemma List.nodup_concat (l : List V) (u : V) : (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup := by
  rw [← List.nodup_reverse]
  simp
