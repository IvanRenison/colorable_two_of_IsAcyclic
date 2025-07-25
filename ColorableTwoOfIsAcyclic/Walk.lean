import Mathlib

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V}

lemma Walk.mem_support_concat_of_mem_support {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w)
    {x : V} (hx : x ∈ p.support) : x ∈ (p.concat hadj).support := by
  rw [concat_eq_append, mem_support_append_iff]
  exact Or.inl hx

lemma Walk.start_mem_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    u ∈ (p.concat hadj).support :=
  p.mem_support_concat_of_mem_support hadj p.start_mem_support

lemma Walk.mem_end_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    w ∈ (p.concat hadj).support := by
  rw [concat_eq_append, mem_support_append_iff]
  exact Or.inr (cons hadj nil).end_mem_support

lemma Walk.end_mem_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    v ∈ (p.concat hadj).support :=
  p.mem_support_concat_of_mem_support hadj (end_mem_support p)

end SimpleGraph
