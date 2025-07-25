import Mathlib

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V}

lemma Walk.mem_concat_support {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    v ∈ (p.concat hadj).support := by
  rw [concat_eq_append, mem_support_append_iff]
  exact Or.inl (end_mem_support p)

end SimpleGraph
