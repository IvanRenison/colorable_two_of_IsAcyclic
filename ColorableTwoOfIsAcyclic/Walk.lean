import Mathlib

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V}

lemma Walk.eq_iff_support_eq {u v : V} (p q : G.Walk u v) :
    p = q ↔ p.support = q.support := by
  sorry

lemma Walk.mem_concat_support {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    v ∈ (p.concat hadj).support := by
  rw [Walk.concat_eq_append]
  rw [Walk.mem_support_append_iff]
  left
  exact Walk.end_mem_support p

end SimpleGraph
