import Mathlib

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V}

lemma Walk.IsPath.mem_support_iff_exists_append {u v w : V} {p : G.Walk u v} (hp : p.IsPath) :
    w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), q.IsPath ∧ r.IsPath ∧ p = q.append r := by
  apply Iff.intro
  · intro hw
    obtain ⟨q, r, hqr⟩ := p.mem_support_iff_exists_append.mp hw
    have hqr' : (q.append r).IsPath := by
      rw [← hqr]
      exact hp
    have hq : q.IsPath := hqr'.of_append_left
    have hr : r.IsPath := hqr'.of_append_right
    exact ⟨q, r, hq, hr, hqr⟩
  · intro ⟨q, r, hq, hr, hqr⟩
    exact p.mem_support_iff_exists_append.mpr ⟨q, r, hqr⟩

lemma Walk.IsPath.not_mem_left_of_mem_right_of_ne_of_IsPath_append {u v w : V} {p : G.Walk u v}
    {q : G.Walk v w} (hpq : (p.append q).IsPath) {x : V} (hxv : x ≠ v) (hxq : x ∈ q.support) :
    x ∉ p.support := by
  intro hxp
  have hp : p.IsPath := of_append_left hpq
  have hq : q.IsPath := of_append_right hpq
  exact hpq.ne_of_mem_support_of_append hxv hxp hxq rfl

end SimpleGraph
