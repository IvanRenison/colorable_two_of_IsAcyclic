import Mathlib

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V} [inst : Nonempty V]

lemma IsTree.diff_dist_adj (hG : G.IsTree) (u v w : V) (hadj : SimpleGraph.Adj G v w) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u v + 1 = G.dist u w :=

  sorry

noncomputable def IsTree.coloring_two_of_elem (hG : G.IsTree) (u : V) : G.Coloring (Fin 2) :=
  Coloring.mk (fun v ↦ ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩) <| by
  intro v w hadj h
  simp only [Fin.mk.injEq] at h
  have := hG.diff_dist_adj u v w hadj
  obtain hA | hB := hG.diff_dist_adj u v w hadj
  · rw [hA] at h
    omega
  · rw [← hB] at h
    omega


noncomputable def IsTree.coloring_two (hG : G.IsTree) : G.Coloring (Fin 2) :=
  let u : V := Classical.choice inst
  hG.coloring_two_of_elem u

lemma IsTree.colorable_two (hG : G.IsTree) : G.Colorable 2 :=
  Nonempty.intro hG.coloring_two

end SimpleGraph
