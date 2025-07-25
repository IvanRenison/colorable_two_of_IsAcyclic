import Mathlib
import ColorableTwoOfIsAcyclic.List
import ColorableTwoOfIsAcyclic.Walk
import ColorableTwoOfIsAcyclic.Path

namespace SimpleGraph

variable {V : Type} {G : SimpleGraph V}

lemma diff_dist_adj (u v w : V) (hG : G.Connected) (hadj : SimpleGraph.Adj G v w) :
    G.dist u w = G.dist u v ∨ G.dist u w = G.dist u v + 1 ∨ G.dist u w = G.dist u v - 1 := by
  have hdistvw : G.dist v w = 1 := dist_eq_one_iff_adj.mpr hadj
  by_cases huv : u = v
  · simp only [huv, hdistvw, G.dist_self, or_true, true_or]
  have hdistuv : 0 < G.dist u v := hG.pos_dist_of_ne huv
  have h1 : G.dist u w ≤ G.dist u v + G.dist v w := hG.dist_triangle
  rw [hdistvw] at h1
  have h2 : G.dist u v ≤ G.dist u w + G.dist w v := hG.dist_triangle
  rw [dist_eq_one_iff_adj.mpr (G.adj_symm hadj)] at h2
  obtain h | h | h := lt_trichotomy (G.dist u v) (G.dist u w)
  · right
    left
    linarith
  · simp [h]
  · right
    right
    omega

lemma Walk.IsPath.concat_ofIsPath {u v w : V} {p : G.Walk u v} (hp : p.IsPath) (hadj : G.Adj v w)
    (hw : w ∉ p.support) : (p.concat hadj).IsPath := by
  refine Walk.IsPath.mk' ?_
  rw [Walk.support_concat, List.nodup_concat]
  constructor
  · exact hw
  · rw [isPath_def] at hp
    assumption

-- Not used
lemma IsTree.walk_length_eq_dist_of_IsPath (hG : G.IsTree) {u v : V} {p : G.Walk u v}
    (hp : p.IsPath) : p.length = G.dist u v := by
  obtain ⟨q, hq, hq'⟩ := hG.isConnected.exists_path_of_dist u v
  have hpq := isAcyclic_iff_path_unique.mp hG.IsAcyclic ⟨p, hp⟩ ⟨q, hq⟩
  simp at hpq
  rw [hpq]
  exact hq'

-- Not used
lemma IsTree.IsPath_iff_walk_length_eq_dist (hG : G.IsTree) {u v : V} (p : G.Walk u v) :
    p.IsPath ↔ p.length = G.dist u v :=
  Iff.intro hG.walk_length_eq_dist_of_IsPath p.isPath_of_length_eq_dist


lemma IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
  {p : G.Walk u v} {q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w) (hv : v ∉ q.support) :
    w ∈ p.support := by
  let r := q.concat hadj.symm
  have hr : r.IsPath := hq.concat_ofIsPath hadj.symm hv
  have h := isAcyclic_iff_path_unique.mp hG ⟨p, hp⟩ ⟨r, hr⟩
  simp at h
  rw [h]
  unfold r
  exact q.mem_concat_support hadj.symm

lemma IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hw : w ∈ p.support) : v ∉ q.support := by
  obtain ⟨p₀, p₁, hp₀, hp₁, happend⟩ := hp.mem_support_iff_exists_append.mp hw
  have hp₀p₁ : (p₀.append p₁).IsPath := by
    rw [← happend]
    exact hp
  have hvw : v ≠ w := hadj.symm.ne'
  have hvp₁ : v ∈ p₁.support := p₁.end_mem_support
  have hp₀q := hG.path_unique ⟨p₀, hp₀⟩ ⟨q, hq⟩
  simp only [Subtype.mk.injEq] at hp₀q
  rw [← hp₀q]
  exact hp₀p₁.not_mem_left_of_mem_right_of_ne_of_IsPath_append hvw hvp₁

lemma IsAcyclic.mem_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V} {p : G.Walk u v}
    {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w) :
    v ∈ q.support ↔ w ∉ p.support := by
  apply Iff.intro (hG.ne_mem_support_of_support_of_adj_of_isPath hq hp hadj.symm)
    (hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp hadj.symm)


lemma IsAcyclic.path_concat (hG : G.IsAcyclic) {u v w : V} {p : G.Walk u v} {q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w) (hv : v ∈ q.support) :
    q = p.concat hadj := by
  have hw : w ∉ p.support := hG.ne_mem_support_of_support_of_adj_of_isPath hq hp hadj.symm hv
  have hpw : (p.concat hadj).IsPath := hp.concat_ofIsPath hadj hw
  have h := isAcyclic_iff_path_unique.mp hG ⟨q, hq⟩ ⟨p.concat hadj, hpw⟩
  simp at h
  exact h

lemma IsTree.dist_ne_of_adj (hG : G.IsTree) (u : V) {v w : V} (hadj : SimpleGraph.Adj G v w) :
    G.dist u v ≠ G.dist u w := by
  obtain ⟨p, hp, hp'⟩ := hG.isConnected.exists_path_of_dist u v
  obtain ⟨q, hq, hq'⟩ := hG.isConnected.exists_path_of_dist u w
  rw [← hp', ← hq']
  by_cases hw : w ∈ p.support
  · have hp : p = q.concat hadj.symm := hG.IsAcyclic.path_concat hq hp hadj.symm hw
    rw [hp]
    rw [q.length_concat]
    exact q.length.ne_add_one.symm
  · have hv : v ∈ q.support := hG.IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp
      hadj.symm hw
    have h : (p.concat hadj).IsPath := by
      rw [← hG.IsAcyclic.path_concat hp hq hadj hv]
      exact hq
    have hq : q = p.concat hadj := hG.IsAcyclic.path_concat hp hq hadj hv
    rw [hq, p.length_concat]
    exact p.length.ne_add_one

lemma IsTree.diff_dist_adj (hG : G.IsTree) (u v w : V) (hadj : SimpleGraph.Adj G v w) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u v + 1 = G.dist u w := by
  have h := SimpleGraph.diff_dist_adj u v w hG.isConnected hadj
  have hne := hG.dist_ne_of_adj u hadj
  rcases h with h₁ | h₂ | h₃
  · exfalso
    apply hne
    rw [h₁]
  · right
    exact h₂.symm
  · left
    have : 0 < G.dist u v := hG.isConnected.pos_dist_of_ne (by
      intro h
      subst h
      have h₁ := dist_eq_one_iff_adj.mpr hadj
      rw [dist_self] at h₃
      simp only [Nat.zero_sub] at h₃
      rw [h₃] at h₁
      exact absurd h₁ (by norm_num))
    rw [h₃]
    exact Eq.symm (Nat.sub_add_cancel this)

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

variable [inst : Nonempty V]

noncomputable def IsTree.coloring_two (hG : G.IsTree) : G.Coloring (Fin 2) :=
  let u : V := Classical.choice inst
  hG.coloring_two_of_elem u

lemma IsTree.colorable_two (hG : G.IsTree) : G.Colorable 2 :=
  Nonempty.intro hG.coloring_two

end SimpleGraph
