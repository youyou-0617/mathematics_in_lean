import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Basic

-- Prop是Lean中的一种类型，用于表示逻辑命题（True/False）
def IsUpperBound (A : Set ℝ) (b : ℝ) :
  Prop :=
  ∀ a ∈ A, a ≤ b
  -- 当集合A中的所有元素都≤b时，b是集合A的上界


def IsSup (A : Set ℝ) (s : ℝ) :
  Prop :=
  -- (i) s 是 A 的一个上界
  (IsUpperBound A s) ∧
  -- (ii) 如果 b 是 A 的任意一个上界，那么 s ≤ b
  (∀ b, IsUpperBound A b → s ≤ b)
  -- s是A的上确界（最小上界）


axiom CompletenessAxiom (A : Set ℝ) (h_nonempty : A.Nonempty)
(h_bdd : ∃ b, IsUpperBound A b) :
  ∃ s, IsSup A s
  -- 实数的完备性公理：任何非空且有上界的实数集都有上确界


-- ？？？
theorem sup_iff_forall_epsilon (A : Set ℝ) (s : ℝ) (h_upper : IsUpperBound A s) :
  IsSup A s ↔ ∀ ε > 0, ∃ a ∈ A, s - ε < a := by
  constructor
  intro h_sup ε hε
  have : ¬IsUpperBound A (s - ε) := by
    intro H -- 假设 s - ε 是上界
    have : s ≤ s - ε := h_sup.right (s - ε) H --由于 s 是上确界，根据第二个条件：s 必须 ≤ 任何上界
    linarith -- 但 ε > 0，所以 s ≤ s - ε 意味着 ε ≤ 0，矛盾
  -- 根据上界定义的否定：存在 a ∈ A 使得 ¬(a ≤ s - ε)，即 s - ε < a
  simpa [IsUpperBound, not_forall] using this -- ¬IsUpperBound A (s - ε)
  intro h
  constructor
  exact h_upper
  intro b hb
  by_contra! H  -- H: s > b
  set ε := s - b with hε_def
  have hε_pos : ε > 0 := by linarith
  rcases h ε hε_pos with ⟨a, ha, ha'⟩
  have : a ≤ b := hb a ha
  linarith



  -- 当且仅当对于任意的ε，都有A中的元素a使得s-ε < a时s是A的上确界(s是“最紧”的上界)

  -- s 的类型是从 ℕ 到 ℝ 的函数 (序列)
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≤ N, |s n - a| < ε
  -- 收敛的定义：当且仅当对任意的ε，都有N使得当n≥N时|s n - a| < ε

theorem monotone_increasing_bounded_converges (x : ℕ → ℝ)
(h_mono : Monotone x) (h_bdd_above : ∃ b, IsUpperBound (Set.range x) b) :
∃ s, IsSup (Set.range x) s ∧ ConvergesTo x s := by
  have h_nonempty : (Set.range x).Nonempty := by
    use (x 0)
    simp
    --apply Set.mem_range_self
  have h_sup : ∃ s, IsSup (Set.range x) s := by
    apply CompletenessAxiom
    apply h_nonempty
    exact h_bdd_above
  rcases h_sup with ⟨s, hs⟩ -- rcases解构“存在∃ ”
  use s, hs
  intro ε hε
  let hup := hs.left
  rw[sup_iff_forall_epsilon] at hs
  rcases hs ε hε with ⟨a, ha⟩ --a ∈ Set.range x的定义是存在n使得x n=a
  rcases ha with ⟨⟨ N, hN⟩, h1⟩
  use N
  intro n hn
  have h2: x n - s ≤ 0 := by
    simp
    apply hup
    simp
  rw[abs_of_nonpos]
  rw[neg_sub]
  have h3: x n ≤ x N := by
    apply h_mono hn
  apply h2
  apply hup




  -- 单调有界收敛定理
  -- 当序列x是单调递增的且序列x有上界，存在极限s既是值域的上确界，又是序列的极限
  -- 已经证明了序列不为空

theorem monotone_increasing_bounded_converges (x : ℕ → ℝ)
    (h_mono : Monotone x) (h_bdd_above : ∃ b, IsUpperBound (Set.range x) b) :
    ∃ s, IsSup (Set.range x) s ∧ ConvergesTo x s := by
  obtain ⟨s, hsup⟩ := CompletenessAxiom (Set.range x) ⟨x 0, 0, rfl⟩ h_bdd_above
  use s, hsup; intro ε εpos
  obtain ⟨_, ⟨i, rfl⟩, _⟩ := (sup_iff_forall_epsilon _ _ hsup.1).mp hsup ε εpos
  use i; intro n ilen
  rw [abs_of_nonpos] <;> linarith [h_mono ilen, hsup.1 (x n) ⟨n, rfl⟩]

  -- 这个有啥问题？
  -- 证明from yxm
