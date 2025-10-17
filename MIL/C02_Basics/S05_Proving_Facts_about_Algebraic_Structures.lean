import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- 偏序是一个集合 + 一个二元关系 ≤
-- 满足自反性、反对称性、传递性
-- 但其中可能有元素不能比较大小

-- 严格偏序
-- 不包含相等的情况
-- 比如真子集

-- 全序
-- 还要满足完全性 对于集合内任意两个元素 x 和 y
-- 要么x ≤ y， 要么y ≤ x（或者两者都成立，即x=y）

#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)


#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  apply le_inf
  trans x⊓y
  -- 看懂trans了！trans是制造一个中间项表示传递关系
  repeat
    apply inf_le_left
  apply le_inf
  trans x⊓y
  apply inf_le_left
  apply inf_le_right
  apply inf_le_right
  repeat
    apply le_inf
  apply inf_le_left
  trans y⊓z
  apply inf_le_right
  apply inf_le_left
  trans y⊓z
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  repeat
    apply sup_le
  apply le_sup_left
  trans y⊔z
  apply le_sup_left
  apply le_sup_right
  trans y⊔z
  repeat
    apply le_sup_right
  apply sup_le
  trans x⊔y
  repeat
    apply le_sup_left
  apply sup_le
  trans x⊔y
  apply le_sup_right
  apply le_sup_left
  apply le_sup_right

-- 这两坨可读性极差，因为发现不写· 也很方便
-- 只要按顺序解决目标

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  apply inf_le_left
  apply le_inf
  apply le_refl
  apply le_sup_left


theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  apply sup_le
  apply le_refl
  apply inf_le_left
  apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

-- 偏序只保证元素间的顺序关系
-- 而格（Lattice）中的任意两个元素x 和 y，
-- 都存在一个唯一的“上确界”和“下确界”
-- x⊓y 最大下界（GLB），下确界（infimum），交（meet）（min）
-- x⊔y 最小上界（LUB），上确界（infimum），并（join）（max）

-- 一个格 = 偏序集合 + 任意两个元素都有 meet 和 join
-- e.g. 实数是一个格，其中 ⊓ 是min， ⊔ 是max
-- e.g. 正整数中“能整除”是一个格，其中 ⊓ 是gcd， ⊔ 是lcm


-- 使用trans而不是le_trans
-- 就不会生成讨厌的占位符

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw[h, inf_comm (a⊔b), absorb1, inf_comm (a⊔b), h, ← sup_assoc, inf_comm c b, inf_comm c a, absorb2 ]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw[h, sup_comm (a⊓b) a, absorb2, sup_comm (a⊓b) c, h, ← inf_assoc, sup_comm c a, absorb1, sup_comm c b]

-- 完全想不到下一步要干什么……尝试定理中……
-- 最后发现换来换去就是为了凑出absorb的两个定理，只有它们可以减少字母

end

section
variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a :=
  have h1: 0+a≤ b-a+a := by
    rw[zero_add, sub_add_cancel b]
    exact h
  le_of_add_le_add_right h1

-- le_of_add_le_add_right h1这行不用加apply？

example (h: 0 ≤ b - a) : a ≤ b := by
  rw[← zero_add a, ← sub_add_cancel b a]
  apply add_le_add_right h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1:0≤(b-a)*c := by
    apply mul_nonneg
    rw [← sub_nonneg] at h
    exact h
    exact h'
  rw[sub_mul] at h1
  rw [← add_zero (a*c)]
  rw[← sub_add_cancel (b*c) (a*c)]
  rw[add_comm (b*c-a*c) (a*c)]
  apply add_le_add_left
  exact h1

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

-- linarith 只能处理线性
-- 非线性的东西可以作为参数告诉它[]

example (x y : X) : 0 ≤ dist x y := by
  have h: dist x x≤ dist x y+dist y x:=by
    apply dist_triangle x y x
  rw[dist_self x, dist_comm y x] at h
  linarith

-- 有时想不到定理的时候直接试试linarith

end
