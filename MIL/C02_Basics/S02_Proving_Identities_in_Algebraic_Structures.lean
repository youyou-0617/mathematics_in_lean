import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]
-- 这边怎么用{}了

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

-- If you are paying careful attention,
-- you may have noticed that we changed the
-- round brackets in (R : Type*) for curly brackets in {R : Type*}.
-- This declares R to be an implicit argument.
-- 好的等一下解释

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc a, add_neg_cancel, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← add_neg_cancel_right b a]
  rw [← add_neg_cancel_right c a]
  rw [add_comm b a, add_comm c a, h]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b]
  rw [← add_neg_cancel_right c b]
  rw [h]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a  = 0 + 0 * a := by
    rw[← add_mul, zero_add, zero_add]
  rw [add_right_cancel h]

-- 感觉这个have好神奇
-- 相当于拆分一个阶段小目标！！然后rw实现


theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  rw [← neg_add_cancel_left b a, add_comm b a, h, add_zero]

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

-- 这个apply稍微有点没懂
-- 是不是目标符合这个定理就把目标变成了neg_eq_of_add_eq_zero的条件
-- 然后证明条件h

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_neg_add, neg_add_cancel]

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]


end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

-- 如果你觉得自大，试着证明以下关于群体的事实，
-- 只使用这些公理。一路走来，你需要证明一些帮助引理。
-- 我们在本节中进行的证明提供了一些提示。
-- 我不自大可以放过我吗。

theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  have h : a * a⁻¹ * a = 1 * a := by
    rw [mul_assoc a a⁻¹ a, inv_mul_cancel a, mul_one, one_mul]
  rw [mul_right_cancel h]

-- 感觉到这才搞明白一点have怎么用
theorem mul_one (a : G) : a * 1 = a := by
  have h : a * 1 * a = a * a := by
    rw [mul_assoc, one_mul]
  rw [mul_right_cancel h]

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  have h : (a * b)⁻¹ * (a * b) = b⁻¹ * a⁻¹ * (a * b) := by
    rw [inv_mul_cancel, ← mul_assoc, mul_assoc b⁻¹ a⁻¹ a, inv_mul_cancel]
    rw [mul_assoc, one_mul, inv_mul_cancel]
  rw [mul_right_cancel h]

-- 没有看答案纯手写版，感觉应该绕了很多圈，但总算写出来了
end MyGroup

end
