import MIL.Common
import Mathlib.Data.Real.Basic
-- An example.
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

-- Try these.
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [←  mul_assoc a b c]
  rw [mul_comm a b]
  rw[mul_assoc b a c]

-- An example.
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]

/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw[← mul_assoc]
  rw[mul_comm a b]
  rw[mul_assoc b a c ]
  rw[mul_comm a c]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw[← mul_assoc]
  rw[mul_comm a b]
  rw[mul_assoc b a c]

-- Using facts from the local context.
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
-- rw [h', ← mul_assoc, h, mul_assoc]其实是要写这个

--mul_assoc a b c可以指定修改对象
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw[mul_assoc a b c]
  rw[mul_assoc a e f]
  rw[h]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw[hyp]
  rw[mul_comm b a]
  rw[hyp']
-- a * b - a * b = 0 不会证这个神奇的步骤
-- 看书了
  rw[sub_self]

example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

section

--variable可以在括号外定义类型，用section/end分开
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]

end

section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end

section
variable (a b : ℝ)

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add]
-- 忘记mul_add了，发现可以单独拆开这行看一下
-- 好像光标点一下就能看
  rw [add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
-- 这个稍微有点绕

-- calc A=B
--    sorry
--       =C
--       =D

-- ？下面居然有拆解
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a*a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]

-- 确实calc一开始比较难写
end

-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

-- 纯rw
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  rw [mul_add, add_mul, add_mul, ← add_assoc ]
  rw [add_assoc (a*c)]
  rw [add_comm (b*c) (a*d)]
  rw [← add_assoc]

-- calc
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  calc
    (a + b) * (c + d) = (a + b) * c + (a + b) * d := by
      rw [mul_add]
    _ = a * c + b * c + a * d + b * d := by
      rw [add_mul, add_mul, ← add_assoc]
    _ = a * c + (a * d + b * c) + b * d := by
      rw [add_assoc (a*c), add_comm (b * c) (a * d)]
    _ = a * c + a * d + b * c + b * d := by
      rw [← add_assoc (a*c)]

-- 发现虽然使用了calc，但还是会自然把一些步骤合并（不是每一步都拆开），因为是先写的每一步的目标结果
-- 所以在实现的时候，有时发现还需要一行内不少步骤


example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [pow_two a, pow_two b]
  rw [mul_sub, add_mul, add_mul]
  rw [← sub_sub]
  rw [mul_comm b a]
  rw [← add_sub (a*a) ]
  --这一步用add_assoc试了半天，就想着加括号（后面反应过来了）
  rw [sub_self]
  rw [add_zero]




#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a

end

-- Examples.

section
variable (a b c d : ℝ)

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

--ring 环
--一个环是一个集合R，定义了两种二元运算
--通常称为加法+，乘法·
--
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

-- 太好了是自动化
end

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
