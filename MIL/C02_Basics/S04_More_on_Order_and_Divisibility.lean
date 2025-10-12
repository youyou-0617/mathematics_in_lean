import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left

example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≤ max y x := by
    intro x y
    apply max_le
    apply le_max_right
    apply le_max_left
  apply le_antisymm
  repeat
    apply h
-- 和min a b = min b a一样的过程


example : min (min a b) c = min a (min b c) := by
  apply le_antisymm
  · apply le_min
    · apply le_trans
      · apply min_le_left
      apply min_le_left
    apply le_min
    · apply le_trans
      apply min_le_left
      apply min_le_right
  apply le_min
  · apply le_min
    apply le_trans
    apply min_le_left
    apply le_refl a
  apply le_trans
  apply min_le_right
  apply min_le_right
--不知道为什么报错



theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  apply le_min
  · apply add_le_add_right
    apply min_le_left
  apply add_le_add_right
  apply min_le_right
-- 差点想不到这个定理add_le_add_right

example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  · apply aux
-- apply le_trans
-- · apply min_le_left
-- apply add_le_add_right
-- 这一步又让我证明a< min(a,b)然后卡住
  have h: min (a +c) (b+c)= min (a+c) (b+c)-c+c := by
    rw[sub_add_cancel]
  rw[h]
  apply add_le_add_right
  apply le_min
  · nth_rw 2 [← add_neg_cancel_right a c]
    apply sub_le_sub_right
    apply min_le_left
  nth_rw 2 [← add_neg_cancel_right b c]
  apply sub_le_sub_right
  apply min_le_right
-- 终于！试出这种写法
-- 刚开始写的时候误用了min_add然后一行就成了？？
-- 遂发现这是要证明的定理

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
  nth_rw 1 [← sub_add_cancel a b]
  have h:|a - b + b| - |b| ≤|a - b| + |b| - |b|:=by
    apply sub_le_sub_right
    apply abs_add
  linarith
-- 还在纠结定理的时候发现linarith竟然可以直接解决
end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  apply dvd_add
  · apply dvd_add
    · apply dvd_mul_of_dvd_right
      apply dvd_mul_right
    apply dvd_mul_left
  rw[pow_two]
  apply dvd_mul_of_dvd_left
  exact h
-- 这个有点容易出错，对dvd的定理还不是很熟

end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.dvd_antisymm
  apply Nat.dvd_gcd
  apply Nat.gcd_dvd_right
  apply Nat.gcd_dvd_left
  apply Nat.dvd_gcd
  apply Nat.gcd_dvd_right
  apply Nat.gcd_dvd_left
-- 这边可以用repeat的
end
