import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

#check ∀ x : ℝ, 0 ≤ x → |x| = x

#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by
      apply abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul
      repeat
        linarith
      repeat
        apply abs_nonneg
    _ < 1 * ε := by
      rw[mul_lt_mul_right epos]
      linarith[xlt,ele1]
    _ = ε := by
      rw[one_mul]

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end

theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by
      apply abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul
      repeat
        linarith
      repeat
        apply abs_nonneg
    _ < 1 * ε := by
      rw[mul_lt_mul_right epos]
      linarith[xlt,ele1]
    _ = ε := by
      rw[one_mul]

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end

theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by
      apply abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul
      repeat
        linarith
      repeat
        apply abs_nonneg
    _ < 1 * ε := by
      rw[mul_lt_mul_right epos]
      linarith[xlt,ele1]
    _ = ε := by
      rw[one_mul]

-- 真正证明的只有lemma4， 前三个展示{}和intro的过程
-- 不过三个sorry看着比较难看，所以我补全了

theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := by
      apply abs_mul x y
    _ ≤ |x| * ε := by
      apply mul_le_mul
      repeat
        linarith
      repeat
        apply abs_nonneg
    _ < 1 * ε := by
      rw[mul_lt_mul_right epos]
      linarith[xlt,ele1]
    _ = ε := by
      rw[one_mul]

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

section
variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb

-- 这个其实和上一个是一样的，只是运用了FnUb和FnLb中的不同项


example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  dsimp
  apply mul_nonneg
  apply nnf
  apply nng


example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
    intro x
    dsimp
    apply mul_le_mul
    apply hfa
    apply hgb
    apply nng
    apply nna

-- 这三题思路是一样的，都是先引入x
-- 然后简洁化
-- 最后使用假设展开的定义

end

section
variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

end

example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h

section
variable (f g : ℝ → ℝ)

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

-- 简化证明过程的方法

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  dsimp
  apply mul_le_mul_of_nonneg_left
  apply mf aleb
  apply nnc

-- 这个定理mul_le_mul_of_nonneg_left也是非常难找
-- 原来自己只找到了mul_le_mul_of_nonneg，然后证不出来
-- 看solution加上了_left

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  dsimp
  apply mf
  apply mg aleb

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  dsimp
  rw[of, og, neg_mul_neg]


example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw[ef, og, neg_mul_eq_mul_neg]


example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw[ef, og, neg_neg]

end

section

variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro h1 h2 x1 x2
  apply h2
  apply h1
  apply x2

-- 这个抽丝剥茧的证明很神奇
-- 首先将要证明的命题拆解成了多个假设
-- 然后引入x1, x2，把集合的包含问题通过一个集合中具体的元素解决

end

section
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x1 x2
  trans a
  apply h
  apply x2
  apply h'


end

section

open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
-- intro x1 x2
-- dsimp
-- intro h1
-- apply mul_eq_mul_left_iff
-- 这个看solution了试不出来
  intro x1 x2 h1
  apply (mul_right_inj' h).mp h1

variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x1 x2 h
  apply injf
  apply injg
  apply h

-- 最后一步apply h稍微有点难以看出，还是喜欢dsimp
-- 不过

end
