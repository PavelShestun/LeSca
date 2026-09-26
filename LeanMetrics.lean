import Mathlib

structure Edge where
  u : ℕ
  w : ℝ
  v : ℕ

noncomputable def edgeDist (e₁ e₂ : Edge) : ℝ :=
  |(e₁.u : ℝ) - (e₂.u : ℝ)| + |e₁.w - e₂.w| + |(e₁.v : ℝ) - (e₂.v : ℝ)|

lemma edgeDist_self (e : Edge) : edgeDist e e = 0 := by
  unfold edgeDist; simp

lemma edgeDist_comm (e₁ e₂ : Edge) : edgeDist e₁ e₂ = edgeDist e₂ e₁ := by
  unfold edgeDist
  have h1 : |(e₁.u : ℝ) - (e₂.u : ℝ)| = |(e₂.u : ℝ) - (e₁.u : ℝ)| :=
    abs_sub_comm _ _
  have h2 : |e₁.w - e₂.w| = |e₂.w - e₁.w| := abs_sub_comm _ _
  have h3 : |(e₁.v : ℝ) - (e₂.v : ℝ)| = |(e₂.v : ℝ) - (e₁.v : ℝ)| :=
    abs_sub_comm _ _
  rw [h1, h2, h3]

lemma edgeDist_triangle (e₁ e₂ e₃ : Edge) :
    edgeDist e₁ e₃ ≤ edgeDist e₁ e₂ + edgeDist e₂ e₃ := by
  unfold edgeDist
  have h1 : |(e₁.u : ℝ) - (e₃.u : ℝ)| ≤
      |(e₁.u : ℝ) - (e₂.u : ℝ)| + |(e₂.u : ℝ) - (e₃.u : ℝ)| := abs_sub_le _ _ _
  have h2 : |e₁.w - e₃.w| ≤ |e₁.w - e₂.w| + |e₂.w - e₃.w| := abs_sub_le _ _ _
  have h3 : |(e₁.v : ℝ) - (e₃.v : ℝ)| ≤
      |(e₁.v : ℝ) - (e₂.v : ℝ)| + |(e₂.v : ℝ) - (e₃.v : ℝ)| := abs_sub_le _ _ _
  linarith

lemma edgeDist_eq_zero {e₁ e₂ : Edge} (h : edgeDist e₁ e₂ = 0) : e₁ = e₂ := by
  unfold edgeDist at h
  have n1 : 0 ≤ |(e₁.u : ℝ) - (e₂.u : ℝ)| := abs_nonneg _
  have n2 : 0 ≤ |e₁.w - e₂.w| := abs_nonneg _
  have n3 : 0 ≤ |(e₁.v : ℝ) - (e₂.v : ℝ)| := abs_nonneg _
  have h1 : |(e₁.u : ℝ) - (e₂.u : ℝ)| = 0 := by linarith
  have h2 : |e₁.w - e₂.w| = 0 := by linarith
  have h3 : |(e₁.v : ℝ) - (e₂.v : ℝ)| = 0 := by linarith
  have hu : (e₁.u : ℝ) = (e₂.u : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp h1)
  have hw : e₁.w = e₂.w := sub_eq_zero.mp (abs_eq_zero.mp h2)
  have hv : (e₁.v : ℝ) = (e₂.v : ℝ) := sub_eq_zero.mp (abs_eq_zero.mp h3)
  have hu' : e₁.u = e₂.u := Nat.cast_injective hu
  have hv' : e₁.v = e₂.v := Nat.cast_injective hv
  cases e₁; cases e₂; simp_all

example : edgeDist ⟨1, 5, 2⟩ ⟨1, 3, 4⟩ = 4 := by
  unfold edgeDist; norm_num
