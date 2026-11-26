import PEqualNP.Weyl.Shift

/-!
# Layer 2b: differencing (Cauchy–Schwarz on a quadratic phase)

The exact expansion of `normSq` of a finite sum into a double sum, which is the
algebraic core of Weyl differencing.
-/

namespace PEqualNP.Weyl

open Finset

noncomputable section

variable {z : ℕ → ℂ}

lemma normSq_sum_range (N : ℕ) :
    Complex.normSq (∑ n ∈ Finset.range N, z n)
      = ∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, (z n * star (z m)).re := by
  have hsq : Complex.normSq (∑ n ∈ Finset.range N, z n)
      = ((∑ n ∈ Finset.range N, z n) * star (∑ m ∈ Finset.range N, z m)).re := by
    rw [Complex.star_def, Complex.mul_conj]
    simp
  rw [hsq, star_sum, Finset.sum_mul_sum]
  simp [Complex.re_sum]

lemma sum_sum_split (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range N, ∑ m ∈ Finset.range N, f n m)
      = (∑ n ∈ Finset.range N, f n n)
        + ∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).erase n, f n m := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [← Finset.sum_erase_add (Finset.range N) (fun m => f n m) hn]
  ring

lemma re_mul_star_comm (a b : ℂ) : (a * star b).re = (b * star a).re := by
  have h : b * star a = star (a * star b) := by
    rw [star_mul, star_star]
  rw [h, Complex.star_def]
  simp

lemma range_erase_eq_filter_ne (N n : ℕ) :
    (Finset.range N).erase n = (Finset.range N).filter (fun m => m ≠ n) := by
  ext m
  simp [Finset.mem_erase, Finset.mem_filter, and_comm]

lemma sum_filter_ne_split (N n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ (Finset.range N).filter (fun m => m ≠ n), f m
      = ∑ m ∈ (Finset.range N).filter (fun m => m < n), f m
        + ∑ m ∈ (Finset.range N).filter (fun m => n < m), f m := by
  rw [← Finset.sum_filter_add_sum_filter_not
    ((Finset.range N).filter (fun m => m ≠ n)) (fun m => m < n) f]
  congr 1
  · apply Finset.sum_congr
    · rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro m _
      omega
    · intro m _
      rfl
  · apply Finset.sum_congr
    · rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro m _
      omega
    · intro m _
      rfl

lemma sum_erase_split (N n : ℕ) (f : ℕ → ℝ) :
    ∑ m ∈ (Finset.range N).erase n, f m
      = ∑ m ∈ (Finset.range N).filter (fun m => m < n), f m
        + ∑ m ∈ (Finset.range N).filter (fun m => n < m), f m := by
  rw [range_erase_eq_filter_ne]
  exact sum_filter_ne_split N n f

lemma sum_lt_reindex (N : ℕ) (f : ℕ → ℕ → ℝ) (hsymm : ∀ a b, f a b = f b a) :
    (∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).filter (fun m => n < m), f n m)
      = ∑ h ∈ Finset.Icc 1 (N - 1), ∑ k ∈ Finset.range (N - h), f (k + h) k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => (⟨p.2 - p.1, p.1⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    omega
  · rintro ⟨n₁, m₁⟩ h₁ ⟨n₂, m₂⟩ h₂ heq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at h₁ h₂
    simp only [Sigma.mk.injEq, heq_eq_eq] at heq
    obtain ⟨hn, hsub⟩ := heq
    subst hsub
    have e1 : m₁ - n₁ + n₁ = m₁ := Nat.sub_add_cancel (le_of_lt h₁.2.2)
    have e2 : m₂ - n₁ + n₁ = m₂ := Nat.sub_add_cancel (le_of_lt h₂.2.2)
    have hm : m₁ = m₂ := by omega
    subst hm
    rfl
  · rintro ⟨h, k⟩ hk
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hk
    refine ⟨⟨k, k + h⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      omega
    · simp
  · rintro ⟨n, m⟩ hn
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hn
    show f n m = f (n + (m - n)) n
    rw [Nat.add_sub_of_le (le_of_lt hn.2.2)]
    exact hsymm n m

lemma sum_gt_reindex (N : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).filter (fun m => m < n), f n m)
      = ∑ h ∈ Finset.Icc 1 (N - 1), ∑ k ∈ Finset.range (N - h), f (k + h) k := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij (fun p _ => (⟨p.1 - p.2, p.2⟩ : Sigma fun _ : ℕ => ℕ)) ?_ ?_ ?_ ?_
  · rintro ⟨n, m⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc] at hp ⊢
    omega
  · rintro ⟨n₁, m₁⟩ h₁ ⟨n₂, m₂⟩ h₂ heq
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at h₁ h₂
    simp only [Sigma.mk.injEq, heq_eq_eq] at heq
    obtain ⟨hsub, hm⟩ := heq
    subst hm
    have e1 : n₁ - m₁ + m₁ = n₁ := Nat.sub_add_cancel (le_of_lt h₁.2.2)
    have e2 : n₂ - m₁ + m₁ = n₂ := Nat.sub_add_cancel (le_of_lt h₂.2.2)
    have hn : n₁ = n₂ := by omega
    subst hn
    rfl
  · rintro ⟨h, k⟩ hk
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hk
    refine ⟨⟨k + h, k⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_filter]
      omega
    · simp
  · rintro ⟨n, m⟩ hn
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_range] at hn
    show f n m = f (m + (n - m)) m
    rw [Nat.add_sub_of_le (le_of_lt hn.2.2)]

lemma offdiag_eq_two (N : ℕ) (f : ℕ → ℕ → ℝ) (hsymm : ∀ a b, f a b = f b a) :
    (∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).erase n, f n m)
      = 2 * ∑ h ∈ Finset.Icc 1 (N - 1), ∑ k ∈ Finset.range (N - h), f (k + h) k := by
  rw [Finset.sum_congr rfl (fun n _ => sum_erase_split N n (fun m => f n m))]
  rw [Finset.sum_add_distrib]
  rw [sum_gt_reindex N f]
  rw [sum_lt_reindex N f hsymm]
  ring

lemma differ_bound (N : ℕ) (z : ℕ → ℂ) :
    ‖∑ n ∈ Finset.range N, z n‖ ^ 2
      ≤ (∑ n ∈ Finset.range N, ‖z n‖ ^ 2)
        + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
            ‖∑ k ∈ Finset.range (N - h), z (k + h) * star (z k)‖ := by
  have hsq : ‖∑ n ∈ Finset.range N, z n‖ ^ 2
      = Complex.normSq (∑ n ∈ Finset.range N, z n) := by
    rw [Complex.normSq_eq_norm_sq]
  rw [hsq, normSq_sum_range]
  rw [sum_sum_split N (fun n m => (z n * star (z m)).re)]
  have hdiag : (∑ n ∈ Finset.range N, (z n * star (z n)).re)
      = ∑ n ∈ Finset.range N, ‖z n‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [hdiag]
  have hoff : (∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).erase n, (z n * star (z m)).re)
      = 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
          ∑ k ∈ Finset.range (N - h), (z (k + h) * star (z k)).re :=
    offdiag_eq_two N (fun n m => (z n * star (z m)).re)
      (fun a b => re_mul_star_comm (z a) (z b))
  rw [hoff]
  have hbound : (∑ h ∈ Finset.Icc 1 (N - 1),
        ∑ k ∈ Finset.range (N - h), (z (k + h) * star (z k)).re)
      ≤ ∑ h ∈ Finset.Icc 1 (N - 1),
          ‖∑ k ∈ Finset.range (N - h), z (k + h) * star (z k)‖ := by
    apply Finset.sum_le_sum
    intro h _
    have : (∑ k ∈ Finset.range (N - h), (z (k + h) * star (z k)).re)
        = (∑ k ∈ Finset.range (N - h), z (k + h) * star (z k)).re := by
      simp [Complex.re_sum]
    rw [this]
    exact Complex.re_le_norm _
  nlinarith [mul_le_mul_of_nonneg_left hbound (show (0 : ℝ) ≤ 2 by norm_num)]

end

end PEqualNP.Weyl
