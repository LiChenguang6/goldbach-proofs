import PEqualNP.Weyl.Bilinear

/-!
# Layer 5b: the Type-II second-moment bound

After Cauchy–Schwarz in the outer variable, the inner second moment splits
into a diagonal part `N·M` and an off-diagonal geometric saving
`2·∑_h (N-h)·min M (1/|αh|)`.
-/

namespace PEqualNP.Weyl

noncomputable section

open Finset

/-- Symmetric distance on `ℕ`. -/
def ndist (a b : ℕ) : ℕ := max a b - min a b

lemma ndist_comm (a b : ℕ) : ndist a b = ndist b a := by
  simp [ndist, max_comm, min_comm]

lemma ndist_self (a : ℕ) : ndist a a = 0 := by
  simp [ndist]

lemma ndist_add_left (k h : ℕ) : ndist (k + h) k = h := by
  have hk : k ≤ k + h := Nat.le_add_right k h
  rw [ndist, max_eq_left hk, min_eq_right hk]
  omega

lemma ndist_eq_zero_iff {a b : ℕ} : ndist a b = 0 ↔ a = b := by
  constructor
  · intro h
    unfold ndist at h
    have h' : max a b ≤ min a b := Nat.sub_eq_zero_iff_le.mp h
    have h1 : min a b ≤ a := min_le_left _ _
    have h2 : a ≤ max a b := le_max_left _ _
    have h3 : min a b ≤ b := min_le_right _ _
    have h4 : b ≤ max a b := le_max_right _ _
    omega
  · intro h
    subst h
    exact ndist_self a

lemma abs_sub_cast (n1 n2 : ℕ) :
    |(n1 : ℝ) - (n2 : ℝ)| = ((ndist n1 n2 : ℕ) : ℝ) := by
  unfold ndist
  rcases le_total n1 n2 with h | h
  · have h1 : (n1 : ℝ) ≤ (n2 : ℝ) := by exact_mod_cast h
    rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]
    rw [Nat.cast_sub h]
    ring
  · have h1 : (n2 : ℝ) ≤ (n1 : ℝ) := by exact_mod_cast h
    rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]
    rw [Nat.cast_sub h]

/-- Off-diagonal weight `min M (1/|αh|)`, with the diagonal value `M`. -/
def kap (M : ℕ) (α : ℝ) : ℕ → ℝ :=
  fun h => if h = 0 then (M : ℝ) else min (M : ℝ) (1 / |α * (h : ℝ)|)

lemma kap_zero (M : ℕ) (α : ℝ) : kap M α 0 = (M : ℝ) := by
  simp [kap]

lemma kap_ne_zero {M : ℕ} {α : ℝ} {h : ℕ} (hh : h ≠ 0) :
    kap M α h = min (M : ℝ) (1 / |α * (h : ℝ)|) := by
  simp [kap, hh]

lemma kap_nonneg (M : ℕ) (α : ℝ) (h : ℕ) : 0 ≤ kap M α h := by
  unfold kap
  split_ifs with hh
  · exact Nat.cast_nonneg M
  · exact le_min (Nat.cast_nonneg M) (by positivity)

/-- A single pair `(n₁, n₂)` of the second moment. -/
lemma norm_sum_E_pair (M N : ℕ) (α : ℝ) (hα0 : α ≠ 0)
    (hα : ∀ h : ℕ, 1 ≤ h → h < N → |α * (h : ℝ)| ≤ 1 / 2)
    {n1 n2 : ℕ} (hn1 : n1 < N) (hn2 : n2 < N) :
    ‖∑ m ∈ Finset.range M, E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))‖
      ≤ kap M α (ndist n1 n2) := by
  have hdN : ndist n1 n2 < N := by
    unfold ndist
    exact lt_of_le_of_lt (Nat.sub_le (max n1 n2) (min n1 n2)) (max_lt hn1 hn2)
  rcases eq_or_ne n1 n2 with heq | hne
  · subst heq
    have hz : (∑ m ∈ Finset.range M, E ((m : ℝ) * (α * ((n1 : ℝ) - (n1 : ℝ))))) = (M : ℂ) := by
      have h0 : ((n1 : ℝ) - (n1 : ℝ)) = 0 := by ring
      simp [E]
    rw [hz, ndist_self, kap_zero]
    simp
  · have hd0 : ndist n1 n2 ≠ 0 := by
      intro h0
      rw [ndist_eq_zero_iff] at h0
      exact hne h0
    have hdpos : 1 ≤ ndist n1 n2 := Nat.one_le_iff_ne_zero.mpr hd0
    have hdne : ((n1 : ℝ) - (n2 : ℝ)) ≠ 0 := by
      intro h0
      exact hne (Nat.cast_injective (by linarith : (n1 : ℝ) = (n2 : ℝ)))
    have hβ0 : α * ((n1 : ℝ) - (n2 : ℝ)) ≠ 0 := mul_ne_zero hα0 hdne
    have hβ : |α * ((n1 : ℝ) - (n2 : ℝ))| ≤ 1 / 2 := by
      have h := hα (ndist n1 n2) hdpos hdN
      have hcast : |((ndist n1 n2 : ℕ) : ℝ)| = ((ndist n1 n2 : ℕ) : ℝ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [abs_mul, hcast] at h
      rw [abs_mul, abs_sub_cast]
      exact h
    calc ‖∑ m ∈ Finset.range M, E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))‖
        ≤ min (M : ℝ) (1 / |α * ((n1 : ℝ) - (n2 : ℝ))|) :=
          norm_sum_E_le_min hβ0 hβ M
      _ = kap M α (ndist n1 n2) := by
          have hl : |α * ((n1 : ℝ) - (n2 : ℝ))| = |α| * ((ndist n1 n2 : ℕ) : ℝ) := by
            rw [abs_mul, abs_sub_cast]
          have hr : |α * ((ndist n1 n2 : ℕ) : ℝ)| = |α| * ((ndist n1 n2 : ℕ) : ℝ) := by
            have hc : |((ndist n1 n2 : ℕ) : ℝ)| = ((ndist n1 n2 : ℕ) : ℝ) :=
              abs_of_nonneg (Nat.cast_nonneg _)
            rw [abs_mul, hc]
          rw [kap_ne_zero hd0, hl, hr]

/-- Counting the pairs by their difference. -/
lemma sum_kap_ndist (M N : ℕ) (α : ℝ) :
    ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N, kap M α (ndist n1 n2)
      = (N : ℝ) * (M : ℝ)
        + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
            ((N - h : ℕ) : ℝ) * kap M α h := by
  have hsymm : ∀ a b : ℕ, kap M α (ndist a b) = kap M α (ndist b a) := by
    intro a b
    rw [ndist_comm]
  have hsplit := sum_sum_split N (fun n1 n2 => kap M α (ndist n1 n2))
  have hdiag : ∑ n ∈ Finset.range N, kap M α (ndist n n) = (N : ℝ) * (M : ℝ) := by
    have h1 : ∀ n ∈ Finset.range N, kap M α (ndist n n) = (M : ℝ) :=
      fun n _ => by rw [ndist_self, kap_zero]
    rw [Finset.sum_congr rfl h1]
    simp [Finset.sum_const]
  have hoff :
      ∑ n ∈ Finset.range N, ∑ m ∈ (Finset.range N).erase n, kap M α (ndist n m)
        = 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
            ∑ k ∈ Finset.range (N - h), kap M α (ndist (k + h) k) :=
    offdiag_eq_two N (fun n1 n2 => kap M α (ndist n1 n2)) hsymm
  have hoff2 :
      (∑ h ∈ Finset.Icc 1 (N - 1),
          ∑ k ∈ Finset.range (N - h), kap M α (ndist (k + h) k))
        = ∑ h ∈ Finset.Icc 1 (N - 1), ((N - h : ℕ) : ℝ) * kap M α h := by
    apply Finset.sum_congr rfl
    intro h hh
    have h1 : ∀ k ∈ Finset.range (N - h), kap M α (ndist (k + h) k) = kap M α h :=
      fun k _ => by rw [ndist_add_left]
    rw [Finset.sum_congr rfl h1]
    simp [Finset.sum_const]
  rw [hsplit, hdiag, hoff, hoff2]

/-- **Type-II second moment.** -/
lemma inner_sum_sq_le (M N : ℕ) (b : ℕ → ℂ) (B : ℝ) (α : ℝ)
    (hB : ∀ n, ‖b n‖ ≤ B) (hα0 : α ≠ 0)
    (hα : ∀ h : ℕ, 1 ≤ h → h < N → |α * (h : ℝ)| ≤ 1 / 2) :
    ∑ m ∈ Finset.range M, ‖∑ n ∈ Finset.range N, b n * E (α * ((m : ℝ) * (n : ℝ)))‖ ^ 2
      ≤ B ^ 2 * ((N : ℝ) * (M : ℝ)
          + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
              ((N - h : ℕ) : ℝ) * min (M : ℝ) (1 / |α * (h : ℝ)|)) := by
  have hB0 : 0 ≤ B := le_trans (norm_nonneg (b 0)) (hB 0)
  have hEq :
      ∑ m ∈ Finset.range M, ‖∑ n ∈ Finset.range N, b n * E (α * ((m : ℝ) * (n : ℝ)))‖ ^ 2
        = ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N,
            (b n1 * star (b n2)
              * ∑ m ∈ Finset.range M,
                  E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re := by
    calc ∑ m ∈ Finset.range M, ‖∑ n ∈ Finset.range N, b n * E (α * ((m : ℝ) * (n : ℝ)))‖ ^ 2
        = ∑ m ∈ Finset.range M, ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N,
            (b n1 * star (b n2) * E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re := by
          apply Finset.sum_congr rfl
          intro m _
          exact inner_sq_expand N b α m
      _ = ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N, ∑ m ∈ Finset.range M,
            (b n1 * star (b n2) * E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro n1 _
          rw [Finset.sum_comm]
      _ = ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N,
            (b n1 * star (b n2)
              * ∑ m ∈ Finset.range M,
                  E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re := by
          apply Finset.sum_congr rfl
          intro n1 _
          apply Finset.sum_congr rfl
          intro n2 _
          rw [← Complex.re_sum, Finset.mul_sum]
  rw [hEq]
  have hBnd :
      (∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N,
          (b n1 * star (b n2)
            * ∑ m ∈ Finset.range M,
                E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re)
        ≤ B ^ 2 * ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N, kap M α (ndist n1 n2) := by
    have hterm : ∀ n1 ∈ Finset.range N, ∀ n2 ∈ Finset.range N,
        (b n1 * star (b n2)
          * ∑ m ∈ Finset.range M,
              E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re
          ≤ B * B * kap M α (ndist n1 n2) := by
      intro n1 hn1 n2 hn2
      have hK := norm_sum_E_pair M N α hα0 hα (Finset.mem_range.mp hn1) (Finset.mem_range.mp hn2)
      calc (b n1 * star (b n2)
            * ∑ m ∈ Finset.range M,
                E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re
          ≤ ‖b n1 * star (b n2)
              * ∑ m ∈ Finset.range M,
                  E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))‖ := Complex.re_le_norm _
        _ = ‖b n1‖ * ‖b n2‖
              * ‖∑ m ∈ Finset.range M,
                  E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))‖ := by
              rw [norm_mul, norm_mul, norm_star]
        _ ≤ B * B * kap M α (ndist n1 n2) := by
              refine mul_le_mul (mul_le_mul (hB n1) (hB n2) (norm_nonneg _) hB0) hK
                (norm_nonneg _) (by positivity)
    calc (∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N,
          (b n1 * star (b n2)
            * ∑ m ∈ Finset.range M,
                E ((m : ℝ) * (α * ((n1 : ℝ) - (n2 : ℝ))))).re)
        ≤ ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N, B * B * kap M α (ndist n1 n2) := by
          apply Finset.sum_le_sum
          intro n1 hn1
          apply Finset.sum_le_sum
          intro n2 hn2
          exact hterm n1 hn1 n2 hn2
      _ = B ^ 2 * ∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N, kap M α (ndist n1 n2) := by
          rw [pow_two]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n1 _
          rw [Finset.mul_sum]
  have hval :
      (∑ n1 ∈ Finset.range N, ∑ n2 ∈ Finset.range N, kap M α (ndist n1 n2))
        = (N : ℝ) * (M : ℝ)
          + 2 * ∑ h ∈ Finset.Icc 1 (N - 1),
              ((N - h : ℕ) : ℝ) * min (M : ℝ) (1 / |α * (h : ℝ)|) := by
    rw [sum_kap_ndist]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro h hh
    have hne : h ≠ 0 := by
      intro h0
      subst h0
      simp at hh
    rw [kap_ne_zero hne]
  rw [hval] at hBnd
  exact hBnd

end

end PEqualNP.Weyl
