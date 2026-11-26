import PEqualNP.Weyl.ZModSq

/-!
# Layer 3g: counting `r² ≡ s² (mod q)` for odd prime `q`

For odd prime `q` the congruence `r² ≡ s² (mod q)` with `0 ≤ r, s < q` holds
exactly for the two residues `s = r` and `s = q - r`.  Hence each fixed `r`
contributes `2` solutions (except `r = 0`, which contributes `1`), and the total
count is `2 q - 1`.  This turns `gauss_second_moment` into `q (2q - 1)`.
-/

set_option maxHeartbeats 600000

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- The set of resonant residues for a fixed `r` is the two-point set `{r, q - r}`. -/
lemma filter_sq_eq {q : ℕ} [Fact q.Prime] {r : ℕ} (hr : r < q) :
    (Finset.range q).filter (fun s => (q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ)))
      = ({r, q - r} : Finset ℕ) ∩ Finset.range q := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨hsv, hdiv⟩
    rcases (prime_dvd_sq_sub_sq (q := q) hr hsv).mp hdiv with h | h
    · exact ⟨Or.inl h.symm, hsv⟩
    · exact ⟨Or.inr (by omega), hsv⟩
  · rintro ⟨hmem, hsv⟩
    rcases hmem with h | h
    · exact ⟨hsv, (prime_dvd_sq_sub_sq (q := q) hr hsv).mpr (Or.inl h.symm)⟩
    · exact ⟨hsv, (prime_dvd_sq_sub_sq (q := q) hr hsv).mpr (Or.inr (by omega))⟩

/-- Each `r` contributes `2` resonant residues, or `1` when `r = 0`. -/
lemma filter_sq_card {q : ℕ} [Fact q.Prime] (hq2 : 2 < q) {r : ℕ} (hr : r < q) :
    ((Finset.range q).filter (fun s => (q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ)))).card
      = if r = 0 then 1 else 2 := by
  rw [filter_sq_eq hr]
  by_cases hr0 : r = 0
  · subst hr0
    have hset : ({0, q} : Finset ℕ) ∩ Finset.range q = {0} := by
      ext s
      simp only [Finset.mem_inter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h | h, hs⟩
        · exact h
        · omega
      · intro h
        exact ⟨Or.inl h, by omega⟩
    simp only [Nat.sub_zero]
    rw [hset]
    simp
  · have hsub : ({r, q - r} : Finset ℕ) ⊆ Finset.range q := by
      rw [Finset.insert_subset_iff]
      refine ⟨Finset.mem_range.mpr hr, ?_⟩
      rw [Finset.singleton_subset_iff]
      exact Finset.mem_range.mpr (by omega)
    rw [Finset.inter_eq_left.mpr hsub, if_neg hr0]
    apply Finset.card_pair
    intro h
    have h2 : 2 * r = q := by omega
    obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two (Fact.out : q.Prime) (by omega)
    omega

/-- Tally of the per-residue counts: one residue contributes `1`, the rest `2`. -/
lemma sum_ite_zero : ∀ n : ℕ, 1 ≤ n →
    (∑ r ∈ Finset.range n, (if r = 0 then (1 : ℕ) else 2)) = 2 * n - 1 := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ k ih =>
    intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      simp
    · have hk1 : 1 ≤ k := hkpos
      rw [Finset.sum_range_succ, ih hk1]
      have hlast : (if k = 0 then (1 : ℕ) else 2) = 2 := by
        rw [if_neg (ne_of_gt hkpos)]
      rw [hlast]
      omega

/-- Total number of resonant pairs: `2 q - 1` for odd prime `q`. -/
lemma count_sq_pairs {q : ℕ} [Fact q.Prime] (hq2 : 2 < q) :
    (∑ r ∈ Finset.range q,
        ((Finset.range q).filter
          (fun s => (q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ)))).card)
      = 2 * q - 1 := by
  rw [Finset.sum_congr rfl (fun r hr => filter_sq_card hq2 (Finset.mem_range.mp hr))]
  exact sum_ite_zero q (by omega)

/-- A constant multiplied by an indicator sums to the constant times the count. -/
lemma sum_ite_const {n : ℕ} (P : ℕ → Prop) [DecidablePred P] (c : ℝ) :
    (∑ s ∈ Finset.range n, (if P s then c else (0 : ℝ)))
      = c * (((Finset.range n).filter P).card : ℝ) := by
  rw [← Finset.sum_filter (s := Finset.range n) (p := P) (f := fun _ => c)]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

/-- Value of the second moment of the residue sums for odd prime `q`: `q (2q - 1)`. -/
theorem gauss_second_moment_value {q : ℕ} [Fact q.Prime] (hq2 : 2 < q) :
    ∑ a ∈ Finset.range q,
        Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ)))
      = (q : ℝ) * (((2 * q - 1 : ℕ) : ℝ)) := by
  rw [gauss_second_moment (Nat.Prime.pos (Fact.out : q.Prime))]
  have hinner : ∀ r ∈ Finset.range q,
      (∑ s ∈ Finset.range q,
          (if (q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ)) then (q : ℝ) else 0))
        = (q : ℝ) * (((Finset.range q).filter
            (fun s => (q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ)))).card : ℝ) :=
    fun r _ => sum_ite_const _ (q : ℝ)
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum, ← Nat.cast_sum]
  rw [count_sq_pairs hq2]

/-- Some residue `a < q` has a residue sum of size at most `√(2q - 1)`. -/
theorem exists_gauss_bound {q : ℕ} [Fact q.Prime] (hq2 : 2 < q) :
    ∃ a ∈ Finset.range q,
      ‖∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))‖
        ≤ Real.sqrt (((2 * q - 1 : ℕ) : ℝ)) := by
  have hqpos : 0 < q := Nat.Prime.pos (Fact.out : q.Prime)
  have hsum := gauss_second_moment_value hq2
  have hle : (∑ a ∈ Finset.range q,
        Complex.normSq (∑ r ∈ Finset.range q, E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))))
      ≤ (q : ℝ) * (((2 * q - 1 : ℕ) : ℝ)) := le_of_eq hsum
  obtain ⟨a, ha, hb⟩ := exists_normSq_gauss_le hqpos hle
  exact ⟨a, ha, norm_le_sqrt_of_normSq_le (by positivity) hb⟩

/-- Block form: for odd prime `q` there is a residue `a` whose full block `n < q * M`
is bounded by `M √(2q - 1)`. -/
theorem exists_block_bound {q : ℕ} [Fact q.Prime] (hq2 : 2 < q) (M : ℕ) :
    ∃ a ∈ Finset.range q,
      ‖∑ n ∈ Finset.range (q * M), E ((a : ℝ) * ((n : ℝ)) ^ 2 / (q : ℝ))‖
        ≤ (M : ℝ) * Real.sqrt (((2 * q - 1 : ℕ) : ℝ)) := by
  obtain ⟨a, ha, hb⟩ := exists_gauss_bound hq2
  exact ⟨a, ha,
    norm_sum_quad_block (Nat.Prime.pos (Fact.out : q.Prime)) a M hb⟩

end

end PEqualNP.Weyl
