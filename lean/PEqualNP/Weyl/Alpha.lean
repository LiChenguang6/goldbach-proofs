import PEqualNP.Weyl.Mod
import PEqualNP.Weyl.Count

/-!
# Layer 4a: residue decomposition for a general phase `α = a/q + β`

Combining the block reindexing `n = q * m + r` with the pointwise factorisation
`E (α n²) = E (a r² / q) * E (β n²)`, the full quadratic sum over a block of
`M` complete residue systems becomes

`∑_{n < qM} E (α n²) = ∑_{r<q} E (a r² / q) * ∑_{m<M} E (β (q m + r)²)`.

The residue weights are the Gauss sums bounded in `Weyl/Count.lean`; the inner
sums are quadratic sums in `m` with small coefficient `β q²`.
-/

set_option maxHeartbeats 600000

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- Reindex a block of `M` complete residue systems. -/
lemma sum_range_mul_blocks {q M : ℕ} (f : ℕ → ℂ) :
    ∑ n ∈ Finset.range (q * M), f n
      = ∑ m ∈ Finset.range M, ∑ r ∈ Finset.range q, f (q * m + r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have hsplit : q * (M + 1) = q * M + q := Nat.mul_succ q M
    rw [hsplit, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-- Residue decomposition of the quadratic sum for the phase `a/q + β`. -/
lemma sum_quad_alpha_split {q : ℕ} (hq : 0 < q) (a : ℤ) (β : ℝ) (M : ℕ) :
    (∑ n ∈ Finset.range (q * M), E (((a : ℝ) / (q : ℝ) + β) * ((n : ℝ) ^ 2)))
      = ∑ r ∈ Finset.range q,
          E ((a : ℝ) * ((r : ℝ)) ^ 2 / (q : ℝ))
            * ∑ m ∈ Finset.range M, E (β * (((q * m + r : ℕ) : ℝ) ^ 2)) := by
  rw [sum_range_mul_blocks (fun n => E (((a : ℝ) / (q : ℝ) + β) * ((n : ℝ) ^ 2)))]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => sum_quad_mod_split a q hq β r M)

end

end PEqualNP.Weyl
