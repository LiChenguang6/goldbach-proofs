import PEqualNP.Weyl.Ortho

/-!
# Layer 3d: residue classes modulo `q`

Splitting `n = q * m + r` and writing `α = a / q + β`, the quadratic character
`E (α n²)` factors as `E (a r² / q) * E (β n²)`: the leftover terms of
`a n² / q` are integers, hence contribute a factor `E (k) = 1`.
-/

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- Pointwise factorisation of the quadratic character over residue classes mod `q`. -/
lemma E_quad_mod_split (a : ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ) (m r : ℕ) :
    E (((a : ℝ) / (q : ℝ) + β) * (((q * m + r : ℕ) : ℝ) ^ 2))
      = E ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ))
        * E (β * (((q * m + r : ℕ) : ℝ) ^ 2)) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hn : (((q * m + r : ℕ) : ℝ)) = (q : ℝ) * (m : ℝ) + (r : ℝ) := by
    push_cast
    ring
  have hn2 : (((q * m + r : ℕ) : ℝ) ^ 2)
      = (q : ℝ) ^ 2 * (m : ℝ) ^ 2 + 2 * (q : ℝ) * (m : ℝ) * (r : ℝ) + (r : ℝ) ^ 2 := by
    rw [hn]
    ring
  have h3 : (a : ℝ) * (q : ℝ) * (m : ℝ) ^ 2 + 2 * (a : ℝ) * (m : ℝ) * (r : ℝ)
      = (((a * (q : ℤ) * (m : ℤ) ^ 2 + 2 * a * (m : ℤ) * (r : ℤ) : ℤ) : ℝ)) := by
    push_cast
    ring
  have hmain : (a : ℝ) / (q : ℝ) *
        ((q : ℝ) ^ 2 * (m : ℝ) ^ 2 + 2 * (q : ℝ) * (m : ℝ) * (r : ℝ) + (r : ℝ) ^ 2)
      = (a : ℝ) * (q : ℝ) * (m : ℝ) ^ 2 + 2 * (a : ℝ) * (m : ℝ) * (r : ℝ)
        + (a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) := by
    field_simp
  have hsplit : ((a : ℝ) / (q : ℝ)) * (((q * m + r : ℕ) : ℝ) ^ 2)
      = (a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ)
        + (((a * (q : ℤ) * (m : ℤ) ^ 2 + 2 * a * (m : ℤ) * (r : ℤ) : ℤ) : ℝ)) := by
    rw [hn2, hmain, h3]
    ring
  have hexp : (((a : ℝ) / (q : ℝ) + β) * (((q * m + r : ℕ) : ℝ) ^ 2))
      = ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ) + β * (((q * m + r : ℕ) : ℝ) ^ 2))
        + (((a * (q : ℤ) * (m : ℤ) ^ 2 + 2 * a * (m : ℤ) * (r : ℤ) : ℤ) : ℝ)) := by
    have he : ((a : ℝ) / (q : ℝ) + β) * (((q * m + r : ℕ) : ℝ) ^ 2)
        = ((a : ℝ) / (q : ℝ)) * (((q * m + r : ℕ) : ℝ) ^ 2)
          + β * (((q * m + r : ℕ) : ℝ) ^ 2) := by
      ring
    rw [he, hsplit]
    ring
  rw [hexp, E_add, E_int, mul_one, E_add]

/-- Sum-level residue-class factorisation: one residue class `r` at a time. -/
lemma sum_quad_mod_split (a : ℤ) (q : ℕ) (hq : 0 < q) (β : ℝ) (r K : ℕ) :
    (∑ m ∈ Finset.range K,
        E (((a : ℝ) / (q : ℝ) + β) * (((q * m + r : ℕ) : ℝ) ^ 2)))
      = E ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ))
        * ∑ m ∈ Finset.range K, E (β * (((q * m + r : ℕ) : ℝ) ^ 2)) := by
  have h1 : (∑ m ∈ Finset.range K,
        E (((a : ℝ) / (q : ℝ) + β) * (((q * m + r : ℕ) : ℝ) ^ 2)))
      = ∑ m ∈ Finset.range K,
          E ((a : ℝ) * (r : ℝ) ^ 2 / (q : ℝ)) * E (β * (((q * m + r : ℕ) : ℝ) ^ 2)) :=
    Finset.sum_congr rfl (fun m _ => E_quad_mod_split a q hq β m r)
  rw [h1, ← Finset.mul_sum]

end

end PEqualNP.Weyl
