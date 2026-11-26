import PEqualNP.Weyl.Gauss
import Mathlib.Data.ZMod.Basic

/-!
# Layer 3f: `r² ≡ s² (mod q)` for prime `q` has exactly the trivial solutions

For prime `q` and `0 ≤ r, s < q`, the congruence `r² ≡ s² (mod q)` forces
`r = s` or `r + s = q`: modulo `q` the ring is a field, so
`(r - s)(r + s) = 0` splits, and the two branches are then pinned by the size
bounds.  This is the counting input behind `∑_a |G a|² = q (2q - 1)`.
-/

set_option maxHeartbeats 600000

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

/-- In `ZMod q` with `q` prime, `r² = s²` only for `r = s` or `r + s = q`. -/
lemma zmod_sq_eq_sq_iff {q : ℕ} [Fact q.Prime] {r s : ℕ} (hr : r < q) (hs : s < q) :
    ((r : ZMod q)) ^ 2 = ((s : ZMod q)) ^ 2 ↔ (r = s ∨ r + s = q) := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  constructor
  · intro h
    have hfac : (((r : ZMod q)) - (s : ZMod q)) * (((r : ZMod q)) + (s : ZMod q)) = 0 := by
      have hring : (((r : ZMod q)) - (s : ZMod q)) * (((r : ZMod q)) + (s : ZMod q))
          = ((r : ZMod q)) ^ 2 - ((s : ZMod q)) ^ 2 := by ring
      rw [hring, h, sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      have hsub : (r : ZMod q) = (s : ZMod q) := sub_eq_zero.mp h1
      have hv : r % q = s % q := by
        have := congrArg ZMod.val hsub
        simpa [ZMod.val_natCast] using this
      rw [Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hs] at hv
      exact hv
    · have hsum : ((r + s : ℕ) : ZMod q) = 0 := by
        push_cast
        exact h1
      rw [CharP.cast_eq_zero_iff (ZMod q) q (r + s)] at hsum
      have hlt : r + s < 2 * q := by omega
      obtain ⟨k, hk⟩ := hsum
      have hk2 : k < 2 := by
        have h1 : q * k < q * 2 := by
          calc q * k = r + s := hk.symm
            _ < 2 * q := hlt
            _ = q * 2 := by ring
        exact Nat.lt_of_mul_lt_mul_left h1
      interval_cases k <;> omega
  · rintro (h | h)
    · rw [h]
    · have hdvd : q ∣ r + s := ⟨1, by omega⟩
      have hzero : ((r + s : ℕ) : ZMod q) = 0 := by
        rw [CharP.cast_eq_zero_iff (ZMod q) q (r + s)]
        exact hdvd
      have hsum0 : (r : ZMod q) + (s : ZMod q) = 0 := by
        push_cast at hzero ⊢
        exact hzero
      have hneg : (r : ZMod q) = -(s : ZMod q) := by linear_combination hsum0
      rw [hneg]
      ring

/-- Integer form: for prime `q`, `q ∣ r² - s²` again only for `r = s` or `r + s = q`. -/
lemma prime_dvd_sq_sub_sq {q : ℕ} [Fact q.Prime] {r s : ℕ} (hr : r < q) (hs : s < q) :
    ((q : ℤ) ∣ (((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ))) ↔ (r = s ∨ r + s = q) := by
  have hx : ((((r ^ 2 : ℕ) : ℤ)) - (((s ^ 2 : ℕ) : ℤ))) = ((r : ℤ)) ^ 2 - ((s : ℤ)) ^ 2 := by
    push_cast
    ring
  have hz : (((((r : ℤ)) ^ 2 - ((s : ℤ)) ^ 2 : ℤ)) : ZMod q)
      = ((r : ZMod q)) ^ 2 - ((s : ZMod q)) ^ 2 := by
    push_cast
    ring
  rw [hx, ← ZMod.intCast_zmod_eq_zero_iff_dvd (((r : ℤ)) ^ 2 - ((s : ℤ)) ^ 2) q, hz, sub_eq_zero]
  exact zmod_sq_eq_sq_iff hr hs

end

end PEqualNP.Weyl
