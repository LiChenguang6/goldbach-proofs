import PEqualNP.Weyl.Linear

/-!
# Layer 2a: conjugation and quadratic shift algebra

`conj (E x) = E (-x)`, hence the differenced term of `E (α n²)` is again a
linear character: `E (α (n+h)²) * conj (E (α n²)) = E (2αhn + αh²)`.
-/

namespace PEqualNP.Weyl

noncomputable section

lemma conj_E (x : ℝ) : star (E x) = E (-x) := by
  unfold E
  rw [Complex.star_def, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma E_mul_conj (x y : ℝ) : E x * star (E y) = E (x - y) := by
  rw [conj_E y, ← E_add]
  rfl

lemma E_quad_shift (α : ℝ) (n h : ℕ) :
    E (α * (((n + h : ℕ) : ℝ)) ^ 2) * star (E (α * ((n : ℝ)) ^ 2))
      = E (2 * α * (h : ℝ) * (n : ℝ) + α * ((h : ℝ)) ^ 2) := by
  rw [E_mul_conj]
  congr 1
  push_cast
  ring

end

end PEqualNP.Weyl


