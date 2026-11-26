import PEqualNP.Weyl.Basic

/-!
# Layer 1: the trig identity behind the linear Weyl bound

`‖E α - 1‖ = 2 |sin (πα)|`, plus the half-angle factorisation used to get it.
-/

namespace PEqualNP.Weyl

noncomputable section
open scoped BigOperators

lemma E_zero : E 0 = 1 := by
  unfold E
  simp

lemma E_neg_mul (x : ℝ) : E (-x) * E x = 1 := by
  rw [← E_add]
  ring_nf
  simp [E_zero]

/-- Real/imaginary decomposition of the character. -/
lemma E_eq (α : ℝ) :
    E α = (Real.cos (2 * Real.pi * α) : ℂ) + (Real.sin (2 * Real.pi * α) : ℂ) * Complex.I := by
  unfold E
  exact Complex.exp_ofReal_mul_I (2 * Real.pi * α)

lemma E_sub_neg (x : ℝ) :
    E x - E (-x) = 2 * Complex.I * (Real.sin (2 * Real.pi * x) : ℂ) := by
  have hx := E_eq x
  have hnx : E (-x) = (Real.cos (2 * Real.pi * x) : ℂ) -
      (Real.sin (2 * Real.pi * x) : ℂ) * Complex.I := by
    rw [E_eq (-x)]
    rw [show 2 * Real.pi * -x = -(2 * Real.pi * x) by ring]
    rw [Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [hx, hnx]
  push_cast
  ring

/-- Half-angle factorisation: `E α - 1 = E (α/2) * (E (α/2) - E (-α/2))`. -/
lemma E_alpha_sub_one (α : ℝ) :
    E α - 1 = E (α / 2) * (E (α / 2) - E (-(α / 2))) := by
  have h1 : E (α / 2) * E (α / 2) = E α := by
    rw [← E_add]
    ring_nf
  have h2 : E (α / 2) * E (-(α / 2)) = 1 := by
    rw [← E_add]
    ring_nf
    simp [E_zero]
  calc E α - 1 = E (α / 2) * E (α / 2) - E (α / 2) * E (-(α / 2)) := by rw [h1, h2]
    _ = E (α / 2) * (E (α / 2) - E (-(α / 2))) := by ring

/-- Layer 1 main identity: `‖E α - 1‖ = 2 |sin (πα)|`. -/
lemma norm_E_sub_one (α : ℝ) : ‖E α - 1‖ = 2 * |Real.sin (Real.pi * α)| := by
  rw [E_alpha_sub_one, norm_mul, norm_E, one_mul]
  rw [E_sub_neg (α / 2), norm_mul]
  have hI : ‖(2 : ℂ) * Complex.I‖ = 2 := by simp
  rw [hI]
  have h : 2 * Real.pi * (α / 2) = Real.pi * α := by ring
  rw [h, Complex.norm_real, Real.norm_eq_abs]

end

end PEqualNP.Weyl
