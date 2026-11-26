import Mathlib

theorem PEqualNP.Outside.L_goldbach_factor_line_fiber_determinant :
    ∀ (a b N r₀ s₀ g i j : ℤ), 0 < g → g ∣ a → g ∣ b →
      a*r₀+b*s₀=N →
      (r₀+(b/g)*i)*(s₀-(a/g)*j)-(r₀+(b/g)*j)*(s₀-(a/g)*i)=-(N/g)*(j-i) := by
  intro a b N r₀ s₀ g i j hg ha hb h
  have ha' : g * (a / g) = a := Int.mul_ediv_cancel' ha
  have hb' : g * (b / g) = b := Int.mul_ediv_cancel' hb
  have hmul : g * ((a / g) * r₀ + (b / g) * s₀) = N := by
    calc
      g * ((a / g) * r₀ + (b / g) * s₀) =
          (g * (a / g)) * r₀ + (g * (b / g)) * s₀ := by ring
      _ = N := by rw [ha', hb', h]
  have hd : g ∣ N := ⟨_, hmul.symm⟩
  have hN : g * (N / g) = N := Int.mul_ediv_cancel' hd
  have hsum : (a / g) * r₀ + (b / g) * s₀ = N / g := by
    apply mul_left_cancel₀ (ne_of_gt hg)
    exact hmul.trans hN.symm
  calc
    (r₀+(b/g)*i)*(s₀-(a/g)*j)-(r₀+(b/g)*j)*(s₀-(a/g)*i) =
        -((a/g)*r₀+(b/g)*s₀)*(j-i) := by ring
    _ = _ := by rw [hsum]
