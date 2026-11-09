module

public import ArtinMatthews.MarkedMajorArcCenteredCoefficient


set_option backward.privateInPublic true
@[expose] public section

/-! Conjugating the literal centered coefficient reverses its real logarithmic
modulation; its prime-minus-rough amplitude is real. -/
namespace ArtinMatthews
open Finset ComplexConjugate

theorem marked_centered_coefficient_conj (W modulation : ℝ) (n : ℕ) :
    conj (markedMajorCenteredCoefficient W modulation n) =
      markedMajorCenteredCoefficient W (-modulation) n := by
  classical
  have harg : (n:ℂ).arg ≠ Real.pi := by
    rw [show (n:ℂ) = ((n:ℝ):ℂ) by simp,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact Real.pi_ne_zero.symm
  have hphase : conj ((n:ℂ)^((modulation:ℂ)*Complex.I)) =
      (n:ℂ)^(((-modulation:ℝ):ℂ)*Complex.I) := by
    have hh := (Complex.cpow_conj (n:ℂ) ((modulation:ℂ)*Complex.I) harg).symm
    simpa using hh
  unfold markedMajorCenteredCoefficient
  rw [map_mul,hphase]
  congr 1
  split_ifs <;> simp only [map_sub,map_mul,map_inv₀,Complex.conj_ofReal,map_one,map_zero]

noncomputable def markedMajorConjugateCenteredSum {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation t H u v : ℝ) : ℂ :=
  (H:ℂ)⁻¹ * ∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
    conj (markedMajorCenteredCoefficient W modulation n) *
      (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))

theorem marked_conjugate_centered_sum_eq {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W modulation t H u v : ℝ) :
    markedMajorConjugateCenteredSum χ W modulation t H u v =
      markedMajorCenteredSum χ W (-modulation) t H u v := by
  simp only [markedMajorConjugateCenteredSum,marked_centered_coefficient_conj,
    markedMajorCenteredSum]

end ArtinMatthews
