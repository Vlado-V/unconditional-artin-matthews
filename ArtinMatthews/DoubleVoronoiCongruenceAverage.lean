module

public import ArtinMatthews.KloostermanWeightedStationary


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized d-congruence average in the double-Voronoi step is
exactly its residue indicator, including composite d. -/

namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {R : Type*} [CommRing R] [Fintype R]
attribute [local instance] Classical.decEq

omit [Fintype R] in
/-- The inverse-linear dual condition is exactly the square-residue
condition because the reduced circle numerator is a unit. -/
theorem inverse_linear_eq_zero_iff (v : Rˣ) (k : R) :
    k*(↑v⁻¹ : R)-(v : R)=0 ↔ k=(v : R)^2 := by
  rw [sub_eq_zero]
  constructor
  · intro h
    have hm := congrArg (fun x : R => x*(v : R)) h
    simpa only [mul_assoc, Units.inv_mul, mul_one, pow_two] using hm
  · intro h
    rw [h, pow_two, mul_assoc, Units.mul_inv, mul_one]

/-- Exact finite normalized average; no divisor or modulus loss. -/
theorem inverse_linear_character_average (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (v : Rˣ) (k : R) :
    (∑ j : R, ψ (j*(k*(↑v⁻¹ : R)-(v : R)))) / (Fintype.card R : ℂ) =
      if k=(v : R)^2 then 1 else 0 := by
  have hc : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [AddChar.sum_mulShift _ hψ]
  simp only [inverse_linear_eq_zero_iff]
  split_ifs <;> simp [hc]

end
end ArtinMatthews
