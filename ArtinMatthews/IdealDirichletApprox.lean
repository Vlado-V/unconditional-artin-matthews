module

public import Mathlib.NumberTheory.DiophantineApproximation.Basic
public import Mathlib.Tactic


set_option backward.privateInPublic true
@[expose] public section

/-! The rational approximation used in the comparison proof is derived
at its actual product scale, for every real additive frequency. -/
namespace ArtinMatthews

theorem idealDirichletApprox (α Z S : ℝ) (hS : 0 < S) (hSZ : S ≤ Z) :
    ∃ (u : ℤ) (r : ℕ) (β : ℝ), 0 < r ∧ IsCoprime u (r : ℤ) ∧
      (r : ℝ) ≤ Z/S ∧ α = (u : ℝ)/r + β ∧
      |β| ≤ 1/(r : ℝ)^2 ∧ |β| * Z ≤ S/r := by
  have hZ : 0 < Z := hS.trans_le hSZ
  let N := ⌊Z/S⌋₊
  have hN : 0 < N := Nat.floor_pos.mpr ((le_div_iff₀ hS).mpr (by simpa using hSZ))
  obtain ⟨q, herr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hN
  have hr : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hden' : (q.den : ℝ) ≤ N := by exact_mod_cast hden
  have hNpos : 0 < (N : ℝ)+1 := by positivity
  have hfloor : (N : ℝ) ≤ Z/S := Nat.floor_le (div_nonneg hZ.le hS.le)
  have hZfloor : Z ≤ S*((N : ℝ)+1) := by
    have hh := (div_lt_iff₀ hS).mp (Nat.lt_floor_add_one (Z/S))
    linarith
  have hcop : IsCoprime q.num (q.den : ℤ) := by
    apply Int.isCoprime_iff_gcd_eq_one.mpr
    simpa only [Int.gcd_def, Int.natAbs_natCast] using q.reduced.gcd_eq_one
  refine ⟨q.num, q.den, α-(q : ℝ), q.pos, hcop, hden'.trans hfloor, ?_, ?_, ?_⟩
  · rw [Rat.cast_def]
    ring
  · exact herr.trans (one_div_le_one_div_of_le (by positivity) (by nlinarith))
  · apply (le_div_iff₀ hr).mpr
    calc
      _ ≤ (1/(((N : ℝ)+1)*q.den))*Z*q.den := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right herr hZ.le) hr.le
      _ = Z/((N : ℝ)+1) := by field_simp
      _ ≤ S := (div_le_iff₀ hNpos).mpr (by nlinarith)

end ArtinMatthews
