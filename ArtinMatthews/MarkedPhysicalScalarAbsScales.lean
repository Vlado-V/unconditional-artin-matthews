module

public import ArtinMatthews.MarkedMajorLabelPolynomial
public import Mathlib.NumberTheory.Harmonic.Bounds


set_option backward.privateInPublic true
@[expose] public section

/-! Fixed constants and logarithmic powers for the absolute scalar
masses. The band normalizer contributes a fixed constant. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators

theorem markedPhysicalScalar_labelMass_bound {J : Type*} [Fintype J]
    (P : J → Finset ℕ) {v : ℝ} (hv : 0 < v) (hV : ∀ j,v ≤ bandReciprocalMass (P j)) :
    0 ≤ markedMajorLabelMass P ∧ markedMajorLabelMass P ≤ (v⁻¹)^(Fintype.card J) := by
  have hVp (j : J) : 0 < bandReciprocalMass (P j) := hv.trans_le (hV j)
  refine ⟨(markedMajorLabelMass_pos P hVp).le,?_⟩
  unfold markedMajorLabelMass
  have h := Finset.prod_le_prod₀ (s := (Finset.univ : Finset J))
    (f := fun j => (bandReciprocalMass (P j))⁻¹) (g := fun _ => v⁻¹)
    (fun j _ => (inv_pos.mpr (hVp j)).le) (fun j _ => inv_anti₀ hv (hV j))
  simpa only [Finset.prod_const,Finset.card_univ] using h

theorem markedPhysicalScalar_harmonic_log_le {x K : ℝ} {Z : ℕ}
    (hx : 0 < x) (hL : 1 ≤ Real.log x) (hK : 0 < K) (hZ : 1 ≤ Z) (hbox : (Z:ℝ) ≤ K*x) :
    1+Real.log (Z:ℝ) ≤ (K+1)*Real.log x ∧
      (∑ d ∈ Finset.Icc 1 Z,1/(d:ℝ)) ≤ (K+1)*Real.log x := by
  have hzp : 0 < (Z:ℝ) := by exact_mod_cast (zero_lt_one.trans_le hZ)
  have hlog := Real.log_le_log hzp hbox
  rw [Real.log_mul hK.ne' hx.ne'] at hlog
  have h : 1+Real.log (Z:ℝ) ≤ (K+1)*Real.log x := by
    nlinarith [Real.log_le_sub_one_of_pos hK,mul_nonneg hK.le (sub_nonneg.mpr hL)]
  refine ⟨h,?_⟩
  have hh : (∑ d ∈ Finset.Icc 1 Z,1/(d:ℝ)) ≤ 1+Real.log (Z:ℝ) := by
    simpa only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
      using harmonic_le_one_add_log Z
  exact hh.trans h

def markedPhysicalScalarAbsLogExponent (Cα Cβ Qexp : ℝ) : ℝ :=
  2*(Cα+Cβ)+3*Qexp+3

theorem markedPhysicalScalarAbs_log_powers {L : ℝ} (hL : 0 < L) (Cα Cβ Qexp : ℝ) :
    (L^Cα*L^Cβ)^2*(L^Qexp)^3*L^3=L^(markedPhysicalScalarAbsLogExponent Cα Cβ Qexp) := by
  rw [← Real.rpow_add hL,← Real.rpow_mul_natCast hL.le,← Real.rpow_mul_natCast hL.le,
    ← Real.rpow_natCast L 3,← Real.rpow_add hL,← Real.rpow_add hL]
  congr 1
  unfold markedPhysicalScalarAbsLogExponent
  push_cast
  ring

end
end ArtinMatthews
