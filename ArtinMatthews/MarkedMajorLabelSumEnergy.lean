module

public import ArtinMatthews.MarkedMajorLabelDyadEnergy
public import ArtinMatthews.MarkedMajorEnergyBounded


set_option backward.privateInPublic true
@[expose] public section

/-! Finite dyadic energy summation with its literal squared cardinality cost. -/
namespace ArtinMatthews
open Finset MeasureTheory

theorem markedMajor_finite_sum_energy {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℂ)
    (hf : ∀ j ∈ S,Continuous (f j)) (T E : ℝ)
    (he : ∀ j ∈ S,(∫ t in Set.Icc (-T) T,‖f j t‖^2) ≤ E) :
    (∫ t in Set.Icc (-T) T,‖∑ j ∈ S,f j t‖^2) ≤ (S.card:ℝ)^2*E := by
  have hi : ∀ j ∈ S,IntegrableOn (fun t => ‖f j t‖^2) (Set.Icc (-T) T) :=
    fun j hj => ((hf j hj).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hsum : Continuous (fun t => ∑ j ∈ S,f j t) := continuous_finsetSum S hf
  have hsumInt : IntegrableOn (fun t => ‖∑ j ∈ S,f j t‖^2) (Set.Icc (-T) T) :=
    (hsum.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  calc
    _ ≤ ∫ t in Set.Icc (-T) T,(S.card:ℝ)*∑ j ∈ S,‖f j t‖^2 := by
      apply integral_mono hsumInt ((integrable_finsetSum S hi).const_mul _)
      intro t
      change ‖∑ j ∈ S,f j t‖^2 ≤ _
      have hcs := sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun j => ‖f j t‖)
      simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hcs
      exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs
    _ = (S.card:ℝ)*∑ j ∈ S,(∫ t in Set.Icc (-T) T,‖f j t‖^2) := by
      rw [integral_const_mul,integral_finsetSum S hi]
    _ ≤ (S.card:ℝ)*∑ _j ∈ S,E := mul_le_mul_of_nonneg_left (sum_le_sum he) (Nat.cast_nonneg _)
    _ = _ := by simp; ring

theorem markedMajorLabelDyad_continuous {J : Type*} [Fintype J]
    (P : J → Finset ℕ) (S : Finset ℕ) (η : ℝ → ℂ) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (θ Y V : ℝ) :
    Continuous (markedMajorLabelDyad P S η χ θ Y V) := by
  unfold markedMajorLabelDyad markedPrimePhase
  fun_prop

end ArtinMatthews
