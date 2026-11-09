module

public import ArtinMatthews.VaryingKummerAnalyticMixedZetaOrders


set_option backward.privateInPublic true
@[expose] public section

/-! The literal finite set of completed-Dedekind zeros in a bounded height
window, and the full pole set for the smoothed explicit-formula rectangle. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField Complex Set
open OAI.PrimeDegreePackets.AnalyticGrowth
open scoped Classical
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

def mixedContourZeros (T : ℝ) : Finset ℂ :=
  (zeroDiskFinset (mixedCompletedDedekindXi K) (T+2)).filter (fun ρ => |ρ.im| ≤ T)

theorem mem_mixedContourZeros (T : ℝ) (ρ : ℂ) :
    ρ ∈ mixedContourZeros K T ↔ mixedCompletedDedekindXi K ρ = 0 ∧ |ρ.im| ≤ T := by
  rw [mixedContourZeros,Finset.mem_filter]
  constructor
  · rintro ⟨hm,hT⟩
    refine ⟨?_,hT⟩
    apply (zeroMultiplicity_ne_zero_iff (mixedCompletedDedekindXi_entire K)
      (mixedCompletedDedekindXi_zero_ne_zero K) ρ).mp
    have H := (mem_zeroDiskFinset (mixedCompletedDedekindXi K) (T+2) ρ).mp hm
    rwa [divisor_closedBall_eq_multiplicity (mixedCompletedDedekindXi_entire K)
      (zeroDiskFinset_norm_le hm)] at H
  · rintro ⟨hz,hT⟩
    refine ⟨?_,hT⟩
    have hstrip := mixedCompletedDedekindXi_zeros_in_strip K ρ hz
    have hn : ‖ρ‖ ≤ T+2 := by
      have H := Complex.norm_le_abs_re_add_abs_im ρ
      rw [abs_of_nonneg hstrip.1] at H
      linarith [hstrip.2]
    rw [mem_zeroDiskFinset,divisor_closedBall_eq_multiplicity
      (mixedCompletedDedekindXi_entire K) hn]
    exact (zeroMultiplicity_ne_zero_iff (mixedCompletedDedekindXi_entire K)
      (mixedCompletedDedekindXi_zero_ne_zero K) ρ).mpr hz

theorem zero_not_mem_mixedContourZeros (T : ℝ) : (0 : ℂ) ∉ mixedContourZeros K T := by
  intro h
  exact mixedCompletedDedekindXi_zero_ne_zero K ((mem_mixedContourZeros K T 0).mp h).1

theorem one_not_mem_mixedContourZeros (T : ℝ) : (1 : ℂ) ∉ mixedContourZeros K T := by
  intro h
  exact mixedCompletedDedekindXi_one_ne_zero K ((mem_mixedContourZeros K T 1).mp h).1

def mixedContourPoles (T : ℝ) : Finset ℂ := insert 0 (insert 1 (mixedContourZeros K T))

theorem mixedContourPoles_inside {T : ℝ} (hT : 0 < T)
    (havoid : ∀ ρ,mixedCompletedDedekindXi K ρ = 0 → |ρ.im| ≠ T) :
    ∀ z ∈ mixedContourPoles K T,-(1/2 : ℝ)<z.re ∧ z.re<2 ∧ -T<z.im ∧ z.im<T := by
  intro z hz
  simp only [mixedContourPoles,Finset.mem_insert] at hz
  rcases hz with rfl | rfl | hz
  · norm_num
    exact hT
  · norm_num
    exact hT
  · have H := (mem_mixedContourZeros K T z).mp hz
    have hs := mixedCompletedDedekindXi_zeros_in_strip K z H.1
    have him := abs_lt.mp (lt_of_le_of_ne H.2 (havoid z H.1))
    exact ⟨by linarith [hs.1],by linarith [hs.2],him.1,him.2⟩

end
end ArtinMatthews.VaryingKummerAnalytic
