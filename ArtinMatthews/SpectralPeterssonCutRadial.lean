module

public import ArtinMatthews.SpectralPeterssonTruncatedMass
public import ArtinMatthews.SpectralPeterssonStripIntegrable


set_option backward.privateInPublic true
@[expose] public section

/-! The exact vertical factor in a pair of sharply truncated holomorphic
seeds is integrable for all weights at least two. -/
noncomputable section
open Set MeasureTheory

namespace ArtinMatthews

def spectralPeterssonCutPairRadial (k : ℕ) (m n : ℕ+) (A y : ℝ) : ℝ :=
  if A < 4*Real.pi*(m : ℝ)*y ∧ A < 4*Real.pi*(n : ℝ)*y then
    y^(k-2)*Real.exp (-(2*Real.pi*((m : ℝ)+(n : ℝ))*y)) else 0

theorem spectralPeterssonCutPairRadial_integrable (k : ℕ) (hk : 2 ≤ k)
    (m n : ℕ+) (A : ℝ) :
    IntegrableOn (spectralPeterssonCutPairRadial k m n A) (Ioi (0 : ℝ)) := by
  let r : ℝ := 2*Real.pi*((m : ℝ)+(n : ℝ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hs : 0 < ((k-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < k-1 by omega)
  have he : ((k-1 : ℕ) : ℝ)-1 = ((k-2 : ℕ) : ℝ) := by
    have h : ((k-2 : ℕ) : ℝ)+1 = ((k-1 : ℕ) : ℝ) := by
      exact_mod_cast (show k-2+1 = k-1 by omega)
    linarith
  have hbase : IntegrableOn (fun y : ℝ => y^(k-2)*Real.exp (-(r*y))) (Ioi (0 : ℝ)) := by
    simpa only [he,Real.rpow_natCast] using spectralPetersson_gammaEnvelope_integrable ((k-1 : ℕ) : ℝ) r hs hr
  have hm : Measurable (fun y : ℝ => 4*Real.pi*(m : ℝ)*y) := by fun_prop
  have hn : Measurable (fun y : ℝ => 4*Real.pi*(n : ℝ)*y) := by fun_prop
  have hset : MeasurableSet {y : ℝ | A < 4*Real.pi*(m : ℝ)*y ∧ A < 4*Real.pi*(n : ℝ)*y} :=
    (measurableSet_lt measurable_const hm).inter (measurableSet_lt measurable_const hn)
  apply (hbase.indicator hset).congr_fun _ measurableSet_Ioi
  intro y hy
  simp only [spectralPeterssonCutPairRadial,Set.indicator_apply,Set.mem_setOf_eq,r]

theorem spectralPeterssonCutPairRadial_diagonal (k : ℕ) (n : ℕ+) (A : ℝ) (hA : 0 ≤ A) :
    (∫ y in Ioi (0 : ℝ), spectralPeterssonCutPairRadial k n n A y) =
      spectralPeterssonTruncatedMass k n A := by
  let r : ℝ := 4*Real.pi*(n : ℝ)
  have hr : 0 < r := by dsimp [r]; positivity
  have hzero (y : ℝ) (hy : y ∉ Ioi (0 : ℝ)) : spectralPeterssonCutPairRadial k n n A y = 0 := by
    have hy0 : y ≤ 0 := not_lt.mp hy
    have hn : ¬A < r*y := not_lt.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos hr.le hy0) hA)
    simp only [spectralPeterssonCutPairRadial,show 2*Real.pi*((n : ℝ)+(n : ℝ)) = r by dsimp [r]; ring]
    exact if_neg (fun h => hn h.1)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have he : spectralPeterssonCutPairRadial k n n A =
      (Ioi (A/r)).indicator (fun y : ℝ => y^(k-2)*Real.exp (-(r*y))) := by
    funext y
    have hcut : A < r*y ↔ A/r < y := by
      simpa only [mul_comm] using (div_lt_iff₀ hr : A/r < y ↔ A < y*r).symm
    simp only [spectralPeterssonCutPairRadial,Set.indicator_apply,mem_Ioi,
      show 2*Real.pi*((n : ℝ)+(n : ℝ)) = r by dsimp [r]; ring,and_self]
    change (if A < r*y then y^(k-2)*Real.exp (-(r*y)) else 0) = _
    simp only [hcut]
  rw [he,integral_indicator measurableSet_Ioi]
  rfl

end ArtinMatthews
