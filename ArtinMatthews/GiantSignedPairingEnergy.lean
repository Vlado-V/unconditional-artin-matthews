module

public import Mathlib.Analysis.Complex.Basic
public import ArtinMatthews.GiantSignedWeightedPairing
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


set_option backward.privateInPublic true
@[expose] public section

/-! Finite original energies imply absolute convergence and the exact
weighted Cauchy bound for the untruncated pairing. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

theorem giantSignedWeightedPairing_summable_of_energy {ι : Type*}
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f g : ι → ℂ)
    (hf : (∑' i, ENNReal.ofReal (w i * ‖f i‖ ^ 2)) ≠ ∞)
    (hg : (∑' i, ENNReal.ofReal (w i * ‖g i‖ ^ 2)) ≠ ∞) :
    Summable (fun i => (w i : ℂ) * star (f i) * g i) :=
  giantSignedWeightedPairing_summable w hw f g
    (giantSignedWeightedEnergy_summable w hw f hf)
    (giantSignedWeightedEnergy_summable w hw g hg)

theorem giantSignedWeightedPairing_energy {ι : Type*}
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (f g : ι → ℂ)
    (hf : (∑' i, ENNReal.ofReal (w i * ‖f i‖ ^ 2)) ≠ ∞)
    (hg : (∑' i, ENNReal.ofReal (w i * ‖g i‖ ^ 2)) ≠ ∞) :
    ENNReal.ofReal (‖∑' i, (w i : ℂ) * star (f i) * g i‖ ^ 2) ≤
      (∑' i, ENNReal.ofReal (w i * ‖f i‖ ^ 2)) *
        ∑' i, ENNReal.ofReal (w i * ‖g i‖ ^ 2) := by
  have hsf := giantSignedWeightedEnergy_summable w hw f hf
  have hsg := giantSignedWeightedEnergy_summable w hw g hg
  have hpf (i : ι) : 0 ≤ w i * ‖f i‖ ^ 2 := mul_nonneg (hw i) (sq_nonneg _)
  have hpg (i : ι) : 0 ≤ w i * ‖g i‖ ^ 2 := mul_nonneg (hw i) (sq_nonneg _)
  calc
    _ ≤ ENNReal.ofReal ((∑' i, w i * ‖f i‖ ^ 2) * ∑' i, w i * ‖g i‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal (giantSignedWeightedPairing_sq_le w hw f g hsf hsg)
    _ = ENNReal.ofReal (∑' i, w i * ‖f i‖ ^ 2) *
        ENNReal.ofReal (∑' i, w i * ‖g i‖ ^ 2) :=
      ENNReal.ofReal_mul (tsum_nonneg hpf)
    _ = _ := by rw [ENNReal.ofReal_tsum_of_nonneg hpf hsf, ENNReal.ofReal_tsum_of_nonneg hpg hsg]

end
end ArtinMatthews
