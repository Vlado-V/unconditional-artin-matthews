module

public import ArtinMatthews.GiantSignedSourceVisitEnergy


set_option backward.privateInPublic true
@[expose] public section

/-! The actual absolute ghost visit with doubled birth weight has the
same source memory-weight choice as the signed visit. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

def giantSignedSourceDoubledVisit (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (qi ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) : GiantSignedState PS PB M → ℂ :=
  giantSignedStateGhostApply PS ν (fun _ => (|qi / ρ ^ 2| : ℝ))
    (fun g => (2 * |-(1-qi) * V g / ρ| : ℝ))
    (fun _ => (|-(1-qi) / ρ| : ℝ)) f

theorem giantSignedSourceDoubledVisit_energy
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (hMass : ∀ g, (∑ p : PB g, ν g p) ≤ 2)
    (V : B → ℝ) {Vmax qi ρ v C₀ L : ℝ}
    (hVmax : 0 ≤ Vmax) (hV0 : ∀ g, 0 ≤ V g) (hV : ∀ g, V g ≤ Vmax)
    (hVS : ∀ g, 0 < bandReciprocalMass (PS g))
    (hρ : 0 < ρ) (hv : 0 < v) (hqi0 : 0 ≤ qi) (hqi1 : qi ≤ 1)
    (hL : 0 < L) (hgroups : (Fintype.card B : ℝ) ≤ C₀ * Real.log L)
    (hrow : |qi / ρ ^ 2| + |-(1-qi) / ρ| / v ≤ 1)
    (hcol : ∀ g, |qi / ρ ^ 2| + 2 * |-(1-qi) * V g / ρ| / v ≤ 1)
    (f : GiantSignedState PS PB M → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m)))
    (U u : ℝ) (hU : 0 ≤ U) (hu : 0 < u)
    (hf : ∀ s a m, ‖f (s,a,m)‖ ≤ U * u ^ (∑ g, m.1 g)) :
    giantSignedStateEnergy PS ν (giantSignedSourceDoubledVisit PS ν V qi ρ f) ≤
      ENNReal.ofReal (L ^ giantSignedSourceVisitExponent C₀ (2 * Vmax) ρ v) *
        giantSignedStateEnergy PS ν f := by
  let A : B → ℂ := fun _ => (|qi / ρ ^ 2| : ℝ)
  let C : B → ℂ := fun g => (2 * |-(1-qi) * V g / ρ| : ℝ)
  let D : B → ℂ := fun _ => (|-(1-qi) / ρ| : ℝ)
  have hA (g : B) : ‖A g‖ = |qi / ρ ^ 2| := by
    simp only [A, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  have hC (g : B) : ‖C g‖ = 2 * |-(1-qi) * V g / ρ| := by
    change ‖((2 * |-(1-qi) * V g / ρ| : ℝ) : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hD (g : B) : ‖D g‖ = |-(1-qi) / ρ| := by
    simp only [D, Complex.norm_real, Real.norm_eq_abs, abs_abs]
  have he := giantSignedStateGhostApply_energy PS hVS ν hν A C D v hv
    (fun g => by rw [hA g, hD g]; exact hrow) (fun g => by rw [hA g, hC g]; exact hcol g)
    f hsym U u hU hu hf
  simp only [hC, hD] at he
  refine he.trans (mul_le_mul_left ?_ _)
  have hfactor := giantSignedSourceVisitFactor_le PB ν hν hMass (fun g => 2 * V g)
    (mul_nonneg (by norm_num) hVmax) (fun g => mul_nonneg (by norm_num) (hV0 g))
    (fun g => mul_le_mul_of_nonneg_left (hV g) (by norm_num)) hρ hv.le hqi0 hqi1 hL hgroups
  have hscale (g : B) : |-(1-qi) * (2 * V g) / ρ| = 2 * |-(1-qi) * V g / ρ| := by
    rw [show -(1-qi) * (2 * V g) / ρ = 2 * (-(1-qi) * V g / ρ) by ring,
      abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
  simpa only [hscale] using hfactor

end
end ArtinMatthews
