module

public import ArtinMatthews.GiantSignedStateGhost


set_option backward.privateInPublic true
@[expose] public section

/-! The actual source visit coefficients on the original full state. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ (g : B) (p : PB g), NeZero p.val]

def giantSignedStateGhostGroup {M : ℕ} (ν : ∀ g, PB g → ℝ)
    (V : B → ℝ) (q ρ : ℝ) (w : GiantSignedState PS PB M → ℂ) :
    GiantSignedState PS PB M → ℂ :=
  giantSignedStateGhostApply PS ν (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ))
    (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ)) (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) w

theorem giantSignedStateGhostGroup_energy {M : ℕ}
    (hV : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (q ρ v : ℝ) (hv : 0 < v)
    (hrow : |q / ρ ^ 2| + |-(1-q) / ρ| / v ≤ 1)
    (hcol : ∀ g, |q / ρ ^ 2| + |-(1-q) * V g / ρ| / v ≤ 1)
    (w : GiantSignedState PS PB M → ℂ)
    (hws : ∀ s a, GiantSignedMemorySymmetric (fun m => w (s, a, m)))
    (Cf u : ℝ) (hCf : 0 ≤ Cf) (hu : 0 < u)
    (hw : ∀ s a m, ‖w (s, a, m)‖ ≤ Cf * u ^ (∑ g, m.1 g)) :
    giantSignedStateEnergy PS ν (giantSignedStateGhostGroup PS ν V q ρ w) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((|-(1-q) * V g / ρ| + |-(1-q) / ρ|) *
        (∑ p : PB g, ν g p) * v))) * giantSignedStateEnergy PS ν w := by
  have h := giantSignedStateGhostApply_energy PS hV ν hν
    (fun _ => ((q / ρ ^ 2 : ℝ) : ℂ)) (fun g => ((-(1-q) * V g / ρ : ℝ) : ℂ))
    (fun _ => ((-(1-q) / ρ : ℝ) : ℂ)) v hv
    (fun _ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hrow)
    (fun g => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hcol g)
    w hws Cf u hCf hu hw
  simpa only [giantSignedStateGhostGroup, Complex.norm_real, Real.norm_eq_abs] using h

end
end ArtinMatthews
