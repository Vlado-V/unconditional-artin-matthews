module

public import ArtinMatthews.GiantSignedGhostBirthApply
public import ArtinMatthews.GiantSignedEnergyDomination
public import ArtinMatthews.GiantSignedCappedStateDomain


set_option backward.privateInPublic true
@[expose] public section

/-! A birth multiplier of modulus at most one inherits the exact
absolute ghost energy bound on the original factorial state measure. -/
namespace ArtinMatthews
open scoped BigOperators ENNReal
noncomputable section

universe u
variable {S B : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]
    [∀ g, ∀ p : PB g, NeZero p.val]

theorem giantSignedStateGhostBirthApply_energy
    (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ)
    (v : ℝ) (hv : 0 < v)
    (hrow : ∀ g, ‖A g‖ + ‖D g‖ / v ≤ 1) (hcol : ∀ g, ‖A g‖ + ‖C g‖ / v ≤ 1)
    (φ : GiantSignedGhostBirthMultiplier PB) (hφ : ∀ b p, ‖φ b p‖ ≤ 1)
    (f : GiantSignedState PS PB M → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m)))
    (hf : GiantSignedWordExponential f) :
    giantSignedStateEnergy PS ν (giantSignedStateGhostBirthApply PS ν A C D φ f) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((‖C g‖ + ‖D g‖) * (∑ p : PB g, ν g p) * v))) *
        giantSignedStateEnergy PS ν f := by
  let a : B → ℂ := fun g => (‖A g‖ : ℂ)
  let c : B → ℂ := fun g => (‖C g‖ : ℂ)
  let d : B → ℂ := fun g => (‖D g‖ : ℂ)
  let w : GiantSignedState PS PB M → ℂ := fun s => (‖f s‖ : ℂ)
  have hdom : ∀ s, ‖giantSignedStateGhostBirthApply PS ν A C D φ f s‖ ≤
      1 * ‖giantSignedStateGhostApply PS ν a c d w s‖ := by
    intro s
    simpa only [one_mul] using giantSignedStateGhostBirthApply_norm_le PS ν hν A C D φ hφ f hf s
  have hE := giantSignedStateEnergy_norm_domination PS hVS ν hν _ _ 1 hdom
  simp only [one_pow, ENNReal.ofReal_one, one_mul] at hE
  have hsym' (s : GiantTwoSidedResidueState PS M) (t : MarkedPhysicalMarking PB M) :
      GiantSignedMemorySymmetric (fun m => w (s,t,m)) :=
    fun m σ => congrArg (fun z : ℂ => (‖z‖ : ℂ)) (hsym s t m σ)
  obtain ⟨U,u,hU,hu,he⟩ := hf
  have hw (s : GiantSignedState PS PB M) : ‖w s‖ ≤ U*u^(∑ g, s.2.2.1 g) := by
    simpa only [w, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using he s
  have henergy := giantSignedStateGhostApply_energy PS hVS ν hν a c d v hv
    (fun g => by simpa only [a, d, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using hrow g)
    (fun g => by simpa only [a, c, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using hcol g)
    w hsym' U u hU hu (fun s t m => hw (s,t,m))
  have hW : giantSignedStateEnergy PS ν w = giantSignedStateEnergy PS ν f := by
    unfold giantSignedStateEnergy
    simp only [w, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  refine hE.trans ?_
  simpa only [c, d, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), hW] using henergy

theorem giantSignedProjectedBirthVisit_energy [Fintype (GiantTwoSidedResidueState PS M)]
    (H : ℕ) (hVS : ∀ j, 0 < bandReciprocalMass (PS j))
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ)
    (qi ρ v : ℝ) (hv : 0 < v) (hrow : |qi/ρ^2| + |-(1-qi)/ρ|/v ≤ 1)
    (hcol : ∀ g, |qi/ρ^2| + |-(1-qi)*V g/ρ|/v ≤ 1)
    (φ : GiantSignedGhostBirthMultiplier PB) (hφ : ∀ b p, ‖φ b p‖ ≤ 1)
    (f : GiantSignedState PS PB M → ℂ)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    giantSignedStateEnergy PS ν (giantSignedProjectedBirthVisit H ν V qi ρ φ f) ≤
      (∏ g, ENNReal.ofReal (Real.exp ((|-(1-qi)*V g/ρ| + |-(1-qi)/ρ|) *
        (∑ p : PB g, ν g p) * v))) * giantSignedStateEnergy PS ν f := by
  let w := giantSignedStateMemoryCutoff H f
  let a : B → ℂ := fun _ => ((qi/ρ^2:ℝ):ℂ)
  let c : B → ℂ := fun g => ((-(1-qi)*V g/ρ:ℝ):ℂ)
  let d : B → ℂ := fun _ => ((-(1-qi)/ρ:ℝ):ℂ)
  have he := giantSignedStateGhostBirthApply_energy hVS ν hν a c d v hv
    (fun _ => by simpa only [a,d,Complex.norm_real,Real.norm_eq_abs] using hrow)
    (fun g => by simpa only [a,c,Complex.norm_real,Real.norm_eq_abs] using hcol g) φ hφ w
    (giantSignedStateMemoryCutoff_memory_symmetric H f hsym) (giantSignedStateMemoryCutoff_exponential H f)
  let C := ∏ g, ENNReal.ofReal (Real.exp ((|-(1-qi)*V g/ρ| + |-(1-qi)/ρ|) *
    (∑ p : PB g, ν g p) * v))
  have hbound : giantSignedStateEnergy PS ν (giantSignedStateGhostBirthGroup PS ν V qi ρ φ w) ≤
      C * giantSignedStateEnergy PS ν w := by
    simpa only [giantSignedStateGhostBirthGroup, C, a, c, d, Complex.norm_real, Real.norm_eq_abs] using he
  exact (giantSignedStateMemoryCutoff_energy_le ν H _).trans
    (hbound.trans (mul_le_mul_right (giantSignedStateMemoryCutoff_energy_le ν H f) C))

end
end ArtinMatthews
