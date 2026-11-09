module

public import ArtinMatthews.GiantSignedSourceDoubledVisit
public import ArtinMatthews.GiantSignedWordDomain


set_option backward.privateInPublic true
@[expose] public section

/-! The doubled absolute ghost visit preserves the original full-memory
domain and pending symmetry. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

variable {S B : Type*} [Fintype S] [Fintype B] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}
    [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedSourceDoubledVisit_exponential
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (qi ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) (hf : GiantSignedWordExponential f) :
    GiantSignedWordExponential (giantSignedSourceDoubledVisit PS ν V qi ρ f) := by
  obtain ⟨U, u, hU, hu, h⟩ := hf
  obtain ⟨U', u', hU', hu', hg⟩ := giantSignedStateGhostApply_exponential PS ν hν
    (fun _ => (|qi / ρ ^ 2| : ℝ)) (fun g => (2 * |-(1-qi) * V g / ρ| : ℝ))
    (fun _ => (|-(1-qi) / ρ| : ℝ)) f U u hU hu (fun s a m => h (s,a,m))
  exact ⟨U', u', hU', hu', fun ⟨s,a,m⟩ => hg s a m⟩

theorem giantSignedSourceDoubledVisit_memorySymmetric
    (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p) (V : B → ℝ) (qi ρ : ℝ)
    (f : GiantSignedState PS PB M → ℂ) (hf : GiantSignedWordExponential f)
    (hsym : ∀ s a, GiantSignedMemorySymmetric (fun m => f (s,a,m))) :
    ∀ s a, GiantSignedMemorySymmetric (fun m => giantSignedSourceDoubledVisit PS ν V qi ρ f (s,a,m)) := by
  obtain ⟨U, u, hU, hu, h⟩ := hf
  exact giantSignedStateGhostApply_memorySymmetric PS ν hν
    (fun _ => (|qi / ρ ^ 2| : ℝ)) (fun g => (2 * |-(1-qi) * V g / ρ| : ℝ))
    (fun _ => (|-(1-qi) / ρ| : ℝ)) f hsym U u hU hu (fun s a m => h (s,a,m))

end
end ArtinMatthews
