module

public import ArtinMatthews.GiantSignedTraceGhostAbsolute
public import ArtinMatthews.GiantSignedWordDomain
public import ArtinMatthews.GiantSignedProjectedWord


set_option backward.privateInPublic true
@[expose] public section

/-! The birth multiplier is inserted into the original simultaneous
move sum. It reads the actual ordered batches and no other move data. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (PS : S → Finset ℕ) {PB : B → Finset ℕ} {M : ℕ}

abbrev GiantSignedGhostBirthMultiplier (PB : B → Finset ℕ) :=
  (b : B → ℕ) → ((g : B) → Fin (b g) → PB g) → ℂ

def giantSignedStateGhostBirthApply (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (φ : GiantSignedGhostBirthMultiplier PB) (f : GiantSignedState PS PB M → ℂ)
    (s : GiantSignedState PS PB M) : ℂ :=
  ∑' r : GiantSignedGhostMemoryMoves s.2.2,
    giantSignedGhostMemoryMoveCoefficient ν A C D s.2.2 r *
      φ (fun g => (r g).2.1) (fun g => (r g).2.2) *
      f (s.1, s.2.1, giantSignedGhostMemoryMoveTarget s.2.2 r)

theorem giantSignedStateGhostBirthApply_one (ν : ∀ g, PB g → ℝ) (A C D : B → ℂ)
    (f : GiantSignedState PS PB M → ℂ) :
    giantSignedStateGhostBirthApply PS ν A C D (fun _ _ => 1) f =
      giantSignedStateGhostApply PS ν A C D f := by
  funext s
  unfold giantSignedStateGhostBirthApply giantSignedStateGhostApply giantSignedGhostSimultaneousApply
  simp only [mul_one]

theorem giantSignedStateGhostBirthApply_norm_le (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (A C D : B → ℂ) (φ : GiantSignedGhostBirthMultiplier PB) (hφ : ∀ b p, ‖φ b p‖ ≤ 1)
    (f : GiantSignedState PS PB M → ℂ) (hf : GiantSignedWordExponential f) (s : GiantSignedState PS PB M) :
    ‖giantSignedStateGhostBirthApply PS ν A C D φ f s‖ ≤
      ‖giantSignedStateGhostApply PS ν (fun g => (‖A g‖ : ℂ))
        (fun g => (‖C g‖ : ℂ)) (fun g => (‖D g‖ : ℂ)) (fun s => (‖f s‖ : ℂ)) s‖ := by
  obtain ⟨U,u,hU,hu,he⟩ := hf
  let a (r : GiantSignedGhostMemoryMoves s.2.2) := giantSignedGhostMemoryMoveCoefficient ν A C D s.2.2 r
  let w (r : GiantSignedGhostMemoryMoves s.2.2) := f (s.1,s.2.1,giantSignedGhostMemoryMoveTarget s.2.2 r)
  let w' (r : GiantSignedGhostMemoryMoves s.2.2) := a r * φ (fun g => (r g).2.1) (fun g => (r g).2.2) * w r
  have hs : Summable (fun r => ‖a r‖ * ‖w r‖) := by
    have h := giantSignedGhostSimultaneous_summable_norm ν hν A C D (fun m => f (s.1,s.2.1,m))
      U u hU hu (fun m => he (s.1,s.2.1,m)) s.2.2
    simpa only [a, w, norm_mul] using h
  have hw (r : GiantSignedGhostMemoryMoves s.2.2) : ‖w' r‖ ≤ ‖a r‖ * ‖w r‖ := by
    simp only [w', norm_mul]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (hφ _ _)) (norm_nonneg _)
  have hs' := hs.of_nonneg_of_le (fun _ => norm_nonneg _) hw
  have hmass : 0 ≤ giantSignedTraceRowMass (giantSignedGhostTraceRow ν A C D) (fun x => ‖f x‖) s :=
    tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  calc
    _ ≤ ∑' r, ‖w' r‖ := norm_tsum_le_tsum_norm hs'
    _ ≤ ∑' r, ‖a r‖ * ‖w r‖ := hs'.tsum_le_tsum hw hs
    _ = ‖(giantSignedTraceRowMass (giantSignedGhostTraceRow ν A C D) (fun x => ‖f x‖) s : ℂ)‖ :=
      ((Complex.norm_real _).trans (Real.norm_of_nonneg hmass)).symm
    _ = _ := congrArg norm (giantSignedGhostTraceRow_mass_coe ν hν A C D (fun x => ‖f x‖) s)

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedStateGhostBirthApply_exponential (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (A C D : B → ℂ) (φ : GiantSignedGhostBirthMultiplier PB) (hφ : ∀ b p, ‖φ b p‖ ≤ 1)
    (f : GiantSignedState PS PB M → ℂ) (hf : GiantSignedWordExponential f) :
    GiantSignedWordExponential (giantSignedStateGhostBirthApply PS ν A C D φ f) := by
  obtain ⟨U,u,hU,hu,he⟩ := hf
  let w : GiantSignedState PS PB M → ℂ := fun s => (‖f s‖ : ℂ)
  have hw (s : GiantSignedState PS PB M) : ‖w s‖ ≤ U * u ^ (∑ g, s.2.2.1 g) := by
    simpa only [w, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)] using he s
  obtain ⟨U',u',hU',hu',hg⟩ := giantSignedStateGhostApply_exponential PS ν hν
    (fun g => (‖A g‖ : ℂ)) (fun g => (‖C g‖ : ℂ)) (fun g => (‖D g‖ : ℂ))
    w U u hU hu (fun s a m => hw (s,a,m))
  exact ⟨U',u',hU',hu',fun s => (giantSignedStateGhostBirthApply_norm_le PS ν hν A C D φ hφ f
    ⟨U,u,hU,hu,he⟩ s).trans (hg s.1 s.2.1 s.2.2)⟩

def giantSignedStateGhostBirthGroup (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (qi ρ : ℝ)
    (φ : GiantSignedGhostBirthMultiplier PB) (f : GiantSignedState PS PB M → ℂ) :
    GiantSignedState PS PB M → ℂ :=
  giantSignedStateGhostBirthApply PS ν (fun _ => ((qi / ρ^2 : ℝ) : ℂ))
    (fun g => ((-(1-qi) * V g / ρ : ℝ) : ℂ)) (fun _ => ((-(1-qi) / ρ : ℝ) : ℂ)) φ f

def giantSignedProjectedBirthVisit {PS : S → Finset ℕ} (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (qi ρ : ℝ) (φ : GiantSignedGhostBirthMultiplier PB)
    (f : GiantSignedState PS PB M → ℂ) : GiantSignedState PS PB M → ℂ :=
  giantSignedStateMemoryCutoff H
    (giantSignedStateGhostBirthGroup PS ν V qi ρ φ (giantSignedStateMemoryCutoff H f))

theorem giantSignedProjectedBirthVisit_one {PS : S → Finset ℕ} (H : ℕ)
    (ν : ∀ g, PB g → ℝ) (V : B → ℝ) (qi ρ : ℝ) (f : GiantSignedState PS PB M → ℂ) :
    giantSignedProjectedBirthVisit H ν V qi ρ (fun _ _ => 1) f =
      giantSignedProjectedVisit H ν V qi ρ f := by
  simp only [giantSignedProjectedBirthVisit, giantSignedStateGhostBirthGroup,
    giantSignedStateGhostBirthApply_one, giantSignedProjectedVisit, giantSignedChronologicalVisit,
    giantSignedStateGhostGroup]

end
end ArtinMatthews
