module

public import ArtinMatthews.GiantSignedTraceRows
public import ArtinMatthews.GiantSignedStateGhostGrowth


set_option backward.privateInPublic true
@[expose] public section

/-! The actual ghost trace mass uses the absolute coefficients of the
original all-degree row. Both its convergence and growth are derived. -/
namespace ArtinMatthews
open scoped BigOperators
noncomputable section

universe u
variable {S B : Type u} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {PS : S → Finset ℕ} {PB : B → Finset ℕ} {M : ℕ}

theorem giantSignedGhostMemoryMoveCoefficient_norm (ν : ∀ g, PB g → ℝ)
    (hν : ∀ g p, 0 ≤ ν g p) (A C D : B → ℂ) (m : GiantSignedMemory PB)
    (r : GiantSignedGhostMemoryMoves m) :
    (‖giantSignedGhostMemoryMoveCoefficient ν A C D m r‖ : ℂ) =
      giantSignedGhostMemoryMoveCoefficient ν (fun g => (‖A g‖ : ℂ))
        (fun g => (‖C g‖ : ℂ)) (fun g => (‖D g‖ : ℂ)) m r := by
  simp only [giantSignedGhostMemoryMoveCoefficient, giantSignedGhostProductMoveCoefficient,
    norm_prod, Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun g _ =>
    giantSignedGhostMoveCoefficient_norm (ν g) (hν g) (A g) (C g) (D g) _ (r g))

theorem giantSignedGhostTraceRow_mass_coe (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (A C D : B → ℂ) (f : GiantSignedState PS PB M → ℝ) (s : GiantSignedState PS PB M) :
    (giantSignedTraceRowMass (giantSignedGhostTraceRow ν A C D) f s : ℂ) =
      giantSignedStateGhostApply PS ν (fun g => (‖A g‖ : ℂ))
        (fun g => (‖C g‖ : ℂ)) (fun g => (‖D g‖ : ℂ)) (fun x => (f x : ℂ)) s := by
  change (((∑' r : GiantSignedGhostMemoryMoves s.2.2,
    ‖giantSignedGhostMemoryMoveCoefficient ν A C D s.2.2 r‖ *
      f (s.1, s.2.1, giantSignedGhostMemoryMoveTarget s.2.2 r)) : ℝ) : ℂ) = _
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro r
  rw [Complex.ofReal_mul, giantSignedGhostMemoryMoveCoefficient_norm ν hν]

variable [∀ p : ↥(markedPhysicalBandPrimes PS), NeZero p.val]

theorem giantSignedGhostTraceRow_absolute (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (A C D : B → ℂ) :
    GiantSignedTraceRowAbsolute (fun s : GiantSignedState PS PB M => ∑ g, s.2.2.1 g)
      (giantSignedGhostTraceRow ν A C D) := by
  intro f hf hfexp
  obtain ⟨Cf, u, hCf, hu, hexp⟩ := hfexp
  let w : GiantSignedState PS PB M → ℂ := fun s => (f s : ℂ)
  have hw (s : GiantSignedState PS PB M) : ‖w s‖ ≤ Cf * u ^ (∑ g, s.2.2.1 g) := by
    simpa only [w, Complex.norm_real, Real.norm_of_nonneg (hf s)] using hexp s
  refine ⟨?_, ?_⟩
  · intro s
    have hs := giantSignedGhostSimultaneous_summable_norm ν hν A C D
      (fun m => w (s.1,s.2.1,m)) Cf u hCf hu (fun m => hw (s.1,s.2.1,m)) s.2.2
    change Summable (fun r : GiantSignedGhostMemoryMoves s.2.2 =>
      ‖giantSignedGhostMemoryMoveCoefficient ν A C D s.2.2 r‖ *
        f (s.1,s.2.1,giantSignedGhostMemoryMoveTarget s.2.2 r))
    simpa only [norm_mul, w, Complex.norm_real, Real.norm_of_nonneg (hf _)] using hs
  · obtain ⟨Cf', u', hCf', hu', hg⟩ := giantSignedStateGhostApply_exponential PS ν hν
      (fun g => (‖A g‖ : ℂ)) (fun g => (‖C g‖ : ℂ)) (fun g => (‖D g‖ : ℂ))
      w Cf u hCf hu (fun s a m => hw (s,a,m))
    refine ⟨Cf', u', hCf', hu', ?_⟩
    intro s
    have hm : 0 ≤ giantSignedTraceRowMass (giantSignedGhostTraceRow ν A C D) f s :=
      tsum_nonneg (fun _ => mul_nonneg (norm_nonneg _) (hf _))
    calc
      _ = ‖(giantSignedTraceRowMass (giantSignedGhostTraceRow ν A C D) f s : ℂ)‖ :=
        ((Complex.norm_real _).trans (Real.norm_of_nonneg hm)).symm
      _ ≤ _ := by
        rw [giantSignedGhostTraceRow_mass_coe ν hν]
        exact hg s.1 s.2.1 s.2.2

theorem giantSignedVisitTraceRow_absolute (ν : ∀ g, PB g → ℝ) (hν : ∀ g p, 0 ≤ ν g p)
    (V : B → ℝ) (q ρ : ℝ) :
    GiantSignedTraceRowAbsolute (fun s : GiantSignedState PS PB M => ∑ g, s.2.2.1 g)
      (giantSignedVisitTraceRow ν V q ρ) :=
  giantSignedGhostTraceRow_absolute ν hν _ _ _

end
end ArtinMatthews
