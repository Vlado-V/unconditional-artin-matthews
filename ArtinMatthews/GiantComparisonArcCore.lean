module

public import ArtinMatthews.GiantComparisonCutoffRows
public import ArtinMatthews.GiantComparisonArcMellin
public import ArtinMatthews.GiantComparisonMellinTail
public import ArtinMatthews.GiantComparisonEndpointGlobalMoment
public import ArtinMatthews.SourceComparisonActualLowTime


set_option backward.privateInPublic true
@[expose] public section

/-! The normalized arc polynomial is the literal centered Mellin sum.
Both normalizations and both phase conventions are retained. -/
namespace ArtinMatthews

open Finset
open scoped BigOperators

noncomputable section
variable {I G : Type*} [Fintype I] [Fintype G]

theorem giantCandidateComparisonLeftEndpoint_eq_centeredEndpoint
    (e : I → ℝ) (ε x Y σ : ℝ) (ψ : ℝ → ℂ)
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    giantCandidateComparisonLeftEndpoint e ε x Y σ ψ P t q b n =
      sourceComparisonCenteredEndpoint e ε x Y σ ψ P t q b n := by
  unfold giantCandidateComparisonLeftEndpoint giantComparisonWeightedEndpoint
    sourceComparisonCenteredEndpoint
  rw [mul_comm Complex.I (σ : ℂ)]
  ring

theorem giantCandidateComparisonLeftEndpoint_mellinPhase
    (e : I → ℝ) (ε x Y v : ℝ) (ψ : ℝ → ℂ)
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) {n : ℕ} (hn : 0 < n) :
    giantCandidateComparisonLeftEndpoint e ε x Y 0 ψ P t q b n *
      primeExtractionMellinPhase (-v) (n : ℝ) =
      giantCandidateComparisonLeftEndpoint e ε x Y (-2 * Real.pi * v) ψ P t q b n := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hphase : primeExtractionMellinPhase (-v) (n : ℝ) =
      (n : ℂ) ^ (((-2 * Real.pi * v : ℝ) : ℂ) * Complex.I) := by
    rw [primeExtractionMellinPhase, Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log]
    push_cast
    ring_nf
  simp only [giantCandidateComparisonLeftEndpoint_eq_centeredEndpoint,
    sourceComparisonCenteredEndpoint, Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one]
  rw [hphase]
  ring

theorem giantComparisonArcPhase_eq_rational (r : ℚ) (n : ℕ) :
    OAI.Problem337.RealPhase.phase ((r : ℝ) * (n : ℝ)) =
      @sourceComparisonRationalPhase r.den ⟨r.den_ne_zero⟩ r.num (n : ZMod r.den) := by
  let _ : NeZero r.den := ⟨r.den_ne_zero⟩
  rw [sourceComparisonRationalPhase_nat, OAI.Problem337.RealPhase.phase, Rat.cast_def]
  congr 1
  push_cast
  ring

theorem giantComparisonArcCore_eq_centeredMellinSum
    (e : I → ℝ) (ε x σ τ : ℝ) (ψ : ℝ → ℂ)
    (P : G → Finset ℕ) (t : G → ℕ) (q : G → ℝ)
    (b : ((g : G) → Fin (t g) → ℕ) → ℂ) (r : ℚ)
    {Y lo hi B : ℝ} (hY : 0 < Y) (hB : hi ≤ B)
    (hψ : Function.support ψ ⊆ Set.Icc lo hi) :
    (Y : ℂ)⁻¹ * giantComparisonMellinPolynomial (giantComparisonCutoffRows Y lo hi)
      (giantComparisonArcTwist (r : ℝ) (giantCandidateComparisonLeftEndpoint e ε x Y σ ψ P t q b)) τ =
      @sourceComparisonCenteredMellinSum I G _ _ e ε x Y σ B ψ P t q b
        r.den ⟨r.den_ne_zero⟩ r.num τ := by
  let _ : NeZero r.den := ⟨r.den_ne_zero⟩
  rw [giantComparisonMellinPolynomial, sourceComparisonCenteredMellinSum, div_eq_mul_inv, mul_comm]
  congr 1
  refine (sum_congr rfl ?_).trans
    (sum_subset (giantComparisonCutoffRows_subset hY.le hB) ?_)
  · intro n _
    rw [giantComparisonArcTwist, giantCandidateComparisonLeftEndpoint_eq_centeredEndpoint,
      giantComparisonArcPhase_eq_rational, mul_comm Complex.I (τ : ℂ)]
  · intro n hn hnot
    have hψ₀ : ψ ((n : ℝ) / Y) = 0 := Function.notMem_support.mp fun h =>
      hnot ((mem_giantComparisonCutoffRows hY).mpr ⟨(mem_Ioc.mp hn).1, hψ h⟩)
    simp [sourceComparisonCenteredEndpoint, hψ₀]

end
end ArtinMatthews
