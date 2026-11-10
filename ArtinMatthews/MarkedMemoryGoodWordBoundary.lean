module

public import ArtinMatthews.MarkedMemoryGoodWordBudget
public import ArtinMatthews.MarkedMemoryGoodBoundary
public import ArtinMatthews.MarkedMinorArcDirtyScalar
public import ArtinMatthews.MarkedMinorArcDirtySecondGood
public import ArtinMatthews.MarkedMemoryGoodWordEnergy
public import ArtinMatthews.MarkedMinorArcRawGhostSymmetryBoundary
public import ArtinMatthews.MarkedRawBoundaryActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine tilted chronological boundary word has a logarithmic
saving for every positive length, uniformly in that length. The ghosts,
full store/promote edges, factorial memory measure and actual source
boundary are retained. No identification with a physical moment is made. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators

theorem markedMemoryGoodBoundary_chosen_rho_log_saving
    {J : Type*} [Fintype J] [decJ : DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10 : ℝ) ≤ e j) (hinj : Function.Injective e)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (hη : Function.support η ⊆ Set.Icc 1 4) (hηnorm : ∀ t, ‖η t‖ ≤ 1)
    (q G H c T A W : ℝ) (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c)
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hW : 0 ≤ W)
    (hdepth : 100*(5*G+36) < (Fintype.card J : ℝ))
    (hψnorm : ∀ t, ‖ψ t‖ ≤ W) (hsupp : Function.support ψ ⊆ Set.Icc (-A) A) :
    ∀ᶠ x : ℝ in atTop, ∀ (Z : Finset (ℤ × ℤ))
      (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (r d₀ Y : ℝ) (w : Z → ℤ × ℤ)
      (χ : ℕ → MarkedRawState (markedRawActualPrimeBand e x)
        (markedPadSlots x) (markedDirtyMemoryCutoff x) Z → ℂ)
      (qStage : ℕ → ℝ) (z₀ : Z),
      0 < d₀ → Real.exp ((Real.log x)^(1/10 : ℝ)) ≤ Y →
      Y ≤ Real.exp (H*(Real.log x)^(1/5 : ℝ)) →
      (∀ z, markedMinorIntegerDet z.1 (w z) = 1) →
      (∀ z ∈ Z, c ≤ |markedMinorIntegerTau r z| ∧ |markedMinorIntegerTau r z| ≤ T) →
      (∀ z v : Z, |markedMinorIntegerTau r v.1/markedMinorIntegerTau r z.1| ≤ 16) →
      (∀ j s, ‖χ j s‖ ≤ 1) →
      (∀ j z a, MarkedRawMemorySymmetric (fun m => χ j (z,(a,m)))) →
      (∀ j, 0 ≤ qStage j ∧ qStage j ≤ Real.sqrt q) →
      ∀ n j : ℕ, 0 < n →
      ‖markedMemoryBoundaryPairing (markedRawActualPrimeAtom e q x)
        (fun i => bandReciprocalMass (markedLogPowerBand (e i) x)) hZ ψ η d₀ Y
        ((Real.log x)^(G+9)) (markedMemoryChosenRho q) qStage
        (fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)) n j z₀‖ ≤
        ((Real.log x)^(-G))^n := by
  classical
  cases Subsingleton.elim decJ (Classical.decEq J)
  let ρ := markedMemoryChosenRho q
  obtain ⟨hρ, hρ₁, hgap⟩ := markedMemoryChosenRho_bounds hq₀ hq₁
  let C := Real.exp ((Fintype.card J : ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ))
  have hC : 1 ≤ C := by
    apply Real.one_le_exp_iff.mpr
    have hp := markedRawGhostSchurParameter_ge_one q ρ
    positivity
  have hdepth' : 100*(5*(G+2)+26) < (Fintype.card J : ℝ) := by nlinarith
  have henergy := markedMemoryGoodChronological_actual_energy e he hinj ψ η hη hηnorm
    q ρ (G+2) H c T A W hq₀ hq₁.le hρ hρ₁ hgap (by linarith) hH hc hT hA hW
    hdepth' hψnorm hsupp
  have hexp : G+2+7 = G+9 := by ring
  simp only [hexp] at henergy
  filter_upwards [henergy, markedRawBoundary_actual_energy_le_two e he,
    markedRawActualStateMass_nonneg_eventually e he, markedMemory_word_constant_budget hC G,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
    with x hx hboundary hmass hbudget hlog
  intro Z hZ r d₀ Y w χ qStage z₀ hd₀ hYlo hYhi hw hτ hbox hχ hχsym hstage n j hn
  let ν := markedRawActualPrimeAtom e q x
  let V := fun i => bandReciprocalMass (markedLogPowerBand (e i) x)
  let χg := fun i => markedRawDirtyGoodCutoff e x r d₀ Y w (χ i)
  let b : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x)
      (markedDirtyMemoryCutoff x) Z → ℂ := markedRawBoundary z₀
  let F := markedMemoryChronologicalApply ν V hZ ψ η d₀ Y ((Real.log x)^(G+9)) ρ
    qStage χg n j b
  let E := markedRawBoundaryEnergy ν (markedPadSlots x) (markedDirtyMemoryCutoff x) z₀
  let k := C^(n+1)*((Real.log x)^(-(G+2)))^n
  have hμ : ∀ s : MarkedRawState (markedRawActualPrimeBand e x) (markedPadSlots x)
      (markedDirtyMemoryCutoff x) Z, 0 ≤ markedRawStateMass ν s :=
    hmass q hq₀ hq₁.le _ _ Z
  have hE₀ : 0 ≤ E := Finset.sum_nonneg (fun s _ => mul_nonneg (hμ s) (sq_nonneg _))
  have hE : E ≤ 2 := hboundary q hq₀ hq₁.le _ Z z₀
  have hk : 0 ≤ k := by dsimp only [k]; positivity
  have hF : (∑ s, markedRawStateMass ν s*‖F s‖^2) ≤ k^2*E :=
    hx Z hZ r d₀ Y w χ qStage b hd₀ hYlo hYhi hw hτ hbox hχ hχsym hstage
      (markedRawBoundary_symmetric z₀) n j
  have hpair := markedWeightedBoundary_cauchy (markedRawStateMass ν) hμ b F
  have hpair' : ‖∑ s, (markedRawStateMass ν s : ℂ)*star (b s)*F s‖^2 ≤ (2*k)^2 := by
    calc
      _ ≤ E*(∑ s, markedRawStateMass ν s*‖F s‖^2) := hpair
      _ ≤ E*(k^2*E) := mul_le_mul_of_nonneg_left hF hE₀
      _ = k^2*E^2 := by ring
      _ ≤ k^2*2^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hE₀ hE 2) (sq_nonneg k)
      _ = _ := by ring
  have hnrm := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hk)).mp hpair'
  calc
    _ ≤ 2*k := hnrm
    _ = 2*C^(n+1)*((Real.log x)^(-(G+2)))^n := by dsimp only [k]; ring
    _ ≤ _ := hbudget n hn

end ArtinMatthews
