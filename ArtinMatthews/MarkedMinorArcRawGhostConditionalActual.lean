module

public import ArtinMatthews.MarkedMinorArcRawGhostConditional
public import ArtinMatthews.MarkedMinorArcRawGhostActualRow
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedMemoryBirthAtom
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

/-! The true tilted ghost row with a conditional ordered-birth gate.
The fixed-length tuple cost is retained, including dependencies between
earlier and later births. The remaining constant is independent of B. -/

noncomputable section
namespace ArtinMatthews
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem markedRawGhostConditional_actual_weighted_row_eventually
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j, (1/10:ℝ) ≤ e j) {q ρ : ℝ}
    (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hρ : 0 < ρ) (hgap : Real.sqrt q < ρ^2) :
    ∀ᶠ x : ℝ in atTop, ∀ qStage : ℝ, 0 ≤ qStage → qStage ≤ Real.sqrt q →
      ∀ (B : ℕ) (m : MarkedRawMemory (markedRawActualPrimeBand e x) B)
        (z : ℤ × ℤ) (hz : IsCoprime z.1 z.2)
        (D : ℝ) (_hD : 0 ≤ D)
        (gate : (del : MarkedRawGhostDeletion m) → (l : MarkedRawGhostBirthSizes m del) →
          MarkedRawGhostBirthLabels l → Prop),
      (∀ del l, (∑ births : MarkedRawGhostBirthLabels l,
        if gate del l births then markedRawGhostBirthMass (markedRawActualPrimeAtom e q x) l births else 0) ≤
          D*∏ j, (2:ℝ)^(l.1 j:ℕ)/(Nat.factorial (l.1 j:ℕ):ℝ)) →
      markedRawGhostConditionalWeightedAbsRow (markedRawActualPrimeAtom e q x)
        (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) qStage ρ
        (markedRawGhostSchurParameter q ρ) m z hz gate ≤
      D*Real.exp ((Fintype.card J:ℝ)*(2*markedRawGhostSchurParameter q ρ/ρ)) := by
  classical
  have hV := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    (show 0 < e j by linarith [he j]))
  filter_upwards [hV,markedMemoryBirthAtom_actual_eventually e he,
    markedRawGhost_actual_band_mass_eventually e he] with x hV hatom hmass
  intro qStage hqs₀ hqs B m z hz D hD gate hdraw
  let v₀ := markedRawGhostSchurParameter q ρ
  have hv₀ : 0 < v₀ := zero_lt_one.trans_le (markedRawGhostSchurParameter_ge_one q ρ)
  have hsqrt : Real.sqrt q ≤ 1 := by nlinarith [Real.sq_sqrt hq₀,Real.sqrt_nonneg q]
  have hqs₁ : qStage ≤ 1 := hqs.trans hsqrt
  have hVp (j : J) : 0 ≤ bandReciprocalMass (markedLogPowerBand (e j) x) :=
    ((by positivity : 0 < Real.log 2/2).trans (hV j).1).le
  have hν (j : J) (p : ↥(markedRawActualPrimeBand e x j)) :
      0 ≤ markedRawActualPrimeAtom e q x j p := (hatom q hq₀ hq₁ j p).1
  have hsurv : (∏ j, (qStage/ρ^2+(1-qStage)/(ρ*v₀))^
      (markedRawGroupHitIndices m j z hz).card) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro j _
      exact pow_nonneg (add_nonneg (div_nonneg hqs₀ (sq_nonneg _))
        (div_nonneg (sub_nonneg.mpr hqs₁) (mul_pos hρ hv₀).le)) _
    · intro j _
      exact pow_le_one₀ (add_nonneg (div_nonneg hqs₀ (sq_nonneg _))
        (div_nonneg (sub_nonneg.mpr hqs₁) (mul_pos hρ hv₀).le))
        (markedRawGhostSchurParameter_survival hρ hgap hqs₀ hqs)
  have hexp : (∏ j, Real.exp ((v₀*(1-qStage)*bandReciprocalMass (markedLogPowerBand (e j) x)/ρ)*2)) ≤
      Real.exp ((Fintype.card J:ℝ)*(2*v₀/ρ)) := by
    calc
      _ ≤ ∏ _j : J, Real.exp (2*v₀/ρ) := by
        apply Finset.prod_le_prod₀ (fun j _ => (Real.exp_pos _).le)
        intro j _
        apply Real.exp_le_exp.mpr
        have hc : v₀*(1-qStage)*bandReciprocalMass (markedLogPowerBand (e j) x) ≤ v₀ := by
          calc
            _ ≤ v₀*1*bandReciprocalMass (markedLogPowerBand (e j) x) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith : 1-qStage ≤ 1) hv₀.le) (hVp j)
            _ ≤ v₀*1*1 := mul_le_mul_of_nonneg_left (hV j).2.le (by positivity)
            _ = _ := by ring
        have hd := div_le_div_of_nonneg_right hc hρ.le
        exact (mul_le_mul_of_nonneg_right hd (by norm_num : (0:ℝ) ≤ 2)).trans_eq (by ring)
      _ = _ := by simp only [Finset.prod_const,Finset.card_univ,← Real.exp_nat_mul]
  have hr := markedRawGhost_conditional_weighted_row (markedRawActualPrimeAtom e q x) hν
    (fun j => bandReciprocalMass (markedLogPowerBand (e j) x)) hVp hqs₀ hqs₁ hρ hv₀
    hD (by norm_num : (0:ℝ) ≤ 2) m z hz gate hdraw
  apply hr.trans
  calc
    _ ≤ D*
        ∏ j, Real.exp ((v₀*(1-qStage)*bandReciprocalMass (markedLogPowerBand (e j) x)/ρ)*2) :=
      mul_le_of_le_one_right (mul_nonneg hD
        (Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le))) hsurv
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp hD

end ArtinMatthews
