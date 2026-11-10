module

public import ArtinMatthews.MarkedPhysicalCoprimeScalarDetector
public import ArtinMatthews.MarkedPhysicalHarmonicScalar
public import ArtinMatthews.MarkedEstimateActualModel
public import ArtinMatthews.MarkedEstimateMertensBands
public import ArtinMatthews.MarkedPhysicalPadCollisionBudget
public import ArtinMatthews.MarkedPhysicalPadScalarError
public import ArtinMatthews.MarkedPhysicalScalarAbsActual
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The actual copied-pad error saves every fixed logarithmic power for
both detector branches, on the original scalar coefficient support. -/
namespace ArtinMatthews
noncomputable section
open Filter

theorem markedPhysicalPadScalarErrors_actual_log_saving {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (δ K Cα Cβ Qexp R W G : ℝ)
    (hδ : 0 < δ) (hK : 0 < K) (hQexp : 0 ≤ Qexp) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (η : ℝ → ℂ) (ψ : SchwartzMap ℝ ℂ) (hη : ∀ u,‖η u‖ ≤ 1) (hψ : ∀ u,‖ψ u‖ ≤ W)
    (hηs : Function.support η ⊆ Set.Icc 1 4) (hψs : Function.support ψ ⊆ Set.Icc (-R) R) :
    ∀ᶠ x : ℝ in atTop,∀ Y : ℝ,0 < Y →
      ∀ (S T : Finset ℕ) (Z : ℕ),x^δ ≤ (Z:ℝ) → (Z:ℝ) ≤ K*x →
      (∀ v ∈ S.product T,v.1*v.2 ∈ Finset.Icc 1 Z) →
      ∀ α β : ℕ → ℂ,(∀ m∈S,‖α m‖ ≤ (Real.log x)^Cα) → (∀ n∈T,‖β n‖ ≤ (Real.log x)^Cβ) →
      let P := fun j => markedLogPowerBand (e j) x
      let M := ⌊(Real.log x)^(1/100:ℝ)⌋₊
      let Δ := markedRawEdgeDeltaDetector ψ Y
      let H := markedRawEdgeMajorDetector ψ ((Real.log x)^Qexp) Y
      ‖markedPhysicalCoprimeScalarDetectorSum P S T η Y Δ α β-
        markedPhysicalPadSurvivalScalarSum P M S T η Y Δ α β‖ ≤ Y*(Z:ℝ)*(Real.log x)^(-G) ∧
      ‖markedPhysicalCoprimeScalarDetectorSum P S T η Y H α β-
        markedPhysicalPadSurvivalScalarSum P M S T η Y H α β‖ ≤ Y*(Z:ℝ)*(Real.log x)^(-G) := by
  let E := markedPhysicalScalarAbsLogExponent Cα Cβ Qexp
  let A := G+E+1
  obtain ⟨C,hC,hbound⟩ := markedPhysicalScalarAbsMass_actual_log_bound e he heUpper
    δ K Cα Cβ Qexp R W hδ hK hQexp hR hW η ψ hη hψ hηs hψs
  have hbands := eventually_all.mpr (fun j => marked_log_power_band_mass_eventually
    ((by norm_num : (0:ℝ)<1/10).trans_le (he j)))
  filter_upwards [hbound, markedPhysicalActualPadCollision_log_saving e he A,
    hbands,marked_array_disjoint_eventually e hinj,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 C))]
    with x hb hc hmass hdis hx
  intro Y hY S T Z hZl hZu hRZ α β hα hβ
  dsimp only
  let L := Real.log x
  let P := fun j => markedLogPowerBand (e j) x
  let M := ⌊L^(1/100:ℝ)⌋₊
  have hL : 0 < L := zero_lt_one.trans_le ((le_max_left _ _).trans hx)
  have hCL : C ≤ L := (le_max_right _ _).trans hx
  have hV (j : J) : 0 < bandReciprocalMass (P j) :=
    (show 0 < Real.log 2/2 by positivity).trans_le (hmass j).1.le
  have hP (j : J) (p : ℕ) (hp : p ∈ P j) : p.Prime := (mem_markedLogPowerBand.mp hp).1
  have hpow : L^(-A)*L^E*L=L^(-G) := by
    calc
      _ = L^(-A)*L^E*L^(1:ℝ) := by rw [Real.rpow_one]
      _ = L^(-A+E+1) := by rw [← Real.rpow_add hL,← Real.rpow_add hL]
      _ = _ := by congr 1; dsimp only [A]; ring
  have ha := hb Y hY S T Z hZl hZu hRZ α β hα hβ
  have hbound' (det : ℤ → ℤ → ℤ → ℂ)
      (hdet : markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y det α β ≤ C*(Y*(Z:ℝ))*L^E) :
      ‖markedPhysicalCoprimeScalarDetectorSum P S T η Y det α β-
        markedPhysicalPadSurvivalScalarSum P M S T η Y det α β‖ ≤ Y*(Z:ℝ)*L^(-G) := by
    calc
      _ ≤ L^(-A)*markedPhysicalCoprimeScalarDetectorAbsMass P S T η Y det α β :=
        markedPhysicalCoprimeScalarDetector_sub_survival_norm_le P hP hdis M S T η Y det α β
          hV (L^(-A)) (Real.rpow_nonneg hL.le _) hc
      _ ≤ L^(-A)*(C*(Y*(Z:ℝ))*L^E) :=
        mul_le_mul_of_nonneg_left hdet (Real.rpow_nonneg hL.le _)
      _ ≤ L^(-A)*(L*(Y*(Z:ℝ))*L^E) := by gcongr
      _ = Y*(Z:ℝ)*(L^(-A)*L^E*L) := by ring
      _ = _ := by rw [hpow]
  exact ⟨hbound' _ ha.1,hbound' _ ha.2⟩

end
end ArtinMatthews
