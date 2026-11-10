module

public import ArtinMatthews.MarkedPhysicalTypeIIDyadSum
public import ArtinMatthews.MarkedPhysicalTypeIIDyadSaving
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

/-! The actual harmonic-padded delta-minus-major source difference has
logarithmic saving. All literal primitive, box, support, and cross-ban
flags remain in both finite source terms. -/
namespace ArtinMatthews
open Filter
noncomputable section

theorem markedPhysicalTypeIIHarmonicDifference_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K B W C P : ℝ) (hK : 0 ≤ K) (hB : 8 ≤ B) (hW : 0 ≤ W) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*C+9)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      let bands := fun j => markedLogPowerBand (e j) x
      let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
      let Q := (Real.log x)^(P+2*C+18)
      let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
      let α := markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα
      let βf := markedPhysicalRestrictedBeta Sβ β
      ‖markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeDeltaDetector ψ Y) α βf-
        markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeMajorDetector ψ Q Y) α βf‖ ≤
        (Y*(Hm*Hn))*(Real.log x)^(-P) := by
  filter_upwards [markedPhysicalTypeIIDyadSum_actual_log_saving e he heUpper hinj hδ ψ η K B W C P
    hK hB hW hC hP hdepth hηsupport hη hψ hψsupport] with x hx
  intro Y Hm Hn hY hYhi hHm hHn Sα Sβ modulation β hSα hβ
  dsimp only
  have h := hx Y Hm Hn hY hYhi hHm hHn Sα Sβ modulation β hSα hβ
  have hEq := markedPhysicalTypeIIDyadSum_eq_harmonic e x ψ η Y ((Real.log x)^(P+2*C+18)) Hm Hn
    Sα Sβ modulation β
  exact (congrArg (fun z : ℂ => ‖z‖) hEq).symm.le.trans h

theorem markedPhysicalTypeIICharacterHarmonicDifference_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (Mχ : ℕ) (ξ : DirichletCharacter ℂ Mχ) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K B W C P : ℝ) (hK : 0 ≤ K) (hB : 8 ≤ B) (hW : 0 ≤ W) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*C+9)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (Y Hm Hn : ℝ),
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      x^δ ≤ Hm → x^δ ≤ Hn →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      let bands := fun j => markedLogPowerBand (e j) x
      let pads := ⌊(Real.log x)^(1/100:ℝ)⌋₊
      let Q := (Real.log x)^(P+2*C+18)
      let Z := markedPhysicalTypeIIDyadBox Y Hm Hn
      let α := fun (n : ℕ) => ξ n*markedMajorRestrictedCoefficient (Real.exp ((Real.log x)^(6/25:ℝ))) modulation Sα n
      let βf := fun (n : ℕ) => ξ n*markedPhysicalRestrictedBeta Sβ β n
      ‖markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeDeltaDetector ψ Y) α βf-
        markedPhysicalHarmonicPaddedDetectorSum bands pads Z η Y (markedRawEdgeMajorDetector ψ Q Y) α βf‖ ≤
        (Y*(Hm*Hn))*(Real.log x)^(-P) := by
  filter_upwards [markedPhysicalTypeIICharacterDyadSum_actual_log_saving e he heUpper hinj Mχ ξ hδ ψ η K B W C P
    hK hB hW hC hP hdepth hηsupport hη hψ hψsupport] with x hx
  intro Y Hm Hn hY hYhi hHm hHn Sα Sβ modulation β hSα hβ
  dsimp only
  have h := hx Y Hm Hn hY hYhi hHm hHn Sα Sβ modulation β hSα hβ
  have hEq := markedPhysicalTypeIICharacterDyadSum_eq_harmonic e x Mχ ξ ψ η Y ((Real.log x)^(P+2*C+18)) Hm Hn
    Sα Sβ modulation β
  exact (congrArg (fun z : ℂ => ‖z‖) hEq).symm.le.trans h

end
end ArtinMatthews
