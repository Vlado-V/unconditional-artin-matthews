module

public import ArtinMatthews.MarkedPhysicalCharacterGoodRemoval
public import ArtinMatthews.MarkedPhysicalTypeIIGoodRemoval
public import ArtinMatthews.MarkedPhysicalCappedGlobalActual
public import ArtinMatthews.MarkedPhysicalCharacterCriterion
public import ArtinMatthews.MarkedPhysicalTypeIICriterion
public import ArtinMatthews.MarkedPhysicalTypeIIEndpointDamping
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

/-! The original unprojected physical Type II estimate, with its actual
capped term now bounded. A strict-gap damping is used inside the proof;
the physical detector pairing itself is returned at damping one. -/
namespace ArtinMatthews
open Filter
open scoped Classical
noncomputable section

theorem markedPhysicalTypeIIPairing_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B W C P : ℝ) (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*C+7)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0 < d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (U V : ℝ),x^δ ≤ U → x^δ ≤ V →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      ‖markedPhysicalTypeIIPairing e x ψ η d₀ Y ((Real.log x)^(P+2*C+16)) 1 U V
        Sα Sβ modulation β‖ ≤ (U*V)*(Real.log x)^(-P) := by
  let G := P+2*C+7
  let Qexp := P+2*C+16
  have hG : 0 < G := by dsimp [G]; positivity
  have hQ : 0 ≤ Qexp := by dsimp [Qexp]; positivity
  have hEq : G+9=Qexp := by dsimp [G,Qexp]; ring
  filter_upwards [markedPhysicalCoordinateCappedGlobal_log_saving e he hinj ψ η hηsupport hη
      (1/2) G B K W (by norm_num) (by norm_num) hG (by linarith) hK hW hdepth hψ hψsupport,
    markedPhysicalTypeIIPairing_of_capped_bound e he heUpper hinj hδ ψ η K Hexp B 1 W Qexp C P
      hK hHexp hB (by norm_num) hW hQ hC hP hη hψ hψsupport] with x hcap hpair
  intro d₀ Y hd₀ hY hYhi hscale U V hU hV Sα Sβ modulation β hSα hβ
  let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hR : 1 ≤ R := markedPhysicalMomentTubeRadius_ge_one _ hK
    (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY))
  have hb := hcap d₀ Y hd₀ hY hYhi R hR U V
  rw [hEq] at hb
  have hp := hpair d₀ Y hd₀ hY hYhi hscale (1/2) U V (by norm_num) (by norm_num) hU hV
    hb Sα Sβ modulation β hSα hβ
  exact (congrArg (fun z : ℂ => ‖z‖)
    (markedPhysicalTypeIIPairing_eq_q_one e x ψ η d₀ Y ((Real.log x)^Qexp) (1/2) U V
      Sα Sβ modulation β)).symm.le.trans hp

theorem markedPhysicalTypeIICharacterPairing_actual_log_saving
    {J : Type*} [Fintype J] [DecidableEq J]
    (e : J → ℝ) (he : ∀ j,(1/10:ℝ) ≤ e j) (heUpper : ∀ j,e j ≤ (1/5:ℝ))
    (hinj : Function.Injective e) (Mχ : ℕ) (ξ : DirichletCharacter ℂ Mχ) {δ : ℝ} (hδ : 0 < δ)
    (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (K Hexp B W C P : ℝ) (hK : 0 ≤ K) (hHexp : 0 ≤ Hexp) (hB : 8 ≤ B)
    (hW : 0 ≤ W) (hC : 0 ≤ C) (hP : 0 ≤ P)
    (hdepth : 100*(5*(P+2*C+7)+36)<(Fintype.card J:ℝ))
    (hηsupport : Function.support η ⊆ Set.Icc 1 4) (hη : ∀ t,‖η t‖ ≤ 1)
    (hψ : ∀ t,‖ψ t‖ ≤ W) (hψsupport : Function.support ψ ⊆ Set.Icc (-K) K) :
    ∀ᶠ x : ℝ in atTop,∀ (d₀ Y : ℝ),0 < d₀ →
      Real.exp ((Real.log x)^(1/10:ℝ)) ≤ Y → Y ≤ Real.exp (B*(Real.log x)^(1/5:ℝ)) →
      d₀*Y ≤ Real.exp (Hexp*(Real.log x)^(21/100:ℝ)) →
      ∀ (U V : ℝ),x^δ ≤ U → x^δ ≤ V →
      ∀ (Sα Sβ : Finset ℕ) (modulation : ℝ) (β : ℕ → ℂ),
      (∀ n∈Sα,x^δ ≤ (n:ℝ)) → (∀ n∈Sβ,‖β n‖ ≤ (Real.log x)^C) →
      ‖markedPhysicalTypeIICharacterPairing e x Mχ ξ ψ η d₀ Y ((Real.log x)^(P+2*C+16)) 1 U V
        Sα Sβ modulation β‖ ≤ (U*V)*(Real.log x)^(-P) := by
  let G := P+2*C+7
  let Qexp := P+2*C+16
  have hG : 0 < G := by dsimp [G]; positivity
  have hQ : 0 ≤ Qexp := by dsimp [Qexp]; positivity
  have hEq : G+9=Qexp := by dsimp [G,Qexp]; ring
  filter_upwards [markedPhysicalCoordinateCappedGlobal_log_saving e he hinj ψ η hηsupport hη
      (1/2) G B K W (by norm_num) (by norm_num) hG (by linarith) hK hW hdepth hψ hψsupport,
    markedPhysicalTypeIICharacterPairing_of_capped_bound e he heUpper hinj Mχ ξ hδ ψ η K Hexp B 1 W Qexp C P
      hK hHexp hB (by norm_num) hW hQ hC hP hη hψ hψsupport] with x hcap hpair
  intro d₀ Y hd₀ hY hYhi hscale U V hU hV Sα Sβ modulation β hSα hβ
  let R := markedPhysicalMomentTubeRadius (markedMemoryMomentLength x) K (d₀*Y)
  have hR : 1 ≤ R := markedPhysicalMomentTubeRadius_ge_one _ hK
    (mul_nonneg hd₀.le ((Real.exp_pos _).le.trans hY))
  have hb := hcap d₀ Y hd₀ hY hYhi R hR U V
  rw [hEq] at hb
  have hp := hpair d₀ Y hd₀ hY hYhi hscale (1/2) U V (by norm_num) (by norm_num) hU hV
    hb Sα Sβ modulation β hSα hβ
  exact (congrArg (fun z : ℂ => ‖z‖)
    (markedPhysicalTypeIICharacterPairing_eq_q_one e x Mχ ξ ψ η d₀ Y ((Real.log x)^Qexp) (1/2) U V
      Sα Sβ modulation β)).symm.le.trans hp

end
end ArtinMatthews
