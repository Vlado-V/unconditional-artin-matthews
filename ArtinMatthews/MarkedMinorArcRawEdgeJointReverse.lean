module

public import ArtinMatthews.MarkedMinorArcRawEdgeJointCoefficient
public import ArtinMatthews.MarkedMinorArcBanKernel
public import ArtinMatthews.MarkedMinorArcBanAdjoint
public import ArtinMatthews.MarkedMinorArcRawCleanSupport
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Reflection of the literal coupled edge coefficient.  Its absolute
reverse has the same physical cutoffs and is controlled by the ordinary
row with the reflected Schwartz cutoff. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def markedRawEdgeReflectedCutoff (ψ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)) ψ

@[simp] theorem markedRawEdgeReflectedCutoff_apply (ψ : SchwartzMap ℝ ℂ) (u : ℝ) :
    markedRawEdgeReflectedCutoff ψ u = ψ (-u) := rfl

theorem markedRawEdgeReflectedCutoff_bounds (ψ : SchwartzMap ℝ ℂ) {A W : ℝ}
    (hψ : ∀ u, ‖ψ u‖ ≤ W) (hsupp : ∀ u, ψ u ≠ 0 → |u| ≤ A) :
    (∀ u, ‖markedRawEdgeReflectedCutoff ψ u‖ ≤ W) ∧
      (∀ u, markedRawEdgeReflectedCutoff ψ u ≠ 0 → |u| ≤ A) := by
  constructor
  · intro u
    exact hψ (-u)
  · intro u hu
    simpa only [abs_neg] using hsupp (-u) hu

theorem markedBanEdgeKernel_norm_reflect (ψ : SchwartzMap ℝ ℂ)
    (Q Y : ℝ) (a b l : ℤ) :
    ‖markedBanEdgeKernel ψ Q Y a b l‖ =
      ‖markedBanEdgeKernel (markedRawEdgeReflectedCutoff ψ) Q Y b a (-l)‖ := by
  rw [← RCLike.norm_conj (markedBanEdgeKernel ψ Q Y a b l),
    ← markedBanEdgeKernel_adjoint ψ Q Y a b l]
  simp only [markedBanEdgeKernel, norm_mul, markedBanAdjointCutoff,
    RCLike.norm_conj, markedRawEdgeReflectedCutoff_apply]

/-- Factor the original endpoint kernel by its exact scalar minor detector. -/
theorem markedRawEdgeJointCoefficient_factor
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (s t : MarkedRawState P (pads+1) B Z) :
    markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t =
      let sourceLast := ((markedRawActiveSplit pads) s.2.1).2
      let targetLast := ((markedRawActiveSplit pads) t.2.1).2
      let D := markedRawCopiedProduct ((markedRawActiveSplit pads) s.2.1).1
      if d₀ ≤ (D : ℝ) ∧ (D : ℝ) < 2*d₀ then
        if (D : ℤ) ∣ markedMinorIntegerDet s.1.1 t.1.1 then
          if MarkedRawFullCrossBan s.2.1 targetLast then 0 else
            (((d₀/(D : ℝ) : ℝ) : ℂ) * markedRawEndpointFactor hZ ρ χ s *
              η ((markedRawLastProduct sourceLast : ℝ)/Y) *
              η ((markedRawLastProduct targetLast : ℝ)/Y) *
              markedRawEndpointFactor hZ ρ χ t) *
            markedBanEdgeKernel ψ Q Y (markedRawLastProduct sourceLast : ℤ)
              (markedRawLastProduct targetLast : ℤ)
              (markedMinorIntegerDet s.1.1 t.1.1 / (D : ℤ))
        else 0 else 0 := by
  unfold markedRawEdgeJointCoefficient
  dsimp only
  split_ifs <;> try rfl
  rw [← markedBan_edge_minor_identity]
  ring

/-- Exact absolute reversal for any two actual endpoint memories with
the same copied slots.  The physical endpoint gates supply precisely the
distinctness needed to reverse the full cross-edge ban. -/
theorem markedRawEdgeJointCoefficient_norm_reverse
    {J : Type*} [Fintype J] [DecidableEq J]
    {P : J → Finset Nat.Primes} {pads B : ℕ} {Z : Finset (ℤ × ℤ)}
    (hdisj : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hZ : ∀ z ∈ Z, IsCoprime z.1 z.2) (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ)
    (d₀ Y Q ρ : ℝ) (χ : MarkedRawState P (pads+1) B Z → ℂ)
    (copied : MarkedRawActive P pads) (x y : Z)
    (a b : (j : J) → ↥(P j)) (m n : MarkedRawMemory P B) :
    ‖markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ
      (x, ((markedRawActiveSplit pads).symm (copied,a),m))
      (y, ((markedRawActiveSplit pads).symm (copied,b),n))‖ =
      ‖markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ
        (y, ((markedRawActiveSplit pads).symm (copied,b),n))
        (x, ((markedRawActiveSplit pads).symm (copied,a),m))‖ := by
  classical
  let s : MarkedRawState P (pads+1) B Z :=
    (x, ((markedRawActiveSplit pads).symm (copied,a),m))
  let t : MarkedRawState P (pads+1) B Z :=
    (y, ((markedRawActiveSplit pads).symm (copied,b),n))
  change ‖markedRawEdgeJointCoefficient hZ ψ η d₀ Y Q ρ χ s t‖ =
    ‖markedRawEdgeJointCoefficient hZ (markedRawEdgeReflectedCutoff ψ) η d₀ Y Q ρ χ t s‖
  rw [markedRawEdgeJointCoefficient_factor, markedRawEdgeJointCoefficient_factor]
  have hs := Equiv.apply_symm_apply (markedRawActiveSplit (P := P) pads) (copied,a)
  have ht := Equiv.apply_symm_apply (markedRawActiveSplit (P := P) pads) (copied,b)
  dsimp only [s,t]
  rw [hs,ht]
  dsimp only
  have hdet : markedMinorIntegerDet y.1 x.1 = -markedMinorIntegerDet x.1 y.1 := by
    unfold markedMinorIntegerDet
    ring
  rw [hdet]
  simp only [dvd_neg]
  by_cases hsrc : markedRawEndpointFactor hZ ρ χ s = 0
  · split_ifs <;> simp only [s] at hsrc ⊢ <;> simp [hsrc]
  by_cases htgt : markedRawEndpointFactor hZ ρ χ t = 0
  · split_ifs <;> simp only [t] at htgt ⊢ <;> simp [htgt]
  have hban : MarkedRawFullCrossBan ((markedRawActiveSplit pads).symm (copied,a)) b ↔
      MarkedRawFullCrossBan ((markedRawActiveSplit pads).symm (copied,b)) a :=
    markedRawFullCrossBan_symmetric hdisj copied a b
      (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ s hsrc)
      (markedRawEndpointFactor_ne_zero_distinct hZ ρ χ t htgt)
  simp only [hban]
  split_ifs with hdyad hdiv hbad <;> try rfl
  rw [Int.neg_ediv_of_dvd hdiv]
  simp only [norm_mul]
  rw [← markedBanEdgeKernel_norm_reflect]
  ring

end
end ArtinMatthews
