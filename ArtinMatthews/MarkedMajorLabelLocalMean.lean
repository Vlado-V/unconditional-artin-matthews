module

public import ArtinMatthews.MarkedMajorLabelMean
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! Exact conversion of the actual translated endpoint mean to intervals of length HU. -/
namespace ArtinMatthews
open Finset Filter MeasureTheory
open scoped Topology

theorem markedMajor_local_integral_eq_translated (f : ℝ → ℝ) (z X : ℝ) (hX : 0 ≤ X) :
    (∫ t in Set.Icc z (z+X),f t) =
      ∫ t in Set.Icc (-(X/2)) (X/2),f (t+(z+X/2)) := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : z ≤ z+X),
    ← intervalIntegral.integral_of_le (by linarith : -(X/2) ≤ X/2),
    intervalIntegral.integral_comp_add_right]
  congr 1 <;> ring

theorem marked_major_label_local_mean (σ D B : ℝ) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (cutoff : ℝ → ℂ) (hcutoff : ∀ y,‖cutoff y‖ ≤ 1)
    (hsupp : Function.support cutoff ⊆ Set.Iic B) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ L : ℝ in atTop,∀ {J : Type} [Fintype J]
      (bands : J → Finset ℕ),
      (∀ j p,p ∈ bands j → p.Prime) →
      Pairwise (fun i j => Disjoint (bands i) (bands j)) →
      (∀ j,0 < bandReciprocalMass (bands j)) →
      ∀ (Y θ H u v U z : ℝ) (l r : ℕ) (β : ℕ → ℂ),
      0 < Y → 0 < H → 0 < U → 1 ≤ H*U → H*U ≤ Real.exp (σ*L) →
      H ≤ u → v ≤ 2*H → 1 ≤ Real.log u → U ≤ (l:ℝ) → (r:ℝ) ≤ 2*U →
      (∀ n ∈ Icc l r,‖β n‖ ≤ L^D) →
      ∀ (k q : ℕ) (χb : DirichletCharacter ℂ k) (χ : DirichletCharacter ℂ q) (modulation : ℝ),
      (∫ t in Set.Icc z (z+H*U),
        ‖markedMajorLabelEndpoint bands cutoff χb θ Y χ (Real.exp (L^(6/25:ℝ))) modulation H u v U l r β t‖^2) ≤
          (3*C/2)*L^(2*D+5) := by
  obtain ⟨C,hC,hmean⟩ := marked_major_label_translated_mean σ D B hσ hB cutoff hcutoff hsupp
  refine ⟨C,hC,?_⟩
  filter_upwards [hmean] with L hL
  intro J _ bands hbands hdis hV Y θ H u v U z l r β hY hH hU hX hXupper hHu hv hlog hl hr hβ
    k q χb χ modulation
  have h := hL bands hbands hdis hV Y θ H u v U (H*U/2) (z+H*U/2) l r β
    hY hH hU (by positivity) hX hXupper hHu hv hlog hl hr hβ k q χb χ modulation
  rw [markedMajor_local_integral_eq_translated _ z (H*U) (mul_pos hH hU).le]
  convert h using 1
  have hx : H*U ≠ 0 := (mul_pos hH hU).ne'
  field_simp
  ring

end ArtinMatthews
