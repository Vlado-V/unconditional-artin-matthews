module

public import ArtinMatthews.MarkedMajorArcDivisorAssembly
public import ArtinMatthews.MarkedMajorArcPartialSummation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! Literal dyadic, logarithmically weighted divisor polynomials with their
actual normalization. -/
namespace ArtinMatthews
open Finset

 theorem marked_divisor_log_normalized_uniform (B : ℝ) (hB : 1/2 ≤ B) :
    ∃ A δ U₀ : ℝ, 0 < A ∧ 0 < δ ∧ δ ≤ 1/2 ∧ 0 < U₀ ∧
      ∀ {ι : Type*} (J : Finset ι) (d : ι → ℕ) (c : ι → ℂ)
        (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t H S u v : ℝ),
        0 < H → U₀ ≤ S →
        (∀ i ∈ J, 0 < d i ∧ S ≤ H/d i ∧ |t/(2*Real.pi)| ≤ (H/d i)^B) →
        1 ≤ |t/(2*Real.pi)| → H ≤ u → u ≤ v → v ≤ 2*H → 1 ≤ Real.log u →
        ‖(H:ℂ)⁻¹*∑ n ∈ Ioc ⌊u⌋₊ ⌊v⌋₊,
          ((Real.log n)⁻¹:ℝ)*(markedMajorDivisorPolynomial J d c n *
            (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)))‖ ≤
        3*(q:ℝ)*A*(∑ i ∈ J, ‖c i‖/(d i:ℝ))*
          (1/Real.sqrt |t/(2*Real.pi)|+S^(-δ)) := by
  classical
  obtain ⟨A,δ,U₀,hA,hδ,hhalf,hU₀,hbound⟩ := marked_divisor_polynomial_phase_uniform B hB
  refine ⟨A,δ,U₀,hA,hδ,hhalf,hU₀,?_⟩
  intro ι J d c q _ χ t H S u v hH hUS hi ht hHu huv hvH hlog
  have hu : 0 < u := hH.trans_le hHu
  have hS : 0 < S := hU₀.trans_le hUS
  let mass : ℝ := ∑ i ∈ J, ‖c i‖/(d i:ℝ)
  let e : ℝ := 1/Real.sqrt |t/(2*Real.pi)|+S^(-δ)
  have hmass : 0 ≤ mass := sum_nonneg (fun i _ => by positivity)
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hD : 0 ≤ (q:ℝ)*A*H*mass*e := by positivity
  have hp (w : ℝ) (hw : w ∈ Set.Icc u v) :
      ‖∑ n ∈ Ioc ⌊u⌋₊ ⌊w⌋₊, markedMajorDivisorPolynomial J d c n *
        (χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I))‖ ≤ (q:ℝ)*A*H*mass*e := by
    apply hbound J d c q χ t H S ⌊u⌋₊ ⌊w⌋₊ hH hUS hi ht
    · exact hHu.trans (Nat.lt_floor_add_one u).le
    · exact (Nat.floor_le (hu.le.trans hw.1)).trans (hw.2.trans hvH)
  have hb := marked_log_weight_interval_bound
    (fun n => markedMajorDivisorPolynomial J d c n*(χ (n:ZMod q)*(n:ℂ)^((t:ℂ)*Complex.I)))
    hu hlog huv (hvH.trans (by linarith)) hD hp
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hH]
  calc
    _ ≤ H⁻¹*(3*((q:ℝ)*A*H*mass*e)) := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hH.le)
    _ = _ := by dsimp [mass,e]; field_simp

end ArtinMatthews
