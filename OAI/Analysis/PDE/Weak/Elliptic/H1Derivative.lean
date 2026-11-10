module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.Analysis.PDE.Weak.Elliptic.Derivative
public import OAI.Analysis.PDE.Weak.Boundary.H1Translation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
public import OAI.Analysis.PDE.Weak.Elliptic.H1Subspace
public import OAI.Analysis.PDE.Weak.Elliptic.SubspaceCompactness


set_option backward.privateInPublic true
@[expose] public section

noncomputable section
open Set _root_.MeasureTheory Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

/-- Difference quotients bounded in the actual H¹ graph have a derivative
which remains in the same zero-boundary graph closure. Both components are
identified by integration against compactly supported test functions. -/
theorem exists_H1_derivative_of_difference_bounds
    (p : H1Pair m) (hp0 : Integrable (p.1 : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ))
    (hp1 : Integrable (p.2 : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m))
    (v : OAI.Analysis.PDE.Variational.CellCoordinates m) {Ω : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} {s : ℕ → ℝ}
    (hs : Tendsto s atTop (𝓝 0)) (hs0 : ∀ n, s n ≠ 0)
    (hadm : ∀ n, differenceH1Pair v (s n) p ∈ H1Zero Ω)
    {C0 C1 : ℝ}
    (h0 : ∀ n, ‖differenceQuotientL2 volume v (s n) p.1‖ ≤ C0)
    (h1 : ∀ n, ‖differenceQuotientL2 volume v (s n) p.2‖ ≤ C1) :
    ∃ q : H1Pair m, q ∈ H1Zero Ω ∧
      HasWeakDirectionalDerivative volume v p.1 q.1 ∧
      HasWeakDirectionalDerivative volume v p.2 q.2 := by
  let : CompleteSpace (OAI.Analysis.PDE.Variational.CellVectors m) := FiniteDimensional.complete ℝ _
  let e : H1Hilbert m ≃L[ℝ] H1Pair m := h1HilbertEquiv
  let u : ℕ → H1Hilbert m := fun n ↦ e.symm (differenceH1Pair v (s n) p)
  have hu (n : ℕ) : u n ∈ h1ZeroHilbertSubmodule Ω := by
    change e (e.symm (differenceH1Pair v (s n) p)) ∈ h1ZeroSubmodule Ω
    rw [e.apply_symm_apply]
    exact hadm n
  have hb (n : ℕ) : ‖u n‖ ≤ ‖e.symm.toContinuousLinearMap‖ * max C0 C1 := by
    refine (e.symm.toContinuousLinearMap.le_opNorm _).trans ?_
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    change max ‖differenceQuotientL2 volume v (s n) p.1‖
      ‖differenceQuotientL2 volume v (s n) p.2‖ ≤ max C0 C1
    exact max_le_max (h0 n) (h1 n)
  obtain ⟨g, hg, -, hlimit⟩ := exists_weak_limit_in_submodule
    (h1ZeroHilbertSubmodule Ω) (isClosed_h1ZeroHilbertSubmodule Ω) u hu hb
  refine ⟨e g, hg, ?_, ?_⟩
  · apply hasWeakDerivative_of_difference_limits volume p.1 (e g).1 hp0 v hs hs0
    intro w l hl
    let φ : H1Hilbert m →L[ℝ] ℝ := (innerSL ℝ w).comp
      ((ContinuousLinearMap.fst ℝ _ _).comp e.toContinuousLinearMap)
    have hφ (n : ℕ) : φ (u n) = inner ℝ (differenceQuotientL2 volume v (s n) p.1) w := by
      change inner ℝ w (e (e.symm (differenceH1Pair v (s n) p))).1 = _
      rw [e.apply_symm_apply]
      exact real_inner_comm _ _
    have he := hlimit φ l (by simpa only [hφ] using hl)
    change inner ℝ w (e g).1 = l at he
    simpa only [real_inner_comm] using he
  · apply hasWeakDerivative_of_difference_limits volume p.2 (e g).2 hp1 v hs hs0
    intro w l hl
    let φ : H1Hilbert m →L[ℝ] ℝ := (innerSL ℝ w).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp e.toContinuousLinearMap)
    have hφ (n : ℕ) : φ (u n) = inner ℝ (differenceQuotientL2 volume v (s n) p.2) w := by
      change inner ℝ w (e (e.symm (differenceH1Pair v (s n) p))).2 = _
      rw [e.apply_symm_apply]
      exact real_inner_comm _ _
    have he := hlimit φ l (by simpa only [hφ] using hl)
    change inner ℝ w (e g).2 = l at he
    simpa only [real_inner_comm] using he

end OAI.Analysis.PDE.Weak
