module

public import ArtinMatthews.MarkedMemoryTiltRescale
public import ArtinMatthews.MarkedMemoryEndpointSum
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

/-! Exact signed normalized endpoint expansion with the actual tilted
source. The original physical constant normalization is exposed as a
factor, while the uniform-line/baseline atoms stay inside the genuine
source and finite endpoint sum. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  (V : J → ℝ)

theorem markedMemoryPhysicalPathNormalization (M n : ℕ) :
    (((∏ j,(V j)⁻¹:ℝ):ℂ)^(M+n))=
      (markedPhysicalMass V M:ℂ)*(((∏ j,(V j)⁻¹:ℝ):ℂ)^n) := by
  rw [pow_add]
  congr 1
  simp only [markedPhysicalMass,Complex.ofReal_prod,Complex.ofReal_pow,Finset.prod_pow]

variable (hV : ∀ j,V j≠0) {pads B n : ℕ} {Z : Finset (ℤ × ℤ)}
  (hZ : ∀ z∈Z,IsCoprime z.1 z.2) (z₀ : Z) (a : MarkedRawActive P (pads+1))
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q q : ℝ)
  (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

local notation "ν" => markedMemoryTiltAtoms (P := P) V q n
local notation "atom" => markedMemoryLineAtoms (P := P) q n
local notation "s" => markedMemoryBoundarySource (B := B) z₀ a
local notation "K" => markedMemoryActualLabelBound (J := J) (pads := pads) (B := B) (n := n)

include hV in
theorem markedMemoryTiltBoundary_endpoint_sum
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (markedRawStateMass ν s:ℂ)*
      (∑ H : MarkedMemoryChronologicalHistory hZ n s,
        if keep H then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q 1
          (markedMemoryHistoryVisitSchedule q n) χ n 0 H*f (markedMemoryChronologicalTarget hZ H) else 0)=
      (markedPhysicalMass V (pads+1):ℂ)*(((∏ j,(V j)⁻¹:ℝ):ℂ)^n)*
        (markedRawStateMass atom s:ℂ)*
        (∑ N : J → Fin (K+1),
          ∑ e : MarkedMemoryEndpointFamily (A := fun j => Fin (N j:ℕ)) (n := n) hZ s,
            (markedMemoryEndpointPrimeScalar hZ s e atom (fun _ => 1) q:ℂ)*
              markedMemoryEndpointSlotMass (J := J) (pads := pads) (n := n)*
              markedMemoryDecorationAverage e.1 (markedMemoryEndpointKernel hZ s ψ η d₀ Y Q χ keep f e)/
                (markedMemoryLabelFactorial (fun j => (N j:ℕ)):ℂ)) := by
  rw [markedMemoryTiltBoundary_guarded_rescale V hV q n hZ z₀ a ψ η d₀ Y Q 1
    (markedMemoryHistoryVisitSchedule q n) χ n 0 keep f]
  rw [markedMemoryEndpoint_signed_sum hZ s (by intro j; rfl) atom (fun _ => 1)
    ψ η d₀ Y Q q χ keep f]
  rw [markedMemoryPhysicalPathNormalization V (pads+1) n]

end
end ArtinMatthews
