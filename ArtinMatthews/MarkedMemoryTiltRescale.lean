module

public import ArtinMatthews.MarkedMemorySourceTilt
public import ArtinMatthews.MarkedMemoryMeasureRescale
public import ArtinMatthews.MarkedMemorySourceBoundary
public import ArtinMatthews.MarkedMemoryBoundaryRescale
public import ArtinMatthews.MarkedMemoryTiltBasic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! At the actual tilted atom, the exact finite rescaling leaves one
uniform projective-line/baseline atom. No source nu atom is absorbed
into the chronological initial birth weight. -/
namespace ArtinMatthews
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset Nat.Primes}
  (V : J → ℝ) (hV : ∀ j,V j≠0) (q : ℝ) (N : ℕ)

abbrev markedMemoryTiltAtoms := fun j (p : P j) => markedMemoryPrimeAtom (V j) q N p.1
abbrev markedMemoryLineAtoms := fun j (p : P j) => markedMemoryLineBirthAtom q N p.1

include hV

omit [Fintype J] in
theorem markedMemoryScaledAtoms_tilt :
    markedMemoryScaledAtoms (markedMemoryTiltAtoms (P := P) V q N) V=
      markedMemoryLineAtoms (P := P) q N := by
  funext j p
  simpa only [markedMemoryScaledAtoms,markedMemoryTiltAtoms,markedMemoryLineAtoms,pow_zero,mul_one,one_mul,markedMemoryLineBirthAtom] using
    markedMemory_ghost_run_charge (hV j) q N (p.1:ℕ) 0

variable {pads B : ℕ} {Z : Finset (ℤ × ℤ)} (hZ : ∀ z∈Z,IsCoprime z.1 z.2)
  (z₀ : Z) (a : MarkedRawActive P (pads+1))
  (ψ : SchwartzMap ℝ ℂ) (η : ℝ → ℂ) (d₀ Y Q ρ : ℝ)
  (qStage : ℕ → ℝ) (χ : ℕ → MarkedRawState P (pads+1) B Z → ℂ)

local notation "ν" => markedMemoryTiltAtoms (P := P) V q N
local notation "atom" => markedMemoryLineAtoms (P := P) q N
local notation "s" => markedMemoryBoundarySource (B := B) z₀ a

theorem markedMemoryTiltBoundaryHistory_rescale (n k : ℕ)
    (H : MarkedMemoryChronologicalHistory hZ n s) :
    (markedRawStateMass ν s:ℂ)*markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^(pads+1+n))*(markedRawStateMass atom s:ℂ)*
        markedMemoryChronologicalWeight atom (fun _ => 1) hZ ψ η d₀ Y Q ρ qStage χ n k H := by
  rw [markedMemoryBoundaryHistory_rescale ν V hV hZ z₀ a ψ η d₀ Y Q ρ qStage χ n k H,
    markedMemoryScaledAtoms_tilt V hV q N]

theorem markedMemoryTiltBoundary_guarded_rescale (n k : ℕ)
    (keep : MarkedMemoryChronologicalHistory hZ n s → Prop)
    (f : MarkedRawState P (pads+1) B Z → ℂ) :
    (markedRawStateMass ν s:ℂ)*
      (∑ H : MarkedMemoryChronologicalHistory hZ n s,
        if keep H then markedMemoryChronologicalWeight ν V hZ ψ η d₀ Y Q ρ qStage χ n k H*
          f (markedMemoryChronologicalTarget hZ H) else 0)=
      (((∏ j,(V j)⁻¹:ℝ):ℂ)^(pads+1+n))*(markedRawStateMass atom s:ℂ)*
        (∑ H : MarkedMemoryChronologicalHistory hZ n s,
          if keep H then markedMemoryChronologicalWeight atom (fun _ => 1) hZ ψ η d₀ Y Q ρ qStage χ n k H*
            f (markedMemoryChronologicalTarget hZ H) else 0) := by
  rw [markedMemoryBoundaryHistory_guarded_rescale ν V hV hZ z₀ a ψ η d₀ Y Q ρ qStage χ n k keep f,
    markedMemoryScaledAtoms_tilt V hV q N]

end
end ArtinMatthews
