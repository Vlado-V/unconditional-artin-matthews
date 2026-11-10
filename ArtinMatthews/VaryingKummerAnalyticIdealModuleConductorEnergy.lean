module

public import ArtinMatthews.VaryingKummerAnalyticIdealModuleFrequencyLabels
public import OAI.NumberTheory.DirichletL.FiniteFourier
public import ArtinMatthews.VaryingKummerAnalyticFiniteConductorEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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

/-! Primitive residue-character energy on an arbitrary fixed ideal, reduced
to its actual trace-frequency energy without a coprimality assumption. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable (I M : Ideal (𝓞 K)) (hI : I ≠ ⊥) [NeZero M]
local instance idealModuleConductorQuotient_finite : Finite ((𝓞 K) ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
local instance idealModuleConductorQuotient_fintype : Fintype ((𝓞 K) ⧸ M) := Fintype.ofFinite _

theorem idealModule_conductor_character_le_additive_energy {ι : Type*}
    (B : Finset ι) (n : ι → I) (a : ι → ℂ)
    (S : Finset (MulChar ((𝓞 K) ⧸ M) ℂ)) (hS : ∀ χ ∈ S, IsPrimitiveOnIdeals χ) :
    (∑ χ ∈ S, ‖∑ i ∈ B, a i * χ (idealResidueCoordinate I M hI (NeZero.ne M) (n i))‖^2) ≤
      ∑ u : ((𝓞 K) ⧸ M)ˣ, ‖∑ i ∈ B, a i *
        idealModuleTraceChar K I (idealModuleFrequencyValue K I M hI (NeZero.ne M) u) (n i)‖^2 := by
  have H := primitive_character_family_le_additive_energy B
    (fun i => idealResidueCoordinate I M hI (NeZero.ne M) (n i)) a S hS
    (idealTraceAddChar K M (NeZero.ne M)) (idealTraceAddChar_isPrimitive K M (NeZero.ne M))
  simpa only [idealModuleFrequencyValue_character,mul_comm] using H

end
end ArtinMatthews.VaryingKummerAnalytic
