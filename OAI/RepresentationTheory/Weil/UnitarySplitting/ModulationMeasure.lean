module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.UnitarySplitting.UltraMultiplier
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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
public import Mathlib.RingTheory.PiTensorProduct
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
public import OAI.RepresentationTheory.Weil.UnitarySplitting.CharacterMeasure


set_option backward.privateInPublic true
@[expose] public section

/-! # Modulation Measure -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.ModulationMeasure.Construction

noncomputable section

/-! Nontrivial local-field modulations determine finite measures. -/

open _root_.MeasureTheory BoundedContinuousFunction
open scoped BigOperators

variable {F : Type} [NormedField F] {d : ℕ}
variable (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x))
variable (hunit : ∀ t, ‖ψ t‖ = 1)

def boundedModulation (p : Local.FunctionsMetaplectic.Construction.Position F d) : Local.FunctionsMetaplectic.Construction.Position F d →ᵇ ℂ where
  toFun := UltraMultiplier.Construction.modulationCharacter ψ p
  continuous_toFun := hψ.comp (by unfold Local.FunctionsMetaplectic.Construction.dot; fun_prop)
  map_bounded' := by
    refine ⟨2, fun x y => ?_⟩
    calc
      dist _ _ ≤ ‖UltraMultiplier.Construction.modulationCharacter ψ p x‖ + ‖UltraMultiplier.Construction.modulationCharacter ψ p y‖ :=
        dist_le_norm_add_norm _ _
      _ = 2 := by rw [UltraMultiplier.Construction.modulationCharacter, UltraMultiplier.Construction.modulationCharacter, hunit, hunit]; norm_num

theorem boundedModulation_zero : boundedModulation ψ hψ hunit (0 : Local.FunctionsMetaplectic.Construction.Position F d) = 1 := by
  ext x
  change ψ (Local.FunctionsMetaplectic.Construction.dot 0 x) = 1
  simp [Local.FunctionsMetaplectic.Construction.dot]

theorem boundedModulation_add (p q : Local.FunctionsMetaplectic.Construction.Position F d) :
    boundedModulation ψ hψ hunit (p + q) =
      boundedModulation ψ hψ hunit p * boundedModulation ψ hψ hunit q := by
  ext x
  change ψ (Local.FunctionsMetaplectic.Construction.dot (p + q) x) = ψ (Local.FunctionsMetaplectic.Construction.dot p x) * ψ (Local.FunctionsMetaplectic.Construction.dot q x)
  simp [Local.FunctionsMetaplectic.Construction.dot, add_mul, Finset.sum_add_distrib, ψ.map_add_eq_mul]

theorem boundedModulation_neg (p : Local.FunctionsMetaplectic.Construction.Position F d) :
    boundedModulation ψ hψ hunit (-p) = star (boundedModulation ψ hψ hunit p) := by
  ext x
  change ψ (Local.FunctionsMetaplectic.Construction.dot (-p) x) = star (ψ (Local.FunctionsMetaplectic.Construction.dot p x))
  have hp : Local.FunctionsMetaplectic.Construction.dot (-p) x = -Local.FunctionsMetaplectic.Construction.dot p x := by simp [Local.FunctionsMetaplectic.Construction.dot]
  rw [hp, ψ.map_neg_eq_inv]
  exact Complex.inv_eq_conj (hunit _)

include hψ hunit in
theorem measures_eq_of_modulation_integrals
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    (hnontrivial : ∃ t, ψ t ≠ 1)
    (μ ν : Measure (Local.FunctionsMetaplectic.Construction.Position F d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ p : Local.FunctionsMetaplectic.Construction.Position F d,
      ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x ∂μ = ∫ x, UltraMultiplier.Construction.modulationCharacter ψ p x ∂ν) : μ = ν := by
  exact CharacterMeasure.measures_eq_of_character_integrals
    (boundedModulation ψ hψ hunit) (boundedModulation_zero ψ hψ hunit)
    (boundedModulation_add ψ hψ hunit) (boundedModulation_neg ψ hψ hunit)
    (UltraMultiplier.Construction.modulationCharacter_separates ψ hnontrivial hunit) μ ν h

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.ModulationMeasure.Construction
