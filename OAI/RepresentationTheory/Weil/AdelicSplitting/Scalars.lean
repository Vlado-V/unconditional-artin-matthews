module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.RepresentationTheory.Weil.AdelicSplitting.Vacuum
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

/-! # Scalars -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.Scalars.Construction

noncomputable section

/-! A restricted family of scalar oscillators is automatically trivial at
all but finitely many places: at finite places its integral components fix
the nonzero vacuum. Consequently its global value is its scalar product. -/

open Filter
open scoped Classical _root_.NumberField

variable (F : Type) [Field F] [NumberField F] (N : ℕ) (ψ : AddChar (ArchimedeanAdeles.Construction.Adeles F) ℂ)

theorem scalarAt_integral_eq_one
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (z : Circle)
    (hz : Vacuum.Construction.scalarAt F N ψ (.inr v) z ∈ Vacuum.Construction.coverIntegral F N ψ (.inr v)) : z = 1 := by
  let : MeasurableSpace (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionMeasurableSpace F (.inr v)
  let : BorelSpace (v.adicCompletion F) := ArchimedeanAdeles.Construction.completionBorelSpace F (.inr v)
  have h := hz.2
  change (Oscillator.Construction.localOperator _ _ _ (Vacuum.Construction.scalarAt F N ψ (.inr v) z) (Vacuum.Construction.finiteVacuum F N v)) =
    Vacuum.Construction.finiteVacuum F N v at h
  have he := congrArg (fun f : Local.FunctionsMetaplectic.Construction.schwartzBruhat (ArchimedeanAdeles.Construction.Completion F (.inr v)) N => f.val 0) h
  change (z : ℂ) * (Vacuum.Construction.finiteVacuum F N v).val 0 = (Vacuum.Construction.finiteVacuum F N v).val 0 at he
  rw [Vacuum.Construction.finiteVacuum_zero, mul_one] at he
  exact Subtype.ext he

theorem restricted_scalar_eventually_one (a : RestrictedLimits.Construction.RestrictedGroup (Vacuum.Construction.coverIntegral F N ψ))
    (z : ArchimedeanAdeles.Construction.Places F → Circle) (ha : ∀ v, a v = Vacuum.Construction.scalarAt F N ψ v (z v)) :
    ∀ᶠ v in cofinite, z v = 1 := by
  have hi : ∀ᶠ v : ArchimedeanAdeles.Construction.Places F in cofinite, v ∉ Set.range (Sum.inl :
      NumberField.InfinitePlace F → ArchimedeanAdeles.Construction.Places F) :=
    (Set.finite_range (Sum.inl : NumberField.InfinitePlace F → ArchimedeanAdeles.Construction.Places F)).compl_mem_cofinite
  filter_upwards [a.property, hi] with v hv hi
  cases v with
  | inl v => exact (hi ⟨v, rfl⟩).elim
  | inr v =>
      exact scalarAt_integral_eq_one F N ψ v (z (.inr v)) ((ha (.inr v)) ▸ hv)

theorem assemble_scalar_eq_one_of_hasProd (w : ArchimedeanAdeles.Construction.Places F)
    (a : RestrictedLimits.Construction.RestrictedGroup (Vacuum.Construction.coverIntegral F N ψ)) (z : ArchimedeanAdeles.Construction.Places F → Circle)
    (ha : ∀ v, a v = Vacuum.Construction.scalarAt F N ψ v (z v)) (hz : HasProd z 1) :
    CentralProduct.Construction.assembleCover (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) a = 1 := by
  have hs := (eventually_cofinite.mp (restricted_scalar_eventually_one F N ψ a z ha))
  exact CentralProduct.Construction.assemble_scalar_family_eq_one (Vacuum.Construction.coverIntegral F N ψ) (Vacuum.Construction.scalarAt F N ψ) w hs.toFinset z
    (fun v hv => by simpa using hs.mem_toFinset.not.mp hv) hz a ha

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.Scalars.Construction
