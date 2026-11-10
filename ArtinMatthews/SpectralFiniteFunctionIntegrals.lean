module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
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

/-! Integral exchange for families having genuinely finite support as
functions.  This is stronger than pointwise finite support. -/

noncomputable section
open Set MeasureTheory Filter

namespace ArtinMatthews

theorem finiteFunctionSupport_eval {ι X : Type*} (F : ι → X → ℂ)
    (hF : Function.HasFiniteSupport F) (x : X) :
    Function.HasFiniteSupport (fun i => F i x) := by
  apply hF.subset
  intro i hi hzero
  exact hi (congrFun hzero x)

theorem finiteFunctionSupport_finsum_eq_sum {ι X : Type*} (F : ι → X → ℂ)
    (hF : Function.HasFiniteSupport F) (x : X) :
    (∑ᶠ i, F i x) = ∑ i ∈ hF.toFinset, F i x := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro i hi
  apply hF.mem_toFinset.mpr
  intro hzero
  exact hi (congrFun hzero x)

theorem finiteFunctionSupport_integrable {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ι → X → ℂ) (hF : Function.HasFiniteSupport F)
    (hI : ∀ i, Integrable (F i) μ) : Integrable (fun x => ∑ᶠ i, F i x) μ := by
  classical
  have he : (fun x => ∑ᶠ i, F i x) = fun x => ∑ i ∈ hF.toFinset, F i x :=
    funext (finiteFunctionSupport_finsum_eq_sum F hF)
  rw [he]
  exact integrable_finsetSum _ (fun i _ => hI i)

theorem finiteFunctionSupport_integral {ι X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : ι → X → ℂ) (hF : Function.HasFiniteSupport F)
    (hI : ∀ i, Integrable (F i) μ) :
    (∫ x, (∑ᶠ i, F i x) ∂μ) = ∑ᶠ i, ∫ x, F i x ∂μ := by
  classical
  have hs : Function.support (fun i => ∫ x, F i x ∂μ) ⊆ hF.toFinset := by
    intro i hi
    apply hF.mem_toFinset.mpr
    intro hzero
    apply hi
    change (∫ x, F i x ∂μ) = 0
    simp only [hzero,Pi.zero_apply,integral_zero]
  simp_rw [finiteFunctionSupport_finsum_eq_sum F hF]
  rw [integral_finsetSum _ (fun i _ => hI i), finsum_eq_sum_of_support_subset _ hs]

theorem finiteFunctionSupport_fibre {ι κ X : Type*} (F : ι × κ → X → ℂ)
    (hF : Function.HasFiniteSupport F) (i : ι) :
    Function.HasFiniteSupport (fun j => F (i,j)) :=
  Function.HasFiniteSupport.fun_comp_of_injective (f := F)
    (g := fun j => (i,j)) (fun _ _ h => congrArg Prod.snd h) hF

theorem finiteFunctionSupport_fibre_sum {ι κ X : Type*} (F : ι × κ → X → ℂ)
    (hF : Function.HasFiniteSupport F) :
    Function.HasFiniteSupport (fun i x => ∑ᶠ j, F (i,j) x) := by
  apply (hF.image Prod.fst).subset
  intro i hi
  by_contra hnot
  apply hi
  funext x
  have hz (j : κ) : F (i,j) = 0 := by
    by_contra hj
    exact hnot ⟨(i,j),hj,rfl⟩
  simp only [hz,Pi.zero_apply,finsum_zero]

end ArtinMatthews
