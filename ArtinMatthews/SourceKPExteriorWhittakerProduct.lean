module

public import ArtinMatthews.SourceKPExteriorWhittakerPhase
public import ArtinMatthews.SourceKPExteriorWhittakerAllowed
public import ArtinMatthews.SourceKPExteriorWhittakerCoefficient
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

/-! The full exterior product has genuine finite support. Its value
is the literal global gamma2 coefficient with both norm factors. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain AllowedGenerators VaryingKummerAnalytic StandardAdelic QuadraticWeil
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)

theorem sourceKPTameExteriorWhittaker_hasFiniteMulSupport (e : SourcePrimeExponents K S₀) :
    Function.HasFiniteMulSupport (fun P : SourceExteriorPrime K S₀ =>
      sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (sourcePrimeExponentUnit K hζ S₀ e)) := by
  apply e.support.finite_toSet.subset
  intro P hP
  by_contra h
  exact hP (sourceKPTameExteriorWhittakerDiagonal_exponent_zero K hζ S₀ P hS e
    (Finsupp.notMem_support_iff.mp h))

theorem sourceKPTameExteriorWhittaker_hasProd
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀) :
    HasProd (fun P : SourceExteriorPrime K S₀ =>
      sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n)))
      (reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ))) := by
  let T := c.val.support ∪ n.support
  have hc : c.val.support ⊆ T := Finset.subset_union_left
  have hn : n.support ⊆ T := Finset.subset_union_right
  rw [← sourceKPTameExteriorWhittakerProduct_squarefree_cube K hζ S₀ hS c n T hc hn]
  apply hasProd_prod_of_ne_finset_one
  intro P hP
  apply sourceKPTameExteriorWhittakerDiagonal_exponent_zero K hζ S₀ P hS
  have hc0 : c.val P = 0 := Finsupp.notMem_support_iff.mp (fun h => hP (hc h))
  have hn0 : n P = 0 := Finsupp.notMem_support_iff.mp (fun h => hP (hn h))
  simp only [Finsupp.add_apply, Finsupp.smul_apply, hc0, hn0, smul_zero, add_zero]

theorem sourceKPTameExteriorWhittaker_tprod
    (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀) :
    (∏' P : SourceExteriorPrime K S₀,
      sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n))) =
      reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ)) :=
  (sourceKPTameExteriorWhittaker_hasProd K hζ S₀ hS c n).tprod_eq

theorem sourceKPTameExteriorWhittaker_allowed_hasProd
    (a : Kˣ) (c : ReflectionSquarefreeExponents K S₀) (n : SourcePrimeExponents K S₀)
    (ha : a ∈ allowedSubgroup K hζ S₀)
    (hI : _root_.toPrincipalIdeal (sourceRing K S₀) K a =
      _root_.toPrincipalIdeal (sourceRing K S₀) K (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n))) :
    HasProd (fun P : SourceExteriorPrime K S₀ => sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS a)
      (reflectionGammaTwo K hζ S₀ c.val /
        ((Real.sqrt (sourcePrimeExponentNorm K S₀ c.val : ℝ) : ℂ) * (sourcePrimeExponentNorm K S₀ n : ℂ))) := by
  have he : (fun P : SourceExteriorPrime K S₀ => sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS a) =
      (fun P : SourceExteriorPrime K S₀ => sourceKPTameExteriorWhittakerDiagonal K hζ S₀ P hS
        (sourcePrimeExponentUnit K hζ S₀ (c.val + 3 • n))) := by
    funext P
    exact sourceKPTameExteriorWhittakerDiagonal_same_ideal K hζ S₀ hS P a _ ha
      (sourcePrimeExponentUnit_allowed K hζ S₀ _) hI
  rw [he]
  exact sourceKPTameExteriorWhittaker_hasProd K hζ S₀ hS c n

end
end ArtinMatthews
