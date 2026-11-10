module

public import ArtinMatthews.SourceKPIntegralGroup
public import ArtinMatthews.SourceFiniteKPTameUnits
public import Mathlib.NumberTheory.NumberField.FiniteAdeleRing
public import ArtinMatthews.SixthKummerSharpModulus
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

/-! Actual finite-adelic rank-two matrices are integral at cofinally
many finite places. The determinant unit condition follows from the
genuine unit group of the finite adele ring. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup AllowedGenerators
open scoped NumberField MatrixGroups AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K]

def sourceKPAdeleEval (P : HeightOneSpectrum (𝓞 K)) : 𝔸ᶠ[K] →+* P.adicCompletion K where
  toFun a := a P
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def sourceKPAdeleMatrixAt (P : HeightOneSpectrum (𝓞 K)) :
    GL (Fin 2) 𝔸ᶠ[K] →* GL (Fin 2) (P.adicCompletion K) :=
  GeneralLinearGroup.map (sourceKPAdeleEval K P)

theorem sourceKPAdeleMatrixAt_apply (P : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) 𝔸ᶠ[K])
    (i j : Fin 2) : sourceKPAdeleMatrixAt K P g i j = g i j P := rfl

theorem sourceKPAdeleMatrixAt_det (P : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) 𝔸ᶠ[K]) :
    (GeneralLinearGroup.det (sourceKPAdeleMatrixAt K P g) : P.adicCompletion K) =
      (GeneralLinearGroup.det g : 𝔸ᶠ[K]) P := by
  unfold sourceKPAdeleMatrixAt
  rw [GeneralLinearGroup.map_det, Units.coe_map]
  rfl

theorem sourceKPAdeleMatrixAt_eventually_integral (g : GL (Fin 2) 𝔸ᶠ[K]) :
    ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      SourceKPIntegralMatrix (sourceKPFiniteVal K P) (sourceKPAdeleMatrixAt K P g) := by
  have he : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      ∀ i j : Fin 2, sourceKPFiniteVal K P (g i j P) ≤ 1 := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    filter_upwards [FiniteAdeleRing.cofinite_mem_adicCompletionIntegers (g i j)] with P hP
    exact (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K P).mp hP
  have hd : ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      sourceKPFiniteVal K P ((GeneralLinearGroup.det g : 𝔸ᶠ[K]) P) = 1 :=
    (FiniteAdeleRing.isUnit_iff.mp (GeneralLinearGroup.det g).isUnit).2
  filter_upwards [he, hd] with P hP hD
  refine ⟨?_, ?_⟩
  · intro i j
    rw [sourceKPAdeleMatrixAt_apply]
    exact hP i j
  · rw [sourceKPAdeleMatrixAt_det]
    exact hD

theorem sourceKPAdele_eventually_tame :
    ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite, (6 : 𝓞 K) ∉ P.asIdeal := by
  rw [Filter.eventually_cofinite]
  apply (sixthWildPrimes K).finite_toSet.subset
  intro P hP
  change ¬ (6 : 𝓞 K) ∉ P.asIdeal at hP
  exact (mem_sixthWildPrimes P).mpr (Classical.not_not.mp hP)

def sourceKPRationalDiagonal : GL (Fin 2) K →* GL (Fin 2) 𝔸ᶠ[K] :=
  GeneralLinearGroup.map (algebraMap K 𝔸ᶠ[K])

theorem sourceKPAdeleMatrixAt_rational (P : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) K) :
    sourceKPAdeleMatrixAt K P (sourceKPRationalDiagonal K g) =
      GeneralLinearGroup.map (algebraMap K (P.adicCompletion K)) g := by
  exact (GeneralLinearGroup.map_comp_apply (algebraMap K 𝔸ᶠ[K]) (sourceKPAdeleEval K P) g).symm

theorem sourceKPRational_eventually_unit (x : K) (hx : x ≠ 0) :
    ∀ᶠ P : HeightOneSpectrum (𝓞 K) in Filter.cofinite,
      sourceKPFiniteVal K P (algebraMap K (P.adicCompletion K) x) = 1 := by
  let u := FiniteAdeleRing.unitEmbedding (𝓞 K) K (Units.mk0 x hx)
  exact (FiniteAdeleRing.isUnit_iff.mp u.isUnit).2

end
end ArtinMatthews
