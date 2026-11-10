module

public import ArtinMatthews.SourceEisensteinNonconstant
public import ArtinMatthews.SourceHyperbolicProductMeasure
public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceKPAdelicRationalProductChart
public import ArtinMatthews.SourceArchIntertwinerProduct
public import ArtinMatthews.SourceHyperbolicH1Measure
public import ArtinMatthews.SourceHyperbolicProductSlices
public import ArtinMatthews.SourceKPAdelicProductWeakEquation
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

/-! The actual incoming and outgoing terms in the full product chart have the
same tested eigenvalue as the initial-region Eisenstein series. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix MeasureTheory OAI.CubicEisenstein
open SourceArchJacquet SourceHyperbolicGreen
open scoped NumberField MatrixGroups AdeleRing ContDiff Topology BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
local notation "P" => ProductSpace (InfinitePlace K)
local notation "U" => productUpper (InfinitePlace K)
local notation "ν" => productVolume (InfinitePlace K)

def sourceKPAdelicOutgoingProductChart (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (p : P) : ℂ :=
  if hp : ∀ v, 0 < p v 2 then sourceKPAdelicTraceIntertwiner K hζ s
    (q * (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) else 0

theorem sourceKPAdelicOutgoingProductChart_eq_section {s : ℂ} (hs : 0 < s.re)
    (q : SourceKPAdelicProjective K hζ) :
    sourceKPAdelicOutgoingProductChart K hζ s q = fun p =>
      (((Real.pi : ℂ)/s)^Fintype.card (InfinitePlace K)*sourceKPFiniteIntertwiner K hζ s q.2) *
        sourceKPAdelicProductSection K hζ (-s) (q.1,1) p := by
  funext p
  by_cases hp : ∀ v, 0 < p v 2
  · rw [sourceKPAdelicOutgoingProductChart,dite_eq_left hp,
      sourceKPAdelicProductSection,dite_eq_left hp]
    let a := q.1 * ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp)
    have he : q * (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1) =
        (a,q.2) := Prod.ext rfl (mul_one _)
    have he' : ((q.1,1) : SourceKPAdelicProjective K hζ) *
        (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1) = (a,1) :=
      Prod.ext rfl (one_mul _)
    rw [he,he',sourceKPAdelicTraceIntertwiner_arch_formula K hζ hs,
      sourceArchCompactScalar_factor]
    have hOne : sourceKPAdelicCompactScalar K hζ (-s) (1,1) = 1 :=
      sourceKPAdelicCompactScalar_one K hζ (-s)
    simp only [hOne,mul_one]
    ring
  · simp only [sourceKPAdelicOutgoingProductChart,dite_eq_right hp,sourceKPAdelicProductSection,mul_zero]

theorem sourceKPAdelicOutgoingProductChart_contDiffAt {s : ℂ} (hs : 0 < s.re)
    (q : SourceKPAdelicProjective K hζ) (p : P) (hp : p ∈ U) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (sourceKPAdelicOutgoingProductChart K hζ s q) p := by
  rw [sourceKPAdelicOutgoingProductChart_eq_section K hζ hs q]
  exact contDiffAt_const.mul (sourceKPAdelicProductSection_contDiffAt K hζ (-s) (q.1,1) p
    (fun v => productUpper_pos hp v))

theorem sourceKPAdelicProductSection_test_eigen (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) {φ : P → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ U) :
    (∫ p, star (sourceArchProductCoordinateLaplacian φ p)*sourceKPAdelicProductSection K hζ s q p ∂ν) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
        ∫ p, star (φ p)*sourceKPAdelicProductSection K hζ s q p ∂ν := by
  have h := sourceKPAdelicRationalProductChart_test_eigen K hζ s q
    (sourceKPRationalBorelCosetMk K 1) hφ hc hsupp
  rw [sourceKPAdelicRationalProductChart_mk,map_one,one_mul] at h
  calc
    _ = ∫ p, star (productLaplacian φ p)*sourceKPAdelicProductSection K hζ s q p ∂ν := by
      apply integral_congr_ae
      filter_upwards [productVolume_ae_upper (ι := InfinitePlace K)] with p hp
      rw [productLaplacian_eq_native (fun _ _ => hφ.contDiffAt) hp]
    _ = _ := h

theorem sourceKPAdelicOutgoingProductChart_test_eigen {s : ℂ} (hs : 0 < s.re)
    (q : SourceKPAdelicProjective K hζ) {φ : P → ℂ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hsupp : tsupport φ ⊆ U) :
    (∫ p, star (sourceArchProductCoordinateLaplacian φ p)*sourceKPAdelicOutgoingProductChart K hζ s q p ∂ν) =
      (InfinitePlace.nrComplexPlaces K : ℂ)*(1-4*s^2) *
        ∫ p, star (φ p)*sourceKPAdelicOutgoingProductChart K hζ s q p ∂ν := by
  let C := ((Real.pi : ℂ)/s)^Fintype.card (InfinitePlace K)*sourceKPFiniteIntertwiner K hζ s q.2
  have hI (ψ : P → ℂ) :
      (∫ p, ψ p*sourceKPAdelicOutgoingProductChart K hζ s q p ∂ν) =
        C*∫ p, ψ p*sourceKPAdelicProductSection K hζ (-s) (q.1,1) p ∂ν := by
    rw [sourceKPAdelicOutgoingProductChart_eq_section K hζ hs q, ← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun p => by dsimp only [C]; ring)
  rw [hI (fun p => star (sourceArchProductCoordinateLaplacian φ p)),
    hI (fun p => star (φ p)),sourceKPAdelicProductSection_test_eigen K hζ (-s) (q.1,1) hφ hc hsupp]
  ring

def sourceKPAdelicNonconstantProductChart (s : ℂ) (q : SourceKPAdelicProjective K hζ)
    (p : P) : ℂ :=
  sourceKPAdelicEisensteinProductChart K hζ s q p -
    (sourceKPAdelicProductSection K hζ s q p + sourceKPAdelicOutgoingProductChart K hζ s q p)

theorem sourceKPAdelicNonconstantProductChart_apply_of_positive (s : ℂ)
    (q : SourceKPAdelicProjective K hζ) (p : P) (hp : ∀ v, 0 < p v 2) :
    sourceKPAdelicNonconstantProductChart K hζ s q p =
      sourceKPAdelicNonconstantEisenstein K hζ s
        (q * (ProjGenLinGroup.mk (sourceArchUpperHalfspaceMatrix K hζ p hp),1)) := by
  simp only [sourceKPAdelicNonconstantProductChart,sourceKPAdelicEisensteinProductChart,
    sourceKPAdelicProductSection,sourceKPAdelicOutgoingProductChart,
    sourceKPAdelicNonconstantEisenstein,dite_eq_left hp]

end
end ArtinMatthews
