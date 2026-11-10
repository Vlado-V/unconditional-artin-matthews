module

public import ArtinMatthews.SourceKPAdelicExceptionalCharacter
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

/-! Exact finite and infinite components of the global exceptional
datum. The normalized idele norm on a single place is precisely its
local absolute value, with the infinite place multiplicity retained. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain
open scoped NumberField AdeleRing BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

theorem sourceKPIdeleAbsoluteNorm_ofAdicCompletion (P : HeightOneSpectrum (𝓞 K))
    (u : (P.adicCompletion K)ˣ) :
    sourceKPIdeleAbsoluteNorm K (IdeleGroup.ofAdicCompletion (𝓞 K) K P u) = ‖(u : P.adicCompletion K)‖ := by
  let x := IdeleGroup.ofAdicCompletion (𝓞 K) K P u
  have hi : ‖(1 : InfiniteAdeleRing K)‖ = 1 := by
    rw [InfiniteAdeleRing.norm_def]
    change (∏ w : InfinitePlace K, ‖(1 : w.Completion)‖ ^ w.mult) = 1
    simp
  change ‖(1 : InfiniteAdeleRing K)‖ * ‖(sourceKPIdeleFiniteUnit K x : 𝔸ᶠ[K])‖ = _
  rw [hi, one_mul, FiniteAdeleRing.norm_eq_finprod_of_unit]
  let f := fun Q : HeightOneSpectrum (𝓞 K) =>
    ‖Pi.mulSingle (M := fun R : HeightOneSpectrum (𝓞 K) => R.adicCompletion K) P (u : P.adicCompletion K) Q‖
  change (∏ᶠ Q, f Q) = _
  rw [finprod_eq_single f P (fun Q hQ => by dsimp only [f]; rw [Pi.mulSingle_eq_of_ne hQ, norm_one])]
  dsimp only [f]
  rw [Pi.mulSingle_eq_same]

theorem sourceKPIdeleAbsoluteNorm_ofCompletion (w : InfinitePlace K) (u : w.Completionˣ) :
    sourceKPIdeleAbsoluteNorm K (IdeleGroup.ofCompletion (𝓞 K) K w u) = ‖(u : w.Completion)‖ ^ w.mult := by
  let x := IdeleGroup.ofCompletion (𝓞 K) K w u
  have hf : ‖(1 : 𝔸ᶠ[K])‖ = 1 := by
    have h := FiniteAdeleRing.norm_eq_finprod_of_unit (1 : 𝔸ᶠ[K]ˣ)
    change ‖(1 : 𝔸ᶠ[K])‖ = ∏ᶠ P : HeightOneSpectrum (𝓞 K), ‖(1 : P.adicCompletion K)‖ at h
    rw [h]
    simp
  change ‖(sourceKPIdeleInfiniteUnit K x : InfiniteAdeleRing K)‖ * ‖(1 : 𝔸ᶠ[K])‖ = _
  rw [hf, mul_one, InfiniteAdeleRing.norm_def]
  let f := fun v : InfinitePlace K =>
    ‖Pi.mulSingle (M := fun t : InfinitePlace K => t.Completion) w (u : w.Completion) v‖ ^ v.mult
  change (∏ v : InfinitePlace K, f v) = _
  rw [Finset.prod_eq_single w]
  · dsimp only [f]
    rw [Pi.mulSingle_eq_same]
  · intro v _ hv
    dsimp only [f]
    rw [Pi.mulSingle_eq_of_ne hv, norm_one, one_pow]
  · intro h
    exact (h (Finset.mem_univ w)).elim

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

theorem sourceKPAdelicExceptionalCharacter_cube_ofAdicCompletion (P : HeightOneSpectrum (𝓞 K))
    (z : rootsOfUnity 3 K) (u : (P.adicCompletion K)ˣ) :
    ((sourceKPAdelicExceptionalCharacter K hζ
      (sourceKPAdelicCubeTorusEquiv K hζ (z, sourceKPIdeleCube K (IdeleGroup.ofAdicCompletion (𝓞 K) K P u))) : ℂˣ) : ℂ) =
      (sourceKPCentralComplex K hζ P (sourceKPRootsTransport K hζ P z) : ℂ) *
        ((‖(u : P.adicCompletion K)‖ ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [sourceKPAdelicExceptionalCharacter_cube, sourceKPIdeleAbsoluteNorm_ofAdicCompletion,
    sourceKPAdelicCentralComplex_transport]

theorem sourceKPAdelicExceptionalCharacter_cube_ofCompletion (w : InfinitePlace K)
    (z : rootsOfUnity 3 K) (u : w.Completionˣ) :
    ((sourceKPAdelicExceptionalCharacter K hζ
      (sourceKPAdelicCubeTorusEquiv K hζ (z, sourceKPIdeleCube K (IdeleGroup.ofCompletion (𝓞 K) K w u))) : ℂˣ) : ℂ) =
      (sourceKPAdelicCentralComplex K hζ z : ℂ) *
        (((‖(u : w.Completion)‖ ^ w.mult) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
  rw [sourceKPAdelicExceptionalCharacter_cube, sourceKPIdeleAbsoluteNorm_ofCompletion]

end
end ArtinMatthews
