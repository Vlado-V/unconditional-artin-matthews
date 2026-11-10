module

public import ArtinMatthews.SourceKPCuspTraceFunctional
public import ArtinMatthews.SourceKPCuspPoincare
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

/-! Cartesian cusp derivatives reconstructed from the genuine scaled-lattice derivatives. -/
namespace ArtinMatthews
open NumberField Module Module.Free MeasureTheory Topology
open scoped NumberField Classical BigOperators
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) [IsTotallyComplex K]
local notation "E" => mixedEmbedding.mixedSpace K
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "Q" => SourceKPCuspPrincipalQuotient K d
local instance sourceKPCuspCartesianQuotientMeasurable : MeasurableSpace Q := borel Q
local instance sourceKPCuspCartesianQuotientBorel : BorelSpace Q := ⟨rfl⟩

def sourceKPCuspCartesianDerivativeC (g : I → C(Q, ℂ)) (v : InfinitePlace K) (k : Fin 2) : C(Q, ℂ) :=
  ∑ i, ((sourceKPCuspCoordinates K d hd (sourceKPCuspHorizontalDirection K v k)) i : ℂ) • g i

theorem sourceKPCuspCartesianDerivativeC_hasDerivAt
    (f : C(Q, ℂ)) (g : I → C(Q, ℂ))
    (hfg : SourceKPCuspDirectionalDerivative K d hd f g)
    (hF : Differentiable ℝ (fun x : E => f (sourceKPCuspArchQuotientMap K d x)))
    (v : InfinitePlace K) (k : Fin 2) (x : E) (t : ℝ) :
    HasDerivAt (fun u : ℝ => f (sourceKPCuspArchQuotientMap K d
      (x + u • sourceKPCuspHorizontalDirection K v k)))
      (sourceKPCuspCartesianDerivativeC K d hd g v k
        (sourceKPCuspArchQuotientMap K d (x + t • sourceKPCuspHorizontalDirection K v k))) t := by
  let F : E → ℂ := fun x => f (sourceKPCuspArchQuotientMap K d x)
  let e := sourceKPCuspHorizontalDirection K v k
  let p := x + t • e
  have hb (i : I) : fderiv ℝ F p (sourceKPCuspLatticeBasis K d hd i) =
      g i (sourceKPCuspArchQuotientMap K d p) := by
    have h1 := (hF (p + (0 : ℝ) • sourceKPCuspLatticeBasis K d hd i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (((hasDerivAt_id (0 : ℝ)).smul_const (sourceKPCuspLatticeBasis K d hd i)).const_add p)
    have h2 := hfg i p 0
    simpa only [Function.comp_def, zero_smul, add_zero, one_smul, F] using h1.unique h2
  have hD : fderiv ℝ F p e = sourceKPCuspCartesianDerivativeC K d hd g v k
      (sourceKPCuspArchQuotientMap K d p) := by
    conv_lhs => rw [← (sourceKPCuspLatticeBasis K d hd).sum_repr e]
    simp only [map_sum, map_smul, hb]
    simp only [sourceKPCuspCartesianDerivativeC, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    change (sourceKPCuspCoordinates K d hd e i) • g i (sourceKPCuspArchQuotientMap K d p) = _
    simp [Algebra.smul_def, e]
  have h := (hF p).hasFDerivAt.comp_hasDerivAt t (((hasDerivAt_id t).smul_const e).const_add x)
  have h' : HasDerivAt (fun u : ℝ => F (x + u • e)) (fderiv ℝ F p e) t := by
    simpa only [Function.comp_def, id_eq, one_smul, F] using h
  exact h'.congr_deriv hD

end
end ArtinMatthews
