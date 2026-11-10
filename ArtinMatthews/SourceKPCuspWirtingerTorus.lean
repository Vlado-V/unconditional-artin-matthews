module

public import ArtinMatthews.SourceKPCuspWirtingerDirection
public import ArtinMatthews.SourceKPReflectionHorizontal
public import ArtinMatthews.UnitTorusSmoothCoordinate
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

/-! A height-weighted native horizontal derivative descends to the
same principal Fourier torus with the exact trace-frequency multiplier. -/
namespace ArtinMatthews
open NumberField Module.Free MeasureTheory UnitAddTorus
open SourceHyperbolicGreen OAI.CubicEisenstein
open scoped NumberField Topology Classical ContDiff BigOperators LineDeriv
noncomputable section

local instance sourceKPWirtingerCircleMeasure : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance sourceKPWirtingerCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private def torusCoefficient {ι : Type*} [Fintype ι] (n : ι → ℤ) :
    C(UnitAddTorus ι, ℂ) →ₗ[ℂ] ℂ where
  toFun f := mFourierCoeff f n
  map_add' f g := by
    simp only [mFourierCoeff,ContinuousMap.add_apply,smul_add]
    exact integral_add (μ := unitTorusHaar ι)
      (((mFourier (-n)).continuous.smul f.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
      (((mFourier (-n)).continuous.smul g.continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
  map_smul' z f := by
    change (∫ t, mFourier (-n) t • (z • f t)) = z • ∫ t, mFourier (-n) t • f t
    simp_rw [smul_comm (mFourier (-n) _) z]
    exact integral_smul z _

private theorem sum_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ℝ) :
    (∑ i, a i • (Pi.single i 1 : ι → ℝ)) = a := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply, mul_ite]

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
variable (d : 𝓞 K) (hd : d ≠ 0)
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "V" => InfinitePlace K
local notation "X" => ProductSpace V
local notation "E" => sourceKPCuspProductCoordinates K hζ d hd
local notation "P" => unitTorusUnitCellProjection I
local notation "Ω" => productUpper V
local notation "a" => sourceKPCuspRealHorizontalDir K hζ d hd

private theorem lift_partial (F : C(UnitAddTorus I, ℂ)) (U : X → ℂ)
    (y : V → ℝ) (hy : ∀ v, 0 < y v)
    (hU : ∀ p ∈ Ω, DifferentiableAt ℝ U p)
    (hF : Differentiable ℝ (fun x : I → ℝ => F (P x)))
    (he : ∀ x : I → ℝ, F (P x) = U (E (x,y)))
    (x : I → ℝ) (v : V) (k : Fin 2) :
    fderiv ℝ (fun z : I → ℝ => F (P z)) x (a v k) =
      productPartial U v k.castSucc (E (x,y)) := by
  have hp : E (x,y) ∈ Ω := fun w _ => hy w
  have h₁ : HasDerivAt (fun t : ℝ => F (P (x + t • a v k)))
      (fderiv ℝ (fun z : I → ℝ => F (P z)) x (a v k)) 0 :=
    (hF x).hasFDerivAt.hasLineDerivAt (a v k)
  have h₂ : HasDerivAt (fun t : ℝ => U (E (x,y) + t • productDirection v k.castSucc))
      (productPartial U v k.castSucc (E (x,y))) 0 :=
    (hU _ hp).hasFDerivAt.hasLineDerivAt (productDirection v k.castSucc)
  apply h₁.unique (h₂.congr_of_eventuallyEq _)
  filter_upwards with t
  rw [he]
  congr 1
  have h : ((x+t • a v k,y) : (I → ℝ) × (V → ℝ)) = (x,y) + t • (a v k,0) := by
    apply Prod.ext
    · rfl
    · change y = y + t • (0 : V → ℝ)
      rw [smul_zero,add_zero]
  rw [h,map_add,map_smul,sourceKPCuspRealHorizontalDir_apply]

theorem sourceKPCuspWirtingerTorus_exists (ε : Bool) (v : V) (y : V → ℝ)
    (hy : ∀ w, 0 < y w) (U : X → ℂ) (hU : ∀ p ∈ Ω, DifferentiableAt ℝ U p)
    (F : C(UnitAddTorus I, ℂ))
    (hF : ContDiff ℝ (∞ : ℕ∞ω) (fun x : I → ℝ => F (P x)))
    (he : ∀ x : I → ℝ, F (P x) = U (E (x,y))) :
    ∃ G : C(UnitAddTorus I, ℂ),
      ContDiff ℝ (∞ : ℕ∞ω) (fun x : I → ℝ => G (P x)) ∧
      (∀ x : I → ℝ, G (P x) = sourceProductHorizontal ε v U (E (x,y))) ∧
      ∀ n : I → ℤ, mFourierCoeff G n =
        sourceKPCuspWirtingerFrequency K ε (sourceKPCuspTraceFrequency K d n) v (y v) *
          mFourierCoeff F n := by
  obtain ⟨g,hg,hgs,hgF⟩ := unitTorus_smooth_coordinate_derivatives I F hF
  let J (k : Fin 2) : C(UnitAddTorus I, ℂ) := ∑ i, (a v k i : ℂ) • g i
  let G : C(UnitAddTorus I, ℂ) :=
    ((y v : ℂ) / 2) • (J 0 + sourceHorizontalOrientation ε • J 1)
  have hJ (k : Fin 2) : ContDiff ℝ (∞ : ℕ∞ω) (fun x : I → ℝ => J k (P x)) := by
    simp only [J,ContinuousMap.coe_sum,Finset.sum_apply,ContinuousMap.coe_smul,Pi.smul_apply]
    exact ContDiff.sum fun i _ => (hgs i).const_smul (a v k i : ℂ)
  refine ⟨G,?_,?_,?_⟩
  · simpa only [G,ContinuousMap.coe_smul,Pi.smul_apply,ContinuousMap.add_apply] using
      ((hJ 0).add ((hJ 1).const_smul (sourceHorizontalOrientation ε))).const_smul ((y v : ℂ) / 2)
  · intro x
    have hJx (k : Fin 2) : J k (P x) = productPartial U v k.castSucc (E (x,y)) := by
      rw [← lift_partial K hζ d hd F U y hy hU (hF.differentiable (by simp)) he x v k]
      conv_rhs => rw [← sum_coord (a v k)]
      simp only [J,ContinuousMap.coe_sum,Finset.sum_apply,ContinuousMap.coe_smul,Pi.smul_apply,hg,
        map_sum,map_smul,Complex.real_smul,smul_eq_mul]
    change ((y v : ℂ) / 2) * (J 0 (P x) + sourceHorizontalOrientation ε * J 1 (P x)) = _
    rw [hJx,hJx,sourceProductHorizontal,sourceKPCuspProductCoordinates_height]
    change ((y v : ℂ) / 2) * (productPartial U v 0 (E (x,y)) +
      sourceHorizontalOrientation ε * productPartial U v 1 (E (x,y))) = _
    ring
  · intro n
    let m := sourceKPCuspTraceFrequency K d n
    let A := 2 * (Real.pi : ℂ) * Complex.I
    have hJn (k : Fin 2) : torusCoefficient n (J k) =
        (A * (∑ i, (a v k i : ℂ) * (n i : ℂ))) * mFourierCoeff F n := by
      simp only [J,map_sum,map_smul,smul_eq_mul]
      change (∑ i, (a v k i : ℂ) * mFourierCoeff (g i) n) = _
      simp_rw [hgF]
      rw [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [A]
      ring
    have hA0 : (∑ i, (a v 0 i : ℂ) * (n i : ℂ)) = (2 * (v.embedding m).re : ℝ) := by
      exact_mod_cast (sourceKPCuspRealHorizontalDir_trace K hζ d hd v n).1
    have hA1 : (∑ i, (a v 1 i : ℂ) * (n i : ℂ)) = (-(2 * (v.embedding m).im) : ℝ) := by
      exact_mod_cast (sourceKPCuspRealHorizontalDir_trace K hζ d hd v n).2
    change torusCoefficient n G = _
    simp only [G,map_smul,map_add,smul_eq_mul,hJn,hA0,hA1,Complex.ofReal_mul,Complex.ofReal_neg]
    let u := v.embedding m
    have hu : (u.re : ℂ) + (u.im : ℂ) * Complex.I = u := Complex.re_add_im u
    have hs : (u.re : ℂ) - (u.im : ℂ) * Complex.I = star u := by
      apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
    change ((y v : ℂ) / 2) * (A * ((2 : ℂ) * u.re) * mFourierCoeff F n +
      sourceHorizontalOrientation ε * (A * (-(2 * (u.im : ℂ))) * mFourierCoeff F n)) =
      A * (y v : ℂ) * (if ε then star u else u) * mFourierCoeff F n
    cases ε
    · simp only [sourceHorizontalOrientation,Bool.false_eq_true,ite_false]
      conv_rhs => rw [← hu]
      ring
    · simp only [sourceHorizontalOrientation,ite_true]
      rw [← hs]
      ring

end
end ArtinMatthews
