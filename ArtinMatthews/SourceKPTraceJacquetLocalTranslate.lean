module

public import ArtinMatthews.SourceKPTraceJacquetLocalFinite
public import ArtinMatthews.SourceKPTameSphericalTranslate
public import ArtinMatthews.SourceKPTameParametricOpenCell
public import ArtinMatthews.SourceLocalAffineIntegral
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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The finite shell formula after an actual local right translate.
The inverse torus action, central scalar, translated additive phase,
and finite-place Haar modulus are all kept in the formula. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic SourcePhysical QuadraticWeil
open scoped NumberField
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "π₀" => sourceKPTameExteriorUniformizer K hζ S₀ P
local notation "hπ₀" => sourceKPTameExteriorUniformizer_valuation K hζ S₀ P
local notation "h₆" => source_exterior_six_not_mem K S₀ P.val P.property
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "μ₀" => sourceJacquetHaar K P.val
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P.val
local notation "κ₀" => sourceFiniteKP2ProjectiveCompactSection K hζ P.val h₆
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P.val
local notation "τ₀" => sourceKPTameParametricBorelRepresentation K hζ P.val h₆ π₀ hπ₀
local notation "b₀" => sourceFiniteKPProjectiveBorelDiagonal K hζ P.val
local notation "F₀" => sourceKPTameSphericalPlainIntegrand K hζ S₀ P

def sourceKPTraceJacquetLocalTranslatedIntegrand (s : ℂ) (m : Lˣ) (g : G₀) (x : L) :
    ZMod 3 → ℂ :=
  ψ₀ (-((m : L)*x)) • F₀ s g x

def sourceKPTraceJacquetLocalTranslatedValue (s : ℂ) (m : Lˣ) (z : rootsOfUnity 3 L)
    (u : L) (y : Lˣ) : ZMod 3 → ℂ :=
  ((sourceKPCentralComplex K hζ P.val z : ℂ) * ψ₀ ((m : L)*u)) •
    τ₀ s (b₀ y⁻¹) (‖(y : L)‖ • sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s (m*y))

theorem sourceKPTraceJacquetLocalTranslatedIntegrand_iwasawa (s : ℂ) (m : Lˣ) (g : G₀)
    (z : rootsOfUnity 3 L) (u : L) (y : Lˣ) (k : SourceFiniteKP2Integral K P.val)
    (hg : g = z₀ z * l₀ (sourceGL2Upper u) * l₀ (sourceGL2Diagonal y) * κ₀ k) (x : L) :
    sourceKPTraceJacquetLocalTranslatedIntegrand K hζ S₀ P s m g x =
      ((sourceKPCentralComplex K hζ P.val z : ℂ) * ψ₀ ((m : L)*u)) •
        τ₀ s (b₀ y⁻¹) (sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s
          ((m*y : Lˣ) : L) ((x+u)/(y : L))) := by
  let t := (x+u)/(y : L)
  have ht : ψ₀ (-((m : L)*x)) = ψ₀ ((m : L)*u) * ψ₀ (-(((m*y : Lˣ) : L)*t)) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    rw [Units.val_mul]
    change -((m : L)*x) = (m : L)*u + -(((m : L)*(y : L))*((x+u)/(y : L)))
    rw [mul_assoc, mul_div_cancel₀ _ y.ne_zero]
    ring
  rw [sourceKPTraceJacquetLocalTranslatedIntegrand,
    sourceKPTameSphericalPlainIntegrand_iwasawa K hζ S₀ P s g z u y k hg x, ht]
  change _ = ((sourceKPCentralComplex K hζ P.val z : ℂ) * ψ₀ ((m : L)*u)) •
    τ₀ s (b₀ y⁻¹) (sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s ((m*y : Lˣ) : L) t)
  rw [sourceKPTraceJacquetLocalOrdinaryIntegrand, ← sourceKPTameParametricSpherical_open K hζ S₀ P, map_smul]
  simp only [sourceKPTameSphericalPlainIntegrand, mul_one, smul_smul]
  congr 1
  ring

theorem sourceKPTraceJacquetLocalTranslated_integral (hP : P.val ∉ traceBadPlaces K)
    {s : ℂ} (hs : 0 < s.re) (m : Lˣ) (g : G₀)
    (z : rootsOfUnity 3 L) (u : L) (y : Lˣ) (k : SourceFiniteKP2Integral K P.val)
    (hg : g = z₀ z * l₀ (sourceGL2Upper u) * l₀ (sourceGL2Diagonal y) * κ₀ k) :
    Integrable (sourceKPTraceJacquetLocalTranslatedIntegrand K hζ S₀ P s m g) μ₀ ∧
    (∫ x, sourceKPTraceJacquetLocalTranslatedIntegrand K hζ S₀ P s m g x ∂μ₀) =
      sourceKPTraceJacquetLocalTranslatedValue K hζ S₀ P s m z u y := by
  let A : (ZMod 3 → ℂ) →L[ℂ] (ZMod 3 → ℂ) := LinearMap.toContinuousLinearMap (τ₀ s (b₀ y⁻¹))
  let I := sourceKPTraceJacquetLocalOrdinaryIntegrand K hζ S₀ P s ((m*y : Lˣ) : L)
  let c := (sourceKPCentralComplex K hζ P.val z : ℂ) * ψ₀ ((m : L)*u)
  have hI : Integrable I μ₀ :=
    sourceKPTraceJacquetLocalOrdinaryIntegrand_integrable K hζ S₀ P hP hs ((m*y : Lˣ) : L)
  have ha := (sourceLocalIntegrable_affine_iff K P.val hP u y I).mpr hI
  have he : sourceKPTraceJacquetLocalTranslatedIntegrand K hζ S₀ P s m g =
      fun x => c • A (I ((x+u)/(y : L))) :=
    funext (sourceKPTraceJacquetLocalTranslatedIntegrand_iwasawa K hζ S₀ P s m g z u y k hg)
  rw [he]
  refine ⟨(A.integrable_comp ha).smul c,?_⟩
  rw [integral_smul, A.integral_comp_comm ha, sourceLocalIntegral_affine K P.val hP u y]
  change c • A (‖(y : L)‖ • sourceKPTraceJacquetLocalOrdinary K hζ S₀ P s ((m*y : Lˣ) : L)) = _
  rw [sourceKPTraceJacquetLocalOrdinary_eq_finite K hζ S₀ P hP hs (m*y)]
  rfl

theorem sourceKPTraceJacquetLocalTranslatedValue_entire (m : Lˣ) (z : rootsOfUnity 3 L)
    (u : L) (y : Lˣ) :
    Differentiable ℂ (fun s => sourceKPTraceJacquetLocalTranslatedValue K hζ S₀ P s m z u y) := by
  let A : (ZMod 3 → ℂ) →L[ℂ] (ZMod 3 → ℂ) := LinearMap.toContinuousLinearMap
    (sourceKPTameBorelRepresentation K hζ P.val h₆ π₀ hπ₀ (b₀ y⁻¹))
  let c : ℂ := (sourceKPCentralComplex K hζ P.val z : ℂ) * ψ₀ ((m : L)*u)
  let θ : ℂ → ℂ := fun s => sourceKPTameBorelTwist K hζ P.val s (b₀ y⁻¹)
  let V : ℂ → ZMod 3 → ℂ := fun s => ‖(y : L)‖ •
    sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s (m*y)
  have hθ : Differentiable ℂ θ := by
    dsimp only [θ]
    simp only [sourceKPTameBorelTwist_diagonal]
    fun_prop
  have hV : Differentiable ℂ V := by
    change Differentiable ℂ (‖(y : L)‖ • (fun s => sourceKPTraceJacquetLocalFiniteValue K hζ S₀ P s (m*y)))
    exact (sourceKPTraceJacquetLocalFiniteValue_entire K hζ S₀ P (m*y)).const_smul ‖(y : L)‖
  have hprod : Differentiable ℂ (fun s => θ s • A (V s)) := hθ.smul (A.differentiable.comp hV)
  change Differentiable ℂ (c • fun s => θ s • A (V s))
  exact hprod.const_smul c

end
end ArtinMatthews
