module

public import ArtinMatthews.SourceKPJacquetSmoothAverage
public import ArtinMatthews.SourceKPTameBorelValues
public import ArtinMatthews.SourceKPJacquetBallCancellation
public import ArtinMatthews.SourceKPJacquetOuterShift
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! The self-dual twisted Jacquet integrals stabilize in the actual
finite-dimensional value space, and define a linear map there. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical MeasureTheory Filter
open scoped NumberField SourcePhysical Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "B" => sourceLocalBall K P
local notation "ν₀" => sourceLocalValuation K P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "n₀" => fun t : L => l₀ (sourceGL2Upper t)
local notation "w₀" => l₀ sourceGL2Weyl
local notation "ψ₀" => localFiniteCharacter K P
local notation "μ₀" => sourceLocalSelfDual K P

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    {ι : Type*} [Fintype ι] (e : V ≃ₗ[ℂ] (ι → ℂ))
local notation "E₀" => sourceKPJacquetCoordinateIntegrand K hζ P ρ C e

theorem sourceKPJacquetCoordinateIntegrand_integrableOn
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C) (f : C) (g : G) (R : ℕ) :
    IntegrableOn (E₀ f g) (B (R : ℤ)) μ₀ := by
  obtain ⟨M, hM⟩ := hSmooth f
  have hc := sourceKPJacquetCoordinateIntegrand_continuous K hζ P ρ C e f g M
    (fun u hu k => (hM u hu k).1)
  let : (μ₀).IsAddHaarMeasure := sourceLocalSelfDual_isHaar K P
  exact hc.continuousOn.integrableOn_compact (sourceLocalBall_isCompact K P _)

def sourceKPJacquetTruncation (R : ℕ) (f : C) : V :=
  e.symm (∫ t in B (R : ℤ), E₀ f w₀ t ∂μ₀)

local notation "Tr" => sourceKPJacquetTruncation K hζ P ρ C e

theorem sourceKPJacquetTruncation_add (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)
    (R : ℕ) (f g : C) : Tr R (f + g) = Tr R f + Tr R g := by
  have hfg : E₀ (f + g) w₀ = fun t => E₀ f w₀ t + E₀ g w₀ t := by
    funext t
    change ψ₀ (-t) • e (f.val.val (w₀ * n₀ t) + g.val.val (w₀ * n₀ t)) = _
    rw [map_add, smul_add]
    rfl
  unfold sourceKPJacquetTruncation
  rw [hfg, integral_add
    (sourceKPJacquetCoordinateIntegrand_integrableOn K hζ P ρ C e hSmooth f w₀ R)
    (sourceKPJacquetCoordinateIntegrand_integrableOn K hζ P ρ C e hSmooth g w₀ R), map_add]

theorem sourceKPJacquetTruncation_smul (R : ℕ) (a : ℂ) (f : C) : Tr R (a • f) = a • Tr R f := by
  have h : E₀ (a • f) w₀ = fun t => a • E₀ f w₀ t := by
    funext t
    change ψ₀ (-t) • e (a • f.val.val (w₀ * n₀ t)) = _
    rw [map_smul, smul_comm (ψ₀ (-t)) a]
    rfl
  unfold sourceKPJacquetTruncation
  rw [h, integral_smul, map_smul]

def SourceKPJacquetHasStableValue (f : C) (v : V) : Prop :=
  ∀ᶠ R : ℕ in atTop, Tr R f = v

local notation "Stable" => SourceKPJacquetHasStableValue K hζ P ρ C e

theorem sourceKPJacquetHasStableValue_unique {f : C} {v v' : V}
    (hv : Stable f v) (hv' : Stable f v') : v = v' := by
  obtain ⟨R, hR, hR'⟩ := (hv.and hv').exists
  exact hR.symm.trans hR'

variable (hUpper : ∀ x : P.adicCompletion K, ∀ v : V, ρ (sourceFiniteKPProjectiveBorelUpper K hζ P x) v = v)
    (hCube : ∀ y : (P.adicCompletion K)ˣ, sourceLocalValuation K P
      (((y ^ 3 : (P.adicCompletion K)ˣ) : P.adicCompletion K)) = 1 → ∀ v : V,
      ρ (sourceFiniteKPProjectiveBorelDiagonal K hζ P (y ^ 3)) v = v)
    (hSmooth : SourceKPJacquetRootSmooth K hζ P ρ C)

include hUpper hCube hSmooth in
theorem sourceKPJacquet_hasStableValue_exists (f : C) : ∃ v : V, Stable f v := by
  obtain ⟨a, haψ⟩ := sourceKPJacquetSelfDual_fixed_shift_exists K P
  obtain ⟨M, hM⟩ := hSmooth f
  obtain ⟨R₀, ha, hOuter⟩ := sourceKPJacquet_open_cell_eventual_fixed_shift K hζ P ρ f.val
    hUpper hCube M (fun t ht => by simpa only [one_mul] using (hM t ht 1).2) a
  have hshift (t : L) (ht : t ∉ B (R₀ : ℤ)) : E₀ f w₀ (t + a) = ψ₀ (-a) • E₀ f w₀ t := by
    unfold sourceKPJacquetCoordinateIntegrand
    rw [hOuter t ht, neg_add, AddChar.map_add_eq_mul, mul_comm (ψ₀ (-t)), smul_smul]
  refine ⟨Tr R₀ f, eventually_atTop.mpr ⟨R₀, ?_⟩⟩
  intro R hR
  unfold sourceKPJacquetTruncation
  apply congrArg e.symm
  exact sourceKPJacquetSelfDual_truncation_stabilizes K P (E₀ f w₀) R₀ a ha (ψ₀ (-a)) haψ
    (sourceKPJacquetCoordinateIntegrand_integrableOn K hζ P ρ C e hSmooth f w₀) hshift R hR

local notation "hEx" => sourceKPJacquet_hasStableValue_exists K hζ P ρ C e hUpper hCube hSmooth

def sourceKPJacquetStableMap : C →ₗ[ℂ] V where
  toFun f := (hEx f).choose
  map_add' f g := by
    apply sourceKPJacquetHasStableValue_unique K hζ P ρ C e (hEx (f + g)).choose_spec
    filter_upwards [(hEx f).choose_spec, (hEx g).choose_spec] with R hf hg
    rw [sourceKPJacquetTruncation_add K hζ P ρ C e hSmooth, hf, hg]
  map_smul' a f := by
    apply sourceKPJacquetHasStableValue_unique K hζ P ρ C e (hEx (a • f)).choose_spec
    filter_upwards [(hEx f).choose_spec] with R hf
    rw [sourceKPJacquetTruncation_smul K hζ P ρ C e, hf]
    rfl

theorem sourceKPJacquetStableMap_hasStableValue (f : C) :
    Stable f (sourceKPJacquetStableMap K hζ P ρ C e hUpper hCube hSmooth f) := (hEx f).choose_spec

end
end ArtinMatthews
