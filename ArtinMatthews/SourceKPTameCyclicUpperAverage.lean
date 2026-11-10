module

public import ArtinMatthews.SourceJacquetFiniteUpperQuotient
public import ArtinMatthews.SourceKPTameCyclicWhittaker
public import ArtinMatthews.CompactFiniteAverage
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.StandardLocalFourier
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Mathlib.Topology.Connected.Separation
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Finite upper-root averaging on the genuine cyclic representation.
Small-ball invariance identifies the finite average with its actual
Haar integral at every point of the cover. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain StandardAdelic SourcePhysical QuadraticWeil MeasureTheory Filter
open scoped NumberField SourcePhysical Classical BigOperators Topology
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (S₀ : Finset (HeightOneSpectrum (𝓞 K))) (P : SourceExteriorPrime K S₀)

local notation "L" => P.val.adicCompletion K
local notation "G₀" => SourceFiniteKP2Projective K hζ P.val
local notation "C₀" => sourceKPTameSphericalCyclicSpace K hζ S₀ P
local notation "r₀" => sourceKPTameSphericalCyclicRepresentation K hζ S₀ P
local notation "n₀" => fun t : L => sourceFiniteKP2ProjectiveLift K hζ P.val (sourceGL2Upper t)
local notation "ψ₀" => localFiniteCharacter K P.val
local notation "ν₀" => sourceLocalValuation K P.val
local notation "B" => sourceLocalBall K P.val
local notation "μ₀" => sourceJacquetHaar K P.val

def sourceKPTameCyclicEval (g : G₀) : C₀ →ₗ[ℂ] (ZMod 3 → ℂ) where
  toFun f := f.val.val g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sourceKPTameCyclicUpperIntegrand (f : C₀) (g : G₀) (t : L) : ZMod 3 → ℂ :=
  ψ₀ (-t) • f.val.val (g * n₀ t)

local notation "E₀" => sourceKPTameCyclicUpperIntegrand K hζ S₀ P

theorem sourceKPTameCyclicUpperIntegrand_eq_of_small (f : C₀) (g : G₀) (M : ℕ)
    (hfix : ∀ u : L, ν₀ u ≤ WithZero.exp (-(M : ℤ)) → r₀ (n₀ u) f = f)
    (x t : L) (ht : ν₀ (t - x) ≤ WithZero.exp (-(M : ℤ))) : E₀ f g t = E₀ f g x := by
  let u := t - x
  have hu : ν₀ u ≤ 1 := ht.trans (by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega))
  have hneg : -u ∈ P.val.adicCompletionIntegers K := by
    change ν₀ (-u) ≤ 1
    rw [Valuation.map_neg]
    exact hu
  have hψ : ψ₀ (-t) = ψ₀ (-x) := by
    have hsum : -t = -x + -u := by dsimp [u]; abel
    rw [hsum, AddChar.map_add_eq_mul, localFiniteCharacter_integral K P.val (-u) hneg, mul_one]
  have hf := congrArg (sourceKPTameCyclicEval K hζ S₀ P (g * n₀ x)) (hfix u ht)
  change f.val.val ((g * n₀ x) * n₀ u) = f.val.val (g * n₀ x) at hf
  have hxu : x + u = t := by dsimp [u]; abel
  rw [mul_assoc, sourceFiniteKP2ProjectiveLift_upper_add, hxu] at hf
  unfold sourceKPTameCyclicUpperIntegrand
  rw [hψ, hf]

theorem sourceKPTameCyclicUpperIntegrand_continuous (f : C₀) (g : G₀) (M : ℕ)
    (hfix : ∀ u : L, ν₀ u ≤ WithZero.exp (-(M : ℤ)) → r₀ (n₀ u) f = f) :
    Continuous (E₀ f g) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply continuousAt_const.congr_of_eventuallyEq
  have hU : IsOpen ((fun u : L => u - t) ⁻¹' B (-(M : ℤ))) :=
    (sourceLocalBall_isOpen K P.val _).preimage (continuous_id.sub continuous_const)
  have ht : t ∈ (fun u : L => u - t) ⁻¹' B (-(M : ℤ)) := by
    change ν₀ (t - t) ≤ _
    rw [sub_self, map_zero]
    exact zero_le
  filter_upwards [hU.mem_nhds ht] with u hu
  exact sourceKPTameCyclicUpperIntegrand_eq_of_small K hζ S₀ P f g M hfix t u hu

def sourceKPTameCyclicUpperAverage (R M : ℕ) (f : C₀) : C₀ := by
  let A := SourceJacquetUpperQuotient K P.val R M
  letI : Finite A := sourceJacquetUpperQuotient_finite K P.val R M
  letI : Fintype A := Fintype.ofFinite A
  let rep (a : A) : L := sourceJacquetUpperRepresentative K P.val R M a
  exact (Fintype.card A : ℂ)⁻¹ • ∑ a : A, ψ₀ (-rep a) • r₀ (n₀ (rep a)) f

theorem sourceKPTameCyclicUpperAverage_eval_integral (R M : ℕ) (f : C₀) (g : G₀)
    (hfix : ∀ u : L, ν₀ u ≤ WithZero.exp (-(M : ℤ)) → r₀ (n₀ u) f = f) :
    (Measure.real μ₀ (B (R : ℤ)) : ℂ) • (sourceKPTameCyclicUpperAverage K hζ S₀ P R M f).val.val g =
      ∫ t in B (R : ℤ), E₀ f g t ∂μ₀ := by
  let U := sourceJacquetUpperBall K P.val R
  let A := SourceJacquetUpperQuotient K P.val R M
  let : Finite A := sourceJacquetUpperQuotient_finite K P.val R M
  let : Fintype A := Fintype.ofFinite A
  let : Measure.IsAddHaarMeasure μ₀ := sourceJacquetHaar_isAddHaar K P.val
  let rep (a : A) : U := sourceJacquetUpperRepresentative K P.val R M a
  let r := sourceJacquetUpperReduction K P.val R M
  have hr : Function.Surjective r := sourceJacquetUpperReduction_surjective K P.val R M
  have hU : IsCompact (U : Set L) := sourceLocalBall_isCompact K P.val (R : ℤ)
  have hc : Continuous (E₀ f g) := sourceKPTameCyclicUpperIntegrand_continuous K hζ S₀ P f g M hfix
  have hi : IntegrableOn (E₀ f g) (U : Set L) μ₀ := hc.continuousOn.integrableOn_compact hU
  have hfactor (t : U) : E₀ f g (t : L) = E₀ f g (rep (r t) : L) := by
    have h := sourceJacquetUpperRepresentative_class K P.val R M (r t)
    have ht : ν₀ ((rep (r t) : L) - (t : L)) ≤ WithZero.exp (-(M : ℤ)) :=
      (sourceJacquetUpperReduction_eq_iff K P.val R M t (rep (r t))).mp h.symm
    exact (sourceKPTameCyclicUpperIntegrand_eq_of_small K hζ S₀ P f g M hfix t (rep (r t)) ht).symm
  let ev := sourceKPTameCyclicEval K hζ S₀ P g
  have hev : ev (sourceKPTameCyclicUpperAverage K hζ S₀ P R M f) =
      (Fintype.card A : ℂ)⁻¹ • ∑ a : A, E₀ f g (rep a : L) := by
    unfold sourceKPTameCyclicUpperAverage
    rw [map_smul, map_sum]
    rfl
  change (Measure.real μ₀ (U : Set L) : ℂ) • ev (sourceKPTameCyclicUpperAverage K hζ S₀ P R M f) =
    ∫ t in (U : Set L), E₀ f g t ∂μ₀
  rw [hev]
  funext i
  let pr : (ZMod 3 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  have hproj := pr.integral_comp_comm hi
  change (∫ t in (U : Set L), E₀ f g t i ∂μ₀) = (∫ t in (U : Set L), E₀ f g t ∂μ₀) i at hproj
  rw [← hproj]
  have hI := compact_finite_integral μ₀ U hU r hr (fun a => E₀ f g (rep a : L) i)
    (fun t => E₀ f g t i) (pr.continuous.comp hc) (fun t => congrFun (hfactor t) i)
  rw [hI]
  change (Measure.real μ₀ (U : Set L) : ℂ) * ((Fintype.card A : ℂ)⁻¹ * (∑ a : A, E₀ f g (rep a : L)) i) = _
  rw [Finset.sum_apply, div_eq_mul_inv]
  ring

theorem sourceKPTameCyclicUpperAverage_whittaker (R M : ℕ) (f : C₀) (ℓ : C₀ →ₗ[ℂ] ℂ)
    (hℓ : ∀ (x : L) (v : C₀), ℓ (r₀ (n₀ x) v) = ψ₀ x * ℓ v) :
    ℓ (sourceKPTameCyclicUpperAverage K hζ S₀ P R M f) = ℓ f := by
  let A := SourceJacquetUpperQuotient K P.val R M
  let : Finite A := sourceJacquetUpperQuotient_finite K P.val R M
  let : Fintype A := Fintype.ofFinite A
  let rep (a : A) : L := sourceJacquetUpperRepresentative K P.val R M a
  unfold sourceKPTameCyclicUpperAverage
  rw [map_smul, map_sum]
  have hterm (a : A) : ℓ (ψ₀ (-rep a) • r₀ (n₀ (rep a)) f) = ℓ f := by
    rw [map_smul, hℓ]
    change ψ₀ (-rep a) * (ψ₀ (rep a) * ℓ f) = ℓ f
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, one_mul]
  change (Fintype.card A : ℂ)⁻¹ • (∑ a : A, ℓ (ψ₀ (-rep a) • r₀ (n₀ (rep a)) f)) = ℓ f
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card A : ℂ) ≠ 0), one_mul]

end
end ArtinMatthews
