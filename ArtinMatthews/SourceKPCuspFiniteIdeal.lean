module

public import ArtinMatthews.SourceKPFiniteUnitTopology
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
public import Mathlib.Topology.Sheaves.Init
public import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactQuotient


set_option backward.privateInPublic true
@[expose] public section

/-! The actual finite principal ideal used for a cusp torus sublevel. -/

set_option relaxedAutoImplicit false

namespace ArtinMatthews
open NumberField IsDedekindDomain Topology
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing
noncomputable section

variable (K : Type) [Field K] [NumberField K] (d : 𝓞 K)

def sourceKPCuspFiniteScale : 𝔸ᶠ[K] →+ 𝔸ᶠ[K] where
  toFun x := algebraMap K 𝔸ᶠ[K] (d : K) * x
  map_zero' := mul_zero _
  map_add' _ _ := mul_add _ _ _

def sourceKPCuspFiniteIdeal : AddSubgroup 𝔸ᶠ[K] :=
  (sourceKPIntegralFiniteRing K).toAddSubgroup.map (sourceKPCuspFiniteScale K d)

lemma sourceKPCuspFiniteIdeal_mem (x : 𝔸ᶠ[K]) :
    x ∈ sourceKPCuspFiniteIdeal K d ↔
      ∃ y : sourceKPIntegralFiniteRing K, algebraMap K 𝔸ᶠ[K] (d : K) * (y : 𝔸ᶠ[K]) = x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨⟨y, hy⟩, hxy⟩
  · rintro ⟨y, hxy⟩
    exact ⟨y, y.property, hxy⟩

omit [NumberField K] in
lemma sourceKPCuspInteger_ne_zero (hd : d ≠ 0) : (d : K) ≠ 0 := by exact_mod_cast hd

def sourceKPCuspFiniteScaleHomeomorph (hd : d ≠ 0) : 𝔸ᶠ[K] ≃ₜ 𝔸ᶠ[K] where
  toFun := sourceKPCuspFiniteScale K d
  invFun x := algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * x
  left_inv x := by
    change algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * (algebraMap K 𝔸ᶠ[K] (d : K) * x) = x
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), map_one, one_mul]
  right_inv x := by
    change algebraMap K 𝔸ᶠ[K] (d : K) * (algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * x) = x
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), map_one, one_mul]
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

lemma sourceKPCuspFiniteIdeal_isOpen (hd : d ≠ 0) : IsOpen (sourceKPCuspFiniteIdeal K d : Set 𝔸ᶠ[K]) := by
  rw [sourceKPCuspFiniteIdeal, AddSubgroup.coe_map]
  exact (sourceKPCuspFiniteScaleHomeomorph K d hd).isOpenMap _ (sourceKPIntegralFiniteRing_isOpen K)

lemma sourceKPCuspFiniteIdeal_isCompact (hd : d ≠ 0) : IsCompact (sourceKPCuspFiniteIdeal K d : Set 𝔸ᶠ[K]) := by
  rw [sourceKPCuspFiniteIdeal, AddSubgroup.coe_map]
  exact (sourceKPIntegralFiniteRing_isCompact K).image (sourceKPCuspFiniteScaleHomeomorph K d hd).continuous

lemma sourceKPCuspFiniteIdeal_rational (hd : d ≠ 0) (q : K) :
    algebraMap K 𝔸ᶠ[K] q ∈ sourceKPCuspFiniteIdeal K d ↔
      ∃ r : 𝓞 K, (d : K) * (r : K) = q := by
  rw [sourceKPCuspFiniteIdeal_mem]
  constructor
  · rintro ⟨x, hx⟩
    have he : algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹ * q) = (x : 𝔸ᶠ[K]) := by
      rw [map_mul, ← hx, ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), map_one, one_mul]
    have hmem : algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹ * q) ∈ IntegralAdeles.Construction.finiteIntegralRing K := by
      rw [he]
      exact (sourceKPIntegralFiniteRing_mem K x.val).mp x.property
    obtain ⟨r, hr⟩ := (IntegralAdeles.Construction.rational_mem_finiteIntegral_iff K _).mp hmem
    refine ⟨r, ?_⟩
    change (r : K) = (d : K)⁻¹ * q at hr
    rw [hr, ← mul_assoc, mul_inv_cancel₀ (sourceKPCuspInteger_ne_zero K d hd), one_mul]
  · rintro ⟨r, rfl⟩
    have hr : algebraMap K 𝔸ᶠ[K] (r : K) ∈ sourceKPIntegralFiniteRing K := by
      apply (sourceKPIntegralFiniteRing_mem K _).mpr
      intro P
      exact HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := K) P r
    exact ⟨⟨_, hr⟩, (map_mul (algebraMap K 𝔸ᶠ[K]) _ _).symm⟩

lemma sourceKPCuspFiniteIdeal_remainder (hd : d ≠ 0) (a : 𝔸ᶠ[K]) :
    ∃ q : K, a - algebraMap K 𝔸ᶠ[K] q ∈ sourceKPCuspFiniteIdeal K d := by
  obtain ⟨q, hq⟩ := CompactQuotient.Construction.exists_rational_finite_integral_remainder K
    (algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * a)
  have hmem : algebraMap K 𝔸ᶠ[K] ((d : K)⁻¹) * a - algebraMap K 𝔸ᶠ[K] q ∈ sourceKPIntegralFiniteRing K :=
    (sourceKPIntegralFiniteRing_mem K _).mpr hq
  refine ⟨(d : K) * q, (sourceKPCuspFiniteIdeal_mem K d _).mpr ⟨⟨_, hmem⟩, ?_⟩⟩
  rw [mul_sub, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (sourceKPCuspInteger_ne_zero K d hd),
    map_one, one_mul, map_mul]

end
end ArtinMatthews
