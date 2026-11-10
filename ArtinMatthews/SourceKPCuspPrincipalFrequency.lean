module

public import ArtinMatthews.SourceKPCuspPrincipalQuotient
public import ArtinMatthews.SourceKPCuspLevelCover
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

/-! Every rational frequency and every genuine finite-level unipotent orbit
factor through a common actual principal cusp torus. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic Module.Free
open scoped NumberField AdeleRing MatrixGroups nonZeroDivisors Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

private theorem sourceKPCuspRationalInteger_finiteIntegral (a : 𝓞 K) :
    algebraMap K 𝔸ᶠ[K] (a : K) ∈ sourceKPIntegralFiniteRing K := by
  apply (sourceKPIntegralFiniteRing_mem K _).mpr
  intro v
  exact HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := K) v a

theorem sourceKPCuspFiniteIdeal_mul_subset (d e : 𝓞 K) :
    sourceKPCuspFiniteIdeal K (d*e) ≤ sourceKPCuspFiniteIdeal K d := by
  intro t ht
  obtain ⟨x,rfl⟩ := (sourceKPCuspFiniteIdeal_mem K (d*e) t).mp ht
  let u : sourceKPIntegralFiniteRing K :=
    ⟨_,sourceKPCuspRationalInteger_finiteIntegral K e⟩
  apply (sourceKPCuspFiniteIdeal_mem K d _).mpr
  refine ⟨u*x,?_⟩
  change algebraMap K 𝔸ᶠ[K] (d:K)*(algebraMap K 𝔸ᶠ[K] (e:K)*x.val) =
    algebraMap K 𝔸ᶠ[K] ((d*e : 𝓞 K):K)*x.val
  rw [show ((d*e : 𝓞 K):K) = (d:K)*(e:K) from map_mul (algebraMap (𝓞 K) K) d e,
    map_mul,mul_assoc]

theorem sourceKPAdelicCuspFrequencyPeriod (m : K) (g : SourceKPAdelicProjective K hζ) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ (∃ r : 𝓞 K, m*(d:K) = (r:K)) ∧
      ∀ t ∈ sourceKPCuspFiniteIdeal K d,
        ∃ k : sourceKPFiniteDeepMatrixGroup K,
          g⁻¹ * sourceKPAdelicUpperLift K hζ (sourceKPFiniteAddEmbedding K t) * g =
            sourceKPFiniteDeepCoverLift K hζ k := by
  obtain ⟨d,hd,hperiod⟩ := sourceKPAdelicCuspFiniteLevelPeriod K hζ g
  obtain ⟨e,r,hr⟩ := IsLocalization.exists_integer_multiple' (𝓞 K)⁰ m
  change (r : K) = m*(e.val:K) at hr
  refine ⟨d*e.val,mul_ne_zero hd (mem_nonZeroDivisors_iff_ne_zero.mp e.prop),
    ⟨d*r,?_⟩,fun t ht => hperiod t (sourceKPCuspFiniteIdeal_mul_subset K d e.val ht)⟩
  rw [show ((d*e.val : 𝓞 K):K) = (d:K)*(e.val:K) from map_mul (algebraMap (𝓞 K) K) d e.val,
    show ((d*r : 𝓞 K):K) = (d:K)*(r:K) from map_mul (algebraMap (𝓞 K) K) d r,hr]
  ring

private theorem sourceKPCuspFiniteFrequency_period (d : 𝓞 K) (m : K)
    (hm : ∃ r : 𝓞 K, m*(d:K) = (r:K)) {t : 𝔸ᶠ[K]}
    (ht : t ∈ sourceKPCuspFiniteIdeal K d) :
    character K (algebraMap K 𝔸[K] m * sourceKPFiniteAddEmbedding K t) = 1 := by
  obtain ⟨r,hr⟩ := hm
  obtain ⟨x,rfl⟩ := (sourceKPCuspFiniteIdeal_mem K d t).mp ht
  rw [show algebraMap K 𝔸[K] m *
    sourceKPFiniteAddEmbedding K (algebraMap K 𝔸ᶠ[K] (d:K)*x.val) =
    (0,algebraMap K 𝔸ᶠ[K] m*(algebraMap K 𝔸ᶠ[K] (d:K)*x.val)) from Prod.ext (mul_zero _) rfl,
    character_finite,← mul_assoc,← map_mul,hr]
  apply finiteCharacter_integral
  exact (sourceKPIntegralFiniteRing_mem K _).mp
    ((sourceKPIntegralFiniteRing K).mul_mem (sourceKPCuspRationalInteger_finiteIntegral K r) x.prop)

theorem sourceKPCuspPrincipalFrequency_period (d : 𝓞 K) (m : K)
    (hm : ∃ r : 𝓞 K, m*(d:K) = (r:K)) {z : 𝔸[K]}
    (hz : z ∈ sourceKPCuspPrincipalPeriods K d) :
    character K (algebraMap K 𝔸[K] m*z) = 1 := by
  obtain ⟨_,⟨q,rfl⟩,_,⟨t,ht,rfl⟩,rfl⟩ := AddSubgroup.mem_sup.mp hz
  change character K (algebraMap K 𝔸[K] m *
    (algebraMap K 𝔸[K] q + sourceKPFiniteAddEmbedding K t)) = 1
  rw [mul_add,AddChar.map_add_eq_mul,← map_mul (algebraMap K 𝔸[K]) m q,character_principal,
    sourceKPCuspFiniteFrequency_period K d m hm ht,one_mul]

def sourceKPCuspPrincipalFrequency (d : 𝓞 K) (m : K)
    (hm : ∃ r : 𝓞 K, m*(d:K) = (r:K)) : SourceKPCuspPrincipalQuotient K d → ℂ :=
  Quotient.lift (fun x : 𝔸[K] => character K (algebraMap K 𝔸[K] m*x)) (by
    intro a b hab
    have hp := sourceKPCuspPrincipalFrequency_period K d m hm
      (QuotientAddGroup.leftRel_apply.mp hab)
    calc
      _ = character K (algebraMap K 𝔸[K] m*a)*1 := (mul_one _).symm
      _ = character K (algebraMap K 𝔸[K] m*(a+(-a+b))) := by
        rw [mul_add,AddChar.map_add_eq_mul,hp]
      _ = _ := by rw [add_neg_cancel_left])

theorem sourceKPCuspPrincipalFrequency_mk (d : 𝓞 K) (m : K)
    (hm : ∃ r : 𝓞 K, m*(d:K) = (r:K)) (x : 𝔸[K]) :
    sourceKPCuspPrincipalFrequency K d m hm (QuotientAddGroup.mk x) =
      character K (algebraMap K 𝔸[K] m*x) := rfl

theorem sourceKPCuspPrincipalFrequency_continuous (d : 𝓞 K) (m : K)
    (hm : ∃ r : 𝓞 K, m*(d:K) = (r:K)) :
    Continuous (sourceKPCuspPrincipalFrequency K d m hm) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspPrincipalPeriods K d)).continuous_iff.mpr
  exact (character_continuous K).comp (continuous_const.mul continuous_id)

end
end ArtinMatthews
