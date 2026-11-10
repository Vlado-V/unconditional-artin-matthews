module

public import ArtinMatthews.SourceKPCuspPrincipalCellIntegral
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
public import OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation


set_option backward.privateInPublic true
@[expose] public section

/-! The actual standard additive character descends to the original principal
cusp quotient for every frequency in the trace-dual fractional ideal. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain MeasureTheory StandardAdelic Module.Free
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField AdeleRing MatrixGroups nonZeroDivisors Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]

local notation "P[" d "]" =>
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ P[d]
local notation "Q[" d "]" => SourceKPCuspPrincipalQuotient K d
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)

theorem sourceKPCuspTraceDual_iff_integralTrace (d : 𝓞 K) (hd : d ≠ 0) (m : K) :
    m ∈ D[d] ↔ ∀ a : 𝓞 K, ∃ n : ℤ, Algebra.trace ℚ K (m * ((d:K) * (a:K))) = (n : ℚ) := by
  have hdI : P[d] ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr (by simpa using hd)
  rw [FractionalIdeal.mem_dual hdI]
  constructor
  · intro h a
    have ha : d*a ∈ (Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) :=
      Ideal.mul_mem_right a _ (Ideal.mem_span_singleton_self d)
    have ha' : (d : K) * (a : K) ∈ P[d] := by
      rw [← map_mul (algebraMap (𝓞 K) K) d a]
      exact FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰ ha
    obtain ⟨n,hn⟩ := h _ ha'
    exact ⟨n,hn.symm⟩
  · intro h x hx
    obtain ⟨a,ha,rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    obtain ⟨r,rfl⟩ := Ideal.mem_span_singleton.mp ha
    obtain ⟨n,hn⟩ := h r
    refine ⟨n,?_⟩
    rw [map_mul]
    exact hn.symm

theorem sourceKPCuspTraceDualFrequency_finite_period (d : 𝓞 K) (hd : d ≠ 0)
    (m : K) (hm : m ∈ D[d]) {t : 𝔸ᶠ[K]} (ht : t ∈ sourceKPCuspFiniteIdeal K d) :
    character K (algebraMap K 𝔸[K] m * sourceKPFiniteAddEmbedding K t) = 1 := by
  obtain ⟨x,rfl⟩ := (sourceKPCuspFiniteIdeal_mem K d t).mp ht
  let F (u : IntegralAdeles.Construction.finiteIntegralRing K) : ℂ :=
    finiteCharacter K (algebraMap K 𝔸ᶠ[K] m *
      (algebraMap K 𝔸ᶠ[K] (d:K) * (u : 𝔸ᶠ[K])))
  have hF : Continuous F := (finiteCharacter_continuous K).comp
    (continuous_const.mul (continuous_const.mul continuous_subtype_val))
  have hFone (u : IntegralAdeles.Construction.finiteIntegralRing K) : F u = 1 := by
    refine (StrongApproximation.Construction.denseRange_integer_finiteIntegralRing K).induction_on
      (p := fun u => F u = 1) u (isClosed_eq hF continuous_const) ?_
    intro a
    obtain ⟨n,hn⟩ := (sourceKPCuspTraceDual_iff_integralTrace K d hd m).mp hm a
    have hr : rationalCharacter K (m * ((d:K) * (a:K))) = 1 := by
      change archCharacter K (algebraMap K (InfiniteAdeleRing K) (m * ((d:K) * (a:K)))) = 1
      rw [archCharacter_rational,hn]
      simpa only [Rat.cast_intCast] using Complex.exp_int_mul_two_pi_mul_I n
    change finiteCharacter K (algebraMap K 𝔸ᶠ[K] m *
      (algebraMap K 𝔸ᶠ[K] (d:K) * algebraMap (𝓞 K) 𝔸ᶠ[K] a)) = 1
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K 𝔸ᶠ[K], ← map_mul, ← map_mul,
      finiteCharacter_rational,hr,inv_one]
  rw [show algebraMap K 𝔸[K] m *
    sourceKPFiniteAddEmbedding K (algebraMap K 𝔸ᶠ[K] (d:K) * x.val) =
    ((0,algebraMap K 𝔸ᶠ[K] m * (algebraMap K 𝔸ᶠ[K] (d:K) * x.val)) : 𝔸[K])
    from Prod.ext (mul_zero _) rfl, character_finite]
  exact hFone ⟨x.val,(sourceKPIntegralFiniteRing_mem K x.val).mp x.prop⟩

theorem sourceKPCuspTraceDualFrequency_period (d : 𝓞 K) (hd : d ≠ 0) (m : K)
    (hm : m ∈ D[d]) {z : 𝔸[K]} (hz : z ∈ sourceKPCuspPrincipalPeriods K d) :
    character K (algebraMap K 𝔸[K] m * z) = 1 := by
  obtain ⟨_,⟨q,rfl⟩,_,⟨t,ht,rfl⟩,rfl⟩ := AddSubgroup.mem_sup.mp hz
  change character K (algebraMap K 𝔸[K] m *
    (algebraMap K 𝔸[K] q + sourceKPFiniteAddEmbedding K t)) = 1
  rw [mul_add,AddChar.map_add_eq_mul,← map_mul (algebraMap K 𝔸[K]) m q,character_principal,
    sourceKPCuspTraceDualFrequency_finite_period K d hd m hm ht,one_mul]

def sourceKPCuspTraceDualFrequency (d : 𝓞 K) (hd : d ≠ 0) (m : K)
    (hm : m ∈ D[d]) : Q[d] → ℂ :=
  Quotient.lift (fun x : 𝔸[K] => character K (algebraMap K 𝔸[K] m * x)) (by
    intro a b hab
    have hp := sourceKPCuspTraceDualFrequency_period K d hd m hm
      (QuotientAddGroup.leftRel_apply.mp hab)
    calc
      _ = character K (algebraMap K 𝔸[K] m * a) * 1 := (mul_one _).symm
      _ = character K (algebraMap K 𝔸[K] m * (a+(-a+b))) := by
        rw [mul_add,AddChar.map_add_eq_mul,hp]
      _ = _ := by rw [add_neg_cancel_left])

theorem sourceKPCuspTraceDualFrequency_mk (d : 𝓞 K) (hd : d ≠ 0) (m : K)
    (hm : m ∈ D[d]) (x : 𝔸[K]) :
    sourceKPCuspTraceDualFrequency K d hd m hm (QuotientAddGroup.mk x) =
      character K (algebraMap K 𝔸[K] m * x) := rfl

theorem sourceKPCuspTraceDualFrequency_continuous (d : 𝓞 K) (hd : d ≠ 0) (m : K)
    (hm : m ∈ D[d]) :
    Continuous (sourceKPCuspTraceDualFrequency K d hd m hm) := by
  apply (QuotientAddGroup.isQuotientMap_mk (sourceKPCuspPrincipalPeriods K d)).continuous_iff.mpr
  exact (character_continuous K).comp (continuous_const.mul continuous_id)

variable {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local instance sourceTraceDualAdelicMeasurable : MeasurableSpace 𝔸[K] := borel _
local instance sourceTraceDualAdelicBorel : BorelSpace 𝔸[K] := ⟨rfl⟩
local instance sourceTraceDualQuotientMeasurable (d : 𝓞 K) : MeasurableSpace Q[d] := borel _
local instance sourceTraceDualQuotientBorel (d : 𝓞 K) : BorelSpace Q[d] := ⟨rfl⟩

include hζ in
theorem sourceKPCuspTraceDualFrequency_integral_unitCell (d : 𝓞 K) (hd : d ≠ 0) (m : K)
    (hm : m ∈ D[d]) (F : Q[d] → ℂ) (hF : Measurable F) :
    (∫ a in sourceKPAdelicFundamentalDomain K,
        star (character K (algebraMap K 𝔸[K] m*a))*F (QuotientAddGroup.mk a)
        ∂sourceKPAdelicTraceProduct K) =
      ∫ x : I → ℝ, star (character K (algebraMap K 𝔸[K] m*sourceKPCuspUnitCellAdelicPoint K d hd x))*
        F (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x)) ∂unitTorusUnitCellMeasure I := by
  let G : Q[d] → ℂ := fun x => star (sourceKPCuspTraceDualFrequency K d hd m hm x)*F x
  have hG : Measurable G := ((sourceKPCuspTraceDualFrequency_continuous K d hd m hm).star.measurable).mul hF
  have h₁ : (∫ x, G x ∂sourceKPCuspTraceHaar K d) =
      ∫ a in sourceKPAdelicFundamentalDomain K, G (QuotientAddGroup.mk a) ∂sourceKPAdelicTraceProduct K := by
    unfold sourceKPCuspTraceHaar
    exact integral_map QuotientAddGroup.continuous_mk.measurable.aemeasurable hG.aestronglyMeasurable
  have h := sourceKPCuspUnitCellAdelicPoint_measurePreserving K hζ d hd
  have hGm : AEStronglyMeasurable G (Measure.map
      (fun x : I → ℝ => (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x) : Q[d]))
      (unitTorusUnitCellMeasure I)) := h.map_eq.symm ▸ hG.aestronglyMeasurable
  have h₂ := integral_map h.measurable.aemeasurable hGm
  rw [h.map_eq] at h₂
  exact h₁.symm.trans h₂

end
end ArtinMatthews
