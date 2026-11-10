module

public import ArtinMatthews.SourceKPCuspTraceDualFrequency
public import ArtinMatthews.SourceKPCuspPrincipalFrequency
public import ArtinMatthews.SourceKPCuspTraceFrequency
public import ArtinMatthews.SourceKPCuspTraceModePhase
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

/-! Every integer mode on the actual principal cusp torus is the standard
adelic character of its unique trace-dual field frequency. -/
namespace ArtinMatthews
open NumberField Module Module.Free StandardAdelic
open scoped NumberField AdeleRing nonZeroDivisors Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K]
local notation "I" => ChooseBasisIndex ℤ (𝓞 K)
local notation "D[" d "]" => FractionalIdeal.dual ℤ ℚ
  ((Ideal.span ({d} : Set (𝓞 K)) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)
local notation "Q[" d "]" => SourceKPCuspPrincipalQuotient K d

theorem sourceKPCuspTraceDualFrequency_period_iff (d : 𝓞 K) (hd : d ≠ 0) (m : K) :
    (∀ z ∈ sourceKPCuspPrincipalPeriods K d, character K (algebraMap K 𝔸[K] m * z) = 1) ↔
      m ∈ D[d] := by
  constructor
  · intro h
    apply (sourceKPCuspTraceDual_iff_integralTrace K d hd m).mpr
    intro a
    let q : K := (d:K) * (a:K)
    let t := algebraMap K 𝔸ᶠ[K] q
    have ht : t ∈ sourceKPCuspFiniteIdeal K d :=
      (sourceKPCuspFiniteIdeal_rational K d hd q).mpr ⟨a,rfl⟩
    have hz : sourceKPFiniteAddEmbedding K t ∈ sourceKPCuspPrincipalPeriods K d :=
      AddSubgroup.mem_sup_right ⟨t,ht,rfl⟩
    have hchar := h _ hz
    rw [show algebraMap K 𝔸[K] m * sourceKPFiniteAddEmbedding K t =
      ((0,algebraMap K 𝔸ᶠ[K] m * t) : 𝔸[K]) from Prod.ext (mul_zero _) rfl,
      character_finite] at hchar
    change finiteCharacter K (algebraMap K 𝔸ᶠ[K] m * algebraMap K 𝔸ᶠ[K] q) = 1 at hchar
    rw [← map_mul, finiteCharacter_rational, inv_eq_one] at hchar
    change archCharacter K (algebraMap K (InfiniteAdeleRing K) (m*q)) = 1 at hchar
    rw [archCharacter_rational, Complex.exp_eq_one_iff] at hchar
    obtain ⟨n,hn⟩ := hchar
    have h2πi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero
    have he : (Algebra.trace ℚ K (m*q) : ℂ) = (n : ℂ) := mul_right_cancel₀ h2πi hn
    exact ⟨n,by exact_mod_cast he⟩
  · intro hm z hz
    exact sourceKPCuspTraceDualFrequency_period K d hd m hm hz

def sourceKPCuspTraceDualIndexEquiv (d : 𝓞 K) (hd : d ≠ 0) :
    (I → ℤ) ≃ {m : K // m ∈ D[d]} := by
  let f : (I → ℤ) → {m : K // m ∈ D[d]} :=
    fun n => ⟨sourceKPCuspTraceFrequency K d n,sourceKPCuspTraceFrequency_mem_dual K d n⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro n k h
    have hval : sourceKPCuspTraceFrequency K d n = sourceKPCuspTraceFrequency K d k :=
      congrArg Subtype.val h
    funext i
    have hn := sourceKPCuspTraceFrequency_pair K d hd n i
    rw [hval,sourceKPCuspTraceFrequency_pair K d hd k i] at hn
    exact_mod_cast hn.symm
  · intro m
    have hm := (sourceKPCuspTraceDual_iff_integralTrace K d hd m.val).mp m.prop
    have hi (i : I) : ∃ n : ℤ,
        Algebra.trace ℚ K (m.val * ((d:K) * integralBasis K i)) = (n:ℚ) := by
      rw [integralBasis_apply]
      exact hm (Module.Free.chooseBasis ℤ (𝓞 K) i)
    choose n hn using hi
    refine ⟨n,Subtype.ext ?_⟩
    change sourceKPCuspTraceFrequency K d n = m.val
    apply mul_right_cancel₀ (sourceKPCuspInteger_ne_zero K d hd)
    apply (integralBasis K).traceDual.repr.injective
    ext i
    rw [Module.Basis.traceDual_repr_apply, Module.Basis.traceDual_repr_apply]
    change Algebra.trace ℚ K ((sourceKPCuspTraceFrequency K d n * (d:K))*integralBasis K i) =
      Algebra.trace ℚ K ((m.val*(d:K))*integralBasis K i)
    rw [mul_assoc (sourceKPCuspTraceFrequency K d n),mul_assoc m.val,hn i]
    exact_mod_cast sourceKPCuspTraceFrequency_pair K d hd n i

theorem sourceKPCuspTraceDualIndexEquiv_val (d : 𝓞 K) (hd : d ≠ 0) (n : I → ℤ) :
    (sourceKPCuspTraceDualIndexEquiv K d hd n).val = sourceKPCuspTraceFrequency K d n := rfl

theorem sourceKPCuspTraceDualFrequency_eq_mFourier (d : 𝓞 K) (hd : d ≠ 0)
    (n : I → ℤ) (q : Q[d]) :
    sourceKPCuspTraceDualFrequency K d hd (sourceKPCuspTraceFrequency K d n)
        (sourceKPCuspTraceFrequency_mem_dual K d n) q =
      UnitAddTorus.mFourier n (sourceKPCuspPrincipalTorusHomeomorph K d hd q) := by
  obtain ⟨z,rfl⟩ := sourceKPCuspArchQuotientMap_surjective K d hd q
  let x := sourceKPCuspCoordinates K d hd z
  have hx : (QuotientAddGroup.mk (sourceKPCuspUnitCellAdelicPoint K d hd x) : Q[d]) =
      sourceKPCuspArchQuotientMap K d z := by
    unfold sourceKPCuspUnitCellAdelicPoint
    dsimp only [x]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    rfl
  rw [← hx, sourceKPCuspTraceDualFrequency_mk, sourceKPCuspUnitCellAdelicPoint_torus]
  exact sourceKPCuspTraceFrequency_unitCell_phase K d hd n x

theorem sourceKPCuspTraceDualFrequency_eq_integralFrequency (d : 𝓞 K) (hd : d ≠ 0)
    (m : K) (hm : m ∈ D[d]) (hi : ∃ r : 𝓞 K, m*(d:K) = (r:K)) :
    sourceKPCuspTraceDualFrequency K d hd m hm = sourceKPCuspPrincipalFrequency K d m hi := by
  funext q
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective q
  rfl

end
end ArtinMatthews
