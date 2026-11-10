module

public import ArtinMatthews.StandardAdelicCharacter
public import ArtinMatthews.ProbeCRTAdditiveComponents
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The finite additive product formula for the constructed standard
adelic character. The S-place contribution is retained explicitly. -/
namespace ArtinMatthews.StandardAdelic

open NumberField IsDedekindDomain
open OAI.RepresentationTheory.Weil.AdelicSplitting
open scoped NumberField BigOperators Classical
noncomputable section
variable (K : Type) [Field K] [NumberField K]

def finitePartial (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ArchimedeanAdeles.Construction.FiniteAdeles K) : ArchimedeanAdeles.Construction.FiniteAdeles K :=
  ∑ v ∈ S, RestrictedProduct.single (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K) v (a v)

theorem finitePartial_apply (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ArchimedeanAdeles.Construction.FiniteAdeles K) (w : HeightOneSpectrum (𝓞 K)) :
    finitePartial K S a w = if w ∈ S then a w else 0 := by
  have he : finitePartial K S a w = ∑ v ∈ S,
      RestrictedProduct.single (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K) v (a v) w := by
    exact map_sum (RestrictedProduct.evalRingHom (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletion K) w) _ _
  rw [he]
  by_cases hw : w ∈ S
  · rw [ite_eq_left hw, Finset.sum_eq_single w]
    · exact RestrictedProduct.single_eq_same _ _ _
    · intro v _ hv
      exact RestrictedProduct.single_eq_of_ne _ _ (Ne.symm hv)
    · exact fun h => (h hw).elim
  · rw [ite_eq_right hw]
    apply Finset.sum_eq_zero
    intro v hv
    apply RestrictedProduct.single_eq_of_ne
    intro he
    exact hw (he ▸ hv)

theorem finitePartial_remainder_integral (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ArchimedeanAdeles.Construction.FiniteAdeles K)
    (ha : ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers K) :
    a - finitePartial K S a ∈ IntegralAdeles.Construction.finiteIntegralRing K := by
  intro w
  change a w - finitePartial K S a w ∈ w.adicCompletionIntegers K
  rw [finitePartial_apply]
  by_cases hw : w ∈ S
  · rw [ite_eq_left hw, sub_self]
    exact (w.adicCompletionIntegers K).zero_mem
  · rw [ite_eq_right hw, sub_zero]
    exact ha w hw

theorem finiteCharacter_prod (S : Finset (HeightOneSpectrum (𝓞 K)))
    (a : ArchimedeanAdeles.Construction.FiniteAdeles K)
    (ha : ∀ v, v ∉ S → a v ∈ v.adicCompletionIntegers K) :
    finiteCharacter K a = ∏ v ∈ S, localFiniteCharacter K v (a v) := by
  have h := finiteCharacter_integral K (a-finitePartial K S a) (finitePartial_remainder_integral K S a ha)
  rw [AddChar.map_sub_eq_div] at h
  have he := (div_eq_one_iff_eq (AddChar.val_isUnit (finiteCharacter K) (finitePartial K S a)).ne_zero).mp h
  calc
    finiteCharacter K a = finiteCharacter K (finitePartial K S a) := he
    _ = ∏ v ∈ S, finiteCharacter K
        (RestrictedProduct.single (fun p : HeightOneSpectrum (𝓞 K) => p.adicCompletionIntegers K) v (a v)) :=
      VaryingKummerAnalytic.probeAddChar_sum (finiteCharacter K) S _
    _ = _ := Finset.prod_congr rfl (fun v _ => (localFiniteCharacter_single K v (a v)).symm)

def rationalSupport (q : K) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (Filter.eventually_cofinite.mp
    (algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) q).property).toFinset

theorem mem_rationalSupport (q : K) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ rationalSupport K q ↔ algebraMap K (v.adicCompletion K) q ∉ v.adicCompletionIntegers K :=
  Set.Finite.mem_toFinset _

def sCharacter (S : Finset (HeightOneSpectrum (𝓞 K))) : AddChar K ℂ where
  toFun q := rationalCharacter K q * ∏ v ∈ S, localFiniteCharacter K v (algebraMap K (v.adicCompletion K) q)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    simp only [map_add, AddChar.map_add_eq_mul, Finset.prod_mul_distrib]
    ring

theorem sCharacter_exterior_product (S : Finset (HeightOneSpectrum (𝓞 K))) (q : K) :
    sCharacter K S q = ∏ v ∈ rationalSupport K q \ S,
      localFiniteCharacter K v (-(algebraMap K (v.adicCompletion K) q)) := by
  let T := S ∪ (rationalSupport K q \ S)
  have hT : ∀ v, v ∉ T → algebraMap K (v.adicCompletion K) q ∈ v.adicCompletionIntegers K := by
    intro v hv
    have hs : v ∉ rationalSupport K q := by
      intro h
      apply hv
      by_cases hS : v ∈ S
      · exact Finset.mem_union_left _ hS
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,hS⟩)
    simpa only [mem_rationalSupport, not_not] using hs
  have hp := finiteCharacter_prod K T (algebraMap K (ArchimedeanAdeles.Construction.FiniteAdeles K) q) hT
  rw [finiteCharacter_rational] at hp
  have hd : Disjoint S (rationalSupport K q \ S) :=
    Finset.disjoint_left.mpr (fun _ hS hD => (Finset.mem_sdiff.mp hD).2 hS)
  rw [show T = S ∪ (rationalSupport K q \ S) from rfl, Finset.prod_union hd] at hp
  change (rationalCharacter K q)⁻¹ =
    (∏ v ∈ S, localFiniteCharacter K v (algebraMap K (v.adicCompletion K) q)) *
      (∏ v ∈ rationalSupport K q \ S, localFiniteCharacter K v (algebraMap K (v.adicCompletion K) q)) at hp
  let C := ∏ v ∈ rationalSupport K q \ S, localFiniteCharacter K v (algebraMap K (v.adicCompletion K) q)
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ =>
    (AddChar.val_isUnit (localFiniteCharacter K v) _).ne_zero)
  have hmul : sCharacter K S q * C = 1 := by
    change (rationalCharacter K q * _) * C = 1
    rw [mul_assoc, ← hp]
    exact mul_inv_cancel₀ (AddChar.val_isUnit (rationalCharacter K) q).ne_zero
  have he := congrArg (fun z : ℂ => z*C⁻¹) hmul
  have he' : sCharacter K S q = C⁻¹ := by
    simpa only [mul_assoc, mul_inv_cancel₀ hC, mul_one, one_mul] using he
  rw [he']
  simp only [C, AddChar.map_neg_eq_inv, Finset.prod_inv_distrib]

end
end ArtinMatthews.StandardAdelic
