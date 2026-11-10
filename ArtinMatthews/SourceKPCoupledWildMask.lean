module

public import ArtinMatthews.SourceIntertwinerArchFinite
public import ArtinMatthews.SourceKPCoupledLocalProduct
public import ArtinMatthews.SourceKPDeepIdealHaar
public import ArtinMatthews.SourceKPExteriorUpperCompatibility
public import ArtinMatthews.SourceKPWildCompactSupport
public import ArtinMatthews.SourceFinitePlaceSplit
public import ArtinMatthews.SourceKPCoupledWildFiber
public import ArtinMatthews.SourceKPCoupledWildLower
public import ArtinMatthews.SourceKPProjectiveBruhatCells
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! All wild coordinates can be removed together from the literal
kernel. Each removal contributes the indicator of its actual deep ideal. -/

namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup
open scoped NumberField AdeleRing MatrixGroups BigOperators Classical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

def sourceKPCoupledZeroPlaces (T : Finset (HeightOneSpectrum (𝓞 K))) (x : 𝔸ᶠ[K]) : 𝔸ᶠ[K] :=
  x - ∑ P ∈ T, sourceKPFiniteAdditiveSingle K P (x P)

theorem sourceKPCoupledZeroPlaces_at (T : Finset (HeightOneSpectrum (𝓞 K))) (x : 𝔸ᶠ[K])
    (P : HeightOneSpectrum (𝓞 K)) : sourceKPCoupledZeroPlaces K T x P = if P ∈ T then 0 else x P := by
  let ev := sourceKPAdeleEval K P
  change ev (x - ∑ Q ∈ T, sourceKPFiniteAdditiveSingle K Q (x Q)) = _
  rw [map_sub, map_sum]
  by_cases hP : P ∈ T
  · rw [ite_eq_left hP, Finset.sum_eq_single P]
    · change x P - sourceKPFiniteAdditiveSingle K P (x P) P = 0
      rw [sourceKPFiniteAdditiveSingle_same, sub_self]
    · intro Q _ hQP
      exact sourceKPFiniteAdditiveSingle_other K Q (x Q) P hQP.symm
    · exact fun h => (h hP).elim
  · have hsum : (∑ Q ∈ T, ev (sourceKPFiniteAdditiveSingle K Q (x Q))) = 0 := by
      apply Finset.sum_eq_zero
      intro Q hQ
      exact sourceKPFiniteAdditiveSingle_other K Q (x Q) P (fun h => hP (h ▸ hQ))
    rw [ite_eq_right hP, hsum, sub_zero]
    rfl

theorem sourceKPCoupledZeroPlaces_insert (T : Finset (HeightOneSpectrum (𝓞 K)))
    (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ T) (x : 𝔸ᶠ[K]) :
    sourceKPCoupledZeroPlaces K (insert P T) x =
      sourceKPCoupledZeroPlaces K {P} (sourceKPCoupledZeroPlaces K T x) := by
  have hx := sourceKPCoupledZeroPlaces_at K T x P
  rw [ite_eq_right hP] at hx
  simp only [sourceKPCoupledZeroPlaces, Finset.sum_insert hP, Finset.sum_singleton] at hx ⊢
  rw [hx]
  abel

theorem sourceKPCoupledLowerAt_zero (P : HeightOneSpectrum (𝓞 K)) :
    sourceKPAdelicLowerAt K hζ P 0 = 1 := by
  have h : (sourceGL2Lower (0 : P.adicCompletion K)) = 1 := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [sourceGL2Lower]
  unfold sourceKPAdelicLowerAt
  rw [h, sourceFiniteKP2ProjectiveLift_one, map_one]

theorem sourceKPCoupledWildKernel_erase (P : HeightOneSpectrum (𝓞 K))
    (hP : (6 : 𝓞 K) ∈ P.asIdeal) (s : ℂ) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteIntertwiningKernel K hζ s (sourceKPCoupledWildWeyl K hζ).2 x =
      sourceKPDeepIdealIndicator K P (x P) *
        sourceKPFiniteIntertwiningKernel K hζ s (sourceKPCoupledWildWeyl K hζ).2
          (sourceKPCoupledZeroPlaces K {P} x) := by
  let f := sourceKPFiniteIntertwiningKernel K hζ s (sourceKPCoupledWildWeyl K hζ).2
  let r := sourceKPCoupledZeroPlaces K {P} x
  have hr : r P = 0 := by
    unfold r
    rw [sourceKPCoupledZeroPlaces_at, ite_eq_left (Finset.mem_singleton_self P)]
  have hrx : sourceKPFiniteAdditiveSingle K P (x P)+r = x := by
    simp only [r, sourceKPCoupledZeroPlaces, Finset.sum_singleton]
    abel
  let R := sourceKPCoupledWildFiberRest K hζ P r
  have hR := sourceKPCoupledWildFiberRest_base K hζ P hP r hr
  have hz := sourceKPCoupledWildFiber_kernel K hζ P hP s r hr (0 : P.adicCompletion K)
  have hsingle : sourceKPFiniteAdditiveSingle K P (0 : P.adicCompletion K) = 0 := by
    apply add_left_cancel (a := sourceKPFiniteAdditiveSingle K P (0 : P.adicCompletion K))
    simpa only [add_zero] using (sourceKPFiniteAdditiveSingle_add K P 0 0).symm
  rw [hsingle, zero_add, sourceKPCoupledLowerAt_zero K hζ P, one_mul] at hz
  change f r = sourceKPAdelicCompactScalar K hζ s R at hz
  have h := sourceKPCoupledWildFiber_kernel K hζ P hP s r hr (x P)
  rw [hrx, sourceKPCoupledWildLower_indicator K hζ P hP s R hR, ← hz] at h
  refine h.trans ?_
  unfold sourceKPDeepIdealIndicator
  by_cases hx : x P ∈ sourceKPDeepIdealImage K P
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

theorem sourceKPCoupledWildKernel_mask (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : T ⊆ sixthWildPrimes K) (s : ℂ) (x : 𝔸ᶠ[K]) :
    sourceKPFiniteIntertwiningKernel K hζ s (sourceKPCoupledWildWeyl K hζ).2 x =
      (∏ P ∈ T, sourceKPDeepIdealIndicator K P (x P)) *
        sourceKPFiniteIntertwiningKernel K hζ s (sourceKPCoupledWildWeyl K hζ).2
          (sourceKPCoupledZeroPlaces K T x) := by
  let f := sourceKPFiniteIntertwiningKernel K hζ s (sourceKPCoupledWildWeyl K hζ).2
  change f x = (∏ P ∈ T, sourceKPDeepIdealIndicator K P (x P)) * f (sourceKPCoupledZeroPlaces K T x)
  induction T using Finset.induction_on with
  | empty => simp [sourceKPCoupledZeroPlaces]
  | insert P T hP ih =>
    have hP₆ := (mem_sixthWildPrimes P).mp (hT (Finset.mem_insert_self P T))
    have hT' : T ⊆ sixthWildPrimes K := fun Q hQ => hT (Finset.mem_insert_of_mem hQ)
    have h := sourceKPCoupledWildKernel_erase K hζ P hP₆ s (sourceKPCoupledZeroPlaces K T x)
    rw [sourceKPCoupledZeroPlaces_at K T x P, ite_eq_right hP,
      ← sourceKPCoupledZeroPlaces_insert K T P hP x] at h
    change f (sourceKPCoupledZeroPlaces K T x) = _ at h
    rw [ih hT', h, Finset.prod_insert hP]
    ring

end
end ArtinMatthews
