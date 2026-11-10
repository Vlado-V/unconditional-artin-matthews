module

/- Adapted in the Artin–Matthews source bundle. The source, upstream and packaged digests are recorded in SOURCE_MANIFEST.json. -/

public import OAI.NumberTheory.Jacobsthal.Estimates.RealCriticalPoints
public import OAI.NumberTheory.Jacobsthal.Estimates.RegularImplicitArc
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

open ErdosImplicitCurvature ErdosCriticalGeometry

theorem peval_eq_eval_pair (Q : MV ℝ) (x y : ℝ) :
    peval Q x y = MvPolynomial.eval ![x,y] Q := by
  have h : (fun i : Fin 2 => if i = 0 then x else y) = ![x,y] := by
    funext i
    fin_cases i <;> simp
  simp only [peval,h]

theorem complexify_inflection (Q : MV ℝ) :
    complexify (inflectionPolynomial Q) = inflection (complexify Q) := by
  unfold inflectionPolynomial partialX partialY inflection
  simp only [complexify, map_add, map_sub, map_mul, map_pow, map_ofNat,
    ← MvPolynomial.pderiv_map, map_neg]
  ring

theorem inflection_zero_of_complex_divisibility (Q : MV ℝ)
    (hdiv : complexify Q ∣ inflection (complexify Q)) (x y : ℝ)
    (hQ : peval Q x y = 0) : peval (inflectionPolynomial Q) x y = 0 := by
  have hQC : MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (complexify Q) = 0 := by
    rw [complexify_eval, ← peval_eq_eval_pair, hQ]
    simp
  obtain ⟨H,hH⟩ := hdiv
  have hIC : MvPolynomial.eval ![(x : ℂ),(y : ℂ)] (inflection (complexify Q)) = 0 := by
    rw [hH, map_mul, hQC, zero_mul]
  rw [← complexify_inflection, complexify_eval, Complex.ofReal_eq_zero] at hIC
  rwa [peval_eq_eval_pair]

theorem real_divisibility_to_complex (Q : MV ℝ) (hdiv : Q ∣ inflectionPolynomial Q) :
    complexify Q ∣ inflection (complexify Q) := by
  rw [← complexify_inflection]
  exact map_dvd (MvPolynomial.map (algebraMap ℝ ℂ)) hdiv

theorem zero_second_derivative_on_divisible_graph (Q : MV ℝ) (f : ℝ → ℝ) (a b : ℝ)
    (hdiv : complexify Q ∣ inflection (complexify Q))
    (hf : ContDiffOn ℝ 2 f (Set.Ioo a b))
    (hcurve : ∀ t ∈ Set.Ioo a b, peval Q t (f t) = 0)
    (hQy : ∀ t ∈ Set.Ioo a b, peval (partialY Q) t (f t) ≠ 0) :
    ∀ t ∈ Set.Ioo a b, deriv (deriv f) t = 0 := by
  intro t ht
  apply (curvature_zero_iff Q f isOpen_Ioo hf hcurve ht (hQy t ht)).mpr
  exact inflection_zero_of_complex_divisibility Q hdiv t (f t) (hcurve t ht)

end ErdosDivisibleInflection

end

end Erdos970

end OAI
