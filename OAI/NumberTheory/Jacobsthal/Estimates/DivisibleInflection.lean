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
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import OAI.NumberTheory.Jacobsthal.Estimates.NestedPartials
public import OAI.NumberTheory.Jacobsthal.Harmonic.PolynomialLocalGraph
public import OAI.NumberTheory.Jacobsthal.Partitions.InflectionTransport
public import OAI.NumberTheory.Jacobsthal.Paths.AffineBranch


set_option backward.privateInPublic true
@[expose] public section

namespace OAI

namespace Erdos970

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry ErdosImplicitCurvature

noncomputable def swapVars (R : Type*) [CommSemiring R] : MV R ≃ₐ[R] MV R :=
  MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)

theorem swap_twice (R : Type*) [CommSemiring R] (Q : MV R) :
    swapVars R (swapVars R Q) = Q := by
  simpa [swapVars] using (MvPolynomial.renameEquiv R (Equiv.swap (0 : Fin 2) 1)).apply_symm_apply Q

theorem nestedX_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    nestedX R (swapVars R Q) = nestedY R Q := rfl

theorem nestedY_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    nestedY R (swapVars R Q) = nestedX R Q := by
  change nestedX R (swapVars R (swapVars R Q)) = _
  rw [swap_twice]

theorem partial_zero_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    MvPolynomial.pderiv 0 (swapVars R Q) = swapVars R (MvPolynomial.pderiv 1 Q) := by
  apply (nestedX R).injective
  rw [nestedX_partial_zero,nestedX_swap,nestedX_swap,nestedY_partial_one]

theorem partial_one_swap (R : Type*) [CommSemiring R] (Q : MV R) :
    MvPolynomial.pderiv 1 (swapVars R Q) = swapVars R (MvPolynomial.pderiv 0 Q) := by
  apply (nestedY R).injective
  rw [nestedY_partial_one,nestedY_swap,nestedY_swap,nestedX_partial_zero]

theorem eval_swap (R : Type*) [CommSemiring R] (Q : MV R) (x y : R) :
    MvPolynomial.eval ![x,y] (swapVars R Q) = MvPolynomial.eval ![y,x] Q := by
  have h1 := eval_nestedX R (swapVars R Q) x y
  rw [nestedX_swap] at h1
  exact h1.symm.trans (eval_nestedY R Q y x)

theorem peval_swap (Q : MV ℝ) (x y : ℝ) : peval (swapVars ℝ Q) x y = peval Q y x := by
  rw [peval_eq_eval_pair,peval_eq_eval_pair,eval_swap]

theorem complexify_swap (Q : MV ℝ) : complexify (swapVars ℝ Q) = swapVars ℂ (complexify Q) := by
  simp only [complexify,swapVars,MvPolynomial.renameEquiv_apply,MvPolynomial.map_rename]

theorem mixed_partials_complex (Q : MV ℂ) :
    MvPolynomial.pderiv 1 (MvPolynomial.pderiv 0 Q) =
      MvPolynomial.pderiv 0 (MvPolynomial.pderiv 1 Q) := by
  classical
  ext m
  simp [MvPolynomial.coeff_pderiv,add_assoc,add_left_comm,add_comm,mul_left_comm,mul_comm]

theorem inflection_swap (Q : MV ℂ) : inflection (swapVars ℂ Q) = swapVars ℂ (inflection Q) := by
  unfold inflection
  simp only [partial_zero_swap,partial_one_swap,mixed_partials_complex,map_add,map_mul,map_pow]
  have hC : swapVars ℂ (MvPolynomial.C (-2 : ℂ)) = MvPolynomial.C (-2 : ℂ) := by simp [swapVars]
  rw [hC]
  ring

theorem complex_divisibility_swap (Q : MV ℝ)
    (hdiv : complexify Q ∣ inflection (complexify Q)) :
    complexify (swapVars ℝ Q) ∣ inflection (complexify (swapVars ℝ Q)) := by
  rw [complexify_swap,inflection_swap]
  exact map_dvd (swapVars ℂ).toRingHom hdiv

end ErdosDivisibleInflection

end

section

namespace ErdosDivisibleInflection

open ErdosCriticalGeometry ErdosImplicitCurvature

theorem no_regular_y_point (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hdiv : complexify Q ∣ inflection (complexify Q))
    (x y : ℝ) (hzero : peval Q x y = 0) (hy : peval (partialY Q) x y ≠ 0) : False := by
  obtain ⟨a,b,f,hax,hxb,hfx,hf,hcurve,hfy⟩ := exists_local_real_graph Q x y hzero hy
  have hsecond := zero_second_derivative_on_divisible_graph Q f a b hdiv hf hcurve hfy
  obtain ⟨A,B,haffine⟩ := affine_of_second_derivative_zero f a b x ⟨hax,hxb⟩ hf hsecond
  have hdegC : 1 < (complexify Q).totalDegree := by rwa [complexify_totalDegree]
  apply no_affine_interval (complexify Q) hQ hdegC (A : ℂ) (B : ℂ) a b (hax.trans hxb)
  intro t ht
  have hz := hcurve t ht
  rw [haffine t ht] at hz
  have hc := complexify_eval Q t (A*t+B)
  rw [← peval_eq_eval_pair,hz] at hc
  simpa only [Complex.ofReal_mul,Complex.ofReal_add,Complex.ofReal_zero] using hc

theorem no_regular_x_point (Q : MV ℝ) (hQ : Irreducible (complexify Q))
    (hdeg : 1 < Q.totalDegree) (hdiv : complexify Q ∣ inflection (complexify Q))
    (x y : ℝ) (hzero : peval Q x y = 0) (hx : peval (partialX Q) x y ≠ 0) : False := by
  have hirr : Irreducible (complexify (swapVars ℝ Q)) := by
    rw [complexify_swap]
    exact (MulEquiv.irreducible_iff (swapVars ℂ).toMulEquiv).mpr hQ
  have hd : 1 < (swapVars ℝ Q).totalDegree := by
    simpa only [swapVars,MvPolynomial.totalDegree_renameEquiv] using hdeg
  have hz : peval (swapVars ℝ Q) y x = 0 := by rw [peval_swap]; exact hzero
  have hpart : peval (partialY (swapVars ℝ Q)) y x ≠ 0 := by
    change peval (MvPolynomial.pderiv 1 (swapVars ℝ Q)) y x ≠ 0
    rw [partial_one_swap,peval_swap]
    exact hx
  exact no_regular_y_point (swapVars ℝ Q) hirr hd (complex_divisibility_swap Q hdiv) y x hz hpart

theorem no_real_regular_point_of_divisible_inflection (Q : MV ℝ)
    (hQ : Irreducible (complexify Q)) (hdeg : 1 < Q.totalDegree)
    (hdiv : complexify Q ∣ inflection (complexify Q)) (x y : ℝ)
    (hzero : peval Q x y = 0)
    (hregular : peval (partialX Q) x y ≠ 0 ∨ peval (partialY Q) x y ≠ 0) : False := by
  rcases hregular with hx | hy
  · exact no_regular_x_point Q hQ hdeg hdiv x y hzero hx
  · exact no_regular_y_point Q hQ hdeg hdiv x y hzero hy

theorem divisible_inflection_gradient_zero (Q : MV ℝ)
    (hQ : Irreducible (complexify Q)) (hdeg : 1 < Q.totalDegree)
    (hdiv : complexify Q ∣ inflection (complexify Q)) (x y : ℝ)
    (hzero : peval Q x y = 0) :
    peval (partialX Q) x y = 0 ∧ peval (partialY Q) x y = 0 := by
  constructor
  · by_contra hx
    exact no_regular_x_point Q hQ hdeg hdiv x y hzero hx
  · by_contra hy
    exact no_regular_y_point Q hQ hdeg hdiv x y hzero hy

theorem real_divisible_inflection_gradient_zero (Q : MV ℝ)
    (hQ : Irreducible (complexify Q)) (hdeg : 1 < Q.totalDegree)
    (hdiv : Q ∣ inflectionPolynomial Q) (x y : ℝ) (hzero : peval Q x y = 0) :
    peval (partialX Q) x y = 0 ∧ peval (partialY Q) x y = 0 :=
  divisible_inflection_gradient_zero Q hQ hdeg (real_divisibility_to_complex Q hdiv) x y hzero

end ErdosDivisibleInflection

end

end Erdos970

end OAI
