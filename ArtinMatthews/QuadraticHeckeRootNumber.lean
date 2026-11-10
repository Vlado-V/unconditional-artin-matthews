module

public import ArtinMatthews.QuadraticHeckeFieldNormalization
public import ArtinMatthews.VaryingKummerAnalyticRayIdealInverseNonprincipal
public import ArtinMatthews.VaryingKummerAnalyticRayIdealPrimitiveContinuation
public import ArtinMatthews.QuadraticHeckePrimitiveReflection
public import ArtinMatthews.QuadraticHeckeRootNumberSign
public import ArtinMatthews.VaryingKummerAnalyticMixedZetaContinuation
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

namespace ArtinMatthews
open NumberField Complex Set Filter VaryingKummerAnalytic OAI.SevenEighths.FiniteFourier
open scoped NumberField Classical Topology
noncomputable section

variable (K L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L]
local notation "r" => InfinitePlace.nrComplexPlaces K

private theorem complex_phase_eq_one_of_positive {W : ℂ} (hW : ‖W‖ = 1) {x y : ℝ}
    (hx : 0 < x) (hy : 0 < y) (he : (x : ℂ) = W * (y : ℂ)) : W = 1 := by
  have hy₀ : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  have hw : W = ((x / y : ℝ) : ℂ) := by
    rw [Complex.ofReal_div]
    exact (eq_div_iff hy₀).mpr he.symm
  rw [hw, Complex.norm_real, Real.norm_of_nonneg (div_nonneg hx.le hy.le)] at hW
  exact hw.trans (by rw [hW, Complex.ofReal_one])

private theorem quadraticHeckeDualGamma_real_pos (A : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    ∃ x : ℝ, 0 < x ∧ quadraticHeckeDualGamma A k (t : ℂ) = (x : ℂ) := by
  refine ⟨Real.exp ((2 * t - 1) * Real.log A) * (Real.Gamma t / Real.Gamma (1 - t)) ^ k,
    mul_pos (Real.exp_pos _) (pow_pos (div_pos (Real.Gamma_pos_of_pos ht)
      (Real.Gamma_pos_of_pos (sub_pos.mpr ht₁))) _), ?_⟩
  rw [quadraticHeckeDualGamma, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal]
  push_cast
  rfl

omit [IsTotallyComplex K] in
private theorem primitive_quotient_continuation {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hprim : IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal)
    (hEuler : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s = NumberField.dedekindZeta K s * ψ.dirichlet s)
    {s : ℂ} (hs : 0 < s.re) :
    mixedRegularizedDedekindZeta L s = mixedRegularizedDedekindZeta K s * ψ.primitiveContinued hM hprim s := by
  let U : Set ℂ := {s | 0 < s.re}
  have hU : IsOpen U := Complex.isOpen_re_gt 0
  have hZ (E : Type) [Field E] [NumberField E] :
      AnalyticOnNhd ℂ (mixedRegularizedDedekindZeta E) U := by
    intro z hz
    exact mixedRegularizedDedekindZeta_analyticAt E (by intro h; simp [U, h] at hz)
  have hA := (hZ K).mul ((ψ.primitiveContinued_entire hM hprim).differentiableOn.analyticOnNhd hU)
  have hpre : IsPreconnected U :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have heq : mixedRegularizedDedekindZeta L =ᶠ[𝓝 (2 : ℂ)]
      (fun z => mixedRegularizedDedekindZeta K z * ψ.primitiveContinued hM hprim z) := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num :
      (2 : ℂ) ∈ {z : ℂ | 1 < z.re}))] with z hz
    rw [mixedRegularizedDedekindZeta_eq L hz, mixedRegularizedDedekindZeta_eq K hz,
      hEuler z hz, ψ.primitiveContinued_eq_dirichlet hM hprim hnp hz, mul_assoc]
  exact (hZ L).eqOn_of_preconnected_of_eventuallyEq hA hpre (by norm_num [U]) heq hs

omit [IsTotallyComplex K] in
private theorem primitive_value_positive_of_zeta_quotient {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hprim : IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal)
    (hEuler : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s = NumberField.dedekindZeta K s * ψ.dirichlet s)
    {t : ℝ} (ht : 0 < t)
    (hK : ∃ z : ℝ, 0 < z ∧ mixedRegularizedDedekindZeta K t = (z : ℂ))
    (hL : ∃ z : ℝ, 0 < z ∧ mixedRegularizedDedekindZeta L t = (z : ℂ)) :
    ∃ v : ℝ, 0 < v ∧ ψ.primitiveContinued hM hprim (t : ℂ) = (v : ℂ) := by
  obtain ⟨x, hx, hX⟩ := hK
  obtain ⟨y, hy, hY⟩ := hL
  have h := primitive_quotient_continuation K L ψ hM hprim hnp hEuler (s := t) (by simpa using ht)
  rw [hX, hY] at h
  refine ⟨y / x, div_pos hy hx, ?_⟩
  rw [Complex.ofReal_div]
  exact (eq_div_iff (Complex.ofReal_ne_zero.mpr hx.ne')).mpr (by rw [mul_comm]; exact h.symm)

/-- For a self-dual primitive factor with the actual quadratic zeta
factorization, positivity at the two real endpoints forces root number one. -/
theorem quadraticHeckePrimitiveReflection_one_of_zeta_quotient {M : Ideal (𝓞 K)}
    (ψ : EvenIdealRayCharacter K M) (hM : M ≠ ⊥) (hprim : IsPrimitiveOnIdeals ψ.residue)
    (hnp : ψ.IsNonprincipal)
    (hself : ∀ s, ψ.inverse.primitiveContinued hM (ψ.inverse_isPrimitive hM hprim) s =
      ψ.primitiveContinued hM hprim s)
    (hEuler : ∀ s : ℂ, 1 < s.re →
      NumberField.dedekindZeta L s = NumberField.dedekindZeta K s * ψ.dirichlet s) :
    ∀ s : ℂ, 0 < s.re →
      ψ.primitiveContinued hM hprim (1 - s) =
        (Ideal.absNorm M : ℂ) ^ (s - 1 / 2) *
          quadraticHeckeDualGamma (quadraticHeckeFieldScale K) r s *
            ψ.primitiveContinued hM hprim s := by
  obtain ⟨W, hW, hfe⟩ := quadraticHeckePrimitiveReflection K ψ hM hprim hnp
  have hzero : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  have hone : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < 1 := by
    have h : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), t < 1 := Iio_mem_nhds (by norm_num)
    exact h.filter_mono inf_le_left
  obtain ⟨t, ht, ht₁, hK, hL⟩ :=
    (hzero.and (hone.and ((mixedRegularizedDedekindZeta_positive_near_zero_and_one K).and
      (mixedRegularizedDedekindZeta_positive_near_zero_and_one L)))).exists
  obtain ⟨v, hv, hV⟩ := primitive_value_positive_of_zeta_quotient K L ψ hM hprim hnp hEuler ht hK.1 hL.1
  obtain ⟨u, hu, hU⟩ := primitive_value_positive_of_zeta_quotient K L ψ hM hprim hnp hEuler
    (sub_pos.mpr ht₁) hK.2 hL.2
  obtain ⟨g, hg, hG⟩ := quadraticHeckeDualGamma_real_pos (quadraticHeckeFieldScale K) r ht ht₁
  let q : ℝ := Ideal.absNorm M
  have hq : 0 < q := by
    change 0 < (Ideal.absNorm M : ℝ)
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hM)
  have hqp : 0 < q ^ (t - 1 / 2) := Real.rpow_pos_of_pos hq _
  have hcp : (Ideal.absNorm M : ℂ) ^ ((t : ℂ) - 1 / 2) =
      ((q ^ (t - 1 / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hq.le]
    push_cast
    rfl
  have he := hfe (t : ℂ) (by simpa using ht)
  rw [hself, hV, hG, hcp, ← Complex.ofReal_one, ← Complex.ofReal_sub, hU] at he
  have he' : (u : ℂ) = W * ((q ^ (t - 1 / 2) * g * v : ℝ) : ℂ) := by
    push_cast
    exact he.trans (by ring)
  have hW₁ : W = 1 := complex_phase_eq_one_of_positive hW hu (mul_pos (mul_pos hqp hg) hv) he'
  intro s hs
  simpa only [hW₁, one_mul, hself] using hfe s hs

end
end ArtinMatthews
