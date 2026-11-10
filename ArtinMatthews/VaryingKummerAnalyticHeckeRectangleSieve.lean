module

public import ArtinMatthews.VaryingKummerAnalyticHeckeGaussianDetector
public import ArtinMatthews.VaryingKummerAnalyticHeckeRectangleDerivatives
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
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
public import OAI.NumberTheory.DirichletL.Hecke.DetectorRowwiseChain


set_option backward.privateInPublic true
@[expose] public section

/-! The actual conductor sieve at different real parts and heights for
each member of a finite coefficient family. The only analytic helper is
the pinned, geometry-independent two-variable derivative estimate. -/
namespace ArtinMatthews.VaryingKummerAnalytic
open NumberField FractionalIdeal Complex Set
open OAI.SevenEighths.FiniteFourier
open scoped NumberField nonZeroDivisors Classical BigOperators
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem actualHecke_coefficientFamily_rowwise_rectangle
    {U X σ₀ σ₁ Y : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X) (hσ : σ₀ ≤ σ₁) (hY : 0 ≤ Y)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (S : Finset (Σ _M : IdealConductorModulus K, integralFractionalIdeals K → ℂ))
    (hS : S ⊆ T.sigma (fun M => (A M).image (fun ψ => ψ.coefficient)))
    (σ t : (Σ _M : IdealConductorModulus K, integralFractionalIdeals K → ℂ) → ℝ)
    (hσS : ∀ i ∈ S, σ i ∈ Icc σ₀ σ₁) (htS : ∀ i ∈ S, |t i| ≤ Y) :
    (∑ i ∈ S, ‖coefficientClassDirichletPolynomial K i.2 B v (σ i) (t i)‖^2) ≤
      (1+2*(σ₁-σ₀))*((1+4*Y)*
        (((NumberField.classNumber K : ℝ)*heckeConductorClassConstant K*(X+U^2))*
          ((1+(Real.log X)^2)^2*coefficientClassDirichletMass K B v σ₀))) := by
  let M (n : ℕ) (i : Σ _M : IdealConductorModulus K, integralFractionalIdeals K → ℂ)
      (x y : ℝ) :=
    coefficientClassDirichletPolynomial K i.2 B ((coefficientClassRealLogWeight K)^[n] v) x (-y)
  have cm (n : ℕ) (i) (_hn : n ≤ 2) : Continuous (Function.uncurry (M n i)) := by
    convert
      (coefficientClassDirichletPolynomial_joint_continuous K i.2 B
        ((coefficientClassRealLogWeight K)^[n] v)).comp
          (continuous_fst.prodMk continuous_snd.neg) using 1
    ext p
    rfl
  have dx (n : ℕ) (i) (x y : ℝ) (_hn : n ≤ 1) :
      HasDerivAt (fun u => M n i u y) (-M (n+1) i x y) x := by
    simpa only [M,Function.iterate_succ_apply'] using
      coefficientClassDirichletPolynomial_sigma_hasDerivAt K i.2 B
        ((coefficientClassRealLogWeight K)^[n] v) x (-y)
  have dy (n : ℕ) (i) (x y : ℝ) (_hn : n ≤ 1) :
      HasDerivAt (M n i x) (I*M (n+1) i x y) y := by
    simpa only [M,Function.iterate_succ_apply'] using
      coefficientClassDirichletPolynomial_reflected_hasDerivAt K i.2 B
        ((coefficientClassRealLogWeight K)^[n] v) x y
  let E := ((NumberField.classNumber K : ℝ)*heckeConductorClassConstant K*(X+U^2))*
    ((1+(Real.log X)^2)^2*coefficientClassDirichletMass K B v σ₀)
  have henergy (n : ℕ) (hn : n ≤ 2) (x : ℝ) (hx : x ∈ Icc σ₀ σ₁)
      (y : ℝ) (_hy : y ∈ Icc (-Y) Y) : ∑ i ∈ S, ‖M n i x y‖^2 ≤ E := by
    have hmajor := actualHecke_coefficientFamily_vertical_sieve K hU hX T hT A hA B hB
      ((coefficientClassRealLogWeight K)^[n] v) x (-y)
    have hsub : (∑ i ∈ S, ‖M n i x y‖^2) ≤
        ∑ M ∈ T, ∑ a ∈ (A M).image (fun ψ => ψ.coefficient),
          ‖coefficientClassDirichletPolynomial K a B ((coefficientClassRealLogWeight K)^[n] v) x (-y)‖^2 := by
      calc
        _ ≤ ∑ i ∈ T.sigma (fun M => (A M).image (fun ψ => ψ.coefficient)), ‖M n i x y‖^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => sq_nonneg _)
        _ = _ := by rw [Finset.sum_sigma]
    have hp : ((Real.log X)^2)^n ≤ (1+(Real.log X)^2)^2 :=
      (pow_le_pow_left₀ (sq_nonneg _) (by linarith [sq_nonneg (Real.log X)]) n).trans
        (pow_le_pow_right₀ (by linarith [sq_nonneg (Real.log X)]) hn)
    have hm := (coefficientClassRealLogWeight_iterate_mass_le K hX B hB v x n).trans
      (mul_le_mul hp (coefficientClassDirichletMass_antitone K B v hx.1)
        (coefficientClassDirichletMass_nonneg K B v x) (by positivity))
    exact (hsub.trans hmajor).trans (mul_le_mul_of_nonneg_left hm (by
      have hc := (heckeConductorClassConstant_pos K).le
      positivity))
  have ht' (i) (hi : i ∈ S) : -t i ∈ Icc (-Y) Y := by
    have H := abs_le.mp (htS i hi)
    constructor <;> linarith
  have H := OAI.SevenEighths.HeckeDetectorRowwise.chain_rowwise S M cm dx dy
    σ₀ σ₁ (-Y) Y E hσ (by linarith) σ (fun i => -t i) hσS ht' henergy
  convert H using 1
  · simp only [M,Function.iterate_zero,id_eq,neg_neg]
  · dsimp [E]
    ring

theorem actualHecke_coefficientFamily_rectangle_count
    {U X σ₀ σ₁ Y : ℝ} (hU : 1 ≤ U) (hX : 1 ≤ X) (hσ : σ₀ ≤ σ₁) (hY : 0 ≤ Y)
    (T : Finset (IdealConductorModulus K))
    (hT : ∀ M ∈ T, (Ideal.absNorm M.val : ℝ) ≤ U)
    (A : ∀ M : IdealConductorModulus K, Finset (EvenIdealRayCharacter K M.val))
    (hA : ∀ M ∈ T, ∀ ψ ∈ A M, IsPrimitiveOnIdeals ψ.residue)
    (B : ∀ c : ClassGroup (𝓞 K),
      Finset (integralIdealClassFiber (rayClassFractionalRepresentative K 1 c)))
    (hB : ∀ c, ∀ J ∈ B c, (FractionalIdeal.absNorm J.val.val : ℝ) ≤ X)
    (v : ∀ c : ClassGroup (𝓞 K),
      integralIdealClassFiber (rayClassFractionalRepresentative K 1 c) → ℂ)
    (δ : ℝ) (hδ : 0 < δ) :
    (∑ M ∈ T, (((A M).image (fun ψ => ψ.coefficient)).filter
      (fun a => ∃ σ t : ℝ, σ ∈ Icc σ₀ σ₁ ∧ |t| ≤ Y ∧
        δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)).card : ℝ) ≤
      ((1+2*(σ₁-σ₀))*((1+4*Y)*
        (((NumberField.classNumber K : ℝ)*heckeConductorClassConstant K*(X+U^2))*
          ((1+(Real.log X)^2)^2*coefficientClassDirichletMass K B v σ₀)))) / δ^2 := by
  let F (M : IdealConductorModulus K) := ((A M).image (fun ψ => ψ.coefficient)).filter
    (fun a => ∃ σ t : ℝ, σ ∈ Icc σ₀ σ₁ ∧ |t| ≤ Y ∧
      δ ≤ ‖coefficientClassDirichletPolynomial K a B v σ t‖)
  let S := T.sigma F
  have hw (i : Σ _M : IdealConductorModulus K, integralFractionalIdeals K → ℂ) :
      ∃ σ t : ℝ, i ∈ S → σ ∈ Icc σ₀ σ₁ ∧ |t| ≤ Y ∧
        δ ≤ ‖coefficientClassDirichletPolynomial K i.2 B v σ t‖ := by
    by_cases hi : i ∈ S
    · obtain ⟨σ,t,hσ',ht,hval⟩ := (Finset.mem_filter.mp (Finset.mem_sigma.mp hi).2).2
      exact ⟨σ,t,fun _ => ⟨hσ',ht,hval⟩⟩
    · exact ⟨σ₀,0,fun h => False.elim (hi h)⟩
  choose σ t hw using hw
  have hS : S ⊆ T.sigma (fun M => (A M).image (fun ψ => ψ.coefficient)) := by
    intro i hi
    have H := Finset.mem_sigma.mp hi
    exact Finset.mem_sigma.mpr ⟨H.1,(Finset.mem_filter.mp H.2).1⟩
  have H := actualHecke_coefficientFamily_rowwise_rectangle K hU hX hσ hY T hT A hA B hB v
    S hS σ t (fun i hi => (hw i hi).1) (fun i hi => (hw i hi).2.1)
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).2
  calc
    _ = (S.card : ℝ)*δ^2 := by
      dsimp only [S]
      rw [Finset.card_sigma,Nat.cast_sum]
    _ = ∑ i ∈ S, δ^2 := by simp
    _ ≤ ∑ i ∈ S, ‖coefficientClassDirichletPolynomial K i.2 B v (σ i) (t i)‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (sq_le_sq₀ hδ.le (norm_nonneg _)).mpr (hw i hi).2.2
    _ ≤ _ := H

end
end ArtinMatthews.VaryingKummerAnalytic
